//! Local induction cuts: establish on entry, havoc the scalar head, check each
//! transferred back edge and stop it. Runtime instruction semantics stay in
//! the canonical CFG transfer. All findings participate in summary publication.
use super::*;
use crate::verifier::relation::{
    RelationComparison as C, RelationTerm as R, difference::DifferencePremise,
};
use crate::verifier::vc::{
    SnapshotValues, VcLimits, VcNormalizer, VcQueryBudget, VcTermId, evaluate_bool,
};
use crate::vir::{ScalarLoopAtom as Atom, ScalarOperand as Operand, scalar_atoms};
pub(super) mod candidates;
mod resources;
mod scalars;
pub use candidates::LoopCandidateAttempt;

pub(super) struct Induction<'a, 'u> {
    loops: Vec<LoopInduction<'a, 'u>>,
}

impl<'a, 'u> Induction<'a, 'u> {
    pub(super) fn new(
        unit: &'a ResolvedVirUnit<'u>,
        function: &'a VirFunction,
        config: CfgAnalysisConfig,
        selected: &BTreeSet<crate::VirSpecLoopInvariantId>,
        registry: Option<&'a super::super::summary::SummaryRegistry>,
    ) -> Result<Self, CfgAnalysisError> {
        let headers: BTreeSet<_> = unit
            .as_unit()
            .specs
            .loop_invariants()
            .iter()
            .filter(|i| i.function == function.id)
            .filter(|i| candidates::enabled(unit, i, selected))
            .map(|i| i.boundary.as_ref().unwrap().header)
            .collect();
        if headers.len() > 64 {
            return Err(CfgAnalysisError::LoopInvariantResourceStateUnsupported);
        }
        Ok(Self {
            loops: headers
                .into_iter()
                .map(|header| {
                    LoopInduction::new(unit, function, config, header, selected, registry)
                })
                .collect::<Result<_, _>>()?,
        })
    }

    pub(super) fn anchors(&self) -> Vec<VirValueId> {
        self.loops
            .first()
            .map_or_else(Vec::new, LoopInduction::anchors)
    }

    pub(super) fn cut_edges(
        &mut self,
        block: &VirBasicBlock,
        evaluated: &mut ConditionalBlockEvaluation,
    ) -> Result<(), CfgAnalysisError> {
        for induction in &mut self.loops {
            induction.cut_edges(block, evaluated)?;
        }
        Ok(())
    }
}

struct LoopInduction<'a, 'u> {
    registry: Option<&'a super::super::summary::SummaryRegistry>,
    unit: &'a ResolvedVirUnit<'u>,
    function: &'a VirFunction,
    clauses: Vec<(&'a crate::VirSpecLoopInvariant, Option<VcTermId>)>,
    resource_entry: Option<ResourceState>,
    normalizer: VcNormalizer,
    budget: VcQueryBudget,
    config: CfgAnalysisConfig,
}

impl<'a, 'u> LoopInduction<'a, 'u> {
    pub(super) fn anchors(&self) -> Vec<VirValueId> {
        if self.clauses.is_empty() {
            return Vec::new();
        }
        self.function
            .blocks
            .iter()
            .find(|b| b.id == self.function.entry)
            .unwrap()
            .parameters
            .iter()
            .filter(|p| matches!(p.ty, VirType::U64 | VirType::Bool))
            .map(|p| p.id)
            .collect()
    }
    pub(super) fn new(
        unit: &'a ResolvedVirUnit<'u>,
        function: &'a VirFunction,
        config: CfgAnalysisConfig,
        header: VirBlockId,
        selected: &BTreeSet<crate::VirSpecLoopInvariantId>,
        registry: Option<&'a super::super::summary::SummaryRegistry>,
    ) -> Result<Self, CfgAnalysisError> {
        let mut normalizer = VcNormalizer::new(VcLimits::default());
        let mut clauses = Vec::new();
        for invariant in unit.as_unit().specs.loop_invariants().iter().filter(|i| {
            i.function == function.id
                && i.boundary.as_ref().unwrap().header == header
                && candidates::enabled(unit, i, selected)
        }) {
            let root = match unit.as_unit().specs.clause(invariant.clause).unwrap().kind {
                crate::VirSpecClauseKind::Logic { root } => Some(
                    normalizer
                        .normalize(unit, root)
                        .map_err(|_| CfgAnalysisError::LoopInvariantBudgetExceeded(invariant.id))?,
                ),
                crate::VirSpecClauseKind::Assertion { root }
                    if crate::vir::resource_atom(&unit.as_unit().specs, root).is_some() =>
                {
                    None
                }
                _ => return Err(CfgAnalysisError::ContractInstantiation),
            };
            clauses.push((invariant, root));
        }
        let mut budget = VcQueryBudget::new(VcLimits::default());
        budget.relation_limits = config.relation_limits;
        Ok(Self {
            registry,
            unit,
            function,
            clauses,
            resource_entry: None,
            normalizer,
            budget,
            config,
        })
    }

    pub(super) fn cut_edges(
        &mut self,
        block: &VirBasicBlock,
        evaluated: &mut ConditionalBlockEvaluation,
    ) -> Result<(), CfgAnalysisError> {
        let Some((first, _)) = self.clauses.first() else {
            return Ok(());
        };
        let first_id = first.id;
        let boundary = first.boundary.clone().expect("validated boundary");
        let resource_values: Vec<_> = self
            .function
            .blocks
            .iter()
            .find(|b| b.id == boundary.header)
            .unwrap()
            .parameters
            .iter()
            .filter(|p| !matches!(p.ty, VirType::U64 | VirType::Bool))
            .map(|p| p.id)
            .collect();
        let mut successors = Vec::new();
        for mut successor in std::mem::take(&mut evaluated.successors) {
            if successor.block != boundary.header {
                successors.push(successor);
                continue;
            }
            let back_edge = block.id != boundary.preheader;
            let mut ledgers: Vec<_> = successor
                .state
                .cases()
                .iter()
                .map(|_| {
                    super::super::spec::separation::MatchLedger::new(
                        self.config.max_region_pairs_per_instruction,
                    )
                })
                .collect();
            for (invariant, root) in &self.clauses {
                let finding = VerifierFinding::loop_invariant(self.unit, invariant, block.id)
                    .ok_or(CfgAnalysisError::InvalidFinding {
                        location: VirLocation::Terminator {
                            function: self.function.id,
                            block: block.id,
                        },
                    })?;
                for (case_ordinal, state) in successor.state.cases().iter().enumerate() {
                    let status = if let Some(root) = root {
                        let result = evaluate_bool(
                            self.normalizer.arena(),
                            *root,
                            &BTreeSet::new(),
                            SnapshotValues::State(state),
                            self.function,
                            &mut self.budget,
                        );
                        match result {
                            Some(AbstractBool::True) => ObligationStatus::Proven,
                            Some(AbstractBool::False) => ObligationStatus::Refuted,
                            _ => ObligationStatus::Unknown,
                        }
                    } else {
                        let crate::VirSpecClauseKind::Assertion { root } = self
                            .unit
                            .as_unit()
                            .specs
                            .clause(invariant.clause)
                            .unwrap()
                            .kind
                        else {
                            unreachable!()
                        };
                        resources::check(
                            self.unit,
                            crate::vir::resource_atom(&self.unit.as_unit().specs, root).unwrap(),
                            state,
                            &mut ledgers[case_ordinal],
                            self.config,
                            &mut self.budget,
                        )
                    };
                    let queries = std::mem::take(&mut self.budget.relations)
                        .finish()
                        .ok_or(CfgAnalysisError::LoopInvariantBudgetExceeded(invariant.id))?;
                    if self.budget.exhausted
                        || queries.len()
                            > self
                                .config
                                .max_relation_evidence
                                .saturating_sub(evaluated.relation_queries.len())
                    {
                        return Err(CfgAnalysisError::LoopInvariantBudgetExceeded(invariant.id));
                    }
                    evaluated
                        .relation_queries
                        .extend(
                            queries
                                .into_iter()
                                .enumerate()
                                .map(|(query_ordinal, query)| {
                                    super::super::relation::audit::QueryEvidence {
                                        config: self.config,
                                        finding,
                                        sources: vec![finding],
                                        sources_truncated: true,
                                        case_ordinal,
                                        edge_ordinal: Some(successor.edge_ordinal),
                                        query_ordinal,
                                        query,
                                    }
                                }),
                        );
                    let record = CfgObligation {
                        block: block.id,
                        origin: match &block.terminator.terminator {
                            VirTerminator::Jump { .. } => CfgObligationOrigin::Jump {
                                target: successor.block,
                            },
                            _ if successor.edge_ordinal == 0 => CfgObligationOrigin::BranchThen {
                                target: successor.block,
                            },
                            _ => CfgObligationOrigin::BranchElse {
                                target: successor.block,
                            },
                        },
                        finding,
                        obligation: ResourceObligation::new(
                            ResourceObligationKind::LoopInvariantEstablished {
                                invariant: invariant.id,
                                back_edge,
                            },
                            status,
                            finding.source_span(),
                        ),
                    };
                    merge_case_obligation(&mut evaluated.obligations, record);
                    if back_edge && invariant.id == first_id {
                        let preserved = self.resource_entry.as_ref().is_some_and(|entry| {
                            state.loop_resources_match(entry, &resource_values)
                        });
                        let mut resource_record = record;
                        resource_record.obligation = ResourceObligation::new(
                            ResourceObligationKind::LoopResourcesPreserved {
                                invariant: invariant.id,
                            },
                            if preserved {
                                ObligationStatus::Proven
                            } else {
                                // Abstract inequality can be precision loss,
                                // not a concrete resource counterexample.
                                ObligationStatus::Unknown
                            },
                            finding.source_span(),
                        );
                        merge_case_obligation(&mut evaluated.obligations, resource_record);
                    }
                }
            }
            if !back_edge {
                // Havoc the head, then restore only independently established
                // immutable scalar aliases and loop-local premises. Never copy
                // a modified parameter's initial value/path facts into the head.
                if successor.state.is_reachable() {
                    let states = successor
                        .state
                        .cases()
                        .iter()
                        .map(|state| {
                            // One fixed resource identity mapping, even when
                            // scalar/content entry facts have alternatives.
                            // Switching mappings could import another case's
                            // untouched frame at a later back edge.
                            if let Some(entry) = &self.resource_entry {
                                if !state.loop_resources_match(entry, &resource_values) {
                                    return Err(
                                        CfgAnalysisError::LoopInvariantResourceStateUnsupported,
                                    );
                                }
                            } else {
                                self.resource_entry = Some(state.clone());
                            }
                            self.arbitrary_head(state)
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    successor.state = ConditionalResourceState::from_cases(
                        states,
                        successor.state.precision_losses().clone(),
                        self.config.guarded_limits(),
                        GuardedReduction::Selective,
                    )
                    .map_err(|error| CfgAnalysisError::ResourceJoin {
                        block: successor.block,
                        error,
                    })?;
                }
                successors.push(successor);
            }
            // Back edges are checked above, never unrolled or merged into the
            // arbitrary head. Unknown/Refuted remain publication barriers.
        }
        evaluated.successors = successors;
        Ok(())
    }

    fn arbitrary_head(&self, entry: &ResourceState) -> Result<ResourceState, CfgAnalysisError> {
        let boundary = self.clauses[0].0.boundary.as_ref().unwrap();
        if scalars::reachable_blocks(self.function, boundary).is_some_and(|blocks| {
            boundary
                .back_edges
                .iter()
                .all(|edge| !blocks.contains(&edge.source))
        }) {
            // A dead generated latch is not an iteration. Keep the actual
            // entry facts (including uninitializedness) for this acyclic body.
            return Ok(entry.clone());
        }
        let header = self
            .function
            .blocks
            .iter()
            .find(|b| b.id == boundary.header)
            .unwrap();
        let mut state = ResourceState::new();
        if !entry.allocations().is_empty()
            && !header
                .parameters
                .iter()
                .any(|p| matches!(p.ty, VirType::Pointer { .. }))
        {
            return Err(CfgAnalysisError::LoopInvariantResourceStateUnsupported);
        }
        let modified = resources::modified_allocations(
            self.unit,
            self.function,
            boundary,
            entry,
            self.registry,
        )?;
        if !state.inherit_loop_resources(entry, &modified) {
            return Err(CfgAnalysisError::LoopInvariantResourceStateUnsupported);
        }
        let anchors = self.anchors();
        let stable = scalars::unchanged(self.function, boundary);
        let retained: BTreeSet<_> = stable
            .iter()
            .copied()
            .chain(anchors.iter().copied())
            .collect();
        state.inherit_loop_scalar_frame(entry, &retained);
        state.inherit_loop_initialization_frame(entry, &retained);
        for &id in &anchors {
            state
                .define_value(id, *entry.value(id).expect("entry scalar anchor"))
                .map_err(|error| CfgAnalysisError::StateDefinition {
                    block: header.id,
                    error,
                })?;
            if matches!(state.value(id), Some(AbstractValue::U64(_))) {
                state.set_word_expression(id, crate::AffineExpression::identity(id));
            }
        }
        for parameter in &header.parameters {
            if !matches!(parameter.ty, VirType::U64 | VirType::Bool)
                && !entry
                    .value(parameter.id)
                    .copied()
                    .is_some_and(ResourceState::stable_loop_value)
            {
                return Err(CfgAnalysisError::LoopInvariantResourceStateUnsupported);
            }
            state
                .define_value(
                    parameter.id,
                    if matches!(parameter.ty, VirType::U64 | VirType::Bool)
                        && !stable.contains(&parameter.id)
                    {
                        unknown_value(parameter.ty)
                    } else {
                        *entry
                            .value(parameter.id)
                            .ok_or(CfgAnalysisError::LoopInvariantResourceStateUnsupported)?
                    },
                )
                .map_err(|error| CfgAnalysisError::StateDefinition {
                    block: header.id,
                    error,
                })?;
            if parameter.ty == VirType::U64 {
                state.set_word_expression(
                    parameter.id,
                    crate::AffineExpression::identity(parameter.id),
                );
            }
        }
        let mut premises = Vec::new();
        let aliases = super::super::summary::scalar_aliases(self.function);
        for parameter in header
            .parameters
            .iter()
            .filter(|p| matches!(p.ty, VirType::U64 | VirType::Bool))
        {
            use super::super::summary::ScalarTerm;
            match aliases.get(&parameter.id) {
                Some(ScalarTerm::Input(slot)) => {
                    // Alias slots refer to the full ABI, not the filtered
                    // scalar-anchor list. Never pin pointer/permission copies.
                    let anchor = self
                        .function
                        .blocks
                        .iter()
                        .find(|b| b.id == self.function.entry)
                        .unwrap()
                        .parameters[*slot]
                        .id;
                    if parameter.ty == VirType::Bool {
                        *state.value_mut(parameter.id).unwrap() = *entry.value(anchor).unwrap();
                    } else {
                        premises.push(DifferencePremise::EqualOffset {
                            left: R::Value {
                                value: parameter.id,
                                ty: VirType::U64,
                            },
                            right: R::Value {
                                value: anchor,
                                ty: VirType::U64,
                            },
                            offset: 0,
                        });
                    }
                }
                Some(ScalarTerm::Constant(n)) => {
                    *state.value_mut(parameter.id).unwrap() =
                        AbstractValue::U64(U64Interval::exact(*n));
                }
                None => {}
            }
        }
        let operand = |o| match o {
            Operand::Value(value) => R::Value {
                value,
                ty: VirType::U64,
            },
            Operand::Constant(n) => R::Constant(n),
        };
        for (invariant, _) in &self.clauses {
            let crate::VirSpecClauseKind::Logic { root } = self
                .unit
                .as_unit()
                .specs
                .clause(invariant.clause)
                .unwrap()
                .kind
            else {
                continue;
            };
            for atom in
                scalar_atoms(&self.unit.as_unit().specs, root).expect("admitted scalar clauses")
            {
                match atom {
                    // False/contradictory assumptions do not erase a path here.
                    // Their failed establishment check must remain observable.
                    Atom::Constant => {}
                    Atom::Boolean(id, expected) => {
                        *state.value_mut(id).unwrap() = AbstractValue::Bool(if expected {
                            AbstractBool::True
                        } else {
                            AbstractBool::False
                        });
                    }
                    Atom::Compare {
                        left,
                        right,
                        strict,
                        equal,
                    } => premises.push(DifferencePremise::Compare {
                        comparison: if equal {
                            C::Equal
                        } else if strict {
                            C::LessThan
                        } else {
                            C::LessOrEqual
                        },
                        left: operand(left),
                        right: operand(right),
                    }),
                }
            }
        }
        // These are provisional loop-local premises, not proven global facts.
        // Every escape is contingent on the establishment and preservation
        // obligations in this same analysis; none enter the trust table.
        state.learn_relations(&premises, self.config.relation_limits);
        state.reduce_relation_intervals();
        for (invariant, _) in &self.clauses {
            if let crate::VirSpecClauseKind::Assertion { root } = self
                .unit
                .as_unit()
                .specs
                .clause(invariant.clause)
                .unwrap()
                .kind
            {
                resources::assume_initialized(
                    self.unit,
                    crate::vir::resource_atom(&self.unit.as_unit().specs, root).unwrap(),
                    &mut state,
                    self.config,
                );
            }
        }
        Ok(state)
    }
}
