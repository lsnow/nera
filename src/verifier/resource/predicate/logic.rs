//! Actual predicate witnesses are read before sealing and retained by the
//! instance. A source field name or a numeric value is never binder identity.
use super::*;
use crate::predicate_logic::*;
mod abstraction;
mod assumptions;
mod identity;
#[cfg(test)]
pub(super) use identity::normalize_closed_parameters_with_aliases;
#[cfg(test)]
pub(super) use identity::normalize_closed_parameters_with_sources;
pub(super) use identity::{
    freshen_instance, freshen_local_instance, mentions_scopes, normalize_closed_scope,
    parameter_local_snapshots,
};
mod arguments;
mod expressions;
use expressions::ExpressionFacts;
mod fact_inputs;
mod local_capture;
mod loops;
mod numeric_inputs;
mod observations;
mod opened_queries;
mod parameter_sources;
mod prefix_access;
mod prefix_domains;
use observations::{observed_bool, observed_word};
mod prefix_sources;
mod prefixes;
pub(super) use prefixes::LogicalInitialization;
mod scalar_capture;
mod scalar_relations;
mod word_sources;
pub(super) use assumptions::PredicateConstraintFact;
pub(super) use parameter_sources::ParameterAlignment;
pub(super) use scalar_capture::ScalarCapture;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum ObservationAtom {
    /// A hidden scalar imported from a checked existential package. It is
    /// neither an SSA value nor a request to choose the declaration default.
    Existential { scope: InstanceScope, binder: u32 },
    Local {
        scope: InstanceScope,
        value: VirValueId,
    },
    Captured {
        scope: InstanceScope,
        value: VirValueId,
    },
    // An actual without a surviving CFG alias is not an old fold snapshot,
    // even when its current SSA number happens to be identical.
    Current {
        scope: InstanceScope,
        value: VirValueId,
    },
    HistoricalBool {
        scope: InstanceScope,
        origin: BoolOrigin,
        local: bool,
    },
    Historical {
        scope: InstanceScope,
        cell: crate::verifier::resource::ScalarOriginCell,
        local: bool,
    },
    Memory {
        scope: InstanceScope,
        allocation: AbstractAllocationId,
        offset: u64,
        access: VirMemoryAccess,
        time: ObservationTime,
        captured: bool,
    },
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct ResourceWitness {
    allocation: AbstractAllocationId,
    pointer: AbstractPointer,
    // This is a typed position, not a capability. Owner-to-loan handoff
    // changes authority without changing the position. Real permissions stay
    // exclusively in SealedResource and are checked by each transition.
}
pub(super) type PredicateLogicValue =
    TypedLogicValue<VirMemoryAccess, ObservationAtom, ResourceWitness>;

/// A surviving CFG alias names an immutable observation, including its capture
/// scope. Refolding must not reinterpret the original SSA number in a new scope.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct LocalSnapshot {
    pub(super) scope: InstanceScope,
    pub(super) value: VirValueId,
}

impl LocalSnapshot {
    fn atom(self) -> ObservationAtom {
        ObservationAtom::Local {
            scope: self.scope,
            value: self.value,
        }
    }
}

pub(super) struct CapturedPredicateLogic {
    pub scope: Option<InstanceScope>,
    pub witnesses: Vec<PredicateLogicValue>,
    pub parameters: Vec<PredicateLogicValue>,
    pub local_aliases: BTreeMap<VirValueId, LocalSnapshot>,
    pub facts: Vec<PredicateConstraintFact>,
}

impl ResourceState {
    /// A read-only ghost observation, available only while this exact opening
    /// is live. Surviving local origins may provide numeric relations; an
    /// existential identity is never fabricated as a runtime SSA value.
    pub(in crate::verifier) fn opened_predicate_snapshot(
        &self,
        action: u32,
        holder: u32,
        binder: u32,
    ) -> Option<(AbstractValue, Option<crate::AffineExpression>)> {
        let instance = self.predicates.get(&PredicateHolder(holder))?;
        if instance.folded
            || instance.opening_action != Some(action)
            || instance.logic_scope.is_none()
        {
            return None;
        }
        let value = self
            .bounded_opened_witness(
                instance,
                self.refine_predicate_boolean(
                    instance.logical_witnesses.get(binder as usize)?.clone(),
                ),
                &mut LogicBudget::default(),
            )
            .ok()?;
        match value.value {
            LogicValue::Word(word) => {
                let (word, aliases) = self.refine_predicate_word(&word)?;
                let interval = U64Interval::new(word.lower, word.upper).ok()?;
                let expression = interval
                    .exact_value()
                    .map(crate::AffineExpression::constant)
                    .or_else(|| {
                        aliases
                            .first()
                            .copied()
                            .map(crate::AffineExpression::identity)
                    });
                Some((AbstractValue::U64(interval), expression))
            }
            LogicValue::Bool(known) => Some((
                AbstractValue::Bool(match known {
                    Some(true) => AbstractBool::True,
                    Some(false) => AbstractBool::False,
                    None => AbstractBool::Unknown,
                }),
                None,
            )),
            LogicValue::BoolAtom { .. }
            | LogicValue::BoolComparison { .. }
            | LogicValue::BoolBinary { .. } => {
                Some((AbstractValue::Bool(AbstractBool::Unknown), None))
            }
            LogicValue::Resource(_) | LogicValue::ResourceAtom { .. } => None,
        }
    }

    pub(super) fn capture_predicate_logic(
        &mut self,
        definition: &PredicateDefinition,
        holder: PredicateHolder,
        resources: &[SealedResource],
        explicit: &WitnessArguments<VirMemoryAccess, VirValueId>,
        imported: bool,
    ) -> Result<CapturedPredicateLogic, PredicateError> {
        if definition.logic.existentials.is_empty()
            && definition.logic.constraints.is_empty()
            && explicit.inputs.is_empty()
            && explicit.values.is_empty()
            && definition.logic.parameters.is_empty()
            && explicit.arguments.is_empty()
            && definition.logical_prefixes.is_empty()
        {
            return Ok(CapturedPredicateLogic {
                scope: None,
                witnesses: vec![],
                parameters: vec![],
                local_aliases: BTreeMap::new(),
                facts: vec![],
            });
        }
        let scope = InstanceScope {
            declaration: definition.id.get(),
            instance: self.next_predicate_scope,
            opening: 0,
        };
        let next = self
            .next_predicate_scope
            .checked_add(1)
            .ok_or(PredicateError::Budget)?;
        if explicit.inputs.len() > MAX_LOGIC_PARAMETERS || explicit.values.len() > MAX_EXISTENTIALS
        {
            return Err(PredicateError::Budget);
        }
        let mut ids = BTreeSet::new();
        if explicit
            .values
            .iter()
            .any(|(id, _)| *id as usize >= definition.logic.existentials.len() || !ids.insert(*id))
        {
            return Err(PredicateError::InvalidBinding);
        }
        let mut budget = LogicBudget::default();
        if imported {
            // The ABI has already checked the real representation. Give its
            // current observations an immutable local identity before capturing
            // witnesses and constraints, even when no entry origin survived a
            // call. This does not recover any pre-call equality or SSA alias.
            self.seed_predicate_observations(definition, resources, scope.instance, &mut budget)?;
        }
        let mut local_aliases = self
            .predicates
            .get(&holder)
            .filter(|instance| !imported && !instance.folded && instance.definition == *definition)
            .map(|instance| instance.logical_local_aliases.clone())
            .unwrap_or_default();
        for (_, input) in &explicit.inputs {
            if let Some(value) = input.scalar() {
                local_aliases.entry(*value).or_insert(LocalSnapshot {
                    scope,
                    value: *value,
                });
            }
        }
        if local_aliases.len() > MAX_PREDICATE_LOCAL_ALIASES {
            return Err(PredicateError::Budget);
        }
        budget.charge(local_aliases.len()).map_err(map_error)?;
        let inputs = self.predicate_logic_inputs(
            definition,
            holder,
            scope,
            explicit,
            &local_aliases,
            true,
            &mut budget,
        )?;
        let available = self
            .predicates
            .get(&holder)
            .filter(|instance| !imported && !instance.folded && instance.definition == *definition)
            .map_or(&[][..], |instance| instance.logical_facts.as_slice());
        let context = ExpressionFacts::new(self, scope, available, explicit, &inputs, &mut budget)?;
        let parameters = self.evaluate_predicate_arguments(
            &definition.logic,
            explicit,
            &inputs,
            &context,
            &mut budget,
        )?;
        let mut observe = |resource, offset, access, time| {
            self.observe_predicate_logic(
                definition,
                resources,
                scope,
                true,
                (resource, offset, access, time),
            )
        };
        let mut resource =
            |index, path: &[u64]| resource_value(self, definition, resources, index, path);
        let witnesses = if imported {
            self.import_predicate_witnesses(
                definition,
                &parameters,
                scope,
                &mut observe,
                &mut resource,
                &mut budget,
            )?
        } else {
            definition.logic.instantiate_witnesses_using(
                &parameters,
                &inputs,
                &explicit.values,
                &mut |expression, parameters, witnesses, budget| {
                    self.evaluate_predicate_expression(
                        expression,
                        parameters,
                        witnesses,
                        &context,
                        &mut observe,
                        &mut resource,
                        false,
                        budget,
                    )
                },
                &mut budget,
            )?
        };
        let facts = self.capture_predicate_constraints(
            definition,
            resources,
            scope,
            &parameters,
            &witnesses,
            available,
            imported,
            Some(&context),
            &mut budget,
        )?;
        // The old field-prefix representation may use an explicit logical
        // count only when it is provably equal to the actual current field.
        // Checking equality does not certify initialization or create authority.
        for (index, _) in &explicit.values {
            if !definition.projected_witnesses.contains(index) {
                continue;
            }
            let declaration = definition
                .logic
                .existentials
                .get(*index as usize)
                .ok_or(PredicateError::InvalidBinding)?;
            let default = declaration
                .default
                .as_ref()
                .ok_or(PredicateError::InvalidDefinition)?;
            let current = default
                .evaluate(
                    &parameters,
                    &witnesses,
                    &mut observe,
                    &mut resource,
                    &mut budget,
                )
                .map_err(map_error)?;
            let saved = witnesses
                .get(*index as usize)
                .ok_or(PredicateError::InvalidBinding)?;
            let equal = match (&current.value, &saved.value) {
                (LogicValue::Word(a), LogicValue::Word(b)) => a.equal(b),
                (
                    a @ (LogicValue::Bool(_)
                    | LogicValue::BoolAtom { .. }
                    | LogicValue::BoolComparison { .. }
                    | LogicValue::BoolBinary { .. }),
                    b @ (LogicValue::Bool(_)
                    | LogicValue::BoolAtom { .. }
                    | LogicValue::BoolComparison { .. }
                    | LogicValue::BoolBinary { .. }),
                ) => a.bool_equal(b),
                _ => None,
            };
            if current.ty != saved.ty || equal != Some(true) {
                return Err(PredicateError::UnprovedRepresentation);
            }
        }
        self.next_predicate_scope = next;
        Ok(CapturedPredicateLogic {
            scope: Some(scope),
            witnesses,
            parameters,
            local_aliases,
            facts,
        })
    }
}

impl ResourceState {
    // Capture and recheck share typed initialization and real authority checks.
    // A current read must never reuse an atom from the earlier fold snapshot.
    fn observe_predicate_logic(
        &self,
        definition: &PredicateDefinition,
        resources: &[SealedResource],
        scope: InstanceScope,
        captured: bool,
        observation: (u32, u64, VirMemoryAccess, ObservationTime),
    ) -> Result<PredicateLogicValue, LogicError> {
        let (resource, offset, access, time) = observation;
        if time != ObservationTime::Current {
            return Err(LogicError::Unbound);
        }
        let r = resources
            .get(resource as usize)
            .ok_or(LogicError::Unbound)?;
        let ty = *definition
            .logic_observations
            .get(&(resource, offset, access))
            .ok_or(LogicError::TypeMismatch)?;
        let width = if ty == LogicType::Bool { 1 } else { 8 };
        let range =
            ByteRange::from_start_and_length(offset, width).map_err(|_| LogicError::InvalidNode)?;
        let allocation = self.allocation(r.allocation).ok_or(LogicError::Unproved)?;
        if allocation.liveness() != LivenessState::Live
            || allocation.initialization().classify(range) != InitializationClass::Initialized
            || !allocation.valid_value_bytes().contains(range)
            || r.permission.availability() != PermissionAvailability::Available
            || !matches!(r.permission.range(),AbstractByteRange::Exact(allowed) if allowed.contains(range))
        {
            return Err(LogicError::Unproved);
        }
        let value = match (ty, allocation.scalar_content(range, access)) {
            (LogicType::Bool, Some(AbstractValue::Bool(value))) => observed_bool(
                scope,
                value,
                allocation.bool_origin(range, access),
                Some(ObservationAtom::Memory {
                    scope,
                    allocation: r.allocation,
                    offset,
                    access,
                    time,
                    captured,
                }),
            ),
            (LogicType::Bool, None) => LogicValue::BoolAtom {
                atom: ObservationAtom::Memory {
                    scope,
                    allocation: r.allocation,
                    offset,
                    access,
                    time,
                    captured,
                },
                negated: false,
                known: None,
            },
            (LogicType::U64 | LogicType::Usize, Some(AbstractValue::U64(value))) => {
                LogicValue::Word(observed_word(
                    scope,
                    value,
                    allocation.scalar_origin(range, access),
                    ObservationAtom::Memory {
                        scope,
                        allocation: r.allocation,
                        offset,
                        access,
                        time,
                        captured,
                    },
                )?)
            }
            (LogicType::U64 | LogicType::Usize, None) => LogicValue::Word(AffineValue::variable(
                ObservationAtom::Memory {
                    scope,
                    allocation: r.allocation,
                    offset,
                    access,
                    time,
                    captured,
                },
                0,
                u64::MAX,
            )?),
            _ => return Err(LogicError::TypeMismatch),
        };
        Ok(self.refine_predicate_boolean(TypedLogicValue { ty, value }))
    }

    pub(super) fn predicate_logic_valid(&self, instance: &PredicateInstance) -> bool {
        let logic = &instance.definition.logic;
        if logic.parameters.len() != instance.logical_parameters.len()
            || logic.existentials.len() != instance.logical_witnesses.len()
            || logic
                .parameters
                .iter()
                .zip(&instance.logical_parameters)
                .any(|(p, v)| p.ty != v.ty)
            || logic
                .existentials
                .iter()
                .zip(&instance.logical_witnesses)
                .any(|(p, v)| p.ty != v.ty)
        {
            return false;
        }
        if !self.predicate_logical_prefixes_valid(instance) {
            return false;
        }
        if logic.constraints.is_empty() {
            return true;
        }
        let Some(scope) = instance.logic_scope else {
            return false;
        };
        let mut budget = LogicBudget::default();
        self.capture_predicate_constraints(
            &instance.definition,
            &instance.resources,
            scope,
            &instance.logical_parameters,
            &instance.logical_witnesses,
            &instance.logical_facts,
            false,
            None,
            &mut budget,
        )
        .is_ok()
    }
}

fn rebind_local_origins(
    value: &mut PredicateLogicValue,
    mut scope: InstanceScope,
    budget: &mut LogicBudget,
) -> Result<(), LogicError> {
    scope.opening = 0;
    for leaf in value.value.capture_leaves_mut(budget)? {
        if let LogicValue::BoolAtom {
            atom:
                ObservationAtom::HistoricalBool {
                    scope: old,
                    local: true,
                    ..
                },
            ..
        } = leaf
        {
            *old = scope;
        }
        match leaf {
            LogicValue::Word(word) => rebind_word_origins(word, scope)?,
            LogicValue::BoolComparison { left, right, .. } => {
                rebind_word_origins(left, scope)?;
                rebind_word_origins(right, scope)?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn rebind_word_origins(
    word: &mut AffineValue<ObservationAtom>,
    scope: InstanceScope,
) -> Result<(), LogicError> {
    let mut terms = BTreeMap::<ObservationAtom, i128>::new();
    for (atom, coefficient) in &word.terms {
        let atom = match atom {
            ObservationAtom::Historical {
                cell, local: true, ..
            } => ObservationAtom::Historical {
                scope,
                cell: *cell,
                local: true,
            },
            other => other.clone(),
        };
        let merged = terms.entry(atom).or_default();
        *merged = merged
            .checked_add(*coefficient)
            .ok_or(LogicError::Overflow)?;
    }
    terms.retain(|_, coefficient| *coefficient != 0);
    if terms.len() > MAX_LINEAR_TERMS {
        return Err(LogicError::Budget);
    }
    word.terms = terms;
    Ok(())
}

fn resource_value(
    state: &ResourceState,
    definition: &PredicateDefinition,
    resources: &[SealedResource],
    index: u32,
    path: &[u64],
) -> Result<PredicateLogicValue, LogicError> {
    let r = resources.get(index as usize).ok_or(LogicError::Unbound)?;
    let (allocation, pointer) = match path {
        [] => (r.allocation, r.pointer),
        [offset] => {
            let field = definition
                .resource_fields
                .get(index as usize)
                .and_then(|fields| fields.iter().find(|f| f.offset == *offset))
                .ok_or(LogicError::Unbound)?;
            let payload = state
                .bounded_field_payload(r.allocation, field)
                .map_err(|_| LogicError::Unbound)?;
            let AbstractProvenance::Known(allocation) = payload.pointer().provenance() else {
                return Err(LogicError::Unbound);
            };
            (allocation, payload.pointer())
        }
        _ => return Err(LogicError::Unbound),
    };
    let access = pointer.memory_access().ok_or(LogicError::TypeMismatch)?;
    // The enclosing fold has already checked the actual whole owner
    // or unique mutable loan and its live, typed allocation.
    Ok(TypedLogicValue {
        ty: LogicType::Resource(access),
        value: LogicValue::Resource(ResourceWitness {
            allocation,
            pointer,
        }),
    })
}

impl ResourceState {
    fn predicate_result_field(
        &self,
        scope: InstanceScope,
        ty: LogicType<VirMemoryAccess>,
        base: VirValueId,
        offset: u64,
        access: VirMemoryAccess,
        captured: bool,
    ) -> Result<PredicateLogicValue, PredicateError> {
        let (id, range) = self.predicate_memory_location(ty, base, offset)?;
        let allocation = self.allocation(id).ok_or(PredicateError::InvalidBinding)?;
        let offset = range.start();
        let fallback = ObservationAtom::Memory {
            scope,
            allocation: id,
            offset,
            access,
            time: ObservationTime::Current,
            captured,
        };
        let value = match (ty, allocation.scalar_content(range, access)) {
            (LogicType::Bool, Some(AbstractValue::Bool(value))) => observed_bool(
                scope,
                value,
                allocation.bool_origin(range, access),
                Some(fallback),
            ),
            (LogicType::Bool, None) => LogicValue::BoolAtom {
                atom: fallback,
                negated: false,
                known: None,
            },
            (LogicType::U64 | LogicType::Usize, Some(AbstractValue::U64(value))) => {
                LogicValue::Word(
                    observed_word(
                        scope,
                        value,
                        allocation.scalar_origin(range, access),
                        fallback,
                    )
                    .map_err(map_error)?,
                )
            }
            (LogicType::U64 | LogicType::Usize, None) => {
                LogicValue::Word(AffineValue::variable(fallback, 0, u64::MAX).map_err(map_error)?)
            }
            _ => return Err(PredicateError::InvalidBinding),
        };
        Ok(self.refine_predicate_boolean(TypedLogicValue { ty, value }))
    }

    #[expect(
        clippy::too_many_arguments,
        reason = "Keep boundary identities, state, evidence and shared budget explicit at the resource adapter"
    )]
    fn predicate_logic_inputs(
        &self,
        definition: &PredicateDefinition,
        holder: PredicateHolder,
        scope: InstanceScope,
        explicit: &WitnessArguments<VirMemoryAccess, VirValueId>,
        aliases: &BTreeMap<VirValueId, LocalSnapshot>,
        capturing: bool,
        budget: &mut LogicBudget,
    ) -> Result<Vec<PredicateLogicValue>, PredicateError> {
        if explicit.inputs.len() > MAX_LOGIC_PARAMETERS {
            return Err(PredicateError::Budget);
        }
        explicit
            .inputs
            .iter()
            .map(|(ty, id)| {
                let id = match id {
                    WitnessInput::Result(_) => return Err(PredicateError::InvalidBinding),
                    WitnessInput::ResultField {
                        base,
                        offset,
                        access,
                    } => {
                        return self.predicate_result_field(
                            scope, *ty, *base, *offset, *access, capturing,
                        );
                    }
                    WitnessInput::Memory {
                        base,
                        offset,
                        access,
                        time,
                    } => {
                        if *time != ObservationTime::Current {
                            return Err(PredicateError::InvalidBinding);
                        }
                        return self.predicate_observation_view().predicate_result_field(
                            scope, *ty, *base, *offset, *access, capturing,
                        );
                    }
                    WitnessInput::Scalar(id) => id,
                    WitnessInput::Opened {
                        action,
                        holder: source,
                        binder,
                    } => {
                        let instance = self
                            .predicates
                            .get(&PredicateHolder(*source))
                            .ok_or(PredicateError::MissingHolder)?;
                        if *source != holder.0
                            || instance.definition != *definition
                            || instance.folded
                            || instance.opening_action != Some(*action)
                            || instance.logic_scope.is_none()
                        {
                            return Err(PredicateError::InvalidBinding);
                        }
                        let value = instance
                            .logical_witnesses
                            .get(*binder as usize)
                            .ok_or(PredicateError::InvalidBinding)?;
                        if value.ty != *ty {
                            return Err(PredicateError::InvalidBinding);
                        }
                        // A binder input denotes the saved immutable value.
                        // Do not solve its tight numeric range just to copy it:
                        // expression evaluation uses the saved guarantees when
                        // an operation actually needs a definedness proof, and
                        // constraint capture checks the resulting package.
                        value.value.capture_leaves(budget).map_err(map_error)?;
                        let mut value = value.clone();
                        // Refold gets a new logical scope, but a local entry
                        // origin still names the same actual historical input.
                        // Foreign/captured origins cannot be rebound this way.
                        if capturing {
                            rebind_local_origins(&mut value, scope, budget).map_err(map_error)?;
                        }
                        return Ok(self.refine_predicate_boolean(value));
                    }
                };
                self.predicate_scalar_input(scope, *ty, *id, aliases)
            })
            .collect::<Result<Vec<PredicateLogicValue>, PredicateError>>()
    }
    pub(super) fn check_predicate_arguments(
        &self,
        definition: &PredicateDefinition,
        holder: PredicateHolder,
        arguments: &WitnessArguments<VirMemoryAccess, VirValueId>,
    ) -> Result<(), PredicateError> {
        if !arguments.values.is_empty() {
            return Err(PredicateError::InvalidBinding);
        }
        let instance = self
            .predicates
            .get(&holder)
            .ok_or(PredicateError::MissingHolder)?;
        if instance.definition != *definition {
            return Err(PredicateError::WrongDeclaration);
        }
        let mut scope = instance.logic_scope.unwrap_or(InstanceScope {
            declaration: definition.id.get(),
            instance: 0,
            opening: 0,
        });
        // Parameters are snapshots of the fold, unaffected by an unfold epoch.
        scope.opening = 0;
        let mut budget = LogicBudget::default();
        let inputs = self.predicate_logic_inputs(
            definition,
            holder,
            scope,
            arguments,
            &instance.logical_local_aliases,
            false,
            &mut budget,
        )?;
        let context = ExpressionFacts::new(
            self,
            scope,
            &instance.logical_facts,
            arguments,
            &inputs,
            &mut budget,
        )?;
        let actual = self.evaluate_predicate_arguments(
            &definition.logic,
            arguments,
            &inputs,
            &context,
            &mut budget,
        )?;
        if actual.len() != instance.logical_parameters.len() {
            return Err(PredicateError::InvalidBinding);
        }
        for (a, b) in actual.iter().zip(&instance.logical_parameters) {
            if a.ty != b.ty {
                return Err(PredicateError::InvalidBinding);
            }
            if !self.predicate_argument_equality(instance, a.clone(), b.clone(), &mut budget)? {
                return Err(PredicateError::InvalidBinding);
            }
        }
        Ok(())
    }
}
pub(super) fn map_error(error: LogicError) -> PredicateError {
    match error {
        LogicError::Budget => PredicateError::Budget,
        LogicError::Overflow | LogicError::Unproved => PredicateError::UnprovedRepresentation,
        _ => PredicateError::InvalidDefinition,
    }
}

impl From<LogicError> for PredicateError {
    fn from(error: LogicError) -> Self {
        map_error(error)
    }
}
