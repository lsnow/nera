//! Structural validation for the untrusted structured HIR body tree.

use std::collections::{BTreeMap, BTreeSet};

use super::program::{HirBody, HirFunction, HirProgramValidationError, require, validation_error};
use super::resolve::resolve_place_from_locals;
use super::validation::all_unique;
use super::{
    HirBlock, HirExpression, HirExpressionKind, HirFieldInitializer, HirForSource, HirLocalId,
    HirLoopId, HirMatchArm, HirMutability, HirPattern, HirPatternKind, HirPlace, HirPlaceAccess,
    HirPlaceBase, HirProgram, HirProjectionKind, HirRegionId, HirRegionOrigin, HirRegionOwner,
    HirScopeId, HirStatement, HirStatementKind, HirTypeId, HirTypeKind, HirUseMode,
};
use crate::ValueCapability;
use crate::diagnostic::span_contains;

const MAX_BODY_DEPTH: usize = 256;

#[derive(Default)]
struct State {
    proves: BTreeSet<super::HirSpecProveId>,
    next_scope: u32,
    next_loop: u32,
    next_statement: usize,
    owned_locals: BTreeSet<HirLocalId>,
    declared_locals: BTreeSet<HirLocalId>,
    pattern_bindings: BTreeSet<HirLocalId>,
    parameters: BTreeSet<HirLocalId>,
    scope_spans: Vec<crate::ByteSpan>,
}

pub(super) fn validate_body(
    program: &HirProgram,
    function: &HirFunction,
    body: &HirBody,
) -> Result<(), HirProgramValidationError> {
    Validator {
        program,
        body,
        function,
    }
    .validate()
}

struct Validator<'hir> {
    program: &'hir HirProgram,
    body: &'hir HirBody,
    function: &'hir HirFunction,
}

impl Validator<'_> {
    fn validate(&self) -> Result<(), HirProgramValidationError> {
        require(
            self.body.parameters.len() == self.function.signature.parameters.len()
                && all_unique(self.body.parameters.iter().copied()),
            "function",
            self.function.id.index(),
            "parameter locals do not match function signature",
        )?;
        for (local_id, parameter_type) in self
            .body
            .parameters
            .iter()
            .zip(&self.function.signature.parameters)
        {
            require(
                self.body
                    .locals
                    .get(local_id.index())
                    .is_some_and(|local| local.id == *local_id && local.ty == *parameter_type),
                "function",
                self.function.id.index(),
                "parameter local type does not match function signature",
            )?;
        }
        require(
            self.body.root.locals.starts_with(&self.body.parameters),
            "function",
            self.function.id.index(),
            "parameter locals are not the root-scope prefix",
        )?;
        require(
            span_contains(self.function.span, self.body.root.span),
            "function",
            self.function.id.index(),
            "root block span is outside function span",
        )?;

        let mut state = State {
            parameters: self.body.parameters.iter().copied().collect(),
            ..State::default()
        };
        self.validate_block(
            &self.body.root,
            &BTreeSet::new(),
            &[],
            &[],
            None,
            None,
            0,
            &mut state,
        )?;
        require(
            state.owned_locals.len() == self.body.locals.len(),
            "function",
            self.function.id.index(),
            "a local is not owned exactly once by a lexical block",
        )?;
        require(
            self.program
                .specs()
                .proves
                .iter()
                .filter(|p| {
                    p.function == self.function.id
                        && matches!(p.location, super::HirSpecLocation::Statement { .. })
                })
                .all(|p| state.proves.contains(&p.id)),
            "function",
            self.function.id.index(),
            "local Prove lacks a body anchor",
        )?;
        for region in self
            .program
            .regions()
            .iter()
            .filter(|region| region.owner == HirRegionOwner::Function(self.function.id))
        {
            if let Some(scope) = region.origin.lexical_scope() {
                require(
                    state
                        .scope_spans
                        .get(scope.index())
                        .is_some_and(|span| span_contains(*span, region.span)),
                    "region",
                    region.id.index(),
                    "lexical/inferred region scope is missing or does not contain its span",
                )?;
            }
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn validate_block(
        &self,
        block: &HirBlock,
        inherited: &BTreeSet<HirLocalId>,
        active_scopes: &[HirScopeId],
        active_loops: &[HirLoopId],
        entry_pattern: Option<&HirPattern>,
        entry_guard: Option<&HirExpression>,
        depth: usize,
        state: &mut State,
    ) -> Result<(), HirProgramValidationError> {
        require(
            depth < MAX_BODY_DEPTH,
            "scope",
            block.scope.index(),
            "HIR block nesting exceeds validation limit",
        )?;
        let expected_scope = HirScopeId::new(state.next_scope);
        state.next_scope = state.next_scope.checked_add(1).ok_or_else(|| {
            validation_error("scope", block.scope.index(), "too many lexical scopes")
        })?;
        require(
            block.scope == expected_scope,
            "scope",
            block.scope.index(),
            "scope ID does not equal deterministic preorder index",
        )?;
        state.scope_spans.push(block.span);
        let mut visible_scopes = active_scopes.to_vec();
        visible_scopes.push(block.scope);
        require(
            all_unique(block.locals.iter().copied()),
            "scope",
            block.scope.index(),
            "duplicate local in block declaration order",
        )?;

        let mut visible = inherited.clone();
        for id in &block.locals {
            let local = self
                .body
                .locals
                .get(id.index())
                .filter(|local| local.id == *id);
            let declaration_is_contained = local.is_some_and(|local| {
                if state.parameters.contains(id) {
                    span_contains(self.function.span, local.declaration_span)
                } else if entry_pattern.is_some_and(|pattern| Self::pattern_binds(pattern, *id)) {
                    entry_pattern
                        .is_some_and(|pattern| span_contains(pattern.span, local.declaration_span))
                } else {
                    span_contains(block.span, local.declaration_span)
                }
            });
            require(
                local.is_some_and(|local| local.scope == block.scope)
                    && declaration_is_contained
                    && state.owned_locals.insert(*id),
                "scope",
                block.scope.index(),
                "missing, foreign, duplicate, or out-of-span local declaration",
            )?;
            if let Some(local) = local {
                self.require_type_regions_visible(
                    local.ty,
                    &visible_scopes,
                    "local",
                    local.id.index(),
                )?;
            }
            visible.insert(*id);
        }

        if let Some(pattern) = entry_pattern {
            self.validate_pattern(pattern, block.scope, &visible, depth + 1, state)?;
        }
        if let Some(guard) = entry_guard {
            self.validate_expression(
                &visible,
                &visible_scopes,
                state.next_statement,
                guard,
                depth + 1,
            )?;
            require(
                matches!(self.program.type_kind(guard.ty), Some(HirTypeKind::Bool)),
                "expression",
                state.next_statement,
                "match guard is not boolean",
            )?;
        }

        for statement in &block.statements {
            let statement_index = state.next_statement;
            state.next_statement = state.next_statement.checked_add(1).ok_or_else(|| {
                validation_error("statement", statement_index, "too many HIR statements")
            })?;
            require(
                span_contains(block.span, statement.span),
                "statement",
                statement_index,
                "statement span is outside its lexical block",
            )?;
            self.validate_statement(
                block.scope,
                &visible,
                &visible_scopes,
                active_loops,
                statement_index,
                statement,
                depth,
                state,
            )?;
        }
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn validate_statement(
        &self,
        scope: HirScopeId,
        visible: &BTreeSet<HirLocalId>,
        active_scopes: &[HirScopeId],
        active_loops: &[HirLoopId],
        statement_index: usize,
        statement: &HirStatement,
        depth: usize,
        state: &mut State,
    ) -> Result<(), HirProgramValidationError> {
        match &statement.kind {
            HirStatementKind::Prove { prove } => {
                let valid = self
                    .program
                    .specs()
                    .proves
                    .get(prove.index())
                    .is_some_and(|p| {
                        p.function == self.function.id
                            && p.span == statement.span
                            && p.location
                                == (super::HirSpecLocation::Statement {
                                    function: self.function.id,
                                    prove: *prove,
                                })
                            && self
                                .program
                                .specs()
                                .terms
                                .iter()
                                .filter(|t| t.clause == p.clause)
                                .all(|t| match t.kind {
                                    super::HirSpecTermKind::Snapshot(
                                        super::HirSpecSnapshot::Local { function, local },
                                    ) => {
                                        function == self.function.id
                                            && visible.contains(&local)
                                            && (state.declared_locals.contains(&local)
                                                || state.parameters.contains(&local)
                                                || state.pattern_bindings.contains(&local))
                                    }
                                    _ => true,
                                })
                    });
                let resources_visible =
                    self.program
                        .specs()
                        .proves
                        .get(prove.index())
                        .is_some_and(|p| {
                            self.program
                                .specs()
                                .assertions
                                .iter()
                                .filter(|a| a.clause == p.clause)
                                .all(|a| {
                                    a.kind.snapshots().copied().all(|s| match s {
                                        super::HirSpecSnapshot::Local { function, local } => {
                                            function == self.function.id
                                                && visible.contains(&local)
                                                && (state.declared_locals.contains(&local)
                                                    || state.parameters.contains(&local)
                                                    || state.pattern_bindings.contains(&local))
                                        }
                                        _ => false,
                                    })
                                })
                        });
                require(
                    valid && resources_visible && state.proves.insert(*prove),
                    "statement",
                    statement_index,
                    "invalid local Prove anchor or invisible snapshot",
                )
            }
            HirStatementKind::Declare { local } => {
                let definition = self
                    .body
                    .locals
                    .get(local.index())
                    .filter(|candidate| candidate.id == *local);
                require(
                    visible.contains(local)
                        && !state.parameters.contains(local)
                        && !state.pattern_bindings.contains(local)
                        && state.declared_locals.insert(*local)
                        && definition.is_some_and(|definition| {
                            definition.scope == scope
                                && definition.mutable
                                && super::types::supports_deferred_local_shape(
                                    self.program.types(),
                                    self.program.fields(),
                                    definition.ty,
                                )
                                && self
                                    .program
                                    .layouts()
                                    .get(definition.layout.index())
                                    .is_some_and(|layout| (1..=4096).contains(&layout.size_bytes))
                        }),
                    "statement",
                    statement_index,
                    "invalid or unsupported deferred storage declaration",
                )
            }
            HirStatementKind::Let { local, value } => {
                let local_definition = self
                    .body
                    .locals
                    .get(local.index())
                    .filter(|candidate| candidate.id == *local);
                require(
                    visible.contains(local)
                        && local_definition.is_some_and(|local| local.scope == scope)
                        && !state.parameters.contains(local)
                        && !state.pattern_bindings.contains(local)
                        && state.declared_locals.insert(*local),
                    "statement",
                    statement_index,
                    "let target is foreign, special, or initialized more than once",
                )?;
                self.require_statement_span(statement, value.span, statement_index)?;
                self.validate_expression(
                    visible,
                    active_scopes,
                    statement_index,
                    value,
                    depth + 1,
                )?;
                require(
                    local_definition.is_some_and(|local| local.ty == value.ty),
                    "statement",
                    statement_index,
                    "let value type does not match local type",
                )
            }
            HirStatementKind::Assign { destination, value } => {
                self.require_statement_span(statement, destination.span, statement_index)?;
                self.require_statement_span(statement, value.span, statement_index)?;
                let destination_type = self.resolve_place(
                    visible,
                    active_scopes,
                    statement_index,
                    destination,
                    HirPlaceAccess::Write,
                    depth + 1,
                )?;
                self.validate_expression(
                    visible,
                    active_scopes,
                    statement_index,
                    value,
                    depth + 1,
                )?;
                require(
                    self.program.types_compatible(value.ty, destination_type),
                    "statement",
                    statement_index,
                    "assignment value type does not match destination",
                )
            }
            HirStatementKind::Free { pointer } => require(
                visible.contains(pointer)
                    && self.body.locals.get(pointer.index()).is_some_and(|local| {
                        local.id == *pointer
                            && matches!(
                                self.program.type_kind(local.ty),
                                Some(HirTypeKind::Own { .. })
                            )
                    }),
                "statement",
                statement_index,
                "free target is not a visible owner local",
            ),
            HirStatementKind::Return { value } => {
                if let Some(value) = value {
                    self.require_statement_span(statement, value.span, statement_index)?;
                    self.validate_expression(
                        visible,
                        active_scopes,
                        statement_index,
                        value,
                        depth + 1,
                    )?;
                }
                let expects_value = !matches!(
                    self.program.type_kind(self.function.signature.return_type),
                    Some(HirTypeKind::Unit)
                );
                let matches = match value {
                    Some(value) if expects_value => {
                        value.ty == self.function.signature.return_type
                            || (self
                                .program
                                .types_compatible(value.ty, self.function.signature.return_type)
                                && match (
                                    self.program.type_kind(value.ty),
                                    self.program.type_kind(self.function.signature.return_type),
                                ) {
                                    (
                                        Some(HirTypeKind::Reference { region: source, .. }),
                                        Some(HirTypeKind::Reference { region: result, .. }),
                                    ) => {
                                        self.region_is_subregion(*result, *source)
                                            || self.function.signature.borrow_result.is_some_and(
                                                |relation| {
                                                    self.function
                                                        .signature
                                                        .parameters
                                                        .get(relation.parameter as usize)
                                                        .and_then(|ty| {
                                                            match self.program.type_kind(*ty) {
                                                                Some(HirTypeKind::Reference {
                                                                    region,
                                                                    ..
                                                                }) => Some(*region),
                                                                _ => None,
                                                            }
                                                        })
                                                        .is_some_and(|parent| {
                                                            self.region_is_subregion(
                                                                *source, parent,
                                                            )
                                                        })
                                                },
                                            )
                                    }
                                    _ => false,
                                })
                    }
                    None => !expects_value,
                    _ => false,
                };
                require(
                    matches,
                    "statement",
                    statement_index,
                    "return value does not match function return type",
                )
            }
            HirStatementKind::Evaluate { expression } => {
                self.require_statement_span(statement, expression.span, statement_index)?;
                self.validate_expression(
                    visible,
                    active_scopes,
                    statement_index,
                    expression,
                    depth + 1,
                )
            }
            HirStatementKind::Block { block } => {
                self.require_child_span(statement, block, statement_index)?;
                self.validate_block(
                    block,
                    visible,
                    active_scopes,
                    active_loops,
                    None,
                    None,
                    depth + 1,
                    state,
                )
            }
            HirStatementKind::If {
                condition,
                then_block,
                else_block,
            } => {
                self.require_statement_span(statement, condition.span, statement_index)?;
                self.validate_condition(
                    visible,
                    active_scopes,
                    statement_index,
                    condition,
                    depth + 1,
                )?;
                self.require_child_span(statement, then_block, statement_index)?;
                self.validate_block(
                    then_block,
                    visible,
                    active_scopes,
                    active_loops,
                    None,
                    None,
                    depth + 1,
                    state,
                )?;
                if let Some(else_block) = else_block {
                    self.require_child_span(statement, else_block, statement_index)?;
                    self.validate_block(
                        else_block,
                        visible,
                        active_scopes,
                        active_loops,
                        None,
                        None,
                        depth + 1,
                        state,
                    )?;
                }
                Ok(())
            }
            HirStatementKind::While {
                loop_id,
                condition,
                body,
            } => {
                self.validate_loop_id(*loop_id, statement_index, state)?;
                self.require_statement_span(statement, condition.span, statement_index)?;
                self.validate_condition(
                    visible,
                    active_scopes,
                    statement_index,
                    condition,
                    depth + 1,
                )?;
                self.require_child_span(statement, body, statement_index)?;
                let mut loops = active_loops.to_vec();
                loops.push(*loop_id);
                self.validate_block(
                    body,
                    visible,
                    active_scopes,
                    &loops,
                    None,
                    None,
                    depth + 1,
                    state,
                )
            }
            HirStatementKind::For {
                loop_id,
                pattern,
                source,
                body,
            } => {
                self.validate_loop_id(*loop_id, statement_index, state)?;
                self.require_statement_span(statement, pattern.span, statement_index)?;
                match source {
                    HirForSource::IntegerRange { start, end, .. } => {
                        self.require_statement_span(statement, start.span, statement_index)?;
                        self.require_statement_span(statement, end.span, statement_index)?;
                    }
                }
                let item_type = self.validate_for_source(
                    visible,
                    active_scopes,
                    statement_index,
                    source,
                    depth + 1,
                )?;
                require(
                    pattern.ty == item_type && Self::pattern_is_irrefutable(pattern),
                    "statement",
                    statement_index,
                    "for pattern type mismatches or pattern is refutable",
                )?;
                self.require_child_span(statement, body, statement_index)?;
                let mut loops = active_loops.to_vec();
                loops.push(*loop_id);
                self.validate_block(
                    body,
                    visible,
                    active_scopes,
                    &loops,
                    Some(pattern),
                    None,
                    depth + 1,
                    state,
                )
            }
            HirStatementKind::Match { scrutinee, arms } => {
                self.require_statement_span(statement, scrutinee.span, statement_index)?;
                self.validate_expression(
                    visible,
                    active_scopes,
                    statement_index,
                    scrutinee,
                    depth + 1,
                )?;
                require(
                    !arms.is_empty(),
                    "statement",
                    statement_index,
                    "match has no arms",
                )?;
                for arm in arms {
                    self.require_statement_span(statement, arm.span, statement_index)?;
                    self.validate_match_arm(
                        visible,
                        active_scopes,
                        active_loops,
                        statement_index,
                        scrutinee.ty,
                        arm,
                        depth + 1,
                        state,
                    )?;
                }
                require(
                    self.match_has_valid_coverage(scrutinee.ty, arms),
                    "statement",
                    statement_index,
                    "match coverage is non-exhaustive or has unreachable arms",
                )
            }
            HirStatementKind::Break { target } | HirStatementKind::Continue { target } => require(
                active_loops.contains(target),
                "statement",
                statement_index,
                "control-flow target is not an enclosing loop",
            ),
        }
    }

    fn validate_loop_id(
        &self,
        loop_id: HirLoopId,
        statement_index: usize,
        state: &mut State,
    ) -> Result<(), HirProgramValidationError> {
        let expected = HirLoopId::new(state.next_loop);
        state.next_loop = state.next_loop.checked_add(1).ok_or_else(|| {
            validation_error("statement", statement_index, "too many structured loops")
        })?;
        require(
            loop_id == expected,
            "statement",
            statement_index,
            "loop ID does not equal deterministic preorder index",
        )
    }

    fn require_child_span(
        &self,
        statement: &HirStatement,
        block: &HirBlock,
        statement_index: usize,
    ) -> Result<(), HirProgramValidationError> {
        require(
            span_contains(statement.span, block.span),
            "statement",
            statement_index,
            "child block span is outside its control-flow statement",
        )
    }

    fn require_statement_span(
        &self,
        statement: &HirStatement,
        child: crate::ByteSpan,
        statement_index: usize,
    ) -> Result<(), HirProgramValidationError> {
        require(
            span_contains(statement.span, child),
            "statement",
            statement_index,
            "statement operand span is outside its source range",
        )
    }

    fn validate_condition(
        &self,
        visible: &BTreeSet<HirLocalId>,
        active_scopes: &[HirScopeId],
        statement_index: usize,
        condition: &HirExpression,
        depth: usize,
    ) -> Result<(), HirProgramValidationError> {
        self.validate_expression(visible, active_scopes, statement_index, condition, depth)?;
        require(
            matches!(
                self.program.type_kind(condition.ty),
                Some(HirTypeKind::Bool)
            ),
            "statement",
            statement_index,
            "control-flow condition is not boolean",
        )
    }

    fn validate_for_source(
        &self,
        visible: &BTreeSet<HirLocalId>,
        active_scopes: &[HirScopeId],
        statement_index: usize,
        source: &HirForSource,
        depth: usize,
    ) -> Result<HirTypeId, HirProgramValidationError> {
        match source {
            HirForSource::IntegerRange {
                start,
                end,
                item_type,
                ..
            } => {
                self.validate_expression(visible, active_scopes, statement_index, start, depth)?;
                self.validate_expression(visible, active_scopes, statement_index, end, depth)?;
                require(
                    start.ty == *item_type
                        && end.ty == *item_type
                        && matches!(
                            self.program.type_kind(*item_type),
                            Some(HirTypeKind::Integer(_))
                        ),
                    "statement",
                    statement_index,
                    "for range bounds do not share an integer type",
                )?;
                Ok(*item_type)
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn validate_match_arm(
        &self,
        visible: &BTreeSet<HirLocalId>,
        active_scopes: &[HirScopeId],
        active_loops: &[HirLoopId],
        statement_index: usize,
        scrutinee_type: HirTypeId,
        arm: &HirMatchArm,
        depth: usize,
        state: &mut State,
    ) -> Result<(), HirProgramValidationError> {
        require(
            arm.pattern.ty == scrutinee_type
                && span_contains(arm.span, arm.pattern.span)
                && arm
                    .guard
                    .as_ref()
                    .is_none_or(|guard| span_contains(arm.span, guard.span))
                && span_contains(arm.span, arm.body.span),
            "statement",
            statement_index,
            "match arm type or source spans are inconsistent",
        )?;
        self.validate_block(
            &arm.body,
            visible,
            active_scopes,
            active_loops,
            Some(&arm.pattern),
            arm.guard.as_ref(),
            depth,
            state,
        )
    }

    fn validate_pattern(
        &self,
        pattern: &HirPattern,
        binding_scope: HirScopeId,
        visible: &BTreeSet<HirLocalId>,
        depth: usize,
        state: &mut State,
    ) -> Result<(), HirProgramValidationError> {
        require(
            depth < MAX_BODY_DEPTH && self.program.type_definition(pattern.ty).is_some(),
            "pattern",
            binding_scope.index(),
            "pattern nesting exceeds limit or pattern type is missing",
        )?;
        match &pattern.kind {
            HirPatternKind::Wildcard => Ok(()),
            HirPatternKind::Binding { local, mode } => {
                require(
                    visible.contains(local)
                        && self
                            .body
                            .locals
                            .get(local.index())
                            .is_some_and(|definition| {
                                definition.id == *local
                                    && definition.scope == binding_scope
                                    && definition.ty == pattern.ty
                            })
                        && !state.parameters.contains(local)
                        && state.pattern_bindings.insert(*local),
                    "pattern",
                    binding_scope.index(),
                    "pattern binding is missing, foreign, reused, or has the wrong type",
                )?;
                require(
                    canonical_use_mode(self.program, pattern.ty) == Some(*mode),
                    "pattern",
                    binding_scope.index(),
                    "pattern binding use mode does not match canonical type capability",
                )
            }
            HirPatternKind::Integer(_) => require(
                matches!(
                    self.program.type_kind(pattern.ty),
                    Some(HirTypeKind::Integer(_))
                ),
                "pattern",
                binding_scope.index(),
                "integer pattern has a non-integer type",
            ),
            HirPatternKind::Bool(_) => require(
                matches!(self.program.type_kind(pattern.ty), Some(HirTypeKind::Bool)),
                "pattern",
                binding_scope.index(),
                "boolean pattern has a non-boolean type",
            ),
            HirPatternKind::Tuple(patterns) => {
                let Some(HirTypeKind::Tuple(types)) = self.program.type_kind(pattern.ty) else {
                    return require(
                        false,
                        "pattern",
                        binding_scope.index(),
                        "tuple pattern has a non-tuple type",
                    );
                };
                require(
                    patterns.len() == types.len(),
                    "pattern",
                    binding_scope.index(),
                    "tuple pattern arity does not match its type",
                )?;
                for (child, ty) in patterns.iter().zip(types) {
                    require(
                        child.ty == *ty && span_contains(pattern.span, child.span),
                        "pattern",
                        binding_scope.index(),
                        "tuple child pattern type or span is inconsistent",
                    )?;
                    self.validate_pattern(child, binding_scope, visible, depth + 1, state)?;
                }
                Ok(())
            }
            HirPatternKind::Variant { variant, fields } => {
                let definition = self.program.variant(*variant);
                require(
                    definition.is_some_and(|variant| {
                        variant.owner == pattern.ty && variant.fields.len() == fields.len()
                    }),
                    "pattern",
                    binding_scope.index(),
                    "variant pattern does not belong to its type or has the wrong arity",
                )?;
                let definition = definition.expect("validated variant remains present");
                for (child, field) in fields.iter().zip(&definition.fields) {
                    let field_type = self.program.field(*field).map(|field| field.ty);
                    require(
                        field_type == Some(child.ty) && span_contains(pattern.span, child.span),
                        "pattern",
                        binding_scope.index(),
                        "variant field pattern type or span is inconsistent",
                    )?;
                    self.validate_pattern(child, binding_scope, visible, depth + 1, state)?;
                }
                Ok(())
            }
        }
    }

    fn pattern_is_irrefutable(pattern: &HirPattern) -> bool {
        match &pattern.kind {
            HirPatternKind::Wildcard | HirPatternKind::Binding { .. } => true,
            HirPatternKind::Tuple(patterns) => patterns.iter().all(Self::pattern_is_irrefutable),
            HirPatternKind::Integer(_)
            | HirPatternKind::Bool(_)
            | HirPatternKind::Variant { .. } => false,
        }
    }

    fn pattern_binds(pattern: &HirPattern, local: HirLocalId) -> bool {
        match &pattern.kind {
            HirPatternKind::Binding {
                local: candidate, ..
            } => *candidate == local,
            HirPatternKind::Tuple(patterns) => patterns
                .iter()
                .any(|pattern| Self::pattern_binds(pattern, local)),
            HirPatternKind::Variant { fields, .. } => fields
                .iter()
                .any(|pattern| Self::pattern_binds(pattern, local)),
            HirPatternKind::Wildcard | HirPatternKind::Integer(_) | HirPatternKind::Bool(_) => {
                false
            }
        }
    }

    fn match_has_valid_coverage(&self, ty: HirTypeId, arms: &[HirMatchArm]) -> bool {
        let mut covered_false = false;
        let mut covered_true = false;
        let mut covered_variants = BTreeSet::new();
        let mut exhaustive = false;
        for arm in arms {
            if exhaustive {
                return false;
            }
            if arm.guard.is_some() {
                continue;
            }
            match &arm.pattern.kind {
                _ if Self::pattern_is_irrefutable(&arm.pattern) => exhaustive = true,
                HirPatternKind::Bool(false) => covered_false = true,
                HirPatternKind::Bool(true) => covered_true = true,
                HirPatternKind::Variant { variant, fields }
                    if fields.iter().all(Self::pattern_is_irrefutable) =>
                {
                    covered_variants.insert(*variant);
                }
                HirPatternKind::Integer(_)
                | HirPatternKind::Tuple(_)
                | HirPatternKind::Variant { .. }
                | HirPatternKind::Wildcard
                | HirPatternKind::Binding { .. } => {}
            }
            exhaustive |= match self.program.type_kind(ty) {
                Some(HirTypeKind::Bool) => covered_false && covered_true,
                Some(HirTypeKind::Enum { variants }) => variants
                    .iter()
                    .all(|variant| covered_variants.contains(variant)),
                _ => false,
            };
        }
        exhaustive
    }

    fn validate_expression(
        &self,
        visible: &BTreeSet<HirLocalId>,
        active_scopes: &[HirScopeId],
        statement_index: usize,
        expression: &HirExpression,
        depth: usize,
    ) -> Result<(), HirProgramValidationError> {
        require(
            depth < MAX_BODY_DEPTH && self.program.type_definition(expression.ty).is_some(),
            "expression",
            statement_index,
            "HIR expression nesting exceeds limit or expression type is missing",
        )?;
        self.require_type_regions_visible(
            expression.ty,
            active_scopes,
            "expression",
            statement_index,
        )?;
        match &expression.kind {
            HirExpressionKind::Unit => require(
                matches!(
                    self.program.type_kind(expression.ty),
                    Some(HirTypeKind::Unit)
                ),
                "expression",
                statement_index,
                "unit expression has a non-unit type",
            ),
            HirExpressionKind::Integer(_) => require(
                matches!(
                    self.program.type_kind(expression.ty),
                    Some(HirTypeKind::Integer(_))
                ),
                "expression",
                statement_index,
                "integer expression has a non-integer type",
            ),
            HirExpressionKind::Bool(_) => require(
                matches!(
                    self.program.type_kind(expression.ty),
                    Some(HirTypeKind::Bool)
                ),
                "expression",
                statement_index,
                "boolean expression has a non-boolean type",
            ),
            HirExpressionKind::TupleConstructor { elements } => {
                let Some(HirTypeKind::Tuple(element_types)) = self.program.type_kind(expression.ty)
                else {
                    return require(
                        false,
                        "expression",
                        statement_index,
                        "tuple constructor has a non-tuple type",
                    );
                };
                require(
                    self.is_supported_aggregate(expression.ty)
                        && elements.len() == element_types.len(),
                    "expression",
                    statement_index,
                    "tuple constructor arity or aggregate capability is invalid",
                )?;
                for (element, expected) in elements.iter().zip(element_types) {
                    self.validate_constructor_operand(
                        visible,
                        active_scopes,
                        statement_index,
                        expression,
                        element,
                        *expected,
                        depth,
                    )?;
                }
                Ok(())
            }
            HirExpressionKind::ArrayConstructor { elements } => {
                let Some(HirTypeKind::Array {
                    element: element_type,
                    length,
                }) = self.program.type_kind(expression.ty)
                else {
                    return require(
                        false,
                        "expression",
                        statement_index,
                        "array constructor has a non-array type",
                    );
                };
                require(
                    self.is_supported_aggregate(expression.ty)
                        && u64::try_from(elements.len()) == Ok(*length),
                    "expression",
                    statement_index,
                    "array constructor length or aggregate capability is invalid",
                )?;
                for element in elements {
                    self.validate_constructor_operand(
                        visible,
                        active_scopes,
                        statement_index,
                        expression,
                        element,
                        *element_type,
                        depth,
                    )?;
                }
                Ok(())
            }
            HirExpressionKind::ArrayRepeatConstructor { value, length } => {
                let Some(HirTypeKind::Array {
                    element: element_type,
                    length: expected_length,
                }) = self.program.type_kind(expression.ty)
                else {
                    return require(
                        false,
                        "expression",
                        statement_index,
                        "array repetition has a non-array type",
                    );
                };
                require(
                    self.is_pointer_free_aggregate(expression.ty) && length == expected_length,
                    "expression",
                    statement_index,
                    "array repetition length or aggregate capability is invalid",
                )?;
                self.validate_constructor_operand(
                    visible,
                    active_scopes,
                    statement_index,
                    expression,
                    value,
                    *element_type,
                    depth,
                )
            }
            HirExpressionKind::StructConstructor { fields } => {
                let Some(HirTypeKind::Struct {
                    fields: expected_fields,
                }) = self.program.type_kind(expression.ty)
                else {
                    return require(
                        false,
                        "expression",
                        statement_index,
                        "struct constructor has a non-struct type",
                    );
                };
                self.validate_field_constructor(
                    visible,
                    active_scopes,
                    statement_index,
                    expression,
                    fields,
                    expected_fields,
                    depth,
                )
            }
            HirExpressionKind::EnumConstructor { variant, fields } => {
                let Some(HirTypeKind::Enum { variants }) = self.program.type_kind(expression.ty)
                else {
                    return require(
                        false,
                        "expression",
                        statement_index,
                        "enum constructor has a non-enum type",
                    );
                };
                let definition = self.program.variant(*variant);
                require(
                    variants.contains(variant)
                        && definition.is_some_and(|variant| variant.owner == expression.ty),
                    "expression",
                    statement_index,
                    "enum constructor variant does not belong to its result type",
                )?;
                self.validate_field_constructor(
                    visible,
                    active_scopes,
                    statement_index,
                    expression,
                    fields,
                    &definition
                        .expect("validated enum variant remains present")
                        .fields,
                    depth,
                )
            }
            HirExpressionKind::PointerDistance { begin, end } => {
                require(
                    matches!(
                        self.program.type_kind(expression.ty),
                        Some(HirTypeKind::Integer(super::HirIntegerType::Usize))
                    ) && matches!((self.program.type_kind(begin.ty), self.program.type_kind(end.ty)), (Some(HirTypeKind::RawPointer { pointee: a, .. }), Some(HirTypeKind::RawPointer { pointee: b, .. })) if a == b)
                        && span_contains(expression.span, begin.span)
                        && span_contains(expression.span, end.span),
                    "expression",
                    statement_index,
                    "pointer distance operand types, result type, or spans are inconsistent",
                )?;
                self.validate_expression(
                    visible,
                    active_scopes,
                    statement_index,
                    begin,
                    depth + 1,
                )?;
                self.validate_expression(visible, active_scopes, statement_index, end, depth + 1)
            }
            HirExpressionKind::Compare {
                left,
                right,
                operation_span,
                ..
            } => {
                require(
                    matches!(
                        self.program.type_kind(expression.ty),
                        Some(HirTypeKind::Bool)
                    ) && ((left.ty == right.ty
                        && matches!(
                            self.program.type_kind(left.ty),
                            Some(HirTypeKind::Integer(_))
                        ))
                        || matches!((self.program.type_kind(left.ty), self.program.type_kind(right.ty)), (Some(HirTypeKind::RawPointer { pointee: a, .. }), Some(HirTypeKind::RawPointer { pointee: b, .. })) if a == b))
                        && span_contains(expression.span, left.span)
                        && span_contains(expression.span, right.span)
                        && span_contains(expression.span, *operation_span),
                    "expression",
                    statement_index,
                    "comparison operand types, result type, or spans are inconsistent",
                )?;
                self.validate_expression(visible, active_scopes, statement_index, left, depth + 1)?;
                self.validate_expression(visible, active_scopes, statement_index, right, depth + 1)
            }
            HirExpressionKind::WordAdd {
                operands,
                operation_spans,
            } => {
                require(
                    operands.len() >= 2
                        && operation_spans.len() + 1 == operands.len()
                        && matches!(
                            self.program.type_kind(expression.ty),
                            Some(HirTypeKind::Integer(_))
                        ),
                    "expression",
                    statement_index,
                    "word addition shape or result type is invalid",
                )?;
                for operand in operands {
                    require(
                        operand.ty == expression.ty && span_contains(expression.span, operand.span),
                        "expression",
                        statement_index,
                        "word-add operand type or span is inconsistent",
                    )?;
                    self.validate_expression(
                        visible,
                        active_scopes,
                        statement_index,
                        operand,
                        depth + 1,
                    )?;
                }
                require(
                    operation_spans
                        .iter()
                        .all(|span| span_contains(expression.span, *span)),
                    "expression",
                    statement_index,
                    "word-add operation span is outside expression span",
                )
            }
            HirExpressionKind::PointerOffset { base, offsets } => {
                require(
                    span_contains(expression.span, base.span)
                        && offsets
                            .iter()
                            .all(|offset| span_contains(expression.span, offset.span)),
                    "expression",
                    statement_index,
                    "pointer-offset child span is outside expression span",
                )?;
                self.validate_expression(visible, active_scopes, statement_index, base, depth + 1)
            }
            HirExpressionKind::Allocate {
                element_type,
                element_count,
                size_bytes,
                alignment,
            } => require(
                super::types::supports_builtin_allocation(
                    self.program.types(),
                    self.program.fields(),
                    self.program.variants(),
                    *element_type,
                    *element_count,
                ) && self
                    .program
                    .type_definition(*element_type)
                    .and_then(|ty| ty.layout)
                    .and_then(|id| self.program.layouts().get(id.index()))
                    .is_some_and(|layout| {
                        element_count.checked_mul(layout.size_bytes) == Some(*size_bytes)
                            && *alignment == layout.alignment
                            && (matches!(
                                self.program.type_kind(*element_type),
                                Some(HirTypeKind::Integer(super::HirIntegerType::U64))
                            ) || (1..=4096).contains(&layout.size_bytes))
                    })
                    && matches!(
                        self.program.type_kind(expression.ty),
                        Some(HirTypeKind::Own { pointee }) if pointee == element_type
                    ),
                "expression",
                statement_index,
                "allocation element or result type is inconsistent",
            ),
            HirExpressionKind::Length { place } => {
                let ty = self.resolve_place(
                    visible,
                    active_scopes,
                    statement_index,
                    place,
                    HirPlaceAccess::Read,
                    depth + 1,
                )?;
                let ty = match self.program.type_kind(ty) {
                    Some(HirTypeKind::Reference { pointee, .. }) => *pointee,
                    _ => ty,
                };
                require(
                    matches!(
                        self.program.type_kind(ty),
                        Some(HirTypeKind::Array { .. } | HirTypeKind::Slice { .. })
                    ) && matches!(
                        self.program.type_kind(expression.ty),
                        Some(HirTypeKind::Integer(super::HirIntegerType::Usize))
                    ) && span_contains(expression.span, place.span),
                    "expression",
                    statement_index,
                    "length requires array/slice metadata and usize result",
                )
            }
            HirExpressionKind::OwnerAddress { place } => {
                let place_type = self.resolve_place(
                    visible,
                    active_scopes,
                    statement_index,
                    place,
                    HirPlaceAccess::Read,
                    depth + 1,
                )?;
                require(
                    matches!(
                        (self.program.type_kind(place_type), self.program.type_kind(expression.ty)),
                        (
                            Some(HirTypeKind::Own { pointee: owner_pointee }),
                            Some(HirTypeKind::RawPointer {
                                pointee: raw_pointee,
                                mutability: HirMutability::Mutable,
                            }),
                        ) if owner_pointee == raw_pointee
                    ) && span_contains(expression.span, place.span),
                    "expression",
                    statement_index,
                    "owner address result does not match the owner pointee type",
                )
            }
            HirExpressionKind::Read { place, mode } => {
                require(
                    span_contains(expression.span, place.span),
                    "expression",
                    statement_index,
                    "read place span is outside expression span",
                )?;
                let place_type = self.resolve_place(
                    visible,
                    active_scopes,
                    statement_index,
                    place,
                    HirPlaceAccess::Read,
                    depth + 1,
                )?;
                require(
                    place_type == expression.ty,
                    "expression",
                    statement_index,
                    "read result type does not match place type",
                )?;
                require(
                    canonical_use_mode(self.program, expression.ty) == Some(*mode),
                    "expression",
                    statement_index,
                    "read use mode does not match canonical type capability",
                )
            }
            HirExpressionKind::Borrow {
                place,
                mutability,
                region,
            } => {
                require(
                    span_contains(expression.span, place.span),
                    "expression",
                    statement_index,
                    "borrowed place span is outside expression span",
                )?;
                let access = if *mutability == HirMutability::Mutable {
                    HirPlaceAccess::Write
                } else {
                    HirPlaceAccess::Read
                };
                let place_type = self.resolve_place(
                    visible,
                    active_scopes,
                    statement_index,
                    place,
                    access,
                    depth + 1,
                )?;
                require(
                    self.region_is_visible(*region, active_scopes),
                    "expression",
                    statement_index,
                    "borrow region is missing, foreign, or outside its lexical scope",
                )?;
                require(
                    self.program.type_kind(expression.ty)
                        == Some(&HirTypeKind::Reference {
                            pointee: place_type,
                            mutability: *mutability,
                            region: *region,
                        }),
                    "expression",
                    statement_index,
                    "borrow result type does not match place, mutability, and region",
                )?;
                let HirPlaceBase::Local(base) = place.base;
                let parent_region = self
                    .body
                    .locals
                    .get(base.index())
                    .filter(|local| local.id == base)
                    .and_then(|local| match self.program.type_kind(local.ty) {
                        Some(HirTypeKind::Reference { region, .. })
                            if matches!(
                                place.projections.first().map(|projection| &projection.kind),
                                Some(HirProjectionKind::Dereference)
                            ) =>
                        {
                            Some(*region)
                        }
                        _ => None,
                    });
                require(
                    parent_region.is_none_or(|parent| self.region_is_subregion(*region, parent)),
                    "expression",
                    statement_index,
                    "reborrow region is not constrained to its explicit dereference parent",
                )
            }
            HirExpressionKind::RawAddress { place, mutability } => {
                require(
                    span_contains(expression.span, place.span),
                    "expression",
                    statement_index,
                    "addressed place span is outside expression span",
                )?;
                let access = if *mutability == HirMutability::Mutable {
                    HirPlaceAccess::Write
                } else {
                    HirPlaceAccess::Read
                };
                let place_type = self.resolve_place(
                    visible,
                    active_scopes,
                    statement_index,
                    place,
                    access,
                    depth + 1,
                )?;
                require(
                    self.program.type_kind(expression.ty)
                        == Some(&HirTypeKind::RawPointer {
                            pointee: place_type,
                            mutability: *mutability,
                        }),
                    "expression",
                    statement_index,
                    "raw address result type does not match place and mutability",
                )
            }
            HirExpressionKind::Call(call) => {
                let callee = self.program.function_by_id(call.callee);
                require(
                    callee.is_some_and(|callee| {
                        callee.signature == call.instantiated_signature
                            && callee.contract == call.contract
                            && callee.signature.calling_convention == call.calling_convention
                            && self
                                .program
                                .call_result_type_compatible(call, expression.ty)
                            && callee.generic_parameters.is_empty()
                            && callee.body.is_some()
                    }) && call.arguments.len() == call.instantiated_signature.parameters.len(),
                    "expression",
                    statement_index,
                    "direct call target, contract, convention, or signature is inconsistent",
                )?;
                for (argument, expected) in call
                    .arguments
                    .iter()
                    .zip(&call.instantiated_signature.parameters)
                {
                    require(
                        self.program.reference_compatible(argument.ty, *expected)
                            && span_contains(expression.span, argument.span),
                        "expression",
                        statement_index,
                        "direct call argument type or span is inconsistent",
                    )?;
                    self.validate_expression(
                        visible,
                        active_scopes,
                        statement_index,
                        argument,
                        depth + 1,
                    )?;
                }
                let region = |ty| match self.program.type_definition(ty).map(|t| &t.kind) {
                    Some(HirTypeKind::Reference { region, .. }) => Some(*region),
                    _ => None,
                };
                let substitution: BTreeMap<_, _> = call
                    .instantiated_signature
                    .parameters
                    .iter()
                    .zip(&call.arguments)
                    .filter_map(|(p, a)| Some((region(*p)?, region(a.ty)?)))
                    .collect();
                for constraint in self
                    .program
                    .region_constraints()
                    .iter()
                    .filter(|c| c.owner == call.callee)
                {
                    let (Some(sub), Some(sup)) = (
                        substitution.get(&constraint.subregion),
                        substitution.get(&constraint.superregion),
                    ) else {
                        continue;
                    };
                    require(
                        self.region_is_subregion(*sub, *sup),
                        "expression",
                        statement_index,
                        "call region substitution is not established by caller regions",
                    )?;
                }
                Ok(())
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn validate_constructor_operand(
        &self,
        visible: &BTreeSet<HirLocalId>,
        active_scopes: &[HirScopeId],
        statement_index: usize,
        parent: &HirExpression,
        operand: &HirExpression,
        expected_type: HirTypeId,
        depth: usize,
    ) -> Result<(), HirProgramValidationError> {
        require(
            self.program.types_compatible(operand.ty, expected_type)
                && span_contains(parent.span, operand.span),
            "expression",
            statement_index,
            "constructor operand type or source span is inconsistent",
        )?;
        self.validate_expression(visible, active_scopes, statement_index, operand, depth + 1)
    }

    #[allow(clippy::too_many_arguments)]
    fn validate_field_constructor(
        &self,
        visible: &BTreeSet<HirLocalId>,
        active_scopes: &[HirScopeId],
        statement_index: usize,
        parent: &HirExpression,
        fields: &[HirFieldInitializer],
        expected_fields: &[super::HirFieldId],
        depth: usize,
    ) -> Result<(), HirProgramValidationError> {
        let actual = fields
            .iter()
            .map(|field| field.field)
            .collect::<BTreeSet<_>>();
        let expected = expected_fields.iter().copied().collect::<BTreeSet<_>>();
        require(
            self.is_supported_aggregate(parent.ty)
                && actual.len() == fields.len()
                && actual == expected,
            "expression",
            statement_index,
            "constructor fields are missing, duplicated, foreign, or nontrivial",
        )?;
        for initializer in fields {
            let field = self.program.field(initializer.field);
            require(
                field.is_some_and(|field| {
                    field.owner == parent.ty
                        || self.field_belongs_to_enum(parent.ty, initializer.field)
                }),
                "expression",
                statement_index,
                "constructor field does not belong to its result type",
            )?;
            self.validate_constructor_operand(
                visible,
                active_scopes,
                statement_index,
                parent,
                &initializer.value,
                field
                    .expect("validated constructor field remains present")
                    .ty,
                depth,
            )?;
        }
        Ok(())
    }

    fn field_belongs_to_enum(&self, owner: HirTypeId, field: super::HirFieldId) -> bool {
        matches!(self.program.type_kind(owner), Some(HirTypeKind::Enum { variants }) if variants
            .iter()
            .filter_map(|variant| self.program.variant(*variant))
            .any(|variant| variant.fields.contains(&field)))
    }

    fn is_pointer_free_aggregate(&self, root: HirTypeId) -> bool {
        matches!(
            self.program.type_kind(root),
            Some(
                HirTypeKind::Array { .. }
                    | HirTypeKind::Tuple(_)
                    | HirTypeKind::Struct { .. }
                    | HirTypeKind::Enum { .. }
            )
        ) && self
            .program
            .type_capabilities(root)
            .is_some_and(crate::TypeCapabilities::pointer_free_trivial)
    }

    fn is_supported_aggregate(&self, root: HirTypeId) -> bool {
        matches!(
            self.program.type_kind(root),
            Some(
                HirTypeKind::Array { .. }
                    | HirTypeKind::Tuple(_)
                    | HirTypeKind::Struct { .. }
                    | HirTypeKind::Enum { .. }
            )
        ) && self.is_supported_value(root, &mut BTreeSet::new(), 0)
    }

    fn is_supported_value(
        &self,
        ty: HirTypeId,
        visiting: &mut BTreeSet<HirTypeId>,
        depth: usize,
    ) -> bool {
        if depth >= crate::TYPE_CAPABILITY_MAX_DEPTH || !visiting.insert(ty) {
            return false;
        }
        let supported = match self.program.type_kind(ty) {
            Some(
                HirTypeKind::Unit
                | HirTypeKind::Bool
                | HirTypeKind::Integer(_)
                | HirTypeKind::Own { .. }
                | HirTypeKind::Reference { .. },
            ) => true,
            Some(HirTypeKind::Array { element, .. }) => {
                self.is_supported_value(*element, visiting, depth + 1)
            }
            Some(HirTypeKind::Tuple(elements)) => elements
                .iter()
                .all(|element| self.is_supported_value(*element, visiting, depth + 1)),
            Some(HirTypeKind::Struct { fields }) => fields.iter().all(|field| {
                self.program
                    .field(*field)
                    .is_some_and(|field| self.is_supported_value(field.ty, visiting, depth + 1))
            }),
            Some(HirTypeKind::Enum { variants }) => variants.iter().all(|variant| {
                self.program.variant(*variant).is_some_and(|variant| {
                    variant.fields.iter().all(|field| {
                        self.program.field(*field).is_some_and(|field| {
                            self.is_supported_value(field.ty, visiting, depth + 1)
                        })
                    })
                })
            }),
            Some(
                HirTypeKind::RawPointer { .. }
                | HirTypeKind::Slice { .. }
                | HirTypeKind::Function(_)
                | HirTypeKind::GenericParameter(_)
                | HirTypeKind::Never,
            )
            | None => false,
        };
        visiting.remove(&ty);
        supported
    }

    fn region_is_visible(&self, region: HirRegionId, active_scopes: &[HirScopeId]) -> bool {
        self.program
            .region(region)
            .is_some_and(|region| match (region.owner, region.origin) {
                (HirRegionOwner::Type(_), HirRegionOrigin::AggregateErased) => true,
                (
                    HirRegionOwner::Function(owner),
                    HirRegionOrigin::Parameter { .. } | HirRegionOrigin::Result,
                ) => owner == self.function.id,
                (
                    HirRegionOwner::Function(owner),
                    HirRegionOrigin::LexicalScope { scope } | HirRegionOrigin::Inferred { scope },
                ) => owner == self.function.id && active_scopes.contains(&scope),
                _ => false,
            })
    }

    fn region_is_subregion(&self, subregion: HirRegionId, superregion: HirRegionId) -> bool {
        self.program
            .region_is_subregion(self.function.id, subregion, superregion)
    }

    fn require_type_regions_visible(
        &self,
        ty: HirTypeId,
        active_scopes: &[HirScopeId],
        table: &'static str,
        index: usize,
    ) -> Result<(), HirProgramValidationError> {
        let regions = self.program.type_borrow_regions(ty);
        require(
            regions.is_some_and(|regions| {
                regions
                    .iter()
                    .all(|region| self.region_is_visible(*region, active_scopes))
            }),
            table,
            index,
            "type contains a borrow region that is not visible in this lexical scope",
        )
    }

    fn resolve_place(
        &self,
        visible: &BTreeSet<HirLocalId>,
        active_scopes: &[HirScopeId],
        statement_index: usize,
        place: &HirPlace,
        access: HirPlaceAccess,
        depth: usize,
    ) -> Result<HirTypeId, HirProgramValidationError> {
        require(
            depth < MAX_BODY_DEPTH,
            "place",
            statement_index,
            "HIR place nesting exceeds validation limit",
        )?;
        let HirPlaceBase::Local(base) = place.base;
        require(
            visible.contains(&base),
            "place",
            statement_index,
            "place base local is outside its lexical scope",
        )?;
        let resolved = resolve_place_from_locals(self.program, &self.body.locals, place, access)
            .map_err(|error| validation_error("place", statement_index, error.problem()))?;
        for projection in &place.projections {
            match &projection.kind {
                HirProjectionKind::DynamicIndex { index } => {
                    self.validate_expression(
                        visible,
                        active_scopes,
                        statement_index,
                        index,
                        depth + 1,
                    )?;
                }
                HirProjectionKind::Slice { start, end } => {
                    for bound in start.iter().chain(end) {
                        self.validate_expression(
                            visible,
                            active_scopes,
                            statement_index,
                            bound,
                            depth + 1,
                        )?;
                    }
                }
                HirProjectionKind::Dereference
                | HirProjectionKind::Field { .. }
                | HirProjectionKind::TupleElement { .. }
                | HirProjectionKind::ConstantIndex { .. }
                | HirProjectionKind::Downcast { .. } => {}
            }
        }
        Ok(resolved.ty)
    }
}

fn canonical_use_mode(program: &HirProgram, ty: HirTypeId) -> Option<HirUseMode> {
    match program.type_capabilities(ty)?.value {
        ValueCapability::Copy => Some(HirUseMode::Copy),
        ValueCapability::MoveOnly => Some(HirUseMode::Move),
    }
}
