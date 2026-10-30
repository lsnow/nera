//! Closed, pre-HIR inference for bounded borrow results.
//!
//! It follows direct parameter/local forwarding, fixed field and affine slice
//! projections, closed calls, the bounded 7.8.3.4 boolean-guard domain, and a
//! finite structural fixed point for loops and recursive call SCCs. These
//! candidates are not proof facts: canonical VIR verification still checks all
//! body accesses, permissions, resources and recursive summaries independently.

use super::lifetimes::SignatureDraft;
use super::*;
use crate::frontend::{
    AstExpression, AstExpressionKind, AstFunction, AstPlace, AstPlaceProjection,
};
use crate::{
    MAX_BORROW_RESULT_ALTERNATIVES, MAX_BORROW_RESULT_GUARD_ATOMS,
    MAX_BORROW_SOURCE_FIXPOINT_ITERATIONS, MAX_BORROW_SOURCE_RELATIONS,
    MAX_BORROW_SOURCE_SCC_FUNCTIONS,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum InferredBorrowSource {
    Unconditional(crate::BorrowResultRelation),
    Conditional(Vec<crate::BorrowResultAlternative>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct BorrowOrigin {
    parameter: u32,
    field: Option<u32>,
    projection: crate::BorrowProjection,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Origin {
    /// The analyzed path cannot return normally. This is the lattice bottom,
    /// not an inferred source and never escapes into HIR.
    NoNormalReturn,
    Parameter(BorrowOrigin),
    /// Inline shape, in canonical layout order; scalar leaves are NotBorrow.
    Aggregate(Vec<(String, Origin)>),
    LocalStorage,
    NotBorrow,
    Projection,
    Deferred,
    Conflict,
}

impl Origin {
    fn within_budget(&self) -> bool {
        let mut pending = vec![(self, 0usize)];
        let mut nodes = 0usize;
        let mut references = 0usize;
        while let Some((value, depth)) = pending.pop() {
            nodes += 1;
            if nodes > 4096 || depth > 16 {
                return false;
            }
            match value {
                Self::Aggregate(fields) => {
                    if fields.len() > 4096 - pending.len() {
                        return false;
                    }
                    pending.extend(fields.iter().map(|(_, v)| (v, depth + 1)));
                }
                Self::NotBorrow => {}
                _ => {
                    references += 1;
                    if references > 256 {
                        return false;
                    }
                }
            }
        }
        true
    }

    fn reference_leaves<'a>(&'a self, out: &mut Vec<&'a Origin>) {
        match self {
            Self::Aggregate(fields) => {
                for (_, value) in fields {
                    value.reference_leaves(out);
                }
            }
            Self::NotBorrow => {}
            _ => out.push(self),
        }
    }
    fn join(self, other: Self) -> Self {
        match (self, other) {
            (left, right) if left == right => left,
            (Self::Parameter(left), Self::Parameter(right))
                if left.parameter == right.parameter && left.field == right.field =>
            {
                // Different selections of one canonical array are one source,
                // with a checked returned pointer/length instead of guessed
                // entry bounds. Different parameters/fields remain conflicts.
                match join_array_views(left.projection, right.projection) {
                    Some(projection) => Self::Parameter(BorrowOrigin { projection, ..left }),
                    None => Self::Conflict,
                }
            }
            (Self::Aggregate(left), Self::Aggregate(right))
                if left.len() == right.len()
                    && left.iter().zip(&right).all(|(a, b)| a.0 == b.0) =>
            {
                Self::Aggregate(
                    left.into_iter()
                        .zip(right)
                        .map(|((key, a), (_, b))| (key, a.join(b)))
                        .collect(),
                )
            }
            (Self::NoNormalReturn, right) => right,
            (left, Self::NoNormalReturn) => left,
            (Self::Deferred, _) | (_, Self::Deferred) => Self::Deferred,
            (Self::Conflict, _) | (_, Self::Conflict) => Self::Conflict,
            (Self::Projection, _) | (_, Self::Projection) => Self::Projection,
            (Self::LocalStorage, Self::LocalStorage) => Self::LocalStorage,
            _ => Self::Conflict,
        }
    }
}

fn join_array_views(
    left: crate::BorrowProjection,
    right: crate::BorrowProjection,
) -> Option<crate::BorrowProjection> {
    use crate::{BorrowProjection::ArraySlice, BorrowSliceBound};
    let (
        ArraySlice {
            offset_bytes,
            length,
            stride_bytes,
            start,
            ..
        },
        ArraySlice {
            offset_bytes: other_offset,
            length: other_length,
            stride_bytes: other_stride,
            start: other_start,
            ..
        },
    ) = (left, right)
    else {
        return None;
    };
    if (offset_bytes, length, stride_bytes) != (other_offset, other_length, other_stride) {
        return None;
    }
    Some(ArraySlice {
        offset_bytes,
        length,
        stride_bytes,
        start: if start == other_start {
            start
        } else {
            BorrowSliceBound::ReturnedOffset
        },
        end: BorrowSliceBound::ReturnedLength,
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Environment(Vec<BTreeMap<String, Origin>>);

impl Environment {
    fn new(function: &AstFunction) -> Self {
        Self(vec![
            function
                .parameters
                .iter()
                .enumerate()
                .map(|(index, parameter)| {
                    (
                        parameter.name.clone(),
                        Origin::Parameter(BorrowOrigin {
                            parameter: index as u32,
                            field: None,
                            projection: crate::BorrowProjection::Whole,
                        }),
                    )
                })
                .collect(),
        ])
    }

    fn lookup(&self, name: &str) -> Origin {
        self.0
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).cloned())
            .unwrap_or(Origin::NotBorrow)
    }

    fn insert(&mut self, name: &str, origin: Origin) {
        self.0
            .last_mut()
            .expect("borrow inference always has a root scope")
            .insert(name.to_owned(), origin);
    }

    fn assign(&mut self, name: &str, origin: Origin) {
        if let Some(scope) = self
            .0
            .iter_mut()
            .rev()
            .find(|scope| scope.contains_key(name))
        {
            scope.insert(name.to_owned(), origin);
        }
    }

    fn merge(&mut self, other: &Self) {
        for (scope, other_scope) in self.0.iter_mut().zip(&other.0) {
            for (name, origin) in scope.iter_mut() {
                if let Some(other) = other_scope.get(name) {
                    *origin = origin.clone().join(other.clone());
                }
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct BlockResult {
    returned: Option<Origin>,
    continues: bool,
    breaks: Vec<Environment>,
    loop_continues: Vec<Environment>,
}

struct OriginContext<'a> {
    function: &'a AstFunction,
    draft: &'a SignatureDraft,
    drafts: &'a [SignatureDraft],
    sources: &'a [Origin],
}

impl BlockResult {
    fn fallthrough() -> Self {
        Self {
            returned: None,
            continues: true,
            breaks: Vec::new(),
            loop_continues: Vec::new(),
        }
    }

    fn add_return(&mut self, origin: Origin) {
        self.returned = Some(
            self.returned
                .take()
                .map_or_else(|| origin.clone(), |current| current.join(origin.clone())),
        );
    }

    fn merge_returns(&mut self, other: &Self) {
        if let Some(origin) = &other.returned {
            self.add_return(origin.clone());
        }
        self.breaks.extend(other.breaks.iter().cloned());
        self.loop_continues
            .extend(other.loop_continues.iter().cloned());
    }

    fn leave_scope(&mut self) {
        for environment in self.breaks.iter_mut().chain(self.loop_continues.iter_mut()) {
            environment.0.pop();
        }
    }
}

impl Elaborator {
    pub(super) fn infer_borrow_sources(
        &mut self,
        functions: &[(usize, &AstFunction)],
        drafts: &[SignatureDraft],
    ) -> Result<Vec<Option<InferredBorrowSource>>, FrontendFailure> {
        let mut sources = vec![None; drafts.len()];
        let graph = self.borrow_source_graph(functions, drafts);
        let mut hypotheses = drafts
            .iter()
            .map(|draft| {
                if self.tracks_borrow_shape(draft) {
                    Origin::Deferred
                } else {
                    Origin::NotBorrow
                }
            })
            .collect::<Vec<_>>();

        // Components are callee-first. Each component is solved in a private
        // environment and published only after every member has reached a
        // stable structural relation and passed one final replay.
        for component in source_components(&graph) {
            let members = component
                .into_iter()
                .filter(|index| self.tracks_borrow_shape(&drafts[*index]))
                .collect::<Vec<_>>();
            if members.is_empty() {
                continue;
            }
            if members.len() > MAX_BORROW_SOURCE_SCC_FUNCTIONS {
                return Err(FrontendFailure::unsupported(
                    functions[members[0]].1.span,
                    "borrow source SCC exceeds the function budget",
                ));
            }

            let mut candidates = vec![Origin::NoNormalReturn; members.len()];
            let mut converged = false;
            for _ in 0..MAX_BORROW_SOURCE_FIXPOINT_ITERATIONS {
                let mut trial = hypotheses.clone();
                for (&member, candidate) in members.iter().zip(&candidates) {
                    trial[member] = candidate.clone();
                }
                let mut next = Vec::with_capacity(members.len());
                for (&member, candidate) in members.iter().zip(&candidates) {
                    self.current_module = functions[member].0;
                    let observed = self.infer_function_origin(
                        functions[member].1,
                        &drafts[member],
                        drafts,
                        &trial,
                    );
                    next.push(candidate.clone().join(observed));
                }
                if next == candidates {
                    converged = true;
                    break;
                }
                candidates = next;
            }
            if !converged {
                return Err(FrontendFailure::unsupported(
                    functions[members[0]].1.span,
                    "borrow source SCC did not converge within the iteration budget",
                ));
            }

            let mut final_trial = hypotheses.clone();
            for (&member, candidate) in members.iter().zip(&candidates) {
                final_trial[member] = candidate.clone();
            }
            for (&member, candidate) in members.iter().zip(&candidates) {
                self.current_module = functions[member].0;
                if self.infer_function_origin(
                    functions[member].1,
                    &drafts[member],
                    drafts,
                    &final_trial,
                ) != *candidate
                {
                    return Err(FrontendFailure::unsupported(
                        functions[member].1.span,
                        "borrow source SCC failed its final replay",
                    ));
                }
            }

            let mut published = Vec::with_capacity(members.len());
            let mut relation_count = 0usize;
            for (&member, origin) in members.iter().zip(&candidates) {
                let origin = origin.clone();
                let function = functions[member].1;
                let draft = &drafts[member];
                if draft.borrow_candidates().is_none() {
                    hypotheses[member] = origin.clone();
                    let mut leaves = Vec::new();
                    origin.reference_leaves(&mut leaves);
                    let expected = draft.value_result_type().and_then(|ty| {
                        super::regions::aggregate_reference_types(&self.types, &self.fields, ty)
                    });
                    if expected.is_some_and(|v| v.len() == leaves.len()) {
                        let sources = leaves
                            .into_iter()
                            .map(|o| match o {
                                Origin::Parameter(p)
                                    if p.projection == crate::BorrowProjection::Whole =>
                                {
                                    Some(p.field.map_or(
                                        crate::BoundarySource::Parameter { index: p.parameter },
                                        |field| crate::BoundarySource::ParameterField {
                                            index: p.parameter,
                                            field,
                                        },
                                    ))
                                }
                                _ => None,
                            })
                            .collect::<Option<Vec<_>>>();
                        if let Some(sources) = sources {
                            self.aggregate_result_sources.insert(draft.owner, sources);
                        }
                    }
                    continue;
                }
                self.current_module = functions[member].0;
                let access = if draft.result_is_mutable() == Some(true) {
                    crate::BorrowAccess::Mutable
                } else {
                    crate::BorrowAccess::Shared
                };
                let inferred = match origin {
                    Origin::Parameter(source) => {
                        InferredBorrowSource::Unconditional(crate::BorrowResultRelation {
                            parameter: source.parameter,
                            parameter_field: source.field,
                            result: 0,
                            projection: source.projection,
                            access,
                        })
                    }
                    Origin::NoNormalReturn => {
                        let candidates = draft.borrow_candidates().unwrap();
                        let [only] = candidates else {
                            return Err(FrontendFailure::unsupported(
                                function.span,
                                "a non-returning borrow SCC with multiple possible sources needs an explicit contract",
                            ));
                        };
                        // The least fixed point found no normal return. The
                        // single type-compatible source is only an ABI shape;
                        // the canonical verifier must independently establish
                        // the no-return body before publishing its SCC summary.
                        InferredBorrowSource::Unconditional(crate::BorrowResultRelation::whole(
                            *only, access,
                        ))
                    }
                    Origin::Conflict => {
                        if let Some(alternatives) =
                            self.infer_guarded_sources(function, draft, drafts, &final_trial)
                        {
                            relation_count = relation_count.saturating_add(alternatives.len());
                            published.push((
                                member,
                                Origin::Deferred,
                                InferredBorrowSource::Conditional(alternatives),
                            ));
                            continue;
                        }
                        return Err(FrontendFailure::unsupported(
                            function.span,
                            "returned reference has multiple path-dependent input sources",
                        ));
                    }
                    Origin::LocalStorage => {
                        return Err(FrontendFailure::elaboration(
                            function.span,
                            "returned reference cannot escape function-local storage",
                        ));
                    }
                    Origin::NotBorrow | Origin::Aggregate(_) => {
                        return Err(FrontendFailure::elaboration(
                            function.span,
                            "return value does not match the function return type",
                        ));
                    }
                    Origin::Projection => {
                        return Err(FrontendFailure::unsupported(
                            function.span,
                            "returned reference projection is outside the bounded field/slice interface",
                        ));
                    }
                    Origin::Deferred => {
                        return Err(FrontendFailure::unsupported(
                            function.span,
                            "returned reference source depends on an unresolved borrow interface",
                        ));
                    }
                };
                relation_count = relation_count.saturating_add(1);
                published.push((member, origin, inferred));
            }
            if relation_count > MAX_BORROW_SOURCE_RELATIONS {
                return Err(FrontendFailure::unsupported(
                    functions[members[0]].1.span,
                    "borrow source SCC exceeds the relation budget",
                ));
            }
            for (member, hypothesis, inferred) in published {
                hypotheses[member] = hypothesis;
                sources[member] = Some(inferred);
            }
        }
        Ok(sources)
    }

    fn borrow_source_graph(
        &mut self,
        functions: &[(usize, &AstFunction)],
        drafts: &[SignatureDraft],
    ) -> Vec<BTreeSet<usize>> {
        functions
            .iter()
            .map(|(module, function)| {
                self.current_module = *module;
                let mut names = BTreeSet::new();
                collect_called_functions(&function.body, &mut names);
                names
                    .into_iter()
                    .filter_map(|name| self.function_names.get(&self.key(&name)).copied())
                    .map(|id| id.index())
                    .filter(|index| self.tracks_borrow_shape(&drafts[*index]))
                    .collect()
            })
            .collect()
    }

    fn infer_guarded_sources(
        &self,
        function: &AstFunction,
        draft: &SignatureDraft,
        drafts: &[SignatureDraft],
        sources: &[Origin],
    ) -> Option<Vec<crate::BorrowResultAlternative>> {
        let candidates = draft.borrow_candidates()?;
        let mutable_guards = assigned_names(&function.body);
        let parameter_names = function
            .parameters
            .iter()
            .enumerate()
            .map(|(index, parameter)| (parameter.name.as_str(), index as u32))
            .collect::<BTreeMap<_, _>>();
        let mut environment = Environment::new(function);
        let mut returns = Vec::new();
        self.collect_guarded_returns(
            &function.body,
            &mut environment,
            function,
            draft,
            drafts,
            sources,
            &parameter_names,
            &mutable_guards,
            &[],
            &mut returns,
        )?;
        if returns.len() < 2 || returns.len() > MAX_BORROW_RESULT_ALTERNATIVES {
            return None;
        }
        let access = if draft.result_is_mutable()? {
            crate::BorrowAccess::Mutable
        } else {
            crate::BorrowAccess::Shared
        };
        let mut alternatives = Vec::new();
        for (mut guard, origin) in returns {
            let Origin::Parameter(BorrowOrigin {
                parameter,
                field,
                projection: crate::BorrowProjection::Whole,
            }) = origin
            else {
                return None;
            };
            guard.sort();
            if !candidates.contains(&parameter)
                || guard.is_empty()
                || guard.len() > MAX_BORROW_RESULT_GUARD_ATOMS
                || guard.windows(2).any(|pair| {
                    matches!(
                        pair,
                        [
                            crate::BorrowGuardAtom::Boolean { parameter: left, .. },
                            crate::BorrowGuardAtom::Boolean { parameter: right, .. }
                        ] if left == right
                    )
                })
            {
                return None;
            }
            let alternative = crate::BorrowResultAlternative {
                guard,
                relation: field.map_or_else(
                    || crate::BorrowResultRelation::whole(parameter, access),
                    |field| {
                        crate::BorrowResultRelation::from_parameter_field(parameter, field, access)
                    },
                ),
            };
            if !alternatives.contains(&alternative) {
                alternatives.push(alternative);
            }
        }
        alternatives.sort_by(|left, right| left.guard.cmp(&right.guard));
        (alternatives.len() >= 2).then_some(alternatives)
    }

    #[allow(clippy::too_many_arguments)]
    fn collect_guarded_returns(
        &self,
        block: &AstBlock,
        environment: &mut Environment,
        function: &AstFunction,
        draft: &SignatureDraft,
        drafts: &[SignatureDraft],
        sources: &[Origin],
        parameter_names: &BTreeMap<&str, u32>,
        assigned: &BTreeSet<String>,
        guard: &[crate::BorrowGuardAtom],
        returns: &mut Vec<(Vec<crate::BorrowGuardAtom>, Origin)>,
    ) -> Option<Option<Vec<crate::BorrowGuardAtom>>> {
        let mut continues = true;
        let mut guard = guard.to_vec();
        for statement in &block.statements {
            if !continues {
                break;
            }
            match &statement.kind {
                AstStatementKind::Predicate { .. } => {}
                AstStatementKind::Declare { name, .. } => {
                    environment.insert(name, Origin::NotBorrow)
                }
                AstStatementKind::Let { name, value, .. } => environment.insert(
                    name,
                    self.infer_expression(value, environment, function, draft, drafts, sources),
                ),
                AstStatementKind::Assign { destination, value }
                    if destination.projections.is_empty() =>
                {
                    environment.assign(
                        &destination.base,
                        self.infer_expression(value, environment, function, draft, drafts, sources),
                    );
                }
                AstStatementKind::Return { value } => {
                    returns.push((
                        guard.to_vec(),
                        value.as_ref().map_or(Origin::NotBorrow, |value| {
                            self.infer_expression(
                                value,
                                environment,
                                function,
                                draft,
                                drafts,
                                sources,
                            )
                        }),
                    ));
                    continues = false;
                }
                AstStatementKind::Block { block } => {
                    environment.0.push(BTreeMap::new());
                    let remaining = self.collect_guarded_returns(
                        block,
                        environment,
                        function,
                        draft,
                        drafts,
                        sources,
                        parameter_names,
                        assigned,
                        &guard,
                        returns,
                    )?;
                    environment.0.pop();
                    continues = remaining.is_some();
                    if let Some(remaining) = remaining {
                        guard = remaining;
                    }
                }
                AstStatementKind::If {
                    condition,
                    then_block,
                    else_block,
                } => {
                    let name = match &condition.kind {
                        AstExpressionKind::Name(name) => name.as_str(),
                        AstExpressionKind::Place(place) if place.projections.is_empty() => {
                            place.base.as_str()
                        }
                        _ => return None,
                    };
                    let parameter = *parameter_names.get(name)?;
                    if assigned.contains(name) {
                        return None;
                    }
                    let mut then_guard = guard.to_vec();
                    then_guard.push(crate::BorrowGuardAtom::Boolean {
                        parameter,
                        expected: true,
                    });
                    let mut else_guard = guard.to_vec();
                    else_guard.push(crate::BorrowGuardAtom::Boolean {
                        parameter,
                        expected: false,
                    });
                    let before = environment.clone();
                    let mut then_environment = before.clone();
                    then_environment.0.push(BTreeMap::new());
                    let then_remaining = self.collect_guarded_returns(
                        then_block,
                        &mut then_environment,
                        function,
                        draft,
                        drafts,
                        sources,
                        parameter_names,
                        assigned,
                        &then_guard,
                        returns,
                    )?;
                    then_environment.0.pop();
                    let mut else_environment = before;
                    let else_remaining = if let Some(else_block) = else_block {
                        else_environment.0.push(BTreeMap::new());
                        let remaining = self.collect_guarded_returns(
                            else_block,
                            &mut else_environment,
                            function,
                            draft,
                            drafts,
                            sources,
                            parameter_names,
                            assigned,
                            &else_guard,
                            returns,
                        )?;
                        else_environment.0.pop();
                        remaining
                    } else {
                        Some(else_guard)
                    };
                    continues = then_remaining.is_some() || else_remaining.is_some();
                    if then_remaining.is_some() && else_remaining.is_some() {
                        then_environment.merge(&else_environment);
                        *environment = then_environment;
                    } else if let Some(remaining) = then_remaining {
                        *environment = then_environment;
                        guard = remaining;
                    } else if let Some(remaining) = else_remaining {
                        *environment = else_environment;
                        guard = remaining;
                    }
                }
                AstStatementKind::Match { .. }
                | AstStatementKind::While { .. }
                | AstStatementKind::For { .. } => return None,
                AstStatementKind::Assert { .. }
                | AstStatementKind::Store { .. }
                | AstStatementKind::Free { .. }
                | AstStatementKind::Evaluate { .. }
                | AstStatementKind::Break
                | AstStatementKind::Continue => {}
                AstStatementKind::Assign { .. } => {}
            }
        }
        Some(continues.then_some(guard))
    }

    fn infer_function_origin(
        &self,
        function: &AstFunction,
        draft: &SignatureDraft,
        drafts: &[SignatureDraft],
        sources: &[Origin],
    ) -> Origin {
        let mut environment = Environment::new(function);
        let context = OriginContext {
            function,
            draft,
            drafts,
            sources,
        };
        let result = self.infer_block(&function.body, &mut environment, &context, false);
        if result.continues {
            // Falling off a non-unit body is a normal exit without a value,
            // not evidence that the function diverges.
            Origin::NotBorrow
        } else {
            self.expand_origin(result.returned.unwrap_or(Origin::NoNormalReturn), draft)
        }
    }

    fn infer_block(
        &self,
        block: &AstBlock,
        environment: &mut Environment,
        context: &OriginContext<'_>,
        nested: bool,
    ) -> BlockResult {
        if nested {
            environment.0.push(BTreeMap::new());
        }
        let mut result = BlockResult::fallthrough();
        for statement in &block.statements {
            if !result.continues {
                break;
            }
            match &statement.kind {
                AstStatementKind::Predicate { .. } => {}
                AstStatementKind::Declare { name, .. } => {
                    environment.insert(name, Origin::NotBorrow);
                }
                AstStatementKind::Let { name, value, .. } => {
                    let origin = self.infer_expression(
                        value,
                        environment,
                        context.function,
                        context.draft,
                        context.drafts,
                        context.sources,
                    );
                    if origin == Origin::NoNormalReturn {
                        result.continues = false;
                    } else {
                        environment.insert(name, origin);
                    }
                }
                AstStatementKind::Assign { destination, value } => {
                    let origin = self.infer_expression(
                        value,
                        environment,
                        context.function,
                        context.draft,
                        context.drafts,
                        context.sources,
                    );
                    if origin == Origin::NoNormalReturn {
                        result.continues = false;
                    } else if destination.projections.is_empty() {
                        environment.assign(&destination.base, origin);
                    }
                }
                AstStatementKind::Return { value } => {
                    let origin = value.as_ref().map_or(Origin::NotBorrow, |value| {
                        self.infer_expression(
                            value,
                            environment,
                            context.function,
                            context.draft,
                            context.drafts,
                            context.sources,
                        )
                    });
                    if origin != Origin::NoNormalReturn {
                        result.add_return(origin);
                    }
                    result.continues = false;
                }
                AstStatementKind::Block { block } => {
                    let child = self.infer_block(block, environment, context, true);
                    result.merge_returns(&child);
                    result.continues = child.continues;
                }
                AstStatementKind::If {
                    then_block,
                    else_block,
                    ..
                } => {
                    let before = environment.clone();
                    let mut then_environment = before.clone();
                    let then_result =
                        self.infer_block(then_block, &mut then_environment, context, true);
                    let mut else_environment = before;
                    let else_result = else_block
                        .as_ref()
                        .map_or_else(BlockResult::fallthrough, |block| {
                            self.infer_block(block, &mut else_environment, context, true)
                        });
                    result.merge_returns(&then_result);
                    result.merge_returns(&else_result);
                    result.continues = then_result.continues || else_result.continues;
                    if then_result.continues && else_result.continues {
                        then_environment.merge(&else_environment);
                        *environment = then_environment;
                    } else if then_result.continues {
                        *environment = then_environment;
                    } else if else_result.continues {
                        *environment = else_environment;
                    }
                }
                AstStatementKind::Match { arms, .. } => {
                    let before = environment.clone();
                    let mut continuation: Option<Environment> = None;
                    for arm in arms {
                        let mut arm_environment = before.clone();
                        let arm_result =
                            self.infer_block(&arm.body, &mut arm_environment, context, true);
                        result.merge_returns(&arm_result);
                        if arm_result.continues {
                            if let Some(current) = &mut continuation {
                                current.merge(&arm_environment);
                            } else {
                                continuation = Some(arm_environment);
                            }
                        }
                    }
                    result.continues = continuation.is_some();
                    if let Some(continuation) = continuation {
                        *environment = continuation;
                    }
                }
                AstStatementKind::While { body, .. } => {
                    let loop_result = self.infer_loop(body, None, environment, context);
                    result.merge_returns(&loop_result);
                    result.continues = loop_result.continues;
                }
                AstStatementKind::For { binding, body, .. } => {
                    let loop_result =
                        self.infer_loop(body, Some(binding.as_str()), environment, context);
                    result.merge_returns(&loop_result);
                    result.continues = loop_result.continues;
                }
                AstStatementKind::Store { value, .. } => {
                    if self.infer_expression(
                        value,
                        environment,
                        context.function,
                        context.draft,
                        context.drafts,
                        context.sources,
                    ) == Origin::NoNormalReturn
                    {
                        result.continues = false;
                    }
                }
                AstStatementKind::Free { .. } => {}
                AstStatementKind::Assert { expression }
                | AstStatementKind::Evaluate { expression } => {
                    if self.infer_expression(
                        expression,
                        environment,
                        context.function,
                        context.draft,
                        context.drafts,
                        context.sources,
                    ) == Origin::NoNormalReturn
                    {
                        result.continues = false;
                    }
                }
                AstStatementKind::Break => {
                    result.breaks.push(environment.clone());
                    result.continues = false;
                }
                AstStatementKind::Continue => {
                    result.loop_continues.push(environment.clone());
                    result.continues = false;
                }
            }
        }
        if nested {
            environment.0.pop();
            result.leave_scope();
        }
        result
    }

    fn infer_loop(
        &self,
        body: &AstBlock,
        binding: Option<&str>,
        environment: &mut Environment,
        context: &OriginContext<'_>,
    ) -> BlockResult {
        let entry = environment.clone();
        let mut head = entry.clone();
        let mut result = BlockResult::fallthrough();
        let mut exits = Vec::<Environment>::new();
        for _ in 0..MAX_BORROW_SOURCE_FIXPOINT_ITERATIONS {
            let mut body_environment = head.clone();
            body_environment.0.push(BTreeMap::new());
            if let Some(binding) = binding {
                body_environment.insert(binding, Origin::NotBorrow);
            }
            let mut body_result = self.infer_block(body, &mut body_environment, context, false);
            body_environment.0.pop();
            body_result.leave_scope();
            if let Some(returned) = body_result.returned {
                result.add_return(returned);
            }
            exits.extend(body_result.breaks);

            let mut back_edge = body_result.continues.then_some(body_environment);
            for continuation in body_result.loop_continues {
                if let Some(current) = &mut back_edge {
                    current.merge(&continuation);
                } else {
                    back_edge = Some(continuation);
                }
            }
            let mut next = entry.clone();
            if let Some(back_edge) = back_edge {
                next.merge(&back_edge);
            }
            if next == head {
                let mut after = head;
                for exit in exits {
                    after.merge(&exit);
                }
                *environment = after;
                return result;
            }
            head = next;
        }
        result.add_return(Origin::Deferred);
        result
    }

    fn infer_expression(
        &self,
        expression: &AstExpression,
        environment: &Environment,
        function: &AstFunction,
        draft: &SignatureDraft,
        drafts: &[SignatureDraft],
        sources: &[Origin],
    ) -> Origin {
        let origin =
            self.infer_expression_shape(expression, environment, function, draft, drafts, sources);
        if origin.within_budget() {
            origin
        } else {
            Origin::Projection
        }
    }

    fn infer_expression_shape(
        &self,
        expression: &AstExpression,
        environment: &Environment,
        function: &AstFunction,
        draft: &SignatureDraft,
        drafts: &[SignatureDraft],
        sources: &[Origin],
    ) -> Origin {
        match &expression.kind {
            AstExpressionKind::Name(name) => environment.lookup(name),
            AstExpressionKind::Place(place) if place.projections.is_empty() => {
                environment.lookup(&place.base)
            }
            AstExpressionKind::Place(place) => {
                self.infer_reference_field(place, environment, draft)
            }
            AstExpressionKind::Borrow { place, .. } => {
                self.infer_borrow_place(place, environment, function, draft)
            }
            AstExpressionKind::Call { callee, arguments }
            | AstExpressionKind::GenericCall {
                callee, arguments, ..
            } => {
                let Some(callee) = self.function_names.get(&self.key(callee)).copied() else {
                    return Origin::NotBorrow;
                };
                if !self.tracks_borrow_shape(&drafts[callee.index()]) {
                    return Origin::NotBorrow;
                }
                let source = sources[callee.index()].clone();
                let actual = arguments
                    .iter()
                    .map(|a| {
                        self.infer_expression(a, environment, function, draft, drafts, sources)
                    })
                    .collect::<Vec<_>>();
                self.substitute_origin(source, &actual, draft)
            }
            AstExpressionKind::Struct {
                name,
                fields: values,
            } => {
                let Some(HirTypeKind::Struct { fields }) = self
                    .type_names
                    .get(&self.key(name))
                    .and_then(|ty| self.type_definition(*ty))
                    .map(|t| &t.kind)
                else {
                    return Origin::Projection;
                };
                let mut fields = fields.clone();
                fields.sort_unstable();
                Origin::Aggregate(
                    fields
                        .into_iter()
                        .map(|id| {
                            let name = self.fields[id.index()].name.clone();
                            let value = values.iter().find(|v| v.name == name).map_or(
                                Origin::Conflict,
                                |v| {
                                    self.infer_expression(
                                        &v.value,
                                        environment,
                                        function,
                                        draft,
                                        drafts,
                                        sources,
                                    )
                                },
                            );
                            (name, self.expand_origin(value, draft))
                        })
                        .collect(),
                )
            }
            AstExpressionKind::Tuple(values) | AstExpressionKind::Array(values)
                if values.len() <= 256 =>
            {
                Origin::Aggregate(
                    values
                        .iter()
                        .enumerate()
                        .map(|(i, v)| {
                            (
                                i.to_string(),
                                self.expand_origin(
                                    self.infer_expression(
                                        v,
                                        environment,
                                        function,
                                        draft,
                                        drafts,
                                        sources,
                                    ),
                                    draft,
                                ),
                            )
                        })
                        .collect(),
                )
            }
            AstExpressionKind::ArrayRepeat { value, length } if *length <= 256 => {
                let value = self.expand_origin(
                    self.infer_expression(value, environment, function, draft, drafts, sources),
                    draft,
                );
                Origin::Aggregate(
                    (0..*length)
                        .map(|i| (i.to_string(), value.clone()))
                        .collect(),
                )
            }
            _ => Origin::NotBorrow,
        }
    }

    /// Select canonical stored reference leaves, including the designated
    /// storage of one owner/reference parameter. Raw pointers have no source.
    fn infer_reference_field(
        &self,
        place: &AstPlace,
        environment: &Environment,
        draft: &SignatureDraft,
    ) -> Origin {
        let origin = environment.lookup(&place.base);
        let designated = matches!(&origin, Origin::Parameter(source) if source.field.is_none()
            && draft.parameter_type(source.parameter).and_then(|ty| self.type_definition(ty))
                .is_some_and(|t| matches!(t.kind, HirTypeKind::Own { .. } | HirTypeKind::Reference { .. })));
        let mut value = self.expand_storage_origin(origin, draft, true);
        if place.projections.len() > 16 {
            return Origin::Projection;
        }
        for (index, projection) in place.projections.iter().enumerate() {
            if index == 0
                && designated
                && matches!(projection, AstPlaceProjection::Dereference { .. })
            {
                continue;
            }
            let key = match projection {
                AstPlaceProjection::Field { name, .. } => name.clone(),
                AstPlaceProjection::TupleElement { index, .. } => index.to_string(),
                AstPlaceProjection::Index { index, .. } => match index.kind {
                    AstExpressionKind::Integer { value, .. } => value.to_string(),
                    _ => return Origin::Projection,
                },
                _ => return Origin::Projection,
            };
            let Origin::Aggregate(fields) = value else {
                return Origin::Projection;
            };
            value = fields
                .into_iter()
                .find(|(name, _)| *name == key)
                .map_or(Origin::Projection, |(_, v)| v);
        }
        value
    }

    fn tracks_borrow_shape(&self, draft: &SignatureDraft) -> bool {
        draft.borrow_candidates().is_some()
            || draft
                .value_result_type()
                .and_then(|ty| {
                    super::regions::aggregate_reference_types(&self.types, &self.fields, ty)
                })
                .is_some_and(|v| !v.is_empty())
    }

    fn expand_origin(&self, origin: Origin, draft: &SignatureDraft) -> Origin {
        self.expand_storage_origin(origin, draft, false)
    }

    fn expand_storage_origin(
        &self,
        origin: Origin,
        draft: &SignatureDraft,
        designated: bool,
    ) -> Origin {
        let Origin::Parameter(source) = origin else {
            return origin;
        };
        if source.field.is_some() || source.projection != crate::BorrowProjection::Whole {
            return origin;
        }
        let Some(ty) = draft.parameter_type(source.parameter) else {
            return Origin::Projection;
        };
        let ty = if designated {
            match self.type_definition(ty).map(|t| &t.kind) {
                Some(HirTypeKind::Own { pointee } | HirTypeKind::Reference { pointee, .. }) => {
                    *pointee
                }
                _ => ty,
            }
        } else {
            ty
        };
        if !self.is_aggregate(ty) {
            return if self.reference_region(ty).is_some() {
                origin
            } else {
                Origin::NotBorrow
            };
        }
        if super::regions::aggregate_reference_types(&self.types, &self.fields, ty).is_none() {
            return Origin::Projection;
        }
        fn walk(
            e: &Elaborator,
            ty: HirTypeId,
            parameter: u32,
            ordinal: &mut u32,
            depth: usize,
            budget: &mut usize,
        ) -> Option<Origin> {
            *budget = budget.checked_sub(1)?;
            if depth > 16 {
                return None;
            }
            let children = match &e.type_definition(ty)?.kind {
                HirTypeKind::Reference { .. } => {
                    let field = *ordinal;
                    *ordinal += 1;
                    return Some(Origin::Parameter(BorrowOrigin {
                        parameter,
                        field: Some(field),
                        projection: crate::BorrowProjection::Whole,
                    }));
                }
                HirTypeKind::Struct { fields } => {
                    let mut fields = fields.clone();
                    fields.sort_unstable();
                    fields
                        .into_iter()
                        .map(|id| {
                            let f = &e.fields[id.index()];
                            (f.name.clone(), f.ty)
                        })
                        .collect::<Vec<_>>()
                }
                HirTypeKind::Tuple(elements) => elements
                    .iter()
                    .enumerate()
                    .map(|(i, t)| (i.to_string(), *t))
                    .collect(),
                HirTypeKind::Array { element, length } if *length <= 256 => {
                    (0..*length).map(|i| (i.to_string(), *element)).collect()
                }
                HirTypeKind::Array { .. } => return None,
                _ => return Some(Origin::NotBorrow),
            };
            Some(Origin::Aggregate(
                children
                    .into_iter()
                    .map(|(key, ty)| {
                        Some((key, walk(e, ty, parameter, ordinal, depth + 1, budget)?))
                    })
                    .collect::<Option<_>>()?,
            ))
        }
        walk(self, ty, source.parameter, &mut 0, 0, &mut 4096).unwrap_or(Origin::Projection)
    }

    fn substitute_origin(
        &self,
        origin: Origin,
        arguments: &[Origin],
        draft: &SignatureDraft,
    ) -> Origin {
        match origin {
            Origin::Aggregate(fields) => Origin::Aggregate(
                fields
                    .into_iter()
                    .map(|(key, v)| (key, self.substitute_origin(v, arguments, draft)))
                    .collect(),
            ),
            Origin::Parameter(source) => {
                let Some(argument) = arguments.get(source.parameter as usize) else {
                    return Origin::Conflict;
                };
                let argument =
                    self.expand_storage_origin(argument.clone(), draft, source.field.is_some());
                let argument = if let Some(field) = source.field {
                    let mut leaves = Vec::new();
                    argument.reference_leaves(&mut leaves);
                    leaves
                        .get(field as usize)
                        .map_or(Origin::Projection, |v| (*v).clone())
                } else {
                    argument
                };
                compose_origin(argument, source.projection)
            }
            other => other,
        }
    }

    fn infer_borrow_place(
        &self,
        place: &AstPlace,
        environment: &Environment,
        function: &AstFunction,
        draft: &SignatureDraft,
    ) -> Origin {
        let Origin::Parameter(source) = environment.lookup(&place.base) else {
            return if place.projections.is_empty() {
                Origin::LocalStorage
            } else {
                Origin::Projection
            };
        };
        let Some(projection) = self.borrow_projection(place, source, function, draft) else {
            return Origin::Projection;
        };
        Origin::Parameter(BorrowOrigin {
            parameter: source.parameter,
            field: source.field,
            projection,
        })
    }

    fn borrow_projection(
        &self,
        place: &AstPlace,
        source: BorrowOrigin,
        function: &AstFunction,
        draft: &SignatureDraft,
    ) -> Option<crate::BorrowProjection> {
        if source.projection != crate::BorrowProjection::Whole {
            return None;
        }
        let parameter = draft.parameter_type(source.parameter)?;
        let parameter = if let Some(field) = source.field {
            super::regions::parameter_reference_types(&self.types, &self.fields, parameter)?
                .get(field as usize)?
                .0
        } else {
            parameter
        };
        let HirTypeKind::Reference { pointee, .. } = self.type_definition(parameter)?.kind else {
            return None;
        };
        if let Some(AstPlaceProjection::Slice { start, end, .. }) = place.projections.last() {
            let mut ty = pointee;
            let mut offset_bytes = 0u64;
            for projection in &place.projections[..place.projections.len() - 1] {
                match projection {
                    AstPlaceProjection::Dereference { .. }
                        if ty == pointee && offset_bytes == 0 => {}
                    AstPlaceProjection::Field { name, .. } => {
                        let HirTypeKind::Struct { fields } = &self.type_definition(ty)?.kind else {
                            return None;
                        };
                        let field = fields
                            .iter()
                            .filter_map(|id| self.fields.get(id.index()))
                            .find(|f| f.name == *name)?;
                        offset_bytes = offset_bytes.checked_add(
                            self.resolved_layout(ty)?
                                .fields
                                .iter()
                                .find(|f| f.field == field.id)?
                                .offset_bytes,
                        )?;
                        ty = field.ty;
                    }
                    _ => return None,
                }
            }
            if let HirTypeKind::Array { element, length } = self.type_definition(ty)?.kind {
                if !self.borrow_projection_pointer_free(element, &mut BTreeSet::new()) {
                    return None;
                }
                let layout = self.resolved_layout(element)?;
                let start = self
                    .borrow_slice_bound(
                        start.as_deref(),
                        function,
                        draft,
                        source.parameter,
                        crate::BorrowSliceBound::Constant(0),
                    )
                    .unwrap_or(crate::BorrowSliceBound::ReturnedOffset);
                let end = if start == crate::BorrowSliceBound::ReturnedOffset {
                    crate::BorrowSliceBound::ReturnedLength
                } else {
                    self.borrow_slice_bound(
                        end.as_deref(),
                        function,
                        draft,
                        source.parameter,
                        crate::BorrowSliceBound::Constant(length),
                    )
                    .unwrap_or(crate::BorrowSliceBound::ReturnedLength)
                };
                return Some(crate::BorrowProjection::ArraySlice {
                    offset_bytes: offset_bytes.try_into().ok()?,
                    length: length.try_into().ok()?,
                    start,
                    end,
                    stride_bytes: layout.size_bytes.try_into().ok()?,
                });
            }
        }
        let projections = match place.projections.as_slice() {
            [projection] => std::slice::from_ref(projection),
            [AstPlaceProjection::Dereference { .. }, projection] => {
                std::slice::from_ref(projection)
            }
            _ => return None,
        };
        match &projections[0] {
            AstPlaceProjection::Dereference { .. } => Some(crate::BorrowProjection::Whole),
            AstPlaceProjection::Field { name, .. } => {
                let HirTypeKind::Struct { fields } = &self.type_definition(pointee)?.kind else {
                    return None;
                };
                let field = fields
                    .iter()
                    .filter_map(|id| self.fields.get(id.index()))
                    .find(|field| field.name == *name)?;
                if !self.borrow_projection_pointer_free(field.ty, &mut BTreeSet::new()) {
                    return None;
                }
                let owner = self.resolved_layout(pointee)?;
                let offset_bytes = owner
                    .fields
                    .iter()
                    .find(|layout| layout.field == field.id)?
                    .offset_bytes;
                let layout = self.resolved_layout(field.ty)?;
                offset_bytes
                    .checked_add(layout.size_bytes)
                    .filter(|end| *end <= owner.size_bytes)?;
                Some(crate::BorrowProjection::Fixed {
                    offset_bytes,
                    size_bytes: layout.size_bytes,
                    alignment: layout.alignment,
                })
            }
            AstPlaceProjection::Slice { start, end, .. } => {
                let HirTypeKind::Slice { element, .. } = self.type_definition(pointee)?.kind else {
                    return None;
                };
                if !self.borrow_projection_pointer_free(element, &mut BTreeSet::new()) {
                    return None;
                }
                let layout = self.resolved_layout(element)?;
                Some(crate::BorrowProjection::Slice {
                    start: self.borrow_slice_bound(
                        start.as_deref(),
                        function,
                        draft,
                        source.parameter,
                        crate::BorrowSliceBound::Constant(0),
                    )?,
                    end: self.borrow_slice_bound(
                        end.as_deref(),
                        function,
                        draft,
                        source.parameter,
                        crate::BorrowSliceBound::SourceLength,
                    )?,
                    stride_bytes: layout.size_bytes,
                    alignment: layout.alignment,
                })
            }
            AstPlaceProjection::TupleElement { .. } | AstPlaceProjection::Index { .. } => None,
        }
    }

    fn borrow_slice_bound(
        &self,
        expression: Option<&AstExpression>,
        function: &AstFunction,
        draft: &SignatureDraft,
        source: u32,
        default: crate::BorrowSliceBound,
    ) -> Option<crate::BorrowSliceBound> {
        let Some(expression) = expression else {
            return Some(default);
        };
        match &expression.kind {
            AstExpressionKind::Integer { value, .. } => {
                Some(crate::BorrowSliceBound::Constant(*value))
            }
            AstExpressionKind::Name(name) => {
                let index = function.parameters.iter().position(|p| p.name == *name)? as u32;
                matches!(
                    draft
                        .parameter_type(index)
                        .and_then(|ty| self.type_definition(ty)),
                    Some(HirTypeDefinition {
                        kind: HirTypeKind::Integer(HirIntegerType::Usize),
                        ..
                    })
                )
                .then_some(crate::BorrowSliceBound::Parameter(index))
            }
            AstExpressionKind::Place(place) if place.projections.is_empty() => {
                let index = function
                    .parameters
                    .iter()
                    .position(|p| p.name == place.base)? as u32;
                matches!(
                    draft
                        .parameter_type(index)
                        .and_then(|ty| self.type_definition(ty)),
                    Some(HirTypeDefinition {
                        kind: HirTypeKind::Integer(HirIntegerType::Usize),
                        ..
                    })
                )
                .then_some(crate::BorrowSliceBound::Parameter(index))
            }
            AstExpressionKind::Call { callee, arguments } if callee == "len" => {
                let [argument] = arguments.as_slice() else {
                    return None;
                };
                let name = match &argument.kind {
                    AstExpressionKind::Name(name) => name,
                    AstExpressionKind::Place(place) if place.projections.is_empty() => &place.base,
                    _ => return None,
                };
                (function
                    .parameters
                    .get(source as usize)
                    .is_some_and(|parameter| parameter.name == *name))
                .then_some(crate::BorrowSliceBound::SourceLength)
            }
            _ => None,
        }
    }

    fn borrow_projection_pointer_free(
        &self,
        ty: HirTypeId,
        seen: &mut BTreeSet<HirTypeId>,
    ) -> bool {
        if !seen.insert(ty) {
            return false;
        }
        let valid = match self.type_definition(ty).map(|definition| &definition.kind) {
            Some(HirTypeKind::Unit | HirTypeKind::Bool | HirTypeKind::Integer(_)) => true,
            Some(HirTypeKind::Array { element, .. }) => {
                self.borrow_projection_pointer_free(*element, seen)
            }
            Some(HirTypeKind::Tuple(elements)) => elements
                .iter()
                .all(|element| self.borrow_projection_pointer_free(*element, seen)),
            Some(HirTypeKind::Struct { fields }) => fields.iter().all(|field| {
                self.fields
                    .get(field.index())
                    .is_some_and(|field| self.borrow_projection_pointer_free(field.ty, seen))
            }),
            _ => false,
        };
        seen.remove(&ty);
        valid
    }
}

fn compose_origin(origin: Origin, projection: crate::BorrowProjection) -> Origin {
    let Origin::Parameter(mut origin) = origin else {
        return origin;
    };
    origin.projection = match (origin.projection, projection) {
        (current, crate::BorrowProjection::Whole) => current,
        (crate::BorrowProjection::Whole, projected) => projected,
        _ => return Origin::Projection,
    };
    Origin::Parameter(origin)
}

fn source_components(graph: &[BTreeSet<usize>]) -> Vec<Vec<usize>> {
    let mut reverse = vec![BTreeSet::new(); graph.len()];
    for (source, targets) in graph.iter().enumerate() {
        for &target in targets {
            reverse[target].insert(source);
        }
    }
    let mut visited = vec![false; graph.len()];
    let mut finish = Vec::with_capacity(graph.len());
    for root in 0..graph.len() {
        let mut stack = vec![(root, false)];
        while let Some((index, expanded)) = stack.pop() {
            if expanded {
                finish.push(index);
                continue;
            }
            if std::mem::replace(&mut visited[index], true) {
                continue;
            }
            stack.push((index, true));
            stack.extend(graph[index].iter().rev().map(|index| (*index, false)));
        }
    }

    visited.fill(false);
    let mut groups = BTreeMap::<usize, Vec<usize>>::new();
    let mut owners = vec![0usize; graph.len()];
    for root in finish.into_iter().rev() {
        if visited[root] {
            continue;
        }
        let mut members = Vec::new();
        let mut stack = vec![root];
        while let Some(index) = stack.pop() {
            if std::mem::replace(&mut visited[index], true) {
                continue;
            }
            members.push(index);
            stack.extend(reverse[index].iter().rev().copied());
        }
        members.sort_unstable();
        let owner = members[0];
        for &member in &members {
            owners[member] = owner;
        }
        groups.insert(owner, members);
    }

    let mut dependencies = groups
        .iter()
        .map(|(&owner, members)| {
            let dependencies = members
                .iter()
                .flat_map(|member| &graph[*member])
                .map(|target| owners[*target])
                .filter(|target| *target != owner)
                .collect::<BTreeSet<_>>();
            (owner, dependencies)
        })
        .collect::<BTreeMap<_, _>>();
    let mut ordered = Vec::with_capacity(groups.len());
    while let Some(owner) = dependencies
        .iter()
        .find_map(|(&owner, dependencies)| dependencies.is_empty().then_some(owner))
    {
        dependencies.remove(&owner);
        ordered.push(groups.remove(&owner).unwrap());
        for remaining in dependencies.values_mut() {
            remaining.remove(&owner);
        }
    }
    debug_assert!(
        groups.is_empty(),
        "borrow source SCC condensation is acyclic"
    );
    ordered
}

fn collect_called_functions(block: &AstBlock, names: &mut BTreeSet<String>) {
    for statement in &block.statements {
        match &statement.kind {
            AstStatementKind::Predicate { .. } => {}
            AstStatementKind::Declare { .. }
            | AstStatementKind::Free { .. }
            | AstStatementKind::Break
            | AstStatementKind::Continue => {}
            AstStatementKind::Assert { expression: value }
            | AstStatementKind::Let { value, .. }
            | AstStatementKind::Store { value, .. }
            | AstStatementKind::Evaluate { expression: value } => {
                collect_expression_calls(value, names)
            }
            AstStatementKind::Assign { destination, value } => {
                collect_place_calls(destination, names);
                collect_expression_calls(value, names);
            }
            AstStatementKind::Return { value } => {
                if let Some(value) = value {
                    collect_expression_calls(value, names);
                }
            }
            AstStatementKind::Block { block } => collect_called_functions(block, names),
            AstStatementKind::If {
                condition,
                then_block,
                else_block,
            } => {
                collect_expression_calls(condition, names);
                collect_called_functions(then_block, names);
                if let Some(block) = else_block {
                    collect_called_functions(block, names);
                }
            }
            AstStatementKind::While {
                condition, body, ..
            } => {
                collect_expression_calls(condition, names);
                collect_called_functions(body, names);
            }
            AstStatementKind::For {
                start, end, body, ..
            } => {
                collect_expression_calls(start, names);
                collect_expression_calls(end, names);
                collect_called_functions(body, names);
            }
            AstStatementKind::Match { scrutinee, arms } => {
                collect_expression_calls(scrutinee, names);
                for arm in arms {
                    if let Some(guard) = &arm.guard {
                        collect_expression_calls(guard, names);
                    }
                    collect_called_functions(&arm.body, names);
                }
            }
        }
    }
}

fn collect_expression_calls(expression: &AstExpression, names: &mut BTreeSet<String>) {
    match &expression.kind {
        AstExpressionKind::Call { callee, arguments }
        | AstExpressionKind::GenericCall {
            callee, arguments, ..
        } => {
            names.insert(callee.clone());
            for argument in arguments {
                collect_expression_calls(argument, names);
            }
        }
        AstExpressionKind::Tuple(elements)
        | AstExpressionKind::Array(elements)
        | AstExpressionKind::Add(elements) => {
            for element in elements {
                collect_expression_calls(element, names);
            }
        }
        AstExpressionKind::ArrayRepeat { value, .. }
        | AstExpressionKind::ConstRepeat { value, .. } => collect_expression_calls(value, names),
        AstExpressionKind::Struct { fields, .. }
        | AstExpressionKind::GenericStruct { fields, .. } => {
            for field in fields {
                collect_expression_calls(&field.value, names);
            }
        }
        AstExpressionKind::EnumVariant { payload, .. } => match payload {
            crate::frontend::AstVariantInitializer::Unit => {}
            crate::frontend::AstVariantInitializer::Tuple(elements) => {
                for element in elements {
                    collect_expression_calls(element, names);
                }
            }
            crate::frontend::AstVariantInitializer::Named(fields) => {
                for field in fields {
                    collect_expression_calls(&field.value, names);
                }
            }
        },
        AstExpressionKind::Place(place)
        | AstExpressionKind::Borrow { place, .. }
        | AstExpressionKind::RawAddress { place, .. } => collect_place_calls(place, names),
        AstExpressionKind::Compare { left, right, .. } => {
            collect_expression_calls(left, names);
            collect_expression_calls(right, names);
        }
        AstExpressionKind::Integer { .. }
        | AstExpressionKind::Bool(_)
        | AstExpressionKind::Name(_)
        | AstExpressionKind::Unit
        | AstExpressionKind::NullPointer { .. }
        | AstExpressionKind::Allocate { .. }
        | AstExpressionKind::Load { .. } => {}
    }
}

fn collect_place_calls(place: &AstPlace, names: &mut BTreeSet<String>) {
    for projection in &place.projections {
        match projection {
            AstPlaceProjection::Index { index, .. } => collect_expression_calls(index, names),
            AstPlaceProjection::Slice { start, end, .. } => {
                if let Some(start) = start {
                    collect_expression_calls(start, names);
                }
                if let Some(end) = end {
                    collect_expression_calls(end, names);
                }
            }
            AstPlaceProjection::Dereference { .. }
            | AstPlaceProjection::Field { .. }
            | AstPlaceProjection::TupleElement { .. } => {}
        }
    }
}

fn assigned_names(block: &AstBlock) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    fn visit(block: &AstBlock, names: &mut BTreeSet<String>) {
        for statement in &block.statements {
            match &statement.kind {
                AstStatementKind::Predicate { .. } => {}
                AstStatementKind::Let { name, .. } | AstStatementKind::Declare { name, .. } => {
                    // A same-named local is not the immutable entry guard.
                    names.insert(name.clone());
                }
                AstStatementKind::Assign { destination, .. }
                    if destination.projections.is_empty() =>
                {
                    names.insert(destination.base.clone());
                }
                AstStatementKind::Block { block } | AstStatementKind::While { body: block, .. } => {
                    visit(block, names)
                }
                AstStatementKind::If {
                    then_block,
                    else_block,
                    ..
                } => {
                    visit(then_block, names);
                    if let Some(block) = else_block {
                        visit(block, names);
                    }
                }
                AstStatementKind::For { body, .. } => visit(body, names),
                AstStatementKind::Match { arms, .. } => {
                    for arm in arms {
                        visit(&arm.body, names);
                    }
                }
                _ => {}
            }
        }
    }
    visit(block, &mut names);
    names
}

#[cfg(test)]
mod origin_join_tests {
    use super::*;
    use crate::{BorrowProjection as P, BorrowSliceBound as B};

    fn origin(parameter: u32, field: Option<u32>, offset: u16, start: B, end: B) -> Origin {
        Origin::Parameter(BorrowOrigin {
            parameter,
            field,
            projection: P::ArraySlice {
                offset_bytes: offset,
                length: 4,
                stride_bytes: 8,
                start,
                end,
            },
        })
    }

    #[test]
    fn array_view_join_widens_coordinates_but_never_the_source_geometry() {
        let dynamic = origin(0, None, 8, B::Parameter(1), B::Parameter(2));
        let empty = origin(0, None, 8, B::Constant(0), B::Constant(0));
        let joined = origin(0, None, 8, B::ReturnedOffset, B::ReturnedLength);
        assert_eq!(dynamic.clone().join(empty.clone()), joined);
        assert_eq!(empty.clone().join(dynamic.clone()), joined);
        assert_eq!(joined.clone().join(dynamic.clone()), joined);
        assert_eq!(joined.clone().join(empty.clone()), joined);
        assert_eq!(dynamic.clone().join(dynamic.clone()), dynamic);
        assert_eq!(
            origin(0, None, 8, B::Constant(0), B::Constant(2)).join(empty.clone()),
            origin(0, None, 8, B::Constant(0), B::ReturnedLength)
        );
        for other in [
            origin(1, None, 8, B::Constant(0), B::Constant(0)),
            origin(0, Some(1), 8, B::Constant(0), B::Constant(0)),
            origin(0, None, 16, B::Constant(0), B::Constant(0)),
        ] {
            assert_eq!(empty.clone().join(other), Origin::Conflict);
        }
        for projection in [
            P::Whole,
            P::ArraySlice {
                offset_bytes: 8,
                length: 5,
                stride_bytes: 8,
                start: B::Constant(0),
                end: B::Constant(0),
            },
            P::ArraySlice {
                offset_bytes: 8,
                length: 4,
                stride_bytes: 16,
                start: B::Constant(0),
                end: B::Constant(0),
            },
        ] {
            assert_eq!(
                empty.clone().join(Origin::Parameter(BorrowOrigin {
                    parameter: 0,
                    field: None,
                    projection
                })),
                Origin::Conflict
            );
        }
    }
}
