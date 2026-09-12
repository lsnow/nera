use super::*;

/// A normalized path fact derived from program structure.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PathFact {
    Boolean {
        value: VirValueId,
        expected: bool,
    },
    Comparison {
        predicate: VirIntegerPredicate,
        left: VirValueId,
        right: VirValueId,
    },
}

impl PathFact {
    #[must_use]
    pub const fn boolean(value: VirValueId, expected: bool) -> Self {
        Self::Boolean { value, expected }
    }

    /// Creates a canonical comparison. Symmetric predicates and reversed
    /// operands normalize to one representation.
    #[must_use]
    pub const fn comparison(
        predicate: VirIntegerPredicate,
        left: VirValueId,
        right: VirValueId,
    ) -> Self {
        if left.get() <= right.get() {
            Self::Comparison {
                predicate,
                left,
                right,
            }
        } else {
            Self::Comparison {
                predicate: swap_comparison_operands(predicate),
                left: right,
                right: left,
            }
        }
    }

    #[must_use]
    pub const fn negated(self) -> Self {
        match self {
            Self::Boolean { value, expected } => Self::Boolean {
                value,
                expected: !expected,
            },
            Self::Comparison {
                predicate,
                left,
                right,
            } => Self::Comparison {
                predicate: negate_comparison(predicate),
                left,
                right,
            },
        }
    }

    const fn constant_truth(self) -> Option<bool> {
        match self {
            Self::Comparison {
                predicate,
                left,
                right,
            } if left.get() == right.get() => Some(matches!(
                predicate,
                VirIntegerPredicate::Equal
                    | VirIntegerPredicate::LessOrEqual
                    | VirIntegerPredicate::GreaterOrEqual
            )),
            Self::Boolean { .. } | Self::Comparison { .. } => None,
        }
    }
}

const fn swap_comparison_operands(predicate: VirIntegerPredicate) -> VirIntegerPredicate {
    match predicate {
        VirIntegerPredicate::Equal => VirIntegerPredicate::Equal,
        VirIntegerPredicate::NotEqual => VirIntegerPredicate::NotEqual,
        VirIntegerPredicate::LessThan => VirIntegerPredicate::GreaterThan,
        VirIntegerPredicate::LessOrEqual => VirIntegerPredicate::GreaterOrEqual,
        VirIntegerPredicate::GreaterThan => VirIntegerPredicate::LessThan,
        VirIntegerPredicate::GreaterOrEqual => VirIntegerPredicate::LessOrEqual,
    }
}

const fn negate_comparison(predicate: VirIntegerPredicate) -> VirIntegerPredicate {
    match predicate {
        VirIntegerPredicate::Equal => VirIntegerPredicate::NotEqual,
        VirIntegerPredicate::NotEqual => VirIntegerPredicate::Equal,
        VirIntegerPredicate::LessThan => VirIntegerPredicate::GreaterOrEqual,
        VirIntegerPredicate::LessOrEqual => VirIntegerPredicate::GreaterThan,
        VirIntegerPredicate::GreaterThan => VirIntegerPredicate::LessOrEqual,
        VirIntegerPredicate::GreaterOrEqual => VirIntegerPredicate::LessThan,
    }
}

/// Conjunctive facts that hold on every execution represented by a state.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PathCondition {
    Unreachable,
    Reachable(BTreeSet<PathFact>),
}

impl PathCondition {
    #[must_use]
    pub const fn empty() -> Self {
        Self::Reachable(BTreeSet::new())
    }

    #[must_use]
    pub const fn unreachable() -> Self {
        Self::Unreachable
    }

    #[must_use]
    pub const fn is_reachable(&self) -> bool {
        matches!(self, Self::Reachable(_))
    }

    #[must_use]
    pub const fn facts(&self) -> Option<&BTreeSet<PathFact>> {
        match self {
            Self::Unreachable => None,
            Self::Reachable(facts) => Some(facts),
        }
    }

    #[must_use]
    pub fn atom_count(&self) -> usize {
        self.facts().map_or(0, BTreeSet::len)
    }

    #[must_use]
    pub fn implies(&self, fact: PathFact) -> bool {
        match self {
            Self::Unreachable => true,
            Self::Reachable(facts) => facts.contains(&fact),
        }
    }

    /// Adds one structurally derived fact. A direct fact/negation conflict
    /// makes the path unreachable; deeper solver reasoning belongs to 5.2+.
    pub fn conjoin(&mut self, fact: PathFact) {
        let Self::Reachable(facts) = self else {
            return;
        };
        if let Some(truth) = fact.constant_truth() {
            if !truth {
                *self = Self::Unreachable;
            }
            return;
        }
        if facts.contains(&fact.negated()) {
            *self = Self::Unreachable;
        } else {
            facts.insert(fact);
        }
    }

    /// Facts guaranteed on either incoming path. Unreachable is the join
    /// identity because it contributes no concrete executions.
    #[must_use]
    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Unreachable, right) => right.clone(),
            (left, Self::Unreachable) => left.clone(),
            (Self::Reachable(left), Self::Reachable(right)) => {
                Self::Reachable(left.intersection(right).copied().collect())
            }
        }
    }

    fn project(&self, renames: &[(VirValueId, VirValueId)]) -> Self {
        let Self::Reachable(facts) = self else {
            return Self::Unreachable;
        };
        // Repeated scalar arguments are legal. Keeping one deterministic
        // target per source retains a sound subset without a Cartesian blowup.
        let mut first_target_by_source = BTreeMap::new();
        for &(source, target) in renames {
            first_target_by_source.entry(source).or_insert(target);
        }

        let mut projected = Self::empty();
        for fact in facts {
            let renamed = match *fact {
                PathFact::Boolean { value, expected } => first_target_by_source
                    .get(&value)
                    .copied()
                    .map(|value| PathFact::boolean(value, expected)),
                PathFact::Comparison {
                    predicate,
                    left,
                    right,
                } => first_target_by_source
                    .get(&left)
                    .copied()
                    .zip(first_target_by_source.get(&right).copied())
                    .map(|(left, right)| PathFact::comparison(predicate, left, right)),
            };
            if let Some(fact) = renamed {
                projected.conjoin(fact);
            }
        }
        projected
    }
}

impl Default for PathCondition {
    fn default() -> Self {
        Self::empty()
    }
}

/// Complete abstract resource facts at one VIR program point.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ResourceState {
    pub(super) relations: RelationState,
    pub(super) path_condition: PathCondition,
    pub(super) allocations: BTreeMap<AbstractAllocationId, AbstractAllocation>,
    pub(super) values: BTreeMap<VirValueId, AbstractValue>,
    pub(super) word_expressions: BTreeMap<VirValueId, AffineExpression>,
    pub(super) loans: BTreeMap<VirLoanId, AbstractLoan>,
    pub(super) loan_precision_losses: BTreeSet<LoanPrecisionLoss>,
}

impl ResourceState {
    #[must_use]
    pub const fn new() -> Self {
        Self {
            relations: RelationState::new(),
            path_condition: PathCondition::empty(),
            allocations: BTreeMap::new(),
            values: BTreeMap::new(),
            word_expressions: BTreeMap::new(),
            loans: BTreeMap::new(),
            loan_precision_losses: BTreeSet::new(),
        }
    }

    #[must_use]
    pub const fn unreachable() -> Self {
        Self {
            relations: RelationState::new(),
            path_condition: PathCondition::unreachable(),
            allocations: BTreeMap::new(),
            values: BTreeMap::new(),
            word_expressions: BTreeMap::new(),
            loans: BTreeMap::new(),
            loan_precision_losses: BTreeSet::new(),
        }
    }

    #[must_use]
    pub const fn path_condition(&self) -> &PathCondition {
        &self.path_condition
    }

    pub fn conjoin_path_fact(&mut self, fact: PathFact) {
        self.path_condition.conjoin(fact);
    }

    pub(in crate::verifier) fn forget_path_condition(&mut self) {
        if self.path_condition.is_reachable() {
            self.path_condition = PathCondition::empty();
        }
    }

    pub(in crate::verifier) fn same_resource_facts(&self, other: &Self) -> bool {
        self.allocations == other.allocations
            && resource_values(&self.values) == resource_values(&other.values)
            && self.loans == other.loans
            && self.loan_precision_losses == other.loan_precision_losses
    }

    #[must_use]
    pub const fn allocations(&self) -> &BTreeMap<AbstractAllocationId, AbstractAllocation> {
        &self.allocations
    }

    #[must_use]
    pub fn allocation(&self, id: AbstractAllocationId) -> Option<&AbstractAllocation> {
        self.allocations.get(&id)
    }

    pub fn allocation_mut(&mut self, id: AbstractAllocationId) -> Option<&mut AbstractAllocation> {
        self.allocations.get_mut(&id)
    }

    pub fn define_allocation(
        &mut self,
        id: AbstractAllocationId,
        allocation: AbstractAllocation,
    ) -> Result<(), ResourceStateDefinitionError> {
        if !self.allocations.contains_key(&id)
            && self.allocations.len() >= instance::MAX_ALLOCATION_SLOTS
        {
            return Err(ResourceStateDefinitionError::AllocationInstanceBudget);
        }
        match self.allocations.entry(id) {
            Entry::Vacant(entry) => {
                entry.insert(allocation);
                Ok(())
            }
            Entry::Occupied(_) => Err(ResourceStateDefinitionError::DuplicateAllocation(id)),
        }
    }

    pub(in crate::verifier) fn replace_allocation(
        &mut self,
        id: AbstractAllocationId,
        allocation: AbstractAllocation,
    ) {
        self.allocations.insert(id, allocation);
    }

    #[must_use]
    pub const fn values(&self) -> &BTreeMap<VirValueId, AbstractValue> {
        &self.values
    }

    #[must_use]
    pub fn value(&self, id: VirValueId) -> Option<&AbstractValue> {
        self.values.get(&id)
    }

    pub fn value_mut(&mut self, id: VirValueId) -> Option<&mut AbstractValue> {
        // Arbitrary abstract-value replacement cannot retain old numeric
        // relations. Branch narrowing uses the monotone helper below instead.
        self.relations.forget_value(id);
        self.values.get_mut(&id)
    }

    pub fn relations(&self) -> &RelationState {
        &self.relations
    }

    pub(in crate::verifier) fn learn_relations(
        &mut self,
        premises: &[DifferencePremise],
        limits: DifferenceLimits,
    ) {
        self.relations.learn(premises, &self.values, limits);
        self.reduce_relation_intervals();
    }

    pub(in crate::verifier) fn limit_relations(&mut self, limits: DifferenceLimits) {
        self.relations.limit(limits);
    }

    pub(in crate::verifier) fn reduce_relation_intervals(&mut self) {
        // These bounds are already established in this whole resource case;
        // narrowing never imports a goal or a guessed loop invariant.
        for bound in self.relations.bounds().collect::<Vec<_>>() {
            let refinement = match (bound.left, bound.right) {
                (Some(value), None) => u64::try_from(bound.bound)
                    .ok()
                    .map(|upper| (value, 0, upper)),
                (None, Some(value)) => bound
                    .bound
                    .checked_neg()
                    .and_then(|n| u64::try_from(n).ok())
                    .map(|lower| (value, lower, u64::MAX)),
                _ => None,
            };
            if let Some((value, lower, upper)) = refinement {
                self.narrow_word_interval(
                    value,
                    U64Interval::new(lower, upper).expect("ordered unsigned relation bound"),
                );
            }
        }
    }

    pub(in crate::verifier) fn narrow_word_interval(
        &mut self,
        id: VirValueId,
        interval: U64Interval,
    ) {
        if let Some(AbstractValue::U64(current)) = self.values.get_mut(&id)
            && let Some(narrowed) = current.intersection(interval)
        {
            *current = narrowed;
        }
    }

    pub fn define_value(
        &mut self,
        id: VirValueId,
        value: AbstractValue,
    ) -> Result<(), ResourceStateDefinitionError> {
        match self.values.entry(id) {
            Entry::Vacant(entry) => {
                entry.insert(value);
                Ok(())
            }
            Entry::Occupied(_) => Err(ResourceStateDefinitionError::DuplicateValue(id)),
        }
    }

    #[must_use]
    pub fn word_expression(&self, id: VirValueId) -> Option<AffineExpression> {
        self.word_expressions.get(&id).copied()
    }

    pub(in crate::verifier) fn set_word_expression(
        &mut self,
        id: VirValueId,
        expression: AffineExpression,
    ) {
        self.word_expressions.insert(id, expression);
    }

    pub(in crate::verifier) fn clear_word_expression(&mut self, id: VirValueId) {
        self.word_expressions.remove(&id);
    }

    #[must_use]
    pub const fn loans(&self) -> &BTreeMap<VirLoanId, AbstractLoan> {
        &self.loans
    }

    #[must_use]
    pub fn loan(&self, id: VirLoanId) -> Option<&AbstractLoan> {
        self.loans.get(&id)
    }

    pub fn loan_mut(&mut self, id: VirLoanId) -> Option<&mut AbstractLoan> {
        self.loans.get_mut(&id)
    }

    pub fn define_loan(
        &mut self,
        id: VirLoanId,
        loan: AbstractLoan,
    ) -> Result<(), ResourceStateDefinitionError> {
        match self.loans.entry(id) {
            Entry::Vacant(entry) => {
                entry.insert(loan);
                Ok(())
            }
            Entry::Occupied(_) => Err(ResourceStateDefinitionError::DuplicateLoan(id)),
        }
    }

    /// Installs the next dynamic instance of one statically unique loan site.
    /// A loop may execute that site again only after the previous instance is
    /// definitely ended; live or uncertain instances remain a closed error.
    pub(in crate::verifier) fn define_next_loan_instance(
        &mut self,
        id: VirLoanId,
        loan: AbstractLoan,
    ) -> Result<(), ResourceStateDefinitionError> {
        match self.loans.entry(id) {
            Entry::Vacant(entry) => {
                entry.insert(loan);
                Ok(())
            }
            Entry::Occupied(mut entry) if matches!(entry.get().activity(), LoanActivity::Ended) => {
                entry.insert(loan);
                Ok(())
            }
            Entry::Occupied(_) => Err(ResourceStateDefinitionError::DuplicateLoan(id)),
        }
    }

    pub fn mark_loan_precision_loss(&mut self, loss: LoanPrecisionLoss) {
        self.loan_precision_losses.insert(loss);
    }

    #[must_use]
    pub const fn loan_precision_losses(&self) -> &BTreeSet<LoanPrecisionLoss> {
        &self.loan_precision_losses
    }

    pub(in crate::verifier) fn project_value_for_cfg(
        &self,
        source: VirValueId,
        renames: &[(VirValueId, VirValueId)],
    ) -> Option<AbstractValue> {
        let remapper = ExpressionRemapper::new(self, renames);
        self.value(source)
            .copied()
            .map(|value| remapper.value(value))
    }

    /// Keeps allocation facts while projecting path facts onto CFG edge
    /// arguments. Target values are deliberately left empty for the CFG
    /// transfer to define after checking types and linear permission moves.
    #[must_use]
    pub(in crate::verifier) fn project_cfg_edge(
        &self,
        renames: &[(VirValueId, VirValueId)],
    ) -> Self {
        if !self.path_condition.is_reachable() {
            return Self::unreachable();
        }
        let remapper = ExpressionRemapper::new(self, renames);
        let mut word_expressions = BTreeMap::new();
        for &(source, target) in renames {
            if let Some(expression) = self.word_expression(source)
                && let Some(expression) = remapper.expression(expression)
            {
                word_expressions.entry(target).or_insert(expression);
            }
        }
        Self {
            path_condition: self.path_condition.project(renames),
            relations: self.relations.project(
                &renames
                    .iter()
                    .copied()
                    .filter(|(source, _)| {
                        matches!(self.value(*source), Some(AbstractValue::U64(_)))
                    })
                    .collect::<Vec<_>>(),
            ),
            allocations: self
                .allocations
                .iter()
                .map(|(id, allocation)| (*id, allocation.project_cfg_edge(&remapper, &self.values)))
                .collect(),
            values: BTreeMap::new(),
            word_expressions,
            loans: self
                .loans
                .iter()
                .map(|(id, loan)| (*id, loan.project_cfg_edge(&remapper)))
                .collect(),
            loan_precision_losses: self.loan_precision_losses.clone(),
        }
    }

    /// Least upper bound for control-flow convergence.
    ///
    /// Value facts missing from either reachable predecessor are dropped, but
    /// outstanding allocation ownership is retained conservatively. CFG edge
    /// transfer must rename arguments to target block parameters before this
    /// operation, so retaining only common value IDs is intentional.
    pub fn join(&self, other: &Self) -> Result<Self, ResourceJoinError> {
        if !self.path_condition.is_reachable() {
            return Ok(other.clone());
        }
        if !other.path_condition.is_reachable() {
            return Ok(self.clone());
        }

        let allocations = instance::join_allocations(&self.allocations, &other.allocations)?;

        let mut values = BTreeMap::new();
        for (id, left) in &self.values {
            if let Some(right) = other.values.get(id) {
                values.insert(*id, (*left).join(*right, *id)?);
            }
        }

        let mut word_expressions = BTreeMap::new();
        for (id, left) in &self.word_expressions {
            if other.word_expressions.get(id) == Some(left) {
                word_expressions.insert(*id, *left);
            }
        }

        let (loans, loan_join_lost) = join_loans(&self.loans, &other.loans)?;
        let mut loan_precision_losses = self.loan_precision_losses.clone();
        loan_precision_losses.extend(other.loan_precision_losses.iter().copied());
        if loan_join_lost {
            loan_precision_losses.insert(LoanPrecisionLoss::LoanJoin);
        }

        Ok(Self {
            path_condition: self.path_condition.join(&other.path_condition),
            relations: self.relations.join(&other.relations),
            allocations,
            values,
            word_expressions,
            loans,
            loan_precision_losses,
        })
    }

    /// Widening for cyclic CFG entries.
    ///
    /// Structural/resource components use their conservative join while
    /// numeric and pointer-offset intervals accelerate expanding bounds to the
    /// domain limits. Callers must first establish that `next` is an ascending
    /// join successor of `self`.
    pub fn widen(&self, next: &Self) -> Result<Self, ResourceJoinError> {
        if !self.path_condition.is_reachable() {
            return Ok(next.clone());
        }
        if !next.path_condition.is_reachable() {
            return Ok(self.clone());
        }

        let allocations = instance::join_allocations(&self.allocations, &next.allocations)?;

        let mut values = BTreeMap::new();
        for (id, current) in &self.values {
            if let Some(next) = next.values.get(id) {
                values.insert(*id, (*current).widen(*next, *id)?);
            }
        }

        let mut word_expressions = BTreeMap::new();
        for (id, current) in &self.word_expressions {
            if next.word_expressions.get(id) == Some(current) {
                word_expressions.insert(*id, *current);
            }
        }

        let (loans, loan_widening_lost) = join_loans(&self.loans, &next.loans)?;
        let mut loan_precision_losses = self.loan_precision_losses.clone();
        loan_precision_losses.extend(next.loan_precision_losses.iter().copied());
        if loan_widening_lost {
            loan_precision_losses.insert(LoanPrecisionLoss::LoanLoopWidening);
        }

        Ok(Self {
            path_condition: self.path_condition.join(&next.path_condition),
            relations: self.relations.widen(&next.relations),
            allocations,
            values,
            word_expressions,
            loans,
            loan_precision_losses,
        })
    }
}

pub(super) fn join_loans(
    left: &BTreeMap<VirLoanId, AbstractLoan>,
    right: &BTreeMap<VirLoanId, AbstractLoan>,
) -> Result<(BTreeMap<VirLoanId, AbstractLoan>, bool), ResourceJoinError> {
    let mut joined = BTreeMap::new();
    let mut precision_lost = false;
    for id in left
        .keys()
        .chain(right.keys())
        .copied()
        .collect::<BTreeSet<_>>()
    {
        let loan = match (left.get(&id), right.get(&id)) {
            (Some(left), Some(right)) => {
                let result = left.join(right, id)?;
                // Ended, authority-free instances are tombstones only. Their
                // old offsets can differ across loop iterations without
                // losing any live alias/permission obligation.
                let ended = left.activity == LoanActivity::Ended
                    && right.activity == LoanActivity::Ended
                    && left.authorities.is_empty()
                    && right.authorities.is_empty();
                precision_lost |= !ended && (result != *left || result != *right);
                Some(result)
            }
            // An ended loan carries no live authority.  Dropping its
            // tombstone when the other alternative has never executed that
            // static site is exact, and lets a loop-local LoanBegin represent
            // a fresh dynamic instance on the next iteration.
            (Some(loan), None) | (None, Some(loan))
                if matches!(loan.activity(), LoanActivity::Ended) =>
            {
                None
            }
            (Some(loan), None) | (None, Some(loan)) => {
                let result = loan.join_absent();
                precision_lost |=
                    result != *loan || !matches!(loan.activity(), LoanActivity::Ended);
                Some(result)
            }
            (None, None) => unreachable!(),
        };
        if let Some(loan) = loan {
            joined.insert(id, loan);
        }
    }
    Ok((joined, precision_lost))
}

fn resource_values(
    values: &BTreeMap<VirValueId, AbstractValue>,
) -> BTreeMap<VirValueId, AbstractValue> {
    values
        .iter()
        .filter_map(|(id, value)| {
            matches!(
                value,
                AbstractValue::Pointer(_)
                    | AbstractValue::Permission(_)
                    | AbstractValue::EnumDiscriminant(_)
            )
            .then_some((*id, *value))
        })
        .collect()
}

pub(in crate::verifier) struct ExpressionRemapper {
    pub(super) roots: BTreeMap<VirValueId, VirValueId>,
    pub(super) expressions: Vec<(AffineExpression, VirValueId)>,
    pub(super) prefix_expressions: Vec<(AffineExpression, VirValueId)>,
}

impl ExpressionRemapper {
    pub(in crate::verifier) fn new(
        state: &ResourceState,
        renames: &[(VirValueId, VirValueId)],
    ) -> Self {
        let mut roots = BTreeMap::new();
        let mut expressions = Vec::new();
        let mut prefix_expressions = Vec::new();
        for &(source, target) in renames {
            roots.entry(source).or_insert(target);
            if let Some(AbstractValue::U64(value)) = state.value(source) {
                prefix_expressions.push((AffineExpression::identity(source), target));
                let expression = state.word_expression(source).unwrap_or_else(|| {
                    value
                        .exact_value()
                        .map(AffineExpression::constant)
                        .unwrap_or_else(|| AffineExpression::identity(source))
                });
                prefix_expressions.push((expression, target));
            }
            if let Some(expression) = state.word_expression(source)
                && !expressions.iter().any(|(known, _)| *known == expression)
            {
                expressions.push((expression, target));
            }
        }
        // An identity-view result (or zero-start slice length) can carry a
        // root under a new SSA ID. Only exact x aliases may rename scaled
        // endpoints; arbitrary x+k expressions are not treated as identities.
        for (expression, target) in &expressions {
            if expression.scale() == 1
                && expression.addend() == 0
                && let Some(root) = expression.root()
            {
                roots.entry(root).or_insert(*target);
            }
        }
        Self {
            roots,
            expressions,
            prefix_expressions,
        }
    }

    pub(in crate::verifier) fn expression(
        &self,
        expression: AffineExpression,
    ) -> Option<AffineExpression> {
        if expression.is_constant() {
            return Some(expression);
        }
        // Preserve a fixed-stride decomposition when every root is carried
        // by the edge. Replacing i+width with a fresh endpoint identity loses
        // the chunk width and forces unnecessary DBM equalities/closure.
        if let Some(renamed) = expression.rename_root(&self.roots) {
            return Some(renamed);
        }
        if let Some((_, target)) = self
            .expressions
            .iter()
            .find(|(known, _)| *known == expression)
        {
            return Some(AffineExpression::identity(*target));
        }
        None
    }

    pub(in crate::verifier) fn bound(
        &self,
        bound: SymbolicRangeBound,
    ) -> Option<SymbolicRangeBound> {
        Some(SymbolicRangeBound::new(
            self.expression(bound.expression())?,
            bound.interval(),
        ))
    }

    pub(in crate::verifier) fn range(&self, range: AbstractByteRange) -> AbstractByteRange {
        match range {
            AbstractByteRange::Exact(_) | AbstractByteRange::Unknown => range,
            AbstractByteRange::Symbolic { start, end } => {
                match (self.bound(start), self.bound(end)) {
                    (Some(start), Some(end)) => AbstractByteRange::from_bounds(start, end),
                    _ => AbstractByteRange::Unknown,
                }
            }
        }
    }

    pub(in crate::verifier) fn value(&self, value: AbstractValue) -> AbstractValue {
        match value {
            AbstractValue::Pointer(pointer) => AbstractValue::Pointer(self.pointer(pointer)),
            AbstractValue::Permission(permission) => {
                AbstractValue::Permission(self.permission(permission))
            }
            AbstractValue::EnumDiscriminant(fact) => {
                AbstractValue::EnumDiscriminant(EnumDiscriminantFact::new(
                    fact.interval(),
                    self.pointer(fact.pointer()),
                    fact.access(),
                ))
            }
            AbstractValue::U64(_) | AbstractValue::Bool(_) => value,
        }
    }

    pub(in crate::verifier) fn pointer(&self, pointer: AbstractPointer) -> AbstractPointer {
        pointer
            .with_domain(match pointer.domain() {
                crate::VirPointerDomain::Restricted(range) => {
                    crate::VirPointerDomain::Restricted(self.range(range))
                }
                domain => domain,
            })
            .with_slice_footprint(pointer.slice_footprint().map(|f| f.project(self)))
            .with_offset_expression(
                pointer
                    .offset_expression()
                    .and_then(|expression| self.expression(expression)),
            )
    }

    pub(in crate::verifier) fn permission(
        &self,
        permission: AbstractPermission,
    ) -> AbstractPermission {
        AbstractPermission::new(
            permission.provenance(),
            self.range(permission.range()),
            permission.access(),
            permission.free_capability(),
        )
        .with_availability(permission.availability())
        .with_authority(permission.authority())
    }
}

/// One atomic path-local resource state. Stage 7.1.4 may place bounded guards
/// around cases, but the facts inside a case continue to have this sole owner.
pub type ResourceCase = ResourceState;

/// Invalid definitions or unavailable fresh-instance capacity in one state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResourceStateDefinitionError {
    AllocationInstanceBudget,
    AllocationInstanceStillReferenced(AbstractAllocationId),
    DuplicateAllocation(AbstractAllocationId),
    DuplicateValue(VirValueId),
    DuplicateLoan(VirLoanId),
}

impl fmt::Display for ResourceStateDefinitionError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AllocationInstanceBudget => {
                formatter.write_str("allocation instance slot budget exhausted")
            }
            Self::AllocationInstanceStillReferenced(allocation) => write!(
                formatter,
                "cannot reuse allocation slot {allocation}: a previous instance may still own resources or loan authority"
            ),
            Self::DuplicateAllocation(allocation) => write!(
                formatter,
                "abstract allocation {allocation} is defined more than once"
            ),
            Self::DuplicateValue(value) => {
                write!(
                    formatter,
                    "abstract value %{} is defined more than once",
                    value.get()
                )
            }
            Self::DuplicateLoan(loan) => {
                write!(
                    formatter,
                    "abstract loan l{} is defined more than once",
                    loan.get()
                )
            }
        }
    }
}

impl Error for ResourceStateDefinitionError {}

/// Metadata mismatch or exhausted allocation capacity at a resource-state join.
///
/// These fail analysis rather than returning a partial resource state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ResourceJoinError {
    AllocationInstanceBudget,
    AllocationRegionMismatch { allocation: AbstractAllocationId },
    AllocationSizeMismatch { allocation: AbstractAllocationId },
    AllocationAlignmentMismatch { allocation: AbstractAllocationId },
    ValueKindMismatch { value: VirValueId },
    LoanMetadataMismatch { loan: VirLoanId },
}

impl fmt::Display for ResourceJoinError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AllocationInstanceBudget => formatter
                .write_str("allocation instance slot budget exhausted at resource-state join"),
            Self::AllocationRegionMismatch { allocation } => write!(
                formatter,
                "allocation {allocation} has inconsistent regions at resource-state join"
            ),
            Self::AllocationSizeMismatch { allocation } => write!(
                formatter,
                "allocation {allocation} has inconsistent sizes at resource-state join"
            ),
            Self::AllocationAlignmentMismatch { allocation } => write!(
                formatter,
                "allocation {allocation} has inconsistent alignments at resource-state join"
            ),
            Self::ValueKindMismatch { value } => write!(
                formatter,
                "value %{} has inconsistent kinds at resource-state join",
                value.get()
            ),
            Self::LoanMetadataMismatch { loan } => write!(
                formatter,
                "loan l{} has inconsistent immutable metadata at resource-state join",
                loan.get()
            ),
        }
    }
}

impl Error for ResourceJoinError {}
