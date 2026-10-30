//! Bounded, typed predicate expressions. Evaluating a resource position only
//! returns an existing identity supplied by the resource checker; it grants no
//! permission. Declaration binders and opened instance binders are distinct.
use std::collections::{BTreeMap, BTreeSet};

pub(crate) mod affine;
mod boolean;
mod boolean_equivalence;
mod boolean_normalize;
mod capture_join;
mod evaluation;
pub(crate) mod facts;
mod propositional;
pub(crate) mod query;
pub(crate) mod scalar_template;

pub const MAX_LOGIC_PARAMETERS: usize = 32;
pub const MAX_EXISTENTIALS: usize = 32;
pub const MAX_EXPRESSION_NODES: usize = 256;
pub const MAX_EXPRESSION_DEPTH: usize = 32;
pub const MAX_SUBSTITUTION_NODES: usize = 4096;
pub const MAX_CONSTRAINTS: usize = 32;
pub const MAX_LINEAR_TERMS: usize = 16;
pub const MAX_BOOLEAN_BRANCHES: usize = 16;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LogicType<T> {
    U64,
    Usize,
    Bool,
    Resource(T),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ObservationTime {
    Entry,
    Current,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum LogicBinder {
    Parameter(u32),
    Existential(u32),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LogicNodeKind<T> {
    Word(u64),
    Bool(bool),
    Binder(LogicBinder),
    Observe {
        resource: u32,
        offset: u64,
        access: T,
        time: ObservationTime,
    },
    /// Every path step selects an actual typed owner/reference payload.
    Resource {
        resource: u32,
        path: Vec<u64>,
    },
    Add(u32, u32),
    Sub(u32, u32),
    Scale {
        operand: u32,
        factor: u64,
    },
    Equal(u32, u32),
    Less(u32, u32),
    LessEqual(u32, u32),
    Not(u32),
    And(u32, u32),
    Or(u32, u32),
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LogicNode<T> {
    pub ty: LogicType<T>,
    pub kind: LogicNodeKind<T>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LogicExpression<T> {
    pub nodes: Vec<LogicNode<T>>,
    pub root: u32,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LogicParameter<T> {
    /// Position among resource and logical parameters in source order.
    pub position: usize,
    pub name: String,
    pub ty: LogicType<T>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Existential<T> {
    pub name: String,
    pub ty: LogicType<T>,
    pub default: Option<LogicExpression<T>>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PredicateLogic<T> {
    pub parameters: Vec<LogicParameter<T>>,
    pub existentials: Vec<Existential<T>>,
    pub constraints: Vec<LogicExpression<T>>,
}
impl<T> Default for PredicateLogic<T> {
    fn default() -> Self {
        Self {
            parameters: vec![],
            existentials: vec![],
            constraints: vec![],
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LogicError {
    Budget,
    InvalidNode,
    TypeMismatch,
    Unbound,
    DuplicateName,
    MissingWitness,
    Unproved,
    Overflow,
    StaleInstance,
}

/// One budget is shared by all expressions of an instantiation, including the
/// caller's actuals and explicit witnesses. Cloning an expression cannot reset it.
#[derive(Clone, Debug)]
pub struct LogicBudget {
    remaining: usize,
}
impl Default for LogicBudget {
    fn default() -> Self {
        Self {
            remaining: MAX_SUBSTITUTION_NODES,
        }
    }
}
impl LogicBudget {
    pub fn charge(&mut self, amount: usize) -> Result<(), LogicError> {
        self.remaining = self
            .remaining
            .checked_sub(amount)
            .ok_or(LogicError::Budget)?;
        Ok(())
    }
}

impl<T: Copy + Eq> LogicExpression<T> {
    pub fn validate(
        &self,
        parameters: &[LogicType<T>],
        existentials: &[LogicType<T>],
        observation: &impl Fn(u32, u64, T, ObservationTime) -> Option<LogicType<T>>,
        resource: &impl Fn(u32, &[u64]) -> Option<T>,
        budget: &mut LogicBudget,
    ) -> Result<LogicType<T>, LogicError> {
        budget.charge(self.nodes.len())?;
        if self.nodes.is_empty()
            || self.nodes.len() > MAX_EXPRESSION_NODES
            || self.root as usize + 1 != self.nodes.len()
        {
            return Err(LogicError::Budget);
        }
        let mut depths = Vec::<usize>::new();
        let mut branches = Vec::<(usize, usize)>::new();
        for (index, node) in self.nodes.iter().enumerate() {
            let get = |id: u32| {
                self.nodes
                    .get(id as usize)
                    .filter(|_| (id as usize) < index)
                    .map(|n| n.ty)
                    .ok_or(LogicError::InvalidNode)
            };
            let mut children = Vec::new();
            let word = |ty| matches!(ty, LogicType::U64 | LogicType::Usize);
            let inferred = match &node.kind {
                LogicNodeKind::Word(_) if word(node.ty) => node.ty,
                LogicNodeKind::Bool(_) => LogicType::Bool,
                LogicNodeKind::Binder(LogicBinder::Parameter(id)) => {
                    *parameters.get(*id as usize).ok_or(LogicError::Unbound)?
                }
                LogicNodeKind::Binder(LogicBinder::Existential(id)) => {
                    *existentials.get(*id as usize).ok_or(LogicError::Unbound)?
                }
                LogicNodeKind::Observe {
                    resource: r,
                    offset,
                    access,
                    time,
                } => observation(*r, *offset, *access, *time).ok_or(LogicError::InvalidNode)?,
                LogicNodeKind::Resource { resource: r, path } => {
                    if path.len() > 16 {
                        return Err(LogicError::Budget);
                    }
                    LogicType::Resource(resource(*r, path).ok_or(LogicError::InvalidNode)?)
                }
                LogicNodeKind::Scale { operand, factor: _ } => {
                    let ty = get(*operand)?;
                    children.push(*operand);
                    if !word(ty) {
                        return Err(LogicError::TypeMismatch);
                    }
                    ty
                }
                LogicNodeKind::Not(operand) => {
                    if get(*operand)? != LogicType::Bool {
                        return Err(LogicError::TypeMismatch);
                    }
                    children.push(*operand);
                    LogicType::Bool
                }
                LogicNodeKind::Add(a, b)
                | LogicNodeKind::Sub(a, b)
                | LogicNodeKind::Equal(a, b)
                | LogicNodeKind::Less(a, b)
                | LogicNodeKind::LessEqual(a, b)
                | LogicNodeKind::And(a, b)
                | LogicNodeKind::Or(a, b) => {
                    let ty = get(*a)?;
                    if ty != get(*b)? {
                        return Err(LogicError::TypeMismatch);
                    }
                    children.extend([*a, *b]);
                    match node.kind {
                        LogicNodeKind::Add(..) | LogicNodeKind::Sub(..) if word(ty) => ty,
                        LogicNodeKind::Equal(..) => LogicType::Bool,
                        LogicNodeKind::Less(..) | LogicNodeKind::LessEqual(..) if word(ty) => {
                            LogicType::Bool
                        }
                        LogicNodeKind::And(..) | LogicNodeKind::Or(..) if ty == LogicType::Bool => {
                            LogicType::Bool
                        }
                        _ => return Err(LogicError::TypeMismatch),
                    }
                }
                _ => return Err(LogicError::InvalidNode),
            };
            if inferred != node.ty {
                return Err(LogicError::TypeMismatch);
            }
            let depth = children
                .iter()
                .map(|id| depths[*id as usize])
                .max()
                .unwrap_or(0)
                + 1;
            // Track both polarities. A NOT must swap DNF/CNF growth rather
            // than reset the count and let nested negations evade the bound.
            let sum = |a: usize, b: usize| a.checked_add(b).ok_or(LogicError::Budget);
            let product = |a: usize, b: usize| a.checked_mul(b).ok_or(LogicError::Budget);
            let count = match node.kind {
                LogicNodeKind::Or(a, b) => {
                    let (ap, an) = branches[a as usize];
                    let (bp, bn) = branches[b as usize];
                    (sum(ap, bp)?, product(an, bn)?)
                }
                LogicNodeKind::And(a, b) => {
                    let (ap, an) = branches[a as usize];
                    let (bp, bn) = branches[b as usize];
                    (product(ap, bp)?, sum(an, bn)?)
                }
                LogicNodeKind::Not(a) => {
                    let (positive, negative) = branches[a as usize];
                    (negative, positive)
                }
                _ => (1, 1),
            };
            if depth > MAX_EXPRESSION_DEPTH
                || count.0 > MAX_BOOLEAN_BRANCHES
                || count.1 > MAX_BOOLEAN_BRANCHES
            {
                return Err(LogicError::Budget);
            }
            depths.push(depth);
            branches.push(count);
        }
        // Dead terms are disallowed: otherwise an unreferenced subtree could
        // hide a malformed witness or evade structural budget accounting.
        let mut used = BTreeSet::new();
        let mut pending = vec![self.root];
        while let Some(id) = pending.pop() {
            if !used.insert(id) {
                continue;
            }
            match &self.nodes[id as usize].kind {
                LogicNodeKind::Add(a, b)
                | LogicNodeKind::Sub(a, b)
                | LogicNodeKind::Equal(a, b)
                | LogicNodeKind::Less(a, b)
                | LogicNodeKind::LessEqual(a, b)
                | LogicNodeKind::And(a, b)
                | LogicNodeKind::Or(a, b) => pending.extend([*a, *b]),
                LogicNodeKind::Scale { operand, .. } | LogicNodeKind::Not(operand) => {
                    pending.push(*operand)
                }
                _ => {}
            }
        }
        if used.len() != self.nodes.len() {
            return Err(LogicError::InvalidNode);
        }
        Ok(self.nodes[self.root as usize].ty)
    }

    pub fn map_access<U: Copy>(
        &self,
        map: &mut impl FnMut(T) -> Result<U, LogicError>,
    ) -> Result<LogicExpression<U>, LogicError> {
        let mut nodes = Vec::new();
        for node in &self.nodes {
            let ty = match node.ty {
                LogicType::U64 => LogicType::U64,
                LogicType::Usize => LogicType::Usize,
                LogicType::Bool => LogicType::Bool,
                LogicType::Resource(t) => LogicType::Resource(map(t)?),
            };
            let kind = match &node.kind {
                LogicNodeKind::Word(n) => LogicNodeKind::Word(*n),
                LogicNodeKind::Bool(b) => LogicNodeKind::Bool(*b),
                LogicNodeKind::Binder(b) => LogicNodeKind::Binder(*b),
                LogicNodeKind::Observe {
                    resource,
                    offset,
                    access,
                    time,
                } => LogicNodeKind::Observe {
                    resource: *resource,
                    offset: *offset,
                    access: map(*access)?,
                    time: *time,
                },
                LogicNodeKind::Resource { resource, path } => LogicNodeKind::Resource {
                    resource: *resource,
                    path: path.clone(),
                },
                LogicNodeKind::Add(a, b) => LogicNodeKind::Add(*a, *b),
                LogicNodeKind::Sub(a, b) => LogicNodeKind::Sub(*a, *b),
                LogicNodeKind::Scale { operand, factor } => LogicNodeKind::Scale {
                    operand: *operand,
                    factor: *factor,
                },
                LogicNodeKind::Equal(a, b) => LogicNodeKind::Equal(*a, *b),
                LogicNodeKind::Less(a, b) => LogicNodeKind::Less(*a, *b),
                LogicNodeKind::LessEqual(a, b) => LogicNodeKind::LessEqual(*a, *b),
                LogicNodeKind::Not(a) => LogicNodeKind::Not(*a),
                LogicNodeKind::And(a, b) => LogicNodeKind::And(*a, *b),
                LogicNodeKind::Or(a, b) => LogicNodeKind::Or(*a, *b),
            };
            nodes.push(LogicNode { ty, kind });
        }
        Ok(LogicExpression {
            nodes,
            root: self.root,
        })
    }
}

impl<T: Copy + Eq> PredicateLogic<T> {
    pub fn validate(
        &self,
        resource_names: &[&str],
        observation: &impl Fn(u32, u64, T, ObservationTime) -> Option<LogicType<T>>,
        resource: &impl Fn(u32, &[u64]) -> Option<T>,
    ) -> Result<(), LogicError> {
        if self.parameters.len() > MAX_LOGIC_PARAMETERS
            || self.existentials.len() > MAX_EXISTENTIALS
            || self.constraints.len() > MAX_CONSTRAINTS
        {
            return Err(LogicError::Budget);
        }
        let mut names = resource_names.iter().copied().collect::<BTreeSet<_>>();
        if names.len() != resource_names.len() {
            return Err(LogicError::DuplicateName);
        }
        let mut budget = LogicBudget::default();
        let mut parameters = Vec::new();
        let mut witnesses = Vec::new();
        if self
            .parameters
            .windows(2)
            .any(|p| p[0].position >= p[1].position)
        {
            return Err(LogicError::InvalidNode);
        }
        let mut positions = BTreeSet::new();
        for parameter in &self.parameters {
            if parameter.position >= resource_names.len() + self.parameters.len()
                || !positions.insert(parameter.position)
            {
                return Err(LogicError::InvalidNode);
            }
            if parameter.name.is_empty() || !names.insert(&parameter.name) {
                return Err(LogicError::DuplicateName);
            }
            if matches!(parameter.ty, LogicType::Resource(_)) {
                return Err(LogicError::TypeMismatch);
            }
            parameters.push(parameter.ty);
        }
        for witness in &self.existentials {
            if witness.name.is_empty() || !names.insert(&witness.name) {
                return Err(LogicError::DuplicateName);
            }
            if let Some(expression) = &witness.default
                && expression.validate(
                    &parameters,
                    &witnesses,
                    observation,
                    resource,
                    &mut budget,
                )? != witness.ty
            {
                return Err(LogicError::TypeMismatch);
            }
            witnesses.push(witness.ty);
        }
        for constraint in &self.constraints {
            if constraint.validate(&parameters, &witnesses, observation, resource, &mut budget)?
                != LogicType::Bool
            {
                return Err(LogicError::TypeMismatch);
            }
        }
        Ok(())
    }
}

/// Binder qualification is independent of the witness value. Neither equal
/// numbers nor a repeated declaration index permit cross-instance substitution.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InstanceScope {
    pub declaration: u32,
    pub instance: u64,
    pub opening: u64,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct OpenedBinder {
    pub scope: InstanceScope,
    pub binder: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpenedBindings<V> {
    scope: InstanceScope,
    values: Vec<V>,
}
impl<V: Clone> OpenedBindings<V> {
    pub fn new(scope: InstanceScope, values: Vec<V>) -> Result<Self, LogicError> {
        if values.len() > MAX_EXISTENTIALS {
            return Err(LogicError::Budget);
        }
        Ok(Self { scope, values })
    }
    pub fn read(&self, binder: OpenedBinder) -> Result<V, LogicError> {
        if binder.scope != self.scope {
            return Err(LogicError::StaleInstance);
        }
        self.values
            .get(binder.binder as usize)
            .cloned()
            .ok_or(LogicError::Unbound)
    }
}

/// A checked affine value. Atom identities include observation time and
/// instance scope at the adapter boundary. Arithmetic never wraps.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AffineValue<A: Ord> {
    pub(crate) lower: u64,
    pub(crate) upper: u64,
    pub(crate) constant: i128,
    pub(crate) terms: BTreeMap<A, i128>,
}
impl<A: Ord + Clone> AffineValue<A> {
    pub fn exact(value: u64) -> Self {
        Self {
            lower: value,
            upper: value,
            constant: i128::from(value),
            terms: BTreeMap::new(),
        }
    }
    pub fn variable(atom: A, lower: u64, upper: u64) -> Result<Self, LogicError> {
        if lower > upper {
            return Err(LogicError::InvalidNode);
        }
        if lower == upper {
            return Ok(Self::exact(lower));
        }
        Self::identified(atom, lower, upper)
    }
    /// Keep the supplied identity even when its current numeric range is a
    /// singleton. Only an adapter with actual identity evidence should choose
    /// this constructor; numeric equality alone does not supply an identity.
    pub(crate) fn identified(atom: A, lower: u64, upper: u64) -> Result<Self, LogicError> {
        if lower > upper {
            return Err(LogicError::InvalidNode);
        }
        Ok(Self {
            lower,
            upper,
            constant: 0,
            terms: BTreeMap::from([(atom, 1)]),
        })
    }
    pub fn add(&self, other: &Self) -> Result<Self, LogicError> {
        self.combine(other, false)
    }
    pub fn sub(&self, other: &Self) -> Result<Self, LogicError> {
        self.combine(other, true)
    }
    fn combine(&self, other: &Self, subtract: bool) -> Result<Self, LogicError> {
        let mut terms = self.terms.clone();
        let sign = if subtract { -1 } else { 1 };
        for (atom, n) in &other.terms {
            let value = terms.entry(atom.clone()).or_default();
            *value = value
                .checked_add(n.checked_mul(sign).ok_or(LogicError::Overflow)?)
                .ok_or(LogicError::Overflow)?;
        }
        terms.retain(|_, n| *n != 0);
        if terms.len() > MAX_LINEAR_TERMS {
            return Err(LogicError::Budget);
        }
        let constant = self
            .constant
            .checked_add(
                other
                    .constant
                    .checked_mul(sign)
                    .ok_or(LogicError::Overflow)?,
            )
            .ok_or(LogicError::Overflow)?;
        if terms.is_empty() {
            let value = u64::try_from(constant).map_err(|_| LogicError::Overflow)?;
            return Ok(Self::exact(value));
        }
        let (lower, upper) = if subtract {
            (
                self.lower.checked_sub(other.upper),
                self.upper.checked_sub(other.lower),
            )
        } else {
            (
                self.lower.checked_add(other.lower),
                self.upper.checked_add(other.upper),
            )
        };
        Ok(Self {
            lower: lower.ok_or(LogicError::Overflow)?,
            upper: upper.ok_or(LogicError::Overflow)?,
            constant,
            terms,
        })
    }
    pub fn scale(&self, factor: u64) -> Result<Self, LogicError> {
        if factor == 0 {
            return Ok(Self::exact(0));
        }
        Ok(Self {
            lower: self.lower.checked_mul(factor).ok_or(LogicError::Overflow)?,
            upper: self.upper.checked_mul(factor).ok_or(LogicError::Overflow)?,
            constant: self
                .constant
                .checked_mul(i128::from(factor))
                .ok_or(LogicError::Overflow)?,
            terms: self
                .terms
                .iter()
                .map(|(a, n)| {
                    Ok((
                        a.clone(),
                        n.checked_mul(i128::from(factor))
                            .ok_or(LogicError::Overflow)?,
                    ))
                })
                .collect::<Result<_, LogicError>>()?,
        })
    }
    pub fn equal(&self, other: &Self) -> Option<bool> {
        if self.terms == other.terms {
            return Some(self.constant == other.constant);
        }
        if self.lower == self.upper && other.lower == other.upper {
            return Some(self.lower == other.lower);
        }
        if self.upper < other.lower || other.upper < self.lower {
            Some(false)
        } else {
            None
        }
    }
    pub fn less_equal(&self, other: &Self) -> Option<bool> {
        if self.terms == other.terms {
            return Some(self.constant <= other.constant);
        }
        if self.upper <= other.lower {
            Some(true)
        } else if self.lower > other.upper {
            Some(false)
        } else {
            None
        }
    }
}

/// Numeric operand type retained by Boolean comparison captures. The result
/// remains Bool; this type distinguishes the numeric reasoning domains.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum WordType {
    U64,
    Usize,
}
impl WordType {
    fn from_logic_type<T>(ty: LogicType<T>) -> Result<Self, LogicError> {
        match ty {
            LogicType::U64 => Ok(Self::U64),
            LogicType::Usize => Ok(Self::Usize),
            _ => Err(LogicError::TypeMismatch),
        }
    }
    pub(crate) fn logic_type<T>(self) -> LogicType<T> {
        match self {
            Self::U64 => LogicType::U64,
            Self::Usize => LogicType::Usize,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum WordComparison {
    Equal,
    LessEqual,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum BooleanOperation {
    And,
    Or,
    Equal,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LogicValue<A: Ord, R> {
    Word(AffineValue<A>),
    Bool(Option<bool>),
    BoolAtom {
        atom: A,
        negated: bool,
        /// Known truth of the atom before negation; refinement is not identity.
        known: Option<bool>,
    },
    BoolComparison {
        word_type: WordType,
        comparison: WordComparison,
        left: AffineValue<A>,
        right: AffineValue<A>,
        negated: bool,
    },
    BoolBinary {
        operation: BooleanOperation,
        left: Box<Self>,
        right: Box<Self>,
        negated: bool,
    },
    Resource(R),
    /// A hidden resource position from an existential package. This symbol
    /// carries no pointer, allocation or permission and cannot authorize access.
    ResourceAtom {
        atom: A,
    },
}
impl<A: Ord + Clone, R: Clone> LogicValue<A, R> {
    /// Truth under the captured bounds, without erasing the expression shape.
    pub(crate) fn known_boolean(&self) -> Option<bool> {
        match self {
            Self::Bool(value) => *value,
            Self::BoolAtom { known, negated, .. } => known.map(|value| value ^ negated),
            Self::BoolComparison {
                comparison,
                left,
                right,
                negated,
                ..
            } => {
                let known = match comparison {
                    WordComparison::Equal => left.equal(right),
                    WordComparison::LessEqual => left.less_equal(right),
                };
                known.map(|value| value ^ negated)
            }
            Self::BoolBinary {
                operation,
                left,
                right,
                negated,
            } => operation
                .evaluate(left.known_boolean(), right.known_boolean())
                .map(|value| value ^ negated),
            _ => None,
        }
    }

    /// Apply an established truth without discarding an atom's identity.
    /// The caller must establish the premise and any runtime source matching.
    pub(crate) fn with_known_boolean(&self, truth: bool) -> Result<Self, LogicError> {
        if self
            .known_boolean()
            .is_some_and(|previous| previous != truth)
        {
            return Err(LogicError::Unproved);
        }
        match self {
            Self::BoolAtom { atom, negated, .. } => Ok(Self::BoolAtom {
                atom: atom.clone(),
                negated: *negated,
                known: Some(truth ^ negated),
            }),
            Self::Bool(_) | Self::BoolComparison { .. } | Self::BoolBinary { .. } => {
                Ok(Self::Bool(Some(truth)))
            }
            _ => Err(LogicError::TypeMismatch),
        }
    }

    /// Anonymous unknowns never acquire identity from abstract-value equality.
    pub fn bool_equal(&self, other: &Self) -> Option<bool> {
        if let (Some(a), Some(b)) = (self.known_boolean(), other.known_boolean()) {
            return Some(a == b);
        }
        match (self, other) {
            (
                Self::BoolBinary {
                    operation: a,
                    left: al,
                    right: ar,
                    negated: an,
                },
                Self::BoolBinary {
                    operation: b,
                    left: bl,
                    right: br,
                    negated: bn,
                },
            ) if a == b && al.bool_equal(bl) == Some(true) && ar.bool_equal(br) == Some(true) => {
                Some(an == bn)
            }
            (Self::Bool(a), Self::Bool(b)) => a.zip(*b).map(|(a, b)| a == b),
            (
                Self::BoolAtom {
                    atom: a,
                    negated: x,
                    ..
                },
                Self::BoolAtom {
                    atom: b,
                    negated: y,
                    ..
                },
            ) if a == b => Some(x == y),
            (
                Self::BoolComparison {
                    word_type: at,
                    comparison: a,
                    left: al,
                    right: ar,
                    negated: an,
                },
                Self::BoolComparison {
                    word_type: bt,
                    comparison: b,
                    left: bl,
                    right: br,
                    negated: bn,
                },
            ) if at == bt
                && a == b
                && ((al.equal(bl) == Some(true) && ar.equal(br) == Some(true))
                    || (*a == WordComparison::Equal
                        && al.equal(br) == Some(true)
                        && ar.equal(bl) == Some(true))) =>
            {
                Some(an == bn)
            }
            _ => None,
        }
    }
    fn bool_not(&self) -> Self {
        match self {
            Self::BoolBinary {
                operation,
                left,
                right,
                negated,
            } => Self::BoolBinary {
                operation: *operation,
                left: left.clone(),
                right: right.clone(),
                negated: !negated,
            },
            Self::Bool(v) => Self::Bool(v.map(|v| !v)),
            Self::BoolAtom {
                atom,
                negated,
                known,
            } => Self::BoolAtom {
                atom: atom.clone(),
                negated: !negated,
                known: *known,
            },
            Self::BoolComparison {
                word_type,
                comparison,
                left,
                right,
                negated,
            } => Self::BoolComparison {
                word_type: *word_type,
                comparison: *comparison,
                left: left.clone(),
                right: right.clone(),
                negated: !negated,
            },
            _ => unreachable!("validated Boolean operand"),
        }
    }
    fn word_comparison(
        word_type: WordType,
        comparison: WordComparison,
        left: AffineValue<A>,
        right: AffineValue<A>,
        negated: bool,
    ) -> Self {
        let known = match comparison {
            WordComparison::Equal => left.equal(&right),
            WordComparison::LessEqual => left.less_equal(&right),
        };
        match known {
            Some(value) => Self::Bool(Some(value ^ negated)),
            None => Self::BoolComparison {
                word_type,
                comparison,
                left,
                right,
                negated,
            },
        }
    }
    fn bool_combine(&self, other: &Self, is_or: bool) -> Self {
        match (self, other) {
            (Self::Bool(Some(v)), _) if *v == is_or => self.clone(),
            (_, Self::Bool(Some(v))) if *v == is_or => other.clone(),
            (Self::Bool(Some(_)), _) => other.clone(),
            (_, Self::Bool(Some(_))) => self.clone(),
            _ => match self.bool_equal(other) {
                Some(true) => self.clone(),
                Some(false) => Self::Bool(Some(is_or)),
                None => Self::Bool(None),
            },
        }
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TypedLogicValue<T, A: Ord, R> {
    pub ty: LogicType<T>,
    pub value: LogicValue<A, R>,
}

impl<T: Copy + Eq> PredicateLogic<T> {
    pub fn map_access<U: Copy>(
        &self,
        map: &mut impl FnMut(T) -> Result<U, LogicError>,
    ) -> Result<PredicateLogic<U>, LogicError> {
        fn ty<T: Copy, U>(
            t: LogicType<T>,
            map: &mut impl FnMut(T) -> Result<U, LogicError>,
        ) -> Result<LogicType<U>, LogicError> {
            Ok(match t {
                LogicType::U64 => LogicType::U64,
                LogicType::Usize => LogicType::Usize,
                LogicType::Bool => LogicType::Bool,
                LogicType::Resource(t) => LogicType::Resource(map(t)?),
            })
        }
        let parameters = self
            .parameters
            .iter()
            .map(|p| {
                Ok(LogicParameter {
                    position: p.position,
                    name: p.name.clone(),
                    ty: ty(p.ty, map)?,
                })
            })
            .collect::<Result<_, LogicError>>()?;
        let existentials = self
            .existentials
            .iter()
            .map(|w| {
                Ok(Existential {
                    name: w.name.clone(),
                    ty: ty(w.ty, map)?,
                    default: w.default.as_ref().map(|e| e.map_access(map)).transpose()?,
                })
            })
            .collect::<Result<_, LogicError>>()?;
        let constraints = self
            .constraints
            .iter()
            .map(|e| e.map_access(map))
            .collect::<Result<_, LogicError>>()?;
        Ok(PredicateLogic {
            parameters,
            existentials,
            constraints,
        })
    }
}

/// A ghost input is tied to the exact opening action and holder, never an
/// address or a witness value. Runtime inputs remain ordinary SSA snapshots.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum WitnessInput<V, T> {
    Scalar(V),
    /// A postcondition's scalar return slot, distinct from entry input slots.
    Result(V),
    /// A typed scalar leaf of an indirect aggregate result. The base denotes
    /// the hidden output pointer slot, which belongs to the input ABI.
    ResultField {
        base: V,
        offset: u64,
        access: T,
    },
    /// Typed observation of local or parameter storage. Entry is
    /// resolved from the immutable boundary state before runtime evaluation.
    Memory {
        base: V,
        offset: u64,
        access: T,
        time: ObservationTime,
    },
    Opened {
        action: u32,
        holder: u32,
        binder: u32,
    },
}
impl<V, T> WitnessInput<V, T> {
    pub fn runtime_value(&self) -> Option<&V> {
        match self {
            Self::Scalar(value) | Self::Memory { base: value, .. } => Some(value),
            _ => None,
        }
    }

    pub fn scalar(&self) -> Option<&V> {
        match self {
            Self::Scalar(value) => Some(value),
            _ => None,
        }
    }
}

/// Explicit witnesses use action-local inputs, separate from declaration
/// parameters and preceding default binders. Inputs are evaluated SSA snapshots.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WitnessArguments<T, V> {
    pub inputs: Vec<(LogicType<T>, WitnessInput<V, T>)>,
    pub values: Vec<(u32, LogicExpression<T>)>,
    pub arguments: Vec<LogicExpression<T>>,
}
impl<T, V> Default for WitnessArguments<T, V> {
    fn default() -> Self {
        Self {
            inputs: vec![],
            values: vec![],
            arguments: vec![],
        }
    }
}
impl<T: Copy + Eq, V> WitnessArguments<T, V> {
    pub fn validate(
        &self,
        logic: &PredicateLogic<T>,
        observation: &impl Fn(u32, u64, T, ObservationTime) -> Option<LogicType<T>>,
        resource: &impl Fn(u32, &[u64]) -> Option<T>,
        budget: &mut LogicBudget,
    ) -> Result<(), LogicError> {
        if self.inputs.len() > MAX_LOGIC_PARAMETERS || self.values.len() > MAX_EXISTENTIALS {
            return Err(LogicError::Budget);
        }
        let parameters = self.inputs.iter().map(|(ty, _)| *ty).collect::<Vec<_>>();
        if self.inputs.iter().any(|(ty, input)| {
            matches!(ty, LogicType::Resource(_))
                && matches!(
                    input,
                    WitnessInput::Scalar(_)
                        | WitnessInput::Result(_)
                        | WitnessInput::ResultField { .. }
                        | WitnessInput::Memory { .. }
                )
        }) {
            return Err(LogicError::TypeMismatch);
        }
        self.validate_arguments(logic, budget)?;
        let mut seen = BTreeSet::new();
        for (binder, expression) in &self.values {
            let expected = logic
                .existentials
                .get(*binder as usize)
                .ok_or(LogicError::Unbound)?
                .ty;
            if !seen.insert(*binder) {
                return Err(LogicError::DuplicateName);
            }
            if expression.validate(&parameters, &[], observation, resource, budget)? != expected {
                return Err(LogicError::TypeMismatch);
            }
        }
        if logic
            .existentials
            .iter()
            .enumerate()
            .any(|(i, w)| w.default.is_none() && !seen.contains(&(i as u32)))
        {
            return Err(LogicError::MissingWitness);
        }
        Ok(())
    }
}

impl<T: Copy + Eq, V> WitnessArguments<T, V> {
    pub fn validate_arguments(
        &self,
        logic: &PredicateLogic<T>,
        budget: &mut LogicBudget,
    ) -> Result<(), LogicError> {
        if self.inputs.len() > MAX_LOGIC_PARAMETERS || self.arguments.len() > MAX_LOGIC_PARAMETERS {
            return Err(LogicError::Budget);
        }
        if self.arguments.len() != logic.parameters.len() {
            return Err(LogicError::Unbound);
        }
        let types = self.inputs.iter().map(|(t, _)| *t).collect::<Vec<_>>();
        for (expression, parameter) in self.arguments.iter().zip(&logic.parameters) {
            // Sealed representations cannot be read while naming an instance.
            if expression.validate(&types, &[], &|_, _, _, _| None, &|_, _| None, budget)?
                != parameter.ty
            {
                return Err(LogicError::TypeMismatch);
            }
        }
        Ok(())
    }
}

impl<T: Copy + Eq> PredicateLogic<T> {
    /// Instantiate one declaration. Actual parameters have already been
    /// captured by the caller; overrides use a separate call-site environment.
    /// The caller retains the same budget used while evaluating actuals.
    pub fn instantiate<A: Ord + Clone, R: Clone + Eq>(
        &self,
        parameters: &[TypedLogicValue<T, A, R>],
        inputs: &[TypedLogicValue<T, A, R>],
        explicit: &[(u32, LogicExpression<T>)],
        observe: &mut impl FnMut(
            u32,
            u64,
            T,
            ObservationTime,
        ) -> Result<TypedLogicValue<T, A, R>, LogicError>,
        resource: &mut impl FnMut(u32, &[u64]) -> Result<TypedLogicValue<T, A, R>, LogicError>,
        budget: &mut LogicBudget,
    ) -> Result<Vec<TypedLogicValue<T, A, R>>, LogicError> {
        let witnesses =
            self.instantiate_witnesses(parameters, inputs, explicit, observe, resource, budget)?;
        for constraint in &self.constraints {
            let value = constraint.evaluate(parameters, &witnesses, observe, resource, budget)?;
            if value.ty != LogicType::Bool || value.value != LogicValue::Bool(Some(true)) {
                return Err(LogicError::Unproved);
            }
        }
        Ok(witnesses)
    }

    /// Evaluate witness choices without discharging the body. The resource
    /// adapter checks every constraint against its instance-scoped facts.
    pub(crate) fn instantiate_witnesses<A: Ord + Clone, R: Clone + Eq>(
        &self,
        parameters: &[TypedLogicValue<T, A, R>],
        inputs: &[TypedLogicValue<T, A, R>],
        explicit: &[(u32, LogicExpression<T>)],
        observe: &mut impl FnMut(
            u32,
            u64,
            T,
            ObservationTime,
        ) -> Result<TypedLogicValue<T, A, R>, LogicError>,
        resource: &mut impl FnMut(u32, &[u64]) -> Result<TypedLogicValue<T, A, R>, LogicError>,
        budget: &mut LogicBudget,
    ) -> Result<Vec<TypedLogicValue<T, A, R>>, LogicError> {
        self.instantiate_witnesses_using(
            parameters,
            inputs,
            explicit,
            &mut |expression, parameters, witnesses, budget| {
                expression.evaluate(parameters, witnesses, observe, resource, budget)
            },
            budget,
        )
    }

    /// Keep declaration ordering, override environments and type checks in one
    /// place. The supplied evaluator may use already established premises; it
    /// receives no pending declaration constraint to assume for a new witness.
    pub(crate) fn instantiate_witnesses_using<
        A: Ord + Clone,
        R: Clone + Eq,
        E: From<LogicError>,
    >(
        &self,
        parameters: &[TypedLogicValue<T, A, R>],
        inputs: &[TypedLogicValue<T, A, R>],
        explicit: &[(u32, LogicExpression<T>)],
        evaluate: &mut impl FnMut(
            &LogicExpression<T>,
            &[TypedLogicValue<T, A, R>],
            &[TypedLogicValue<T, A, R>],
            &mut LogicBudget,
        ) -> Result<TypedLogicValue<T, A, R>, E>,
        budget: &mut LogicBudget,
    ) -> Result<Vec<TypedLogicValue<T, A, R>>, E> {
        if self.parameters.len() > MAX_LOGIC_PARAMETERS
            || inputs.len() > MAX_LOGIC_PARAMETERS
            || self.existentials.len() > MAX_EXISTENTIALS
            || explicit.len() > MAX_EXISTENTIALS
            || self.constraints.len() > MAX_CONSTRAINTS
        {
            return Err(LogicError::Budget.into());
        }
        if parameters.len() != self.parameters.len()
            || self
                .parameters
                .iter()
                .zip(parameters)
                .any(|(p, a)| p.ty != a.ty || matches!(p.ty, LogicType::Resource(_)))
        {
            return Err(LogicError::TypeMismatch.into());
        }
        if parameters.iter().chain(inputs).any(|value| {
            !matches!(
                (&value.ty, &value.value),
                (LogicType::U64 | LogicType::Usize, LogicValue::Word(_))
                    | (
                        LogicType::Bool,
                        LogicValue::Bool(_)
                            | LogicValue::BoolAtom { .. }
                            | LogicValue::BoolComparison { .. }
                            | LogicValue::BoolBinary { .. }
                    )
                    | (
                        LogicType::Resource(_),
                        LogicValue::Resource(_) | LogicValue::ResourceAtom { .. }
                    )
            )
        }) {
            return Err(LogicError::TypeMismatch.into());
        }
        let mut overrides = BTreeMap::new();
        for (binder, expression) in explicit {
            if *binder as usize >= self.existentials.len() {
                return Err(LogicError::Unbound.into());
            }
            if overrides.insert(*binder, expression).is_some() {
                return Err(LogicError::DuplicateName.into());
            }
        }
        let mut witnesses = Vec::new();
        for (index, binder) in self.existentials.iter().enumerate() {
            let value = if let Some(expression) = overrides.get(&(index as u32)) {
                evaluate(expression, inputs, &[], budget)?
            } else {
                let expression = binder.default.as_ref().ok_or(LogicError::MissingWitness)?;
                evaluate(expression, parameters, &witnesses, budget)?
            };
            if value.ty != binder.ty {
                return Err(LogicError::TypeMismatch.into());
            }
            witnesses.push(value);
        }
        Ok(witnesses)
    }
}

#[cfg(test)]
mod tests;
