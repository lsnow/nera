//! Elaborate a bounded scalar query independently of runtime sources. Word
//! literals and erased scalar slots are polymorphic between u64 and usize;
//! opened values supply nominal types. Shared syntax never merges those types.
use super::*;

#[derive(Clone, Copy)]
pub(crate) enum Term<O> {
    Operand(O),
    Add(u32, u32),
    Sub(u32, u32),
    Scale(u32, u64),
    Equal(u32, u32),
    Less(u32, u32),
    LessEqual(u32, u32),
    Not(u32),
    And(u32, u32),
    Or(u32, u32),
}

#[derive(Clone, Copy)]
pub(crate) enum InputType {
    Word,
    U64,
    Usize,
    Bool,
}

const U64: u8 = 1;
const USIZE: u8 = 2;
const BOOL: u8 = 4;
const WORD: u8 = U64 | USIZE;

pub(crate) struct Query<T> {
    pub expression: LogicExpression<T>,
    /// Elaborated leaf -> original operand node, including typed copies.
    pub operands: Vec<(u32, u32)>,
}

/// All nodes are checked, including unreachable syntax. The adapter must
/// separately qualify all operand identities before supplying their types.
pub(crate) fn elaborate<T: Copy + Eq, O: Copy>(
    terms: &[Term<O>],
    root: u32,
    inputs: &BTreeMap<u32, InputType>,
    budget: &mut LogicBudget,
) -> Result<Query<T>, LogicError> {
    if terms.len() > MAX_EXPRESSION_NODES {
        return Err(LogicError::Budget);
    }
    if root as usize >= terms.len() {
        return Err(LogicError::InvalidNode);
    }
    let mut masks = Vec::<u8>::new();
    let mut depths = Vec::<usize>::new();
    for (index, term) in terms.iter().enumerate() {
        budget.charge(1)?;
        let mut depth = 1;
        let mut child = |id: u32| -> Result<u8, LogicError> {
            if id as usize >= index {
                return Err(LogicError::InvalidNode);
            }
            depth = depth.max(1 + depths[id as usize]);
            Ok(masks[id as usize])
        };
        let mask = match *term {
            Term::Operand(_) => match inputs.get(&(index as u32)).ok_or(LogicError::Unbound)? {
                InputType::Word => WORD,
                InputType::U64 => U64,
                InputType::Usize => USIZE,
                InputType::Bool => BOOL,
            },
            Term::Add(a, b) | Term::Sub(a, b) => child(a)? & child(b)? & WORD,
            Term::Scale(a, _) => child(a)? & WORD,
            Term::Equal(a, b) | Term::Less(a, b) | Term::LessEqual(a, b) => {
                let allowed = if matches!(term, Term::Equal(..)) {
                    WORD | BOOL
                } else {
                    WORD
                };
                if child(a)? & child(b)? & allowed == 0 {
                    return Err(LogicError::TypeMismatch);
                }
                BOOL
            }
            Term::Not(a) => child(a)? & BOOL,
            Term::And(a, b) | Term::Or(a, b) => child(a)? & child(b)? & BOOL,
        };
        if mask == 0 {
            return Err(LogicError::TypeMismatch);
        }
        if depth > MAX_EXPRESSION_DEPTH {
            return Err(LogicError::Budget);
        }
        masks.push(mask);
        depths.push(depth);
    }
    if masks[root as usize] != BOOL {
        return Err(LogicError::TypeMismatch);
    }
    let mut builder = Builder {
        terms,
        masks: &masks,
        nodes: vec![],
        operands: vec![],
        mapped: BTreeMap::new(),
        covered: BTreeSet::new(),
    };
    let mut root = builder.emit(root, BOOL, budget)?;
    for (id, mask) in masks.iter().enumerate() {
        budget.charge(1)?;
        if !builder.covered.contains(&(id as u32)) {
            let node = builder.emit(id as u32, select(*mask), budget)?;
            budget.charge(2)?;
            if builder.nodes.len() + 2 > MAX_EXPRESSION_NODES {
                return Err(LogicError::Budget);
            }
            // LogicExpression forbids dead terms. A reflexive check connects
            // unused syntax without assuming its value: facts.proves checks
            // every arithmetic intermediate before evaluating the equality.
            let check = builder.nodes.len() as u32;
            builder.nodes.push(LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::Equal(node, node),
            });
            builder.nodes.push(LogicNode {
                ty: LogicType::Bool,
                kind: LogicNodeKind::And(root, check),
            });
            root = builder.nodes.len() as u32 - 1;
        }
    }
    let types = builder
        .operands
        .iter()
        .map(|(id, _)| builder.nodes[*id as usize].ty)
        .collect::<Vec<_>>();
    let expression = LogicExpression {
        nodes: builder.nodes,
        root,
    };
    expression.validate(&types, &[], &|_, _, _, _| None, &|_, _| None, budget)?;
    Ok(Query {
        expression,
        operands: builder.operands,
    })
}

fn select(mask: u8) -> u8 {
    if mask & U64 != 0 {
        U64
    } else if mask & USIZE != 0 {
        USIZE
    } else {
        BOOL
    }
}

struct Builder<'a, T, O> {
    terms: &'a [Term<O>],
    masks: &'a [u8],
    nodes: Vec<LogicNode<T>>,
    operands: Vec<(u32, u32)>,
    mapped: BTreeMap<(u32, u8), u32>,
    covered: BTreeSet<u32>,
}

impl<T: Copy, O: Copy> Builder<'_, T, O> {
    fn emit(&mut self, id: u32, mask: u8, budget: &mut LogicBudget) -> Result<u32, LogicError> {
        budget.charge(1)?;
        if let Some(node) = self.mapped.get(&(id, mask)) {
            return Ok(*node);
        }
        let kind = match self.terms[id as usize] {
            Term::Operand(_) => {
                LogicNodeKind::Binder(LogicBinder::Parameter(self.operands.len() as u32))
            }
            Term::Scale(a, factor) => LogicNodeKind::Scale {
                operand: self.emit(a, mask, budget)?,
                factor,
            },
            Term::Not(a) => LogicNodeKind::Not(self.emit(a, BOOL, budget)?),
            term => {
                let (a, b, operands) = match term {
                    Term::Add(a, b) | Term::Sub(a, b) => (a, b, mask),
                    Term::Equal(a, b) | Term::Less(a, b) | Term::LessEqual(a, b) => (
                        a,
                        b,
                        select(self.masks[a as usize] & self.masks[b as usize]),
                    ),
                    Term::And(a, b) | Term::Or(a, b) => (a, b, BOOL),
                    _ => unreachable!(),
                };
                let a = self.emit(a, operands, budget)?;
                let b = self.emit(b, operands, budget)?;
                match term {
                    Term::Add(..) => LogicNodeKind::Add(a, b),
                    Term::Sub(..) => LogicNodeKind::Sub(a, b),
                    Term::Equal(..) => LogicNodeKind::Equal(a, b),
                    Term::Less(..) => LogicNodeKind::Less(a, b),
                    Term::LessEqual(..) => LogicNodeKind::LessEqual(a, b),
                    Term::And(..) => LogicNodeKind::And(a, b),
                    Term::Or(..) => LogicNodeKind::Or(a, b),
                    _ => unreachable!(),
                }
            }
        };
        if self.nodes.len() >= MAX_EXPRESSION_NODES {
            return Err(LogicError::Budget);
        }
        let node = self.nodes.len() as u32;
        if matches!(self.terms[id as usize], Term::Operand(_)) {
            self.operands.push((node, id));
        }
        self.nodes.push(LogicNode {
            ty: match mask {
                U64 => LogicType::U64,
                USIZE => LogicType::Usize,
                _ => LogicType::Bool,
            },
            kind,
        });
        self.mapped.insert((id, mask), node);
        self.covered.insert(id);
        Ok(node)
    }
}

#[cfg(test)]
mod tests;
