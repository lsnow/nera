//! Simultaneous, whole-case projection at a CFG boundary. All operands are read
//! from the old state, including swaps and repeated scalar arguments. This does
//! not perform a join or change the availability of a linear permission.
use super::*;

impl ResourceState {
    /// Count-independent loss detection: newly materialized drop-flag facts
    /// must not conceal a comparison whose operands were not carried.
    pub(in crate::verifier) fn loses_cfg_guards(
        &self,
        renames: &[(VirValueId, VirValueId)],
    ) -> bool {
        let carried: BTreeSet<_> = renames.iter().map(|&(source, _)| source).collect();
        self.path_condition()
            .facts()
            .into_iter()
            .flatten()
            .any(|fact| match fact {
                PathFact::Boolean { value, .. } => !carried.contains(value),
                PathFact::Comparison { left, right, .. } => {
                    !carried.contains(left) || !carried.contains(right)
                }
            })
    }

    pub(in crate::verifier) fn project_cfg_case(
        &self,
        renames: &[(VirValueId, VirValueId)],
    ) -> Result<Self, ResourceStateDefinitionError> {
        if !self.path_condition().is_reachable() {
            return Ok(Self::unreachable());
        }
        let mut targets = BTreeSet::new();
        for &(_, target) in renames {
            if !targets.insert(target) {
                return Err(ResourceStateDefinitionError::DuplicateValue(target));
            }
        }
        let mut projected = self.project_cfg_edge(renames);
        let remapper = ExpressionRemapper::new(self, renames);
        for &(source, target) in renames {
            let Some(value) = self.value(source).copied() else {
                // The boundary's typed consumer supplies its existing unknown
                // fallback; absence must never manufacture an available token.
                continue;
            };
            projected.define_value(target, remapper.value(value))?;
            // A carried bool is its OLD SSA value, not a re-evaluation of the
            // expression that created it. This also preserves duplicated drop
            // flags even when the original comparison operands disappear.
            let truth = match value {
                AbstractValue::Bool(AbstractBool::True) => Some(true),
                AbstractValue::Bool(AbstractBool::False) => Some(false),
                AbstractValue::Bool(AbstractBool::Unknown) => {
                    if self
                        .path_condition()
                        .implies(PathFact::boolean(source, true))
                    {
                        Some(true)
                    } else if self
                        .path_condition()
                        .implies(PathFact::boolean(source, false))
                    {
                        Some(false)
                    } else {
                        None
                    }
                }
                _ => None,
            };
            if let Some(expected) = truth {
                projected.conjoin_path_fact(PathFact::boolean(target, expected));
            }
        }
        Ok(projected)
    }
}

#[cfg(test)]
mod tests;
