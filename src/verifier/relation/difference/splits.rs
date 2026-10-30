//! Split logical disequalities, not repeated observations of the same one.
//! Only supplied mutual zero bounds identify vertices; equal intervals do not.
use super::*;

pub(super) enum Choice {
    Fixed(bool),
    Split { bit: usize, inverted: bool },
}

impl Choice {
    pub(super) fn in_branch(&self, branch: usize) -> bool {
        match *self {
            Self::Fixed(value) => value,
            Self::Split { bit, inverted } => (branch & (1 << bit) != 0) ^ inverted,
        }
    }
}

pub(super) fn plan(query: &mut Query) -> Result<(Vec<Choice>, usize), DifferenceStop> {
    if query.limits.max_branches == 0 {
        return Err(DifferenceStop::Budget);
    }
    if query.disequalities.is_empty() {
        return Ok((Vec::new(), 1));
    }
    let mut bounds = BTreeMap::<(usize, usize), i128>::new();
    for index in 0..query.edges.len() {
        query.tick()?;
        let (a, b, bound, _) = query.edges[index];
        bounds
            .entry((a, b))
            .and_modify(|old| *old = (*old).min(bound))
            .or_insert(bound);
    }
    let mut classes = (0..=query.variables.len()).collect::<Vec<_>>();
    for (&(a, b), &bound) in &bounds {
        query.tick()?;
        if bound <= 0 && bounds.get(&(b, a)).is_some_and(|reverse| *reverse <= 0) {
            let low = classes[a].min(classes[b]);
            let high = classes[a].max(classes[b]);
            for class in &mut classes {
                query.tick()?;
                if *class == high {
                    *class = low;
                }
            }
        }
    }
    let mut groups = BTreeMap::new();
    let mut choices = Vec::new();
    for index in 0..query.disequalities.len() {
        query.tick()?;
        let (left, right, origin) = query.disequalities[index];
        let lt = query.edge(left, right, -1, origin)?;
        let gt = query.edge(right, left, -1, origin)?;
        let fixed = if bounds.get(&(lt.0, lt.1)).is_some_and(|b| *b <= lt.2) {
            Some(true)
        } else if bounds.get(&(gt.0, gt.1)).is_some_and(|b| *b <= gt.2) {
            Some(false)
        } else {
            None
        };
        choices.push(if let Some(value) = fixed {
            Choice::Fixed(value)
        } else {
            let lt = (classes[lt.0], classes[lt.1], lt.2);
            let gt = (classes[gt.0], classes[gt.1], gt.2);
            let key = (lt.min(gt), lt.max(gt));
            let next = groups.len();
            let bit = *groups.entry(key).or_insert(next);
            Choice::Split {
                bit,
                inverted: lt > gt,
            }
        });
    }
    let count = 1usize
        .checked_shl(u32::try_from(groups.len()).map_err(|_| DifferenceStop::Budget)?)
        .filter(|count| *count <= query.limits.max_branches)
        .ok_or(DifferenceStop::Budget)?;
    Ok((choices, count))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn actual_equalities_share_splits_and_keep_every_original_choice_replayable() {
        let [a, b, c] = [0, 1, 2].map(|id| word(VirValueId::new(id)));
        let neq = |left, right| DifferencePremise::Compare {
            comparison: RelationComparison::NotEqual,
            left,
            right,
        };
        let goal = DifferenceGoal {
            comparison: RelationComparison::NotEqual,
            left: b,
            right: RelationTerm::Constant(2),
        };
        let mut premises = vec![
            DifferencePremise::EqualOffset {
                left: a,
                right: b,
                offset: 0,
            },
            neq(a, RelationTerm::Constant(2)),
            neq(RelationTerm::Constant(2), b),
            neq(c, RelationTerm::Constant(2)),
        ];
        let limits = DifferenceLimits::default();
        let evidence = solve_difference(&premises, goal, limits);
        assert_eq!(evidence.stop, DifferenceStop::Complete);
        assert_eq!(evidence.status, ObligationStatus::Proven);
        assert_eq!(evidence.branches.len(), 4);
        for branch in &evidence.branches {
            assert_eq!(branch.choices.len(), 3);
            assert_ne!(branch.choices[0], branch.choices[1]);
        }
        assert!(replay_difference(&premises, goal, limits, &evidence));
        // Compare against exhaustive splitting without the planner. Only
        // contradictory combinations may disappear; every feasible original
        // choice vector must remain in the optimized evidence.
        let mut exhaustive = Query {
            variables: BTreeMap::new(),
            edges: Vec::new(),
            disequalities: Vec::new(),
            limits,
            steps: 0,
            derivations: 0,
        };
        exhaustive.term(goal.left).unwrap();
        exhaustive.term(goal.right).unwrap();
        for (index, premise) in premises.iter().enumerate() {
            exhaustive.premise(premise, index).unwrap();
        }
        let viable = (0..8)
            .map(|branch| {
                exhaustive
                    .branch((0..3).map(|bit| branch & (1 << bit) != 0).collect(), goal)
                    .unwrap()
            })
            .filter(|branch| branch.contradiction.is_none())
            .map(|branch| branch.choices)
            .collect::<std::collections::BTreeSet<_>>();
        assert_eq!(
            viable,
            evidence
                .branches
                .iter()
                .filter(|branch| branch.contradiction.is_none())
                .map(|branch| branch.choices.clone())
                .collect()
        );
        let mut forged = evidence.clone();
        forged.branches[0].choices[1] ^= true;
        assert!(!replay_difference(&premises, goal, limits, &forged));
        premises.remove(0);
        assert_eq!(
            solve_difference(&premises, goal, limits).stop,
            DifferenceStop::Budget
        );
        // The same relation in one direction is not an equality certificate.
        premises.push(DifferencePremise::Bound {
            left: a,
            right: b,
            bound: 0,
        });
        assert_eq!(
            solve_difference(&premises, goal, limits).stop,
            DifferenceStop::Budget
        );
    }
}
