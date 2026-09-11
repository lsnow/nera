//! Finite simultaneous-induction domain. Candidates are hypotheses, not seals.
//! Scalar widening is explicit; unsupported resource changes widen to failure,
//! never to an invented permission or a no-return interface.
use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SccLimits {
    pub max_functions: usize,
    pub max_iterations: u32,
    /// Additional trial/final analyses; the ordinary baseline pass is mandatory.
    pub max_body_analyses: usize,
    pub max_worlds: usize,
    pub max_candidate_bytes: usize,
}
impl Default for SccLimits {
    fn default() -> Self {
        Self {
            max_functions: 64,
            max_iterations: 8,
            max_body_analyses: 1024,
            max_worlds: 32,
            max_candidate_bytes: 1_048_576,
        }
    }
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SccOutcome {
    Closed,
    FunctionBudget,
    AnalysisBudget,
    IterationBudget,
    StateBudget,
    Unsupported,
    NotCovered,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SccCandidate {
    pub function: VirFunctionId,
    /// Final induction interface; ordinals refer to this candidate namespace,
    /// not to the reprojected body's CFG returns.
    pub normal_returns: Knowledge<Vec<ReturnAlternative>>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SccAnalysis {
    pub final_candidates: Arc<[SccCandidate]>,
    pub baseline_block_visits: u64,
    /// Work in completed extra trial/final body analyses (baseline excluded).
    pub body_block_visits: u64,
    pub body_queries: usize,
    pub body_call_evidence: usize,
    pub members: Vec<VirFunctionId>,
    pub iterations: u32,
    pub body_analyses: usize,
    pub peak_worlds: usize,
    pub peak_candidate_bytes: usize,
    pub widenings: usize,
    pub final_recheck: bool,
    pub outcome: SccOutcome,
}
pub(crate) fn record(summary: &mut FunctionSummary, analysis: &SccAnalysis) {
    summary.recursion = Some(analysis.clone());
    summary.recursion_shape = summary.recursion.clone();
}

fn worlds(summary: &FunctionSummary) -> Option<impl Iterator<Item = &ReturnWorld>> {
    let Knowledge::Known(alternatives) = &summary.normal_returns else {
        return None;
    };
    Some(alternatives.iter().flat_map(|a| &a.worlds))
}
pub(crate) fn world_count(summary: &FunctionSummary) -> usize {
    worlds(summary).map_or(0, Iterator::count)
}
pub(crate) fn fits(summary: &FunctionSummary, limits: SccLimits) -> bool {
    let count = world_count(summary);
    count > 0
        && count <= limits.max_worlds
        && candidate_bytes(summary) <= limits.max_candidate_bytes
}
pub(crate) fn candidate_bytes(summary: &FunctionSummary) -> usize {
    format!("{:?}", summary.normal_returns).len()
}

pub(crate) fn seed(summary: &FunctionSummary) -> Option<FunctionSummary> {
    let mut retained = Vec::new();
    for original in worlds(summary)? {
        // Baseline skeleton failures may leave unknown owner results. Do not
        // turn those into an existential, or treat their absence as no-return.
        if original.values.iter().any(|v| match &v.value {
            SummaryValue::Pointer(p) => {
                p.resource == Knowledge::Unknown || p.domain == SummaryDomain::Unknown
            }
            SummaryValue::Permission(p) => {
                p.resource == Knowledge::Unknown
                    || p.range == SummaryRange::Unknown
                    || p.authority == SummaryAuthority::Unknown
                    || p.availability != PermissionAvailability::Available
            }
            _ => false,
        }) || original
            .resources
            .iter()
            .any(|r| !matches!(r.storage, ResourceStorage::Input | ResourceStorage::Heap))
        {
            continue;
        }
        let mut world = original.clone();
        // Initial effects cover all visible resources, including every writable
        // input and escaping fresh resource. Never start at empty/pure effects
        // merely because a recursive call has not been analyzed yet.
        let all = world
            .resources
            .iter()
            .map(|r| {
                Some(SummaryFootprint {
                    resource: r.name.clone(),
                    range: SummaryRange::Exact(ByteRange::new(0, r.size).ok()?),
                })
            })
            .collect::<Option<Vec<_>>>()?;
        world.effects = SummaryEffects {
            may_read: Knowledge::Known(all.clone()),
            may_write: Knowledge::Known(all),
            may_free: Knowledge::Known(
                world
                    .resources
                    .iter()
                    .filter(|r| r.ownership == OwnershipState::Owned)
                    .map(|r| r.name.clone())
                    .collect(),
            ),
        };
        world.return_evidence = retained.len();
        retained.push(world);
    }
    if retained.is_empty() {
        return None;
    }
    // Prefer informative observed exits when proposing an induction invariant.
    // This is NOT coverage: every exit (including omitted unknown results) is
    // checked again under the hypothesis and must be included before publishing.
    let informative = |w: &ReturnWorld| {
        !w.values.iter().any(|v| {
            matches!(&v.value,
        SummaryValue::Word { interval, expression: None } if *interval == U64Interval::unknown())
                || matches!(v.value, SummaryValue::Bool(AbstractBool::Unknown))
        })
    };
    if retained.iter().any(informative) {
        retained.retain(informative);
    }
    for (index, world) in retained.iter_mut().enumerate() {
        world.return_evidence = index;
    }
    let mut candidate = summary.clone();
    candidate.closed = false;
    candidate.state = SummaryState::Hypothesis;
    candidate.normal_returns = Knowledge::Known(vec![ReturnAlternative {
        guard: Vec::new(),
        worlds: retained,
    }]);
    Some(candidate)
}

fn range_covers(outer: &SummaryRange, inner: &SummaryRange) -> bool {
    if outer == inner {
        return true;
    }
    match (outer, inner) {
        (SummaryRange::Exact(a), SummaryRange::Exact(b)) => a.contains(*b),
        (SummaryRange::Exact(a), SummaryRange::Symbolic { start, end }) => {
            a.start() <= start.interval.lower() && end.interval.upper() <= a.end()
        }
        _ => false,
    }
}
fn footprints_cover(
    a: &Knowledge<Vec<SummaryFootprint>>,
    b: &Knowledge<Vec<SummaryFootprint>>,
) -> bool {
    let (Knowledge::Known(a), Knowledge::Known(b)) = (a, b) else {
        return false;
    };
    b.iter().all(|b| {
        a.iter()
            .any(|a| a.resource == b.resource && range_covers(&a.range, &b.range))
    })
}
fn effects_cover(a: &SummaryEffects, b: &SummaryEffects) -> bool {
    let (Knowledge::Known(a_free), Knowledge::Known(b_free)) = (&a.may_free, &b.may_free) else {
        return false;
    };
    footprints_cover(&a.may_read, &b.may_read)
        && footprints_cover(&a.may_write, &b.may_write)
        && b_free.iter().all(|b| a_free.contains(b))
}
fn value_covers(a: &SummaryValue, b: &SummaryValue) -> bool {
    match (a, b) {
        (
            SummaryValue::Word {
                interval: a,
                expression: ae,
            },
            SummaryValue::Word {
                interval: b,
                expression: be,
            },
        ) => a.contains(b.lower()) && a.contains(b.upper()) && (ae.is_none() || ae == be),
        (SummaryValue::Bool(AbstractBool::Unknown), SummaryValue::Bool(_)) => true,
        _ => a == b,
    }
}
fn same_resources(a: &ReturnWorld, b: &ReturnWorld) -> bool {
    // Exact resource/loan must-fact equality is a conservative subdomain.
    // No fieldwise permission join can mix two incompatible resource worlds.
    a.resources == b.resources
        && a.borrow_restoration == b.borrow_restoration
        && a.values.len() == b.values.len()
}
fn world_covers(a: &ReturnWorld, b: &ReturnWorld) -> bool {
    same_resources(a, b)
        && effects_cover(&a.effects, &b.effects)
        && a.values
            .iter()
            .zip(&b.values)
            .all(|(a, b)| a.coordinate == b.coordinate && value_covers(&a.value, &b.value))
}
pub(crate) fn covers(candidate: &FunctionSummary, observed: &FunctionSummary) -> bool {
    if candidate.binding != observed.binding
        || candidate.parameters != observed.parameters
        || candidate.results != observed.results
        || candidate.inputs != observed.inputs
        || candidate.input_resources != observed.input_resources
    {
        return false;
    }
    if !matches!(&candidate.normal_returns, Knowledge::Known(alternatives) if alternatives.iter().all(|a| a.guard.is_empty()))
    {
        return false;
    }
    let (Some(a), Some(b)) = (worlds(candidate), worlds(observed)) else {
        return false;
    };
    let a = a.collect::<Vec<_>>();
    let b = b.collect::<Vec<_>>();
    // Empty observations never certify non-return or discharge missing coverage.
    !a.is_empty() && !b.is_empty() && b.iter().all(|b| a.iter().any(|a| world_covers(a, b)))
}

pub(crate) fn join(
    candidate: &mut FunctionSummary,
    observed: &FunctionSummary,
    widen: bool,
) -> usize {
    let Some(observed) = worlds(observed) else {
        return 0;
    };
    let Knowledge::Known(alternatives) = &mut candidate.normal_returns else {
        return 0;
    };
    let worlds = &mut alternatives[0].worlds;
    let mut widened = 0;
    for b in observed {
        if worlds.iter().any(|a| world_covers(a, b)) {
            continue;
        }
        if let Some(a) = worlds.iter_mut().find(|a| {
            same_resources(a, b)
                && a.values.iter().zip(&b.values).all(|(a, b)| {
                    matches!(
                        (&a.value, &b.value),
                        (SummaryValue::Word { .. }, SummaryValue::Word { .. })
                            | (SummaryValue::Bool(_), SummaryValue::Bool(_))
                    ) || a.value == b.value
                })
        }) {
            for (a, b) in a.values.iter_mut().zip(&b.values) {
                match (&mut a.value, &b.value) {
                    (
                        SummaryValue::Word {
                            interval,
                            expression,
                        },
                        SummaryValue::Word {
                            interval: bi,
                            expression: be,
                        },
                    ) => {
                        if !interval.contains(bi.lower()) || !interval.contains(bi.upper()) {
                            *interval = if widen {
                                widened += 1;
                                U64Interval::unknown()
                            } else {
                                U64Interval::new(
                                    interval.lower().min(bi.lower()),
                                    interval.upper().max(bi.upper()),
                                )
                                .unwrap()
                            };
                        }
                        if expression != be {
                            *expression = None;
                        }
                    }
                    (SummaryValue::Bool(value), SummaryValue::Bool(b)) if value != b => {
                        *value = AbstractBool::Unknown
                    }
                    _ => {}
                }
            }
            union_effects(&mut a.effects, &b.effects);
        } else {
            let mut b = b.clone();
            b.return_evidence = worlds.len();
            worlds.push(b);
        }
    }
    widened
}
fn union_effects(a: &mut SummaryEffects, b: &SummaryEffects) {
    fn union<T: Clone + PartialEq>(a: &mut Knowledge<Vec<T>>, b: &Knowledge<Vec<T>>) {
        match (&mut *a, b) {
            (Knowledge::Known(a), Knowledge::Known(b)) => {
                for item in b {
                    if !a.contains(item) {
                        a.push(item.clone());
                    }
                }
            }
            _ => *a = Knowledge::Unknown,
        }
    }
    union(&mut a.may_read, &b.may_read);
    union(&mut a.may_write, &b.may_write);
    union(&mut a.may_free, &b.may_free);
}

#[cfg(test)]
mod tests {
    use super::*;
    fn projected(source: &str, name: &str) -> FunctionSummary {
        let output = crate::analyze(&crate::SourceFile::from_text("scc-domain.nera", source));
        let unit = output.vir().unwrap().resolve().unwrap();
        let report = crate::verify_program(&unit, Default::default()).unwrap();
        assert!(report.is_memory_checked_core0());
        let id = unit
            .runtime()
            .functions
            .iter()
            .find(|f| f.name == name)
            .unwrap()
            .id;
        report.functions()[&id].summary().clone()
    }
    fn first(summary: &mut FunctionSummary) -> &mut ReturnWorld {
        let Knowledge::Known(a) = &mut summary.normal_returns else {
            panic!();
        };
        &mut a[0].worlds[0]
    }
    #[test]
    fn finite_scalar_join_and_widen_cover_both_operands() {
        let original = projected(
            "fn main()->u64 { return f(true); } fn f(flag:bool)->u64 { if flag { return 0; } return 2; }",
            "f",
        );
        let mut candidate = seed(&original).unwrap();
        for value in 0..16 {
            let previous = candidate.clone();
            let mut observed = original.clone();
            first(&mut observed).values[0].value = SummaryValue::Word {
                interval: U64Interval::exact(value),
                expression: None,
            };
            join(&mut candidate, &observed, value > 3);
            assert!(covers(&candidate, &previous));
            assert!(covers(&candidate, &observed));
        }
        let mut empty = original.clone();
        empty.normal_returns = Knowledge::Known(Vec::new());
        assert!(!covers(&candidate, &empty));
        let mut guarded = candidate.clone();
        let Knowledge::Known(alternatives) = &mut guarded.normal_returns else {
            panic!();
        };
        alternatives[0].guard.push(SummaryGuard::Boolean {
            parameter: 0,
            expected: false,
        });
        assert!(
            !covers(&guarded, &original),
            "unconditional domain cannot silently ignore candidate guards"
        );
    }
    #[test]
    fn coverage_checks_resource_worlds_and_all_may_effects() {
        let original = projected(
            "fn main()->u64 { let p=alloc<u64>(1); *p=42; let q=id(p); return *q; } fn id(p:Own<u64>)->Own<u64> { return p; }",
            "id",
        );
        let candidate = seed(&original).unwrap();
        assert!(covers(&candidate, &original));
        for mutation in 0..4 {
            let mut observed = original.clone();
            let world = first(&mut observed);
            match mutation {
                0 => world.resources[0].liveness = crate::LivenessState::Dead,
                1 => world.effects.may_write = Knowledge::Unknown,
                2 => {
                    world.effects.may_write = Knowledge::Known(vec![SummaryFootprint {
                        resource: world.resources[0].name.clone(),
                        range: SummaryRange::Exact(ByteRange::new(0, 16).unwrap()),
                    }])
                }
                _ => {
                    let SummaryValue::Permission(p) = &mut world.values[1].value else {
                        panic!();
                    };
                    p.free = FreeCapability::No;
                }
            }
            assert!(!covers(&candidate, &observed), "mutation {mutation}");
        }
    }
}
