//! Occurrence-preserving Spec construction; no runtime permission effects.
use super::spec_memory;
use nera::*;

#[derive(Clone, Copy)]
pub struct Claim {
    pub pointer: u32,
    pub authority: u32,
    pub start: u64,
    pub end: u64,
    pub access: SpecAccess,
    pub points_to: bool,
}

impl Claim {
    pub fn write(start: u64, end: u64) -> Self {
        Self {
            pointer: 1,
            authority: 2,
            start,
            end,
            access: SpecAccess::Write,
            points_to: false,
        }
    }
}

pub fn add(unit: &mut VirUnit, location: VirLocation, claims: &[Claim]) -> VirSpecAssertionId {
    assert!(claims.len() >= 2);
    let function = location.function();
    let snapshot = |value| VirSpecSnapshot::Value {
        function,
        value: VirValueId::new(value),
    };
    let kind = |claim: Claim, start_bytes, end_bytes| {
        let memory = SpecMemoryClaim {
            pointer: snapshot(claim.pointer),
            authority: snapshot(claim.authority),
            start_bytes,
            end_bytes,
            layout: VirMemoryAccess::core_u64(),
            access: claim.access,
        };
        if claim.points_to {
            SpecAssertionKind::PointsTo {
                memory,
                value: None,
            }
        } else {
            SpecAssertionKind::Permission(memory)
        }
    };
    let first = unit.specs.assertions().len();
    let first_term = unit.specs.terms().len();
    spec_memory::add(unit, location, |t| kind(claims[0], t[0], t[1]));
    unit.specs.terms_mut()[first_term].kind = VirSpecTermKind::U64(claims[0].start);
    unit.specs.terms_mut()[first_term + 1].kind = VirSpecTermKind::U64(claims[0].end);
    let clause = unit.specs.assertions()[first].clause;
    let origin = unit.specs.assertions()[first].origin;
    for claim in &claims[1..] {
        let start = VirSpecTermId::new(unit.specs.terms().len() as u32);
        let end = VirSpecTermId::new(start.get() + 1);
        for (id, value) in [(start, claim.start), (end, claim.end)] {
            unit.specs.terms_mut().push(VirSpecTerm {
                id,
                clause,
                ty: VirSpecType::U64,
                kind: VirSpecTermKind::U64(value),
                origin,
            });
        }
        let id = VirSpecAssertionId::new(unit.specs.assertions().len() as u32);
        unit.specs.assertions_mut().push(VirSpecAssertion {
            id,
            clause,
            kind: kind(*claim, start, end),
            origin,
        });
    }
    let root = VirSpecAssertionId::new(unit.specs.assertions().len() as u32);
    unit.specs.assertions_mut().push(VirSpecAssertion {
        id: root,
        clause,
        origin,
        kind: SpecAssertionKind::Separation(
            (first..root.get() as usize)
                .map(|i| VirSpecAssertionId::new(i as u32))
                .collect(),
        ),
    });
    unit.specs.clauses_mut()[clause.get() as usize].kind = VirSpecClauseKind::Assertion { root };
    root
}

pub fn checked_unit() -> VirUnit {
    let mut unit = spec_memory::unit();
    add(
        &mut unit,
        spec_memory::location(2),
        &[Claim::write(0, 8), Claim::write(8, 16)],
    );
    unit
}
