//! Explicit scalar witnesses over the existing allocation/permission fixture.
use super::spec_memory;
use nera::*;

pub fn term(
    unit: &mut VirUnit,
    clause: VirSpecClauseId,
    ty: VirSpecType,
    kind: VirSpecTermKind,
) -> VirSpecTermId {
    let id = VirSpecTermId::new(unit.specs.terms().len() as u32);
    let origin = unit.specs.proves()[clause.get() as usize].origin;
    unit.specs.terms_mut().push(VirSpecTerm {
        id,
        clause,
        ty,
        kind,
        origin,
    });
    id
}

pub fn binder(unit: &mut VirUnit, clause: VirSpecClauseId, ty: VirSpecType) -> VirSpecBinderId {
    let id = VirSpecBinderId::new(unit.specs.binders().len() as u32);
    let origin = unit.specs.proves()[clause.get() as usize].origin;
    unit.specs.binders_mut().push(VirSpecBinder {
        id,
        owner: VirSpecBinderOwner::Clause(clause),
        name: format!("w{}", id.get()),
        ty,
        origin,
    });
    id
}

pub fn node(
    unit: &mut VirUnit,
    clause: VirSpecClauseId,
    kind: VirSpecAssertionKind,
) -> VirSpecAssertionId {
    let id = VirSpecAssertionId::new(unit.specs.assertions().len() as u32);
    let origin = unit.specs.proves()[clause.get() as usize].origin;
    unit.specs.assertions_mut().push(VirSpecAssertion {
        id,
        clause,
        kind,
        origin,
    });
    unit.specs.clauses_mut()[clause.get() as usize].kind =
        VirSpecClauseKind::Assertion { root: id };
    id
}

pub fn range(unit: &mut VirUnit, point: u32, end: u64) -> VirSpecClauseId {
    let clause = VirSpecClauseId::new(unit.specs.clauses().len() as u32);
    let leaf = VirSpecAssertionId::new(unit.specs.assertions().len() as u32);
    let witness = VirSpecTermId::new(unit.specs.terms().len() as u32 + 1);
    spec_memory::add(unit, spec_memory::location(point), |t| {
        SpecAssertionKind::Permission(spec_memory::claim(t))
    });
    unit.specs.terms_mut()[witness.get() as usize].kind = VirSpecTermKind::U64(end);
    let binder = binder(unit, clause, VirSpecType::U64);
    let value = term(
        unit,
        clause,
        VirSpecType::U64,
        VirSpecTermKind::Binder(binder),
    );
    let SpecAssertionKind::Permission(memory) =
        &mut unit.specs.assertions_mut()[leaf.get() as usize].kind
    else {
        unreachable!()
    };
    memory.end_bytes = value;
    node(
        unit,
        clause,
        SpecAssertionKind::Exists {
            binder,
            body: leaf,
            witness: Some(witness),
        },
    );
    clause
}

pub fn checked_unit() -> VirUnit {
    let mut unit = spec_memory::unit();
    range(&mut unit, 2, 8);
    unit
}
