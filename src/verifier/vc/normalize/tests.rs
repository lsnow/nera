use super::*;
use crate::verifier::{
    resource::AbstractBool,
    vc::{SnapshotValues, VcQueryBudget, evaluate_bool},
};
use crate::*;

fn unit() -> ValidatedVirUnit {
    let output = analyze(&SourceFile::from_text(
        "instantiate.nera",
        "fn main() -> u64 { return 7; }",
    ));
    let mut unit = output.vir().unwrap().as_unit().clone();
    let function = VirFunctionId::new(0);
    let origin = unit
        .source_map
        .origin_at(VirLocation::FunctionEntry { function })
        .unwrap()
        .id;
    let clause = VirSpecClauseId::new(unit.specs.clauses().len() as u32);
    let binder = VirSpecBinderId::new(unit.specs.binders().len() as u32);
    let prove = VirSpecProveId::new(unit.specs.proves().len() as u32);
    let first = unit.specs.terms().len() as u32;
    unit.specs.binders_mut().push(VirSpecBinder {
        id: binder,
        owner: VirSpecBinderOwner::Clause(clause),
        name: "value".into(),
        ty: VirSpecType::U64,
        origin,
    });
    for (offset, kind) in [
        VirSpecTermKind::U64(2),
        VirSpecTermKind::U64(3),
        VirSpecTermKind::Binder(binder),
        VirSpecTermKind::Equal {
            left: VirSpecTermId::new(first + 2),
            right: VirSpecTermId::new(first),
        },
    ]
    .into_iter()
    .enumerate()
    {
        unit.specs.terms_mut().push(VirSpecTerm {
            id: VirSpecTermId::new(first + offset as u32),
            clause,
            ty: if offset == 3 {
                VirSpecType::Bool
            } else {
                VirSpecType::U64
            },
            kind,
            origin,
        });
    }
    let location = VirSpecLocation::FunctionEntry { function };
    unit.specs.clauses_mut().push(VirSpecClause {
        id: clause,
        owner: VirSpecClauseOwner::Prove(prove),
        location,
        origin: VirSpecClauseOrigin::Explicit { origin },
        kind: VirSpecClauseKind::Logic {
            root: VirSpecTermId::new(first + 3),
        },
    });
    unit.specs.proves_mut().push(VirSpecProve {
        id: prove,
        function,
        location,
        clause,
        origin,
    });
    unit.into_validated().unwrap()
}

#[test]
fn local_instantiations_do_not_share_source_id_cache_or_leak_substitutions() {
    let unit = unit();
    let resolved = unit.resolve().unwrap();
    let terms = unit.as_unit().specs.terms();
    let first = terms.len() - 4;
    let root = terms[first + 3].id;
    let binder = unit.as_unit().specs.binders().last().unwrap().id.get();
    let mut normalizer = VcNormalizer::new(VcLimits::default());
    let unbound = normalizer.normalize(&resolved, root).unwrap();
    let two = normalizer.normalize(&resolved, terms[first].id).unwrap();
    let three = normalizer
        .normalize(&resolved, terms[first + 1].id)
        .unwrap();
    let mut instances = Vec::new();
    for value in [two, three, two] {
        let term = normalizer
            .normalize_bound(&resolved, root, &BTreeMap::from([(binder, value)]))
            .unwrap();
        assert_ne!(term, unbound);
        let actual = evaluate_bool(
            normalizer.arena(),
            term,
            &Default::default(),
            SnapshotValues::Results(&[]),
            &unit.as_unit().runtime.functions[0],
            &mut VcQueryBudget::new(VcLimits::default()),
        );
        assert_eq!(
            actual,
            Some(if value == two {
                AbstractBool::True
            } else {
                AbstractBool::False
            })
        );
        instances.push(term);
    }
    assert_eq!(instances[0], instances[2]);
    assert_ne!(instances[0], instances[1]);
    assert_eq!(normalizer.normalize(&resolved, root).unwrap(), unbound);
}

#[test]
fn instantiation_node_and_work_budgets_are_not_reset_with_scopes() {
    let unit = unit();
    let resolved = unit.resolve().unwrap();
    let terms = unit.as_unit().specs.terms();
    let first = terms.len() - 4;
    for limits in [
        VcLimits {
            max_nodes: 1,
            ..Default::default()
        },
        VcLimits {
            max_normalization_steps: 1,
            ..Default::default()
        },
    ] {
        let mut normalizer = VcNormalizer::new(limits);
        let witness = normalizer.normalize(&resolved, terms[first].id).unwrap();
        let bindings = BTreeMap::from([(
            unit.as_unit().specs.binders().last().unwrap().id.get(),
            witness,
        )]);
        for _ in 0..2 {
            assert!(
                normalizer
                    .normalize_bound(&resolved, terms[first + 3].id, &bindings)
                    .is_err()
            );
        }
    }
}
