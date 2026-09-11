use nera::{ValidatedVirUnit, VirUnit};

pub(crate) fn check_spec_mutation(program: &ValidatedVirUnit, selector: u64) {
    let first = malformed_spec_unit(program, selector).into_validated();
    let second = malformed_spec_unit(program, selector).into_validated();
    assert_eq!(
        first, second,
        "spec mutation rejection must be deterministic"
    );
    assert!(first.is_err(), "malformed spec mutation must fail closed");
}

pub(crate) fn malformed_spec_unit(program: &ValidatedVirUnit, selector: u64) -> VirUnit {
    let mut unit = program.as_unit().clone();
    let function = unit.runtime.entry;
    let origin = unit
        .source_map
        .origin_at(nera::VirLocation::FunctionEntry { function })
        .expect("validated entry has an origin")
        .id;
    let term = nera::VirSpecTermId::new(unit.specs.terms().len() as u32);
    let clause = nera::VirSpecClauseId::new(unit.specs.clauses().len() as u32);
    let prove = nera::VirSpecProveId::new(unit.specs.proves().len() as u32);
    let location = nera::VirSpecLocation::FunctionEntry { function };
    unit.specs.terms_mut().push(nera::VirSpecTerm {
        id: term,
        clause,
        ty: nera::VirSpecType::Bool,
        kind: nera::VirSpecTermKind::Bool(true),
        origin,
    });
    unit.specs.clauses_mut().push(nera::VirSpecClause {
        id: clause,
        owner: nera::VirSpecClauseOwner::Prove(prove),
        location,
        origin: nera::VirSpecClauseOrigin::Explicit { origin },
        kind: nera::VirSpecClauseKind::Logic { root: term },
    });
    unit.specs.proves_mut().push(nera::VirSpecProve {
        id: prove,
        function,
        location,
        clause,
        origin,
    });

    match selector % 5 {
        0 => {
            unit.specs.proves_mut()[prove.get() as usize].clause =
                nera::VirSpecClauseId::new(u32::MAX)
        }
        1 => {
            unit.specs.proves_mut()[prove.get() as usize].location =
                nera::VirSpecLocation::FunctionResult { function };
        }
        2 => {
            unit.specs.proves_mut()[prove.get() as usize].origin = nera::VirOriginId::new(u32::MAX)
        }
        3 => {
            unit.specs.clauses_mut()[clause.get() as usize].location =
                nera::VirSpecLocation::Runtime(nera::VirLocation::Instruction {
                    function,
                    block: nera::VirBlockId::new(0),
                    ordinal: u64::MAX,
                });
        }
        _ => {
            let trust = nera::VirTrustEntryId::new(unit.specs.trust_entries().len() as u32);
            unit.specs.clauses_mut()[clause.get() as usize].owner =
                nera::VirSpecClauseOwner::TrustEntry(trust);
            unit.specs.proves_mut().pop();
            unit.specs.trust_entries_mut().push(nera::VirTrustEntry {
                id: trust,
                scope: nera::VirTrustScope::FunctionEntry { function },
                policy: nera::VirTrustPolicyKind::ForeignContract,
                clause,
                origin,
            });
        }
    }
    unit
}
