//! Loan authority substitution is independent of pointer/address substitution.
//! A body world may export only the actual caller token admitted by the ABI;
//! it cannot activate a parent, introduce a callee-local loan, or mint an owner.
use super::*;
use crate::verifier::{AbstractValue, PermissionAuthority};

pub(super) fn validate_exports(
    world: &ReturnWorld,
    cx: &CallInstantiation<'_>,
    values: &[AbstractValue],
) -> bool {
    let Some(abi) = &cx.target.abi else {
        return world.borrow_restoration.is_empty()
            && !values.iter().any(|v| {
                matches!(v, AbstractValue::Permission(p)
                if matches!(p.authority(), PermissionAuthority::Loan(_)))
            });
    };
    let mut permissions = std::collections::BTreeSet::new();
    let mut export_slots = std::collections::BTreeSet::new();
    for (index, binding) in abi.parameters().iter().enumerate() {
        if !binding.interface().transfer.is_borrow() {
            continue;
        }
        let Some(&slot) = binding.parameter_slots().last() else {
            return false;
        };
        let slot = slot as usize;
        let Some(&argument) = cx.arguments.get(slot) else {
            return false;
        };
        let Some(AbstractValue::Permission(input)) = cx.before.value(argument) else {
            return false;
        };
        let PermissionAuthority::Loan(id) = input.authority() else {
            return false;
        };
        let Some(loan) = cx.before.loan(id) else {
            return false;
        };
        if loan.activity() != LoanActivity::Active
            || !loan.has_value_authority(argument)
            || input.availability() != PermissionAvailability::Available
            || input.free_capability() != FreeCapability::No
        {
            return false;
        }
        permissions.insert(slot);
        let Some(restoration) = world
            .borrow_restoration
            .iter()
            .find(|r| r.input_permission == slot)
        else {
            return false;
        };
        if !matches!(
            restoration.activity,
            LoanActivity::Active | LoanActivity::Suspended
        ) || restoration.permission.authority != SummaryAuthority::InputLoan(slot)
        {
            return false;
        }
        for output in binding.result_slots().iter().copied() {
            export_slots.insert(output as usize);
            let Some(AbstractValue::Permission(returned)) = values.get(output as usize) else {
                return false;
            };
            if returned.authority() != input.authority()
                || returned.provenance() != input.provenance()
                || returned.access() != input.access()
                || returned.free_capability() != FreeCapability::No
                || returned.availability() != PermissionAvailability::Available
                // The current ABI restores the complete imported endpoint.
                // Restricted pointer views do not authorize a larger loan.
                || !cx.queries.contained(cx.before, input.range(), returned.range(), cx.limits).is_proven()
                || !cx.queries.contained(cx.before, returned.range(), input.range(), cx.limits).is_proven()
            {
                return false;
            }
        }
        if abi.borrow_result_parameters().contains(&index) {
            let Some(output) = abi.results()[0].result_slots().last().copied() else {
                return false;
            };
            let Some(AbstractValue::Permission(returned)) = values.get(output as usize) else {
                return false;
            };
            if returned.authority() == input.authority() {
                let projected = abi
                    .borrow_result()
                    .filter(|relation| relation.parameter as usize == index)
                    .is_some_and(|relation| relation.projection != crate::BorrowProjection::Whole);
                export_slots.insert(output as usize);
                if returned.provenance() != input.provenance()
                    || returned.access() != input.access()
                    || returned.free_capability() != FreeCapability::No
                    || returned.availability() != PermissionAvailability::Available
                    || !cx
                        .queries
                        .contained(cx.before, input.range(), returned.range(), cx.limits)
                        .is_proven()
                    || (!projected
                        && !cx
                            .queries
                            .contained(cx.before, returned.range(), input.range(), cx.limits)
                            .is_proven())
                {
                    return false;
                }
            }
        }
    }
    world.borrow_restoration.len() == permissions.len()
        && world
            .borrow_restoration
            .iter()
            .all(|r| permissions.contains(&r.input_permission))
        && values.iter().enumerate().all(|(slot, value)| {
            !matches!(value,
            AbstractValue::Permission(p) if matches!(p.authority(), PermissionAuthority::Loan(_))
                && !export_slots.contains(&slot))
        })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verifier::relation::audit::QueryLog;
    use crate::{SourceFile, VirInstruction};

    #[test]
    fn equal_addresses_do_not_substitute_a_different_loan_or_wider_authority() {
        let source =
            "fn main()->u64 { let value=21; let a=&value; let b=&value; return pair(a,b); }
            fn pair(a:&u64,b:&u64)->u64 { return *a+*b; }";
        let output = crate::analyze(&SourceFile::from_text("borrow-substitution.nera", source));
        let unit = output.vir().unwrap().resolve().unwrap();
        let report = crate::verify_program(&unit, Default::default()).unwrap();
        assert!(report.is_memory_checked_core0());
        let caller = &unit.runtime().functions[0];
        let callee = &unit.runtime().functions[1];
        let summary = report.functions()[&callee.id].summary();
        let Knowledge::Known(alternatives) = &summary.normal_returns else {
            panic!();
        };
        let world = &alternatives[0].worlds[0];
        let (block, index, target, arguments) = caller
            .blocks
            .iter()
            .find_map(|b| {
                b.instructions
                    .iter()
                    .enumerate()
                    .find_map(|(i, instruction)| {
                        if let VirInstruction::Call {
                            target, arguments, ..
                        } = &instruction.instruction
                        {
                            Some((b, i, target, arguments))
                        } else {
                            None
                        }
                    })
            })
            .unwrap();
        let analysis = &report.functions()[&caller.id].cfg().blocks()[&block.id];
        let before = if index == 0 {
            analysis.entry_state()
        } else {
            &analysis.instruction_states()[index - 1]
        };
        let queries = QueryLog::default();
        let cx = CallInstantiation {
            loss: &std::cell::Cell::new(None),
            before,
            consumed: before,
            arguments,
            memory: unit.runtime().memory,
            site: 99,
            target,
            queries: &queries,
            limits: Default::default(),
        };
        let outcomes = super::super::instantiate(summary, cx).unwrap().unwrap();
        let original = &outcomes[0].values;
        let abi = target.abi.as_ref().unwrap();
        let a = abi.parameters()[0].result_slots()[0] as usize;
        let b = abi.parameters()[1].result_slots()[0] as usize;
        let AbstractValue::Permission(first) = original[a] else {
            panic!();
        };
        let AbstractValue::Permission(second) = original[b] else {
            panic!();
        };
        assert_eq!(first.provenance(), second.provenance());
        assert_eq!(first.range(), second.range());
        assert_ne!(
            first.authority(),
            second.authority(),
            "same bytes, distinct live shared tokens"
        );
        let cx = CallInstantiation {
            loss: &std::cell::Cell::new(None),
            before,
            consumed: before,
            arguments,
            memory: unit.runtime().memory,
            site: 99,
            target,
            queries: &queries,
            limits: Default::default(),
        };
        assert!(validate_exports(world, &cx, original));
        for changed in [
            first.with_authority(second.authority()),
            first.with_authority(PermissionAuthority::Owner),
            first.with_availability(PermissionAvailability::Consumed),
            crate::AbstractPermission::new(
                first.provenance(),
                crate::AbstractByteRange::Exact(ByteRange::new(0, 16).unwrap()),
                first.access(),
                FreeCapability::No,
            )
            .with_authority(first.authority()),
        ] {
            let mut values = original.clone();
            values[a] = AbstractValue::Permission(changed);
            assert!(!validate_exports(world, &cx, &values));
        }
    }
}
