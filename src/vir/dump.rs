use std::fmt::{self, Write};

use super::{
    RuntimeVirView, SpannedVirInstruction, SpannedVirTerminator, VirAbiClass, VirAbiSignature,
    VirAbiValue, VirBasicBlock, VirBlockTarget, VirBorrowEnvironment, VirBorrowRegionOrigin,
    VirBorrowRegionScope, VirConstant, VirEndianness, VirFunction, VirIndexBounds, VirInstruction,
    VirIntegerPredicate, VirIntegerType, VirLoanEffect, VirLoanKind, VirMemoryAccess,
    VirMemorySchema, VirMemoryTypeKind, VirMutability, VirObjectDestinationMode,
    VirObjectSourceMode, VirOriginKind, VirPointerKind, VirSignature, VirTerminator, VirType,
    VirUnit, VirUnitVersion, VirValue, VirValueId,
};
use crate::{BorrowGuardAtom, ByteSpan};

pub(super) fn stable_dump(unit: &VirUnit) -> String {
    let mut output = String::new();
    dump_unit(&mut output, unit).expect("writing VIR to a String cannot fail");
    output
}

pub(super) fn stable_runtime_dump(runtime: RuntimeVirView<'_>) -> String {
    let mut output = String::new();
    writeln!(output, "runtime-vir-v17").expect("writing VIR to a String cannot fail");
    dump_memory_schema(&mut output, runtime.memory).expect("writing VIR to a String cannot fail");
    writeln!(output, "borrow-regions {{").expect("writing VIR to a String cannot fail");
    dump_borrow_environment(&mut output, runtime.borrows)
        .expect("writing VIR to a String cannot fail");
    writeln!(output, "}}").expect("writing VIR to a String cannot fail");
    dump_runtime_program(&mut output, runtime).expect("writing VIR to a String cannot fail");
    output
}

fn dump_unit(output: &mut String, unit: &VirUnit) -> fmt::Result {
    match unit.version {
        VirUnitVersion::V1 => writeln!(output, "vir-unit-v1")?,
        VirUnitVersion::V2 => writeln!(output, "vir-unit-v2")?,
        VirUnitVersion::V3 => writeln!(output, "vir-unit-v3")?,
        VirUnitVersion::V4 => writeln!(output, "vir-unit-v4")?,
        VirUnitVersion::V5 => writeln!(output, "vir-unit-v5")?,
        VirUnitVersion::V6 => writeln!(output, "vir-unit-v6")?,
        VirUnitVersion::V7 => writeln!(output, "vir-unit-v7")?,
        VirUnitVersion::V8 => writeln!(output, "vir-unit-v8")?,
        VirUnitVersion::V9 => writeln!(output, "vir-unit-v9")?,
        VirUnitVersion::V10 => writeln!(output, "vir-unit-v10")?,
        VirUnitVersion::V11 => writeln!(output, "vir-unit-v11")?,
        VirUnitVersion::V12 => writeln!(output, "vir-unit-v12")?,
        VirUnitVersion::V13 => writeln!(output, "vir-unit-v13")?,
        VirUnitVersion::V14 => writeln!(output, "vir-unit-v14")?,
        VirUnitVersion::V15 => writeln!(output, "vir-unit-v15")?,
        VirUnitVersion::V16 => writeln!(output, "vir-unit-v16")?,
        VirUnitVersion::V17 => writeln!(output, "vir-unit-v17")?,
        VirUnitVersion::V18 => writeln!(output, "vir-unit-v18")?,
        VirUnitVersion::V19 => writeln!(output, "vir-unit-v19")?,
        VirUnitVersion::V20 => writeln!(output, "vir-unit-v20")?,
        VirUnitVersion::V21 => writeln!(output, "vir-unit-v21")?,
        VirUnitVersion::V22 => writeln!(output, "vir-unit-v22")?,
        VirUnitVersion::V23 => writeln!(output, "vir-unit-v23")?,
        VirUnitVersion::V24 => writeln!(output, "vir-unit-v24")?,
        VirUnitVersion::V27 => writeln!(output, "vir-unit-v27")?,
        VirUnitVersion::V28 => writeln!(output, "vir-unit-v28")?,
        VirUnitVersion::V26 => writeln!(output, "vir-unit-v26")?,
        VirUnitVersion::V25 => writeln!(output, "vir-unit-v25")?,
    }
    writeln!(output, "memory {{")?;
    dump_memory_schema(output, &unit.memory)?;
    writeln!(output, "}}")?;
    writeln!(output, "borrow-regions {{")?;
    dump_borrow_environment(output, &unit.borrows)?;
    writeln!(output, "}}")?;
    writeln!(output, "runtime {{")?;
    dump_runtime_program(output, unit.runtime())?;
    writeln!(output, "}}")?;
    writeln!(output, "specs {{")?;
    dump_specs(output, &unit.specs)?;
    writeln!(output, "}}")?;
    writeln!(output, "source-map {{")?;
    for source in unit.source_map.sources() {
        write!(output, "source source{} ", source.id.get())?;
        write_quoted(output, &source.name)?;
        writeln!(output, " bytes {}", source.byte_len)?;
    }
    for origin in unit.source_map.origins() {
        write!(output, "origin origin{} = ", origin.id.get())?;
        match &origin.kind {
            VirOriginKind::User { source, span } => {
                write!(output, "user source{} ", source.get())?;
                write_span(output, *span)?;
                writeln!(output)?;
            }
            VirOriginKind::Generated { parent, reason } => writeln!(
                output,
                "generated origin{} reason {}",
                parent.get(),
                generated_reason_name(*reason)
            )?,
        }
    }
    for entry in unit.source_map.locations() {
        write!(output, "location ")?;
        write_location(output, entry.location)?;
        writeln!(output, " -> origin{}", entry.origin.get())?;
    }
    writeln!(output, "}}")
}

fn dump_specs(output: &mut String, specs: &super::VirSpecEnvironment) -> fmt::Result {
    for contract in specs.contracts() {
        write!(
            output,
            "contract contract{} function fn{} ",
            contract.id.get(),
            contract.function.get()
        )?;
        write_signature(output, &contract.signature)?;
        writeln!(output, " {{")?;
        for binder in &contract.binders {
            write!(
                output,
                "  binder binder{} {} slot{}: ",
                binder.id.get(),
                contract_position_name(binder.position),
                binder.slot
            )?;
            write_type(output, binder.ty)?;
            writeln!(output)?;
        }
        for resource in &contract.resources {
            writeln!(output, "  resource resource{}", resource.id.get())?;
        }
        write!(output, "  clauses [")?;
        for (index, clause) in contract.clauses.iter().enumerate() {
            if index != 0 {
                write!(output, ", ")?;
            }
            write!(output, "clause{}", clause.get())?;
        }
        writeln!(output, "]")?;
        writeln!(output, "}}")?;
    }
    for predicate in specs.predicates() {
        write!(output, "predicate predicate{} ", predicate.id.get())?;
        write_quoted(output, &predicate.name)?;
        write!(output, " binders [")?;
        for (index, binder) in predicate.binders.iter().enumerate() {
            if index != 0 {
                write!(output, ", ")?;
            }
            write!(output, "sbinder{}", binder.get())?;
        }
        writeln!(
            output,
            "] origin{} body {}",
            predicate.origin.get(),
            predicate.body.map_or_else(
                || "none".to_owned(),
                |clause| format!("clause{}", clause.get())
            )
        )?;
    }
    for binder in specs.binders() {
        write!(output, "spec-binder sbinder{} ", binder.id.get())?;
        write_spec_binder_owner(output, binder.owner)?;
        write!(output, " ")?;
        write_quoted(output, &binder.name)?;
        writeln!(
            output,
            ": {} origin{}",
            spec_type_name(binder.ty),
            binder.origin.get()
        )?;
    }
    for assertion in specs.assertions() {
        write!(
            output,
            "assertion assertion{} clause{} origin{} = ",
            assertion.id.get(),
            assertion.clause.get(),
            assertion.origin.get()
        )?;
        dump_spec_assertion_kind(output, &assertion.kind)?;
        writeln!(output)?;
    }
    for term in specs.terms() {
        write!(
            output,
            "term term{} clause{}: {} origin{} = ",
            term.id.get(),
            term.clause.get(),
            spec_type_name(term.ty),
            term.origin.get()
        )?;
        dump_spec_term_kind(output, &term.kind)?;
        writeln!(output)?;
    }
    for clause in specs.clauses() {
        write!(output, "clause clause{} ", clause.id.get())?;
        write_spec_clause_owner(output, clause.owner)?;
        write!(output, " at ")?;
        write_spec_location(output, clause.location)?;
        write!(output, " {} = ", clause_origin_name(clause.origin))?;
        dump_spec_clause_kind(output, &clause.kind)?;
        writeln!(output)?;
    }
    for prove in specs.proves() {
        write!(
            output,
            "prove prove{} function fn{} at ",
            prove.id.get(),
            prove.function.get()
        )?;
        write_spec_location(output, prove.location)?;
        writeln!(
            output,
            " clause{} origin{}",
            prove.clause.get(),
            prove.origin.get()
        )?;
    }
    for entry in specs.trust_entries() {
        write!(output, "trust trust{} ", entry.id.get())?;
        write_trust_scope(output, entry.scope)?;
        writeln!(
            output,
            " policy {} clause{} origin{}",
            trust_policy_name(entry.policy),
            entry.clause.get(),
            entry.origin.get()
        )?;
    }
    for invariant in specs.loop_invariants() {
        writeln!(output, "loop-boundary {:?}", invariant.boundary)?;
        write!(
            output,
            "loop-invariant invariant{} function fn{} at ",
            invariant.id.get(),
            invariant.function.get()
        )?;
        write_spec_location(output, invariant.location)?;
        writeln!(
            output,
            " clause{} origin{}",
            invariant.clause.get(),
            invariant.origin.get()
        )?;
    }
    Ok(())
}

fn dump_borrow_environment(output: &mut String, borrows: &VirBorrowEnvironment) -> fmt::Result {
    for region in borrows.regions() {
        write!(
            output,
            "region bregion{} owner fn{} origin ",
            region.id.get(),
            region.owner.get()
        )?;
        match region.origin {
            VirBorrowRegionOrigin::Lexical => write!(output, "lexical")?,
            VirBorrowRegionOrigin::Parameter { index } => {
                write!(output, "parameter({index})")?;
            }
            VirBorrowRegionOrigin::Result { index } => write!(output, "result({index})")?,
            VirBorrowRegionOrigin::Inferred => write!(output, "inferred")?,
        }
        write!(output, " scope ")?;
        match &region.scope {
            VirBorrowRegionScope::Function => write!(output, "function")?,
            VirBorrowRegionScope::Blocks(blocks) => {
                write!(output, "blocks[")?;
                for (index, block) in blocks.iter().enumerate() {
                    if index != 0 {
                        write!(output, ",")?;
                    }
                    write!(output, "bb{}", block.get())?;
                }
                write!(output, "]")?;
            }
        }
        writeln!(output, " source origin{}", region.source_origin.get())?;
    }
    for constraint in borrows.constraints() {
        writeln!(
            output,
            "constraint bconstraint{} owner fn{} bregion{} <= bregion{} source origin{}",
            constraint.id.get(),
            constraint.owner.get(),
            constraint.subregion.get(),
            constraint.superregion.get(),
            constraint.source_origin.get()
        )?;
    }
    Ok(())
}

fn dump_spec_assertion_kind(
    output: &mut String,
    kind: &super::VirSpecAssertionKind,
) -> fmt::Result {
    use crate::SpecAssertionKind as A;
    match kind {
        A::Footprint { write, range } => write!(
            output,
            "{} {range:?}",
            if *write { "writes" } else { "reads" }
        ),
        A::Disjoint { left, right } => write!(output, "disjoint {left:?} {right:?}"),
        A::Alive(pointer) => {
            write!(output, "alive ")?;
            dump_spec_term_kind(output, &super::VirSpecTermKind::Snapshot(*pointer))
        }
        A::SameAllocation { left, right } => {
            write!(output, "same-allocation ")?;
            dump_spec_term_kind(output, &super::VirSpecTermKind::Snapshot(*left))?;
            write!(output, " ")?;
            dump_spec_term_kind(output, &super::VirSpecTermKind::Snapshot(*right))
        }
        A::Initialized {
            pointer,
            start_bytes,
            end_bytes,
            layout,
        } => {
            write!(output, "initialized ")?;
            dump_spec_term_kind(output, &super::VirSpecTermKind::Snapshot(*pointer))?;
            write!(
                output,
                " bytes [term{}, term{}) type{} layout{}",
                start_bytes.get(),
                end_bytes.get(),
                layout.ty.get(),
                layout.layout.get()
            )
        }
        A::Pure(term) => write!(output, "pure term{}", term.get()),
        A::Permission(memory) | A::PointsTo { memory, .. } => {
            write!(
                output,
                "{} ",
                if matches!(kind, A::Permission(_)) {
                    "permission"
                } else {
                    "points-to"
                }
            )?;
            dump_spec_term_kind(output, &super::VirSpecTermKind::Snapshot(memory.pointer))?;
            write!(output, " authority ")?;
            dump_spec_term_kind(output, &super::VirSpecTermKind::Snapshot(memory.authority))?;
            write!(
                output,
                " bytes [term{}, term{}) type{} layout{} {}",
                memory.start_bytes.get(),
                memory.end_bytes.get(),
                memory.layout.ty.get(),
                memory.layout.layout.get(),
                match memory.access {
                    crate::SpecAccess::Read => "read",
                    crate::SpecAccess::Write => "write",
                }
            )?;
            if let A::PointsTo { value, .. } = kind {
                if let Some(value) = value {
                    write!(output, " value term{}", value.get())?;
                } else {
                    write!(output, " value _")?;
                }
            }
            Ok(())
        }
        A::Conditional { guard, body } => write!(
            output,
            "conditional term{} assertion{}",
            guard.get(),
            body.get()
        ),
        A::Separation(children) => {
            write!(output, "separation [")?;
            for (i, child) in children.iter().enumerate() {
                if i != 0 {
                    write!(output, ", ")?;
                }
                write!(output, "assertion{}", child.get())?;
            }
            write!(output, "]")
        }
        A::Exists {
            binder,
            body,
            witness,
        } => {
            write!(
                output,
                "exists sbinder{} body assertion{} witness ",
                binder.get(),
                body.get()
            )?;
            match witness {
                Some(id) => write!(output, "term{}", id.get()),
                None => write!(output, "none"),
            }
        }
    }
}

fn dump_spec_clause_kind(output: &mut String, kind: &super::VirSpecClauseKind) -> fmt::Result {
    match kind {
        super::VirSpecClauseKind::Resource(summary) => {
            write!(
                output,
                "resource resource{} region{} size {} align {} {} {} {} pointers [",
                summary.resource.get(),
                summary.region.get(),
                summary.size_bytes,
                summary.alignment,
                liveness_name(summary.liveness),
                ownership_name(summary.ownership),
                initialization_name(summary.initialization),
            )?;
            for (index, pointer) in summary.pointers.iter().enumerate() {
                if index != 0 {
                    write!(output, ", ")?;
                }
                write!(
                    output,
                    "binder{}@{}..{}/{}",
                    pointer.binder.get(),
                    pointer.offset_lower,
                    pointer.offset_upper,
                    pointer.alignment
                )?;
            }
            write!(output, "] permissions [")?;
            for (index, permission) in summary.permissions.iter().enumerate() {
                if index != 0 {
                    write!(output, ", ")?;
                }
                write!(
                    output,
                    "binder{}@{}..{}/{}/{}",
                    permission.binder.get(),
                    permission.start_byte,
                    permission.end_byte,
                    contract_access_name(permission.access),
                    contract_free_name(permission.free)
                )?;
            }
            write!(output, "]")
        }
        super::VirSpecClauseKind::U64Range {
            binder,
            lower,
            upper,
        } => write!(
            output,
            "u64-range binder{} {}..{}",
            binder.get(),
            lower,
            upper
        ),
        super::VirSpecClauseKind::BoolValue { binder, value } => {
            write!(output, "bool-value binder{} {value}", binder.get())
        }
        super::VirSpecClauseKind::Logic { root } => write!(output, "logic term{}", root.get()),
        super::VirSpecClauseKind::Assertion { root } => {
            write!(output, "assertion assertion{}", root.get())
        }
    }
}

fn write_spec_binder_owner(output: &mut String, owner: super::VirSpecBinderOwner) -> fmt::Result {
    match owner {
        super::VirSpecBinderOwner::Clause(clause) => write!(output, "clause{}", clause.get()),
        super::VirSpecBinderOwner::Predicate(predicate) => {
            write!(output, "predicate{}", predicate.get())
        }
    }
}

fn write_spec_clause_owner(output: &mut String, owner: super::VirSpecClauseOwner) -> fmt::Result {
    match owner {
        super::VirSpecClauseOwner::Contract { contract, position } => write!(
            output,
            "contract{} {}",
            contract.get(),
            contract_position_name(position)
        ),
        super::VirSpecClauseOwner::Prove(prove) => {
            write!(output, "prove{}", prove.get())
        }
        super::VirSpecClauseOwner::TrustEntry(entry) => {
            write!(output, "trust{}", entry.get())
        }
        super::VirSpecClauseOwner::LoopInvariant(invariant) => {
            write!(output, "invariant{}", invariant.get())
        }
    }
}

fn write_trust_scope(output: &mut String, scope: super::VirTrustScope) -> fmt::Result {
    match scope {
        super::VirTrustScope::FunctionEntry { function } => {
            write!(output, "scope fn{}:entry", function.get())
        }
        super::VirTrustScope::FunctionResult { function } => {
            write!(output, "scope fn{}:result", function.get())
        }
        super::VirTrustScope::Runtime(location) => {
            write!(output, "scope ")?;
            write_location(output, location)
        }
    }
}

const fn trust_policy_name(policy: super::VirTrustPolicyKind) -> &'static str {
    match policy {
        super::VirTrustPolicyKind::EntryPointAssumption => "entry-point-assumption",
        super::VirTrustPolicyKind::ForeignContract => "foreign-contract",
        super::VirTrustPolicyKind::ExternallyVerified => "externally-verified",
    }
}

fn write_spec_location(output: &mut String, location: super::VirSpecLocation) -> fmt::Result {
    match location {
        super::VirSpecLocation::FunctionEntry { function } => {
            write!(output, "fn{}:entry", function.get())
        }
        super::VirSpecLocation::FunctionResult { function } => {
            write!(output, "fn{}:result", function.get())
        }
        super::VirSpecLocation::Runtime(location) => write_location(output, location),
    }
}

const fn spec_type_name(ty: super::VirSpecType) -> &'static str {
    match ty {
        super::VirSpecType::Bool => "bool",
        super::VirSpecType::U64 => "u64",
    }
}

fn dump_spec_term_kind(output: &mut String, kind: &super::VirSpecTermKind) -> fmt::Result {
    match kind {
        super::VirSpecTermKind::CheckedAdd { left, right } => {
            write!(output, "checked-add term{} term{}", left.get(), right.get())
        }
        super::VirSpecTermKind::CheckedSub { left, right } => {
            write!(output, "checked-sub term{} term{}", left.get(), right.get())
        }
        super::VirSpecTermKind::CheckedScale { operand, stride } => write!(
            output,
            "checked-scale term{} stride {stride}",
            operand.get()
        ),
        super::VirSpecTermKind::RangeContains {
            outer_start: a,
            outer_end: b,
            inner_start: c,
            inner_end: d,
        }
        | super::VirSpecTermKind::RangeDisjoint {
            left_start: a,
            left_end: b,
            right_start: c,
            right_end: d,
        } => write!(
            output,
            "{} bytes [term{}, term{}) [term{}, term{})",
            if matches!(kind, super::VirSpecTermKind::RangeContains { .. }) {
                "range-contains"
            } else {
                "range-disjoint"
            },
            a.get(),
            b.get(),
            c.get(),
            d.get()
        ),
        super::VirSpecTermKind::Snapshot(super::VirSpecSnapshot::Memory {
            function,
            parameter,
            old,
            projection,
        }) => write!(
            output,
            "memory fn{} input={parameter:?} old={old} {projection:?}",
            function.get()
        ),
        super::VirSpecTermKind::Bool(value) => write!(output, "bool {value}"),
        super::VirSpecTermKind::U64(value) => write!(output, "u64 {value}"),
        super::VirSpecTermKind::Binder(binder) => write!(output, "sbinder{}", binder.get()),
        super::VirSpecTermKind::Snapshot(super::VirSpecSnapshot::EntryParameter {
            function,
            slot,
        }) => {
            write!(output, "entry-param fn{} slot{}", function.get(), slot)
        }
        super::VirSpecTermKind::Snapshot(super::VirSpecSnapshot::Parameter { function, slot }) => {
            write!(output, "snapshot fn{}:parameter{}", function.get(), slot)
        }
        super::VirSpecTermKind::Snapshot(super::VirSpecSnapshot::Result { function, slot }) => {
            write!(output, "snapshot fn{}:result{}", function.get(), slot)
        }
        super::VirSpecTermKind::Snapshot(super::VirSpecSnapshot::Value { function, value }) => {
            write!(output, "snapshot fn{}:%{}", function.get(), value.get())
        }
        super::VirSpecTermKind::Equal { left, right } => {
            write!(output, "eq term{} term{}", left.get(), right.get())
        }
        super::VirSpecTermKind::LessThan { left, right } => {
            write!(output, "lt term{} term{}", left.get(), right.get())
        }
        super::VirSpecTermKind::LessOrEqual { left, right } => {
            write!(output, "le term{} term{}", left.get(), right.get())
        }
        super::VirSpecTermKind::Not(operand) => write!(output, "not term{}", operand.get()),
        super::VirSpecTermKind::And(operands) => dump_spec_term_list(output, "and", operands),
        super::VirSpecTermKind::Or(operands) => dump_spec_term_list(output, "or", operands),
    }
}

fn dump_spec_term_list(
    output: &mut String,
    operator: &str,
    operands: &[super::VirSpecTermId],
) -> fmt::Result {
    write!(output, "{operator} [")?;
    for (index, operand) in operands.iter().enumerate() {
        if index != 0 {
            write!(output, ", ")?;
        }
        write!(output, "term{}", operand.get())?;
    }
    write!(output, "]")
}

fn clause_origin_name(origin: super::VirSpecClauseOrigin) -> String {
    match origin {
        super::VirSpecClauseOrigin::InferredType { origin } => {
            format!("inferred-type origin{}", origin.get())
        }
        super::VirSpecClauseOrigin::InferredLoop { origin } => {
            format!("inferred-loop origin{}", origin.get())
        }
        super::VirSpecClauseOrigin::Explicit { origin } => {
            format!("explicit origin{}", origin.get())
        }
    }
}

const fn contract_position_name(position: super::VirContractPosition) -> &'static str {
    match position {
        super::VirContractPosition::Requires => "requires",
        super::VirContractPosition::Ensures => "ensures",
    }
}

const fn liveness_name(liveness: super::VirContractLiveness) -> &'static str {
    match liveness {
        super::VirContractLiveness::Live => "live",
        super::VirContractLiveness::Dead => "dead",
    }
}

const fn ownership_name(ownership: super::VirContractOwnership) -> &'static str {
    match ownership {
        super::VirContractOwnership::Owned => "owned",
        super::VirContractOwnership::Unowned => "unowned",
        super::VirContractOwnership::Local => "local",
    }
}

const fn initialization_name(initialization: super::VirContractInitialization) -> &'static str {
    match initialization {
        super::VirContractInitialization::Initialized => "initialized",
        super::VirContractInitialization::Uninitialized => "uninitialized",
        super::VirContractInitialization::Unknown => "unknown-initialization",
    }
}

const fn contract_access_name(access: super::VirContractAccess) -> &'static str {
    match access {
        super::VirContractAccess::Read => "read",
        super::VirContractAccess::Write => "write",
    }
}

const fn contract_free_name(free: super::VirContractFree) -> &'static str {
    match free {
        super::VirContractFree::No => "no-free",
        super::VirContractFree::Yes => "free",
    }
}

fn generated_reason_name(reason: super::VirGeneratedReason) -> &'static str {
    match reason {
        super::VirGeneratedReason::ControlFlowBlock => "control-flow-block",
        super::VirGeneratedReason::BlockParameter => "block-parameter",
        super::VirGeneratedReason::PermissionParameter => "permission-parameter",
        super::VirGeneratedReason::ControlFlowEdge => "control-flow-edge",
        super::VirGeneratedReason::ImplicitReturn => "implicit-return",
        super::VirGeneratedReason::LoopIncrement => "loop-increment",
        super::VirGeneratedReason::TemporaryStorage => "temporary-storage",
        super::VirGeneratedReason::ImplicitCopy => "implicit-copy",
        super::VirGeneratedReason::ImplicitMove => "implicit-move",
        super::VirGeneratedReason::ImplicitDrop => "implicit-drop",
        super::VirGeneratedReason::ScopeCleanup => "scope-cleanup",
        super::VirGeneratedReason::BranchCleanup => "branch-cleanup",
        super::VirGeneratedReason::CallTransfer => "call-transfer",
        super::VirGeneratedReason::ReturnTransfer => "return-transfer",
        super::VirGeneratedReason::LoanEffect => "loan-effect",
    }
}

fn write_location(output: &mut impl Write, location: super::VirLocation) -> fmt::Result {
    match location {
        super::VirLocation::FunctionEntry { function } => {
            write!(output, "fn{}:entry", function.get())
        }
        super::VirLocation::BlockEntry { function, block } => {
            write!(output, "fn{}/bb{}:entry", function.get(), block.get())
        }
        super::VirLocation::BlockParameter {
            function,
            block,
            ordinal,
        } => write!(
            output,
            "fn{}/bb{}:parameter{}",
            function.get(),
            block.get(),
            ordinal
        ),
        super::VirLocation::Instruction {
            function,
            block,
            ordinal,
        } => write!(
            output,
            "fn{}/bb{}:instruction{}",
            function.get(),
            block.get(),
            ordinal
        ),
        super::VirLocation::CallEdge {
            function,
            block,
            instruction,
        } => write!(
            output,
            "fn{}/bb{}:call-edge{}",
            function.get(),
            block.get(),
            instruction
        ),
        super::VirLocation::Terminator { function, block } => {
            write!(output, "fn{}/bb{}:terminator", function.get(), block.get())
        }
    }
}

fn dump_runtime_program(output: &mut String, runtime: RuntimeVirView<'_>) -> fmt::Result {
    writeln!(output, "entry fn{}", runtime.entry.get())?;
    for function in runtime.functions {
        writeln!(output)?;
        if let Some(abi) = runtime.abis.function(function.id)
            && abi.signature != VirAbiSignature::identity(&function.signature)
        {
            dump_abi_signature(output, function.id, &abi.signature)?;
        }
        dump_function(output, function)?;
    }
    Ok(())
}

fn dump_abi_signature(
    output: &mut String,
    function: super::VirFunctionId,
    signature: &VirAbiSignature,
) -> fmt::Result {
    write!(output, "abi fn{} params [", function.get())?;
    for (index, binding) in signature.parameters().iter().enumerate() {
        if index != 0 {
            write!(output, ", ")?;
        }
        write_abi_value(output, binding.value())?;
        write_interface_effect(output, binding.interface())?;
        write!(
            output,
            " p{:?} r{:?}",
            binding.parameter_slots(),
            binding.result_slots()
        )?;
    }
    write!(output, "] results [")?;
    for (index, binding) in signature.results().iter().enumerate() {
        if index != 0 {
            write!(output, ", ")?;
        }
        write_abi_value(output, binding.value())?;
        write_interface_effect(output, binding.interface())?;
        write!(
            output,
            " p{:?} r{:?}",
            binding.parameter_slots(),
            binding.result_slots()
        )?;
    }
    write!(output, "]")?;
    if let Some(relation) = signature.borrow_result() {
        write!(
            output,
            " borrow-result{}=param{}/{:?}/{:?}",
            relation.result, relation.parameter, relation.projection, relation.access
        )?;
    }
    for (index, alternative) in signature.borrow_result_alternatives().iter().enumerate() {
        write!(output, " borrow-result-alt{index}[")?;
        for (atom_index, atom) in alternative.guard.iter().enumerate() {
            if atom_index != 0 {
                write!(output, ",")?;
            }
            match atom {
                BorrowGuardAtom::Boolean {
                    parameter,
                    expected,
                } => write!(output, "param{parameter}={expected}")?,
            }
        }
        let relation = alternative.relation;
        write!(
            output,
            "]=result{}:param{}/{:?}/{:?}",
            relation.result, relation.parameter, relation.projection, relation.access
        )?;
    }
    writeln!(output)
}

fn write_interface_effect(output: &mut String, effect: super::VirInterfaceEffect) -> fmt::Result {
    write!(
        output,
        " effect {}/{}",
        interface_transfer_name(effect.transfer),
        interface_storage_name(effect.storage)
    )
}

fn write_abi_value(output: &mut String, value: &VirAbiValue) -> fmt::Result {
    match value {
        VirAbiValue::Opaque(ty) => {
            write!(output, "opaque<")?;
            write_type(output, *ty)?;
            write!(output, ">")
        }
        VirAbiValue::Unit { access } => write!(output, "unit<{}>", access_name(*access)),
        VirAbiValue::Scalar { access, .. } => {
            write!(output, "scalar<{}>", access_name(*access))
        }
        VirAbiValue::Pointer { access, .. } => {
            write!(output, "pointer<{}>", access_name(*access))
        }
        VirAbiValue::Slice { access, .. } => {
            write!(output, "slice<{}>", access_name(*access))
        }
        VirAbiValue::DirectAggregate { access, leaves } => {
            write!(output, "direct<{}:[", access_name(*access))?;
            for (index, leaf) in leaves.iter().enumerate() {
                if index != 0 {
                    write!(output, ",")?;
                }
                write!(
                    output,
                    "{}@{}",
                    access_name(leaf.access()),
                    leaf.offset_bytes()
                )?;
            }
            write!(output, "]>")
        }
        VirAbiValue::IndirectAggregate { access } => {
            write!(output, "indirect<{}>", access_name(*access))
        }
    }
}

fn dump_function(output: &mut String, function: &VirFunction) -> fmt::Result {
    write!(output, "fn fn{} ", function.id.get())?;
    write_quoted(output, &function.name)?;
    write!(output, " ")?;
    write_signature(output, &function.signature)?;
    write!(
        output,
        " contract contract{} entry bb{} ",
        function.contract.get(),
        function.entry.get()
    )?;
    write_span(output, function.source_span)?;
    writeln!(output, " {{")?;
    for block in &function.blocks {
        dump_block(output, block)?;
    }
    writeln!(output, "}}")
}

fn dump_block(output: &mut String, block: &VirBasicBlock) -> fmt::Result {
    write!(output, "  bb{}(", block.id.get())?;
    write_value_declarations(output, &block.parameters)?;
    write!(output, ") ")?;
    write_span(output, block.source_span)?;
    writeln!(output, ":")?;
    for instruction in &block.instructions {
        dump_instruction(output, instruction)?;
    }
    dump_terminator(output, &block.terminator)
}

fn dump_instruction(output: &mut String, spanned: &SpannedVirInstruction) -> fmt::Result {
    write!(output, "    ")?;
    match &spanned.instruction {
        VirInstruction::PointerCompare {
            result,
            predicate,
            left,
            right,
        } => {
            write_value_declaration(output, *result)?;
            write!(
                output,
                " = ptr.cmp.{} {}, {}",
                predicate_name(*predicate),
                value_name(*left),
                value_name(*right)
            )?;
        }
        VirInstruction::PointerDistance { result, begin, end } => {
            write_value_declaration(output, *result)?;
            write!(
                output,
                " = ptr.byte_distance {}, {}",
                value_name(*begin),
                value_name(*end)
            )?;
        }
        VirInstruction::Constant { result, value } => {
            write_value_declaration(output, *result)?;
            match value {
                VirConstant::U64(value) => write!(output, " = const.u64 {value}")?,
                VirConstant::Bool(value) => write!(output, " = const.bool {value}")?,
            }
        }
        VirInstruction::WordAdd {
            result,
            left,
            right,
        } => {
            write_value_declaration(output, *result)?;
            write!(
                output,
                " = add {}, {}",
                value_name(*left),
                value_name(*right)
            )?;
        }
        VirInstruction::Compare {
            result,
            predicate,
            left,
            right,
        } => {
            write_value_declaration(output, *result)?;
            write!(
                output,
                " = cmp.{} {}, {}",
                predicate_name(*predicate),
                value_name(*left),
                value_name(*right)
            )?;
        }
        VirInstruction::Allocate {
            pointer_result,
            permission_result,
            size_bytes,
            alignment,
            region,
            element,
        } => {
            write_value_declaration(output, *pointer_result)?;
            write!(output, ", ")?;
            write_value_declaration(output, *permission_result)?;
            write!(
                output,
                " = alloc {} align {} region{} access {}",
                value_name(*size_bytes),
                alignment,
                region.get(),
                access_name(*element)
            )?;
        }
        VirInstruction::LocalStorage {
            pointer_result,
            permission_result,
            access,
        } => {
            write_value_declaration(output, *pointer_result)?;
            write!(output, ", ")?;
            write_value_declaration(output, *permission_result)?;
            write!(output, " = local-storage access {}", access_name(*access))?;
        }
        VirInstruction::Initialize {
            pointer,
            value,
            permission,
            access,
        } => write!(
            output,
            "init {}, {} using {} access {}",
            value_name(*pointer),
            value_name(*value),
            value_name(*permission),
            access_name(*access)
        )?,
        VirInstruction::ObjectTransfer {
            destination,
            destination_permission,
            source,
            source_permission,
            access,
            destination_mode,
            source_mode,
        } => write!(
            output,
            "object.{}.{} {}, {} using {}, {} access {}",
            object_destination_mode_name(*destination_mode),
            object_source_mode_name(*source_mode),
            value_name(*destination),
            value_name(*source),
            value_name(*destination_permission),
            value_name(*source_permission),
            access_name(*access)
        )?,
        VirInstruction::ResourceStorageReset {
            pointer,
            permission,
            access,
        } => write!(
            output,
            "resource.storage.reset {} using {} access {}",
            value_name(*pointer),
            value_name(*permission),
            access_name(*access)
        )?,
        VirInstruction::StorageReset {
            pointer,
            permission,
            access,
        } => write!(
            output,
            "storage.reset {} using {} access {}",
            value_name(*pointer),
            value_name(*permission),
            access_name(*access)
        )?,
        VirInstruction::ObjectDeinitialize {
            pointer,
            permission,
            access,
        } => write!(
            output,
            "object.deinit {} using {} access {}",
            value_name(*pointer),
            value_name(*permission),
            access_name(*access)
        )?,
        VirInstruction::ObjectDrop {
            pointer,
            permission,
            access,
            condition,
        } => write!(
            output,
            "object.drop {} using {} if {} access {}",
            value_name(*pointer),
            value_name(*permission),
            value_name(*condition),
            access_name(*access)
        )?,
        VirInstruction::EnumSetDiscriminant {
            pointer,
            permission,
            access,
            variant,
            mode,
        } => write!(
            output,
            "enum.{}-discriminant {} using {} access {} variant{}",
            object_destination_mode_name(*mode),
            value_name(*pointer),
            value_name(*permission),
            access_name(*access),
            variant.get()
        )?,
        VirInstruction::Write {
            pointer,
            value,
            permission,
            access,
        } => write!(
            output,
            "write {}, {} using {} access {}",
            value_name(*pointer),
            value_name(*value),
            value_name(*permission),
            access_name(*access)
        )?,
        VirInstruction::Load {
            result,
            pointer,
            permission,
            access,
        } => {
            write_value_declaration(output, *result)?;
            write!(
                output,
                " = load {} using {} access {}",
                value_name(*pointer),
                value_name(*permission),
                access_name(*access)
            )?;
        }
        VirInstruction::EnumDiscriminant {
            result,
            pointer,
            permission,
            access,
        } => {
            write_value_declaration(output, *result)?;
            write!(
                output,
                " = enum.discriminant {} using {} access {}",
                value_name(*pointer),
                value_name(*permission),
                access_name(*access)
            )?;
        }
        VirInstruction::Store {
            pointer,
            value,
            permission,
            access,
        } => write!(
            output,
            "store {}, {} using {} access {}",
            value_name(*pointer),
            value_name(*value),
            value_name(*permission),
            access_name(*access)
        )?,
        VirInstruction::ResourceInitialize {
            destination,
            destination_permission,
            value,
            value_permission,
            access,
        } => write!(
            output,
            "resource.init {}, {} using {}, {} access {}",
            value_name(*destination),
            value_name(*value),
            value_name(*destination_permission),
            value_name(*value_permission),
            access_name(*access)
        )?,
        VirInstruction::ResourceTake {
            pointer_result,
            permission_result,
            source,
            source_permission,
            access,
        } => {
            write_value_declaration(output, *pointer_result)?;
            write!(output, ", ")?;
            write_value_declaration(output, *permission_result)?;
            write!(
                output,
                " = resource.take {} using {} access {}",
                value_name(*source),
                value_name(*source_permission),
                access_name(*access)
            )?;
        }
        VirInstruction::DropOwn {
            pointer,
            permission,
            condition,
        } => write!(
            output,
            "drop.own {} using {} if {}",
            value_name(*pointer),
            value_name(*permission),
            value_name(*condition)
        )?,
        VirInstruction::FieldAddress {
            result,
            base,
            field,
            owner,
            field_access,
            offset_bytes,
        } => {
            write_value_declaration(output, *result)?;
            write!(
                output,
                " = field.address {} field{} owner {} result {} offset {}",
                value_name(*base),
                field.get(),
                access_name(*owner),
                access_name(*field_access),
                offset_bytes
            )?;
        }
        VirInstruction::TupleElementAddress {
            result,
            base,
            index,
            owner,
            element_access,
            offset_bytes,
        } => {
            write_value_declaration(output, *result)?;
            write!(
                output,
                " = tuple.address {} element{} owner {} result {} offset {}",
                value_name(*base),
                index,
                access_name(*owner),
                access_name(*element_access),
                offset_bytes
            )?;
        }
        VirInstruction::ObjectLeafAddress {
            result,
            base,
            owner,
            leaf,
            offset_bytes,
        } => {
            write_value_declaration(output, *result)?;
            write!(
                output,
                " = object.leaf.address {} owner {} leaf {} offset {}",
                value_name(*base),
                access_name(*owner),
                access_name(*leaf),
                offset_bytes
            )?;
        }
        VirInstruction::IndexAddress {
            result,
            base,
            index,
            source,
            element,
            stride_bytes,
            bounds,
        } => {
            write_value_declaration(output, *result)?;
            write!(
                output,
                " = index.address {}, {} source {} element {} stride {} bounds ",
                value_name(*base),
                value_name(*index),
                access_name(*source),
                access_name(*element),
                stride_bytes
            )?;
            match bounds {
                VirIndexBounds::Array { length } => write!(output, "array({length})")?,
                VirIndexBounds::Slice { length } => {
                    write!(output, "slice({})", value_name(*length))?;
                }
            }
        }
        VirInstruction::SliceRange {
            pointer_result,
            length_result,
            permission_result,
            base,
            permission,
            start,
            end,
            source,
            slice,
            element,
            stride_bytes,
            bounds,
        } => {
            write_value_declaration(output, *pointer_result)?;
            write!(output, ", ")?;
            write_value_declaration(output, *length_result)?;
            write!(output, ", ")?;
            write_value_declaration(output, *permission_result)?;
            write!(
                output,
                " = slice.range {} using {} start {} end {} source {} slice {} element {} stride {} bounds ",
                value_name(*base),
                value_name(*permission),
                value_name(*start),
                value_name(*end),
                access_name(*source),
                access_name(*slice),
                access_name(*element),
                stride_bytes
            )?;
            match bounds {
                VirIndexBounds::Array { length } => write!(output, "array({length})")?,
                VirIndexBounds::Slice { length } => {
                    write!(output, "slice({})", value_name(*length))?;
                }
            }
        }
        VirInstruction::SliceAddress {
            pointer_result,
            length_result,
            base,
            start,
            end,
            source,
            slice,
            element,
            stride_bytes,
            bounds,
        } => {
            write_value_declaration(output, *pointer_result)?;
            write!(output, ", ")?;
            write_value_declaration(output, *length_result)?;
            write!(
                output,
                " = slice.address {} start {} end {} source {} slice {} element {} stride {} bounds ",
                value_name(*base),
                value_name(*start),
                value_name(*end),
                access_name(*source),
                access_name(*slice),
                access_name(*element),
                stride_bytes
            )?;
            match bounds {
                VirIndexBounds::Array { length } => write!(output, "array({length})")?,
                VirIndexBounds::Slice { length } => {
                    write!(output, "slice({})", value_name(*length))?;
                }
            }
        }
        VirInstruction::RawAddress {
            result,
            base,
            source_permission,
            raw_type,
        } => {
            write!(
                output,
                "{} = raw_address {} using {} as {}",
                value_name(result.id),
                value_name(*base),
                value_name(*source_permission),
                access_name(*raw_type)
            )?;
        }
        VirInstruction::PointerOffset {
            result,
            base,
            delta_bytes,
        } => {
            write_value_declaration(output, *result)?;
            write!(
                output,
                " = offset {}, {}",
                value_name(*base),
                value_name(*delta_bytes)
            )?;
        }
        VirInstruction::Free {
            pointer,
            permission,
        } => write!(
            output,
            "free {} using {}",
            value_name(*pointer),
            value_name(*permission)
        )?,
        VirInstruction::PermissionSplit {
            left_result,
            right_result,
            source,
            split_at_bytes,
        } => {
            write_value_declaration(output, *left_result)?;
            write!(output, ", ")?;
            write_value_declaration(output, *right_result)?;
            write!(
                output,
                " = permission.split {} at {}",
                value_name(*source),
                value_name(*split_at_bytes)
            )?;
        }
        VirInstruction::PermissionJoin {
            result,
            left,
            right,
        } => {
            write_value_declaration(output, *result)?;
            write!(
                output,
                " = permission.join {}, {}",
                value_name(*left),
                value_name(*right)
            )?;
        }
        VirInstruction::PermissionMove { result, source } => {
            write_value_declaration(output, *result)?;
            write!(output, " = permission.move {}", value_name(*source))?;
        }
        VirInstruction::LoanBegin {
            effect,
            reference_result,
            permission_result,
        } => {
            write_loan_results(output, *reference_result, *permission_result)?;
            write!(output, " = loan.begin ")?;
            write_loan_effect(output, *effect)?;
        }
        VirInstruction::LoanAliasShared {
            effect,
            reference_result,
            permission_result,
        } => {
            write_loan_results(output, *reference_result, *permission_result)?;
            write!(output, " = loan.alias-shared ")?;
            write_loan_effect(output, *effect)?;
        }
        VirInstruction::LoanReborrow {
            effect,
            reference_result,
            permission_result,
        } => {
            write_loan_results(output, *reference_result, *permission_result)?;
            write!(output, " = loan.reborrow ")?;
            write_loan_effect(output, *effect)?;
        }
        VirInstruction::LoanEnd { effect } => {
            write!(output, "loan.end ")?;
            write_loan_effect(output, *effect)?;
        }
        VirInstruction::LoanAliasAuthority {
            effect,
            reference_result,
            permission_result,
        } => {
            write_loan_results(output, *reference_result, *permission_result)?;
            write!(output, " = loan.alias-authority ")?;
            write_loan_authority_effect(output, *effect)?;
        }
        VirInstruction::LoanEndAuthority { effect } => {
            write!(output, "loan.end-authority ")?;
            write_loan_authority_effect(output, *effect)?;
        }
        VirInstruction::LoanReborrowAuthority {
            loan,
            region,
            effect,
            reference_result,
            permission_result,
        } => {
            write_loan_results(output, *reference_result, *permission_result)?;
            write!(
                output,
                " = loan.reborrow-authority l{} region{} ",
                loan.get(),
                region.get()
            )?;
            write_loan_authority_effect(output, *effect)?;
        }
        VirInstruction::Check { condition } => {
            write!(output, "check {}", value_name(*condition))?;
        }
        VirInstruction::Call {
            results,
            target,
            arguments,
        } => {
            if !results.is_empty() {
                write_value_declarations(output, results)?;
                write!(output, " = ")?;
            }
            write!(output, "call ")?;
            write_quoted(output, &target.symbol)?;
            write!(output, " contract contract{} (", target.contract.get())?;
            write_value_ids(output, arguments)?;
            write!(output, ") : ")?;
            write_signature(output, &target.signature)?;
            if target.abi.is_some() {
                write!(output, " abi canonical")?;
            }
        }
    }
    write!(output, " ")?;
    write_span(output, spanned.source_span)?;
    writeln!(output)
}

fn write_loan_authority_effect(
    output: &mut String,
    effect: super::VirLoanAuthorityEffect,
) -> fmt::Result {
    write!(
        output,
        "source {} permission {} reference {} origin origin{}",
        value_name(effect.source_pointer),
        value_name(effect.source_permission),
        access_name(effect.reference),
        effect.origin.get()
    )
}

fn write_loan_results(
    output: &mut String,
    reference_result: VirValue,
    permission_result: VirValue,
) -> fmt::Result {
    write_value_declaration(output, reference_result)?;
    write!(output, ", ")?;
    write_value_declaration(output, permission_result)
}

fn write_loan_effect(output: &mut String, effect: VirLoanEffect) -> fmt::Result {
    write!(
        output,
        "loan{} {} region bregion{} parent ",
        effect.loan.get(),
        match effect.kind {
            VirLoanKind::Shared => "shared",
            VirLoanKind::Mutable => "mutable",
        },
        effect.region.get()
    )?;
    match effect.parent {
        Some(parent) => write!(output, "loan{}", parent.get())?,
        None => write!(output, "none")?,
    }
    write!(
        output,
        " from {} using {} reference {} range [{},{}) origin origin{}",
        value_name(effect.source_pointer),
        value_name(effect.source_permission),
        access_name(effect.reference),
        effect.range.start_bytes,
        effect.range.end_bytes,
        effect.origin.get()
    )
}

fn dump_memory_schema(output: &mut String, memory: &VirMemorySchema) -> fmt::Result {
    let endianness = match memory.target.endianness {
        VirEndianness::Little => "little",
        VirEndianness::Big => "big",
    };
    writeln!(
        output,
        "target {endianness} pointer {}/{} usize {}/{}",
        memory.target.pointer_size_bytes,
        memory.target.pointer_alignment,
        memory.target.usize_size_bytes,
        memory.target.usize_alignment
    )?;
    for ty in &memory.types {
        write!(output, "type type{} = ", ty.id.get())?;
        dump_memory_type_kind(output, &ty.kind)?;
        if let Some(capability) = memory.type_capabilities(ty.id) {
            writeln!(
                output,
                " layout layout{} capabilities {}/{}/{}/{}",
                ty.layout.get(),
                value_capability_name(capability.value),
                drop_capability_name(capability.drop),
                if capability.contains_resource {
                    "resource"
                } else {
                    "resource-free"
                },
                size_capability_name(capability.size)
            )?;
        } else {
            writeln!(
                output,
                " layout layout{} capabilities <missing>",
                ty.layout.get()
            )?;
        }
    }
    for field in &memory.fields {
        writeln!(
            output,
            "field field{} owner type{} type type{}",
            field.id.get(),
            field.owner.get(),
            field.ty.get()
        )?;
    }
    for variant in &memory.variants {
        write!(
            output,
            "variant variant{} owner type{} discriminant {} fields [",
            variant.id.get(),
            variant.owner.get(),
            variant.discriminant
        )?;
        for (index, field) in variant.fields.iter().enumerate() {
            if index != 0 {
                write!(output, ", ")?;
            }
            write!(output, "field{}", field.get())?;
        }
        writeln!(output, "]")?;
    }
    for layout in &memory.layouts {
        write!(
            output,
            "layout layout{} type type{} size {} align {} abi {} fields [",
            layout.id.get(),
            layout.ty.get(),
            layout.size_bytes,
            layout.alignment,
            abi_name(layout.abi)
        )?;
        for (index, field) in layout.fields.iter().enumerate() {
            if index != 0 {
                write!(output, ", ")?;
            }
            write!(output, "field{}@{}", field.field.get(), field.offset_bytes)?;
        }
        write!(output, "]")?;
        if let Some(variants) = &layout.variants {
            write!(
                output,
                " variants tag {}/{} [",
                variants.tag_size_bytes, variants.tag_alignment
            )?;
            for (index, case) in variants.cases.iter().enumerate() {
                if index != 0 {
                    write!(output, ", ")?;
                }
                write!(
                    output,
                    "variant{}@{}(",
                    case.variant.get(),
                    case.payload_offset_bytes
                )?;
                for (field_index, field) in case.fields.iter().enumerate() {
                    if field_index != 0 {
                        write!(output, ", ")?;
                    }
                    write!(output, "field{}@{}", field.field.get(), field.offset_bytes)?;
                }
                write!(output, ")")?;
            }
            write!(output, "]")?;
        }
        writeln!(output)?;
    }
    Ok(())
}

fn dump_memory_type_kind(output: &mut String, kind: &VirMemoryTypeKind) -> fmt::Result {
    match kind {
        VirMemoryTypeKind::Unit => write!(output, "unit"),
        VirMemoryTypeKind::Bool => write!(output, "bool"),
        VirMemoryTypeKind::Integer(integer) => write!(output, "{}", integer_name(*integer)),
        VirMemoryTypeKind::Pointer {
            pointee,
            kind,
            mutability,
        } => write!(
            output,
            "{} {} pointer<type{}>",
            pointer_kind_name(*kind),
            mutability_name(*mutability),
            pointee.get()
        ),
        VirMemoryTypeKind::Array { element, length } => {
            write!(output, "array<type{}; {}>", element.get(), length)
        }
        VirMemoryTypeKind::Slice {
            element,
            mutability,
        } => write!(
            output,
            "slice<{} type{}>",
            mutability_name(*mutability),
            element.get()
        ),
        VirMemoryTypeKind::Tuple(elements) => {
            write!(output, "tuple<")?;
            for (index, element) in elements.iter().enumerate() {
                if index != 0 {
                    write!(output, ", ")?;
                }
                write!(output, "type{}", element.get())?;
            }
            write!(output, ">")
        }
        VirMemoryTypeKind::Struct { fields } => write_id_list(
            output,
            "struct",
            fields.iter().map(|id| ("field", id.get())),
        ),
        VirMemoryTypeKind::Enum { variants } => write_id_list(
            output,
            "enum",
            variants.iter().map(|id| ("variant", id.get())),
        ),
        VirMemoryTypeKind::Never => write!(output, "never"),
    }
}

fn write_id_list(
    output: &mut String,
    name: &str,
    ids: impl Iterator<Item = (&'static str, u32)>,
) -> fmt::Result {
    write!(output, "{name}<")?;
    for (index, (prefix, id)) in ids.enumerate() {
        if index != 0 {
            write!(output, ", ")?;
        }
        write!(output, "{prefix}{id}")?;
    }
    write!(output, ">")
}

fn access_name(access: VirMemoryAccess) -> String {
    format!("type{}/layout{}", access.ty.get(), access.layout.get())
}

const fn abi_name(abi: VirAbiClass) -> &'static str {
    match abi {
        VirAbiClass::Ignore => "ignore",
        VirAbiClass::Scalar => "scalar",
        VirAbiClass::ScalarPair => "scalar-pair",
        VirAbiClass::Aggregate => "aggregate",
    }
}

const fn integer_name(integer: VirIntegerType) -> &'static str {
    match integer {
        VirIntegerType::U8 => "u8",
        VirIntegerType::U16 => "u16",
        VirIntegerType::U32 => "u32",
        VirIntegerType::U64 => "u64",
        VirIntegerType::U128 => "u128",
        VirIntegerType::Usize => "usize",
        VirIntegerType::I8 => "i8",
        VirIntegerType::I16 => "i16",
        VirIntegerType::I32 => "i32",
        VirIntegerType::I64 => "i64",
        VirIntegerType::I128 => "i128",
        VirIntegerType::Isize => "isize",
    }
}

const fn mutability_name(mutability: VirMutability) -> &'static str {
    match mutability {
        VirMutability::Const => "const",
        VirMutability::Mutable => "mutable",
    }
}

const fn pointer_kind_name(kind: VirPointerKind) -> &'static str {
    match kind {
        VirPointerKind::Own => "own",
        VirPointerKind::Raw => "raw",
        VirPointerKind::Reference => "reference",
    }
}

const fn value_capability_name(capability: crate::ValueCapability) -> &'static str {
    match capability {
        crate::ValueCapability::Copy => "copy",
        crate::ValueCapability::MoveOnly => "move-only",
    }
}

const fn drop_capability_name(capability: crate::DropCapability) -> &'static str {
    match capability {
        crate::DropCapability::TrivialDrop => "trivial-drop",
        crate::DropCapability::BuiltinDrop => "builtin-drop",
        crate::DropCapability::UserDropGated => "user-drop-gated",
    }
}

const fn size_capability_name(capability: crate::SizeCapability) -> &'static str {
    match capability {
        crate::SizeCapability::Sized => "sized",
        crate::SizeCapability::Unsized => "unsized",
    }
}

const fn interface_transfer_name(transfer: super::VirInterfaceTransfer) -> &'static str {
    match transfer {
        super::VirInterfaceTransfer::Opaque => "opaque",
        super::VirInterfaceTransfer::Ignore => "ignore",
        super::VirInterfaceTransfer::Copy => "copy",
        super::VirInterfaceTransfer::Move => "move",
        super::VirInterfaceTransfer::BorrowShared => "borrow-shared",
        super::VirInterfaceTransfer::BorrowMutable => "borrow-mutable",
    }
}

const fn interface_storage_name(storage: super::VirInterfaceStorage) -> &'static str {
    match storage {
        super::VirInterfaceStorage::Opaque => "opaque",
        super::VirInterfaceStorage::None => "none",
        super::VirInterfaceStorage::Direct => "direct",
        super::VirInterfaceStorage::Indirect => "indirect",
    }
}

fn dump_terminator(output: &mut String, spanned: &SpannedVirTerminator) -> fmt::Result {
    write!(output, "    ")?;
    match &spanned.terminator {
        VirTerminator::Jump { target } => {
            write!(output, "jump ")?;
            write_block_target(output, target)?;
        }
        VirTerminator::Branch {
            condition,
            then_target,
            else_target,
        } => {
            write!(output, "branch {} then ", value_name(*condition))?;
            write_block_target(output, then_target)?;
            write!(output, " else ")?;
            write_block_target(output, else_target)?;
        }
        VirTerminator::Return { values } => {
            write!(output, "return (")?;
            write_value_ids(output, values)?;
            write!(output, ")")?;
        }
    }
    write!(output, " ")?;
    write_span(output, spanned.source_span)?;
    writeln!(output)
}

fn write_signature(output: &mut String, signature: &VirSignature) -> fmt::Result {
    write!(output, "(")?;
    write_types(output, &signature.parameters)?;
    write!(output, ") -> (")?;
    write_types(output, &signature.results)?;
    write!(output, ")")
}

fn write_types(output: &mut String, types: &[VirType]) -> fmt::Result {
    for (index, ty) in types.iter().enumerate() {
        if index != 0 {
            write!(output, ", ")?;
        }
        write_type(output, *ty)?;
    }
    Ok(())
}

fn write_type(output: &mut String, ty: VirType) -> fmt::Result {
    match ty {
        VirType::U64 => write!(output, "u64"),
        VirType::Bool => write!(output, "bool"),
        VirType::Pointer { access } => write!(output, "ptr<{}>", access_name(access)),
        VirType::Permission => write!(output, "permission"),
    }
}

fn write_value_declarations(output: &mut String, values: &[VirValue]) -> fmt::Result {
    for (index, value) in values.iter().enumerate() {
        if index != 0 {
            write!(output, ", ")?;
        }
        write_value_declaration(output, *value)?;
    }
    Ok(())
}

fn write_value_declaration(output: &mut String, value: VirValue) -> fmt::Result {
    write!(output, "{}: ", value_name(value.id))?;
    write_type(output, value.ty)
}

fn write_value_ids(output: &mut String, values: &[VirValueId]) -> fmt::Result {
    for (index, value) in values.iter().enumerate() {
        if index != 0 {
            write!(output, ", ")?;
        }
        write!(output, "{}", value_name(*value))?;
    }
    Ok(())
}

fn write_block_target(output: &mut String, target: &VirBlockTarget) -> fmt::Result {
    write!(output, "bb{}(", target.block.get())?;
    write_value_ids(output, &target.arguments)?;
    write!(output, ")")
}

fn write_span(output: &mut String, span: ByteSpan) -> fmt::Result {
    write!(output, "@{}..{}", span.start(), span.end())
}

fn write_quoted(output: &mut String, text: &str) -> fmt::Result {
    write!(output, "\"")?;
    for character in text.chars() {
        for escaped in character.escape_default() {
            output.write_char(escaped)?;
        }
    }
    write!(output, "\"")
}

fn value_name(value: VirValueId) -> String {
    format!("%{}", value.get())
}

const fn object_destination_mode_name(mode: VirObjectDestinationMode) -> &'static str {
    match mode {
        VirObjectDestinationMode::Initialize => "init",
        VirObjectDestinationMode::Replace => "replace",
    }
}

const fn object_source_mode_name(mode: VirObjectSourceMode) -> &'static str {
    match mode {
        VirObjectSourceMode::Copy => "copy",
        VirObjectSourceMode::Move => "move",
    }
}

const fn predicate_name(predicate: VirIntegerPredicate) -> &'static str {
    match predicate {
        VirIntegerPredicate::Equal => "eq",
        VirIntegerPredicate::NotEqual => "ne",
        VirIntegerPredicate::LessThan => "ult",
        VirIntegerPredicate::LessOrEqual => "ule",
        VirIntegerPredicate::GreaterThan => "ugt",
        VirIntegerPredicate::GreaterOrEqual => "uge",
    }
}
