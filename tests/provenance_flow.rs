#[path = "support/frontend_checks.rs"]
mod frontend_checks;

use nera::{CfgAnalysisConfig, interpret, verify_program};

#[test]
fn cfg_loops_and_identity_views_keep_their_source() {
    let source = include_str!("../spec/cases/verify/provenance-flow.nera");
    for condition in ["true", "false"] {
        frontend_checks::checked(
            "provenance-flow.nera",
            &source.replace("return true;", &format!("return {condition};")),
            42,
        );
    }
}

#[test]
fn parameter_relative_paths_support_derivation_without_inventing_root_identity() {
    for source in [
        "fn main()->u64 { let a=[1,2]; return check(&a[1]); } fn check(p:&u64)->u64 { let r=identity(p); let x=&raw *p; let y=&raw *r; if x==y { return 42; } return 0; } fn identity(p:&u64)->&u64 { return p; }",
        "fn main() -> u64 { let a=[1,2]; return check(&a[1]); } fn check(p: &u64) -> u64 { let x=&raw *p; let y=x+8; if ptr_byte_distance(x,y)==8usize { return 42; } return 0; }",
        "struct Pair { a:u64, b:u64, } fn main() -> u64 { let p=Pair { a:1,b:2 }; return check(&p); } fn check(p: &Pair) -> u64 { let x=&raw p.a; let y=&raw p.a; if x==y { return 42; } return 0; }",
        "fn main() -> u64 { let a=[1,2]; let r=identity(&a[1],0); let x=&raw a[1]; let y=&raw *r; if x==y { return 42; } return 0; } fn identity(p:&u64,n:u64)->&u64 { if n==2 { return p; } return identity(p,n+1); }",
        "fn main() -> u64 { let mut a=1; let r=identity(&mut a); *r=42; let x=&raw *r; if x==x { return *r; } return 0; } fn identity(p:&mut u64)->&mut u64 { return p; }",
        "fn main() -> u64 { let a=[1,2,3]; return check(&a[..]); } fn check(p:&[u64])->u64 { if len(p)>1usize { let a=&p[0..2]; let b=&p[0..2]; let x=&raw a[0]; let y=&raw b[1]; if x<y { return 42; } } return 0; }",
    ] {
        frontend_checks::checked("parameter-paths.nera", source, 42);
    }
}

#[test]
fn local_object_payload_moves_and_copies_preserve_pointer_metadata() {
    for source in [
        "struct Holder { r: &u64, } fn main() -> u64 { let a=[1,2]; let h=Holder { r:&a[1] }; let copy=h; let r=copy.r; let x=&raw a[1]; let y=&raw *r; if x==y { return 42; } return 0; }",
        "struct Holder { p: Own<u64>, q: Own<u64>, } fn main() -> u64 { let p=alloc<u64>(1); *p=20; let old=&raw *p; let q=alloc<u64>(1); *q=22; let mut h=Holder { p:p, q:q }; let moved=h.p; let current=&raw *moved; let replacement=alloc<u64>(1); *replacement=1; h.p=replacement; let other=h.q; if old==current { return *moved + *other; } return 0; }",
    ] {
        frontend_checks::checked("payload-provenance.nera", source, 42);
    }
}

#[test]
fn different_origins_and_opaque_owner_returns_do_not_gain_identity() {
    for source in [
        "fn main() -> u64 { let a=1; let b=2; let x=&raw a; let mut p=x; if choose() { p=&raw b; } if p==x { return 42; } return 0; } fn choose()->bool { return true; }",
        // Recursive replacement releases the old instance; a proved identity
        // recursion is now positive coverage in summary_recursive.
        "fn main() -> u64 { let p=alloc<u64>(1); *p=42; let old=&raw *p; let returned=replace(p,false); let new=&raw *returned; if old==new { return 42; } return 0; } fn replace(p:Own<u64>,stop:bool)->Own<u64> { if stop { free(p); let q=alloc<u64>(1); *q=42; return q; } return replace(p,true); }",
        // Same concrete selection, but the parameter's incoming arithmetic
        // domain is not assumed to equal a newly constructed view domain.
        "fn main()->u64 { let a=[1,2]; return check(&a[..]); } fn check(p:&[u64])->u64 { if len(p)>0usize { let x=&raw p[0]; let s=&p[..]; let y=&raw s[0]; if x==y { return 42; } } return 0; }",
    ] {
        let output = frontend_checks::accepted("unknown-origin.nera", source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        assert!(
            !verify_program(&resolved, CfgAnalysisConfig::default())
                .unwrap()
                .is_memory_checked_core0(),
            "{source}"
        );
    }
}

#[test]
fn incoming_parameter_domain_is_not_the_pointee_object_domain() {
    use nera::*;
    let output = frontend_checks::accepted(
        "parameter-domain.nera",
        "fn main()->u64 { let a=[1,2]; return check(&a[0]); } fn check(p:&u64)->u64 { let x=&raw *p; let y=x+0; if x==y { return 42; } return 0; }",
    );
    let mut unit = output.vir().unwrap().as_unit().clone();
    let instruction = unit.runtime.functions[1]
        .blocks
        .iter_mut()
        .flat_map(|b| &mut b.instructions)
        .find(|i| matches!(i.instruction, VirInstruction::PointerOffset { .. }))
        .unwrap();
    let VirInstruction::PointerOffset { result, base, .. } = instruction.instruction else {
        unreachable!()
    };
    let VirType::Pointer { access } = result.ty else {
        unreachable!()
    };
    instruction.instruction = VirInstruction::ObjectLeafAddress {
        result,
        base,
        owner: access,
        leaf: access,
        offset_bytes: 0,
    };
    let validated = unit.into_validated().unwrap();
    let resolved = validated.resolve().unwrap();
    let report = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
    assert!(!report.is_memory_checked_core0());
    assert!(
        report
            .functions()
            .values()
            .flat_map(|f| f.cfg().obligations())
            .any(|o| matches!(
                o.obligation().kind(),
                ResourceObligationKind::PointerCompatibleDomain { .. }
            ) && o.obligation().status() == ObligationStatus::Unknown)
    );
    assert!(matches!(
        interpret(resolved.runtime()).unwrap_err().kind(),
        VirExecutionErrorKind::PointerRelationIncompatible
    ));
}

#[test]
fn parameter_anchors_are_scoped_and_selection_does_not_change_object_identity() {
    use nera::*;
    let access = VirMemoryAccess::core_u64();
    let a = VirPointerPaths::parameter(access, VirFunctionId::new(0), 0);
    let b = VirPointerPaths::parameter(access, VirFunctionId::new(1), 0);
    let c = VirPointerPaths::parameter(access, VirFunctionId::new(0), 1);
    assert_ne!(a, b);
    assert_ne!(a, c);
    assert_ne!(a.object, a.domain);
    assert_ne!(a, VirPointerPaths::root(access));
    assert_eq!(a.object, a.selected().object);
    assert_ne!(a.domain, a.selected().domain);
    assert_eq!(a.selected(), a.selected().selected());
    assert_eq!(a.join(b), VirPointerPaths::default());
}

#[test]
fn transferred_owners_do_not_leave_a_live_promise_for_old_raw_aliases() {
    for source in [
        "fn main() -> u64 { let p=alloc<u64>(1); *p=42; let old=&raw *p; consume(p); if old==old { return 42; } return 0; } fn consume(p: Own<u64>) { free(p); return; }",
        "struct Box { p: Own<u64>, } fn main() -> u64 { let p=alloc<u64>(1); *p=42; let old=&raw *p; let b=Box { p: p }; consume(b); if old==old { return 42; } return 0; } fn consume(b: Box) { return; }",
    ] {
        let output = frontend_checks::accepted("transferred-instance.nera", source);
        let resolved = output.vir().unwrap().resolve().unwrap();
        let report = verify_program(&resolved, CfgAnalysisConfig::default()).unwrap();
        assert!(!report.is_memory_checked_core0(), "{source}");
        assert!(matches!(
            interpret(resolved.runtime()).unwrap_err().kind(),
            nera::VirExecutionErrorKind::UseAfterFree { .. }
        ));
    }
}
