use super::*;
use crate::{HirSpecLocation, HirSpecSnapshot, HirStatementKind};

#[test]
fn local_prove_anchors_and_snapshot_scope_are_independently_validated() {
    let base = accepted_program(
        "fn main()->u64 { let x=1; assert x==1; { let y=2; assert y==2; } return x; }",
    );
    for mutation in 0..4 {
        let mut tables = program_tables(&base);
        match mutation {
            0 => {
                tables.functions[0]
                    .body
                    .as_mut()
                    .unwrap()
                    .root
                    .statements
                    .remove(1);
            }
            1 => {
                let body = tables.functions[0].body.as_mut().unwrap();
                let duplicate = body.root.statements[1].clone();
                body.root.statements.insert(2, duplicate);
            }
            2 => {
                // A later inner-scope local is a real, correctly typed table
                // entry, but cannot be observed at the first assertion.
                let term = tables
                    .specs
                    .terms
                    .iter_mut()
                    .find(|t| matches!(t.kind, HirSpecTermKind::Snapshot(_)))
                    .unwrap();
                term.kind = HirSpecTermKind::Snapshot(HirSpecSnapshot::Local {
                    function: HirFunctionId::new(0),
                    local: crate::HirLocalId::new(1),
                });
            }
            _ => {
                let location = HirSpecLocation::FunctionResult {
                    function: HirFunctionId::new(0),
                };
                tables.specs.proves[0].location = location;
                tables.specs.clauses[0].location = location;
            }
        }
        assert!(hir_from_tables(tables).is_err(), "mutation {mutation}");
    }
    assert!(matches!(
        base.functions()[0].body().unwrap().root.statements[1].kind,
        HirStatementKind::Prove { .. }
    ));
}

#[test]
fn logical_snapshot_unavailable_without_runtime_evaluation_is_explicitly_gated() {
    // x is object-backed because its address escapes to a reference. Spec
    // must not insert a Load to manufacture a scalar snapshot.
    let source = "fn main()->u64 { let mut x=7; let p=&x; assert x==7; return *p; }";
    let output = analyze(&SourceFile::from_text("heap-snapshot.nera", source));
    assert!(output.vir().is_none());
    assert!(
        output
            .issues()
            .iter()
            .any(|i| i.diagnostic.message().contains("object-backed"))
    );
}
