use nera::session::{CompilerSession, SessionRequest};
use nera::source::{SourceDatabase, SourceInput};
use nera::verification::render_text;
use nera::{
    BorrowAccess, FrontendStatus, InterfaceArtifact, InterfaceArtifactError,
    InterfaceArtifactVersion, InterfaceDeclarationIdentity, InterfaceMemoryRole,
    InterfaceNominalKind, InterfacePrecondition, InterfaceType, SourceFile,
};

const APP: &str = include_str!("../spec/cases/modules/generic-app.nera");
const VALUES: &str = include_str!("../spec/cases/modules/generic-values.nera");
const BORROW: &str = include_str!("../spec/cases/modules/generic-borrow.nera");

fn session(files: &[(&str, &str)], request: SessionRequest) -> CompilerSession {
    let sources = files
        .iter()
        .map(|(name, text)| {
            SourceInput::new(*name, SourceFile::from_text(format!("{name}.nera"), text))
        })
        .collect();
    CompilerSession::modules(SourceDatabase::new(sources).unwrap(), request, "app::main").unwrap()
}

fn artifact(files: &[(&str, &str)]) -> (nera::session::SourceAnalysis, InterfaceArtifact) {
    let analysis = session(files, Default::default()).analyze("app").unwrap();
    assert_eq!(
        analysis.frontend().status(),
        FrontendStatus::AcceptedProposal
    );
    let artifact = analysis.interface_artifact().unwrap();
    (analysis, artifact)
}

#[test]
fn projection_uses_semantic_module_declaration_and_instance_identities() {
    let (analysis, artifact) = artifact(&[("app", APP), ("values", VALUES), ("borrow", BORROW)]);
    assert_eq!(artifact.version(), InterfaceArtifactVersion::V1);
    assert_eq!(artifact.input().capability_profile, "system-v1");
    assert_eq!(artifact.input().hir_schema, 12);
    assert_eq!(artifact.input().vir_schema, 18);
    assert_eq!(artifact.input().sources.len(), 3);
    assert!(artifact.matches_input(analysis.input()));
    assert!(artifact.matches_analysis(&analysis));

    let paths: Vec<_> = artifact
        .modules()
        .iter()
        .map(|module| module.identity.path.join("::"))
        .collect();
    assert_eq!(paths, ["app", "borrow", "values"]);
    assert_eq!(artifact.instances().len(), 3);
    assert!(
        artifact
            .instances()
            .iter()
            .all(|instance| !instance.definition.contains('$'))
    );

    let hold = artifact
        .modules()
        .iter()
        .flat_map(|module| &module.functions)
        .find(|function| {
            matches!(
                &function.identity,
                InterfaceDeclarationIdentity::ConcreteInstance(instance)
                    if instance.definition == "borrow::hold"
            )
        })
        .unwrap();
    let relation = hold.borrow_result.unwrap();
    assert_eq!(relation.parameter, 0);
    assert_eq!(relation.access, BorrowAccess::Shared);
    assert!(matches!(
        hold.parameters[0],
        InterfaceType::Reference { .. }
    ));
    assert_eq!(
        hold.effects.parameters[0].memory,
        InterfaceMemoryRole::SharedBorrow
    );
    assert!(
        hold.effects
            .preconditions
            .contains(&InterfacePrecondition::LiveBorrow {
                parameter: 0,
                mutability: nera::HirMutability::Const,
            })
    );

    let buffer = artifact
        .modules()
        .iter()
        .flat_map(|module| &module.types)
        .find(|definition| {
            matches!(
                &definition.identity,
                InterfaceDeclarationIdentity::ConcreteInstance(instance)
                    if instance.definition == "values::Buffer"
            )
        })
        .unwrap();
    let InterfaceNominalKind::Struct { fields } = &buffer.kind else {
        panic!("Buffer instance must remain a struct");
    };
    assert_eq!(fields[0].name, "values");
    assert!(matches!(
        fields[0].ty,
        InterfaceType::Array { length: 2, .. }
    ));
}

#[test]
fn guarded_borrow_worlds_are_projected_without_region_table_ids() {
    let source = "module app;
        pub fn choose(flag:bool,left:&u64,right:&u64)->&u64 {
            if flag { return left; } else { return right; }
        }
        fn main()->u64 { let a=20;let b=22;let r=choose(false,&a,&b);return *r; }";
    let (_, artifact) = artifact(&[("app", source)]);
    let choose = &artifact.modules()[0].functions[0];
    assert!(choose.borrow_result.is_none());
    assert_eq!(choose.borrow_result_alternatives.len(), 2);
    assert!(
        choose
            .borrow_result_alternatives
            .iter()
            .any(|alternative| alternative.relation.parameter == 1)
    );
    assert!(
        choose
            .borrow_result_alternatives
            .iter()
            .any(|alternative| alternative.relation.parameter == 2)
    );
}

#[test]
fn source_order_and_dense_assignment_do_not_change_the_projection() {
    let (_, first) = artifact(&[("app", APP), ("values", VALUES), ("borrow", BORROW)]);
    let (_, reordered) = artifact(&[("borrow", BORROW), ("app", APP), ("values", VALUES)]);
    assert_eq!(first, reordered);
}

#[test]
fn explicit_module_mapping_is_part_of_input_and_semantic_identity() {
    let app = "module app; use lib::value; pub fn main()->u64{return value();}";
    let library = "module lib; pub fn value()->u64{return 42;}";
    let (_, original) = artifact(&[("app", app), ("lib", library)]);

    let remapped_app = app.replace("lib::value", "util::value");
    let remapped_library = library.replace("module lib", "module util");
    let (remapped_analysis, remapped) =
        artifact(&[("app", &remapped_app), ("util", &remapped_library)]);

    let original_modules: Vec<_> = original
        .modules()
        .iter()
        .map(|module| module.identity.path.join("::"))
        .collect();
    let remapped_modules: Vec<_> = remapped
        .modules()
        .iter()
        .map(|module| module.identity.path.join("::"))
        .collect();
    assert_eq!(original_modules, ["app", "lib"]);
    assert_eq!(remapped_modules, ["app", "util"]);
    assert_ne!(original.input(), remapped.input());
    assert_ne!(original.modules(), remapped.modules());
    assert!(!original.matches_analysis(&remapped_analysis));
}

#[test]
fn exact_input_binding_and_semantic_interface_mutations_are_distinct() {
    let (original_analysis, original) =
        artifact(&[("app", APP), ("values", VALUES), ("borrow", BORROW)]);

    // Private implementation bytes change, while the projected public interface does not.
    let private_change = APP.replace("21", "20");
    let (private_analysis, private) = artifact(&[
        ("app", &private_change),
        ("values", VALUES),
        ("borrow", BORROW),
    ]);
    assert_eq!(original.modules(), private.modules());
    assert_ne!(original.input(), private.input());
    assert!(!original.matches_input(private_analysis.input()));
    assert!(!original.matches_analysis(&private_analysis));

    // A concrete instance argument changes semantic identity and public layout.
    let app_three = APP.replace("1 + 1", "3").replace("[u64; 2]", "[u64; 3]");
    let (_, different_instance) =
        artifact(&[("app", &app_three), ("values", VALUES), ("borrow", BORROW)]);
    assert_ne!(original.instances(), different_instance.instances());
    assert_ne!(original.modules(), different_instance.modules());

    // A public representation change is reflected independently of dense type IDs.
    let renamed_values = VALUES.replace("values:", "items:");
    let renamed_app = APP.replace("buffer.values", "buffer.items");
    let (_, different_field) = artifact(&[
        ("app", &renamed_app),
        ("values", &renamed_values),
        ("borrow", BORROW),
    ]);
    assert_ne!(original.modules(), different_field.modules());
    assert!(original.matches_analysis(&original_analysis));
}

#[test]
fn analysis_budget_is_part_of_identity_but_not_semantic_projection() {
    let (_, normal) = artifact(&[("app", APP), ("values", VALUES), ("borrow", BORROW)]);
    let mut analysis_config = nera::CfgAnalysisConfig::default();
    analysis_config.max_block_visits += 1;
    let requested = SessionRequest {
        analysis: analysis_config,
        ..Default::default()
    };
    let changed_analysis = session(
        &[("app", APP), ("values", VALUES), ("borrow", BORROW)],
        requested,
    )
    .analyze("app")
    .unwrap();
    let changed = changed_analysis.interface_artifact().unwrap();
    assert_eq!(normal.modules(), changed.modules());
    assert_ne!(normal.input(), changed.input());
    assert!(!normal.matches_input(changed_analysis.input()));
}

#[test]
fn artifact_creation_is_not_a_memory_checked_conclusion() {
    let bad = "module app; pub fn main()->u64{let p=alloc<u64>(1);free(p);return *p;}";
    let compiler = session(&[("app", bad)], Default::default());
    let analysis = compiler.analyze("app").unwrap();
    assert_eq!(
        analysis.frontend().status(),
        FrontendStatus::AcceptedProposal
    );
    let artifact = analysis.interface_artifact().unwrap();
    assert_eq!(artifact.modules()[0].functions.len(), 1);
    let preview = compiler.verify("app").unwrap();
    assert!(
        !preview.is_checked(),
        "{}",
        render_text(&preview, Default::default())
    );

    let invalid = session(&[("app", "module app; fn main( {")], Default::default())
        .analyze("app")
        .unwrap();
    assert_eq!(
        invalid.interface_artifact(),
        Err(InterfaceArtifactError::FrontendNotAccepted)
    );
}
