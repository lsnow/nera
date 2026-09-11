use nera::backend::{
    GnuAssemblySyntax, NativeEndianness, NativeObjectFormat, X86_64_UNKNOWN_LINUX_GNU,
    X86_64AbiErrorKind, X86_64AbiParameterLocation, X86_64AbiResultLocation,
    X86_64CallerStackLocation, X86_64EntryResult, X86_64IntegerRegister, X86_64IsaBaseline,
    X86_64LinuxTarget, X86_64RuntimeType,
};
use nera::{VirFunctionId, VirSignature, VirType};

#[test]
fn target_profile_is_frozen_and_selected_by_exact_triple() {
    let target = X86_64_UNKNOWN_LINUX_GNU;

    assert_eq!(target.triple(), "x86_64-unknown-linux-gnu");
    assert_eq!(target.to_string(), target.triple());
    assert_eq!(target.endianness(), NativeEndianness::Little);
    assert_eq!(target.object_format(), NativeObjectFormat::Elf64);
    assert_eq!(target.assembly_syntax(), GnuAssemblySyntax::IntelNoPrefix);
    assert_eq!(target.isa_baseline(), X86_64IsaBaseline::V1);
    assert_eq!(target.pointer_size_bytes(), 8);
    assert_eq!(target.runtime_word_size_bytes(), 8);
    assert_eq!(target.call_stack_alignment_bytes(), 16);
    assert!(!target.uses_red_zone());
    assert!(target.emits_position_independent_executables());
    assert_eq!(
        target.integer_argument_registers(),
        &[
            X86_64IntegerRegister::Rdi,
            X86_64IntegerRegister::Rsi,
            X86_64IntegerRegister::Rdx,
            X86_64IntegerRegister::Rcx,
            X86_64IntegerRegister::R8,
            X86_64IntegerRegister::R9,
        ]
    );
    assert_eq!(
        target.caller_saved_registers(),
        &[
            X86_64IntegerRegister::Rax,
            X86_64IntegerRegister::Rcx,
            X86_64IntegerRegister::Rdx,
            X86_64IntegerRegister::Rsi,
            X86_64IntegerRegister::Rdi,
            X86_64IntegerRegister::R8,
            X86_64IntegerRegister::R9,
            X86_64IntegerRegister::R10,
            X86_64IntegerRegister::R11,
        ]
    );
    assert_eq!(
        target.callee_preserved_registers(),
        &[
            X86_64IntegerRegister::Rbx,
            X86_64IntegerRegister::Rbp,
            X86_64IntegerRegister::Rsp,
            X86_64IntegerRegister::R12,
            X86_64IntegerRegister::R13,
            X86_64IntegerRegister::R14,
            X86_64IntegerRegister::R15,
        ]
    );
    assert_eq!(
        target.allocatable_callee_saved_registers(),
        &[
            X86_64IntegerRegister::Rbx,
            X86_64IntegerRegister::R12,
            X86_64IntegerRegister::R13,
            X86_64IntegerRegister::R14,
            X86_64IntegerRegister::R15,
        ]
    );
    assert_eq!(target.direct_result_register(), X86_64IntegerRegister::Rax);
    assert_eq!(target.stack_pointer_register(), X86_64IntegerRegister::Rsp);
    assert_eq!(target.frame_pointer_register(), X86_64IntegerRegister::Rbp);
    assert_eq!(
        target.internal_function_symbol(VirFunctionId::new(17)),
        ".Lnera_v0_fn_17"
    );
    assert_eq!(target.executable_entry_symbol(), "main");
    assert_eq!(X86_64LinuxTarget::default(), target);
    assert_eq!(target.triple().parse(), Ok(target));

    let error = "aarch64-unknown-linux-gnu"
        .parse::<X86_64LinuxTarget>()
        .expect_err("unsupported triples fail closed");
    assert_eq!(error.triple(), "aarch64-unknown-linux-gnu");
    assert!(error.to_string().contains(target.triple()));

    assert_eq!(
        target.classify_type(VirType::U64),
        Some(X86_64RuntimeType::U64)
    );
    assert_eq!(
        target.classify_type(VirType::Bool),
        Some(X86_64RuntimeType::Bool)
    );
    assert_eq!(
        target.classify_type(pointer()),
        Some(X86_64RuntimeType::Pointer)
    );
    assert_eq!(target.classify_type(VirType::Permission), None);
}

#[test]
fn direct_signature_erases_permissions_and_preserves_vir_positions() {
    let signature = VirSignature {
        parameters: vec![
            VirType::Permission,
            VirType::U64,
            VirType::Bool,
            pointer(),
            VirType::U64,
            VirType::U64,
            VirType::U64,
            VirType::U64,
        ],
        results: vec![VirType::Permission, VirType::U64],
    };

    let classified = X86_64_UNKNOWN_LINUX_GNU
        .classify_signature(&signature)
        .expect("the VIR v0 signature is representable");

    assert_eq!(classified.result_buffer(), None);
    assert_eq!(classified.stack_parameter_count(), 1);
    assert_eq!(classified.stack_argument_size_bytes(), 8);
    assert_eq!(classified.outgoing_stack_size_bytes(), 16);
    assert_eq!(classified.outgoing_stack_padding_bytes(), 8);
    assert_eq!(classified.caller_stack_cleanup_bytes(), 16);
    assert_eq!(
        classified
            .parameters()
            .iter()
            .map(|parameter| (parameter.vir_index(), parameter.ty(), parameter.location()))
            .collect::<Vec<_>>(),
        vec![
            (
                1,
                X86_64RuntimeType::U64,
                X86_64AbiParameterLocation::Register(X86_64IntegerRegister::Rdi)
            ),
            (
                2,
                X86_64RuntimeType::Bool,
                X86_64AbiParameterLocation::Register(X86_64IntegerRegister::Rsi)
            ),
            (
                3,
                X86_64RuntimeType::Pointer,
                X86_64AbiParameterLocation::Register(X86_64IntegerRegister::Rdx)
            ),
            (
                4,
                X86_64RuntimeType::U64,
                X86_64AbiParameterLocation::Register(X86_64IntegerRegister::Rcx)
            ),
            (
                5,
                X86_64RuntimeType::U64,
                X86_64AbiParameterLocation::Register(X86_64IntegerRegister::R8)
            ),
            (
                6,
                X86_64RuntimeType::U64,
                X86_64AbiParameterLocation::Register(X86_64IntegerRegister::R9)
            ),
            (
                7,
                X86_64RuntimeType::U64,
                X86_64AbiParameterLocation::CallerStack(X86_64CallerStackLocation::from_slot(0))
            ),
        ]
    );
    assert_eq!(classified.results().len(), 1);
    assert_eq!(classified.results()[0].vir_index(), 1);
    assert_eq!(classified.results()[0].ty(), X86_64RuntimeType::U64);
    assert_eq!(
        classified.results()[0].location(),
        X86_64AbiResultLocation::Register(X86_64IntegerRegister::Rax)
    );
}

#[test]
fn multiple_results_use_a_hidden_buffer_and_shift_parameters() {
    let signature = VirSignature {
        parameters: vec![
            VirType::Permission,
            VirType::U64,
            VirType::Bool,
            pointer(),
            VirType::U64,
            VirType::U64,
            VirType::U64,
        ],
        results: vec![VirType::U64, VirType::Permission, VirType::Bool, pointer()],
    };

    let classified = X86_64_UNKNOWN_LINUX_GNU
        .classify_signature(&signature)
        .expect("the VIR v0 signature is representable");
    let buffer = classified
        .result_buffer()
        .expect("multiple runtime results use sret");

    assert_eq!(buffer.pointer_register(), X86_64IntegerRegister::Rdi);
    assert_eq!(buffer.size_bytes(), 24);
    assert_eq!(buffer.alignment_bytes(), 8);
    assert_eq!(classified.stack_parameter_count(), 1);
    assert_eq!(classified.outgoing_stack_size_bytes(), 16);
    assert_eq!(
        classified
            .parameters()
            .iter()
            .map(|parameter| parameter.location())
            .collect::<Vec<_>>(),
        vec![
            X86_64AbiParameterLocation::Register(X86_64IntegerRegister::Rsi),
            X86_64AbiParameterLocation::Register(X86_64IntegerRegister::Rdx),
            X86_64AbiParameterLocation::Register(X86_64IntegerRegister::Rcx),
            X86_64AbiParameterLocation::Register(X86_64IntegerRegister::R8),
            X86_64AbiParameterLocation::Register(X86_64IntegerRegister::R9),
            X86_64AbiParameterLocation::CallerStack(X86_64CallerStackLocation::from_slot(0)),
        ]
    );
    assert_eq!(
        classified
            .results()
            .iter()
            .map(|result| (result.vir_index(), result.ty(), result.location()))
            .collect::<Vec<_>>(),
        vec![
            (
                0,
                X86_64RuntimeType::U64,
                X86_64AbiResultLocation::ResultBuffer { offset_bytes: 0 }
            ),
            (
                2,
                X86_64RuntimeType::Bool,
                X86_64AbiResultLocation::ResultBuffer { offset_bytes: 8 }
            ),
            (
                3,
                X86_64RuntimeType::Pointer,
                X86_64AbiResultLocation::ResultBuffer { offset_bytes: 16 }
            ),
        ]
    );
}

#[test]
fn caller_stack_slots_have_frozen_offsets_and_trailing_padding() {
    let target = X86_64_UNKNOWN_LINUX_GNU;

    for (runtime_parameters, expected_stack_count, expected_padding) in
        [(6, 0, 0), (7, 1, 8), (8, 2, 0)]
    {
        let classified = target
            .classify_signature(&VirSignature {
                parameters: vec![VirType::U64; runtime_parameters],
                results: vec![],
            })
            .expect("small scalar signatures are representable");

        assert_eq!(classified.stack_parameter_count(), expected_stack_count);
        assert_eq!(
            classified.stack_argument_size_bytes(),
            u64::from(expected_stack_count) * 8
        );
        assert_eq!(classified.outgoing_stack_padding_bytes(), expected_padding);
        assert_eq!(
            classified.caller_stack_cleanup_bytes(),
            classified.outgoing_stack_size_bytes()
        );

        for (expected_slot, parameter) in classified.parameters()[6..].iter().enumerate() {
            let X86_64AbiParameterLocation::CallerStack(location) = parameter.location() else {
                panic!("parameters after the sixth runtime word must use the caller stack");
            };
            let expected_slot = u32::try_from(expected_slot).expect("test slot fits u32");
            assert_eq!(location.slot(), expected_slot);
            assert_eq!(
                location.offset_from_call_site_rsp_bytes(),
                u64::from(expected_slot) * 8
            );
            assert_eq!(
                location.offset_from_callee_entry_rsp_bytes(),
                8 + u64::from(expected_slot) * 8
            );
            assert_eq!(
                location.offset_from_callee_frame_pointer_bytes(),
                16 + u64::from(expected_slot) * 8
            );
        }
    }
}

#[test]
fn executable_entry_is_stricter_than_an_internal_function() {
    let target = X86_64_UNKNOWN_LINUX_GNU;

    for (results, expected) in [
        (vec![], X86_64EntryResult::Unit),
        (vec![VirType::Permission], X86_64EntryResult::Unit),
        (vec![VirType::Bool], X86_64EntryResult::BoolExitStatus),
        (
            vec![VirType::Permission, VirType::U64],
            X86_64EntryResult::U64Low32ExitStatus,
        ),
    ] {
        let entry = target
            .classify_entry(&VirSignature {
                parameters: vec![],
                results,
            })
            .expect("the entry result has a process representation");
        assert_eq!(entry.result(), expected);
    }

    let error = target
        .classify_entry(&VirSignature {
            parameters: vec![VirType::Permission],
            results: vec![],
        })
        .expect_err("even ghost entry parameters require an unavailable input resource");
    assert_eq!(
        error.kind(),
        &X86_64AbiErrorKind::EntryParametersUnsupported {
            vir_count: 1,
            runtime_count: 0,
        }
    );

    let error = target
        .classify_entry(&VirSignature {
            parameters: vec![],
            results: vec![pointer()],
        })
        .expect_err("a pointer cannot be a process status");
    assert_eq!(
        error.kind(),
        &X86_64AbiErrorKind::EntryResultsUnsupported {
            runtime_types: vec![X86_64RuntimeType::Pointer],
        }
    );

    let error = target
        .classify_entry(&VirSignature {
            parameters: vec![],
            results: vec![VirType::U64, VirType::Bool],
        })
        .expect_err("multiple runtime results cannot be a process status");
    assert_eq!(
        error.kind(),
        &X86_64AbiErrorKind::EntryResultsUnsupported {
            runtime_types: vec![X86_64RuntimeType::U64, X86_64RuntimeType::Bool],
        }
    );
}

const fn pointer() -> VirType {
    VirType::Pointer {
        access: nera::VirMemoryAccess::core_u64(),
    }
}
