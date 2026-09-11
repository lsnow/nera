//! Unit-scoped SSA source recipes; static roots are not runtime instances.
use super::{VirSequence, VirSubobject};
use crate::vir::{
    ValidatedVirUnit, VirFunctionId, VirInstruction, VirLocation, VirMemoryAccess,
    VirObjectPathSegment, VirOriginId, VirRegionId, VirType, VirValueId,
};
use std::collections::BTreeMap;

/// Dynamic index/slice recipes retain SSA operands and the canonical extent
/// source. They do not assert any numeric bounds or initialized elements.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VirAddressStep {
    Subobject(VirSubobject),
    /// Existing ABI leaf encoding can describe several same-address variants.
    /// Preserve the source edge, but do not invent a unique arithmetic domain.
    UnresolvedLeaf {
        owner: VirMemoryAccess,
        leaf: VirMemoryAccess,
        offset_bytes: u64,
    },
    Index {
        sequence: VirSequence,
        index: VirValueId,
    },
    Slice {
        sequence: VirSequence,
        slice: VirMemoryAccess,
        start: VirValueId,
        end: VirValueId,
    },
    ByteOffset {
        delta_bytes: VirValueId,
    },
    /// Address formation preserves provenance, not the source authority.
    RawAddress {
        raw_type: VirMemoryAccess,
    },
    /// Loan identity/range/authority remain owned by the loan subsystem.
    Preserve,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct VirPointerKey {
    pub function: VirFunctionId,
    pub value: VirValueId,
}

/// A root here is a static source, NOT a fresh allocation instance. Block
/// parameters, returned pointers and loaded payloads require later CFG/caller
/// bindings; this catalog deliberately makes no non-aliasing claim about them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VirPointerSource {
    AllocationSite {
        region: VirRegionId,
        size_bytes: VirValueId,
    },
    LocalStorageSite {
        size_bytes: u64,
    },
    SymbolicParameter {
        function_entry: bool,
    },
    SymbolicCallResult,
    LoadedPayload,
    Derived {
        base: VirPointerKey,
        step: VirAddressStep,
    },
}

/// Public proposal data for inspection/replay, not a permission token.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirPointerDescription {
    pub location: VirLocation,
    pub origin: VirOriginId,
    pub access: VirMemoryAccess,
    pub source: VirPointerSource,
}

/// Unit-scoped, linear-size source graph. Cross-block provenance propagation
/// and concrete instance freshness are intentionally not solved by this graph.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VirProvenanceCatalog {
    entries: BTreeMap<VirPointerKey, VirPointerDescription>,
}

impl VirProvenanceCatalog {
    pub fn entries(&self) -> &BTreeMap<VirPointerKey, VirPointerDescription> {
        &self.entries
    }

    /// Compare with metadata derived from the sealed unit. Source, path, extent, type, location and
    /// origin must all match; a matching recipe still establishes no safety.
    pub fn matches(&self, key: VirPointerKey, proposal: &VirPointerDescription) -> bool {
        self.entries.get(&key) == Some(proposal)
    }
}

impl ValidatedVirUnit {
    /// Derives inspection metadata exclusively from validated runtime/schema
    /// and source tables. No serialized metadata or ABI change is necessary.
    pub fn provenance_catalog(&self) -> VirProvenanceCatalog {
        let unit = self.as_unit();
        let memory = &unit.memory;
        let mut entries = BTreeMap::new();
        for function in &unit.runtime.functions {
            for block in &function.blocks {
                for (ordinal, parameter) in block.parameters.iter().enumerate() {
                    let VirType::Pointer { access } = parameter.ty else {
                        continue;
                    };
                    let location = VirLocation::BlockParameter {
                        function: function.id,
                        block: block.id,
                        ordinal: ordinal as u64,
                    };
                    entries.insert(
                        VirPointerKey {
                            function: function.id,
                            value: parameter.id,
                        },
                        VirPointerDescription {
                            location,
                            origin: unit
                                .source_map
                                .origin_at(location)
                                .expect("validated parameter origin")
                                .id,
                            access,
                            source: VirPointerSource::SymbolicParameter {
                                function_entry: block.id == function.entry,
                            },
                        },
                    );
                }
                for (ordinal, spanned) in block.instructions.iter().enumerate() {
                    let instruction = &spanned.instruction;
                    let location = VirLocation::Instruction {
                        function: function.id,
                        block: block.id,
                        ordinal: ordinal as u64,
                    };
                    instruction.visit_results(|result| {
                        let VirType::Pointer { access } = result.ty else {
                            return;
                        };
                        let derive = |base, step| VirPointerSource::Derived {
                            base: VirPointerKey {
                                function: function.id,
                                value: base,
                            },
                            step,
                        };
                        let source = match instruction {
                            VirInstruction::Allocate {
                                region, size_bytes, ..
                            } => VirPointerSource::AllocationSite {
                                region: *region,
                                size_bytes: *size_bytes,
                            },
                            VirInstruction::LocalStorage { access, .. } => {
                                VirPointerSource::LocalStorageSite {
                                    size_bytes: memory
                                        .layout(access.layout)
                                        .expect("validated local layout")
                                        .size_bytes,
                                }
                            }
                            VirInstruction::FieldAddress {
                                base, owner, field, ..
                            } => derive(
                                *base,
                                VirAddressStep::Subobject(
                                    memory
                                        .field_subobject(*owner, *field)
                                        .expect("validated field path"),
                                ),
                            ),
                            VirInstruction::TupleElementAddress {
                                base, owner, index, ..
                            } => derive(
                                *base,
                                VirAddressStep::Subobject(
                                    memory
                                        .subobject(
                                            *owner,
                                            &[VirObjectPathSegment::TupleElement(*index)],
                                        )
                                        .expect("validated tuple path"),
                                ),
                            ),
                            VirInstruction::ObjectLeafAddress {
                                base,
                                owner,
                                leaf,
                                offset_bytes,
                                ..
                            } => derive(
                                *base,
                                memory
                                    .leaf_subobject(*owner, *leaf, *offset_bytes)
                                    .map(VirAddressStep::Subobject)
                                    .unwrap_or(VirAddressStep::UnresolvedLeaf {
                                        owner: *owner,
                                        leaf: *leaf,
                                        offset_bytes: *offset_bytes,
                                    }),
                            ),
                            VirInstruction::IndexAddress {
                                base,
                                index,
                                source,
                                bounds,
                                ..
                            } => derive(
                                *base,
                                VirAddressStep::Index {
                                    sequence: memory
                                        .sequence(*source, *bounds)
                                        .expect("validated sequence"),
                                    index: *index,
                                },
                            ),
                            VirInstruction::SliceAddress {
                                base,
                                start,
                                end,
                                source,
                                slice,
                                bounds,
                                ..
                            }
                            | VirInstruction::SliceRange {
                                base,
                                start,
                                end,
                                source,
                                slice,
                                bounds,
                                ..
                            } => derive(
                                *base,
                                VirAddressStep::Slice {
                                    sequence: memory
                                        .slice_sequence(*source, *slice, *bounds)
                                        .expect("validated slice"),
                                    slice: *slice,
                                    start: *start,
                                    end: *end,
                                },
                            ),
                            VirInstruction::RawAddress { base, raw_type, .. } => derive(
                                *base,
                                VirAddressStep::RawAddress {
                                    raw_type: *raw_type,
                                },
                            ),
                            VirInstruction::PointerOffset {
                                base, delta_bytes, ..
                            } => derive(
                                *base,
                                VirAddressStep::ByteOffset {
                                    delta_bytes: *delta_bytes,
                                },
                            ),
                            VirInstruction::LoanBegin { effect, .. }
                            | VirInstruction::LoanAliasShared { effect, .. }
                            | VirInstruction::LoanReborrow { effect, .. } => {
                                derive(effect.source_pointer, VirAddressStep::Preserve)
                            }
                            VirInstruction::LoanAliasAuthority { effect, .. }
                            | VirInstruction::LoanReborrowAuthority { effect, .. } => {
                                derive(effect.source_pointer, VirAddressStep::Preserve)
                            }
                            VirInstruction::Call { .. } => VirPointerSource::SymbolicCallResult,
                            _ => VirPointerSource::LoadedPayload,
                        };
                        entries.insert(
                            VirPointerKey {
                                function: function.id,
                                value: result.id,
                            },
                            VirPointerDescription {
                                location,
                                origin: unit
                                    .source_map
                                    .origin_at(location)
                                    .expect("validated instruction origin")
                                    .id,
                                access,
                                source,
                            },
                        );
                    });
                }
            }
        }
        VirProvenanceCatalog { entries }
    }
}
