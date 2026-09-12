//! Compatibility projection from validated VIR to the frozen Core0 proposal.
//!
//! This is not a second surface-language lowering path.  It exists only so the
//! frozen stage 3 Lean frontend prototype can keep checking its historical Core
//! proposal while the production pipeline moves through VIR.

use std::collections::{BTreeMap, BTreeSet};

use super::{
    Core0CompatibilityError, CoreInstruction, CoreProgramProposal, Register, SpannedCoreInstruction,
};
use crate::ByteSpan;
use crate::vir::{
    ResolvedRuntimeVirView, VirConstant, VirInstruction, VirTerminator, VirType, VirValueId,
};

pub(super) fn project(
    vir: &ResolvedRuntimeVirView<'_>,
) -> Result<CoreProgramProposal, Core0CompatibilityError> {
    Projector::new(vir).project(vir)
}

struct Projector {
    instructions: Vec<SpannedCoreInstruction>,
    registers: BTreeMap<VirValueId, Register>,
    constants: BTreeMap<VirValueId, u64>,
    inline_constants: BTreeSet<VirValueId>,
    next_register: Register,
}

impl Projector {
    fn new(vir: &ResolvedRuntimeVirView<'_>) -> Self {
        let inline_constants = vir
            .functions
            .iter()
            .flat_map(|function| &function.blocks)
            .flat_map(|block| &block.instructions)
            .filter_map(|spanned| match spanned.instruction {
                VirInstruction::Allocate { size_bytes, .. } => Some(size_bytes),
                VirInstruction::PointerOffset { delta_bytes, .. } => Some(delta_bytes),
                _ => None,
            })
            .collect();
        Self {
            instructions: Vec::new(),
            registers: BTreeMap::new(),
            constants: BTreeMap::new(),
            inline_constants,
            next_register: 0,
        }
    }

    fn project(
        mut self,
        vir: &ResolvedRuntimeVirView<'_>,
    ) -> Result<CoreProgramProposal, Core0CompatibilityError> {
        let [function] = vir.functions else {
            return Err(invalid_vir(
                vir.functions
                    .first()
                    .map_or_else(ByteSpan::empty, |function| function.source_span),
            ));
        };
        if function.id != vir.entry
            || !function.signature.parameters.is_empty()
            || !matches!(function.signature.results.as_slice(), [] | [VirType::U64])
        {
            return Err(invalid_vir(function.source_span));
        }
        let [block] = function.blocks.as_slice() else {
            return Err(invalid_vir(function.source_span));
        };
        if block.id != function.entry || !block.parameters.is_empty() {
            return Err(invalid_vir(block.source_span));
        }

        for instruction in &block.instructions {
            self.project_instruction(&instruction.instruction, instruction.source_span)?;
        }
        let VirTerminator::Return { values } = &block.terminator.terminator else {
            return Err(invalid_vir(block.terminator.source_span));
        };
        let source = match values.as_slice() {
            [] => self.emit_integer(0, block.terminator.source_span)?,
            [value] => self.lookup_register(*value, block.terminator.source_span)?,
            _ => return Err(invalid_vir(block.terminator.source_span)),
        };
        self.emit(
            CoreInstruction::Return { source },
            block.terminator.source_span,
        );

        Ok(CoreProgramProposal {
            function_name: function.name.clone(),
            instructions: self.instructions,
            register_count: self.next_register,
            source_span: function.source_span,
        })
    }

    fn project_instruction(
        &mut self,
        instruction: &VirInstruction,
        source_span: ByteSpan,
    ) -> Result<(), Core0CompatibilityError> {
        match instruction {
            VirInstruction::Constant { result, value } => {
                let VirConstant::U64(word) = value else {
                    // Compiler-generated drop flags have no Core0 runtime
                    // representation. Any attempted Core0 use still fails at
                    // register lookup, so an otherwise dead flag is erasable.
                    return Ok(());
                };
                if self.constants.insert(result.id, *word).is_some() {
                    return Err(invalid_vir(source_span));
                }
                if !self.inline_constants.contains(&result.id) {
                    let register = self.fresh_register(source_span)?;
                    self.assign_register(result.id, register, source_span)?;
                    self.emit(
                        CoreInstruction::Set {
                            destination: register,
                            word: *word,
                        },
                        source_span,
                    );
                }
            }
            VirInstruction::WordAdd {
                result,
                left,
                right,
            } => {
                let left = self.lookup_register(*left, source_span)?;
                let right = self.lookup_register(*right, source_span)?;
                let destination = self.fresh_register(source_span)?;
                self.assign_register(result.id, destination, source_span)?;
                self.emit(
                    CoreInstruction::Add {
                        destination,
                        left,
                        right,
                    },
                    source_span,
                );
            }
            VirInstruction::Allocate {
                pointer_result,
                size_bytes,
                alignment,
                region,
                ..
            } => {
                if !matches!(alignment, 1 | 2 | 4 | 8) {
                    return Err(invalid_vir(source_span));
                }
                let size_bytes = self.lookup_constant(*size_bytes, source_span)?;
                let destination = self.fresh_register(source_span)?;
                self.assign_register(pointer_result.id, destination, source_span)?;
                self.emit(
                    CoreInstruction::Allocate {
                        destination,
                        size_bytes,
                        alignment: *alignment,
                        region: u64::from(region.get()),
                    },
                    source_span,
                );
            }
            VirInstruction::Initialize { pointer, value, .. }
            | VirInstruction::Write { pointer, value, .. }
            | VirInstruction::Store { pointer, value, .. } => {
                let pointer = self.lookup_register(*pointer, source_span)?;
                let source = self.lookup_register(*value, source_span)?;
                self.emit(CoreInstruction::Store { pointer, source }, source_span);
            }
            VirInstruction::Load {
                result, pointer, ..
            } => {
                let pointer = self.lookup_register(*pointer, source_span)?;
                let destination = self.fresh_register(source_span)?;
                self.assign_register(result.id, destination, source_span)?;
                self.emit(
                    CoreInstruction::Load {
                        destination,
                        pointer,
                    },
                    source_span,
                );
            }
            VirInstruction::PointerOffset {
                result,
                base,
                delta_bytes,
            } => {
                let base = self.lookup_register(*base, source_span)?;
                let delta_bytes = self.lookup_constant(*delta_bytes, source_span)?;
                let destination = self.fresh_register(source_span)?;
                self.assign_register(result.id, destination, source_span)?;
                self.emit(
                    CoreInstruction::Offset {
                        destination,
                        base,
                        delta_bytes,
                    },
                    source_span,
                );
            }
            VirInstruction::Free { pointer, .. } => {
                let pointer = self.lookup_register(*pointer, source_span)?;
                self.emit(CoreInstruction::Free { pointer }, source_span);
            }
            VirInstruction::LocalStorage { .. }
            | VirInstruction::DropOwn { .. }
            | VirInstruction::ObjectTransfer { .. }
            | VirInstruction::ResourceInitialize { .. }
            | VirInstruction::ResourceTake { .. }
            | VirInstruction::ObjectDeinitialize { .. }
            | VirInstruction::StorageReset { .. }
            | VirInstruction::ResourceStorageReset { .. }
            | VirInstruction::ObjectDrop { .. }
            | VirInstruction::EnumDiscriminant { .. }
            | VirInstruction::EnumSetDiscriminant { .. }
            | VirInstruction::FieldAddress { .. }
            | VirInstruction::RawAddress { .. }
            | VirInstruction::TupleElementAddress { .. }
            | VirInstruction::ObjectLeafAddress { .. }
            | VirInstruction::IndexAddress { .. }
            | VirInstruction::SliceAddress { .. }
            | VirInstruction::SliceRange { .. }
            | VirInstruction::Compare { .. }
            | VirInstruction::PointerCompare { .. }
            | VirInstruction::PointerDistance { .. }
            | VirInstruction::PermissionSplit { .. }
            | VirInstruction::PermissionJoin { .. }
            | VirInstruction::PermissionMove { .. }
            | VirInstruction::LoanBegin { .. }
            | VirInstruction::LoanAliasShared { .. }
            | VirInstruction::LoanReborrow { .. }
            | VirInstruction::LoanEnd { .. }
            | VirInstruction::LoanAliasAuthority { .. }
            | VirInstruction::LoanReborrowAuthority { .. }
            | VirInstruction::LoanEndAuthority { .. }
            | VirInstruction::Check { .. }
            | VirInstruction::Call { .. } => return Err(invalid_vir(source_span)),
        }
        Ok(())
    }

    fn emit_integer(
        &mut self,
        word: u64,
        source_span: ByteSpan,
    ) -> Result<Register, Core0CompatibilityError> {
        let destination = self.fresh_register(source_span)?;
        self.emit(CoreInstruction::Set { destination, word }, source_span);
        Ok(destination)
    }

    fn lookup_register(
        &self,
        value: VirValueId,
        source_span: ByteSpan,
    ) -> Result<Register, Core0CompatibilityError> {
        self.registers
            .get(&value)
            .copied()
            .ok_or_else(|| invalid_vir(source_span))
    }

    fn lookup_constant(
        &self,
        value: VirValueId,
        source_span: ByteSpan,
    ) -> Result<u64, Core0CompatibilityError> {
        self.constants
            .get(&value)
            .copied()
            .ok_or_else(|| invalid_vir(source_span))
    }

    fn assign_register(
        &mut self,
        value: VirValueId,
        register: Register,
        source_span: ByteSpan,
    ) -> Result<(), Core0CompatibilityError> {
        if self.registers.insert(value, register).is_some() {
            return Err(invalid_vir(source_span));
        }
        Ok(())
    }

    fn fresh_register(
        &mut self,
        source_span: ByteSpan,
    ) -> Result<Register, Core0CompatibilityError> {
        let register = self.next_register;
        self.next_register = self
            .next_register
            .checked_add(1)
            .ok_or_else(|| invalid_vir(source_span))?;
        Ok(register)
    }

    fn emit(&mut self, instruction: CoreInstruction, source_span: ByteSpan) {
        self.instructions.push(SpannedCoreInstruction {
            instruction,
            source_span,
        });
    }
}

const fn invalid_vir(source_span: ByteSpan) -> Core0CompatibilityError {
    Core0CompatibilityError::new(source_span)
}
