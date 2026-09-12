use std::collections::BTreeMap;

use nera::{CoreInstruction, CoreProgramProposal, Register};

const WORD_BYTES: u64 = 8;
const MAX_ALLOCATION_BYTES: u64 = 4096;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CoreOutcome {
    Returned(u64),
    Fault(CoreFault),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CoreFault {
    AllocationFailure,
    InvalidAlignment,
    InvalidRuntimeState,
    PointerOffsetOutOfBounds,
    OutOfBounds,
    Misaligned,
    UninitializedRead,
    DoubleFree,
    UseAfterFree,
    InvalidFree,
    PermissionDenied,
}

#[derive(Clone, Copy, Debug)]
enum Value {
    Word(u64),
    Pointer(Pointer),
}

#[derive(Clone, Copy, Debug)]
struct Pointer {
    allocation: usize,
    offset_bytes: u64,
    permission: Permission,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Permission {
    ReadWrite,
    Owner,
}

#[derive(Debug)]
struct Allocation {
    size_bytes: u64,
    alignment: u64,
    live: bool,
    cells: BTreeMap<u64, u64>,
}

#[derive(Debug)]
struct Machine {
    registers: Vec<Option<Value>>,
    allocations: Vec<Allocation>,
}

pub fn execute(program: &CoreProgramProposal) -> CoreOutcome {
    let Ok(register_count) = usize::try_from(program.register_count) else {
        return CoreOutcome::Fault(CoreFault::InvalidRuntimeState);
    };
    let mut machine = Machine {
        registers: vec![None; register_count],
        allocations: Vec::new(),
    };

    for spanned in &program.instructions {
        match machine.execute_instruction(&spanned.instruction) {
            Ok(Some(value)) => return CoreOutcome::Returned(value),
            Ok(None) => {}
            Err(fault) => return CoreOutcome::Fault(fault),
        }
    }
    CoreOutcome::Returned(0)
}

impl Machine {
    fn execute_instruction(
        &mut self,
        instruction: &CoreInstruction,
    ) -> Result<Option<u64>, CoreFault> {
        match *instruction {
            CoreInstruction::Set { destination, word } => {
                self.write(destination, Value::Word(word))?;
            }
            CoreInstruction::Add {
                destination,
                left,
                right,
            } => {
                let value = self.word(left)?.wrapping_add(self.word(right)?);
                self.write(destination, Value::Word(value))?;
            }
            CoreInstruction::Allocate {
                destination,
                size_bytes,
                alignment,
                ..
            } => {
                if !matches!(alignment, 1 | 2 | 4 | 8) {
                    return Err(CoreFault::InvalidAlignment);
                }
                if size_bytes == 0 || size_bytes > MAX_ALLOCATION_BYTES {
                    return Err(CoreFault::AllocationFailure);
                }
                let allocation = self.allocations.len();
                self.allocations.push(Allocation {
                    size_bytes,
                    alignment,
                    live: true,
                    cells: BTreeMap::new(),
                });
                self.write(
                    destination,
                    Value::Pointer(Pointer {
                        allocation,
                        offset_bytes: 0,
                        permission: Permission::Owner,
                    }),
                )?;
            }
            CoreInstruction::Offset {
                destination,
                base,
                delta_bytes,
            } => {
                let base = self.pointer(base)?;
                let allocation = self.allocation(base.allocation)?;
                if !allocation.live {
                    return Err(CoreFault::UseAfterFree);
                }
                let Some(offset_bytes) = base.offset_bytes.checked_add(delta_bytes) else {
                    return Err(CoreFault::PointerOffsetOutOfBounds);
                };
                if offset_bytes > allocation.size_bytes {
                    return Err(CoreFault::PointerOffsetOutOfBounds);
                }
                self.write(
                    destination,
                    Value::Pointer(Pointer {
                        offset_bytes,
                        permission: Permission::ReadWrite,
                        ..base
                    }),
                )?;
            }
            CoreInstruction::Store { pointer, source } => {
                let pointer = self.pointer(pointer)?;
                let value = self.word(source)?;
                self.check_access(pointer, false)?;
                self.allocation_mut(pointer.allocation)?
                    .cells
                    .insert(pointer.offset_bytes, value);
            }
            CoreInstruction::Load {
                destination,
                pointer,
            } => {
                let pointer = self.pointer(pointer)?;
                self.check_access(pointer, true)?;
                let value = self
                    .allocation(pointer.allocation)?
                    .cells
                    .get(&pointer.offset_bytes)
                    .copied()
                    .ok_or(CoreFault::UninitializedRead)?;
                self.write(destination, Value::Word(value))?;
            }
            CoreInstruction::Free { pointer } => {
                let pointer = self.pointer(pointer)?;
                let allocation = self.allocation(pointer.allocation)?;
                if !allocation.live {
                    return Err(CoreFault::DoubleFree);
                }
                if pointer.offset_bytes != 0 {
                    return Err(CoreFault::InvalidFree);
                }
                if pointer.permission != Permission::Owner {
                    return Err(CoreFault::PermissionDenied);
                }
                self.allocation_mut(pointer.allocation)?.live = false;
            }
            CoreInstruction::Return { source } => return Ok(Some(self.word(source)?)),
        }
        Ok(None)
    }

    fn check_access(&self, pointer: Pointer, read: bool) -> Result<(), CoreFault> {
        let allocation = self.allocation(pointer.allocation)?;
        if !allocation.live {
            return Err(CoreFault::UseAfterFree);
        }
        if allocation.alignment < WORD_BYTES || !pointer.offset_bytes.is_multiple_of(WORD_BYTES) {
            return Err(CoreFault::Misaligned);
        }
        let end = pointer
            .offset_bytes
            .checked_add(WORD_BYTES)
            .ok_or(CoreFault::OutOfBounds)?;
        if end > allocation.size_bytes {
            return Err(CoreFault::OutOfBounds);
        }
        if read && !allocation.cells.contains_key(&pointer.offset_bytes) {
            return Err(CoreFault::UninitializedRead);
        }
        Ok(())
    }

    fn word(&self, register: Register) -> Result<u64, CoreFault> {
        match self.read(register)? {
            Value::Word(value) => Ok(value),
            Value::Pointer(_) => Err(CoreFault::InvalidRuntimeState),
        }
    }

    fn pointer(&self, register: Register) -> Result<Pointer, CoreFault> {
        match self.read(register)? {
            Value::Pointer(value) => Ok(value),
            Value::Word(_) => Err(CoreFault::InvalidRuntimeState),
        }
    }

    fn read(&self, register: Register) -> Result<Value, CoreFault> {
        self.registers
            .get(register as usize)
            .and_then(|value| *value)
            .ok_or(CoreFault::InvalidRuntimeState)
    }

    fn write(&mut self, register: Register, value: Value) -> Result<(), CoreFault> {
        let slot = self
            .registers
            .get_mut(register as usize)
            .ok_or(CoreFault::InvalidRuntimeState)?;
        *slot = Some(value);
        Ok(())
    }

    fn allocation(&self, allocation: usize) -> Result<&Allocation, CoreFault> {
        self.allocations
            .get(allocation)
            .ok_or(CoreFault::InvalidRuntimeState)
    }

    fn allocation_mut(&mut self, allocation: usize) -> Result<&mut Allocation, CoreFault> {
        self.allocations
            .get_mut(allocation)
            .ok_or(CoreFault::InvalidRuntimeState)
    }
}
