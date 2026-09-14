//! Signature substitution only. This view carries no proof or resource authority.
use super::*;
use crate::{
    VirContractPosition, VirLocation, VirSpecClauseOwner, VirSpecSnapshot, VirSpecTermId,
    VirSpecTermKind, VirValue, VirValueId,
};

/// One statically resolved call occurrence bound to its validated unit.
/// Repeated execution must still instantiate fresh verifier state; this is not
/// a cache key or a certificate that the callee/contract has been verified.
#[derive(Debug)]
pub struct VirContractCallBinding<'unit> {
    unit: &'unit VirUnit,
    location: VirLocation,
    callee: &'unit VirFunction,
    arguments: &'unit [VirValueId],
    results: &'unit [VirValue],
}

impl VirContractCallBinding<'_> {
    #[must_use]
    pub const fn location(&self) -> VirLocation {
        self.location
    }

    /// Maps a clause-owned scalar snapshot to a caller SSA slot and the side
    /// of the call at which it is observed. EntryParameter stays pre-call even
    /// though the containing clause is an ensures clause.
    #[must_use]
    pub fn snapshot(&self, term: VirSpecTermId) -> Option<(VirContractPosition, VirValueId)> {
        let term = self
            .unit
            .specs
            .terms()
            .get(term.get() as usize)
            .filter(|t| t.id == term)?;
        let clause = self.unit.specs.clause(term.clause)?;
        let VirSpecClauseOwner::Contract { contract, .. } = clause.owner else {
            return None;
        };
        if contract != self.callee.contract {
            return None;
        }
        match term.kind {
            VirSpecTermKind::Snapshot(
                VirSpecSnapshot::Parameter { function, slot }
                | VirSpecSnapshot::EntryParameter { function, slot },
            ) if function == self.callee.id => self
                .arguments
                .get(slot as usize)
                .map(|id| (VirContractPosition::Requires, *id)),
            VirSpecTermKind::Snapshot(VirSpecSnapshot::Result { function, slot })
                if function == self.callee.id =>
            {
                self.results
                    .get(slot as usize)
                    .map(|v| (VirContractPosition::Ensures, v.id))
            }
            _ => None,
        }
    }
}

impl<'unit> ResolvedVirUnit<'unit> {
    #[must_use]
    pub fn contract_call_binding(
        &self,
        location: VirLocation,
    ) -> Option<VirContractCallBinding<'unit>> {
        let VirLocation::Instruction {
            function,
            block,
            ordinal,
        } = location
        else {
            return None;
        };
        let body = self.runtime.block(function, block)?;
        let VirInstruction::Call {
            target,
            arguments,
            results,
        } = &body
            .instructions
            .get(usize::try_from(ordinal).ok()?)?
            .instruction
        else {
            return None;
        };
        let callee = self.runtime.call_function(target)?;
        Some(VirContractCallBinding {
            unit: self.validated.as_unit(),
            location,
            callee,
            arguments,
            results,
        })
    }
}
