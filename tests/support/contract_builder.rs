#![allow(dead_code)]

use nera::{
    VirContract, VirContractAccess, VirContractFree, VirContractId, VirContractInitialization,
    VirContractLiveness, VirContractOwnership, VirContractPermission, VirContractPointer,
    VirContractPosition, VirContractResourceId, VirContractResourceSummary, VirFunctionId,
    VirLocation, VirOriginId, VirRegionId, VirSpecClauseKind, VirSpecClauseOrigin,
    VirSpecEnvironment, VirUnit,
};

pub fn function_origin(unit: &VirUnit, function: VirFunctionId) -> VirOriginId {
    unit.source_map
        .origin_at(VirLocation::FunctionEntry { function })
        .expect("fixture function has a source-map origin")
        .id
}

pub fn ensure_resource(contract: &mut VirContract, raw: u32) -> VirContractResourceId {
    while contract.resources.len() <= raw as usize {
        let _ = contract.add_resource();
    }
    VirContractResourceId::new(raw)
}

#[derive(Clone, Copy)]
pub struct PointerFact {
    pub slot: usize,
    pub lower: u64,
    pub upper: u64,
    pub alignment: u64,
}

#[derive(Clone, Copy)]
pub struct PermissionFact {
    pub slot: usize,
    pub start: u64,
    pub end: u64,
    pub access: VirContractAccess,
    pub free: VirContractFree,
}

#[allow(clippy::too_many_arguments)]
pub fn add_resource_clause(
    specs: &mut VirSpecEnvironment,
    contract_id: VirContractId,
    position: VirContractPosition,
    origin: VirOriginId,
    inferred: bool,
    resource: u32,
    region: VirRegionId,
    size_bytes: u64,
    alignment: u64,
    liveness: VirContractLiveness,
    ownership: VirContractOwnership,
    initialization: VirContractInitialization,
    pointers: &[PointerFact],
    permissions: &[PermissionFact],
) {
    let resource = ensure_resource(
        specs.contract_mut(contract_id).expect("fixture contract"),
        resource,
    );
    let (pointers, permissions) = {
        let contract = specs.contract(contract_id).expect("fixture contract");
        let pointers = pointers
            .iter()
            .map(|fact| VirContractPointer {
                binder: contract
                    .binder(position, fact.slot)
                    .expect("pointer fixture slot has a binder"),
                offset_lower: fact.lower,
                offset_upper: fact.upper,
                alignment: fact.alignment,
            })
            .collect();
        let permissions = permissions
            .iter()
            .map(|fact| VirContractPermission {
                binder: contract
                    .binder(position, fact.slot)
                    .expect("permission fixture slot has a binder"),
                start_byte: fact.start,
                end_byte: fact.end,
                access: fact.access,
                free: fact.free,
            })
            .collect();
        (pointers, permissions)
    };
    let origin = if inferred {
        VirSpecClauseOrigin::InferredType { origin }
    } else {
        VirSpecClauseOrigin::Explicit { origin }
    };
    let _ = specs.add_contract_clause(
        contract_id,
        position,
        origin,
        VirSpecClauseKind::Resource(VirContractResourceSummary {
            resource,
            region,
            size_bytes,
            alignment,
            liveness,
            ownership,
            initialization,
            pointers,
            permissions,
        }),
    );
}

pub fn add_u64_range(
    specs: &mut VirSpecEnvironment,
    contract_id: VirContractId,
    position: VirContractPosition,
    origin: VirOriginId,
    slot: usize,
    lower: u64,
    upper: u64,
) {
    let binder = specs
        .contract(contract_id)
        .expect("fixture contract")
        .binder(position, slot)
        .expect("u64 fixture slot has a binder");
    let _ = specs.add_contract_clause(
        contract_id,
        position,
        VirSpecClauseOrigin::Explicit { origin },
        VirSpecClauseKind::U64Range {
            binder,
            lower,
            upper,
        },
    );
}

pub fn add_bool_value(
    specs: &mut VirSpecEnvironment,
    contract_id: VirContractId,
    position: VirContractPosition,
    origin: VirOriginId,
    slot: usize,
    value: bool,
) {
    let binder = specs
        .contract(contract_id)
        .expect("fixture contract")
        .binder(position, slot)
        .expect("bool fixture slot has a binder");
    let _ = specs.add_contract_clause(
        contract_id,
        position,
        VirSpecClauseOrigin::Explicit { origin },
        VirSpecClauseKind::BoolValue { binder, value },
    );
}

#[allow(clippy::too_many_arguments)]
pub fn add_own_word(
    specs: &mut VirSpecEnvironment,
    contract_id: VirContractId,
    position: VirContractPosition,
    origin: VirOriginId,
    resource: u32,
    pointer_slot: usize,
    permission_slot: usize,
    initialization: VirContractInitialization,
) {
    add_resource_clause(
        specs,
        contract_id,
        position,
        origin,
        true,
        resource,
        VirRegionId::new(0),
        8,
        8,
        VirContractLiveness::Live,
        VirContractOwnership::Owned,
        initialization,
        &[PointerFact {
            slot: pointer_slot,
            lower: 0,
            upper: 0,
            alignment: 8,
        }],
        &[PermissionFact {
            slot: permission_slot,
            start: 0,
            end: 8,
            access: VirContractAccess::Write,
            free: VirContractFree::Yes,
        }],
    );
}
