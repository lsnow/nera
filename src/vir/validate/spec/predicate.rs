//! Independent structural checks for representation bodies and erased effects.
use super::*;
use crate::{VirPredicateActionKind as Action, VirPredicateRepresentation};

pub(super) fn validate(unit: &VirUnit) -> Result<(), VirValidationError> {
    for predicate in unit.specs.predicates() {
        let Some(body) = &predicate.representation else {
            continue;
        };
        if predicate.body.is_some() || !predicate.binders.is_empty() || !valid_body(unit, body) {
            return Err(program_error(VirValidationErrorKind::InvalidPredicate(
                predicate.id,
            )));
        }
    }
    let mut owned_slots = BTreeSet::new();
    let mut holders = BTreeSet::new();
    if unit.specs.predicate_interfaces().len() > 256 {
        return Err(program_error(
            VirValidationErrorKind::InvalidPredicateInterface(256),
        ));
    }
    for (index, interface) in unit.specs.predicate_interfaces().iter().enumerate() {
        let invalid = || {
            program_error(VirValidationErrorKind::InvalidPredicateInterface(
                index as u32,
            ))
        };
        let body = unit
            .specs
            .predicates()
            .get(interface.predicate.get() as usize)
            .and_then(|p| p.representation.as_ref())
            .ok_or_else(invalid)?;
        let abi = &unit
            .runtime
            .abis
            .function(interface.function)
            .ok_or_else(invalid)?
            .signature;
        if !body.has_supported_interface_witnesses()
            || !interface.arguments.values.is_empty()
            || interface
                .arguments
                .validate_arguments(
                    &body.logic,
                    &mut crate::predicate_logic::LogicBudget::default(),
                )
                .is_err()
            || !interface.arguments.inputs.iter().all(|(ty, input)| {
                use crate::predicate_logic::WitnessInput;
                let nominal = |access: crate::VirMemoryAccess| matches!((ty, unit.memory.kind(access.ty)),
                    (crate::predicate_logic::LogicType::U64, Some(crate::VirMemoryTypeKind::Integer(crate::VirIntegerType::U64)))
                    | (crate::predicate_logic::LogicType::Usize, Some(crate::VirMemoryTypeKind::Integer(crate::VirIntegerType::Usize)))
                    | (crate::predicate_logic::LogicType::Bool, Some(crate::VirMemoryTypeKind::Bool)));
                match input {
                    WitnessInput::Memory { base,offset,access,time } => (interface.ensures || *time==crate::predicate_logic::ObservationTime::Current) && nominal(*access) && abi.parameters().iter().any(|binding| {
                        if binding.parameter_slots().first()!=Some(base) { return false; }
                        let root=match binding.value() {
                            crate::VirAbiValue::Pointer { access,pointee } if matches!(unit.memory.kind(access.ty),Some(crate::VirMemoryTypeKind::Pointer { kind:crate::VirPointerKind::Own | crate::VirPointerKind::Reference,.. })) => *pointee,
                            crate::VirAbiValue::IndirectAggregate { access } => *access,
                            _=>return false,
                        };
                        unit.memory.object_shape(root).is_ok_and(|shape|shape.leaves().iter().any(|leaf|leaf.bytes().start_bytes()==*offset && leaf.access()==*access))
                    }),
                    WitnessInput::ResultField { base, offset, access } => interface.ensures && nominal(*access) && abi.results().iter().any(|binding| {
                        binding.parameter_slots().first() == Some(base)
                        && matches!(binding.value(), crate::VirAbiValue::IndirectAggregate { access: root }
                            if unit.memory.object_shape(*root).is_ok_and(|shape| shape.leaves().iter().any(|leaf|
                                leaf.bytes().start_bytes() == *offset && leaf.access() == *access)))
                    }),
                    WitnessInput::Scalar(slot) | WitnessInput::Result(slot) => {
                        let result = matches!(input, WitnessInput::Result(_));
                        (!result || interface.ensures) && (if result { abi.results() } else { abi.parameters() }).iter().any(|binding| {
                            let slots = if result { binding.result_slots() } else { binding.parameter_slots() };
                            match binding.value() {
                                crate::VirAbiValue::Scalar { access, .. } => slots == [*slot] && nominal(*access),
                                crate::VirAbiValue::DirectAggregate { leaves, .. } => slots.iter().position(|s| s == slot).and_then(|index| leaves.get(index)).is_some_and(|leaf| nominal(leaf.access())),
                                _ => false,
                            }
                        })
                    }
                    _ => false,
                }
            })
            || (interface.in_place && !interface.ensures)
            || !origin_belongs_to_function(unit, interface.function, interface.origin)
            || interface.bindings.len() != body.resources.len()
            || interface.fields.len() != body.resources.len()
            || (!interface.ensures && !holders.insert((interface.function, interface.holder)))
        {
            return Err(invalid());
        }
        let owner_bindings = if interface.ensures && !interface.in_place {
            abi.results()
        } else {
            abi.parameters()
        };
        for (((pointer, permission), path), resource) in interface
            .bindings
            .iter()
            .zip(&interface.fields)
            .zip(&body.resources)
        {
            let valid = owner_bindings.iter().any(|binding| {
                if !path.is_empty() {
                    return !interface.in_place
                        && (if interface.ensures {
                            binding.parameter_slots().first() == Some(pointer)
                                && binding.result_slots() == [*permission]
                        } else { binding.parameter_slots() == [*pointer,*permission] })
                        && binding.interface().transfer == crate::VirInterfaceTransfer::Move
                        && matches!(binding.value(), crate::VirAbiValue::IndirectAggregate { access }
                            if crate::vir::predicate_owner_field(&unit.memory,*access,path).is_some_and(|(_,_,p)| p==resource.pointee));
                }
                let slots = if interface.ensures { binding.result_slots() } else { binding.parameter_slots() };
                (if interface.in_place {
                    binding.parameter_slots().first() == Some(pointer)
                        && binding.result_slots() == [*permission]
                        && binding.interface().transfer == crate::VirInterfaceTransfer::BorrowMutable
                        && (!abi.borrow_result_parameters().iter().any(|index| &abi.parameters()[*index] == binding)
                            || (abi.borrow_result_alternatives().is_empty() && abi.borrow_result().is_some_and(|r| r.projection != crate::BorrowProjection::Whole)))
                } else { slots == [*pointer, *permission] })
                    && matches!(binding.value(), crate::VirAbiValue::Pointer { access, pointee }
                        if *pointee == resource.pointee && matches!(
                            (binding.interface().transfer, unit.memory.kind(access.ty)),
                            (crate::VirInterfaceTransfer::Move, Some(crate::VirMemoryTypeKind::Pointer { kind: crate::VirPointerKind::Own, .. }))
                            | (crate::VirInterfaceTransfer::BorrowMutable, Some(crate::VirMemoryTypeKind::Pointer { kind: crate::VirPointerKind::Reference, mutability: crate::VirMutability::Mutable, .. }))
                        ))
            });
            if !valid
                || !owned_slots.insert((
                    interface.function,
                    interface.ensures,
                    *permission,
                    path.clone(),
                ))
            {
                return Err(invalid());
            }
        }
    }
    if unit.specs.predicate_actions().len() > 4096 {
        return Err(program_error(
            VirValidationErrorKind::InvalidPredicateAction(4096),
        ));
    }
    for (index, action) in unit.specs.predicate_actions().iter().enumerate() {
        let invalid = || program_error(VirValidationErrorKind::InvalidPredicateAction(action.id));
        if action.id as usize != index {
            return Err(invalid());
        }
        let predicate = unit
            .specs
            .predicates()
            .get(action.predicate.get() as usize)
            .ok_or_else(invalid)?;
        let body = predicate.representation.as_ref().ok_or_else(invalid)?;
        let origin = unit
            .source_map
            .source_span_for_origin(action.origin)
            .ok_or_else(invalid)?;
        let owner = unit
            .source_map
            .source_span_for_origin(predicate.origin)
            .ok_or_else(invalid)?;
        // Source IDs are module input identities in the closed compilation unit.
        // No caller-supplied module number can authorize a representation open.
        if origin.source != owner.source
            || !origin_belongs_to_function(unit, action.location.function(), action.origin)
        {
            return Err(invalid());
        }
        if matches!(action.kind, Action::Fold { .. }) {
            crate::vir::spec::validate_predicate_witnesses(&unit.memory, body, &action.witnesses)
                .map_err(|_| invalid())?;
        } else {
            if !action.witnesses.values.is_empty() {
                return Err(invalid());
            }
            action
                .witnesses
                .validate_arguments(
                    &body.logic,
                    &mut crate::predicate_logic::LogicBudget::default(),
                )
                .map_err(|_| invalid())?;
        }
        let function = unit
            .runtime
            .functions
            .iter()
            .find(|f| f.id == action.location.function())
            .ok_or_else(invalid)?;
        let block = function
            .blocks
            .iter()
            .find(|b| Some(b.id) == action.location.block())
            .ok_or_else(invalid)?;
        let boundary = match action.location {
            VirLocation::BlockEntry { .. } => 0,
            VirLocation::Instruction { ordinal, .. }
                if ordinal < block.instructions.len() as u64 =>
            {
                ordinal as usize + 1
            }
            _ => return Err(invalid()),
        };
        for (ty, id) in &action.witnesses.inputs {
            let id = match id {
                crate::predicate_logic::WitnessInput::Result(_)
                | crate::predicate_logic::WitnessInput::ResultField { .. } => return Err(invalid()),
                crate::predicate_logic::WitnessInput::Memory {
                    base,
                    offset,
                    access,
                    time,
                } => {
                    let Some(VirType::Pointer { access: root }) =
                        value_type(block, boundary, *base)
                    else {
                        return Err(invalid());
                    };
                    if *time != crate::predicate_logic::ObservationTime::Current
                        || !unit.memory.object_shape(root).is_ok_and(|shape| {
                            shape.leaves().iter().any(|leaf| {
                                leaf.access() == *access && leaf.bytes().start_bytes() == *offset
                            })
                        })
                        || !matches!(
                            (ty, unit.memory.kind(access.ty)),
                            (
                                crate::predicate_logic::LogicType::U64,
                                Some(crate::VirMemoryTypeKind::Integer(
                                    crate::VirIntegerType::U64
                                ))
                            ) | (
                                crate::predicate_logic::LogicType::Usize,
                                Some(crate::VirMemoryTypeKind::Integer(
                                    crate::VirIntegerType::Usize
                                ))
                            ) | (
                                crate::predicate_logic::LogicType::Bool,
                                Some(crate::VirMemoryTypeKind::Bool)
                            )
                        )
                    {
                        return Err(invalid());
                    }
                    continue;
                }
                crate::predicate_logic::WitnessInput::Scalar(id) => id,
                crate::predicate_logic::WitnessInput::Opened {
                    action: opened,
                    holder,
                    binder,
                } => {
                    let open = unit
                        .specs
                        .predicate_actions()
                        .get(*opened as usize)
                        .ok_or_else(invalid)?;
                    if open.id >= action.id
                        || open.location.function() != action.location.function()
                        || open.predicate != action.predicate
                        || !matches!(open.kind, Action::Unfold { holder: h, .. } if h == *holder)
                        || !matches!(action.kind,
                            Action::Fold { holder: h, .. }
                            | Action::Finish { holder: h } if h == *holder)
                        || body
                            .logic
                            .existentials
                            .get(*binder as usize)
                            .is_none_or(|b| b.ty != *ty)
                    {
                        return Err(invalid());
                    }
                    continue;
                }
            };
            let expected = match ty {
                crate::predicate_logic::LogicType::Bool => VirType::Bool,
                crate::predicate_logic::LogicType::U64
                | crate::predicate_logic::LogicType::Usize => VirType::U64,
                _ => return Err(invalid()),
            };
            if value_type(block, boundary, *id) != Some(expected) {
                return Err(invalid());
            }
        }
        let bindings = match &action.kind {
            Action::Fold { bindings, .. } | Action::Unfold { bindings, .. } => bindings,
            Action::Move {
                source,
                destination,
            } if source == destination => return Err(invalid()),
            Action::Move { .. } | Action::Finish { .. } => continue,
        };
        if bindings.len() != body.resources.len() {
            return Err(invalid());
        }
        let mut permissions = BTreeSet::new();
        for (binding, resource) in bindings.iter().zip(&body.resources) {
            if !permissions.insert(binding.permission)
                || value_type(block, boundary, binding.pointer)
                    != Some(VirType::Pointer {
                        access: resource.pointee,
                    })
                || value_type(block, boundary, binding.permission) != Some(VirType::Permission)
            {
                return Err(invalid());
            }
        }
    }
    Ok(())
}

fn value_type(block: &VirBasicBlock, boundary: usize, id: VirValueId) -> Option<VirType> {
    if let Some(p) = block.parameters.iter().find(|p| p.id == id) {
        return Some(p.ty);
    }
    for instruction in block.instructions.iter().take(boundary) {
        let mut ty = None;
        instruction.instruction.visit_results(|value| {
            if value.id == id {
                ty = Some(value.ty);
            }
        });
        if ty.is_some() {
            return ty;
        }
    }
    None
}

fn valid_body(unit: &VirUnit, body: &VirPredicateRepresentation) -> bool {
    if crate::vir::validate_predicate_logic(&unit.memory, body).is_err() {
        return false;
    }
    if body.resources.is_empty() || body.resources.len() > 32 || body.bounds.len() > 32 {
        return false;
    }
    let mut names = BTreeSet::new();
    for resource in &body.resources {
        if resource.name.is_empty()
            || !names.insert(&resource.name)
            || crate::vir::predicate_resource_fields(&unit.memory, resource.pointee).is_none()
        {
            return false;
        }
        let Ok(shape) = unit.memory.object_shape(resource.pointee) else {
            return false;
        };
        if shape.size_bytes() == 0
            || shape.size_bytes() > 4096
            || resource.initialized.len() > 32
            || !shape.variants().is_empty()
            || resource
                .initialized
                .iter()
                .any(|(start, end)| start >= end || *end > shape.size_bytes())
        {
            return false;
        }
    }
    if body.witnesses.len() > 32
        || body.witnesses.iter().any(|w| {
            let Some(resource) = body.resources.get(w.resource as usize) else {
                return true;
            };
            w.name.is_empty()
                || !names.insert(&w.name)
                || crate::vir::spec::predicate_logic_observation(
                    &unit.memory,
                    body,
                    w.resource,
                    w.offset,
                    w.ty,
                    crate::predicate_logic::ObservationTime::Current,
                )
                .is_none()
                || w.offset
                    .checked_add(
                        if matches!(
                            unit.memory.kind(w.ty.ty),
                            Some(crate::VirMemoryTypeKind::Bool)
                        ) {
                            1
                        } else {
                            8
                        },
                    )
                    .is_none_or(|end| {
                        !resource
                            .initialized
                            .iter()
                            .any(|(a, b)| *a <= w.offset && *b >= end)
                    })
        })
    {
        return false;
    }
    if body.prefixes.len() > 32
        || body.prefixes.iter().any(|p| {
            let Some(r) = body.resources.get(p.resource as usize) else {
                return true;
            };
            let Ok(shape) = unit.memory.object_shape(r.pointee) else {
                return true;
            };
            (match &p.count {
                crate::PredicatePrefixCount::Stored { offset } => {
                    crate::vir::predicate_word_access(&unit.memory, r.pointee, *offset).is_none()
                }
                crate::PredicatePrefixCount::Logical(expression) => !matches!(
                    expression.validate(
                        &body
                            .logic
                            .parameters
                            .iter()
                            .map(|p| p.ty)
                            .collect::<Vec<_>>(),
                        &body
                            .logic
                            .existentials
                            .iter()
                            .map(|w| w.ty)
                            .collect::<Vec<_>>(),
                        &|r, o, a, t| crate::vir::spec::predicate_logic_observation(
                            &unit.memory,
                            body,
                            r,
                            o,
                            a,
                            t
                        ),
                        &|r, path| crate::vir::predicate_resource_access(
                            &unit.memory,
                            body,
                            r,
                            path
                        ),
                        &mut crate::predicate_logic::LogicBudget::default(),
                    ),
                    Ok(crate::predicate_logic::LogicType::U64
                        | crate::predicate_logic::LogicType::Usize)
                ),
            }) || !shape.arrays().iter().any(|a| {
                a.extent().start_bytes() == p.array_offset
                    && a.element_access() == p.element
                    && a.length() == p.length
                    && a.stride_bytes() == p.stride
            }) || !matches!(
                unit.memory.kind(p.element.ty),
                Some(
                    crate::VirMemoryTypeKind::Bool
                        | crate::VirMemoryTypeKind::Integer(
                            crate::VirIntegerType::U64 | crate::VirIntegerType::Usize
                        )
                )
            ) || !crate::vir::prefix_bounds_valid(p, &body.bounds)
        })
    {
        return false;
    }
    for bound in &body.bounds {
        let Some(resource) = body.resources.get(bound.resource as usize) else {
            return false;
        };
        let Ok(shape) = unit.memory.object_shape(resource.pointee) else {
            return false;
        };
        if crate::vir::predicate_word_access(&unit.memory, resource.pointee, bound.offset).is_none()
            || bound.lower > bound.upper
            || bound.offset % 8 != 0
            || bound
                .offset
                .checked_add(8)
                .is_none_or(|end| end > shape.size_bytes())
        {
            return false;
        }
    }
    true
}
