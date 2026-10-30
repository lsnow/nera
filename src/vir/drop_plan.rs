//! Bounded destruction of finite owning storage. This plan contains layout,
//! never authority; each consumer checks its own actual payloads.
use super::{VirMemoryAccess, VirMemorySchema, VirObjectShape, VirPointerKind};

pub(crate) const MAX_DROP_DEPTH: usize = 16;
pub(crate) const MAX_DROP_NODES: usize = super::VIR_OBJECT_SHAPE_MAX_NODES;

#[derive(Clone, Debug)]
pub(crate) struct ObjectDropPlan {
    pub access: VirMemoryAccess,
    pub shape: VirObjectShape,
    pub children: Vec<(u64, VirMemoryAccess, ObjectDropPlan)>,
}

impl ObjectDropPlan {
    pub fn child(&self, offset: u64, access: VirMemoryAccess) -> Option<&Self> {
        self.children
            .iter()
            .find(|(o, a, _)| *o == offset && *a == access)
            .map(|(_, _, p)| p)
    }
}

impl VirMemorySchema {
    pub(crate) fn object_drop_plan(&self, access: VirMemoryAccess) -> Option<ObjectDropPlan> {
        fn build(
            memory: &VirMemorySchema,
            access: VirMemoryAccess,
            depth: usize,
            budget: &mut usize,
        ) -> Option<ObjectDropPlan> {
            if depth > MAX_DROP_DEPTH {
                return None;
            }
            *budget = budget.checked_sub(1)?;
            let shape = memory.object_shape(access).ok()?;
            *budget = budget.checked_sub(shape.resource_leaves().len())?;
            let mut children = Vec::new();
            for leaf in shape
                .resource_leaves()
                .iter()
                .filter(|l| l.kind() == VirPointerKind::Own)
            {
                // object_shape validated the canonical capability table.
                // Scalar-only pointees have no child authority to retire.
                if !memory
                    .type_capabilities(leaf.pointee_access().ty)?
                    .contains_resource
                {
                    continue;
                }
                let child = memory.object_shape(leaf.pointee_access()).ok()?;
                if child
                    .resource_leaves()
                    .iter()
                    .any(|l| l.kind() != VirPointerKind::Raw)
                {
                    children.push((
                        leaf.bytes().start_bytes(),
                        leaf.access(),
                        build(memory, leaf.pointee_access(), depth + 1, budget)?,
                    ));
                }
            }
            Some(ObjectDropPlan {
                access,
                shape,
                children,
            })
        }
        let mut budget = MAX_DROP_NODES;
        build(self, access, 0, &mut budget)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        VirAbiClass, VirLayout, VirLayoutId, VirMemoryType, VirMemoryTypeKind, VirMutability,
        VirTypeId,
    };

    fn chain(length: usize) -> VirMemorySchema {
        let mut memory = VirMemorySchema::core_u64();
        for index in 1..=length {
            let id = VirTypeId::new(index as u32);
            let layout = VirLayoutId::new(index as u32);
            memory.types.push(VirMemoryType {
                id,
                layout,
                kind: VirMemoryTypeKind::Pointer {
                    pointee: VirTypeId::new(index as u32 - 1),
                    kind: VirPointerKind::Own,
                    mutability: VirMutability::Mutable,
                },
            });
            memory.layouts.push(VirLayout {
                id: layout,
                ty: id,
                size_bytes: 8,
                alignment: 8,
                abi: VirAbiClass::Scalar,
                fields: vec![],
                variants: None,
            });
        }
        memory.assign_canonical_type_capabilities().unwrap();
        memory
    }

    #[test]
    fn finite_ownership_depth_is_bounded_and_raw_cycles_are_not_followed() {
        let depth = MAX_DROP_DEPTH + 1;
        let mut memory = chain(depth + 1);
        assert!(
            memory
                .object_drop_plan(memory.access(VirTypeId::new(depth as u32)).unwrap())
                .is_some()
        );
        let access = memory.access(VirTypeId::new(depth as u32 + 1)).unwrap();
        assert!(memory.object_drop_plan(access).is_none());
        memory.types[access.ty.index()].kind = VirMemoryTypeKind::Pointer {
            pointee: access.ty,
            kind: VirPointerKind::Own,
            mutability: VirMutability::Mutable,
        };
        memory.assign_canonical_type_capabilities().unwrap();
        memory.validate().unwrap();
        assert!(memory.object_drop_plan(access).is_none());
        memory.types[access.ty.index()].kind = VirMemoryTypeKind::Pointer {
            pointee: access.ty,
            kind: VirPointerKind::Raw,
            mutability: VirMutability::Mutable,
        };
        memory.assign_canonical_type_capabilities().unwrap();
        memory.validate().unwrap();
        assert!(memory.object_drop_plan(access).unwrap().children.is_empty());
    }
}
