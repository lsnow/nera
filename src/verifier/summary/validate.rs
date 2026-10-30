use super::*;
use crate::{VirMemorySchema, VirMemoryTypeKind};
use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SummaryValidationError {
    Version,
    Binding,
    State,
    Signature,
    Evidence,
    Value,
    Resource,
    Path,
    Guard,
    Return,
}
impl fmt::Display for SummaryValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "invalid summary structure: {self:?}")
    }
}
impl std::error::Error for SummaryValidationError {}
type Result<T = ()> = std::result::Result<T, SummaryValidationError>;

pub(super) fn validate(
    summary: &FunctionSummary,
    program: &ResolvedVirUnit<'_>,
    function: VirFunctionId,
    config: CfgAnalysisConfig,
) -> Result {
    use SummaryValidationError as E;
    if summary.recursion != summary.recursion_shape {
        return Err(E::Evidence);
    }
    if summary.state == SummaryState::Closed && !summary.audit_complete {
        return Err(E::Evidence);
    }
    if summary.version != SUMMARY_SCHEMA_VERSION
        || summary.verifier_profile != SUMMARY_VERIFIER_PROFILE
    {
        return Err(E::Version);
    }
    if summary.binding != SummaryBinding::new(SummaryBinding::unit(program), function, config) {
        return Err(E::Binding);
    }
    let function = program
        .runtime()
        .functions
        .iter()
        .find(|f| f.id == function)
        .ok_or(E::Binding)?;
    if summary.parameters != function.signature.parameters
        || summary.results != function.signature.results
    {
        return Err(E::Signature);
    }
    let expected = dependencies(program, function, &summary.binding);
    if summary
        .dependencies
        .iter()
        .map(|d| &d.binding)
        .ne(expected.iter().map(|d| &d.binding))
        || summary
            .dependencies
            .iter()
            .map(|d| &d.state)
            .ne(summary.dependency_states.iter())
    {
        return Err(E::Binding);
    }
    // Only private publication can issue Closed; DTO mutation cannot mint it.
    match &summary.state {
        SummaryState::Closed if !summary.closed => return Err(E::State),
        SummaryState::Uncomputed | SummaryState::Hypothesis => return Err(E::State),
        SummaryState::Unknown(losses) if losses.is_empty() => return Err(E::State),
        SummaryState::Candidate
            if summary
                .faults
                .requirements
                .iter()
                .any(|r| !r.status.is_proven()) =>
        {
            return Err(E::State);
        }
        _ => {}
    }
    if summary.state != summary.projected_state {
        return Err(E::State);
    }
    if summary.faults.requirements != summary.evidence_shape {
        return Err(E::Evidence);
    }
    // Mutation cannot turn observed writes into an empty frame or manufacture
    // a fault whitelist. Structural validity alone still grants no authority.
    if summary.effects != summary.effects_shape
        || summary.faults.runtime_faults != Knowledge::Unknown
    {
        return Err(E::State);
    }
    let cx = Validator {
        summary,
        memory: program.runtime().memory,
    };
    let names = cx.resources(&summary.input_resources, true)?;
    if summary
        .input_resources
        .iter()
        .map(|r| r.name.clone())
        .collect::<Vec<_>>()
        != summary.input_shape
    {
        return Err(E::Resource);
    }
    cx.values(
        &summary.inputs,
        &summary.parameters,
        ValueEpoch::Pre,
        true,
        &names,
    )?;
    let Knowledge::Known(alternatives) = &summary.normal_returns else {
        return Err(E::Return);
    };
    let mut returns = BTreeSet::new();
    for alternative in alternatives {
        if alternative.worlds.is_empty() {
            return Err(E::Return);
        }
        for guard in &alternative.guard {
            cx.guard(guard)?;
        }
        for world in &alternative.worlds {
            if world.return_evidence >= summary.return_count
                || !returns.insert(world.return_evidence)
            {
                return Err(E::Evidence);
            }
            let names = cx.resources(&world.resources, false)?;
            if summary.return_guards.get(world.return_evidence) != Some(&alternative.guard) {
                return Err(E::Guard);
            }
            for input in &summary.input_shape {
                if !names.contains(input) {
                    return Err(E::Resource);
                }
            }
            cx.values(
                &world.values,
                &summary.results,
                ValueEpoch::Post,
                false,
                &names,
            )?;
            if world.bool_value_origins.len() != world.values.len() {
                return Err(E::Return);
            }
            for (value, origin) in world.values.iter().zip(&world.bool_value_origins) {
                if let Some(origin) = origin {
                    let SummaryValue::Bool(value) = value.value else {
                        return Err(E::Value);
                    };
                    cx.bool_origin(origin, value)?;
                }
            }
            if world.value_origins.len() != world.values.len() {
                return Err(E::Return);
            }
            for (value, origin) in world.values.iter().zip(&world.value_origins) {
                if let Some(origin) = origin {
                    let SummaryValue::Word { interval, .. } = &value.value else {
                        return Err(E::Value);
                    };
                    cx.scalar_origin(origin, *interval)?;
                }
            }
            if let Knowledge::Known(values) = &world.post_inputs {
                cx.values(values, &summary.parameters, ValueEpoch::Post, true, &names)?;
            }
            let mut restores = BTreeSet::new();
            for restore in &world.borrow_restoration {
                if !restores.insert(restore.input_permission)
                    || summary.parameters.get(restore.input_permission)
                        != Some(&VirType::Permission)
                {
                    return Err(E::Resource);
                }
                cx.permission(&restore.permission, &names)?;
            }
            let expected = summary
                .input_resources
                .iter()
                .flat_map(|r| &r.payloads)
                .filter_map(|p| match &p.state {
                    SummaryMovePath::Available { permission, .. } => match &permission.authority {
                        SummaryAuthority::InputPayloadLoan(path) => Some(path.clone()),
                        _ => None,
                    },
                    _ => None,
                })
                .collect::<BTreeSet<_>>();
            let mut restored = BTreeSet::new();
            for restore in &world.stored_borrow_restoration {
                if !expected.contains(&restore.input) || !restored.insert(restore.input.clone()) {
                    return Err(E::Resource);
                }
                let authority = SummaryAuthority::InputPayloadLoan(restore.input.clone());
                let carriers = world.resources.iter().flat_map(|r| r.payloads.iter().filter(|&p| matches!(&p.state, SummaryMovePath::Available { permission, .. } if permission.authority == authority)).map(|p| StoredBorrowLocation { resource: r.name.clone(), offset: p.offset, access: p.access })).collect::<Vec<_>>();
                let ssa = world
                    .values
                    .iter()
                    .enumerate()
                    .filter_map(|(slot, v)| {
                        matches!(&v.value, SummaryValue::Permission(p) if p.authority == authority)
                            .then_some(slot)
                    })
                    .collect::<Vec<_>>();
                let valid = match &restore.exit {
                    crate::BoundaryExit::Value(slot) => {
                        carriers.is_empty()
                            && ssa == [*slot]
                            && program
                                .runtime()
                                .abis
                                .function(function.id)
                                .and_then(|a| {
                                    super::borrow::field_return_slots(
                                        program.runtime().memory,
                                        &a.signature,
                                        &restore.input,
                                    )
                                })
                                .is_some_and(|(_, permission)| permission == *slot)
                    }
                    crate::BoundaryExit::Shared { stored, values } => {
                        let reference = super::borrow::input_payload_field(
                            program.runtime().memory,
                            &summary.parameters,
                            &restore.input,
                        );
                        let mut observed = carriers.clone();
                        observed.sort();
                        matches!(
                            reference.and_then(|a| program.runtime().memory.kind(a.ty)),
                            Some(crate::VirMemoryTypeKind::Pointer {
                                kind: crate::VirPointerKind::Reference,
                                mutability: crate::VirMutability::Const,
                                ..
                            })
                        ) && stored.len() + values.len() > 1
                            && stored.windows(2).all(|w| w[0] < w[1])
                            && values.windows(2).all(|w| w[0] < w[1])
                            && *stored == observed
                            && *values == ssa
                            && values.iter().all(|slot| {
                                program
                                    .runtime()
                                    .abis
                                    .function(function.id)
                                    .and_then(|a| {
                                        super::borrow::field_return_slots(
                                            program.runtime().memory,
                                            &a.signature,
                                            &restore.input,
                                        )
                                    })
                                    .is_some_and(|(_, permission)| permission == *slot)
                            })
                    }
                    _ => {
                        ssa.is_empty()
                            && valid_stored_exit(&restore.input, &restore.exit, &carriers)
                    }
                };
                if !valid {
                    return Err(E::Resource);
                }
            }
            if restored != expected {
                return Err(E::Resource);
            }
        }
    }
    if returns.len() != summary.return_count {
        return Err(E::Return);
    }
    if alternatives
        .iter()
        .flat_map(|a| &a.worlds)
        .collect::<Vec<_>>()
        != summary.world_shapes.iter().collect::<Vec<_>>()
    {
        return Err(E::Return);
    }
    Ok(())
}
struct Validator<'a> {
    summary: &'a FunctionSummary,
    memory: &'a VirMemorySchema,
}
impl Validator<'_> {
    fn bool_origin(&self, origin: &SummaryScalarRoot, output: AbstractBool) -> Result {
        use SummaryValidationError as E;
        let input = match origin {
            SummaryScalarRoot::Parameter(slot) => {
                if self.summary.parameters.get(*slot) != Some(&VirType::Bool) {
                    return Err(E::Resource);
                }
                self.summary
                    .inputs
                    .iter()
                    .find_map(|v| match (&v.coordinate, &v.value) {
                        (
                            ValueReference {
                                epoch: ValueEpoch::Pre,
                                coordinate: ValueCoordinate::Parameter(p),
                            },
                            SummaryValue::Bool(b),
                        ) if p == slot => Some(*b),
                        _ => None,
                    })
                    .ok_or(E::Resource)?
            }
            SummaryScalarRoot::Cell {
                resource,
                bytes,
                access,
            } => {
                if !matches!(resource, ResourceName::Input { .. }) {
                    return Err(E::Resource);
                }
                self.summary
                    .input_resources
                    .iter()
                    .find(|r| &r.name == resource)
                    .and_then(|r| {
                        r.scalar_contents.iter().find_map(|(b, a, v)| match v {
                            super::super::AbstractValue::Bool(value)
                                if b == bytes && a == access =>
                            {
                                Some(*value)
                            }
                            _ => None,
                        })
                    })
                    .ok_or(E::Resource)?
            }
        };
        if matches!(
            (input, output),
            (AbstractBool::True, AbstractBool::False) | (AbstractBool::False, AbstractBool::True)
        ) {
            return Err(E::Resource);
        }
        Ok(())
    }
    fn scalar_origin(&self, origin: &SummaryScalarOrigin, output: U64Interval) -> Result {
        use SummaryValidationError as E;
        let mut lower = origin.addend;
        let mut upper = origin.addend;
        let mut cells = BTreeSet::new();
        for source in origin.sources() {
            if source.scale == 0 || !cells.insert(source.root.clone()) {
                return Err(E::Resource);
            }
            let input = match source.root {
                SummaryScalarRoot::Parameter(slot) => {
                    if self.summary.parameters.get(slot) != Some(&VirType::U64) {
                        return Err(E::Resource);
                    }
                    self.summary
                        .inputs
                        .iter()
                        .find_map(|input| match (&input.coordinate, &input.value) {
                            (
                                ValueReference {
                                    epoch: ValueEpoch::Pre,
                                    coordinate: ValueCoordinate::Parameter(p),
                                },
                                SummaryValue::Word { interval, .. },
                            ) if *p == slot => Some(*interval),
                            _ => None,
                        })
                        .ok_or(E::Resource)?
                }
                SummaryScalarRoot::Cell {
                    resource,
                    bytes,
                    access,
                } => {
                    if !matches!(resource, ResourceName::Input { .. }) {
                        return Err(E::Resource);
                    }
                    self.summary
                        .input_resources
                        .iter()
                        .find(|r| r.name == resource)
                        .and_then(|r| {
                            r.scalar_contents.iter().find_map(|(b, a, v)| match v {
                                super::super::AbstractValue::U64(value)
                                    if *b == bytes && *a == access =>
                                {
                                    Some(*value)
                                }
                                _ => None,
                            })
                        })
                        .ok_or(E::Resource)?
                }
            };
            lower = lower
                .checked_add(input.lower().checked_mul(source.scale).ok_or(E::Resource)?)
                .ok_or(E::Resource)?;
            upper = upper.saturating_add(input.upper().saturating_mul(source.scale));
        }
        if lower > output.upper() || upper < output.lower() {
            return Err(E::Resource);
        }

        Ok(())
    }

    fn resources(
        &self,
        resources: &[ResourcePostState],
        input: bool,
    ) -> Result<BTreeSet<ResourceName>> {
        use SummaryValidationError as E;
        let names = resources
            .iter()
            .map(|r| r.name.clone())
            .collect::<BTreeSet<_>>();
        if names.len() != resources.len() {
            return Err(E::Resource);
        }
        let mut fresh = BTreeSet::new();
        for resource in resources {
            if matches!(resource.name, ResourceName::Input { .. })
                != (resource.storage == ResourceStorage::Input)
            {
                return Err(E::Resource);
            }
            match &resource.name {
                ResourceName::Input {
                    parameter,
                    payload_offsets,
                } => {
                    if !matches!(
                        self.summary.parameters.get(*parameter),
                        Some(VirType::Pointer { .. } | VirType::Permission)
                    ) || payload_offsets.len() > crate::vir::VIR_OBJECT_SHAPE_MAX_DEPTH
                    {
                        return Err(E::Resource);
                    }
                }
                ResourceName::Fresh(index) if !input => {
                    fresh.insert(*index);
                }
                _ => return Err(E::Resource),
            }
            if !resource.alignment.is_power_of_two() {
                return Err(E::Resource);
            }
            for bytes in [
                resource.initialization.initialized(),
                resource.initialization.uninitialized(),
                &resource.validity,
            ] {
                if bytes.ranges().iter().any(|r| r.end() > resource.size) {
                    return Err(E::Resource);
                }
            }
            if !resource
                .initialization
                .initialized()
                .is_disjoint(resource.initialization.uninitialized())
            {
                return Err(E::Resource);
            }
            if resource.scalar_contents.len() > 64 {
                return Err(E::Resource);
            }
            let mut cells = Vec::new();
            for (range, access, value) in &resource.scalar_contents {
                self.location(range.start(), *access, resource.size)?;
                if resource.liveness != LivenessState::Live
                    || self
                        .memory
                        .layout(access.layout)
                        .is_none_or(|l| l.size_bytes != (range.end() - range.start()))
                    || !resource.initialization.initialized().contains(*range)
                    || !resource.validity.contains(*range)
                    || cells.iter().any(|cell: &ByteRange| cell.overlaps(*range))
                    || !matches!(
                        (value, self.memory.kind(access.ty)),
                        (
                            super::super::AbstractValue::Bool(_),
                            Some(VirMemoryTypeKind::Bool)
                        ) | (
                            super::super::AbstractValue::U64(_),
                            Some(VirMemoryTypeKind::Integer(
                                crate::VirIntegerType::U64 | crate::VirIntegerType::Usize
                            ))
                        )
                    )
                {
                    return Err(E::Resource);
                }
                cells.push(*range);
            }
            if resource.bool_origins.len() > 64 {
                return Err(E::Resource);
            }
            let mut bool_cells = BTreeSet::new();
            for (bytes, access, origin) in &resource.bool_origins {
                if !bool_cells.insert((*bytes, *access)) {
                    return Err(E::Resource);
                }
                let value = resource
                    .scalar_contents
                    .iter()
                    .find_map(|(b, a, v)| match v {
                        super::super::AbstractValue::Bool(value) if b == bytes && a == access => {
                            Some(*value)
                        }
                        _ => None,
                    })
                    .ok_or(E::Resource)?;
                self.bool_origin(origin, value)?;
            }
            if resource.scalar_origins.len() > 64 {
                return Err(E::Resource);
            }
            let mut origin_cells = BTreeSet::new();
            for (bytes, access, origin) in &resource.scalar_origins {
                if !origin_cells.insert((*bytes, *access))
                    || !resource.scalar_contents.iter().any(|(b, a, v)| {
                        b == bytes
                            && a == access
                            && matches!(v, super::super::AbstractValue::U64(_))
                    })
                {
                    return Err(E::Resource);
                }
                let output = resource
                    .scalar_contents
                    .iter()
                    .find_map(|(b, a, v)| match v {
                        super::super::AbstractValue::U64(value) if b == bytes && a == access => {
                            Some(*value)
                        }
                        _ => None,
                    })
                    .ok_or(E::Resource)?;
                self.scalar_origin(origin, output)?;
            }
            let mut paths = BTreeSet::new();
            for variant in &resource.variants {
                self.location(variant.offset, variant.access, resource.size)?;
                if !paths.insert((variant.offset, variant.access)) {
                    return Err(E::Path);
                }
                let Some(VirMemoryTypeKind::Enum { variants }) =
                    self.memory.kind(variant.access.ty)
                else {
                    return Err(E::Path);
                };
                if let Knowledge::Known(active) = &variant.alternatives
                    && (active.is_empty()
                        || active.iter().collect::<BTreeSet<_>>().len() != active.len()
                        || active.iter().any(|v| !variants.contains(v)))
                {
                    return Err(E::Path);
                }
            }
            paths.clear();
            for payload in &resource.payloads {
                self.location(payload.offset, payload.access, resource.size)?;
                if !paths.insert((payload.offset, payload.access)) {
                    return Err(E::Path);
                }
                if !matches!(
                    self.memory.kind(payload.access.ty),
                    Some(VirMemoryTypeKind::Pointer { .. })
                ) {
                    return Err(E::Path);
                }
                if let SummaryMovePath::Available {
                    pointer,
                    permission,
                } = &payload.state
                {
                    self.pointer(pointer, &names)?;
                    self.permission(permission, &names)?;
                    if matches!(permission.authority, SummaryAuthority::InputPayloadLoan(_))
                        && !super::borrow::stored_reference_shape(
                            self.memory,
                            payload.access,
                            pointer.access,
                            permission.access,
                            permission.free,
                        )
                    {
                        return Err(E::Resource);
                    }
                    if let (Knowledge::Known(a), Knowledge::Known(b)) =
                        (&pointer.resource, &permission.resource)
                        && a != b
                    {
                        return Err(E::Resource);
                    }
                }
            }
        }
        if fresh.iter().copied().ne(0..fresh.len()) {
            return Err(E::Resource);
        }
        Ok(names)
    }
    fn location(&self, offset: u64, access: VirMemoryAccess, size: u64) -> Result {
        if !self.memory.resolves_access(access) {
            return Err(SummaryValidationError::Path);
        }
        let bytes = self.memory.layout(access.layout).unwrap().size_bytes;
        if offset.checked_add(bytes).is_none_or(|end| end > size) {
            return Err(SummaryValidationError::Path);
        }
        Ok(())
    }
    fn resource(
        &self,
        resource: &Knowledge<ResourceName>,
        names: &BTreeSet<ResourceName>,
    ) -> Result {
        if let Knowledge::Known(name) = resource
            && !names.contains(name)
        {
            return Err(SummaryValidationError::Resource);
        }
        Ok(())
    }
    fn bound(&self, bound: &SummaryBound) -> Result {
        let mut seen = BTreeSet::new();
        for (parameter, scale) in &bound.terms {
            if *scale == 0
                || !seen.insert(*parameter)
                || self.summary.parameters.get(*parameter) != Some(&VirType::U64)
            {
                return Err(SummaryValidationError::Value);
            }
        }
        let mut seen = BTreeSet::new();
        for (result, scale) in &bound.result_offset_terms {
            if *scale == 0
                || !seen.insert(*result)
                || !matches!(
                    self.summary.results.get(*result),
                    Some(VirType::Pointer { .. })
                )
            {
                return Err(SummaryValidationError::Value);
            }
        }
        let mut seen = BTreeSet::new();
        for (result, scale) in &bound.result_terms {
            if *scale == 0
                || !seen.insert(*result)
                || self.summary.results.get(*result) != Some(&VirType::U64)
            {
                return Err(SummaryValidationError::Value);
            }
        }
        Ok(())
    }
    fn range(&self, range: &SummaryRange) -> Result {
        if let SummaryRange::Symbolic { start, end } = range {
            self.bound(start)?;
            self.bound(end)?;
        }
        Ok(())
    }
    fn path(&self, path: &SummaryPath) -> Result {
        if let Some((index, role)) = path.parameter
            && (role > 2
                || self.summary.parameters.get(index)
                    != Some(&VirType::Pointer {
                        access: path.access,
                    }))
        {
            return Err(SummaryValidationError::Path);
        }
        if self.memory.subobject(path.access, &path.steps).is_none() {
            return Err(SummaryValidationError::Path);
        }
        Ok(())
    }
    fn pointer(&self, pointer: &SummaryPointer, names: &BTreeSet<ResourceName>) -> Result {
        self.resource(&pointer.resource, names)?;
        if let Some(bound) = &pointer.offset_expression {
            self.bound(bound)?;
        }
        if !pointer.alignment.is_power_of_two()
            || pointer
                .access
                .is_some_and(|a| !self.memory.resolves_access(a))
        {
            return Err(SummaryValidationError::Path);
        }
        if let SummaryDomain::Restricted(range) = &pointer.domain {
            self.range(range)?;
        }
        for path in [&pointer.object_path, &pointer.domain_path]
            .into_iter()
            .flatten()
        {
            self.path(path)?;
        }
        if let Some(range) = &pointer.slice_range {
            self.range(range)?;
        }
        Ok(())
    }
    fn permission(&self, permission: &SummaryPermission, names: &BTreeSet<ResourceName>) -> Result {
        self.resource(&permission.resource, names)?;
        self.range(&permission.range)?;
        if let SummaryAuthority::InputLoan(index) = permission.authority
            && self.summary.parameters.get(index) != Some(&VirType::Permission)
        {
            return Err(SummaryValidationError::Resource);
        }
        if let SummaryAuthority::InputPayloadLoan(path) = &permission.authority {
            let field =
                super::borrow::input_payload_field(self.memory, &self.summary.parameters, path)
                    .ok_or(SummaryValidationError::Resource)?;
            let ResourceName::Input {
                parameter,
                payload_offsets,
            } = path
            else {
                return Err(SummaryValidationError::Resource);
            };
            if payload_offsets.is_empty()
                || payload_offsets.len() > 16
                || !matches!(
                    self.summary.parameters.get(*parameter),
                    Some(VirType::Pointer { .. })
                )
                || permission.free != FreeCapability::No
            {
                return Err(SummaryValidationError::Resource);
            }
            let mut parent = payload_offsets.clone();
            let offset = parent.pop().unwrap();
            let parent = ResourceName::Input {
                parameter: *parameter,
                payload_offsets: parent,
            };
            let resource = self
                .summary
                .input_resources
                .iter()
                .find(|r| r.name == parent)
                .ok_or(SummaryValidationError::Resource)?;
            let mut payloads = resource.payloads.iter().filter(|p| p.offset == offset);
            let payload = payloads.next().ok_or(SummaryValidationError::Resource)?;
            let SummaryMovePath::Available {
                pointer,
                permission: input,
            } = &payload.state
            else {
                return Err(SummaryValidationError::Resource);
            };
            if payloads.next().is_some()
                || payload.access != field
                || !matches!(
                    self.memory.kind(payload.access.ty),
                    Some(VirMemoryTypeKind::Pointer {
                        kind: crate::VirPointerKind::Reference,
                        ..
                    })
                )
                || input.authority != permission.authority
                || input.free != FreeCapability::No
                || pointer.resource != permission.resource
                || input.resource != permission.resource
                || (input.access != permission.access && input.access != AccessPermission::Write)
            {
                return Err(SummaryValidationError::Resource);
            }
        }
        Ok(())
    }
    fn values(
        &self,
        values: &[ValueMapping],
        types: &[VirType],
        epoch: ValueEpoch,
        input: bool,
        names: &BTreeSet<ResourceName>,
    ) -> Result {
        use SummaryValidationError as E;
        if values.len() != types.len() {
            return Err(E::Value);
        }
        for (index, (mapping, ty)) in values.iter().zip(types).enumerate() {
            let coordinate = if input {
                ValueCoordinate::Parameter(index)
            } else {
                ValueCoordinate::Result(index)
            };
            if mapping.coordinate != (ValueReference { epoch, coordinate }) {
                return Err(E::Value);
            }
            match (&mapping.value, ty) {
                (SummaryValue::Word { expression, .. }, VirType::U64) => {
                    if let Some(bound) = expression {
                        self.bound(bound)?;
                    }
                }
                (SummaryValue::Bool(_), VirType::Bool) => {}
                (SummaryValue::Pointer(pointer), VirType::Pointer { access }) => {
                    if pointer.access.is_some_and(|a| a != *access) {
                        return Err(E::Value);
                    }
                    self.pointer(pointer, names)?;
                }
                (SummaryValue::Permission(permission), VirType::Permission) => {
                    self.permission(permission, names)?
                }
                _ => return Err(E::Value),
            }
        }
        Ok(())
    }
    fn guard(&self, guard: &SummaryGuard) -> Result {
        match guard {
            SummaryGuard::Boolean { parameter, .. }
                if self.summary.parameters.get(*parameter) != Some(&VirType::Bool) =>
            {
                return Err(SummaryValidationError::Guard);
            }
            SummaryGuard::Compare { left, right, .. } => {
                for term in [left, right] {
                    if let ScalarTerm::Input(index) = term
                        && self.summary.parameters.get(*index) != Some(&VirType::U64)
                    {
                        return Err(SummaryValidationError::Guard);
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }
}

/// This validates the declared disposition against observed world carriers;
/// it does not infer a destination and is independent of the projector.
fn valid_stored_exit(
    input: &ResourceName,
    exit: &crate::BoundaryExit<StoredBorrowLocation, usize>,
    carriers: &[StoredBorrowLocation],
) -> bool {
    match exit {
        crate::BoundaryExit::Ended => carriers.is_empty(),
        crate::BoundaryExit::InPlace => {
            matches!(carriers, [location] if super::borrow::is_input_location(input, location))
        }
        crate::BoundaryExit::Stored(destination) => {
            matches!(carriers, [location] if location == destination)
                && !super::borrow::is_input_location(input, destination)
        }
        crate::BoundaryExit::Value(_) | crate::BoundaryExit::Shared { .. } => false,
    }
}

#[cfg(test)]
mod boundary_tests {
    #[test]
    fn shared_exit_claims_match_all_real_carriers_without_relying_on_the_seal() {
        for (source, name) in [
            (
                include_str!(concat!(
                    env!("CARGO_MANIFEST_DIR"),
                    "/spec/cases/verify/predicate-shared-field-exit.nera"
                )),
                "get",
            ),
            (
                include_str!(concat!(
                    env!("CARGO_MANIFEST_DIR"),
                    "/spec/cases/verify/predicate-shared-field-copies.nera"
                )),
                "duplicate",
            ),
        ] {
            let output =
                crate::analyze(&crate::SourceFile::from_text("shared-summary.nera", source));
            let unit = output.vir().unwrap().resolve().unwrap();
            let report = crate::verify_program(&unit, Default::default()).unwrap();
            assert!(report.is_memory_checked_core0());
            let id = unit
                .runtime()
                .functions
                .iter()
                .find(|f| f.name == name)
                .unwrap()
                .id;
            let original = report.functions()[&id].summary();
            original
                .validate_structure(&unit, id, Default::default())
                .unwrap();
            for mutation in 0..7 {
                let mut changed = original.clone();
                let Knowledge::Known(returns) = &mut changed.normal_returns else {
                    panic!("closed summary");
                };
                let restores = &mut returns[0].worlds[0].stored_borrow_restoration;
                let exit = &mut restores[0].exit;
                let crate::BoundaryExit::Shared { stored, values } = exit else {
                    panic!("multiple carriers");
                };
                match mutation {
                    0 => {
                        stored.pop();
                    }
                    1 => {
                        stored.push(stored[0].clone());
                    }
                    2 => {
                        values.push(usize::MAX);
                    }
                    3 => {
                        stored[0].offset += 8;
                    }
                    4 => {
                        stored[0].resource = ResourceName::Fresh(usize::MAX);
                    }
                    5 => {
                        *exit = crate::BoundaryExit::Ended;
                    }
                    6 => {
                        restores.push(restores[0].clone());
                    }
                    _ => unreachable!(),
                }
                // Keep the private evidence mirror consistent, so rejection
                // must come from authority/schema checks, not mirror mismatch.
                changed.world_shapes = returns
                    .iter()
                    .flat_map(|a| a.worlds.iter().cloned())
                    .collect();
                assert_eq!(
                    changed.validate_structure(&unit, id, Default::default()),
                    Err(SummaryValidationError::Resource),
                    "{name} mutation {mutation}"
                );
            }
        }
    }

    use super::*;
    #[test]
    fn disposition_must_name_the_actual_unique_carrier() {
        let output = crate::analyze(&crate::SourceFile::from_text(
            "boundary.nera",
            "fn main()->u64{return 0;}",
        ));
        let memory = &output.vir().unwrap().as_unit().memory;
        let access = memory.access(memory.types[0].id).unwrap();
        // Only disposition coordinates are tested here. Typed resource leaves
        // and actual loan authority are checked separately by the validator.
        let input = ResourceName::Input {
            parameter: 2,
            payload_offsets: vec![8, 16],
        };
        let source = StoredBorrowLocation {
            resource: ResourceName::Input {
                parameter: 2,
                payload_offsets: vec![8],
            },
            offset: 16,
            access,
        };
        let target = StoredBorrowLocation {
            resource: ResourceName::Fresh(1),
            offset: 24,
            access,
        };
        assert!(valid_stored_exit(
            &input,
            &crate::BoundaryExit::InPlace,
            std::slice::from_ref(&source)
        ));
        assert!(valid_stored_exit(
            &input,
            &crate::BoundaryExit::Stored(target.clone()),
            std::slice::from_ref(&target)
        ));
        assert!(valid_stored_exit(&input, &crate::BoundaryExit::Ended, &[]));
        for exit in [
            crate::BoundaryExit::InPlace,
            crate::BoundaryExit::Stored(source.clone()),
            crate::BoundaryExit::Value(0),
            crate::BoundaryExit::Ended,
        ] {
            assert!(!valid_stored_exit(
                &input,
                &exit,
                std::slice::from_ref(&target)
            ));
            assert!(!valid_stored_exit(
                &input,
                &exit,
                &[target.clone(), target.clone()]
            ));
        }
        assert!(!valid_stored_exit(
            &input,
            &crate::BoundaryExit::Stored(source.clone()),
            &[source]
        ));
        assert!(!valid_stored_exit(
            &input,
            &crate::BoundaryExit::Stored(target),
            &[]
        ));
    }
}
