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
