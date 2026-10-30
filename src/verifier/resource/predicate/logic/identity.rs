//! Instance scope and history adaptation, separate from constraint reasoning.
use super::*;

/// Check that the proposed bound namespace belongs to this closed declaration.
fn closed_scope(
    instance: &PredicateInstance,
    target: InstanceScope,
) -> Result<InstanceScope, PredicateError> {
    let source = instance.logic_scope.ok_or(PredicateError::InvalidBinding)?;
    if !instance.folded
        || instance.opening_action.is_some()
        || source.opening != 0
        || target.opening != 0
        || source.declaration != instance.definition.id.get()
        || target.declaration != source.declaration
    {
        return Err(PredicateError::InvalidBinding);
    }
    Ok(source)
}

/// Public values are outside the existential quantifier. This check must not
/// depend on whether the private witnesses can be renamed or will be forgotten.
pub(in crate::verifier::resource::predicate) fn normalize_closed_parameters(
    instance: &PredicateInstance,
    target: InstanceScope,
    budget: &mut LogicBudget,
) -> Result<Vec<PredicateLogicValue>, PredicateError> {
    normalize_closed_parameters_with_aliases(instance, target, &BTreeMap::new(), budget)
}

/// The CFG adapter supplies capture substitutions established by surviving
/// actual aliases. This visitor only rewrites typed values; it cannot establish
/// aliasing, inspect memory, or grant resource authority.
pub(in crate::verifier::resource::predicate) fn normalize_closed_parameters_with_aliases(
    instance: &PredicateInstance,
    target: InstanceScope,
    aliases: &BTreeMap<LocalSnapshot, VirValueId>,
    budget: &mut LogicBudget,
) -> Result<Vec<PredicateLogicValue>, PredicateError> {
    let sources = aliases
        .iter()
        .map(|(snapshot, slot)| (snapshot.atom(), *slot))
        .collect();
    normalize_closed_parameters_with_sources(instance, target, &sources, budget)
}

/// Rebind only source atoms for which the CFG adapter checked an actual slot.
/// Historical scopes remain checked; foreign and opaque names are not aliases.
pub(in crate::verifier::resource::predicate) fn normalize_closed_parameters_with_sources(
    instance: &PredicateInstance,
    target: InstanceScope,
    sources: &BTreeMap<ObservationAtom, VirValueId>,
    budget: &mut LogicBudget,
) -> Result<Vec<PredicateLogicValue>, PredicateError> {
    let source = closed_scope(instance, target)?;
    // Public arguments are fixed values, not existentially quantified by this
    // package. Renaming a hidden binder must never identify different actuals.
    let mut parameters = instance.logical_parameters.clone();
    for parameter in &parameters {
        if parameter
            .value
            .capture_leaves(budget)
            .map_err(map_error)?
            .iter()
            .any(|leaf| matches!(leaf, LogicValue::Bool(None)))
        {
            return Err(PredicateError::InvalidBinding);
        }
    }
    let mut names = BTreeMap::new();
    map_logic_values(parameters.iter_mut(), budget, false, &mut |atom, _| {
        let original = atom.clone();
        let mapped = (|| {
            if let Some(value) = sources.get(atom) {
                match atom {
                    ObservationAtom::Local { .. } => {}
                    ObservationAtom::Historical {
                        scope, local: true, ..
                    }
                    | ObservationAtom::HistoricalBool {
                        scope, local: true, ..
                    } if *scope == source => {}
                    _ => return Err(PredicateError::InvalidBinding),
                }
                return Ok(ObservationAtom::Local {
                    scope: target,
                    value: *value,
                });
            }
            match atom {
                ObservationAtom::Local { .. } => return Ok(atom.clone()),
                // Immutable opaque captures may match by exact qualified identity.
                // Neither matching bounds nor reused SSA IDs erase their namespace.
                ObservationAtom::Captured { .. }
                | ObservationAtom::Historical { local: false, .. }
                | ObservationAtom::HistoricalBool { local: false, .. } => return Ok(atom.clone()),
                _ => {}
            }
            let mut atom = atom.clone();
            let scope = match &mut atom {
                ObservationAtom::Historical {
                    scope, local: true, ..
                }
                | ObservationAtom::HistoricalBool {
                    scope, local: true, ..
                } => scope,
                _ => return Err(PredicateError::InvalidBinding),
            };
            if *scope != source {
                return Err(PredicateError::InvalidBinding);
            }
            *scope = target;
            Ok(atom)
        })()?;
        // Check injectivity across the entire public vector, including two
        // distinct Boolean values or separate sides of a comparison.
        if names
            .insert(mapped.clone(), original.clone())
            .is_some_and(|old| old != original)
        {
            return Err(PredicateError::InvalidBinding);
        }
        Ok(mapped)
    })?;
    Ok(parameters)
}

/// Normalize after replacing complete, actual CFG word coordinates. Validate
/// every original atom before elimination so cancellation cannot hide an
/// invalid scope. Coordinate names must be fresh across the entire vector.
pub(in crate::verifier::resource::predicate) fn normalize_closed_parameters_with_coordinates(
    instance: &PredicateInstance,
    target: InstanceScope,
    sources: &BTreeMap<ObservationAtom, VirValueId>,
    coordinates: &[(VirValueId, AffineValue<ObservationAtom>)],
    budget: &mut LogicBudget,
) -> Result<Vec<PredicateLogicValue>, PredicateError> {
    let normalized = normalize_closed_parameters_with_sources(instance, target, sources, budget)?;
    if coordinates.is_empty() {
        return Ok(normalized);
    }
    let mut used = parameter_local_snapshots(&normalized, budget)?;
    used.extend(parameter_local_snapshots(
        &instance.logical_parameters,
        budget,
    )?);
    let mut words = Vec::new();
    for (slot, word) in coordinates {
        budget.charge(1).map_err(map_error)?;
        let snapshot = LocalSnapshot {
            scope: target,
            value: *slot,
        };
        if used.contains(&snapshot) {
            return Err(PredicateError::InvalidBinding);
        }
        words.push((snapshot.atom(), word.clone()));
    }
    let mut rebased = instance.clone();
    for value in &mut rebased.logical_parameters {
        if matches!(value.ty, LogicType::Resource(_)) {
            continue;
        }
        value.value = crate::predicate_logic::scalar_template::ScalarTemplate::rebase_capture(
            &value.value,
            &words,
            &mut |atom, _, _| Ok(atom.clone()),
            budget,
        )
        .map_err(map_error)?;
    }
    normalize_closed_parameters_with_sources(&rebased, target, sources, budget)
}

pub(in crate::verifier::resource::predicate) fn parameter_local_snapshots(
    values: &[PredicateLogicValue],
    budget: &mut LogicBudget,
) -> Result<BTreeSet<LocalSnapshot>, PredicateError> {
    let mut snapshots = BTreeSet::new();
    map_logic_values(values.to_vec().iter_mut(), budget, false, &mut |atom, _| {
        if let ObservationAtom::Local { scope, value } = atom {
            snapshots.insert(LocalSnapshot {
                scope: *scope,
                value: *value,
            });
        }
        Ok(atom.clone())
    })?;
    Ok(snapshots)
}

/// Rename only bound names; immutable captured values are never equated by
/// their numeric bounds. Failure here does not preclude existential forgetting.
pub(in crate::verifier::resource::predicate) fn normalize_closed_scope(
    instance: &PredicateInstance,
    target: InstanceScope,
    budget: &mut LogicBudget,
) -> Result<PredicateInstance, PredicateError> {
    let source = closed_scope(instance, target)?;
    normalize_closed_parameters(instance, target, budget)?;
    let mut result = instance.clone();
    map_instance_atoms(&mut result, budget, false, &mut |atom, _| {
        let mut atom = atom.clone();
        let scope = match &mut atom {
            ObservationAtom::Existential { scope, .. }
            | ObservationAtom::Historical {
                scope, local: true, ..
            }
            | ObservationAtom::HistoricalBool {
                scope, local: true, ..
            } => scope,
            // These identify an evaluation/capture, not an alpha-renamable
            // binder. Equal intervals or reused SSA numbers are insufficient.
            _ => return Err(PredicateError::InvalidBinding),
        };
        if *scope != source {
            return Err(PredicateError::InvalidBinding);
        }
        *scope = target;
        Ok(atom)
    })?;
    result.logic_scope = Some(target);
    // Do not make either predecessor's local names visible after normalization.
    result.logical_local_aliases.clear();
    Ok(result)
}

pub(in crate::verifier::resource::predicate) fn mentions_scopes(
    instance: &PredicateInstance,
    scopes: &[InstanceScope],
    budget: &mut LogicBudget,
) -> Result<bool, PredicateError> {
    budget
        .charge(1 + instance.logical_local_aliases.len())
        .map_err(map_error)?;
    let mut found = instance.logic_scope.is_some_and(|s| scopes.contains(&s))
        || instance
            .logical_local_aliases
            .values()
            .any(|s| scopes.contains(&s.scope));
    map_instance_atoms(&mut instance.clone(), budget, false, &mut |atom, _| {
        let scope = match atom {
            ObservationAtom::Existential { scope, .. }
            | ObservationAtom::Local { scope, .. }
            | ObservationAtom::Captured { scope, .. }
            | ObservationAtom::Current { scope, .. }
            | ObservationAtom::Memory { scope, .. }
            | ObservationAtom::Historical { scope, .. }
            | ObservationAtom::HistoricalBool { scope, .. } => scope,
        };
        found |= scopes.contains(scope);
        Ok(atom.clone())
    })?;
    Ok(found)
}

/// Scalar pairs have already been copied and type checked by the resource
/// boundary. Only surviving local aliases may follow that explicit mapping.
pub(in crate::verifier::resource::predicate) fn freshen_instance(
    instance: &mut PredicateInstance,
    next: &mut u64,
    scopes: &mut BTreeMap<InstanceScope, InstanceScope>,
    budget: &mut LogicBudget,
    histories: &ScalarOriginTransport,
    scalars: &[(VirValueId, VirValueId)],
) -> Result<(), PredicateError> {
    rename_instance(
        instance,
        next,
        scopes,
        budget,
        true,
        Some(histories),
        scalars,
    )
}

pub(in crate::verifier::resource::predicate) fn freshen_local_instance(
    instance: &mut PredicateInstance,
    next: &mut u64,
) -> Result<(), PredicateError> {
    rename_instance(
        instance,
        next,
        &mut BTreeMap::new(),
        &mut LogicBudget::default(),
        false,
        None,
        &[],
    )
}

fn rename_instance(
    instance: &mut PredicateInstance,
    next: &mut u64,
    scopes: &mut BTreeMap<InstanceScope, InstanceScope>,
    budget: &mut LogicBudget,
    foreign: bool,
    histories: Option<&ScalarOriginTransport>,
    scalars: &[(VirValueId, VirValueId)],
) -> Result<(), PredicateError> {
    fn rename(
        old: InstanceScope,
        next: &mut u64,
        scopes: &mut BTreeMap<InstanceScope, InstanceScope>,
        budget: &mut LogicBudget,
    ) -> Result<InstanceScope, PredicateError> {
        if let Some(scope) = scopes.get(&old) {
            return Ok(*scope);
        }
        budget.charge(1).map_err(map_error)?;
        let following = next.checked_add(1).ok_or(PredicateError::Budget)?;
        let scope = InstanceScope {
            declaration: old.declaration,
            instance: *next,
            opening: 0,
        };
        *next = following;
        scopes.insert(old, scope);
        Ok(scope)
    }
    if !instance.folded {
        return Err(PredicateError::OpenBoundary);
    }
    if let Some(scope) = instance.logic_scope {
        instance.logic_scope = Some(rename(scope, next, scopes, budget)?);
    } else if !instance.logical_witnesses.is_empty()
        || !instance.logical_parameters.is_empty()
        || !instance.logical_facts.is_empty()
    {
        return Err(PredicateError::InvalidBinding);
    }
    let local_scope = instance.logic_scope;
    let mut mapped_locals = BTreeMap::new();
    let mut aliases = Vec::new();
    for &(source, target) in scalars {
        budget.charge(1).map_err(map_error)?;
        if let Some(snapshot) = instance.logical_local_aliases.get(&source) {
            let canonical = *mapped_locals.entry(*snapshot).or_insert(target);
            aliases.push((target, *snapshot, canonical));
        }
    }
    map_instance_atoms(
        instance,
        budget,
        histories.is_some(),
        &mut |atom, budget| {
            if let ObservationAtom::Local { scope, value } = atom
                && let Some(target) = mapped_locals.get(&LocalSnapshot {
                    scope: *scope,
                    value: *value,
                })
            {
                return Ok(ObservationAtom::Local {
                    scope: rename(*scope, next, scopes, budget)?,
                    value: *target,
                });
            }
            // Already foreign histories remain opaque, even if an unrelated frame
            // happens to reuse their old root coordinates. Only a local origin on
            // the actual source side can authorize this boundary's substitution.
            if let (Some(histories), Some(mut scope)) = (histories, local_scope) {
                scope.opening = 0;
                match atom {
                    ObservationAtom::Historical {
                        cell, local: true, ..
                    } => {
                        if let Some(cell) = histories.mapped_word(*cell) {
                            return Ok(ObservationAtom::Historical {
                                scope,
                                cell,
                                local: true,
                            });
                        }
                    }
                    ObservationAtom::HistoricalBool {
                        origin,
                        local: true,
                        ..
                    } => {
                        if let Some(origin) = histories.mapped_bool(*origin) {
                            return Ok(ObservationAtom::HistoricalBool {
                                scope,
                                origin,
                                local: true,
                            });
                        }
                    }
                    _ => {}
                }
            }
            // Foreign SSA identities never become local identities on return.
            let mut atom = match atom {
                ObservationAtom::Local { scope, value } if foreign => ObservationAtom::Captured {
                    scope: *scope,
                    value: *value,
                },
                ObservationAtom::HistoricalBool { scope, origin, .. } if foreign => {
                    ObservationAtom::HistoricalBool {
                        scope: *scope,
                        origin: *origin,
                        local: false,
                    }
                }
                ObservationAtom::Historical { scope, cell, .. } if foreign => {
                    ObservationAtom::Historical {
                        scope: *scope,
                        cell: *cell,
                        local: false,
                    }
                }
                other => other.clone(),
            };
            let scope = match &mut atom {
                ObservationAtom::Existential { scope, .. }
                | ObservationAtom::Local { scope, .. }
                | ObservationAtom::Captured { scope, .. }
                | ObservationAtom::Current { scope, .. }
                | ObservationAtom::Memory { scope, .. }
                | ObservationAtom::Historical { scope, .. }
                | ObservationAtom::HistoricalBool { scope, .. } => scope,
            };
            *scope = rename(*scope, next, scopes, budget)?;
            Ok(atom)
        },
    )?;
    instance.opening_action = None;
    if foreign {
        instance.logical_local_aliases.clear();
        for (target, snapshot, canonical) in aliases {
            instance.logical_local_aliases.insert(
                target,
                LocalSnapshot {
                    scope: rename(snapshot.scope, next, scopes, budget)?,
                    value: canonical,
                },
            );
        }
    } else {
        for snapshot in instance.logical_local_aliases.values_mut() {
            budget.charge(1).map_err(map_error)?;
            snapshot.scope = rename(snapshot.scope, next, scopes, budget)?;
        }
    }
    Ok(())
}

/// Both scope freshening and checked memory transport visit every retained
/// atom, including atoms nested in Boolean comparisons and saved facts.
fn map_instance_atoms(
    instance: &mut PredicateInstance,
    budget: &mut LogicBudget,
    merge_aliases: bool,
    map: &mut impl FnMut(&ObservationAtom, &mut LogicBudget) -> Result<ObservationAtom, PredicateError>,
) -> Result<(), PredicateError> {
    map_logic_values(
        instance
            .logical_witnesses
            .iter_mut()
            .chain(&mut instance.logical_parameters)
            .chain(
                instance
                    .logical_initialization
                    .iter_mut()
                    .map(|fact| &mut fact.count),
            )
            .chain(
                instance
                    .logical_facts
                    .iter_mut()
                    .flat_map(|fact| fact.leaves.iter_mut().map(|(_, v)| v)),
            ),
        budget,
        merge_aliases,
        map,
    )
}

fn map_logic_values<'a>(
    values: impl Iterator<Item = &'a mut PredicateLogicValue>,
    budget: &mut LogicBudget,
    merge_aliases: bool,
    map: &mut impl FnMut(&ObservationAtom, &mut LogicBudget) -> Result<ObservationAtom, PredicateError>,
) -> Result<(), PredicateError> {
    for witness in values {
        budget.charge(1).map_err(map_error)?;
        for leaf in witness
            .value
            .capture_leaves_mut(budget)
            .map_err(map_error)?
        {
            let words: Vec<&mut AffineValue<ObservationAtom>> = match leaf {
                LogicValue::Word(word) => vec![word],
                LogicValue::BoolComparison { left, right, .. } => vec![left, right],
                LogicValue::BoolAtom { atom, .. } | LogicValue::ResourceAtom { atom } => {
                    budget.charge(1).map_err(map_error)?;
                    *atom = map(atom, budget)?;
                    vec![]
                }
                _ => vec![],
            };
            for word in words {
                let mut terms = BTreeMap::<ObservationAtom, i128>::new();
                for (atom, coefficient) in &word.terms {
                    budget.charge(1).map_err(map_error)?;
                    let atom = map(atom, budget)?;
                    if terms.contains_key(&atom) {
                        // Only the checked memory map establishes new aliases.
                        // Scope freshening must remain injective for every other
                        // atom, including Local -> Captured conversions.
                        let transported = matches!(&atom,
                        ObservationAtom::Historical { cell, local: true, .. }
                            if matches!(cell.root, ScalarOriginRoot::Transported(_)));
                        if !merge_aliases || !transported {
                            return Err(PredicateError::InvalidBinding);
                        }
                    }
                    let entry = terms.entry(atom).or_default();
                    *entry = entry
                        .checked_add(*coefficient)
                        .ok_or(PredicateError::Budget)?;
                }
                terms.retain(|_, coefficient| *coefficient != 0);
                word.terms = terms;
            }
        }
    }
    Ok(())
}
