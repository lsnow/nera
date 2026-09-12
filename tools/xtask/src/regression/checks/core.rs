use std::{error::Error, path::Path};

pub(in crate::regression) fn check_place_regression(_root: &Path) -> Result<(), Box<dyn Error>> {
    Ok(())
}

pub(in crate::regression) fn check_control_flow_regression(
    _root: &Path,
) -> Result<(), Box<dyn Error>> {
    Ok(())
}

pub(in crate::regression) fn check_vir_unit_regression(_root: &Path) -> Result<(), Box<dyn Error>> {
    Ok(())
}

pub(in crate::regression) fn check_aggregate_regression(
    _root: &Path,
) -> Result<(), Box<dyn Error>> {
    Ok(())
}
