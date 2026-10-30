//! Translate established Boolean histories to query-local scalar names.
//! Callers must first prove that a memory observation is readable. Equal
//! abstract values or equal addresses never supply a history here.
use crate::{VirSpecSnapshot, verifier::resource::BoolOrigin};
use std::collections::BTreeMap;

#[derive(Default)]
pub(super) struct BooleanInputs {
    origins: BTreeMap<BoolOrigin, u32>,
    pub snapshots: BTreeMap<VirSpecSnapshot, u32>,
}

impl BooleanInputs {
    pub fn bind(&mut self, snapshot: VirSpecSnapshot, origin: Option<BoolOrigin>) {
        let Some(origin) = origin else {
            return;
        };
        let identity = if let Some(identity) = self.origins.get(&origin) {
            *identity
        } else {
            // Precision limit only: no unknown identity is invented on overflow.
            if self.origins.len() >= 64 {
                return;
            }
            let identity = self.origins.len() as u32;
            self.origins.insert(origin, identity);
            identity
        };
        self.snapshots.insert(snapshot, identity);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{VirFunctionId, VirValueId};

    #[test]
    fn only_matching_histories_share_a_query_identity_and_capacity_fails_closed() {
        let function = VirFunctionId::new(0);
        let snapshot = |slot| VirSpecSnapshot::Result { function, slot };
        let origin = |id| BoolOrigin::Parameter {
            function,
            value: VirValueId::new(id),
        };
        let mut inputs = BooleanInputs::default();
        inputs.bind(snapshot(0), None);
        assert!(inputs.snapshots.is_empty());
        inputs.bind(snapshot(0), Some(origin(0)));
        inputs.bind(snapshot(1), Some(origin(0)));
        assert_eq!(
            inputs.snapshots[&snapshot(0)],
            inputs.snapshots[&snapshot(1)]
        );
        for id in 1..64 {
            inputs.bind(snapshot(id + 1), Some(origin(id)));
        }
        assert_ne!(
            inputs.snapshots[&snapshot(0)],
            inputs.snapshots[&snapshot(2)]
        );
        inputs.bind(snapshot(65), Some(origin(64)));
        assert!(!inputs.snapshots.contains_key(&snapshot(65)));
        inputs.bind(snapshot(66), Some(origin(0)));
        assert_eq!(
            inputs.snapshots[&snapshot(0)],
            inputs.snapshots[&snapshot(66)]
        );
    }
}
