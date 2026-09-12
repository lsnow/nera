//! Resolution of the one closed production configuration from the capability profile.
use super::SessionError;
use crate::{
    CapabilityProfile, CfgAnalysisConfig, VIR_SYSTEM_SEMANTICS_V2, VirRuntimeSemanticProfile,
    current_capability_profile,
};

/// None requests the current production default. Unknown names never fall back.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SessionRequest {
    pub target: Option<String>,
    pub runtime: Option<String>,
    pub verifier: Option<String>,
    pub analysis: CfgAnalysisConfig,
}

/// Only configuration resolution can construct an effective configuration.
/// Budgets are passed unchanged: zero budgets still exercise fail-closed paths.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CompilationConfig {
    analysis: CfgAnalysisConfig,
}
impl CompilationConfig {
    pub(super) fn resolve(request: &SessionRequest) -> Result<Self, SessionError> {
        let profile = current_capability_profile()
            .map_err(|error| SessionError::InvalidCapabilityProfile(error.to_string()))?;
        for (field, requested, known) in [
            ("target", &request.target, profile.target()),
            ("runtime", &request.runtime, profile.runtime()),
            ("verifier", &request.verifier, profile.verifier()),
        ] {
            if let Some(name) = requested
                && name != known
            {
                return Err(SessionError::UnsupportedConfiguration {
                    field,
                    requested: name.clone(),
                });
            }
        }
        Ok(Self {
            analysis: request.analysis,
        })
    }
    pub fn target(self) -> &'static str {
        self.profile().target()
    }
    pub fn runtime(self) -> VirRuntimeSemanticProfile {
        debug_assert_eq!(self.profile().runtime(), "system-v2");
        VIR_SYSTEM_SEMANTICS_V2
    }
    pub fn verifier(self) -> &'static str {
        self.profile().verifier()
    }
    pub fn analysis(self) -> CfgAnalysisConfig {
        self.analysis
    }
    pub fn profile(self) -> &'static CapabilityProfile {
        current_capability_profile().expect("resolved capability profile")
    }
}
