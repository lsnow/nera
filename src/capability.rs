//! Canonical semantic capabilities shared by validated HIR and VIR types.

/// Consumer boundary at which a well-classified capability request failed.
/// This is orthogonal to verification status and memory-safety findings.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CapabilityFailureKind {
    /// The implementation has not admitted a language/runtime meaning yet.
    RuntimeSemanticsUnsupported,
    /// Runtime semantics exist but the selected verifier profile has no rule.
    VerificationUnsupported,
    /// Runtime semantics exist but the selected code-generation target cannot lower them.
    TargetUnsupported,
}

/// Maximum by-value type nesting admitted while deriving capabilities.
pub const TYPE_CAPABILITY_MAX_DEPTH: usize = 512;

/// Whether a value may be duplicated without transferring ownership.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ValueCapability {
    Copy,
    MoveOnly,
}

/// Cleanup semantics required when a live value leaves its scope.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum DropCapability {
    TrivialDrop,
    BuiltinDrop,
    UserDropGated,
}

/// Whether the type has a statically fixed runtime representation.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SizeCapability {
    Sized,
    Unsized,
}

/// Orthogonal semantic facts derived once from a concrete type definition.
///
/// This is deliberately not an execution/backend support flag. Consumers may
/// impose tighter limits, but must base semantic copy/drop/resource decisions
/// on this canonical value instead of recursively reinterpreting type shapes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct TypeCapabilities {
    pub value: ValueCapability,
    pub drop: DropCapability,
    pub contains_resource: bool,
    pub size: SizeCapability,
}

impl TypeCapabilities {
    #[must_use]
    pub const fn pointer_free_trivial(self) -> bool {
        matches!(self.value, ValueCapability::Copy)
            && matches!(self.drop, DropCapability::TrivialDrop)
            && !self.contains_resource
            && matches!(self.size, SizeCapability::Sized)
    }
}
