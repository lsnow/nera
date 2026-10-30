//! Shared boundary vocabulary, never proof of an actual resource.
//! Static coordinates do not contain allocation identities. Consumers bind
//! their own checked authorities and validate every exit independently.

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BoundarySource {
    Parameter { index: u32 },
    ParameterField { index: u32, field: u32 },
}

/// The view and authority are consumer-owned: verifier loans and runtime
/// invocation tokens must not be converted into each other.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundaryBinding<A, V> {
    pub source: BoundarySource,
    pub authority: A,
    pub view: V,
}

/// Dispositions of the actual carriers derived from one imported authority.
/// Shared permits checked alias expansion; it does not itself create authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BoundaryExit<S, V> {
    InPlace,
    Stored(S),
    Value(V),
    Ended,
    Shared { stored: Vec<S>, values: Vec<V> },
}

impl<S, V> BoundaryExit<S, V> {
    pub fn stored(&self) -> &[S] {
        match self {
            Self::Stored(s) => std::slice::from_ref(s),
            Self::Shared { stored, .. } => stored,
            _ => &[],
        }
    }
    pub fn values(&self) -> &[V] {
        match self {
            Self::Value(v) => std::slice::from_ref(v),
            Self::Shared { values, .. } => values,
            _ => &[],
        }
    }
}
