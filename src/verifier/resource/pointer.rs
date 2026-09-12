use super::*;

/// Pointer provenance knowledge.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AbstractProvenance {
    Known(AbstractAllocationId),
    Unknown,
}

impl AbstractProvenance {
    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Known(left), Self::Known(right)) if left.same_identity(right) => {
                Self::Known(left)
            }
            _ => Self::Unknown,
        }
    }
}

/// Canonical allocation-relative object offsets represented by the analysis.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AbstractObjectOffsets {
    Exact(u64),
    Strided {
        first: u64,
        stride_bytes: u64,
        count: u16,
    },
    Unknown,
}

impl AbstractObjectOffsets {
    #[must_use]
    pub fn from_interval(interval: U64Interval) -> Self {
        interval.exact_value().map_or(Self::Unknown, Self::Exact)
    }

    #[must_use]
    pub fn candidates(self) -> Option<Vec<u64>> {
        match self {
            Self::Exact(offset) => Some(vec![offset]),
            Self::Strided {
                first,
                stride_bytes,
                count,
            } => (0..u64::from(count))
                .map(|index| index.checked_mul(stride_bytes)?.checked_add(first))
                .collect(),
            Self::Unknown => None,
        }
    }

    #[must_use]
    pub const fn join(self, other: Self) -> Self {
        match (self, other) {
            (Self::Exact(left), Self::Exact(right)) if left == right => self,
            (Self::Exact(_), Self::Exact(_)) => Self::Unknown,
            (
                Self::Strided {
                    first: left_first,
                    stride_bytes: left_stride,
                    count: left_count,
                },
                Self::Strided {
                    first: right_first,
                    stride_bytes: right_stride,
                    count: right_count,
                },
            ) if left_first == right_first
                && left_stride == right_stride
                && left_count == right_count =>
            {
                self
            }
            _ => Self::Unknown,
        }
    }

    #[must_use]
    pub const fn offset_by_exact(self, delta: u64) -> Self {
        match self {
            Self::Exact(offset) => match offset.checked_add(delta) {
                Some(offset) => Self::Exact(offset),
                None => Self::Unknown,
            },
            Self::Strided {
                first,
                stride_bytes,
                count,
            } => match first.checked_add(delta) {
                Some(first) => Self::Strided {
                    first,
                    stride_bytes,
                    count,
                },
                None => Self::Unknown,
            },
            Self::Unknown => Self::Unknown,
        }
    }

    #[must_use]
    pub fn offset_by_index(self, indices: U64Interval, stride_bytes: u64) -> Self {
        let Some(count) = indices
            .upper()
            .checked_sub(indices.lower())
            .and_then(|width| width.checked_add(1))
            .and_then(|count| usize::try_from(count).ok())
        else {
            return Self::Unknown;
        };
        if count > VERIFIER_OBJECT_OFFSET_MAX_CANDIDATES {
            return Self::Unknown;
        }
        let Some(delta) = indices.lower().checked_mul(stride_bytes) else {
            return Self::Unknown;
        };
        let Self::Exact(base) = self else {
            return Self::Unknown;
        };
        let Some(first) = base.checked_add(delta) else {
            return Self::Unknown;
        };
        if count == 1 {
            Self::Exact(first)
        } else {
            Self::Strided {
                first,
                stride_bytes,
                count: u16::try_from(count).expect("candidate budget fits u16"),
            }
        }
    }
}

/// Abstract pointer value.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct AbstractPointer {
    pub(super) provenance: AbstractProvenance,
    pub(super) offset_bytes: U64Interval,
    pub(super) alignment: GuaranteedAlignment,
    pub(super) offset_expression: Option<AffineExpression>,
    pub(super) access: Option<VirMemoryAccess>,
    pub(super) object_offsets: AbstractObjectOffsets,
    /// Actual slice selection produced by address calculation, not authority.
    pub(super) slice_footprint: Option<MemoryFootprint>,
    pub(super) domain: crate::VirPointerDomain<AbstractByteRange>,
    pub(super) paths: crate::VirPointerPaths,
}

impl AbstractPointer {
    #[must_use]
    pub const fn new(
        provenance: AbstractProvenance,
        offset_bytes: U64Interval,
        alignment: GuaranteedAlignment,
    ) -> Self {
        Self {
            provenance,
            offset_bytes,
            alignment,
            offset_expression: None,
            access: None,
            slice_footprint: None,
            domain: crate::VirPointerDomain::Allocation,
            paths: crate::VirPointerPaths {
                object: None,
                domain: None,
            },
            object_offsets: if offset_bytes.lower() == offset_bytes.upper() {
                AbstractObjectOffsets::Exact(offset_bytes.lower())
            } else {
                AbstractObjectOffsets::Unknown
            },
        }
    }

    #[must_use]
    pub const fn with_offset_expression(mut self, expression: Option<AffineExpression>) -> Self {
        self.offset_expression = expression;
        self
    }

    #[must_use]
    pub const fn with_memory_access(mut self, access: Option<VirMemoryAccess>) -> Self {
        if self.access.is_none()
            && let Some(access) = access
        {
            self.paths = crate::VirPointerPaths::root(access);
        }
        self.access = access;
        self
    }

    #[must_use]
    pub const fn with_object_offsets(mut self, object_offsets: AbstractObjectOffsets) -> Self {
        self.object_offsets = object_offsets;
        self
    }

    #[must_use]
    pub const fn provenance(self) -> AbstractProvenance {
        self.provenance
    }

    #[must_use]
    pub const fn offset_bytes(self) -> U64Interval {
        self.offset_bytes
    }

    #[must_use]
    pub const fn alignment(self) -> GuaranteedAlignment {
        self.alignment
    }

    #[must_use]
    pub const fn offset_expression(self) -> Option<AffineExpression> {
        self.offset_expression
    }

    #[must_use]
    pub const fn memory_access(self) -> Option<VirMemoryAccess> {
        self.access
    }

    #[must_use]
    pub const fn object_offsets(self) -> AbstractObjectOffsets {
        self.object_offsets
    }

    pub const fn slice_footprint(self) -> Option<MemoryFootprint> {
        self.slice_footprint
    }
    pub const fn domain(self) -> crate::VirPointerDomain<AbstractByteRange> {
        self.domain
    }
    pub const fn paths(self) -> crate::VirPointerPaths {
        self.paths
    }
    pub const fn with_paths(mut self, paths: crate::VirPointerPaths) -> Self {
        self.paths = paths;
        self
    }
    pub const fn with_domain(mut self, domain: crate::VirPointerDomain<AbstractByteRange>) -> Self {
        self.domain = domain;
        self
    }
    pub const fn with_slice_footprint(mut self, footprint: Option<MemoryFootprint>) -> Self {
        self.slice_footprint = footprint;
        self
    }

    #[must_use]
    pub fn join(self, other: Self) -> Self {
        Self {
            provenance: self.provenance.join(other.provenance),
            paths: self.paths.join(other.paths),
            domain: if self.domain == other.domain {
                self.domain
            } else {
                crate::VirPointerDomain::Unknown
            },
            offset_bytes: self.offset_bytes.join(other.offset_bytes),
            alignment: self.alignment.join(other.alignment),
            offset_expression: if self.offset_expression == other.offset_expression {
                self.offset_expression
            } else {
                None
            },
            access: if self.access == other.access {
                self.access
            } else {
                None
            },
            object_offsets: self.object_offsets.join(other.object_offsets),
            slice_footprint: match (self.slice_footprint, other.slice_footprint) {
                (Some(a), Some(b)) => a.join(b),
                _ => None,
            },
        }
    }

    #[must_use]
    pub(super) fn widen(self, next: Self) -> Self {
        Self {
            provenance: self.provenance.join(next.provenance),
            paths: self.paths.join(next.paths),
            domain: if self.domain == next.domain {
                self.domain
            } else {
                crate::VirPointerDomain::Unknown
            },
            offset_bytes: self.offset_bytes.widen(next.offset_bytes),
            alignment: self.alignment.join(next.alignment),
            offset_expression: if self.offset_expression == next.offset_expression {
                self.offset_expression
            } else {
                None
            },
            access: if self.access == next.access {
                self.access
            } else {
                None
            },
            object_offsets: self.object_offsets.join(next.object_offsets),
            slice_footprint: match (self.slice_footprint, next.slice_footprint) {
                (Some(a), Some(b)) => a.join(b),
                _ => None,
            },
        }
    }
}
