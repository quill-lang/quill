use std::fmt::Debug;

use diagnostic::miette;

/// A span of code in a given source file.
/// Represented by a range of UTF-8 characters.
///
/// The default span is `0..0`.
#[derive(Default, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Span {
    /// The lower bound of the span (inclusive).
    pub start: usize,
    /// The upper bound of the span (exclusive).
    pub end: usize,
}

impl Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}..{}", self.start, self.end)
    }
}

impl From<std::ops::Range<usize>> for Span {
    fn from(value: std::ops::Range<usize>) -> Self {
        Self {
            start: value.start,
            end: value.end,
        }
    }
}

impl From<&std::ops::Range<usize>> for Span {
    fn from(value: &std::ops::Range<usize>) -> Self {
        Self {
            start: value.start,
            end: value.end,
        }
    }
}

impl From<Span> for std::ops::Range<usize> {
    fn from(value: Span) -> Self {
        value.start..value.end
    }
}

impl From<Span> for miette::SourceSpan {
    fn from(value: Span) -> Self {
        Self::new(value.start.into(), (value.end - value.start).into())
    }
}

pub trait Spanned {
    fn span(&self) -> Span;
}
