use std::{
    fmt::Debug,
    ops::{Deref, DerefMut},
};

use files::{Source, SourceSpan, Span, Spanned};

/// The place that an object in quill code came from.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Provenance {
    /// The object originated from being written directly in a quill source file.
    Quill(SourceSpan),
    Synthetic,
}

impl Default for Provenance {
    fn default() -> Self {
        Provenance::Synthetic
    }
}

/// Attaches provenance data to a type.
///
/// # Common patterns
///
/// It is common to create a newtype wrapper as follows.
/// ```
/// # use parse::provenance::WithProvenance;
/// # use std::ops::{Deref, DerefMut};
///
/// #[derive(PartialEq, Eq)]
/// pub struct TContents;
///
/// #[derive(PartialEq, Eq)]
/// pub struct T(pub WithProvenance<TContents>);
///
/// impl Deref for T {
///     type Target = TContents;
///
///     fn deref(&self) -> &Self::Target {
///         &self.0.contents
///     }
/// }
///
/// impl DerefMut for T {
///     fn deref_mut(&mut self) -> &mut Self::Target {
///         &mut self.0.contents
///     }
/// }
/// ```
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct WithProvenance<T> {
    /// The origin of the value.
    pub provenance: Provenance,
    /// The actual contents of the value.
    pub contents: T,
}

impl<T> WithProvenance<T> {
    pub fn new_synthetic(contents: T) -> Self {
        Self {
            provenance: Provenance::Synthetic,
            contents,
        }
    }

    pub fn new(provenance: Provenance, contents: T) -> Self {
        Self {
            provenance,
            contents,
        }
    }
}

impl<T> Debug for WithProvenance<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            write!(f, "{:?}@{:#?}", self.provenance, self.contents)
        } else {
            write!(f, "{:?}", self.contents)
        }
    }
}

impl<T> Deref for WithProvenance<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.contents
    }
}

impl<T> DerefMut for WithProvenance<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.contents
    }
}

impl Provenance {
    pub fn source(&self) -> Option<&Source> {
        match self {
            Provenance::Quill(source_span) => Some(&source_span.source),
            Provenance::Synthetic => None,
        }
    }
}

impl Spanned for Provenance {
    /// Returns the span, or `0..0` if it was synthetic.
    fn span(&self) -> Span {
        match self {
            Provenance::Quill(source_span) => source_span.span,
            Provenance::Synthetic => Span { start: 0, end: 0 },
        }
    }
}
