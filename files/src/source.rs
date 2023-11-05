use std::fmt::{Debug, Display};

use diagnostic::miette;
use internment::Intern;

use crate::{Db, Span};

/// A path to a source file.
///
/// Note that the segments in the path are interned strings; that is, they are strings whose
/// underlying data has been leaked and will never be cleaned up, but they have very cheap
/// comparison and hashing operations.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct Source {
    pub directory: Vec<Intern<String>>,
    pub name: Intern<String>,
    pub extension: FileExtension,
}

impl Display for Source {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}/{}.{}",
            self.directory
                .iter()
                .map(|x| x.as_str())
                .collect::<Vec<_>>()
                .join("/"),
            self.name,
            self.extension,
        )
    }
}

impl Debug for Source {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{self}")
    }
}

impl From<&Source> for std::path::PathBuf {
    fn from(value: &Source) -> Self {
        let mut out = std::path::PathBuf::new();
        for segment in &value.directory {
            out.push(segment.as_str());
        }
        out.push(value.name.as_str());
        out.set_extension(value.extension.to_string());
        out
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum FileExtension {
    Quill,
}

impl Display for FileExtension {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FileExtension::Quill => write!(f, "quill"),
        }
    }
}

/// All of the database's data for a given source.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SourceData {
    src: Source,
    contents: String,
}

impl SourceData {
    pub fn src(&self) -> &Source {
        &self.src
    }

    pub fn contents(&self) -> &str {
        &self.contents
    }

    pub fn new(src: Source, db: &impl Db) -> Self {
        SourceData {
            src: src.clone(),
            contents: db
                .read_source(src)
                .value()
                .map(|value| (**value).clone())
                .unwrap_or("<could not read source file>".to_owned()),
        }
    }

    pub fn new_empty(src: Source) -> Self {
        SourceData {
            src,
            contents: "<could not read source file>".to_owned(),
        }
    }
}

impl miette::SourceCode for SourceData {
    fn read_span<'a>(
        &'a self,
        span: &miette::SourceSpan,
        context_lines_before: usize,
        context_lines_after: usize,
    ) -> Result<Box<dyn miette::SpanContents<'a> + 'a>, miette::MietteError> {
        self.contents
            .read_span(span, context_lines_before, context_lines_after)
            .map(|contents| {
                Box::new(miette::MietteSpanContents::new_named(
                    self.src.to_string(),
                    contents.data(),
                    *contents.span(),
                    contents.line(),
                    contents.column(),
                    contents.line_count(),
                )) as Box<dyn miette::SpanContents<'a> + 'a>
            })
    }
}

/// A span of code in a particular source file.
/// See also [`Span`].
/// Not to be confused with [`miette::SourceSpan`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct SourceSpan {
    pub source: Source,
    pub span: Span,
}

impl SourceSpan {
    pub fn new(source: Source, span: Span) -> Self {
        Self { source, span }
    }
}
