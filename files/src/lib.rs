mod source;
mod span;

use std::sync::Arc;

use diagnostic::Dr;
pub use source::*;
pub use span::*;

pub trait Db {
    type ReadFileDiagnostic;

    /// Attempts to read a file from disk.
    /// This method is expected to be memoised: when this function is called, its return value is
    /// retained and returned in any subsequent calls.
    fn read_source(&self, src: Source) -> Dr<Arc<String>, Self::ReadFileDiagnostic>;
}
