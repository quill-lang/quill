use std::{
    collections::HashMap,
    path::{Path, PathBuf},
    sync::{Arc, RwLock},
};

use diagnostic::{miette, Dr};
use files::Source;
use thiserror::Error;

pub struct Database {
    /// The root directory that we are looking for files inside.
    root: PathBuf,
    files: Arc<RwLock<HashMap<Source, Dr<Arc<String>, ReadFileDiagnostic>>>>,
}

impl Database {
    pub fn new(root: impl AsRef<Path>) -> Self {
        Self {
            root: root.as_ref().to_owned(),
            files: Default::default(),
        }
    }
}

impl files::Db for Database {
    type ReadFileDiagnostic = ReadFileDiagnostic;

    fn read_source(&self, src: Source) -> Dr<Arc<String>, ReadFileDiagnostic> {
        let mut guard = self.files.write().expect("could not write to database");
        guard
            .entry(src)
            .or_insert_with_key(|src| {
                let filename = self.root.join(PathBuf::from(src));
                tracing::trace!("reading {}", filename.to_string_lossy());
                match std::fs::read_to_string(&filename) {
                    Ok(value) => Dr::new(Arc::new(value)),
                    Err(err) => Dr::new_err(ReadFileDiagnostic {
                        src: src.clone(),
                        message: err.to_string(),
                        help: format!(
                            "the current working directory is {}",
                            self.root
                                .canonicalize()
                                .expect("could not canonicalise root path")
                                .to_string_lossy()
                        ),
                    }),
                }
            })
            .clone()
    }
}

#[derive(Error, miette::Diagnostic, Debug, Clone, PartialEq, Eq)]
#[error("could not read file [{src}]: {message}")]
pub struct ReadFileDiagnostic {
    src: Source,
    message: String,
    #[help]
    help: String,
}
