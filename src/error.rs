use std::path::PathBuf;
use std::{fmt, io};

/// What went wrong; the message is what `main` prints.
#[derive(Debug)]
pub enum Error {
    Io(io::Error),
    File {
        path: PathBuf,
        source: io::Error,
    },
    /// The file is not a heap dump this can read.
    Dump(String),
    /// A bad argument or shell command.
    Usage(String),
}

pub type Result<T> = std::result::Result<T, Error>;

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Error::Io(source) => source.fmt(f),
            Error::File { path, source } => write!(f, "{}: {source}", path.display()),
            Error::Dump(message) | Error::Usage(message) => f.write_str(message),
        }
    }
}

impl std::error::Error for Error {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Error::Io(source) | Error::File { source, .. } => Some(source),
            Error::Dump(_) | Error::Usage(_) => None,
        }
    }
}

impl From<io::Error> for Error {
    fn from(source: io::Error) -> Error {
        Error::Io(source)
    }
}
