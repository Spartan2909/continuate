use std::fmt;

pub struct Error(String);

impl From<&str> for Error {
    fn from(value: &str) -> Self {
        Error(value.to_string())
    }
}

impl From<String> for Error {
    fn from(value: String) -> Self {
        Error(value)
    }
}

impl fmt::Debug for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Error({:?})", self.0)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.0, f)
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;
