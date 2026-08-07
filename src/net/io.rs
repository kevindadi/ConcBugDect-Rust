//! I/O: JSON, RON, and optional PNML serialization helpers.
use std::fs::File;
use std::io::{Read, Write};
use std::path::Path;

use ron::ser::PrettyConfig;
use serde::{Serialize, de::DeserializeOwned};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum IoError {
    #[error("json error: {0}")]
    Json(#[from] serde_json::Error),
    #[error("ron error: {0}")]
    Ron(#[from] ron::Error),
    #[error("io error: {0}")]
    Io(#[from] std::io::Error),
}

pub fn to_json_string<T>(value: &T) -> Result<String, IoError>
where
    T: Serialize,
{
    Ok(serde_json::to_string_pretty(value)?)
}

pub fn from_json_str<T>(s: &str) -> Result<T, IoError>
where
    T: DeserializeOwned,
{
    Ok(serde_json::from_str(s)?)
}

pub fn write_json<P: AsRef<Path>, T: Serialize>(path: P, value: &T) -> Result<(), IoError> {
    let mut file = File::create(path)?;
    let content = to_json_string(value)?;
    file.write_all(content.as_bytes())?;
    Ok(())
}

pub fn read_json<P: AsRef<Path>, T: DeserializeOwned>(path: P) -> Result<T, IoError> {
    let mut file = File::open(path)?;
    let mut content = String::new();
    file.read_to_string(&mut content)?;
    from_json_str(&content)
}

pub fn to_ron_string<T>(value: &T) -> Result<String, IoError>
where
    T: Serialize,
{
    let mut pretty = PrettyConfig::default();
    pretty.new_line = "\n".into();
    Ok(ron::ser::to_string_pretty(value, pretty)?)
}

pub fn from_ron_str<T>(s: &str) -> Result<T, IoError>
where
    T: DeserializeOwned,
{
    Ok(ron::from_str(s).unwrap())
}

pub fn write_ron<P: AsRef<Path>, T: Serialize>(path: P, value: &T) -> Result<(), IoError> {
    let mut file = File::create(path)?;
    let content = to_ron_string(value)?;
    file.write_all(content.as_bytes())?;
    Ok(())
}

pub fn read_ron<P: AsRef<Path>, T: DeserializeOwned>(path: P) -> Result<T, IoError> {
    let mut file = File::open(path)?;
    let mut content = String::new();
    file.read_to_string(&mut content)?;
    from_ron_str(&content)
}

#[cfg(feature = "pnml")]
pub mod pnml {
    use super::IoError;
    use crate::net::core::Net;

    pub fn import_pnml(_content: &str) -> Result<Net, IoError> {
        Err(IoError::Io(std::io::Error::new(
            std::io::ErrorKind::Unsupported,
            "PNML import not yet implemented",
        )))
    }

    pub fn export_pnml(_net: &Net) -> Result<String, IoError> {
        Err(IoError::Io(std::io::Error::new(
            std::io::ErrorKind::Unsupported,
            "PNML export not yet implemented",
        )))
    }
}
