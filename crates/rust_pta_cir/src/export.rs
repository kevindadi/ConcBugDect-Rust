//! Write CIR programs to JSON files.

use std::fs;
use std::io::Write;
use std::path::Path;

use thiserror::Error;

use crate::ast::Program;

#[derive(Debug, Error)]
pub enum ExportError {
    #[error("failed to serialize CIR to JSON: {0}")]
    Serialize(#[from] serde_json::Error),
    #[error("failed to write CIR file: {0}")]
    Io(#[from] std::io::Error),
}

pub fn to_json_pretty(program: &Program) -> Result<String, ExportError> {
    Ok(serde_json::to_string_pretty(program)?)
}

pub fn write_cir_json(program: &Program, path: impl AsRef<Path>) -> Result<(), ExportError> {
    write_cir_json_pretty(program, path)
}

pub fn write_cir_json_pretty(program: &Program, path: impl AsRef<Path>) -> Result<(), ExportError> {
    let path = path.as_ref();
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent)?;
        }
    }
    let json = to_json_pretty(program)?;
    let mut file = fs::File::create(path)?;
    file.write_all(json.as_bytes())?;
    file.write_all(b"\n")?;
    Ok(())
}
