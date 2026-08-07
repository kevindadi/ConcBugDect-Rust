//! Petri net → CIR conversion (sync experiment crate).

#![feature(rustc_private)]

pub mod ast;
pub mod convert;
pub mod export;

pub use ast::Program;
pub use convert::{ConvertReport, PnToCirOptions, convert_net_to_cir};
pub use export::{write_cir_json, write_cir_json_pretty};

pub use rust_petri_net_analysis::net;
