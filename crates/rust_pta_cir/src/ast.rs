//! CIR AST

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use serde_json::Value;

/// Top-level CIR program.
#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct Program {
    pub program: String,
    pub resources: Vec<Resource>,
    pub protection: Vec<Protection>,
    pub functions: Vec<Function>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub fn_summaries: Vec<FnSummary>,
    pub entry: String,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Resource {
    pub name: String,
    pub kind: ResourceKind,
    #[serde(rename = "type")]
    pub res_type: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub mode: Option<SyncMode>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub count: Option<u64>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub base: Option<BaseType>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub init: Option<Value>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ResourceKind {
    Sync,
    Var,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum SyncMode {
    Sync,
    Async,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(untagged)]
pub enum BaseType {
    Primitive(String),
    Complex(ComplexBaseType),
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "PascalCase")]
pub enum ComplexBaseType {
    Enum { r#enum: Vec<String> },
    Struct(BTreeMap<String, String>),
    Array { array: ArrayDef },
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct ArrayDef {
    pub elem: String,
    pub len: u64,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Protection {
    pub var: String,
    pub lock: String,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct Function {
    pub name: String,
    pub kind: FnKind,
    pub body: Vec<Statement>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum FnKind {
    Normal,
    Async,
    Closure,
}

#[derive(Debug, Clone, PartialEq, Serialize)]
pub struct Statement {
    pub sid: String,
    pub op: Op,
    pub transfer: Transfer,
}

/// CIR operation
#[derive(Debug, Clone, PartialEq)]
pub enum Op {
    ResOp {
        resource: String,
        action: String,
        args: Vec<String>,
    },
    Spawn(String),
    SpawnAsync(String),
    Join(String),
    Await(String),
    Call(String),
    Return,
    Nop,
}

impl Serialize for Op {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeSeq;
        match self {
            Op::Return => serializer.serialize_str("return"),
            Op::Nop => serializer.serialize_str("nop"),
            Op::ResOp {
                resource,
                action,
                args,
            } => {
                let mut seq = serializer.serialize_seq(Some(3 + args.len()))?;
                seq.serialize_element("res_op")?;
                seq.serialize_element(resource)?;
                seq.serialize_element(action)?;
                for a in args {
                    seq.serialize_element(a)?;
                }
                seq.end()
            }
            Op::Spawn(f) => {
                let mut seq = serializer.serialize_seq(Some(2))?;
                seq.serialize_element("spawn")?;
                seq.serialize_element(f)?;
                seq.end()
            }
            Op::SpawnAsync(f) => {
                let mut seq = serializer.serialize_seq(Some(2))?;
                seq.serialize_element("spawn_async")?;
                seq.serialize_element(f)?;
                seq.end()
            }
            Op::Join(f) => {
                let mut seq = serializer.serialize_seq(Some(2))?;
                seq.serialize_element("join")?;
                seq.serialize_element(f)?;
                seq.end()
            }
            Op::Await(f) => {
                let mut seq = serializer.serialize_seq(Some(2))?;
                seq.serialize_element("await")?;
                seq.serialize_element(f)?;
                seq.end()
            }
            Op::Call(f) => {
                let mut seq = serializer.serialize_seq(Some(2))?;
                seq.serialize_element("call")?;
                seq.serialize_element(f)?;
                seq.end()
            }
        }
    }
}

/// CIR control-flow transfer.
#[derive(Debug, Clone, PartialEq)]
pub enum Transfer {
    Next(String),
    Branch {
        cond: String,
        true_sid: String,
        false_sid: String,
    },
    Switch {
        var: String,
        cases: BTreeMap<String, String>,
    },
    Return,
}

impl Serialize for Transfer {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        use serde::ser::SerializeSeq;
        match self {
            Transfer::Return => serializer.serialize_str("return"),
            Transfer::Next(sid) => {
                let mut seq = serializer.serialize_seq(Some(2))?;
                seq.serialize_element("next")?;
                seq.serialize_element(sid)?;
                seq.end()
            }
            Transfer::Branch {
                cond,
                true_sid,
                false_sid,
            } => {
                let mut seq = serializer.serialize_seq(Some(4))?;
                seq.serialize_element("branch")?;
                seq.serialize_element(cond)?;
                seq.serialize_element(true_sid)?;
                seq.serialize_element(false_sid)?;
                seq.end()
            }
            Transfer::Switch { var, cases } => {
                let mut seq = serializer.serialize_seq(Some(3))?;
                seq.serialize_element("switch")?;
                seq.serialize_element(var)?;
                seq.serialize_element(cases)?;
                seq.end()
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FnSummary {
    pub name: String,
    pub reads: Vec<String>,
    pub writes: Vec<String>,
    pub callees: Vec<String>,
    pub has_concurrency: bool,
}

impl Program {
    pub fn empty(program: impl Into<String>, entry: impl Into<String>) -> Self {
        let entry = entry.into();
        Self {
            program: program.into(),
            resources: Vec::new(),
            protection: Vec::new(),
            functions: Vec::new(),
            fn_summaries: Vec::new(),
            entry,
        }
    }
}

impl Statement {
    pub fn new(sid: impl Into<String>, op: Op, transfer: Transfer) -> Self {
        Self {
            sid: sid.into(),
            op,
            transfer,
        }
    }

    pub fn sid_index(s: &str) -> Option<u32> {
        s.strip_prefix('s')?.parse().ok()
    }

    pub fn format_sid(n: u32) -> String {
        format!("s{n}")
    }
}
