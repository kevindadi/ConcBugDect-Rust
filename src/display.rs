//! DOT rendering helpers.
//!
//! The upstream `unipn::pt::PtNet::to_dot` writes place/transition names and
//! `Debug` payloads into quoted labels verbatim. Names like
//! `crate::foo::{closure#0}` and transition types like
//! `Spawn("std::thread::functions::spawn")` contain `"`, `{}`, `::`, `()` and
//! other characters that break the DOT grammar, so the analyzer owns a small
//! escaped exporter here instead.

use std::fmt::Write as _;
use std::io;

use unipn::net::ArcDir;
use unipn::pt::PtNet;

/// Escape a string for use inside a DOT double-quoted label.
///
/// `"` must be escaped or it terminates the quoted string early; `\` must be
/// doubled; real newlines are rendered as the `\n` escape; `{}` and `<>` are
/// escaped defensively for record/HTML-label quirks in some parsers.
pub fn dot_escape(s: &str) -> String {
    s.replace('\\', "\\\\")
        .replace('"', "\\\"")
        .replace('\n', "\\n")
        .replace('\r', "")
        .replace('{', "\\{")
        .replace('}', "\\}")
        .replace('<', "\\<")
        .replace('>', "\\>")
}

/// Render a Petri net as a DOT graph. Mirrors `PtNet::to_dot` but escapes every
/// label, so names and `Debug` payloads containing quotes / braces / colons /
/// parentheses parse cleanly.
pub fn petri_net_to_dot(net: &PtNet) -> String {
    let mut out = String::from("digraph PetriNet {\n  rankdir=LR;\n");
    for (i, place) in net.places.iter().enumerate() {
        let cap = place
            .kind
            .capacity
            .map_or("inf".to_string(), |c| c.to_string());
        let label = dot_escape(&format!(
            "{}\n{:?}\n{}",
            place.name, place.kind.place_type, cap
        ));
        let _ = writeln!(out, "  p{i} [label=\"{label}\", shape=circle];");
    }
    for (i, transition) in net.transitions.iter().enumerate() {
        let label = dot_escape(&format!(
            "{}\n{:?}",
            transition.name, transition.kind.transition_type
        ));
        let _ = writeln!(out, "  t{i} [label=\"{label}\", shape=box];");
    }
    for arc in &net.arcs {
        match arc.direction {
            ArcDir::Input => {
                let _ = writeln!(
                    out,
                    "  p{} -> t{};",
                    arc.place.index(),
                    arc.transition.index()
                );
            }
            ArcDir::Output => {
                let _ = writeln!(
                    out,
                    "  t{} -> p{};",
                    arc.transition.index(),
                    arc.place.index()
                );
            }
            ArcDir::Inhibitor => {
                let _ = writeln!(
                    out,
                    "  p{} -> t{} [style=dotted];",
                    arc.place.index(),
                    arc.transition.index()
                );
            }
            _ => {}
        }
    }
    out.push_str("}\n");
    out
}

/// Write a Petri net DOT file, creating the parent directory if needed.
pub fn write_petri_net_dot(net: &PtNet, path: impl AsRef<std::path::Path>) -> io::Result<()> {
    let path = path.as_ref();
    if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
    }
    std::fs::write(path, petri_net_to_dot(net))
}

#[cfg(test)]
mod tests {
    use super::dot_escape;

    #[test]
    fn escapes_quotes_backslashes_and_newlines() {
        assert_eq!(dot_escape("a\"b\\c\nd"), "a\\\"b\\\\c\\nd");
    }

    #[test]
    fn escapes_braces_and_angle_brackets() {
        assert_eq!(dot_escape("{a}<b>"), "\\{a\\}\\<b\\>");
    }

    #[test]
    fn strips_carriage_returns() {
        assert_eq!(dot_escape("a\rb"), "ab");
    }
}
