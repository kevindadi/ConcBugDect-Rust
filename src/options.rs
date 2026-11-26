use std::path::PathBuf;

use clap::error::ErrorKind;

use crate::config::{AliasUnknownPolicy, CondvarModel, LoopSemantics, PnConfig, ReportLevel};
use clap::{Arg, ArgGroup, Command};
use rustc_session::EarlyDiagCtxt;

const DEFAULT_ANALYSIS_DIR: &str = "./tmp";
#[derive(Debug, Clone)]
pub enum CrateNameList {
    White(Vec<String>),
    Black(Vec<String>),
}

impl Default for CrateNameList {
    fn default() -> Self {
        CrateNameList::White(Vec::new())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum DetectorKind {
    Deadlock,
}

pub fn print_help() {
    let _ = make_options_parser().print_help();
}

fn make_options_parser() -> clap::Command {
    let analysis_help = "Analysis mode: deadlock.";

    let analysis_arg = Arg::new("analysis_mode")
        .short('m')
        .long("mode")
        .help(analysis_help)
        .default_values(&["deadlock"])
        .hide_default_value(true)
        .value_parser(["deadlock"]);

    let parser = Command::new("spn")
        .no_binary_name(true)
        .version("v0.1.0")
        .arg(analysis_arg)
        .arg(
            Arg::new("diagnostics_output")
                .long("spn-analysis-dir")
                .value_name("PATH")
                .help("Directory for Petri net analysis outputs")
                .default_value(DEFAULT_ANALYSIS_DIR),
        )
        .arg(
            Arg::new("config_file")
                .long("config")
                .value_name("FILE")
                .help("Path to configuration file (default: spn.toml)"),
        )
        .arg(
            Arg::new("target_crate")
                .short('p')
                .long("spn-crate")
                .help("Target crate for analysis (required for cargo; optional for single file)")
                .default_value("main"),
        )
        .arg(
            Arg::new("input_file")
                .short('f')
                .long("file")
                .value_name("FILE")
                .help("Single .rs file to analyze (optional; not needed for cargo)"),
        )
        .group(
            ArgGroup::new("visualization")
                .args([
                    "dump_callgraph",
                    "dump_petrinet",
                    "dump_stategraph",
                    "dump_unsafe",
                    "dump_points_to",
                    "dump_mir",
                ])
                .multiple(true),
        )
        .arg(
            Arg::new("dump_callgraph")
                .long("viz-callgraph")
                .help("Generate call graph visualization")
                .action(clap::ArgAction::SetTrue),
        )
        .arg(
            Arg::new("dump_petrinet")
                .long("viz-petrinet")
                .help("Generate Petri net visualization")
                .action(clap::ArgAction::SetTrue),
        )
        .arg(
            Arg::new("dump_stategraph")
                .long("viz-stategraph")
                .help("Generate state graph visualization")
                .action(clap::ArgAction::SetTrue),
        )
        .arg(
            Arg::new("dump_unsafe")
                .long("viz-unsafe")
                .help("Generate unsafe operations report")
                .action(clap::ArgAction::SetTrue),
        )
        .arg(
            Arg::new("dump_points_to")
                .long("viz-pointsto")
                .help("Generate points-to relations report")
                .action(clap::ArgAction::SetTrue),
        )
        .arg(
            Arg::new("dump_mir")
                .long("viz-mir")
                .help("Generate MIR visualization (dot format)")
                .action(clap::ArgAction::SetTrue),
        )
        .arg(
            Arg::new("dump_cir")
                .long("viz-cir")
                .help("Write cir.yaml (concurrency intermediate representation)")
                .action(clap::ArgAction::SetTrue),
        )
        .arg(
            Arg::new("stop_after")
                .long("stop-after")
                .value_name("STAGE")
                .help("Stop analysis after specified stage: mir, callgraph, pointsto, petrinet, stategraph")
                .value_parser(["mir", "callgraph", "pointsto", "petrinet", "stategraph"]),
        )
        .arg(
            Arg::new("state_limit")
                .long("state-limit")
                .value_name("N")
                .help("Max states to explore in reachability (default: 50000, 0 = unlimited)")
                .value_parser(clap::value_parser!(usize)),
        )
        .arg(
            Arg::new("full")
                .long("full")
                .help("Translate all functions (disables entry-reachable and concurrent-roots filtering)")
                .action(clap::ArgAction::SetTrue),
        )
        .arg(
            Arg::new("crate_whitelist")
                .long("crate-whitelist")
                .value_name("CRATES")
                .help("Comma-separated crate names to analyze (only these crates)")
                .value_delimiter(','),
        )
        .arg(
            Arg::new("crate_blacklist")
                .long("crate-blacklist")
                .value_name("CRATES")
                .help("Comma-separated crate names to exclude from analysis")
                .value_delimiter(','),
        )
        .arg(
            Arg::new("cross_crate")
                .long("spn-cross-crate")
                .value_name("CRATES")
                .help(
                    "Comma-separated dependency crate name prefixes whose lock-bearing \
                     functions are translated and analysed as part of the target crate \
                     (workspace-level resource identity; requires their MIR to be \
                     available to the consumer, e.g. #[inline] or -Zalways-encode-mir)",
                )
                .value_delimiter(','),
        )
        .arg(
            Arg::new("no_reduce")
                .long("no-reduce")
                .help("Disable Petri net reduction before reachability")
                .action(clap::ArgAction::SetTrue),
        )
        .arg(
            Arg::new("por")
                .long("por")
                .help("Enable partial order reduction (POR) to reduce equivalent interleavings")
                .action(clap::ArgAction::SetTrue),
        )
        .arg(
            Arg::new("no_concurrent_roots")
                .long("no-concurrent-roots")
                .help("Disable translating functions that use locks/atomics/condvars (and their callees)")
                .action(clap::ArgAction::SetTrue),
        )
        .arg(
            Arg::new("alias_unknown_policy")
                .long("alias-unknown-policy")
                .value_name("POLICY")
                .help("When alias analysis returns Unknown: conservative (treat as Possibly, sound) or optimistic (treat as Unlikely)")
                .value_parser(["conservative", "optimistic"]),
        )
        .arg(
            Arg::new("report_level")
                .long("report-level")
                .value_name("LEVEL")
                .help("Report audience: developer (default, concise) or research (internal diagnostics)")
                .value_parser(["developer", "research"]),
        )
        .arg(
            Arg::new("exclude_candidates")
                .long("exclude-candidates")
                .value_name("FILE")
                .help(
                    "Candidate-level refinements (pn-refinements/1) to exclude from the report; \
                     read fail-open, report-side only",
                ),
        )
        .arg(
            Arg::new("pta_k")
                .long("pta-k")
                .value_name("N")
                .help("Call-site sensitivity depth (k-CFA) for the pointer-analysis engine (default: 1, 0 = context-insensitive)")
                .value_parser(clap::value_parser!(usize)),
        )
        .arg(
            Arg::new("slice_max_roots")
                .long("slice-max-roots")
                .value_name("N")
                .help(
                    "Maximum library roots started per slice (default: 4, 0 = disable \
                     partitioned slicing); oversized shared-resource groups are split \
                     while keeping every synchronizing root pair together",
                )
                .value_parser(clap::value_parser!(usize)),
        )
        .arg(
            Arg::new("slice_state_budget")
                .long("slice-state-budget")
                .value_name("N")
                .help(
                    "Total state budget across all library slices (default: unlimited, \
                     each slice may use --state-limit); slices are explored in partition \
                     order until the budget is spent and the rest are reported unexplored",
                )
                .value_parser(clap::value_parser!(usize)),
        )
        .arg(
            Arg::new("loop_semantics")
                .long("loop-semantics")
                .value_name("MODE")
                .help(
                    "Cut-back-edge semantics: cut (existing behaviour; default for binaries) or \
                     summary (loop re-entry, bounded unroll k = loop_summary_k, default 1; \
                     default for libraries)",
                )
                .value_parser(["cut", "summary"]),
        )
        .arg(
            Arg::new("loop_summary_k")
                .long("loop-summary-k")
                .value_name("N")
                .help(
                    "How many times a loop-summary transition may re-enter its target \
                     (default: 1; summary semantics only)",
                )
                .value_parser(clap::value_parser!(usize)),
        )
        .arg(
            Arg::new("condvar_model")
                .long("spn-condvar-model")
                .value_name("MODEL")
                .help(
                    "Scenario-level condition-variable model: std (default; std::sync::Condvar \
                     only), parking_lot (parking_lot::Condvar plus its &mut guard argument \
                     shape), or all (both). parking_lot/all also enable the waiter-counter \
                     ordering guard; std keeps the previous nets byte-identical",
                )
                .value_parser(["std", "parking_lot", "all"]),
        )
        .arg(
            Arg::new("bool_guard_abstraction")
                .long("bool-guard-abstraction")
                .value_name("BOOL")
                .help(
                    "Enable boolean guard predicate abstraction for Mutex<bool> condvar loops \
                     (default: true; false restores the previous unextracted-wait behavior)",
                )
                .value_parser(["true", "false"]),
        )
        .arg(
            Arg::new("resource_atomic_partition")
                .long("resource-atomic-partition")
                .value_name("MODE")
                .help(
                    "Experiment switch; `legacy` is only for comparison runs \
                     (default: alias, one place per atomic class)",
                )
                .value_parser(["alias", "legacy"]),
        )
        .arg(
            Arg::new("resource_lock_grouper")
                .long("resource-lock-grouper")
                .value_name("MODE")
                .help(
                    "Experiment switch; `ported` is only for comparison runs \
                     (default: original union-find). `typed` adds the type filter",
                )
                .value_parser(["original", "ported", "typed"]),
        )
        .arg(
            Arg::new("dump_resource_map")
                .long("spn-dump-resource-map")
                .action(clap::ArgAction::SetTrue)
                .help(
                    "Write resources-map.json: the proposed sync-object slots and how they \
                     differ from the places the current binders built. Does not change the net",
                ),
        )
        .arg(
            Arg::new("dump_projected_subnets")
                .long("spn-dump-projected-subnets")
                .action(clap::ArgAction::SetTrue)
                .help(
                    "Also write subnets-projected.json, a subnet summary read back from the \
                     built net. Off by default; subnets.json stays the recorded summary",
                ),
        )
        .arg(
            Arg::new("export_concir_net")
                .long("export-concir-net")
                .value_name("FILE")
                .help(
                    "Export the ConcIR implementation sync Petri net and state graph \
                     (concir-impl-net/1) to FILE; disables Petri-net reduction for this run",
                ),
        )
        .arg(
            Arg::new("codegen_map")
                .long("codegen-map")
                .value_name("FILE")
                .help(
                    "Path to ConcIR codegen.json (with optional hole_ranges) for canonical \
                     resource mapping and hole purity checks",
                ),
        );
    parser
}
#[derive(Debug, Clone)]
pub struct Options {
    pub detector_kind: DetectorKind,
    pub output: Option<PathBuf>,
    pub crate_name: String,
    /// `--exclude-candidates`: candidate-level refinements file.
    pub exclude_candidates: Option<PathBuf>,
    /// `--export-concir-net`: write `concir-impl-net/1` JSON at the end of `pipeline::project`.
    pub export_concir_net: Option<PathBuf>,
    /// `--codegen-map`: `codegen.json` (plus optional `hole_ranges`) for resource mapping and purity checks.
    pub codegen_map: Option<PathBuf>,
    /// Single-file analysis path (`-f`), used for CIR / filtering when set.
    pub input_file: Option<PathBuf>,
    pub crate_filter: CrateNameList,
    /// Dependency-crate name prefixes translated together with the
    /// target crate (workspace-level resource identity). Empty by default, so
    /// single-crate analyses are byte-for-byte unchanged.
    pub cross_crate: Vec<String>,
    pub dump_options: DumpOptions,
    pub stop_after: StopAfter,
    pub config: PnConfig,
}

impl Default for Options {
    fn default() -> Self {
        Options {
            detector_kind: DetectorKind::Deadlock,
            output: Option::default(),
            crate_name: String::new(),
            exclude_candidates: None,
            export_concir_net: None,
            codegen_map: None,
            input_file: None,
            crate_filter: CrateNameList::default(),
            cross_crate: Vec::new(),
            dump_options: DumpOptions::default(),
            stop_after: StopAfter::None,
            config: PnConfig::default(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct DumpOptions {
    pub dump_call_graph: bool,
    pub dump_petri_net: bool,
    pub dump_state_graph: bool,
    pub dump_unsafe_info: bool,
    pub dump_points_to: bool,
    pub dump_mir: bool,
    /// Emit `cir.yaml` (concurrency IR) alongside analysis outputs.
    pub dump_cir: bool,
    /// Also write `subnets-projected.json`. Off by default.
    pub dump_projected_subnets: bool,
    /// Write `resources-map.json`. Off by default. Does not change the net.
    pub dump_resource_map: bool,
}

/// Pipeline stop point for debugging.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StopAfter {
    None,
    AfterMir,        // Stop after MIR dump
    AfterCallGraph,  // Stop after call graph construction
    AfterPointsTo,   // Stop after pointer analysis
    AfterPetriNet,   // Stop after Petri net construction
    AfterStateGraph, // Stop after state graph construction
}

impl Default for DumpOptions {
    fn default() -> Self {
        DumpOptions {
            dump_call_graph: false,
            dump_petri_net: false,
            dump_state_graph: false,
            dump_unsafe_info: false,
            dump_points_to: false,
            dump_mir: false,
            dump_cir: false,
            dump_projected_subnets: false,
            dump_resource_map: false,
        }
    }
}

impl Options {
    pub fn parse_from_str(&mut self, s: &str, handler: &EarlyDiagCtxt) -> Vec<String> {
        let args = shellwords::split(s).unwrap_or_else(|e| {
            handler.early_fatal(format!("Cannot parse argument string: {e:?}"))
        });

        self.parse_from_args(&args)
    }

    pub fn parse_from_args(&mut self, args: &[String]) -> Vec<String> {
        let (pn_args, rustc_args) = match args.iter().position(|s| s == "--") {
            Some(pos) => (&args[..pos], &args[pos + 1..]),
            None => (args, &[][..]),
        };

        let matches = make_options_parser()
            .try_get_matches_from(pn_args.iter())
            .unwrap_or_else(|e| match e.kind() {
                ErrorKind::DisplayHelp => {
                    e.exit();
                }
                // Unknown arguments are rustc flags — skip them and parse what remains.
                ErrorKind::UnknownArgument => {
                    log::debug!("Unknown SPN arg (skipping, likely rustc arg): {}", e);
                    make_options_parser()
                        .get_matches_from(pn_args.iter().filter(|s| !s.starts_with('-')))
                }
                _ => {
                    log::debug!("{e}");
                    e.exit();
                }
            });

        self.detector_kind = match matches.get_one::<String>("analysis_mode").unwrap().as_str() {
            "deadlock" => DetectorKind::Deadlock,
            _ => DetectorKind::Deadlock,
        };

        self.input_file = matches.get_one::<String>("input_file").map(PathBuf::from);
        self.crate_name = matches
            .get_one::<String>("target_crate")
            .cloned()
            .or_else(|| {
                matches.get_one::<String>("input_file").map(|f| {
                    std::path::Path::new(f)
                        .file_stem()
                        .and_then(|s| s.to_str())
                        .unwrap_or("main")
                        .to_string()
                })
            })
            .unwrap_or_else(|| "main".to_string());
        self.output = matches
            .get_one::<String>("diagnostics_output")
            .cloned()
            .map(PathBuf::from);
        self.exclude_candidates = matches
            .get_one::<String>("exclude_candidates")
            .cloned()
            .map(PathBuf::from);
        self.export_concir_net = matches
            .get_one::<String>("export_concir_net")
            .cloned()
            .map(PathBuf::from);
        self.codegen_map = matches
            .get_one::<String>("codegen_map")
            .cloned()
            .map(PathBuf::from);

        self.dump_options = DumpOptions {
            dump_call_graph: matches.get_flag("dump_callgraph"),
            dump_petri_net: matches.get_flag("dump_petrinet"),
            dump_state_graph: matches.get_flag("dump_stategraph"),
            dump_unsafe_info: matches.get_flag("dump_unsafe"),
            dump_points_to: matches.get_flag("dump_points_to"),
            dump_mir: matches.get_flag("dump_mir"),
            dump_cir: matches.get_flag("dump_cir"),
            dump_projected_subnets: matches.get_flag("dump_projected_subnets"),
            dump_resource_map: matches.get_flag("dump_resource_map"),
        };

        self.stop_after = match matches.get_one::<String>("stop_after") {
            Some(stage) => match stage.as_str() {
                "mir" => StopAfter::AfterMir,
                "callgraph" => StopAfter::AfterCallGraph,
                "pointsto" => StopAfter::AfterPointsTo,
                "petrinet" => StopAfter::AfterPetriNet,
                "stategraph" => StopAfter::AfterStateGraph,
                _ => StopAfter::None,
            },
            None => StopAfter::None,
        };

        let config_path = matches
            .get_one::<String>("config_file")
            .map(PathBuf::from)
            .unwrap_or_else(|| PathBuf::from("spn.toml"));

        match PnConfig::load_from_file(&config_path) {
            Ok(cfg) => self.config = cfg,
            Err(e) => {
                log::warn!("Failed to load config from {:?}: {}", config_path, e);
            }
        }

        if let Some(&n) = matches.get_one::<usize>("state_limit") {
            self.config.state_limit = if n == 0 { None } else { Some(n) };
        }
        if matches.get_flag("full") {
            self.config.entry_reachable = false;
        }
        if let Some(crates) = matches.get_many::<String>("crate_whitelist") {
            self.crate_filter = CrateNameList::White(crates.cloned().collect());
        } else if let Some(crates) = matches.get_many::<String>("crate_blacklist") {
            self.crate_filter = CrateNameList::Black(crates.cloned().collect());
        }
        if let Some(crates) = matches.get_many::<String>("cross_crate") {
            self.cross_crate = crates
                .map(|name| name.replace('-', "_"))
                .filter(|name| !name.is_empty())
                .collect();
        }
        if matches.get_flag("no_reduce") || self.export_concir_net.is_some() {
            self.config.reduce_net = false;
        }
        if matches.get_flag("por") {
            self.config.por_enabled = true;
        }
        if matches.get_flag("no_concurrent_roots") {
            self.config.translate_concurrent_roots = false;
        }
        if let Some(policy) = matches.get_one::<String>("alias_unknown_policy") {
            self.config.alias_unknown_policy = match policy.as_str() {
                "optimistic" => AliasUnknownPolicy::Optimistic,
                _ => AliasUnknownPolicy::Conservative,
            };
        }
        if let Some(level) = matches.get_one::<String>("report_level") {
            self.config.report_level = match level.as_str() {
                "research" => ReportLevel::Research,
                _ => ReportLevel::Developer,
            };
        }
        if let Some(&k) = matches.get_one::<usize>("pta_k") {
            self.config.pta_k = k;
        }
        if let Some(&cap) = matches.get_one::<usize>("slice_max_roots") {
            self.config.slice_max_roots = if cap == 0 { None } else { Some(cap) };
        }
        if let Some(&budget) = matches.get_one::<usize>("slice_state_budget") {
            self.config.slice_state_budget = if budget == 0 { None } else { Some(budget) };
        }
        if let Some(mode) = matches.get_one::<String>("resource_atomic_partition") {
            if let Some(parsed) = crate::config::PartitionSwitch::parse(mode) {
                self.config.resource_atomic_partition = parsed;
            }
        }
        if let Some(mode) = matches.get_one::<String>("resource_lock_grouper") {
            if let Some(parsed) = crate::config::LockGrouper::parse(mode) {
                self.config.resource_lock_grouper = parsed;
            }
        }
        if let Some(mode) = matches.get_one::<String>("loop_semantics") {
            self.config.loop_semantics = Some(match mode.as_str() {
                "summary" => LoopSemantics::Summary,
                _ => LoopSemantics::Cut,
            });
        }
        if let Some(&k) = matches.get_one::<usize>("loop_summary_k") {
            self.config.loop_summary_k = k;
        }
        if let Some(model) = matches.get_one::<String>("condvar_model") {
            self.config.condvar_model = match model.as_str() {
                "parking_lot" => CondvarModel::ParkingLot,
                "all" => CondvarModel::All,
                _ => CondvarModel::Std,
            };
        }
        if let Some(val) = matches.get_one::<String>("bool_guard_abstraction") {
            self.config.bool_guard_abstraction = val == "true";
        }

        // Cargo package names may contain `-`; rustc def paths use `_`.
        // Normalize once here so crate filtering and the output directory
        // agree with `targets_current_crate`.
        self.crate_name = self.crate_name.replace('-', "_");

        rustc_args.to_vec()
    }

    pub fn targets_current_crate(&self, current_crate_name: &str) -> bool {
        self.crate_name == current_crate_name
    }

    /// Whether `func_name` (a rustc `def_path_str`) belongs to the target crate,
    /// a `--spn-cross-crate` dependency, and is not excluded by the crate filter.
    ///
    /// The include/exclude lists are matched as stored. Only `crate_name` is
    /// hyphen-normalized, and that happens in [`Self::parse_from_args`].
    pub fn crate_filter_match(&self, func_name: &str) -> bool {
        let include = match &self.crate_filter {
            CrateNameList::White(list) if !list.is_empty() => {
                list.iter().any(|c| func_name.starts_with(c))
            }
            _ => func_name.starts_with(&self.crate_name),
        };
        let exclude = match &self.crate_filter {
            CrateNameList::Black(list) if !list.is_empty() => {
                list.iter().any(|c| func_name.starts_with(c))
            }
            _ => false,
        };
        // `--spn-cross-crate` widens the reachable translation set to
        // the named dependency crates, so their lock-using frames become
        // part of the net.
        (include || self.cross_crate_matches(func_name)) && !exclude
    }

    /// Whether `func_name` (a rustc `def_path_str`) belongs to one of
    /// the dependency crates listed by `--spn-cross-crate`. The match is
    /// crate-boundary aware, so `ws_lib` covers `ws_lib::Ledger::transfer` but
    /// not the unrelated crate `ws_library::...` (a plain `starts_with` would
    /// silently pull that crate in as well).
    pub fn cross_crate_matches(&self, func_name: &str) -> bool {
        self.cross_crate.iter().any(|prefix| {
            func_name == prefix
                || func_name
                    .strip_prefix(prefix.as_str())
                    .is_some_and(|rest| rest.starts_with("::"))
        })
    }

    pub fn analysis_output_dir(&self) -> PathBuf {
        let base = self
            .output
            .clone()
            .unwrap_or_else(|| PathBuf::from(DEFAULT_ANALYSIS_DIR));
        base.join(&self.crate_name)
    }

    /// Infer crate name from rustc arguments when neither `-p` nor `-f` is set.
    pub fn infer_crate_name_from_rustc_args(&mut self, rustc_args: &[String]) {
        if !self.crate_name.is_empty() && self.crate_name != "main" {
            return;
        }
        // Look for `--crate-name`.
        if let Some(pos) = rustc_args.iter().position(|a| a == "--crate-name") {
            if let Some(name) = rustc_args.get(pos + 1) {
                self.crate_name = name.clone();
                return;
            }
        }
        // Fall back to first `.rs` input path.
        for arg in rustc_args {
            if arg.ends_with(".rs") {
                self.crate_name = std::path::Path::new(arg)
                    .file_stem()
                    .and_then(|s| s.to_str())
                    .unwrap_or("main")
                    .to_string();
                return;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::ReportLevel;

    #[test]
    fn parses_report_level_research_flag() {
        let mut options = Options::default();
        options.parse_from_args(&["--report-level".to_string(), "research".to_string()]);

        assert_eq!(options.config.report_level, ReportLevel::Research);
    }

    #[test]
    fn parses_slice_state_budget_flag() {
        let mut options = Options::default();
        options.parse_from_args(&["--slice-state-budget".to_string(), "50000".to_string()]);
        assert_eq!(options.config.slice_state_budget, Some(50000));

        let mut options = Options::default();
        options.parse_from_args(&["--slice-state-budget".to_string(), "0".to_string()]);
        assert_eq!(options.config.slice_state_budget, None);
    }

    #[test]
    fn parses_loop_semantics_flag() {
        let mut options = Options::default();
        options.parse_from_args(&["--loop-semantics".to_string(), "summary".to_string()]);
        assert_eq!(options.config.loop_semantics, Some(LoopSemantics::Summary));

        let mut options = Options::default();
        options.parse_from_args(&["--loop-semantics".to_string(), "cut".to_string()]);
        assert_eq!(options.config.loop_semantics, Some(LoopSemantics::Cut));
    }

    #[test]
    fn parses_loop_summary_k_flag() {
        let mut options = Options::default();
        options.parse_from_args(&[
            "--loop-semantics".to_string(),
            "summary".to_string(),
            "--loop-summary-k".to_string(),
            "3".to_string(),
        ]);
        assert_eq!(options.config.loop_semantics, Some(LoopSemantics::Summary));
        assert_eq!(options.config.loop_summary_k, 3);
        // The flag alone leaves the semantics at the per-entry-mode default.
        let mut options = Options::default();
        options.parse_from_args(&["--loop-summary-k".to_string(), "2".to_string()]);
        assert_eq!(options.config.loop_semantics, None);
        assert_eq!(options.config.loop_summary_k, 2);
    }

    #[test]
    fn matches_only_the_target_crate() {
        let options = Options {
            crate_name: "dr_1".to_string(),
            ..Options::default()
        };

        assert!(options.targets_current_crate("dr_1"));
        assert!(!options.targets_current_crate("hashbrown"));
    }

    #[test]
    fn parses_cross_crate_prefixes() {
        let mut options = Options::default();
        options.parse_from_args(&[
            "--spn-cross-crate".to_string(),
            "ws_lib,ledger_util".to_string(),
        ]);
        assert_eq!(options.cross_crate, vec!["ws_lib", "ledger_util"]);
        assert_eq!(Options::default().cross_crate, Vec::<String>::new());
    }

    #[test]
    fn cross_crate_matching_stops_at_crate_boundaries() {
        // `--spn-cross-crate ws_lib` must cover the dependency's
        // functions but not an unrelated crate whose name merely shares the
        // prefix (`ws_library`). The boundary is `::` (or an exact name).
        let options = Options {
            cross_crate: vec!["ws_lib".to_string()],
            ..Options::default()
        };

        assert!(options.cross_crate_matches("ws_lib"));
        assert!(options.cross_crate_matches("ws_lib::Ledger::transfer"));
        assert!(options.cross_crate_matches("ws_lib::{impl#1}::transfer"));
        assert!(!options.cross_crate_matches("ws_library::Ledger::transfer"));
        assert!(!options.cross_crate_matches("ws_lib_extra"));
        assert!(!options.cross_crate_matches("ws"));
        assert!(!Options::default().cross_crate_matches("ws_lib::anything"));
    }

    #[test]
    fn normalizes_hyphenated_cargo_package_names() {
        let mut options = Options::default();
        options.parse_from_args(&["-p".to_string(), "foo-bar".to_string()]);

        assert_eq!(options.crate_name, "foo_bar");
        assert!(options.targets_current_crate("foo_bar"));
    }

    #[test]
    fn hyphenated_crate_name_matches_rustc_def_path() {
        let mut options = Options::default();
        options.parse_from_args(&["-p".to_string(), "foo-bar".to_string()]);

        assert!(options.crate_filter_match("foo_bar::f"));
    }

    #[test]
    fn analysis_output_dir_normalizes_hyphenated_crate_name() {
        let mut options = Options::default();
        options.parse_from_args(&[
            "-p".to_string(),
            "foo-bar".to_string(),
            "--spn-analysis-dir".to_string(),
            "./tmp".to_string(),
        ]);

        assert_eq!(
            options.analysis_output_dir(),
            PathBuf::from("./tmp/foo_bar")
        );
    }

    #[test]
    fn analysis_output_dir_uses_target_crate_name() {
        let options = Options {
            crate_name: "dr_1".to_string(),
            output: Some(PathBuf::from("./tmp/spn-tests")),
            ..Options::default()
        };

        assert_eq!(
            options.analysis_output_dir(),
            PathBuf::from("./tmp/spn-tests/dr_1")
        );
    }

    #[test]
    fn parses_bool_guard_abstraction_flag() {
        let options = Options::default();
        assert!(options.config.bool_guard_abstraction);

        let mut options = Options::default();
        options.parse_from_args(&["--bool-guard-abstraction".to_string(), "false".to_string()]);
        assert!(!options.config.bool_guard_abstraction);

        let mut options = Options::default();
        options.parse_from_args(&["--bool-guard-abstraction".to_string(), "true".to_string()]);
        assert!(options.config.bool_guard_abstraction);
    }

    #[test]
    fn partition_switches_default_to_alias_and_original_and_cli_overrides_the_file() {
        use crate::config::{LockGrouper, PartitionSwitch};

        let defaults = crate::config::PnConfig::default();
        assert_eq!(defaults.resource_atomic_partition, PartitionSwitch::Alias);
        assert_eq!(defaults.resource_lock_grouper, LockGrouper::Original);

        let mut help = Vec::new();
        make_options_parser().write_help(&mut help).unwrap();
        let help = String::from_utf8(help).unwrap();
        assert!(help.contains("--resource-atomic-partition"));
        assert!(help.contains("--resource-lock-grouper"));
        assert!(help.contains("comparison runs"));
        assert!(!help.contains("resource-unsafe-partition"));

        let mut options = Options::default();
        options.parse_from_args(&[
            "--resource-atomic-partition".to_string(),
            "legacy".to_string(),
        ]);
        assert_eq!(
            options.config.resource_atomic_partition,
            PartitionSwitch::Legacy
        );
        assert_eq!(options.config.resource_lock_grouper, LockGrouper::Original);

        let path = std::env::temp_dir().join(format!("spn-r44-{}.toml", std::process::id()));
        std::fs::write(
            &path,
            "resource_atomic_partition = \"legacy\"\nresource_lock_grouper = \"ported\"\n",
        )
        .unwrap();
        let mut from_file = Options::default();
        from_file.parse_from_args(&["--config".to_string(), path.display().to_string()]);
        assert_eq!(
            from_file.config.resource_atomic_partition,
            PartitionSwitch::Legacy
        );
        assert_eq!(from_file.config.resource_lock_grouper, LockGrouper::Ported);

        let mut options = Options::default();
        options.parse_from_args(&[
            "--config".to_string(),
            path.display().to_string(),
            "--resource-atomic-partition".to_string(),
            "alias".to_string(),
            "--resource-lock-grouper".to_string(),
            "original".to_string(),
        ]);
        assert_eq!(
            options.config.resource_atomic_partition,
            PartitionSwitch::Alias
        );
        assert_eq!(options.config.resource_lock_grouper, LockGrouper::Original);
        let _ = std::fs::remove_file(&path);
    }

    #[test]
    fn parses_export_concir_net_and_codegen_map_flags() {
        let mut options = Options::default();
        assert_eq!(options.export_concir_net, None);
        assert_eq!(options.codegen_map, None);
        assert!(options.config.reduce_net);

        options.parse_from_args(&[
            "--export-concir-net".to_string(),
            "out/impl_net.json".to_string(),
            "--codegen-map".to_string(),
            "out/codegen.json".to_string(),
        ]);

        assert_eq!(
            options.export_concir_net,
            Some(PathBuf::from("out/impl_net.json"))
        );
        assert_eq!(
            options.codegen_map,
            Some(PathBuf::from("out/codegen.json"))
        );
        assert!(
            !options.config.reduce_net,
            "--export-concir-net must disable Petri-net reduction"
        );
    }
}
