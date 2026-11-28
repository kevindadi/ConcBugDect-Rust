extern crate rustc_driver;
extern crate rustc_hir;

use crate::options::{Options, StopAfter};
use crate::util::mem_watcher::MemoryWatcher;
use log::{debug, info, warn};
use rustc_driver::Compilation;
use rustc_hir::def_id::LOCAL_CRATE;
use rustc_interface::interface;
use rustc_middle::ty::TyCtxt;
use std::fmt::{Debug, Formatter, Result};
use std::path::PathBuf;

#[derive(Clone)]
pub struct SpnCallbacks {
    pub options: Options,
    pub output_directory: PathBuf,
    test_run: bool,
}

impl SpnCallbacks {
    pub fn new(options: Options) -> Self {
        let diagnostics_output = options.analysis_output_dir();

        Self {
            options,
            output_directory: diagnostics_output,
            test_run: false,
        }
    }

    fn ensure_output_directory(&self) {
        std::fs::create_dir_all(&self.output_directory).unwrap_or_else(|e| {
            log::debug!("Warning: Failed to create output directory: {}", e);
        });
    }
}

impl Debug for SpnCallbacks {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        "SpnCallbacks".fmt(f)
    }
}

impl Default for SpnCallbacks {
    fn default() -> Self {
        Self::new(Options::default())
    }
}

impl rustc_driver::Callbacks for SpnCallbacks {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        config.opts.optimize = rustc_session::config::OptLevel::No;
        config.opts.debuginfo = rustc_session::config::DebugInfo::None;

        if config.opts.test {
            debug!("in test only mode");
        }
    }

    fn after_analysis<'tcx>(
        &mut self,
        compiler: &rustc_interface::interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        compiler.sess.dcx().abort_if_errors();

        // Dump MIR, then stop before the Petri-net analysis.
        if self.options.stop_after == StopAfter::AfterMir {
            let current_crate_name = tcx.crate_name(LOCAL_CRATE).to_string();
            crate::note_ice_crate_name(&current_crate_name);
            if self.options.targets_current_crate(&current_crate_name) {
                self.output_directory = self.options.analysis_output_dir();
                self.ensure_output_directory();
                let ctx = crate::pipeline::RunCtx {
                    tcx,
                    options: &self.options,
                    crate_name: current_crate_name,
                    output_dir: self.output_directory.clone(),
                };
                crate::pipeline::collect::emit_mir_dots(&ctx);
                info!("Stopping analysis after MIR output");
            } else {
                debug!(
                    "skip MIR dump for crate {} (target crate: {})",
                    current_crate_name, self.options.crate_name
                );
            }
            return Compilation::Stop;
        }

        self.analyze(compiler, tcx);

        // When a stop point is set, stop compilation after analysis.
        if self.options.stop_after != StopAfter::None || self.test_run {
            Compilation::Stop
        } else {
            Compilation::Continue
        }
    }
}

impl SpnCallbacks {
    /// Reuse a previous full analysis when the crate sources, the
    /// analysed options and the driver binary are unchanged. A miss runs the
    /// complete analysis and stores its output artifacts; a hit copies the
    /// stored snapshot back byte for byte and skips translation and BFS.
    fn analyze<'tcx>(&mut self, _compiler: &interface::Compiler, tcx: TyCtxt<'tcx>) {
        // If codegen is disabled, skip the analysis. Because the Petri-net analysis requires MIR.
        // Exception: `--export-concir-net` also supports `cargo check` (`--emit=metadata`) where
        // MIR is still available in `after_analysis` even though codegen is disabled.
        if (tcx.sess.opts.unstable_opts.no_codegen || !tcx.sess.opts.output_types.should_codegen())
            && self.options.export_concir_net.is_none()
        {
            return;
        }

        let current_crate_name = tcx.crate_name(LOCAL_CRATE).to_string();
        crate::note_ice_crate_name(&current_crate_name);

        if !self.options.targets_current_crate(&current_crate_name) {
            debug!(
                "skip Petri net construction for crate {} (target crate: {})",
                current_crate_name, self.options.crate_name
            );
            return;
        }

        self.output_directory = self.options.analysis_output_dir();
        self.ensure_output_directory();

        if let Some(cache) = self.analysis_cache() {
            match cache.key_for(&self.options, &current_crate_name) {
                Ok(key) => {
                    match cache.restore(&key, &self.output_directory) {
                        Ok(true) => return,
                        Ok(false) => info!(
                            "analysis cache miss for {} ({} source file(s), key {})",
                            current_crate_name,
                            key.source_files,
                            &key.hex[..12.min(key.hex.len())]
                        ),
                        Err(err) => {
                            warn!(
                                "analysis cache lookup failed for {}: {err}",
                                current_crate_name
                            )
                        }
                    }
                    self.analyze_uncached(tcx, &current_crate_name);
                    if let Err(err) = cache.store(&key, &self.output_directory) {
                        warn!(
                            "analysis cache store failed for {}: {err}",
                            current_crate_name
                        );
                    }
                    return;
                }
                Err(err) => {
                    info!("analysis cache disabled for {}: {err}", current_crate_name);
                }
            }
        }
        self.analyze_uncached(tcx, &current_crate_name);
    }

    /// v1 caches single-crate analyses only: a cross-crate run also translates
    /// dependency sources (`--spn-cross-crate`), which are not part of the
    /// source hash, so it always takes the full path.
    fn analysis_cache(&self) -> Option<crate::cache::AnalysisCache> {
        if !self.options.cross_crate.is_empty() {
            info!(
                "analysis cache disabled: cross-crate run (v1 hashes only the target crate sources)"
            );
            return None;
        }
        if self.options.export_concir_net.is_some() {
            info!(
                "analysis cache disabled: --export-concir-net writes to an explicit external path"
            );
            return None;
        }
        let cache = crate::cache::AnalysisCache::from_env();
        if cache.is_none() {
            debug!("analysis cache disabled: no cache root configured");
        }
        cache
    }

    fn analyze_uncached<'tcx>(&mut self, tcx: TyCtxt<'tcx>, current_crate_name: &str) {
        let mut mem_watcher = MemoryWatcher::new();
        mem_watcher.start();

        let ctx = crate::pipeline::RunCtx {
            tcx,
            options: &self.options,
            crate_name: current_crate_name.to_string(),
            output_dir: self.output_directory.clone(),
        };
        let collected = crate::pipeline::collect(&ctx);
        if collected.stop {
            return;
        }
        let analysis = crate::pipeline::analyze_resources(&ctx, &collected);
        let mut constructed = crate::pipeline::construct(&ctx, &collected, analysis);
        let plan = crate::pipeline::plan(&ctx, &constructed);
        let explored = crate::pipeline::explore(&ctx, &mut constructed, &plan);
        if explored.stop == crate::pipeline::PhaseStop::AfterPointsTo {
            return;
        }
        crate::pipeline::project(&ctx, &constructed, &explored);
        if ctx.options.stop_after != StopAfter::AfterStateGraph {
            mem_watcher.stop();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn callbacks_new_does_not_create_output_directory() {
        let output_root = std::env::temp_dir().join(format!(
            "rustpta_callbacks_new_no_create_{}",
            std::process::id()
        ));
        let output_dir = output_root.join("target_crate");
        let _ = std::fs::remove_dir_all(&output_root);

        let options = Options {
            crate_name: "target_crate".to_string(),
            output: Some(output_root.clone()),
            ..Options::default()
        };

        let callbacks = SpnCallbacks::new(options);

        assert_eq!(callbacks.output_directory, PathBuf::from(&output_dir));
        assert!(!output_dir.exists());

        let _ = std::fs::remove_dir_all(&output_root);
    }
}
