//! Async compiler callbacks.
//!
//! Override behavior here instead of editing `rust_petri_net_analysis::callback`.

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;

use rust_petri_net_analysis::callback::PTACallbacks;
use rust_petri_net_analysis::options::Options;
use std::fmt::{Debug, Formatter, Result as FmtResult};

/// Async analysis callbacks. Currently delegates entirely to core [`PTACallbacks`].
///
/// Replace or wrap `inner` when adding async alias analysis or other extensions.
pub struct AsyncPTACallbacks {
    inner: PTACallbacks,
}

impl AsyncPTACallbacks {
    pub fn new(options: Options) -> Self {
        Self {
            inner: PTACallbacks::new(options),
        }
    }
}

impl Debug for AsyncPTACallbacks {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        "AsyncPTACallbacks".fmt(f)
    }
}

impl rustc_driver::Callbacks for AsyncPTACallbacks {
    fn config(&mut self, config: &mut rustc_interface::interface::Config) {
        self.inner.config(config);
    }

    fn after_analysis<'tcx>(
        &mut self,
        compiler: &rustc_interface::interface::Compiler,
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        self.inner.after_analysis(compiler, tcx)
    }
}
