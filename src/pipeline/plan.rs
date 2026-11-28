//! Partition library roots into slices before reduction rewrites place ids.

use super::{Constructed, RunCtx, SlicePlan};

pub fn plan<'a, 'tcx>(ctx: &RunCtx<'_, 'tcx>, constructed: &Constructed<'a, 'tcx>) -> SlicePlan {
    // Library-mode per-entry slicing : partition the
    // concurrent roots by the non-atomic resources they can reach on the
    // *raw* net, before reduction rewrites ids. Main-mode crates have no
    // library roots and take the joint path unchanged.
    let grouped = super::slices::group_roots(&constructed.raw_net, &constructed.library_roots);
    // Shared-resource grouping can put dozens of roots into one
    // slice whose product state space truncates before any of them reaches
    // a wait. Split oversized groups into pair-covering slices of at most
    // `slice_max_roots` roots each.
    let slices = super::slices::partition_groups(
        &constructed.raw_net,
        &constructed.library_roots,
        &grouped,
        ctx.options.config.slice_max_roots,
    );
    if !constructed.library_roots.is_empty() {
        let group_sizes: Vec<usize> = grouped.iter().map(Vec::len).collect();
        let sizes: Vec<usize> = slices.iter().map(Vec::len).collect();
        log::info!(
            "library slicing: {} root(s) -> {} group(s) {:?} -> {} slice(s) {:?} (root cap {:?})",
            constructed.library_roots.len(),
            grouped.len(),
            group_sizes,
            slices.len(),
            sizes,
            ctx.options.config.slice_max_roots
        );
    }
    SlicePlan {
        groups: grouped,
        slices,
    }
}
