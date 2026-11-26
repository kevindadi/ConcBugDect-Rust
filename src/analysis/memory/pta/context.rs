use smallvec::SmallVec;

/// A single call-site (caller instance + basic block of the call terminator).
///
/// `value` is the *value fingerprint*: an FNV-1a hash of the
/// proven-constant argument values at the call site (positional, with an
/// explicit "unknown" marker per position), or `None` when no argument is a
/// proven constant. It makes two calls to the same callee at the same call
/// site with different constant arguments (e.g. `account(from)` /
/// `account(to)`) distinct callee contexts even under k=1 truncation, which
/// otherwise drops the caller context and with it the argument value.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct CallSite {
    pub func: u32,
    pub bb: u32,
    pub value: Option<u64>,
}

impl CallSite {
    /// A site without a value fingerprint.
    pub fn new(func: u32, bb: u32) -> Self {
        Self {
            func,
            bb,
            value: None,
        }
    }

    /// A site fingerprinted by the proven-constant argument values.
    pub fn with_args(func: u32, bb: u32, arg_consts: &[Option<u64>]) -> Self {
        let mut any = false;
        let mut hash: u64 = 0xcbf2_9ce4_8422_2325; // FNV-1a offset basis
        for c in arg_consts {
            let v = match c {
                Some(v) => {
                    any = true;
                    *v
                }
                // Out-of-band marker for "unknown at this position"; the
                // separator below keeps `[Some(1)]` distinct from
                // `[Some(0), Some(1)]`-style collisions.
                None => u64::MAX,
            };
            for b in v.to_le_bytes() {
                hash ^= u64::from(b);
                hash = hash.wrapping_mul(0x0000_0100_0000_01b3); // FNV prime
            }
            hash ^= 0xff;
            hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
        }
        Self {
            func,
            bb,
            value: if any { Some(hash) } else { None },
        }
    }
}

/// k-limited call-string context. Empty = the single context-insensitive context.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Context(SmallVec<[CallSite; 2]>);

impl Context {
    pub fn empty() -> Self {
        Context(SmallVec::new())
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn as_slice(&self) -> &[CallSite] {
        &self.0
    }

    /// Append a call site **without** applying the k limit.
    ///
    /// Used by the `Option`-adapter fn-item binding: unlike a normal call, the
    /// adapter invocation must keep the caller context — it carries the
    /// argument value (e.g. the shard index) that distinguishes the payload
    /// elements — while still appending the adapter call site so that two
    /// adapters in the same caller context stay separate.
    pub fn push_site(&mut self, site: CallSite) {
        self.0.push(site);
    }
}

/// Strategy for deriving a callee context from a caller context + call-site.
///
/// This is the precision extension point: `KCallSite` implements call-site
/// sensitivity; object-sensitivity can be added later as another impl.
pub trait ContextPolicy {
    fn extend(&self, caller: Context, site: CallSite) -> Context;
}

/// k-CFA call-site sensitivity. `k = 0` ⇒ context-insensitive.
pub struct KCallSite {
    k: usize,
}

impl KCallSite {
    pub fn new(k: usize) -> Self {
        Self { k }
    }
}

impl ContextPolicy for KCallSite {
    fn extend(&self, caller: Context, site: CallSite) -> Context {
        if self.k == 0 {
            return Context::empty();
        }
        let mut v = caller.0;
        v.push(site);
        let len = v.len();
        if len > self.k {
            v.drain(0..len - self.k);
        }
        Context(v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_context_is_singleton() {
        assert_eq!(Context::empty(), Context::empty());
        assert!(Context::empty().is_empty());
    }

    #[test]
    fn k0_policy_is_insensitive() {
        let p = KCallSite::new(0);
        let c0 = Context::empty();
        let c1 = p.extend(c0.clone(), CallSite::new(1, 2));
        assert_eq!(c0, c1);
    }

    #[test]
    fn k1_policy_keeps_last_callsite() {
        let p = KCallSite::new(1);
        let c0 = Context::empty();
        let cs1 = CallSite::new(1, 2);
        let cs2 = CallSite::new(3, 4);
        let c1 = p.extend(c0, cs1);
        let c2 = p.extend(c1.clone(), cs2);
        assert_ne!(c1, c2);
        assert_eq!(c2, p.extend(Context::empty(), cs2));
    }

    #[test]
    fn push_site_keeps_the_caller_prefix() {
        // The Option-adapter fn-item binding appends the adapter
        // call site without truncating, so callers reached through different
        // argument paths (store.len(0) vs store.len(1)) stay distinct.
        let p = KCallSite::new(1);
        let site = CallSite::new(9, 7);
        let caller_a = p.extend(Context::empty(), CallSite::new(1, 2));
        let caller_b = p.extend(Context::empty(), CallSite::new(3, 4));
        let mut a = caller_a.clone();
        let mut b = caller_b.clone();
        a.push_site(site);
        b.push_site(site);
        assert_ne!(a, b);
        assert_eq!(a.as_slice().len(), 2);
        assert_eq!(a.as_slice()[1], site);
        // The normal policy truncates both to the same adapter site.
        assert_eq!(p.extend(caller_a, site), p.extend(caller_b, site));
    }

    #[test]
    fn value_fingerprint_splits_the_same_call_site() {
        // Same caller + basic block, different proven-constant arguments: the
        // that value fingerprint keeps the callee contexts distinct even
        // after k=1 truncation.
        let p = KCallSite::new(1);
        let caller = p.extend(Context::empty(), CallSite::new(5, 6));
        let a0 = p.extend(caller.clone(), CallSite::with_args(9, 2, &[None, Some(0)]));
        let a1 = p.extend(caller.clone(), CallSite::with_args(9, 2, &[None, Some(1)]));
        assert_ne!(a0, a1);
        // Without any constant argument the fingerprint is absent, so the
        // site is the plain one.
        let plain = CallSite::with_args(9, 2, &[None, None]);
        assert_eq!(plain.value, None);
        assert_eq!(plain, CallSite::new(9, 2));
        // Positions are part of the fingerprint.
        assert_ne!(
            CallSite::with_args(9, 2, &[Some(1), None]).value,
            CallSite::with_args(9, 2, &[None, Some(1)]).value
        );
    }
}
