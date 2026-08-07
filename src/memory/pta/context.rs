use smallvec::SmallVec;

/// A single call-site (caller instance + basic block of the call terminator).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct CallSite {
    pub func: u32,
    pub bb: u32,
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
        let c1 = p.extend(c0.clone(), CallSite { func: 1, bb: 2 });
        assert_eq!(c0, c1);
    }

    #[test]
    fn k1_policy_keeps_last_callsite() {
        let p = KCallSite::new(1);
        let c0 = Context::empty();
        let cs1 = CallSite { func: 1, bb: 2 };
        let cs2 = CallSite { func: 3, bb: 4 };
        let c1 = p.extend(c0, cs1);
        let c2 = p.extend(c1.clone(), cs2);
        assert_ne!(c1, c2);
        assert_eq!(c2, p.extend(Context::empty(), cs2));
    }
}
