use std::fmt;

use serde::{Deserialize, Serialize};

use crate::net::index_vec::Idx;

macro_rules! define_id {
    ($name:ident) => {
        #[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
        #[repr(transparent)]
        pub struct $name(pub u32);

        impl $name {
            pub const fn new(raw: u32) -> Self {
                Self(raw)
            }

            pub const fn raw(self) -> u32 {
                self.0
            }
        }

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(f, stringify!($name))?;
                f.debug_tuple("").field(&self.0).finish()
            }
        }

        impl Idx for $name {
            fn index(self) -> usize {
                self.0 as usize
            }

            fn from_usize(idx: usize) -> Self {
                Self(idx as u32)
            }
        }
    };
}

define_id!(PlaceId);
define_id!(TransitionId);
