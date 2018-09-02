
#[macro_use]
extern crate log;
extern crate fnv;

pub mod manager;

pub use manager::AstManager;

/// Internal utils
mod util {
    use std::hash::{Hash,Hasher};
    use std::default::Default;

    use fnv;

    pub fn hash<T : Hash>(x: &T) -> u64 {
        let mut hasher : fnv::FnvHasher = Default::default();
        x.hash(&mut hasher);
        hasher.finish()
    }
}
