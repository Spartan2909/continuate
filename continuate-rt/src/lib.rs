#![allow(unsafe_code)]

pub mod garbage_collector;

pub mod layout;

pub mod slice;

use std::{error::Error, io};

#[cfg(debug_assertions)]
macro_rules! debug {
    ($($tt:tt)*) => {
        tracing::debug!($($tt)*)
    };
}
use debug;

#[cfg(not(debug_assertions))]
macro_rules! debug {
    ($($tt:tt)*) => {};
}

use tracing_subscriber::filter::LevelFilter;

#[unsafe(export_name = "cont_rt_init")]
#[expect(clippy::missing_panics_doc)]
#[cfg(feature = "object")]
pub extern "C" fn init_for_object() {
    unsafe extern "C" {
        #[link_name = "cont_stack_maps"]
        static STACK_MAPS: u8;
    }

    #[cfg(debug_assertions)]
    init_tracing(LevelFilter::DEBUG).expect("failed to instantiate logger");

    garbage_collector::set_stack_maps_ptr((&raw const STACK_MAPS).cast());

    #[cfg(debug_assertions)]
    debug!("runtime initialised");
}

/// # Safety
///
/// - All garbage-collected values must be valid.
///
/// - No garbage-collected values may be accessed again.
#[cfg(feature = "object")]
#[unsafe(export_name = "cont_rt_cleanup")]
pub unsafe extern "C" fn cleanup() {
    #[cfg(debug_assertions)]
    debug!("runtime cleaning up");

    // SAFETY: Must be ensured by caller.
    unsafe {
        garbage_collector::clear();
    }
}

/// # Errors
///
/// Returns an error if `tracing` instantiation fails.
#[inline]
pub fn init_tracing(filter: LevelFilter) -> Result<(), Box<dyn Error + Send + Sync + 'static>> {
    tracing_subscriber::fmt()
        .with_max_level(filter)
        .without_time()
        .with_writer(io::stderr)
        .try_init()
}
