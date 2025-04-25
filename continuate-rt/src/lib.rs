#![allow(unsafe_code)]
#![warn(clippy::missing_inline_in_public_items)]

mod garbage_collector;

pub mod layout;

pub mod slice;

use std::error::Error;
use std::io;

#[cfg(debug_assertions)]
use tracing::debug;

use tracing_subscriber::filter::LevelFilter;

#[export_name = "cont_rt_init"]
#[allow(clippy::missing_panics_doc)]
#[inline]
pub extern "C" fn enable_log() {
    #[cfg(debug_assertions)]
    init_tracing(LevelFilter::DEBUG).expect("failed to instantiate logger");

    #[cfg(debug_assertions)]
    debug!("runtime initialised");
}

/// ## Safety
///
/// - All garbage-collected values must be valid.
///
/// - No garbage-collected values may be accessed again.
#[inline]
#[export_name = "cont_rt_cleanup"]
pub unsafe extern "C" fn cleanup() {
    #[cfg(debug_assertions)]
    debug!("runtime cleaning up");

    // SAFETY: Must be ensured by caller.
    unsafe {
        garbage_collector::clear();
    }
}

/// ## Errors
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
