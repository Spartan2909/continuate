#![feature(allocator_api)]
#![feature(build_hasher_default_const_new)]
#![feature(const_collections_with_hasher)]

mod garbage_collector;

#[cfg(debug_assertions)]
use tracing::debug;

#[cfg(debug_assertions)]
use tracing_subscriber::filter::LevelFilter;

#[export_name = "cont_rt_init"]
#[allow(clippy::missing_panics_doc)]
pub extern "C" fn enable_log() {
    #[cfg(debug_assertions)]
    continuate_common::init_tracing(LevelFilter::DEBUG).expect("failed to instantiate logger");

    #[cfg(debug_assertions)]
    debug!("runtime initialised");
}
