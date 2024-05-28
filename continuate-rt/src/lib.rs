#![feature(allocator_api)]

mod garbage_collector;

#[cfg(debug_assertions)]
use tracing::debug;

#[cfg(debug_assertions)]
use tracing_subscriber::filter::LevelFilter;

#[cfg(not(miri))]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[export_name = "cont_rt_init"]
#[allow(clippy::missing_panics_doc)]
pub extern "C" fn enable_log() {
    #[cfg(debug_assertions)]
    continuate_common::init_tracing(LevelFilter::DEBUG).expect("failed to instantiate logger");

    garbage_collector::init_garbage_collector();

    #[cfg(debug_assertions)]
    debug!("runtime initialised");
}
