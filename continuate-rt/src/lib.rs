#![feature(allocator_api)]

mod garbage_collector;

#[cfg(debug_assertions)]
use tracing_subscriber::filter::LevelFilter;

#[cfg(not(miri))]
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

#[cfg(debug_assertions)]
#[export_name = "cont_rt_enable_log"]
#[allow(clippy::missing_panics_doc)]
pub extern "C" fn enable_log() {
    continuate_common::init_tracing(LevelFilter::DEBUG).expect("failed to instantiate logger");
}

#[cfg(not(debug_assertions))]
#[export_name = "cont_rt_enable_log"]
#[inline(always)]
pub extern "C" fn cont_rt_enable_log() {}
