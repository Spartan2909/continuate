#![feature(allocator_api)]

use std::alloc;
use std::alloc::Allocator;
use std::alloc::Global;
use std::alloc::Layout;
use std::process;
use std::ptr::NonNull;

use continuate_rt_common::TyLayout;

#[export_name = "@rt_alloc_gc"]
pub extern "C" fn alloc_gc(layout: &TyLayout, variant: usize) -> NonNull<()> {
    let layout = Layout::from_size_align(layout.size() as usize, layout.align() as usize).unwrap();
    let ptr = Global
        .allocate(layout)
        .unwrap_or_else(|_| alloc::handle_alloc_error(layout));
    let ptr: NonNull<u8> = ptr.cast();
    ptr.cast()
}

#[export_name = "@rt_exit"]
pub extern "C-unwind" fn exit(code: i64) {
    panic!("{code}");
}
