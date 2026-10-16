//@ check-fail

// Both NVPTX ISA cfgs require `#![feature(nvptx_isa_cfg)]`, regardless of target.

#[cfg(target_has_compute_capability = "12.0")]
//~^ ERROR `cfg(target_has_compute_capability)` is experimental and subject to change
fn compute_capability() {}

#[cfg(target_has_ptx_version = "9.0")]
//~^ ERROR `cfg(target_has_ptx_version)` is experimental and subject to change
fn ptx_version() {}

fn main() {
    let _ = cfg!(target_has_compute_capability = "12.0");
    //~^ ERROR `cfg(target_has_compute_capability)` is experimental and subject to change

    let _ = cfg!(target_has_ptx_version = "9.0");
    //~^ ERROR `cfg(target_has_ptx_version)` is experimental and subject to change
}
