//@ compile-flags: --target=nvptx64-nvidia-cuda --crate-type cdylib -C target-cpu=sm_90
//@ needs-llvm-components: nvptx
//@ check-pass
//@ ignore-backends: gcc
#![feature(no_core, rustc_attrs, nvptx_isa_cfg)]
#![no_core]
#![allow(dead_code)]

#[rustc_builtin_macro]
#[macro_export]
macro_rules! compile_error {
    ($msg:expr $(,)?) => {{ /* compiler built-in */ }};
}

// -Ctarget-cpu=sm_90 directly enables sm_90 and ptx78.
#[cfg(not(all(target_has_compute_capability = "9.0", target_has_ptx_version = "7.8",)))]
compile_error!("direct target features not enabled");

// Versions are cumulative: earlier compute capabilities and PTX versions are set too.
#[cfg(not(all(
    target_has_compute_capability = "7.0",
    target_has_compute_capability = "8.0",
    target_has_ptx_version = "7.1",
    target_has_ptx_version = "7.4",
)))]
compile_error!("implied target features not enabled");

#[cfg(target_has_ptx_version = "8.0")]
compile_error!("sm_90 requires only ptx78, but ptx80 enabled");
#[cfg(target_has_compute_capability = "9.0a")]
compile_error!("sm_90 does not support sm_90a");
