//@ compile-flags: --target=nvptx64-nvidia-cuda --crate-type cdylib -Ctarget-cpu=sm_120
//@ needs-llvm-components: nvptx
//@ check-pass
//@ ignore-backends: gcc
#![feature(no_core, rustc_attrs, nvptx_isa_cfg)]
#![no_core]
#[rustc_builtin_macro]
#[macro_export]
macro_rules! compile_error {
    ($msg:expr $(,)?) => {{ /* compiler built-in */ }};
}

#[cfg(not(all(
    target_has_compute_capability = "12.0",
    target_has_compute_capability = "11.0",
    target_has_compute_capability = "10.0",
    target_has_compute_capability = "9.0",
    target_has_ptx_version = "8.7",
)))]
compile_error!("sm_120 or its implied features not enabled");

#[cfg(target_has_compute_capability = "12.0a")]
compile_error!("sm_120a was not requested");
