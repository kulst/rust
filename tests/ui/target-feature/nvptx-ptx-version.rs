//@ compile-flags: --target=nvptx64-nvidia-cuda --crate-type cdylib -Ctarget-cpu=sm_90 -Zptx-version=9.0
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
    target_has_compute_capability = "9.0",
    target_has_ptx_version = "9.0",
    target_has_ptx_version = "8.8",
    target_has_ptx_version = "7.8",
)))]
compile_error!("PTX 9.0 or implied versions are missing");

#[cfg(target_has_ptx_version = "9.1")]
compile_error!("PTX 9.1 was not requested");
