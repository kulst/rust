//@ compile-flags: --target=nvptx64-nvidia-cuda --crate-type cdylib -Ctarget-feature=+sm_90,+ptx90
//@ needs-llvm-components: nvptx
//@ check-fail
//@ ignore-backends: gcc
#![feature(no_core)]
#![no_core]
//~? ERROR target feature `sm_90` cannot be enabled with `-Ctarget-feature`
//~? ERROR target feature `ptx90` cannot be enabled with `-Ctarget-feature`
