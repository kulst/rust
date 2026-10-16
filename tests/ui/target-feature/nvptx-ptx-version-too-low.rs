//@ compile-flags: --target=nvptx64-nvidia-cuda --crate-type cdylib -Ctarget-cpu=sm_90 -Zptx-version=7.7
//@ needs-llvm-components: nvptx
//@ check-fail
//@ ignore-backends: gcc
#![feature(no_core)]
#![no_core]

//~? ERROR PTX version 7.7 is incompatible with `-Ctarget-cpu=sm_90`
