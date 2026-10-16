//@ check-fail
//@ max-llvm-major-version: 22
//@ needs-llvm-components: nvptx
//@ ignore-backends: gcc
//@ compile-flags: --target=nvptx64-nvidia-cuda --crate-type=lib -Ctarget-cpu=sm_90 -Zptx-version=9.1

#![feature(no_core)]
#![no_core]

//~? ERROR PTX version 9.1 requested by `-Zptx-version` is not supported by LLVM
