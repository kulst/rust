//@ add-minicore
//@ compile-flags: --target=nvptx64-nvidia-cuda --crate-type lib -Ctarget-cpu=sm_90
//@ needs-llvm-components: nvptx
//@ check-fail
//@ ignore-backends: gcc
#![feature(no_core, nvptx_target_feature)]
#![no_core]

extern crate minicore;
use minicore::*;

#[target_feature(enable = "sm_90")]
//~^ ERROR target feature `sm_90` cannot be enabled with `#[target_feature]`
pub unsafe fn disallowed_sm() {}

#[target_feature(enable = "ptx90")]
//~^ ERROR target feature `ptx90` cannot be enabled with `#[target_feature]`
pub unsafe fn disallowed_ptx() {}
