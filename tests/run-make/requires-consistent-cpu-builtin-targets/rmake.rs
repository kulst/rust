// Check that only the intended built-in targets opt into treating
// `-Ctarget-cpu` as a target modifier.
//
// The test prints the target-spec JSON for all built-in targets known to the
// compiler and verifies that only the intended targets have
// `requires-consistent-cpu` set to true.
//
// The behavior of `requires-consistent-cpu` itself is tested separately.
use std::collections::BTreeSet;

use run_make_support::*;
use serde_json::Value;

fn main() {
    let expected = BTreeSet::from(["amdgcn-amd-amdhsa", "avr-none", "nvptx64-nvidia-cuda"]);

    let target_list = rustc().print("target-list").run().stdout_utf8();

    let actual = target_list
        .lines()
        .filter(|target| requires_consistent_cpu(target))
        .collect::<BTreeSet<_>>();

    assert_eq!(
        actual, expected,
        "unexpected set of built-in targets with `requires-consistent-cpu = true`"
    );
}

fn requires_consistent_cpu(target: &str) -> bool {
    let json = rustc()
        .arg("-Zunstable-options")
        .target(target)
        .print("target-spec-json")
        .run()
        .stdout_utf8();

    let spec: Value = serde_json::from_str(&json).unwrap();

    spec.get("requires-consistent-cpu").and_then(Value::as_bool).unwrap_or(false)
}
