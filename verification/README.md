# Verification records

These are the outputs of the checks in `REPRODUCE.md`, run on 2026-09-28 from a clean copy of this repository on an
M5 Pro Mac (48 GiB, macOS 26.6) with the Mathlib cache already downloaded. Local paths are replaced by `<repo>` (the
clean copy) and `<tools>` (the checker checkouts built by `formal/lean/scripts/tools.sh`); nothing else is edited.

| file | what it records |
|---|---|
| `check.log` | the full output of `bash formal/check.sh`, exit 0 |
| `build.log` | `lake build ThomsonN7 ComparatorChallenges`: 8,928 jobs, 3 `sorry` warnings, all in the challenge file |
| `axioms.log` | `#print axioms` for both theorems: `propext`, `Classical.choice`, `Quot.sound` |
| `statement.log` | exact comparison of the challenge constants with the solution's |
| `negative-control.log` | the same comparison on a challenge with `thomson_seven` flipped: it fails on exactly that theorem |
| `comparator.log` | `bash formal/lean/ComparatorChallenges/run_comparator.sh`: "Your solution is okay!" |
| `second-kernel/nanoda-accept.out` | nanoda on the lean4export export of both theorems: "Checked 47854 declarations with no errors" |
| `second-kernel/nanoda-tampered.*` | nanoda on the same export with one certificate integer changed: rejected |
| `second-kernel/export.sha256` | hash and size of the export |
| `second-kernel.log` | the full output of `bash formal/lean/scripts/second-kernel.sh` |
| `environment.txt` | operating system, machine, tool versions and checker revisions |
