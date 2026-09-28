# Reproduce the checked result

## Requirements

Install Lean's `elan` toolchain manager, Git and Python 3. The build needs about 14 GB of RAM and 10 GB of disk, and
internet access the first time, for the pinned Lean toolchain, Mathlib and Mathlib's prebuilt cache. The second-kernel
check also needs `cargo` (Rust).

Pins:
- Lean: `leanprover/lean4:v4.34.1`
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`
- Full dependency revisions: `formal/lean/lake-manifest.json`
- Checkers (fetched and built by `formal/lean/scripts/tools.sh`): Comparator `fd5d5bcf14177b187f66d4502071268d877887c3`,
  lean4export `076e8e57707e813375e8f9da8bf989799ace9680`, nanoda_lib `3a2407216ee84a75f9e1aead6803d0578be06ae7`

## One command

From this repository:

```sh
bash formal/check.sh
```

This checks the hashes of the two Lean files and that their first 310 lines are identical, scans the solution for
`sorry`, `native_decide`, extra axioms and metaprogramming, checks the paper-to-Lean index, fetches the Mathlib cache,
builds the proof and the challenge, prints the axioms of both theorems, compares every challenge constant with the
solution's exactly, and finally runs a negative control: a copy of the challenge with the inequality of `thomson_seven`
flipped must be rejected by that comparison. It prints `DONE: all checks above passed` and then
`NEGATIVE CONTROL OK`, and stops at the first failing step.

From a clean copy on an M5 Pro Mac (48 GiB) with the Mathlib cache already downloaded, it took 599 s (the build itself 344 s). Do not run
`lake update`, since that would change the dependency resolution.

## Individual steps

```sh
cd formal/lean
lake exe cache get
lake build ThomsonN7 ComparatorChallenges     # 3 "declaration uses sorry" warnings, all in the challenge file
lake env lean scripts/CheckAxioms.lean        # axioms of both theorems
bash scripts/negative-control.sh              # after scripts/check.sh
bash ComparatorChallenges/run_comparator.sh   # Lean Comparator
bash scripts/second-kernel.sh                 # lean4export + nanoda, and a tampered export
```

Expected axiom list for `ThomsonN7.thomson_seven` and `ThomsonN7.thomson_seven_unique`:

```text
[propext, Classical.choice, Quot.sound]
```

The Comparator prints `Your solution is okay!`. The second-kernel script prints nanoda's
`Checked 47854 declarations with no errors` for the real export and requires nanoda to reject the tampered one.

On macOS with a recent Xcode SDK the nanoda link step can fail with a `tapi` error about `libSystem.B.tbd`; set
`SDKROOT=/Library/Developer/CommandLineTools/SDKs/MacOSX26.sdk` (or another older SDK) for that build.

## Original evidence

The logs of the runs from a clean copy of this repository are in `verification/`, with local paths replaced by
`<repo>` and `<tools>`:

- `verification/check.log`: `formal/check.sh`, exit 0.
- `verification/build.log`, `axioms.log`, `statement.log`, `negative-control.log`: the individual outputs of that run.
- `verification/comparator.log`: the Lean Comparator run.
- `verification/second-kernel/`: the nanoda output for the real export and for the tampered export, and the export's hash.
- `verification/environment.txt`: machine, operating system and tool versions.
