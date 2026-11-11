# Verification records

Release check of `lean/` (every `.lean` file and the Lake configuration byte-identical to the published ones; sha256 in
`files.sha256`), 2026-11-07, Linux x86_64, Lean v4.34.1, in two fresh copies of the package. Each copy was prepared with
`regen.sh` (`regen.out`: the eight imported upstream-derived modules match `generated.sha256`) and
`lake exe cache get` (Mathlib from the cache).

| file | content |
|---|---|
| `build_test5.tsv`, `build_test5.out` | first copy: `scripts/build_test.sh build_test5.tsv "Kissing5.Statement Kissing5.Solution Kissing5.Axioms"`. The 170 modules reachable from these roots (159 in `Kissing5/`, two in `Kissing/`, `Kissing8.Kernel`, eight regenerated upstream modules) were each compiled one at a time in dependency order (`lean -j1`). Wall time and peak resident memory (KiB) are recorded per module; all exited 0. Total 3.41 h; largest peak 9018016 KiB (8.60 GiB, `ThomsonGen.M2`). Then the axiom check of the script: "6 of 6 theorems reported, 0 outside" the three standard axioms, "BUILD TEST OK" |
| `comparator5.out`, `comparator5.time` | second copy: `scripts/run_comparator.sh comparator5.json`, after compiling every module once with `lake build` (one at a time). Output: lean4export, "Lean default kernel accepts the solution", "Your solution is okay!", exit 0, for the six theorems of `lean/comparator5.json`. 2 h 41 min wall, peak 6763888 KiB |
| `axioms5.out` | `#print axioms`: `[propext, Classical.choice, Quot.sound]` for all six (the same output in both copies) |
| `files.sha256` | sha256 of the Lean files present in the checked copies and the Lake configuration (`regen.sh` writes all split modules; eight of them are imported); identical in both copies |
| `regen.out` | output of `regen.sh` |
| `scan_upstream.txt` | `lean/ThomsonGen/scripts/scan_upstream.py` on the 193 stored Lean files that the proof uses (159 under `lean/Kissing5/`, 33 under `lean/Kissing/`, `lean/Kissing8/Kernel.lean`): 0 verbatim, 45 near-copies, all attributed |
| `second_kernel/` | second-kernel check, see below |

Comparator ran with its non-sandboxing shim `fake-landrun.sh`, because `landrun` was not available on the machine.
Tool revisions and binary sha256: `lean/scripts/tools.sh`. In the logs, `<tools>` stands for the directory of the
prebuilt tools, `<copy2>` for the second copy and `<out>` for the output directory.

## Second kernel

`lean/scripts/second-kernel.sh comparator5.json`, run in the second copy after Comparator:

1. lean4export writes the six theorems of `comparator5.json` and everything they depend on: 4402589 lines,
   264 MB, sha256 in `export.sha256`.
2. nanoda (nanoda_lib 0.4.19, an independent type checker for Lean 4 written in Rust) checks the export:
   "Checked 37338 declarations with no errors". It prints the six statements and the three axioms used
   (`nanoda-accept.out`, configuration `config.json`). 1 h 15 min wall, peak 6637032 KiB (`run1.time`).
3. Negative control: in a copy of the export, one natural-number literal is changed to a value that occurs nowhere in
   the export. The literal is the longest one that occurs exactly once, 157316 digits. nanoda must reject the copy.
   It does: the failure is in a definitional-equality check of the type checker (`nanoda-tampered.err`), not a parse
   error.

`run1.out` is the first run, with an earlier version of `second-kernel.sh`. That version did the negative control
with inline Python and had no `NEG_ONLY` mode. Steps 1 and 2 passed. Step 3 stopped before nanoda ran, because the
inline Python hit Python's default limit of 4300 digits for integer conversion. That code is now
`lean/scripts/tamper_literal.py`, which lifts the limit.

`run2_negative_control.out` is the rerun of step 3 alone (`NEG_ONLY=1`). Before running, it checks that the export has
the accepted sha256. This rerun used scripts byte-identical to the published `lean/scripts/second-kernel.sh` and
`tamper_literal.py`.
