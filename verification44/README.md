# Verification records for κ(5) ≤ 44

Two release checks of `lean/` on Linux x86_64 with Lean v4.34.1, each in a fresh copy of the package. Each copy was
prepared the same way:
- `regen.sh` (`regen.out`: the eight imported upstream-derived modules match `generated.sha256`);
- `lake exe cache get` (Mathlib from the cache);
- the 472 generated modules `Kissing5/Cert44/`, produced by `regen44.sh` from `numerics/kissing5/d32/k64/cert.json`.
  The second copy checked them against `lean/gen/cert44.sha256`. `regen44.sh` itself needs gmpy2, which the Linux
  machine lacked, so the files were generated on the laptop. A regeneration there from the stored inputs was
  byte-identical to them.

## Second copy (the published files)

Every `.lean` file and the Lake configuration are byte-identical to the published ones (`files.sha256`). The
generated `Kissing5/Cert44/` files are those listed in `lean/gen/cert44.sha256`.

| file | content |
|---|---|
| `prebuild44.tsv` | every module of the closure of `Kissing5.Statement44`, `Kissing5.Solution44` and `Kissing5.Axioms44` built one at a time with `lake build <module>`, with wall time and peak resident memory (KiB); all exited 0. 504 modules, 9.06 h in total; largest peak 9039292 KiB (8.62 GiB, `ThomsonGen.M2`), `Kissing5.Cert44.Check` 8789020 KiB, the 448 row-chunk modules at most 2321576 KiB (2.21 GiB) each |
| `comparator44.out`, `comparator44.time` | `scripts/run_comparator.sh comparator44.json`: "Lean default kernel accepts the solution", "Your solution is okay!", exit 0; 12:56:28 wall, peak 8781872 KiB |
| `axioms44.out` | `#print axioms` of `Kissing5/Axioms44.lean`: `[propext, Classical.choice, Quot.sound]` for both theorems |
| `second_kernel/` | `scripts/second-kernel.sh comparator44.json`: export accepted by nanoda, tampered export rejected; see below |
| `files.sha256` | sha256 of the Lean files and the Lake configuration of this copy, including the generated `Kissing5/Cert44/` files |
| `regen.out` | output of `regen.sh` |

## First copy (2026-11-24)

`first_copy/`: the clean build test `scripts/build_test.sh build_test44.tsv "Kissing5.Solution44"`.
- The 502 modules reachable from `Kissing5.Solution44` were each compiled one at a time in dependency order
  (`lean -j1`). They are 472 in `Kissing5/Cert44/`, 19 more in `Kissing5/`, two in `Kissing/`, `Kissing8.Kernel`, and
  eight regenerated upstream modules. All exited 0.
- Total 8.7 h. Largest peak 8951488 KiB (8.54 GiB, `ThomsonGen.M2`); `Kissing5.Cert44.Check` 8775780 KiB; the 448
  row-chunk modules at most 2.21 GiB each.
- The script's own axiom step found no axiom file, because no `Axioms` root was given, and exited 1. The axiom check
  was then run by hand in the same copy (`axioms44.out`: both theorems depend on `[propext, Classical.choice,
  Quot.sound]`).

`build_test44.tsv` (the copy at the top level of this directory) is the table of the README's clean-build summary.

This copy was made before four files gained comments only:
- `Kissing5/Tree/Cert.lean`, `Kissing5/G4/Positivity.lean` and the generated `Kissing5/Cert44/Check.lean`: upstream
  attribution comments;
- `Kissing5/Tree/Core.lean`: one comment rephrased.

`Kissing5/Statement44.lean` and `Kissing5/Axioms44.lean` were added after it. All of them are checked in the second
copy. `first_copy/files.sha256` lists the files of the first copy.

## Upstream-text scans

- `scan_upstream.txt`: `lean/ThomsonGen/scripts/scan_upstream.py` on the 24 stored Lean files that the proof of 44
  uses (`scan_files.txt`): 0 verbatim, 49 near-copies, all attributed, PASS.
- `scan_generated.txt`: the same scan on the 472 generated files of `Kissing5/Cert44/`: 0 verbatim, 2 near-copies (in `Check.lean`), all attributed, PASS.

## Second kernel

`scripts/second-kernel.sh comparator44.json`, run in the second copy after Comparator and the axiom check:

1. lean4export writes the two theorems of `comparator44.json` and everything they depend on: 30321016 lines,
   1857960061 bytes (1.86 GB), sha256 in `export.sha256`. This took about 11 h.
2. nanoda (nanoda_lib 0.4.19, an independent type checker for Lean 4 written in Rust) checks the export:
   "Checked 45712 declarations with no errors". It prints the two statements and the three axioms used
   (`nanoda-accept.out`, configuration `config.json`). This took about 1 h 45 min.
3. Negative control: in a copy of the export, one natural-number literal is changed to a value that occurs nowhere in
   the export. The literal is the longest one that occurs exactly once, 73772 digits. nanoda must reject the copy.
   It does: the failure is in a definitional-equality check of the type checker (`nanoda-tampered.err`), not a parse
   error.

`run1.out` is the first run. Steps 1 and 2 passed. Step 3 was stopped before nanoda ran: the machine's memory guard
stops any single process above 9 GiB, and the version of `tamper_literal.py` used then read the whole 1.86 GB export
into memory (10949564 KiB when stopped; `gate.txt`). Its wall time and memory were not recorded, because the run was
stopped. `tamper_literal.py` was then rewritten to read the export line by line; it keeps only a digest of each long
literal and gives the same output as before. The published `lean/scripts/tamper_literal.py` is that version.

`run2_negative_control.out` is the rerun of step 3 alone (`NEG_ONLY=1`). Before running, it checks that the export has
the accepted sha256. 59 min 34 s wall, peak 3750908 KiB (`run2_negative_control.time`). This rerun used scripts
byte-identical to the published `lean/scripts/second-kernel.sh` and `lean/scripts/tamper_literal.py`. After it, the
Lean files and the Lake configuration of the copy were compared with `files.sha256` again: unchanged.

The rerun of the negative control for the bound 45 (`verification/second_kernel/run2_negative_control.out`) used the
earlier version of `tamper_literal.py`, the one published in version 1 of this package.

Comparator ran with its non-sandboxing shim `fake-landrun.sh`, because `landrun` was not available on the machine.
Tool revisions and binary sha256: `lean/scripts/tools.sh` (the same binaries as for `verification/`). In the logs,
`<tools>` stands for the directory of the prebuilt tools, `<copy2>` for the second copy and `<out>` for the output
directory.
