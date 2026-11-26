# AI disclosure

AI models produced the content of this repository: the Lean formalisation, the generators, the numerical computations
and checks, the figures and the text. The repository owner chose the problem, approved the Lean statements, directed
the work and decided on scope and publication. The owner did not check the mathematics or the Lean code line by line.

**Models**
- Claude Opus 5.5 (Anthropic, via Claude Code) did the work.
- Before the work started, a separate read-only instance of Claude Fable 5.2 (Anthropic) reviewed the numerical plan
  and the literature. It advised that a formal $`\kappa(5) \le 44`$ was out of reach with the pipeline of the time:
  degree 30 to 32, Gram matrices up to size 969, and a high-precision solver would be needed. It found
  $`\kappa(5) \le 45`$ feasible. The owner chose $`\kappa(5) \le 45`$ for version 1 and then asked for 44 as well.
  Version 2 needed exactly the changes the review named: a high-precision solver, a symmetry-reduced formulation, and
  a redesigned Lean checker.
- Fable also did literature and solver research for version 2 and a few planning reviews. It did not write any of
  the published code or data.
- Before the publication of version 1, a separate read-only instance of Claude Opus 5.5, without the working context,
  reviewed the statement, the proof chain, the certificate data and the documentation. Version 2 had a review of the
  same kind (below).
- The commits carry a `Co-Authored-By: Claude Opus 5.5` trailer.

**Review of version 2.** The review found no soundness problem and no gap between the statement and its
plain-English reading. It checked that the definitions of `Statement44.lean` are word for word those of
`Statement.lean`, followed the proof chain (the degrees `k ≤ 16` of the positivity theorem against `K ≤ 17` in the
checker, the multipliers, the margin, $`n = 45`$), and searched the 502 files of the proof for constructs that weaken
checking (none). With its own code it decoded all 17 $`F`$-blocks of the generated Lean data and compared them exactly
with `cert.json`. It compared the multipliers, sizes and bases of the five sum-of-squares blocks too, and evaluated
their rows and the whole identity at random points modulo a prime, with negative controls. It reported:
- one bug, fixed: the cached $`F`$-block shifts were not yet in the committed `lam.json`, so `regen44.sh` would have
  stopped;
- documentation points, all fixed: the precision of the 256-bit data (written with 60 digits), the source of the
  eigenvalue estimates, the list of regeneration inputs, an unpublished number (now with its log), module counts, a
  checksum label, and a degree in `formalization.yaml`;
- that "40 ≤ κ(5) ≤ 44" is two Lean theorems with textually identical definitions in two namespaces, not one theorem
  (now said at the top of the README);
- two nits left unchanged so that the checked Lean files stay as they are: the comment of the `Kissing5` library in
  `lean/lakefile.toml` mentions only the bound 45, and the docstrings of the definitions in `Solution44.lean` are
  shorter than those of `Statement44.lean` (the code is identical);
- that the log of the first run of `check_big_k5.py` does not record the sha256 of the file checked; a rerun that does
  is in `numerics/kissing5/d32/k64/check_big_release.log`.

**Review of version 1.** The review found no mathematical error and no gap between the statement and its plain-English
reading. It decoded the Lean certificate data with its own code and compared it with `cert_D16.json`: the margin, all
$`F`$-blocks, and the multipliers, sizes, bases and sampled entries of the sum-of-squares blocks. It also reran the
exact checker, followed the proof chain from 46 points to the certificate and the positivity degrees, and searched the
files for constructs that weaken checking (none). It reported five documentation points:
- two in `lean/STATEMENT5.md`, both fixed: where the definitions come from, and that the certificate is for exactly
  46 points;
- three in Lean docstrings, left unchanged so that the published Lean files stay byte-identical to the checked ones:
  - the docstring of `GramHalf` (`lean/Kissing/CertK.lean`) says "unit vectors of ℝ³", although the definition is
    used for any dimension;
  - the generated headers of `lean/Kissing5/Addition3_7.lean` and its three siblings say "degrees `k ∈ 7`" for
    "degree `k = 7`" (or 8);
  - the `Q5` docstring in `lean/Kissing5/Kernel.lean` writes $`(k+1)! \cdot U_k/(k+1)`$, which equals the simpler
    $`k! \cdot U_k`$.

Problems found and fixed during the work on 44:
- **Prior work missed.** The literature searches did not find T. S. Tomar's preprint proving $`\kappa(5) \le 43`$
  (Zenodo, first version 2026-10-27). It was pointed out during the release preparation; the drafts had called 44
  the best published upper bound. The README, `STATEMENT44.md`, `CITATION.cff` and `formalization.yaml` now cite it
  and say that 44 is not the best known bound.
- **Precision of the data.** The first degree-32 data were written in double precision. The solution then satisfied
  the true identity only to about $`10^{-10}`$, far above the smallest eigenvalues of its Gram matrices, so it could
  not be rounded. The data were recomputed at 256 bits and written with 60 significant digits (`sdpa5.py`, `HP=1`) and the solver warm-started
  from the earlier solution.
- **Smallest eigenvalues below double precision.** The shifts of the $`LDL^T`$ packing need an estimate of the
  smallest eigenvalue of each Gram matrix. Double precision cannot resolve it, so a fixed-point $`LDL^T`$ with inverse
  iteration (`numerics/kissing5/d32/hp_blocks.py`) is used. The estimates are cached in `d32/t5/lam.json`. With the
  default scaling $`2^{64}`$ no shift works for one block, so the scaling is $`2^{72}`$.
- **Lean memory.** At degree 32, checking a row of the largest Gram matrix with the version-1 checker took more than
  4 GiB; the core-only tree-shaped row checks take 0.24 GB. The $`F`$-part, written as in version 1, kept about 4 GB of
  intermediate values in the kernel; balanced sums fixed this (`Tree/FPart.lean`).
- **A literal hashing collision.** The kernel hashes a natural-number literal by its low 64 bits. Large values are
  written as trees of literal pieces, and most pieces ended in 64 zero or 64 one bits. So the kernel's caches filled
  with colliding keys, and the modules that add up many chunk values timed out. The generator now chooses piece
  boundaries so that all pieces have distinct low 64 bits, and it adds the chunk values in groups of 8.
- **A name not qualified.** In a first version of the composition module, an unqualified `gKE` became an automatically
  bound variable. Elaborating the resulting error used more memory than the limit set for the machine. The generator
  now writes `Kissing.gKE`.
- **Regeneration.** The first regeneration recomputed an eigenvalue estimate instead of using the cached, rounded value
  that the built files had used. It gave a different, also valid, certificate. Since then the cached values are part
  of the inputs, and `regen44.sh` refuses to continue if any is recomputed. The shifts of the 17 $`F`$-blocks came from
  a LAPACK eigenvalue routine, which may differ between machines in the last bits. They are cached too, so the
  regeneration does not depend on the machine.

Problems found and fixed during the work on 45:
- **Rounding precision.** Rounding the certificate with 28 bits, as in dimension 4, failed: the kernels of $`S^4`$
  amplify the rounding error. 40 bits work.
- **Memory.** The first chunking of the large sum-of-squares blocks (10 rows per module) needed about 10.9 GB per
  module, above the 9 GB limit set for the build machine. It was re-emitted with 4 to 8 rows per module.
- **Recursion limit.** A composition module hit Lean's recursion limit; the five composition modules now set
  `maxRecDepth`.
- **Second-kernel script.** The first negative control of the second-kernel check stopped on Python's digit limit
  before it ran (see `verification/README.md`). For 44, the first negative control was stopped by the 9 GiB memory
  limit, because `tamper_literal.py` read the whole 1.86 GB export into memory. It was rewritten to read the export
  line by line, with the same output, and the rerun passed (see `verification44/README.md`).

AI review is not peer review, and no human expert has checked this work. In the terminology of the Lean community
this is a *warrant*, not a human-readable proof.

**What is checked by software**
- The Lean 4 kernel checks the formalisation in `lean/`. `#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
- Comparator checks that the proved theorems have the statements of `lean/Kissing5/Statement44.lean` and
  `lean/Kissing5/Statement.lean`. It ran without the `landrun` sandbox (`verification44/`, `verification/`).
- nanoda, an independent type checker for Lean 4, accepts the lean4export exports of the theorems and rejects copies
  with one changed number.
- Exact Python checkers that share no code with the rounding accept the certificates:
  - `numerics/kissing5/check_big_k5.py` for 44;
  - `numerics/kissing5/check_cert_k5.py` for 45, which also rejects ten tampered versions.
- The generators check every identity and every packing exactly before writing the Lean files; the Lean kernel then
  checks them again.
- `lean/regen44.sh` checks the regenerated certificate modules against the sha256 of the files that were compiled.

What remains to be trusted:
- that the statement files express the intended theorems (see `lean/STATEMENT44.md` and `lean/STATEMENT5.md`);
- the Mathlib definitions used in the statement files, which import only Mathlib;
- the Lean kernel and toolchain (the second kernel is an independent check of the kernel's verdict);
- Comparator and lean4export (run without the `landrun` sandbox).
