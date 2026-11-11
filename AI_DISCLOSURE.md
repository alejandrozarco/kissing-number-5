# AI disclosure

AI models produced the content of this repository: the Lean formalisation, the generators, the numerical computations
and checks, the figures and the text. The repository owner chose the problem, approved the Lean statement, directed
the work and decided on scope and publication. The owner did not check the mathematics or the Lean code line by line.

**Models**
- Claude Opus 5.5 (Anthropic, via Claude Code) did the work.
- Before the work started, a separate read-only instance of Claude Fable 5.2 (Anthropic) reviewed the numerical plan
  and the literature. It advised that a formal $`\kappa(5) \le 44`$ was out of reach with this pipeline and that
  $`\kappa(5) \le 45`$ was feasible. The owner chose $`\kappa(5) \le 45`$.
- Before publication, a separate read-only instance of Claude Opus 5.5, without the working context, reviewed the
  statement, the proof chain, the certificate data and the documentation.
- The commits carry a `Co-Authored-By: Claude Opus 5.5` trailer.

**Review and errors found.** The review found no mathematical error and no gap between the statement and its
plain-English reading. It decoded the Lean certificate data with its own code and compared it with `cert_D16.json`:
the margin, all $`F`$-blocks, and the multipliers, sizes, bases and sampled entries of the sum-of-squares blocks. It
also reran the exact checker, followed the proof chain from 46 points to the certificate and the positivity degrees,
and searched the files for constructs that weaken checking (none). It reported five documentation points:
- two in `lean/STATEMENT5.md`, both fixed: where the definitions come from, and that the certificate is for exactly
  46 points;
- three in Lean docstrings, left unchanged so that the published Lean files stay byte-identical to the checked ones:
  - the docstring of `GramHalf` (`lean/Kissing/CertK.lean`) says "unit vectors of ℝ³", although the definition is
    used for any dimension;
  - the generated headers of `lean/Kissing5/Addition3_7.lean` and its three siblings say "degrees `k ∈ 7`" for
    "degree `k = 7`" (or 8);
  - the `Q5` docstring in `lean/Kissing5/Kernel.lean` writes $`(k+1)! \cdot U_k/(k+1)`$, which equals the simpler
    $`k! \cdot U_k`$.

Problems found and fixed during the work:
- **Rounding precision.** Rounding the certificate with 28 bits, as in dimension 4, failed: the kernels of $`S^4`$
  amplify the rounding error. 40 bits work.
- **Memory.** The first chunking of the large sum-of-squares blocks (10 rows per module) needed about 10.9 GB per
  module, above the 9 GB limit set for the build machine. It was re-emitted with 4 to 8 rows per module.
- **Recursion limit.** A composition module hit Lean's recursion limit; the five composition modules now set
  `maxRecDepth`.
- **Second-kernel script.** The first negative control of the second-kernel check stopped on Python's digit limit
  before it ran (see `verification/README.md`).

AI review is not peer review, and no human expert has checked this work. In the terminology of the Lean community
this is a *warrant*, not a human-readable proof.

**What is checked by software**
- The Lean 4 kernel checks the formalisation in `lean/`. `#print axioms` reports `[propext, Classical.choice, Quot.sound]`.
- Comparator checks that the proved theorems have the statements of `lean/Kissing5/Statement.lean`. It ran without the
  `landrun` sandbox (`verification/`).
- nanoda, an independent type checker for Lean 4, accepts the lean4export export of the six theorems and rejects a
  copy with one changed number.
- An exact Python checker (`numerics/kissing5/check_cert_k5.py`, sharing no code with the rounding) accepts the
  certificate and rejects ten tampered versions. The generators check every addition identity with sympy before
  writing the Lean files; the Lean kernel then checks them again.

What remains to be trusted:
- that `lean/Kissing5/Statement.lean` expresses the intended theorem (see `lean/STATEMENT5.md`);
- the Mathlib definitions used in `lean/Kissing5/Statement.lean`, which imports only Mathlib;
- the Lean kernel and toolchain (the second kernel is an independent check of the kernel's verdict);
- Comparator and lean4export (run without the `landrun` sandbox).
