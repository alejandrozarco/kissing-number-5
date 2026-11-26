# Numerics for dimension 5

## Version 1: the certificate for 46 points (κ(5) ≤ 45)

Python 3 with numpy, scipy, cvxpy (Clarabel) for the floating-point SDP; python-flint for the exact checker. The code
builds on `../kissing3/` (`k3.py`, `polyk.py`, `round_k3.py`) and replaces the kernels of $`S^2`$ by those of $`S^4`$.

| file | content |
|---|---|
| `k5.py` | the three-point SDP for $`S^4`$: `test`, `bv D` (bound), `fixn D N` (fixed-$`n`$ problem, margin `e`), `mu D N FRAC` (interior solution), `check TAG` (float check) |
| `sym.py`, `symtest.py` | the reduction of the sum-of-squares part by the symmetric group on $`(u, v, t)`$ (`SYM=1`), and its test against the unreduced form |
| `run.sh` | runs `k5.py` at low priority with a memory watchdog; logs to `logs/` |
| `round_k5.py` | expands the reduced solution to ordinary Gram matrices and rounds it to an exact rational certificate |
| `check_cert_k5.py` | independent exact checker (shares no code with the rounding) |
| `check_controls_k5.py` | ten tampered certificates, all of which the checker must reject |
| `cert_D16.json` | the certificate: $`n = 46`$, total degree 16, $`e = 1/32`$, blocks $`F_0, \dots, F_8`$ and the sum-of-squares blocks |
| `results.jsonl`, `checks.jsonl` | floating-point results by run, and the float check of the interior solution |
| `sol/` | floating-point solutions (`*_sym` with the reduction, `*_mlin2` with the multipliers $`1/2 - x`$ only) |
| `logs/` | the logs of the runs, the rounding, the exact check and the controls |

Environment variables of `k5.py`:
- `SYM=1`: use the symmetry reduction;
- `MULTS=lin2`: use only the multipliers $`1/2 - x`$ (besides $`1`$ and the Gram determinant);
- `DEL=D`: add an explicit two-point (Delsarte) term of degree `D`;
- `SOLVER=SCS`: use the low-memory first-order solver.

The certificate run was `SYM=1 MULTS=lin2 ./run.sh mu 16 46 0.5`, then `python3 round_k5.py
sol/fixn_D16_n46_mu0.5_sym_mlin2.npz cert_D16.json 40`.

Unfinished runs in `logs/`:
- **Watchdog stops.** Some logs end with a memory-watchdog stop. Those runs (e.g. `bv 16` without `MULTS=lin2`)
  exceeded the limit set for the machine and were redone with less memory.
- **No `rc` line.** Logs without an `rc` line (`bv_18_`, `fixn_14_45_`) are runs stopped by a machine restart.
- **`round_D16.log`.** The failed rounding with 28 bits.
- **`check_fixn_..._.log`.** The first attempt stopped on a wrong degree setting; the second attempt in the same file
  passed.

## Version 2: the certificate for 45 points (κ(5) ≤ 44)

Python 3 with numpy, scipy, mpmath, python-flint; gmpy2 for `lean/gen/gen_t5.py`; the solver
[SDPA-GMP](https://github.com/nakatamaho/sdpa-gmp) 7.1.3, built locally.

| file | content |
|---|---|
| `sdpa5.py` | the fixed-$`n`$ three-point program with the $`S_3`$ reduction, written in SDPA sparse format (`write D N OUT`), and the reader of SDPA-GMP's output (`read`); `HP=1` computes the data at 256 bits and writes 60 significant digits |
| `sdpa_ckpt.py` | runs SDPA-GMP in chunks of iterations, each chunk starting from the previous one's output, so that a long solve survives restarts |
| `blockeig_sdpa.py` | floating-point eigenvalue diagnostics of the blocks of a solution |
| `d32/hp_blocks.py` | high-precision block diagnostics: exact parse, fixed-point $`LDL^T`$, smallest eigenvalue by inverse iteration |
| `d32/round_hp.py` | exact rounding of an SDPA-GMP solution to a certificate, with exact checks: identity coefficient by coefficient, $`LDL^T`$ for the $`F_k`$, congruence certificates for the Gram matrices |
| `d32/neg_control_pd.py` | negative controls of the congruence certificate: $`B - c I`$ for $`c`$ just above and just below $`\lambda_{\min}(B)`$ must fail and pass |
| `check_big_k5.py` | independent exact checker for large certificates (shares no code with the rounding): the identity as polynomials and at three random points in matrix form, and positive definiteness by an Arb-certified congruence |
| `d32/k64/cert.json.xz` | the certificate: $`n = 45`$, total degree 32, $`e = 2^{-25}`$, blocks $`F_0, \dots, F_{16}`$ and the Gram matrices of sizes 969, 816, 816, 816, 680 (155 MB uncompressed, sha256 `69d25a7c…167d`) |
| `d32/k64/round.log`, `d32/k64/check_big.log` | the rounding and the independent check of that certificate |
| `d32/hp072.out.xz` | the SDPA-GMP solution that was rounded (chunk 72 of the high-precision solve; sha256 of the decompressed file `5794e7e4…9fcb`). Each chunk stops after one iteration, so SDPA-GMP reports `phase.value = noINFO` (no stopping rule reached); the run was not continued because the margin was already large enough to round |
| `d32/k5_D32_n45_hp.dat-s.meta.json`, `d32/k5_D32_n45_hp.dat-s.sha256` | block structure and sha256 of the SDP file (140 MB, not stored; `HP=1 python3 sdpa5.py write 32 45` writes it) |
| `d32/t5/lam.json` | cached smallest-eigenvalue estimates for `lean/gen/gen_t5.py` (an input of `lean/regen44.sh`) |
| `sdpa/s24.log`, `sdpa/w24.log` | the degree-24 run for $`n = 45`$ (double-precision data, 200 bits): optimal, $`e = -4.76 \cdot 10^{-9} < 0`$, so degree 24 does not give 44 |
| `d32/k64/check_big_release.log` | a rerun of `check_big_k5.py` on the decompressed `cert.json.xz`, with the sha256 of the file checked |
| `d32/k64/reround_release.log` | a reproduction from the stored inputs: the SDP file and the certificate rewritten from `d32/hp072.out.xz`, both byte-identical to the stored ones (sha256) |
| `d32/try072/`, `d32/val16/` | logs of the first rounding of the same solution (KBITS 150, also passed) and of the validation of the method on degree 16 |

The solve: SDPA-GMP through `sdpa_ckpt.py`, one iteration per chunk, at 256 bits for chunks 0–9 and 160 bits from
then on. Chunks 0–70 solved the program written with double-precision data (`sdpa5.py write 32 45`); that data
could not be rounded exactly, so chunks 71–72 solved the high-precision version (`HP=1`), starting from chunk 70. Neither
the double-precision data nor its iterates are stored. At chunk 72: dual $`1 + e`$ with $`e = 6.976 \cdot 10^{-8}`$,
dual feasibility error $`6.3 \cdot 10^{-12}`$.
The rounding claims the smaller margin $`2^{-25} \approx 2.98 \cdot 10^{-8}`$ and absorbs the residual into the Gram
matrix of the multiplier 1.
