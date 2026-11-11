# Numerics for dimension 5

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
