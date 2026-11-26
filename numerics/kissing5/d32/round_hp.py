"""Exact rounding of an SDPA-GMP solution of the S3-reduced fixed-n program (sdpa5.py, HP=1 data) to a rational
certificate, with exact checks that scale to D = 32.

usage: python3 round_hp.py PROBLEM.dat-s RESULT.out OUT.json KBITS E [PBITS]

  PROBLEM.dat-s   the problem written by `HP=1 python3 sdpa5.py write D N PROBLEM.dat-s` (its .meta.json is read)
  RESULT.out      the SDPA-GMP output (yMat = F_k, ep, the reduced Gram blocks), printed with >= 40 digits
  KBITS           dyadic rounding of F_k and of the expanded Gram matrices (denominator 2^KBITS)
  E               the exact margin claimed (a rational below the solution's e = ep - 1)
  PBITS           fixed-point precision of the positive-definiteness certificates (default 320)

Steps (as ../round_k5.py, which expands with float bases and so cannot be used here):
  1. F_k rounded to dyadics; the target P = -R - E/C(n,2) computed exactly (round_k3.target_poly, kernels of S^4).
  2. The reduced Gram blocks expanded back to ordinary Gram matrices in the monomial basis with the HP orthonormal
     bases of sdpa5.py (mpmath), for the multipliers 1, 1/2-u, 1/2-v, 1/2-t, detG; then rounded to dyadics.
  3. The exact residual P - sum_r g_r z^T B_r z absorbed into the Gram matrix of the multiplier 1 (as round_k5.py);
     the identity is then checked exactly, coefficient by coefficient.
  4. Positive definiteness, exactly: small blocks by an exact LDL^T; large blocks by a congruence certificate: an
     integer matrix W (from a fixed-point LDL^T, W ~ D^{-1/2} L^{-1}) with W B W^T strictly diagonally dominant with a
     positive diagonal (computed exactly with flint); then W B W^T > 0, so W is invertible and B > 0.
"""
import json, os, sys, time, math
from fractions import Fraction as Fr
from math import comb
import numpy as np

os.environ["HP"] = "1"
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
import sdpa5                                   # noqa: E402  (HP bases)
import round_k5                                # noqa: E402  (sets the S^4 kernels in round_k3)
import round_k3 as R                           # noqa: E402
import mpmath                                  # noqa: E402
import flint                                   # noqa: E402
from hp_blocks import parse_ymat, ldl_fixed    # noqa: E402

T0 = time.time()


def log(s):
    print(f"[{time.time() - T0:8.1f}s] {s}", flush=True)


def dy(x, K):
    """nearest dyadic with denominator 2^K of an mpf / Fraction, as an integer numerator."""
    if isinstance(x, Fr):
        return round(x * (1 << K))
    return int(mpmath.nint(x * (mpmath.mpf(2) ** K)))


def expand(Yb, bases, d):
    """sum over parts: sum_ij Y[i][j] b_i b_j^T for each (basis list, reduced block) pair; dict (z1, z2) -> mpf."""
    G = {}
    for Y, basis in Yb:
        r = len(basis)
        for i in range(r):
            bi = basis[i]
            for j in range(r):
                y = Y[i][j]
                if y == 0:
                    continue
                for z1, c1 in bi.items():
                    yc = y * c1
                    for z2, c2 in basis[j].items():
                        key = (z1, z2)
                        G[key] = G.get(key, 0) + yc * c2
    return G


def perm_slots(z, a, b):
    z = list(z); z[a], z[b] = z[b], z[a]
    return tuple(z)


def pd_certificate(Bnum, den, P):
    """Bnum: list of lists of ints, B = Bnum / den (den > 0).  Returns (ok, info)."""
    n = len(Bnum)
    A = np.array([[(x << P) // den for x in row] for row in Bnum], dtype=object)    # fixed point 2^P
    L, d, bad = ldl_fixed(A, P)
    if bad is not None:
        return False, f"fixed-point LDL pivot {bad} <= 0"
    one = 1 << P
    # Linv (unit lower), fixed point: solve L X = I column by column
    Linv = np.zeros((n, n), dtype=object)
    for i in range(n):
        Linv[i, i] = one
        if i:
            # row i of Linv: -sum_{k<i} L[i,k] Linv[k, :i]
            Linv[i, :i] = -np.dot(L[i, :i], Linv[:i, :i]) // one
    # W = D^{-1/2} Linv  (row scaling), still fixed point 2^P
    s = [math.isqrt((one * one * one) // dk) for dk in d]          # s_i ~ 2^P / sqrt(d_i / 2^P) * ... in 2^P units
    W = [[(s[i] * int(Linv[i, j])) >> P for j in range(n)] for i in range(n)]
    Wm = flint.fmpz_mat(W)
    Bm = flint.fmpz_mat(Bnum)
    M = Wm * Bm * Wm.transpose()
    ok = True; worst = None
    for i in range(n):
        mii = M[i, i]
        off = sum(abs(M[i, j]) for j in range(n) if j != i)
        if not mii > off:
            ok = False; worst = i; break
        ratio = int(off * 10 ** 9 // mii) / 1e9
        if worst is None or ratio > worst:
            worst = ratio
    return ok, (f"W B W^T strictly diagonally dominant, max off/diag ratio {worst:.3g}" if ok
                else f"row {worst} not diagonally dominant")


def main(dats, res, out, K, E, P=320):
    meta = json.load(open(dats + ".meta.json"))
    D, n = meta["D"], meta["n"]
    C2 = comb(n, 2)
    names = [nm for nm, _ in meta["blocks"]]
    Ys = parse_ymat(res)
    Yd = {}
    for nm, blk in zip(names, Ys):
        if isinstance(blk[0], list):
            Yd[nm] = [[mpmath.mpf(t) for t in row] for row in blk]
        else:
            Yd[nm] = [mpmath.mpf(t) for t in blk]
    ep = Yd["ep"][0] if not isinstance(Yd["ep"][0], list) else Yd["ep"][0][0]
    efl = ep - 1
    log(f"{res}: D={D} n={n}, solution e = {mpmath.nstr(efl, 12)}, claimed E = {E} ({float(E):.6g}), KBITS={K}")
    Emp = mpmath.mpf(E.numerator) / E.denominator
    assert 0 < Emp < efl, "E must be positive and below the solution's margin"
    d5, d4, d3 = D // 2, D // 2 - 1, D // 2 - 2
    # 1. F_k and the exact target
    F = []
    for k in range(D // 2 + 1):
        Y = Yd[f"F{k}"]
        if not isinstance(Y[0], list):
            Y = [[Y[0]]]
        m = len(Y)
        F.append([[Fr(dy((Y[i][j] + Y[j][i]) / 2, K), 1 << K) for j in range(m)] for i in range(m)])
    Ptar = R.target_poly(F, n, E, D)
    log(f"target P: {len(Ptar)} monomials, degree {max(sum(m) for m in Ptar)}")
    # 2. expanded Gram matrices (monomial basis in round_k3.monos_upto order)
    B1 = sdpa5.iso_bases(d5); B3 = sdpa5.iso_bases(d3); S = sdpa5.stab_bases(d4)
    G1 = expand([(Yd["G1_triv"], B1["triv"]), (Yd["G1_sign"], B1["sign"]),
                 (Yd["G1_std"], B1["std1"]), (Yd["G1_std"], B1["std2"])], None, d5)
    Gd = expand([(Yd["Gdet_triv"], B3["triv"]), (Yd["Gdet_sign"], B3["sign"]),
                 (Yd["Gdet_std"], B3["std1"]), (Yd["Gdet_std"], B3["std2"])], None, d3)
    Gu = expand([(Yd["lin2_even"], S["even"]), (Yd["lin2_odd"], S["odd"])], None, d4)
    Gv = {(perm_slots(a, 0, 1), perm_slots(b, 0, 1)): x for (a, b), x in Gu.items()}
    Gt = {(perm_slots(a, 0, 2), perm_slots(b, 0, 2)): x for (a, b), x in Gu.items()}
    log("expanded the reduced blocks (mpmath)")
    mult = round_k5.multipliers5(D)          # (name, g, deg): 1, 1/2-u, 1/2-v, 1/2-t, detG
    Gs = [G1, Gu, Gv, Gt, Gd]
    Bs, Zs = [], []
    for (nm, g, d), G in zip(mult, Gs):
        Z = R.monos_upto(d); idx = {z: i for i, z in enumerate(Z)}
        assert all(a in idx and b in idx for a, b in G), nm
        m = len(Z)
        Bi = [[0] * m for _ in range(m)]
        for (a, b), x in G.items():
            ia, ib = idx[a], idx[b]
            if ia <= ib:
                y = (x + G.get((b, a), 0)) / 2
                v = dy(y, K)
                Bi[ia][ib] = v; Bi[ib][ia] = v
        Bs.append(Bi); Zs.append(Z)
        log(f"rounded Gram {nm:>6s}: size {m}")
    # 3. residual (exact): P - sum_r g_r z^T B_r z, B_r = Bi / 2^K
    den = 1 << K
    rhs = {}
    for (nm, g, d), Bi, Z in zip(mult, Bs, Zs):
        gp = {}
        for i, zi in enumerate(Z):
            row = Bi[i]
            for j, zj in enumerate(Z):
                v = row[j]
                if v:
                    mm = (zi[0] + zj[0], zi[1] + zj[1], zi[2] + zj[2])
                    gp[mm] = gp.get(mm, 0) + v
        gp = {m_: Fr(v, den) for m_, v in gp.items() if v}
        rhs = R.padd(rhs, R.pmul(g, gp))
    resid = R.padd(Ptar, rhs, -1)
    rmax = max((abs(float(v)) for m_, v in resid.items() if m_ != (0, 0, 0)), default=0.0)
    r0 = float(resid.get((0, 0, 0), 0))
    log(f"residual: {len(resid)} monomials, max |non-constant coef| {rmax:.3e}; constant {r0:.6e} "
        f"(dropped margin (e - E)/C(n,2) = {float((efl - Emp) / C2):.6e})")
    # absorb into B0 (multiplier 1), as round_k5.py: B0 becomes rational (not dyadic) on the touched entries
    Z0 = Zs[0]; idx0 = {z: i for i, z in enumerate(Z0)}
    B0 = [[Fr(v, den) for v in row] for row in Bs[0]]
    for m_, v in resid.items():
        half = tuple(x // 2 for x in m_)
        if all(x % 2 == 0 for x in m_) and half in idx0:
            i = idx0[half]; B0[i][i] += v
            continue
        for zi in Z0:
            zj = (m_[0] - zi[0], m_[1] - zi[1], m_[2] - zi[2])
            if min(zj) >= 0 and zj in idx0 and zj != zi:
                i, j = idx0[zi], idx0[zj]
                B0[i][j] += v / 2; B0[j][i] += v / 2
                break
        else:
            raise AssertionError(f"monomial {m_} not representable")
    Bfr = [B0] + [[[Fr(v, den) for v in row] for row in Bi] for Bi in Bs[1:]]
    # exact identity check
    rhs = {}
    for (nm, g, d), B, Z in zip(mult, Bfr, Zs):
        gp = {}
        for i, zi in enumerate(Z):
            for j, zj in enumerate(Z):
                v = B[i][j]
                if v:
                    mm = (zi[0] + zj[0], zi[1] + zj[1], zi[2] + zj[2])
                    gp[mm] = gp.get(mm, 0) + v
        rhs = R.padd(rhs, R.pmul(g, gp))
    assert R.padd(Ptar, rhs, -1) == {}, "identity fails"
    log("identity P == sum_r g_r z^T B_r z holds exactly")
    # 4. positive definiteness
    allok = True
    for k, Fk in enumerate(F):
        ok, mp_ = R.ldl_pd(Fk)
        log(f"F{k:<2d} size {len(Fk):3d}: {'positive definite, min pivot %.3g' % float(mp_) if ok else 'NOT PD at %s' % mp_}")
        allok &= ok
    for (nm, g, d), B in zip(mult, Bfr):
        L = 1
        for row in B:
            for x in row:
                L = math.lcm(L, x.denominator)
        Bnum = [[x.numerator * (L // x.denominator) for x in row] for row in B]
        assert all(Bnum[i][j] == Bnum[j][i] for i in range(len(B)) for j in range(i))
        ok, info = pd_certificate(Bnum, L, P)
        log(f"B[{nm:>6s}] size {len(B):4d}: {'positive definite: ' if ok else 'FAILED: '}{info}")
        allok &= ok
    log("ALL CHECKS PASSED" if allok else "SOME CHECK FAILED")
    J = {"dim": 5, "n": n, "D": D, "cut": "1/2", "e": str(E),
         "F": [[[str(x) for x in row] for row in Fk] for Fk in F],
         "SOS": [{"g": nm, "deg": d, "basis": [list(z) for z in Z], "B": [[str(x) for x in row] for row in B]}
                 for (nm, g, d), B, Z in zip(mult, Bfr, Zs)],
         "stats": {"KBITS": K, "residual_max_abs": rmax, "all_checks": allok},
         "generated_from": os.path.basename(res)}
    if not allok and not os.environ.get("WRITE_FAILED"):
        log(f"not writing {out} (a check failed; set WRITE_FAILED=1 to write it anyway)")
        return allok
    with open(out, "w") as fh:
        json.dump(J, fh)
    log(f"wrote {out} ({os.path.getsize(out) // 1024} KiB)")
    return allok


if __name__ == "__main__":
    a = sys.argv
    ok = main(a[1], a[2], a[3], int(a[4]), Fr(a[5]), int(a[6]) if len(a) > 6 else 320)
    sys.exit(0 if ok else 1)
