"""Exact rounding of the 5D fixed-n interior solution (k5.py mode mu, SYM=1, MULTS=lin2) to a rational certificate.

usage: python3 round_k5.py sol/fixn_D16_n46_mu0.5_sym_mlin2.npz cert_D16.json [KBITS] [E]

The float solution is S3-reduced (sym.py).  It is first expanded back to ordinary Gram matrices in the monomial basis
(the reduction is an orthogonal change of basis, so the expanded blocks are positive definite with the same minimum
eigenvalue mu); the certificate is then rounded and verified exactly as in ../kissing3/round_k3.py:
    P(u,v,t) := -R(u,v,t) - e / C(n,2) = sum_r g_r(u,v,t) * z_r^T B_r z_r        (polynomial identity)
with the multipliers g_r in {1, 1/2-u, 1/2-v, 1/2-t, detG} (the lin2 orbit of sym.py), every F_k and B_r positive
definite, and the kernels of S^4: Q_k with (k+2) Q_{k+1} = 2 (k+1) w Q_k - k g Q_{k-1} (Gegenbauer of the tangent S^3).
"""
import json, os, sys
from fractions import Fraction as Fr
from math import comb, lcm
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "kissing3"))
import round_k3 as R
from round_k3 import padd, pmul, pscale, ONE, U, V, T, monos_upto, gram_poly, ldl_pd, dymat, log

CUT = Fr(1, 2)


def Qs5(kmax):
    w = padd(T, pmul(U, V), -1)
    g = pmul(padd(ONE, pmul(U, U), -1), padd(ONE, pmul(V, V), -1))
    Q = [ONE, w]
    k = 1
    while len(Q) <= kmax:
        Q.append(pscale(padd(pscale(pmul(w, Q[-1]), Fr(2 * (k + 1))), pmul(g, Q[-2]), -k), Fr(1, k + 2)))
        k += 1
    return Q


R.Qs = Qs5


def multipliers5(D):
    d5, d4, d3 = D // 2, D // 2 - 1, D // 2 - 2
    out = [("1", ONE, d5)]
    for nm, X in (("u", U), ("v", V), ("t", T)):
        out.append((f"1/2-{nm}", padd(pscale(ONE, CUT), X, -1), d4))
    detG = padd(padd(ONE, pscale(pmul(pmul(U, V), T), 2)), padd(padd(pmul(U, U), pmul(V, V)), pmul(T, T)), -1)
    out.append(("detG", detG, d3))
    return out


def expand_blocks(sol, D, mu):
    """float Gram matrices (monomial basis, order of monos_upto) for the multipliers of multipliers5, from the
    reduced blocks (each reduced block + mu I, as in the mu-mode solve)."""
    os.environ["POLYD"] = str(D)
    import polyk
    assert polyk.D == D
    import sym
    d5, d4, d3 = D // 2, D // 2 - 1, D // 2 - 2

    def blk(name):
        X = np.asarray(sol[name], float)
        return X + mu * np.eye(X.shape[0])

    def inv_full(nm, d):
        _, B = sym.iso_bases(d)
        G = B["triv"] @ blk(f"T_{nm}_triv") @ B["triv"].T
        if B["sign"].shape[1]:
            G += B["sign"] @ blk(f"T_{nm}_sign") @ B["sign"].T
        Qs = blk(f"T_{nm}_std")
        G += B["std1"] @ Qs @ B["std1"].T + B["std2"] @ Qs @ B["std2"].T
        return G

    out = [inv_full("G1", d5)]
    Z, S = sym.stab_bases(d4)
    Gu = S["even"] @ blk("T_lin2_even") @ S["even"].T + S["odd"] @ blk("T_lin2_odd") @ S["odd"].T
    # sigma_v(u,v,t) = sigma_u(v,u,t), sigma_t(u,v,t) = sigma_u(t,v,u):  z(perm) = Pi^T z  ->  B = Pi B_u Pi^T
    for order in [(0, 1, 2), (1, 0, 2), (2, 1, 0)]:
        Pi = sym.mono_perm(Z, order)
        out.append(Pi @ Gu @ Pi.T)
    out.append(inv_full("Gdet", d3))
    assert all(sorted(map(tuple, sym.monos_upto(d))) == sorted(monos_upto(d)) for d in (d5, d4, d3))
    return out


def main(solfile, out, K=28, E=Fr(1, 32)):
    sol = np.load(solfile)
    meta = json.loads(str(sol["meta"]))
    D, n = meta["D"], int(round(meta["n"]))
    assert meta["mode"] == "mu" and meta["delsarte"] is None and float(meta["n"]) == n
    assert meta.get("mults") == "lin2" and "sym_blocks" in meta, "expects a SYM=1 MULTS=lin2 solution"
    mu = float(meta["mu"])
    assert 0 < E <= Fr(meta["e"]), (E, meta["e"])
    log(f"{solfile}: D={D} n={n} mu={mu:.3g} float e={meta['e']:.6g} -> exact e={E}, KBITS={K}")
    sizes = [D // 2 + 1 - k for k in range(D // 2 + 1)]
    F = [dymat(sol[f"F{k}"] + mu * np.eye(m), K) for k, m in enumerate(sizes)]
    P = R.target_poly(F, n, E, D)
    log(f"exact target P: {len(P)} monomials, degree {max(sum(m) for m in P)}")
    mult = multipliers5(D)
    Gs = expand_blocks(sol, D, mu)
    Bs, Zs, rhs = [], [], {}
    for (nm, g, d), G in zip(mult, Gs):
        Z = monos_upto(d)
        assert G.shape == (len(Z), len(Z))
        lam = np.linalg.eigvalsh((G + G.T) / 2)[0]
        log(f"expanded block {nm:>6s}: size {len(Z)}, float min eigenvalue {lam:.3g}")
        B = dymat(G, K)
        Bs.append(B); Zs.append(Z)
        rhs = padd(rhs, pmul(g, gram_poly(B, Z)))
    res = padd(P, rhs, -1)
    rmax = max((abs(float(v)) for m, v in res.items() if m != (0, 0, 0)), default=0.0)
    r0 = float(res.get((0, 0, 0), 0))
    e_drop = (float(meta["e"]) - float(E)) / comb(n, 2)
    log(f"rounding residual: {len(res)} monomials, max |non-constant coef| {rmax:.3g}; constant {r0:.6g} "
        f"(expected about the dropped e/C(n,2) = {e_drop:.6g})")
    if not (rmax < 1e-2 * mu and abs(r0 - e_drop) < 1e-2 * mu):
        log("WARNING: residual not small against mu; positive definiteness may fail")
    Z0 = Zs[0]
    idx = {z: i for i, z in enumerate(Z0)}
    B0 = Bs[0]
    for m, v in res.items():
        half = tuple(x // 2 for x in m)
        if all(x % 2 == 0 for x in m) and half in idx:
            i = idx[half]; B0[i][i] += v
            continue
        for zi in Z0:
            zj = (m[0] - zi[0], m[1] - zi[1], m[2] - zi[2])
            if min(zj) >= 0 and zj in idx and zj != zi:
                i, j = idx[zi], idx[zj]
                B0[i][j] += v / 2; B0[j][i] += v / 2
                break
        else:
            raise AssertionError(f"monomial {m} not representable")
    rhs = {}
    for (nm, g, d), B, Z in zip(mult, Bs, Zs):
        rhs = padd(rhs, pmul(g, gram_poly(B, Z)))
    assert padd(P, rhs, -1) == {}, "identity fails"
    log("identity P == sum_r g_r z^T B_r z holds exactly")
    for nmb, M in [(f"F{k}", Fk) for k, Fk in enumerate(F)] + [(f"B{r}:{mult[r][0]}", B) for r, B in enumerate(Bs)]:
        assert all(M[i][j] == M[j][i] for i in range(len(M)) for j in range(len(M))), nmb
        ok, mp = ldl_pd(M)
        assert ok, f"{nmb} not positive definite (pivot {mp})"
        log(f"{nmb:>22s}: size {len(M):3d}, positive definite, min pivot {float(mp):.3g}")
    dens = [x.denominator for M in F + Bs for row in M for x in row] + [Fr(E).denominator]
    Lam = lcm(*dens)
    nums = [abs(x.numerator) * (Lam // x.denominator) for M in F + Bs for row in M for x in row]
    J = {
        "dim": 5,
        "claim": ("dimension 5 (kernels of S^4): for all (u,v,t) with GramOK and u,v,t <= 1/2:  "
                  "sum_k <F_k, Rk n k u v t> <= -e / C(n,2)"),
        "n": n, "D": D, "cut": str(CUT), "e": str(E),
        "F": [[[str(x) for x in row] for row in Fk] for Fk in F],
        "SOS": [{"g": nm, "deg": d, "basis": [list(z) for z in Z], "B": [[str(x) for x in row] for row in B]}
                for (nm, g, d), B, Z in zip(mult, Bs, Zs)],
        "Lam": str(Lam),
        "stats": {"KBITS": K, "residual_max_abs": rmax, "Lam_bits": Lam.bit_length(),
                  "max_scaled_entry_bits": max(nums).bit_length()},
        "generated_from": os.path.basename(solfile),
    }
    with open(out, "w") as fh:
        json.dump(J, fh)
    log(f"wrote {out} ({os.path.getsize(out) // 1024} KiB); Lam: {Lam.bit_length()} bits, "
        f"max |entry|*Lam: {max(nums).bit_length()} bits")


if __name__ == "__main__":
    a = sys.argv
    main(a[1], a[2], int(a[3]) if len(a) > 3 else 28, Fr(a[4]) if len(a) > 4 else Fr(1, 32))
