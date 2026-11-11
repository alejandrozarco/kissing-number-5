"""S3 symmetry reduction of the Putinar SOS certificate in k3.Prob.tri_nonneg (as in Machado-de Oliveira Filho 2018).

The polynomial certified on Delta (BV: -s; fixed n: -R - e/C) is invariant under permutations of (u, v, t), and so is
Delta.  Averaging any certificate over S3 gives an invariant one, so the reduction loses nothing:

  * invariant multipliers g in {1, DETG}: the Gram matrix Q of g * z^T Q z (z = monomials of degree <= d) may be
    taken S3-invariant; in a symmetry-adapted basis it splits into blocks for the trivial, the sign and the
    standard representation (the latter shared by its two rows: Q_std (x) I_2);
  * multiplier orbits {g(u), g(v), g(t)} (g = 1+x, 1/2-x, (1+x)(1/2-x)): one Gram matrix Q_u for g(u), invariant under
    the stabiliser (v t), split into a (v t)-even and a (v t)-odd block; the members for v and t are its images
    under the transpositions (u v) and (u t);
  * both sides of the identity are symmetric, so one equation per S3-orbit of monomials (exponents a >= b >= c)
    suffices (keeping all rows would make the equality system rank deficient).

Enable with env SYM=1 (k5.py imports this module and patches k3.Prob.tri_nonneg).
"""
import itertools, os
import numpy as np
import scipy.sparse as sp
import cvxpy as cp
import polyk
from polyk import D, L, N3, EXPS, ONE, U, V, T, pmul, fidx, monos_upto, sos_columns, PERM_M, HIGHROWS

CUT = 0.5
DETG = ONE + 2 * pmul(pmul(U, V), T) - pmul(U, U) - pmul(V, V) - pmul(T, T)
REPROWS = np.array(sorted(fidx(*e) for e in EXPS if e.sum() <= D and e[0] >= e[1] >= e[2]))


def mono_perm(Z, order):
    """n x n permutation matrix of the monomial basis Z under (x0,x1,x2) -> (x[order[0]], ...), as in polyk."""
    idx = {tuple(e): i for i, e in enumerate(Z)}
    P = np.zeros((len(Z), len(Z)))
    for i, e in enumerate(Z):
        ne = [0, 0, 0]
        for slot in range(3):
            ne[order[slot]] += e[slot]
        P[idx[tuple(ne)], i] = 1.0
    return P


def sign(order):
    return 1 if sum(order[i] > order[j] for i in range(3) for j in range(i + 1, 3)) % 2 == 0 else -1


def orth(M, tol=1e-9):
    if M.shape[1] == 0:
        return M
    Uu, s, _ = np.linalg.svd(M, full_matrices=False)
    return Uu[:, s > tol * max(1.0, s[0])]


def iso_bases(d):
    """symmetry-adapted bases (columns, orthonormal) of the monomials of degree <= d:
    triv, sign, std1 ((v t)-fixed vectors of the standard component), std2 (their partners)."""
    Z = np.array(monos_upto(d)); n = len(Z)
    Ps = {o: mono_perm(Z, o) for o in itertools.permutations(range(3))}
    Ptr = sum(Ps.values()) / 6
    Psg = sum(sign(o) * P for o, P in Ps.items()) / 6
    Pst = np.eye(n) - Ptr - Psg
    tau = Ps[(0, 2, 1)]
    Btr, Bsg = orth(Ptr), orth(Psg)
    B1 = orth(Pst @ (np.eye(n) + tau) / 2)
    c, c2 = Ps[(1, 2, 0)], Ps[(2, 0, 1)]
    B2 = (c - c2) @ B1 / np.sqrt(3)
    return Z, dict(triv=Btr, sign=Bsg, std1=B1, std2=B2)


def stab_bases(d):
    """(v t)-even and (v t)-odd orthonormal bases of the monomials of degree <= d."""
    Z = np.array(monos_upto(d)); n = len(Z)
    tau = mono_perm(Z, (0, 2, 1))
    return Z, dict(even=orth((np.eye(n) + tau) / 2), odd=orth((np.eye(n) - tau) / 2))


def reduced_columns(g, d, N, rows, chunk=64):
    """dense len(rows) x r^2 matrix: coefficients (on `rows`) of g * (N^T z)^T Q (N^T z) as a linear map of vec(Q)."""
    Mg, n = sos_columns(g, d)
    Mg = Mg[rows]
    r = N.shape[1]
    out = np.zeros((len(rows), r * r))
    for s in range(0, len(rows), chunk):
        T3 = Mg[s:s + chunk]                                    # c x n^2 sparse
        c = T3.shape[0]
        Tr = sp.csr_matrix(T3.reshape(c * n, n))
        A1 = (Tr @ N).reshape(c, n, r)                          # contract j
        out[s:s + c] = np.einsum('cir,ia->car', A1, N).reshape(c, r * r)
    return out


def sym_tri_nonneg(self, lp, tag):
    """lp >= 0 on Delta via an S3-reduced Putinar SOS (replaces k3.Prob.tri_nonneg)."""
    for k, M in lp.terms.items():
        assert np.abs(np.asarray(M)[HIGHROWS]).max(initial=0) < 1e-12, (tag, k)
    d5, d4, d3 = D // 2, D // 2 - 1, D // 2 - 2
    rows = REPROWS
    rhs = 0
    nblk = 0
    # invariant multipliers
    for g, d, nm in [(ONE, d5, "G1"), (DETG, d3, "Gdet")]:
        if d < 0:
            continue
        _, B = iso_bases(d)
        for part, cols in [("triv", [B["triv"]]), ("sign", [B["sign"]]), ("std", [B["std1"], B["std2"]])]:
            r = cols[0].shape[1]
            if r == 0:
                continue
            A = sum(reduced_columns(g, d, N, rows) for N in cols)
            name = f"{tag}_{nm}_{part}"; self.psd(name, r); nblk += 1
            rhs = rhs + A @ cp.vec(self.blk(name), order='C')
    # multiplier orbits: g(u) with Q_u (v t)-invariant; images under (u v), (u t)
    gens = [("lin1", ONE + U), ("lin2", CUT * ONE - U)]
    if os.environ.get("NOQ") != "1":
        gens.append(("quad", pmul(ONE + U, CUT * ONE - U)))
    if os.environ.get("MULTS"):                  # e.g. MULTS=lin2 or MULTS=lin2,quad: keep only these orbits
        keep = os.environ["MULTS"].split(",")
        gens = [gn for gn in gens if gn[0] in keep]
    Porb = (sp.identity(N3, format='csr') + PERM_M[(1, 0, 2)] + PERM_M[(2, 1, 0)]).tocsr()
    allrows = np.where(EXPS.sum(1) <= D)[0]
    pos = np.full(N3, -1); pos[allrows] = np.arange(len(allrows))
    for nm, g in gens:
        _, B = stab_bases(d4)
        for part in ("even", "odd"):
            N = B[part]; r = N.shape[1]
            if r == 0:
                continue
            A_all = reduced_columns(g, d4, N, allrows)            # all low rows, then symmetrise
            Afull = np.zeros((N3, r * r)); Afull[allrows] = A_all
            A = (Porb @ Afull)[rows]
            name = f"{tag}_{nm}_{part}"; self.psd(name, r); nblk += 1
            rhs = rhs + A @ cp.vec(self.blk(name), order='C')
    self.cons.append(self.expr(lp, rows) == rhs)
    self.symblocks = getattr(self, "symblocks", 0) + nblk


def block_sizes():
    """sizes of the reduced SOS blocks at the current D (for logging)."""
    d5, d4, d3 = D // 2, D // 2 - 1, D // 2 - 2
    out = {}
    for d, nm in [(d5, "G1"), (d3, "Gdet")]:
        if d >= 0:
            _, B = iso_bases(d)
            out[nm] = [B["triv"].shape[1], B["sign"].shape[1], B["std1"].shape[1]]
    _, B = stab_bases(d4)
    out["orbit"] = [B["even"].shape[1], B["odd"].shape[1]]
    return out
