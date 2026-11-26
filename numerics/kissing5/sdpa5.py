#!/usr/bin/env python3
"""Fixed-n three-point SDP for the kissing number in dimension 5, S3-reduced, written in SDPA sparse format
(for SDPA-GMP), and the reader of SDPA-GMP's solution.

Same program as `SYM=1 MULTS=lin2 k5.py fixn D N` (k3.build_fixn + sym.sym_tri_nonneg with the S^4 kernels of
k5.Qk5, no explicit Delsarte term), rebuilt sparse and standalone: polyk allocates dense (D+1)^3 x (D+1)^3 tables at
import (10 GB at D = 32), which this module avoids.

  max e  s.t.  -R(u,v,t) - e/C(n,2) = sum of S3-reduced Putinar SOS terms   (one equation per S3-orbit of monomials)
               sum_k tr F_k = 1,   F_k PSD (k = 0..D/2, size D/2+1-k),
  R = (n-2) s + s(u,u,1) + s(v,v,1) + s(t,t,1) + s(1,1,1)/(n-1),  s = Sym( sum_k <F_k, (u^a v^b Q_k)_{ab}> ),
  Q_k of S^4: (k+2) Q_{k+1} = 2(k+1) w Q_k - k g Q_{k-1},  w = t - uv,  g = (1-u^2)(1-v^2).
SOS terms: g = 1 (degree D/2 basis) and g = detG (D/2-2): trivial, sign and standard isotypic blocks (standard:
one Gram for both partner rows); the orbit {1/2-u, 1/2-v, 1/2-t} (D/2-1): one Gram for 1/2-u, (v t)-even and
(v t)-odd blocks, plus its images under (u v), (u t).  e is written e = ep - 1 with ep >= 0 (an LP block).
The symmetry-adapted bases are built orbit by orbit, so every basis vector lives on one monomial orbit (sparse).

usage: python3 sdpa5.py write D N OUT.dat-s        writes the problem (+ OUT.meta.json: block names and sizes)
       python3 sdpa5.py read  OUT.dat-s RESULT     prints phase, e = ep - 1, min eigenvalues per block
"""
import sys, json, itertools, math, os
from fractions import Fraction
import numpy as np
import scipy.sparse as sp

CUT = 0.5

# HP=1: high-precision data (mpmath, HP_PREC bits, default 256): the orthonormal bases are refined from the float ones
# (exact projection, then Gram-Schmidt), every coefficient is accumulated in mpmath, and the file is written with
# HP_DIGITS (default 60) significant digits, so that a solution can be rounded to an exact certificate.  The float
# basis choice is kept, so a solution of the float problem is a near-solution of the HP one (warm start).
HP = os.environ.get("HP") == "1"
if HP:
    import mpmath
    mpmath.mp.prec = int(os.environ.get("HP_PREC", "256"))
    HP_DIGITS = int(os.environ.get("HP_DIGITS", "60"))
    ZTOL = mpmath.mpf(2) ** (-(mpmath.mp.prec // 2))


def num(v):
    """a coefficient in the working number type: float, or mpmath mpf in HP mode (Fractions converted exactly)."""
    if not HP:
        return float(v)
    if isinstance(v, Fraction):
        return mpmath.mpf(v.numerator) / v.denominator
    return mpmath.mpf(v)


def fmt(v):
    return mpmath.nstr(v, HP_DIGITS, strip_zeros=False) if HP else repr(float(v))


# ------------------------------------------------------------------ monomials and polynomials (dict exponent -> coef)
def monos_upto(d):
    return [(a, b, c) for s in range(d + 1) for a in range(s, -1, -1) for b in range(s - a, -1, -1) for c in [s - a - b]]


def pmul(p, q):
    r = {}
    for e1, c1 in p.items():
        for e2, c2 in q.items():
            e = (e1[0] + e2[0], e1[1] + e2[1], e1[2] + e2[2])
            r[e] = r.get(e, 0) + c1 * c2
    return {e: c for e, c in r.items() if c != 0}


def padd(p, q, a=1, b=1):
    r = {e: a * c for e, c in p.items()}
    for e, c in q.items():
        r[e] = r.get(e, 0) + b * c
    return {e: c for e, c in r.items() if c != 0}


ONE = {(0, 0, 0): Fraction(1)}
U = {(1, 0, 0): Fraction(1)}; V = {(0, 1, 0): Fraction(1)}; T = {(0, 0, 1): Fraction(1)}
DETG = {(0, 0, 0): 1, (1, 1, 1): 2, (2, 0, 0): -1, (0, 2, 0): -1, (0, 0, 2): -1}


def qk5(kmax):
    """exact Q_0..Q_kmax of S^4 (Fractions)."""
    w = padd(T, pmul(U, V), 1, -1)
    g = pmul(padd(ONE, pmul(U, U), 1, -1), padd(ONE, pmul(V, V), 1, -1))
    Q = [dict(ONE), dict(w)]
    k = 1
    while len(Q) <= kmax:
        Q.append(padd(pmul(w, Q[-1]), pmul(g, Q[-2]), Fraction(2 * (k + 1), k + 2), Fraction(-k, k + 2)))
        k += 1
    return Q[:kmax + 1]


PERMS = list(itertools.permutations(range(3)))


def permute(e, o):
    """exponent of the monomial obtained from x^e by x_slot -> x_{o[slot]}."""
    ne = [0, 0, 0]
    for slot in range(3):
        ne[o[slot]] += e[slot]
    return tuple(ne)


def rep(e):
    return tuple(sorted(e, reverse=True))


# ------------------------------------------------------------------ symmetry-adapted bases, orbit by orbit
def _orth(M, tol=1e-9):
    if M.shape[1] == 0:
        return M
    Uu, s, _ = np.linalg.svd(M, full_matrices=False)
    return Uu[:, s > tol * max(1.0, s[0])]


def _sign(o):
    return 1 if sum(o[i] > o[j] for i in range(3) for j in range(i + 1, 3)) % 2 == 0 else -1


def iso_bases(d):
    """{triv, sign, std1, std2}: lists of sparse vectors {monomial: coef} (orthonormal), as sym.iso_bases."""
    out = {k: [] for k in ("triv", "sign", "std1", "std2")}
    orbits = {}
    for e in monos_upto(d):
        orbits.setdefault(rep(e), []).append(e)
    for r0 in sorted(orbits):
        O = orbits[r0]; idx = {e: i for i, e in enumerate(O)}; n = len(O)
        P = {}
        for o in PERMS:
            M = np.zeros((n, n))
            for i, e in enumerate(O):
                M[idx[permute(e, o)], i] = 1.0
            P[o] = M
        Ptr = sum(P.values()) / 6
        Psg = sum(_sign(o) * M for o, M in P.items()) / 6
        Pst = np.eye(n) - Ptr - Psg
        tau = P[(0, 2, 1)]
        B1 = _orth(Pst @ (np.eye(n) + tau) / 2)
        B2 = (P[(1, 2, 0)] - P[(2, 0, 1)]) @ B1 / np.sqrt(3)
        if HP:
            # exact projectors (P[o] are 0/1 matrices), then the float bases refined onto their exact ranges
            I = np.eye(n, dtype=int)
            Pi = {o: M.astype(int) for o, M in P.items()}
            Mtr = sum(Pi.values()) * Fraction(1, 6)
            Msg = sum(_sign(o) * M for o, M in Pi.items()) * Fraction(1, 6)
            Mst = I - Mtr - Msg
            M1 = Mst.dot(I + Pi[(0, 2, 1)]) * Fraction(1, 2)
            H1 = _refine(M1, B1)
            R = Pi[(1, 2, 0)] - Pi[(2, 0, 1)]; s3 = mpmath.sqrt(3)
            H2 = [[sum(int(R[i, k]) * col[k] for k in range(n)) / s3 for i in range(n)] for col in H1]
            parts = (("triv", _refine(Mtr, _orth(Ptr))), ("sign", _refine(Msg, _orth(Psg))), ("std1", H1), ("std2", H2))
            for nm, cols in parts:
                for col in cols:
                    out[nm].append({O[i]: col[i] for i in range(n) if abs(col[i]) > ZTOL})
            continue
        for nm, B in (("triv", _orth(Ptr)), ("sign", _orth(Psg)), ("std1", B1), ("std2", B2)):
            for j in range(B.shape[1]):
                out[nm].append({O[i]: B[i, j] for i in range(n) if abs(B[i, j]) > 1e-14})
    return out


def _refine(M, B):
    """HP: the columns of the float orthonormal basis B projected by the exact projector M (a numpy object array of
    Fractions / ints) and re-orthonormalised by modified Gram-Schmidt in mpmath; close to B (to float accuracy)."""
    n, r = B.shape
    Mm = [[num(Fraction(M[i, k])) for k in range(n)] for i in range(n)]
    cols = []
    for j in range(r):
        b = [mpmath.mpf(float(B[k, j])) for k in range(n)]
        v = [mpmath.fsum(Mm[i][k] * b[k] for k in range(n)) for i in range(n)]
        for c in cols:
            p = mpmath.fsum(c[i] * v[i] for i in range(n))
            v = [v[i] - p * c[i] for i in range(n)]
        nv = mpmath.sqrt(mpmath.fsum(x * x for x in v))
        cols.append([x / nv for x in v])
    return cols


def stab_bases(d):
    """(v t)-even and (v t)-odd orthonormal bases (sparse vectors), as sym.stab_bases."""
    ev, od = [], []
    for (a, b, c) in monos_upto(d):
        if b == c:
            ev.append({(a, b, c): num(1)})
        elif b > c:
            s = 1 / mpmath.sqrt(2) if HP else 1 / math.sqrt(2)
            ev.append({(a, b, c): s, (a, c, b): s}); od.append({(a, b, c): s, (a, c, b): -s})
    return {"even": ev, "odd": od}


# ------------------------------------------------------------------ the program
class Prog:
    """equations sum_blocks <A_blk[row], Y_blk> = c[row]; coefficients kept on ordered pairs (i, j)."""

    def __init__(self, rows):
        self.rows = rows; self.ridx = {m: i for i, m in enumerate(rows)}
        self.blocks = []          # (name, size)
        self.ent = []             # per block: dict (row, i, j) -> coef
        self.c = np.zeros(len(rows) + 1)
        self.cx = {}              # exact right-hand side (Fractions), used for writing in HP mode

    def block(self, name, size):
        self.blocks.append((name, size)); self.ent.append({})
        return len(self.blocks) - 1

    def add(self, b, row, i, j, v):
        if v != 0:
            key = (row, i, j); d = self.ent[b]; d[key] = d.get(key, 0) + num(v)


def sos_block(pr, name, g, basis, orbit_images=False, weight=-1.0):
    """adds - g * sum_parts (N^T z)^T Q (N^T z) on the representative rows (weight -1: right-hand side moved left).
    basis: list of lists of sparse vectors (several lists share one Gram, e.g. std1 and std2)."""
    r = len(basis[0])
    if r == 0:
        return
    b = pr.block(name, r)
    gi = list(g.items())
    for part in basis:
        for i in range(r):
            for j in range(i, r):
                acc = {}
                for e1, c1 in part[i].items():
                    for e2, c2 in part[j].items():
                        for eg, cg in gi:
                            e = (e1[0] + e2[0] + eg[0], e1[1] + e2[1] + eg[1], e1[2] + e2[2] + eg[2])
                            acc[e] = acc.get(e, 0.0) + c1 * c2 * num(cg)
                for e, v in acc.items():
                    targets = [e]
                    if orbit_images:     # images of g(u) p under (u v), (u t): the rep row m collects p at m, (u v)m, (u t)m
                        targets = [e, (e[1], e[0], e[2]), (e[2], e[1], e[0])]
                    for t_ in targets:
                        if t_ in pr.ridx and t_ == rep(t_):
                            row = pr.ridx[t_]
                            pr.add(b, row, i, j, weight * v)
                            if i != j:
                                pr.add(b, row, j, i, weight * v)


def build(D, n):
    rows = sorted({rep(e) for e in monos_upto(D)})
    pr = Prog(rows)
    C2 = Fraction(n * (n - 1), 2)
    Q = qk5(D // 2)
    for k in range(D // 2 + 1):
        m = D // 2 + 1 - k
        b = pr.block(f"F{k}", m)
        for a in range(m):
            for bb in range(m):
                p = {(e[0] + a, e[1] + bb, e[2]): c for e, c in Q[k].items()}
                s = {}                                   # Sym(p) = average over the 6 permutations
                for e, c in p.items():
                    for o in PERMS:
                        pe = permute(e, o); s[pe] = s.get(pe, 0) + c / 6
                Rm = {}                                  # R on the representative rows
                for e, c in s.items():
                    if e == rep(e):
                        Rm[e] = Rm.get(e, 0) + (n - 2) * c
                tot = sum(s.values())
                diag = {}                                # coefficient of x^j in s(x,x,1): sum over a+b=j of s[a,b,c]
                for e, c in s.items():
                    j = e[0] + e[1]; diag[j] = diag.get(j, 0) + c
                for j, c in diag.items():
                    e = (j, 0, 0)
                    Rm[e] = Rm.get(e, 0) + (3 * c if j == 0 else c)
                Rm[(0, 0, 0)] = Rm.get((0, 0, 0), 0) + tot / (n - 1)
                for e, c in Rm.items():
                    if e in pr.ridx:
                        pr.add(b, pr.ridx[e], a, bb, -c)            # slack = -R - e/C
        for a in range(m):
            pr.add(b, len(rows), a, a, 1.0)                         # normalisation sum_k tr F_k = 1
    eb = pr.block("ep", -1)                                         # LP block: e = ep - 1
    pr.add(eb, pr.ridx[(0, 0, 0)], 0, 0, -1 / C2)
    pr.c[pr.ridx[(0, 0, 0)]] = -1.0 / float(C2)                     # -(ep - 1)/C moved: -ep/C ... = -1/C
    pr.c[len(rows)] = 1.0
    pr.cx[pr.ridx[(0, 0, 0)]] = -1 / C2; pr.cx[len(rows)] = Fraction(1)
    d5, d4, d3 = D // 2, D // 2 - 1, D // 2 - 2
    for g, d, nm in ((ONE, d5, "G1"), (DETG, d3, "Gdet")):
        B = iso_bases(d)
        for part, cols in (("triv", [B["triv"]]), ("sign", [B["sign"]]), ("std", [B["std1"], B["std2"]])):
            sos_block(pr, f"{nm}_{part}", g, cols)
    S = stab_bases(d4)
    glin = {(0, 0, 0): Fraction(1, 2), (1, 0, 0): Fraction(-1)}
    for part in ("even", "odd"):
        sos_block(pr, f"lin2_{part}", glin, [S[part]], orbit_images=True)
    return pr


def write(pr, path, D, n):
    nrow = len(pr.rows) + 1
    # drop identically empty equations (both sides zero), keep the numbering of the rest
    used = set()
    for d in pr.ent:
        used.update(k[0] for k in d)
    keep = [r for r in range(nrow) if r in used or pr.c[r] != 0]
    assert all(pr.c[r] == 0 for r in range(nrow) if r not in used), "an empty equation with a non-zero constant"
    new = {r: i + 1 for i, r in enumerate(keep)}
    with open(path, "w") as fh:
        fh.write(f'"kissing 5 fixed n = {n}, D = {D}, S3-reduced (sdpa5.py)"\n')
        fh.write(f"{len(keep)}\n{len(pr.blocks)}\n")
        fh.write(" ".join(str(s) for _, s in pr.blocks) + "\n")
        fh.write(" ".join((fmt(num(pr.cx.get(r, 0))) if HP else repr(float(pr.c[r]))) for r in keep) + "\n")
        eb = [i for i, (nm, _) in enumerate(pr.blocks) if nm == "ep"][0]
        fh.write(f"0 {eb + 1} 1 1 1.0\n")                          # objective: max ep
        for b, d in enumerate(pr.ent):
            sym = {}
            for (row, i, j), v in d.items():
                key = (row, min(i, j), max(i, j))
                sym[key] = sym.get(key, 0.0) + (v if i == j else v / 2)
            for (row, i, j), v in sorted(sym.items()):
                if v != 0:
                    fh.write(f"{new[row]} {b + 1} {i + 1} {j + 1} {fmt(v)}\n")
    meta = dict(D=D, n=n, blocks=pr.blocks, m=len(keep), rows=[list(pr.rows[r]) if r < len(pr.rows) else "norm"
                                                             for r in keep])
    json.dump(meta, open(path + ".meta.json", "w"))
    return meta


def read_result(path):
    txt = open(path).read()
    out = {}
    for key in ("phase.value", "objValPrimal", "objValDual", "relative gap", "total time"):
        for line in txt.splitlines():
            if line.strip().startswith(key):
                out[key] = line.split("=", 1)[1].strip()
                break
    i = txt.find("yMat =")
    body = txt[i + len("yMat ="):]
    # nested braces: { {block}, {block}, ... }
    blocks, depth, cur, start = [], 0, [], None
    tok = ""
    mats = []
    j = body.find("{")
    s = body[j:]
    level = 0; buf = ""
    stack = []
    for ch in s:
        if ch == "{":
            level += 1; stack.append([]); buf = ""
        elif ch == "}":
            if buf.strip():
                stack[-1].append(float(buf)); buf = ""
            top = stack.pop(); level -= 1
            if level == 0:
                mats = top; break
            stack[-1].append(top)
        elif ch == ",":
            if buf.strip():
                stack[-1].append(float(buf))
            buf = ""
        else:
            buf += ch
    out["yMat"] = mats
    return out


if __name__ == "__main__":
    if sys.argv[1] == "write":
        D, n, path = int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
        import time
        t0 = time.time()
        pr = build(D, n)
        meta = write(pr, path, D, n)
        print(json.dumps(dict(D=D, n=n, m=meta["m"], blocks=[s for _, s in pr.blocks],
                              nnz=sum(len(d) for d in pr.ent), time=round(time.time() - t0, 1))))
    elif sys.argv[1] == "read":
        meta = json.load(open(sys.argv[2] + ".meta.json"))
        res = read_result(sys.argv[3])
        ym = res.pop("yMat")
        info = dict(res)
        names = [nm for nm, _ in meta["blocks"]]
        ep = None; mins = {}
        for nm, blk in zip(names, ym):
            if nm == "ep":
                ep = blk[0] if not isinstance(blk[0], list) else blk[0][0]
            else:
                M = np.array(blk, dtype=float)
                mins[nm] = float(np.linalg.eigvalsh(M)[0]) if M.ndim == 2 else float(min(M))
        info["e"] = None if ep is None else ep - 1
        info["min_eig"] = min(mins.values()) if mins else None
        print(json.dumps(info))
