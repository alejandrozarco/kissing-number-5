#!/usr/bin/env python3
"""gen_t5.py -- a 5D kissing certificate JSON (numerics/kissing5, e.g. d32/k64/cert.json) -> `Kissing5.Tree.CertK5T`
Lean data with tree-encoded SOS blocks, row-chunk checks in core Lean, and the composition.

usage (always nice 19, under the heavy-slot lock on the Mac):
  python3 lean/gen/gen_t5.py pack CERT.json WORK      integer data: Λ, F blocks (L D Lᵀ + Δ), SOS blocks (same packing)
  python3 lean/gen/gen_t5.py plan WORK                Kronecker parameters, all statistics, chunking; exact simulation
  python3 lean/gen/gen_t5.py emit WORK LEANDIR        the Lean modules (see `emit`)

Semantics (as lean/gen/emit_k5.py; JSON independently checked by numerics/kissing5/check_big_k5.py):
  -sum_k <F_k, Rk n k u v t> - e/C(n,2) = sum_r g_r(u,v,t) z_r^T B_r z_r.
Integer data with common denominator Λ = Λ0 2^s: eps = Λ e, F~_k = F_k/(k+1)! = ent_k / Λ (Blk, L D Lᵀ + Δ, checked by
`Blk.ok` in Lean), and each SOS block as Λ B_r / c_r = Σ_q d_q l_q l_qᵀ + Δ with Δ diagonally dominant, written as the
explicit sum of squares (`Kissing5.Tree.TBlk`)
  Σ_q d_q (Σ_c l_q[c] z_c)²  +  Σ_i [ di z_i² + Σ_{j>i} |Δ_ij| (z_i + sgn(Δ_ij) z_j)² ],   di = Δ_ii - Σ_{j≠i} |Δ_ij|,
which equals zᵀ (L D Lᵀ + Δ) z exactly; nonnegativity is then structural (no PSD test in Lean).
"""
import json, os, pickle, sys, time
from fractions import Fraction as Fr
from math import comb, factorial, lcm

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.abspath(os.path.join(HERE, "..", "..", "numerics", "kissing5", "d32")))
import cert3_util as U                     # noqa: E402
from emit_k5 import CODES, fk5E, gKE       # noqa: E402  (also installs the memory-light U.kev)

T0 = time.time()


def log(*a):
    print(f"[{time.time() - T0:7.1f}s]", *a, flush=True)


# ------------------------------------------------------------------ pack
def pack_np(M, eps):
    """cert3_util.pack_psd with a given shift eps (an integer, in the units of M), vectorised with numpy object
    arrays (lean/bench/gen/d32prep.py: same exact arithmetic, bit-identical to pack_psd on the D16 data)."""
    import numpy as np
    r = len(M)
    A = np.array([list(row) for row in M], dtype=object)
    for i in range(r):
        A[i, i] -= eps
    d, L = [], np.zeros((r, r), dtype=object)
    for q in range(r):
        P = int(A[q, q])
        if P <= 0:
            return None, f"pivot {q} <= 0 after shift"
        col = A[q + 1:, q]
        S = int(sum(abs(x) for x in col))
        lp = P.bit_length() - 1
        pstar = (2 * lp - (S.bit_length() - 1) + (r.bit_length() - 1) - 1) / 3.0 if S > 0 else lp / 2.0
        p = max(0, min(int(round(pstar)), lp // 2))
        lq = np.zeros(r, dtype=object)
        lq[q] = 1 << p
        if q + 1 < r:
            lq[q + 1:] = np.array([(2 * (int(x) << p) + P) // (2 * P) for x in col], dtype=object)
        dq = P >> (2 * p)
        v = lq[q:]
        A[q:, q:] -= np.outer(dq * v, v)
        d.append(dq)
        L[q] = lq
    for i in range(r):
        A[i, i] += eps
    dL = L * np.array(d, dtype=object)[:, None]
    assert (L.T.dot(dL) + A == np.array([list(row) for row in M], dtype=object)).all(), "packing identity broken"
    return (d, [[int(x) for x in row] for row in L], [[int(x) for x in row] for row in A]), None


def lam_min_est(Bn, den, P=320):
    """λ_min of the rational matrix Bn/den (Bn integer), by numerics/kissing5/d32/hp_blocks (fixed-point LDLᵀ and
    inverse iteration): only an estimate, used for the shift; everything built from it is checked exactly."""
    import numpy as np
    from hp_blocks import ldl_fixed, lam_min
    A = np.array([[(x << P) // den for x in row] for row in Bn], dtype=object)
    Lf, d, bad = ldl_fixed(A, P)
    assert bad is None, f"fixed-point LDL: not positive definite at pivot {bad}"
    return lam_min(Lf, d, P, iters=40)


def dd_slack(D):
    r = len(D)
    return min(D[i][i] - sum(abs(D[i][j]) for j in range(r) if j != i) for i in range(r))


def cmd_pack(cert, work, s=None):
    os.makedirs(work, exist_ok=True)
    raw = open(cert, "rb").read()
    import hashlib
    sha = hashlib.sha256(raw).hexdigest()
    J = json.loads(raw); del raw
    log(f"read {cert} (sha256 {sha[:16]}…): n = {J['n']}, D = {J.get('D')}, {len(J['F'])} F blocks, "
        f"SOS {[(b['g'], len(b['basis'])) for b in J['SOS']]}")
    n, e = J["n"], Fr(J["e"])
    L0 = e.denominator
    for k, M in enumerate(J["F"]):
        for row in M:
            for x in row:
                L0 = lcm(L0, (Fr(x) / factorial(k + 1)).denominator)
    for b in J["SOS"]:
        cr = CODES[b["g"]][1]
        for row in b["B"]:
            for x in row:
                L0 = lcm(L0, (Fr(x) / cr).denominator)
    log(f"Λ0 = {L0.bit_length()} bits")
    s = int(s if s is not None else os.environ.get("S", "64"))
    Lam = L0 << s
    eps = e * Lam
    assert eps.denominator == 1
    meta = dict(cert=os.path.relpath(cert, os.path.join(HERE, "..", "..")), sha256=sha, n=n, e=J["e"], L0=L0, s=s,
                Lam=Lam, eps=eps.numerator, K=len(J["F"]), S=[])
    # F blocks: exact LDLᵀ + DD remainder (pack_psd, as emit_k5.py). The float λ_min that sets the shift is cached
    # in WORK/lam.json (key F{k}, exact, in the units of the integer block) so that a regeneration does not depend on
    # the LAPACK build: pack_psd then computes the same shift int(λ θ) as from its own float estimate.
    import numpy as np
    lp = os.path.join(work, "lam.json")
    Fb = []
    for k, M in enumerate(J["F"]):
        Mi = [[Fr(x) / factorial(k + 1) * Lam for x in row] for row in M]
        assert all(x.denominator == 1 for row in Mi for x in row)
        Mn = [[x.numerator for x in row] for row in Mi]
        lams = json.load(open(lp)) if os.path.exists(lp) else {}
        if f"F{k}" not in lams:
            e2 = max(abs(x) for row in Mn for x in row).bit_length()
            lf = float(np.linalg.eigvalsh(np.array([[float(Fr(x, 1 << e2)) for x in row] for row in Mn]))[0])
            assert lf > 0, f"F{k}: float λ_min {lf:.3e} <= 0"
            lams[f"F{k}"] = str(Fr(lf) * (1 << e2))
            json.dump(lams, open(lp, "w"), indent=1)
        b, info = U.pack_psd(Mn, Fr(1, 2), lmin=Fr(lams[f"F{k}"]))
        assert b is not None and info["ok"], f"F{k}: {info}"
        r = len(M)
        assert [[Fr(b.ent(r, a, c), Lam) * factorial(k + 1) for c in range(r)] for a in range(r)] == \
            [[Fr(x) for x in row] for row in M], f"F{k} round trip"
        Fb.append((b.d, b.l, b.D))
    log(f"F0..F{len(Fb) - 1}: packed, Blk.ok, exact round trip")
    pickle.dump(Fb, open(os.path.join(work, "F.pkl"), "wb"))
    blocks = J["SOS"]
    del J
    for i, blk in enumerate(blocks):
        g = blk["g"]; codes, cr = CODES[g]; z = [tuple(t) for t in blk["basis"]]; r = len(z)
        B = [[Fr(x) for x in row] for row in blk["B"]]
        den = 1
        for row in B:
            for x in row:
                den = lcm(den, x.denominator)
        Bn = [[x.numerator * (den // x.denominator) for x in row] for row in B]
        lp = os.path.join(work, "lam.json")
        lams = json.load(open(lp)) if os.path.exists(lp) else {}
        if f"S{i}" not in lams:
            lams[f"S{i}"] = lam_min_est(Bn, den)
            json.dump(lams, open(lp, "w"), indent=1)
        lam = lams[f"S{i}"]
        log(f"S{i} ({g}, r = {r}): λ_min(B) ≈ {lam:.4e}")
        M = [[x * Lam / cr for x in row] for row in B]
        assert all(x.denominator == 1 for row in M for x in row)
        M = [[x.numerator for x in row] for row in M]
        # shift ε = θ λ (in the units of M = Λ B / c_r): a larger θ gives Δ more diagonal slack, too large a θ makes a
        # pivot nonpositive (both are detected exactly); first θ that works
        for th in [Fr(x) for x in os.environ.get("THETAS", "0.86,0.8,0.7,0.6,0.5").split(",")]:
            epsS = int(Fr(lam) * th * Lam / cr)
            pk, why = pack_np(M, epsS)
            if pk is None:
                log(f"S{i}: θ = {float(th)}: {why}")
                continue
            d, l, D = pk
            sl = dd_slack(D)
            log(f"S{i}: θ = {float(th)}: packed at Λ = Λ0·2^{s}; Δ diagonal slack {'+' if sl >= 0 else '-'}"
                f"{abs(sl).bit_length()} bits")
            if sl >= 0:
                break
        else:
            raise SystemExit(f"S{i}: no shift θ works at s = {s}")
        assert all(x >= 0 for x in d) and all(D[a][c] == D[c][a] for a in range(r) for c in range(r)), f"S{i}: d, Δ"
        pickle.dump(dict(g=g, codes=codes, cr=cr, z=z, d=d, l=l, D=D, lam=lam, eps=epsS, theta=str(th)),
                    open(os.path.join(work, f"S{i}.pkl"), "wb"))
        meta["S"].append(dict(g=g, codes=codes, cr=cr, r=r, lam=lam, theta=str(th), eps=str(epsS)))
        del B, Bn, M, d, l, D, pk
        blocks[i] = None
    json.dump({k: (str(v) if isinstance(v, int) and v.bit_length() > 60 else v) for k, v in meta.items()},
              open(os.path.join(work, "meta.json"), "w"), indent=1)
    log(f"wrote {work}/meta.json, F.pkl, S*.pkl")


# ------------------------------------------------------------------ Python twins of Kissing5.Tree.Core (St, comb, rows)
import gmpy2
from gmpy2 import mpz

ZERO = (0, 0, 0, 0, 0, mpz(0), mpz(0))


def comb(s, t):
    """Kissing5.Tree.comb (canonical: the result does not depend on the order of the summands)."""
    if s[4] <= t[4]:
        return (s[0] + t[0], max(s[1], t[1]), max(s[2], t[2]), max(s[3], t[3]), s[4],
                s[5] + (t[5] << (t[4] - s[4])), s[6] + (t[6] << (t[4] - s[4])))
    return (s[0] + t[0], max(s[1], t[1]), max(s[2], t[2]), max(s[3], t[3]), t[4],
            t[5] + (s[5] << (s[4] - t[4])), t[6] + (s[6] << (s[4] - t[4])))


def sum_st(xs):
    """Kissing5.Tree.sumSt (canonical, so summed here as a balanced tree)."""
    xs = list(xs)
    if not xs:
        return ZERO
    while len(xs) > 1:
        xs = [comb(xs[i], xs[i + 1]) if i + 1 < len(xs) else xs[i] for i in range(0, len(xs), 2)]
    return xs[0]


def to_c1(s):
    """St.toC1."""
    return (s[0], s[1], s[2], s[3], int((mpz(1) << s[4]) * (s[5] - s[6])))


class Kr:
    def __init__(self, w, D):
        self.w, self.D = w, D

    def ex(self, m):
        return self.w * (m[0] + self.D * m[1] + self.D * self.D * m[2])

    def tev(self, terms, dbl=False):
        """T.ev (dbl: T.ev2) of a tree with these signed terms ((a, b, d), c), c != 0: canonical."""
        k = 2 if dbl else 1
        leaves = sorted(((k * self.ex(m), c) for m, c in terms), key=lambda x: x[0])
        def go(lo, hi):                      # (e, P, N) of leaves[lo:hi], balanced (O(N log r))
            if hi - lo == 1:
                e, c = leaves[lo]
                if dbl:
                    return (e, mpz(abs(c)), mpz(0))
                return (e, mpz(c), mpz(0)) if c > 0 else (e, mpz(0), mpz(-c))
            m = (lo + hi) // 2
            a, b = go(lo, m), go(m, hi)
            return (a[0], a[1] + (b[1] << (b[0] - a[0])), a[2] + (b[2] << (b[0] - a[0])))
        e, P, N = go(0, len(leaves))
        l1 = sum(abs(c) for _, c in terms)
        dg = [k * max(m[i] for m, _ in terms) for i in range(3)]
        return (l1, dg[0], dg[1], dg[2], e, P, N)

    def sq_row(self, q, terms):
        s = self.tev(terms)
        v = abs(s[5] - s[6])
        return (q * s[0] * s[0], 2 * s[1], 2 * s[2], 2 * s[3], 2 * s[4], q * v * v, mpz(0))

    def pair_row(self, z, di, terms):
        a, b, d = z
        E = self.ex(z)
        if not terms:
            return (di, 2 * a, 2 * b, 2 * d, 2 * E, mpz(di), mpz(0))
        s1, s2 = self.tev(terms), self.tev(terms, True)
        c0 = (di + s1[0], 2 * a, 2 * b, 2 * d, 2 * E, mpz(di + s1[0]), mpz(0))
        c3 = (2 * s1[0], a + s1[1], b + s1[2], d + s1[3], E + 1 + s1[4], s1[5], s1[6])
        return comb(comb(c0, s2), c3)

    # ---- Kissing5.Tree.rst on cert3_util expression trees (with lazy substitution nodes, as Cert.sbst)
    def rst(self, e):
        memo = {}
        w, D = self.w, self.D

        def go(e, ijk):
            key = (id(e), ijk)
            if key in memo:
                return memo[key][0]
            tg = e[0]
            if tg == U.C:
                n = e[1]
                r = (abs(n), 0, 0, 0, 0, mpz(max(n, 0)), mpz(max(-n, 0)))
            elif tg == U.MON:
                a, b, d = e[1], e[2], e[3]
                if ijk is not None:
                    a, b, d = U.sbst_exps(ijk, a, b, d)
                r = (1, a, b, d, w * (a + D * b + D * D * d), mpz(1), mpz(0))
            elif tg == U.SB:
                r = go(e[2], e[1])
            elif tg == U.ADD:
                r = comb(go(e[1], ijk), go(e[2], ijk))
            else:
                s, t = go(e[1], ijk), go(e[2], ijk)
                r = (s[0] * t[0], s[1] + t[1], s[2] + t[2], s[3] + t[3], s[4] + t[4],
                     s[5] * t[5] + s[6] * t[6], s[5] * t[6] + s[6] * t[5])
            memo[key] = (r, e)
            return r
        return go(e, None)


# ------------------------------------------------------------------ Python twins of Kissing5.Tree.FPart
def bs(f, lo, n, d=64):
    if d == 0:
        return U.sumRange(n, lambda i: f(lo + i))
    if n <= 1:
        return U.c(0) if n == 0 else f(lo)
    return U.add(bs(f, lo, n // 2, d - 1), bs(f, lo + n // 2, n - n // 2, d - 1))


def fpB(r, b):
    ent = [[b.ent(r, a, c) for c in range(r)] for a in range(r)]
    return bs(lambda a: bs(lambda c: U.smul(ent[a][c], U.mon(a, c, 0)), 0, r), 0, r)


def fkB(r, b, k):
    from emit_k5 import q5E
    return U.mul(fpB(r, b), q5E(k))


SIX = [(0, 1, 2), (0, 0, 3), (1, 1, 3), (2, 2, 3), (3, 3, 3)]


def c1_ftotK_groups(n, G):
    """Kissing5.Tree.c1Stat_c1FtotK: the statistic of c1FtotK n e from those of its five sixE groups."""
    return U.c1Add(U.c1Add(U.c1Smul((n - 1) * (n - 2), G[0]),
                           U.c1Smul(n - 1, U.c1Add(U.c1Add(G[1], G[2]), G[3]))), G[4])


# ------------------------------------------------------------------ the SOS rows of a block
def block_rows(S):
    """(sq, pr): sq = [(q, d_q, terms)], terms = [((a, b, d), l_q[c])] over c with l_q[c] != 0;
    pr = [(i, z_i, di, terms)], terms = [(z_j, Δ_ij)] over j > i with Δ_ij != 0, di = Δ_ii - Σ_{j≠i} |Δ_ij|."""
    z, d, l, D = S["z"], S["d"], S["l"], S["D"]
    r = len(z)
    sq = [(q, d[q], [(z[c], l[q][c]) for c in range(r) if l[q][c] != 0]) for q in range(r)]
    pr = []
    for i in range(r):
        di = D[i][i] - sum(abs(D[i][j]) for j in range(r) if j != i)
        assert di >= 0
        pr.append((i, z[i], di, [(z[j], D[i][j]) for j in range(i + 1, r) if D[i][j] != 0]))
    return sq, pr


def row_l1_deg(kind, row):
    """(ℓ¹, dx, dy, dz) of sqRow / PRow.st (w-independent), as Kissing5.Tree.Core computes them."""
    if kind == "Q":
        q, dq, terms = row
        A = sum(abs(c) for _, c in terms)
        return (dq * A * A, *[2 * max(m[i] for m, _ in terms) for i in range(3)])
    i, zi, di, terms = row
    if not terms:
        return (di, 2 * zi[0], 2 * zi[1], 2 * zi[2])
    A = sum(abs(c) for _, c in terms)
    dg = [max(m[k] for m, _ in terms) for k in range(3)]
    return (di + 4 * A, *[max(2 * zi[k], 2 * dg[k], zi[k] + dg[k]) for k in range(3)])


def chunk_rows(rows, kind, budget):
    """Consecutive chunks with at most `budget` terms each (a chunk holds at least one row)."""
    out, cur, cost = [], [], 0
    for row in rows:
        t = len(row[2] if kind == "Q" else row[3]) + 1
        if cur and cost + t > budget:
            out.append(cur); cur, cost = [], 0
        cur.append(row); cost += t
    if cur:
        out.append(cur)
    return out


# ------------------------------------------------------------------ Lean text
CH = 4096
GROUP = int(os.environ.get("GROUP", "8"))      # chunk values per group sum in S*/Sum.lean


def lean_nat(x):
    """A Nat literal as a balanced `cat` tree of CH-bit hex chunks (zero chunks are `0x0`)."""
    x = mpz(x)
    if x < (mpz(1) << CH):
        return hex(int(x))
    h = gmpy2.digits(x, 16)
    k = CH // 4
    ch = [h[max(0, j - k):j] for j in range(len(h), 0, -k)]           # least significant first
    ch = ["0x" + (c.lstrip("0") or "0") for c in ch]

    def go(lo, hi):
        if hi - lo == 1:
            return ch[lo]
        m = (lo + hi) // 2
        return f"(cat {CH * (m - lo)} {go(lo, m)} {go(m, hi)})"
    return go(0, len(ch))


def lean_st(s):
    return "⟨" + ", ".join([str(x) for x in s[:5]] + [lean_nat(s[5]), lean_nat(s[6])]) + "⟩"


# The kernel hashes a Nat literal by its low 64 bits. With `lean_nat`, most chunks of a packed value end in 64 zero or
# 64 one bits, so a declaration that evaluates many such values fills the kernel's caches with colliding keys and slows
# down superlinearly (8 chunk values: 23 s; 62: hours). `lean_nat_u` moves the piece boundaries so that all pieces of
# all values written with it have pairwise distinct low 64 bits (long runs of equal bits become one piece: `0x0` or all
# ones); the same 8 values then take 0.7 s. The chunk values `V…` (one per declaration) keep `lean_nat`.
M64 = (1 << 64) - 1
USED = set()


def lean_nat_u(x):
    """A Nat literal as a balanced `cat` tree whose pieces have low 64 bits distinct from all pieces written so far."""
    x = mpz(x)
    if x < (mpz(1) << CH):
        return hex(int(x))
    n = x.bit_length()
    by = int(x).to_bytes((n + 7) // 8 + 9, "little")

    def win(b):
        return (int.from_bytes(by[b // 8:b // 8 + 9], "little") >> (b % 8)) & M64
    cuts = [0]
    while n - cuts[-1] > CH:
        base = cuts[-1] + CH
        for b in list(range(base, cuts[-1] + 64, -1)) + list(range(base + 1, min(n - 64, cuts[-1] + 2 * CH))):
            wb = win(b)
            if wb not in USED and wb != 0 and wb != M64:
                break
        else:                       # a long run of equal bits: one piece for the run, cut again where it ends
            q = gmpy2.bit_scan1(x, base) if win(base) == 0 else gmpy2.bit_scan0(x, base)
            cuts.append(base)
            if q >= n:
                break
            cuts.append(q)
            USED.add(win(q))
            continue
        USED.add(wb)
        cuts.append(b)
    USED.add(int(x & M64))
    cuts.append(n)
    pv = [(x >> cuts[i]) & ((mpz(1) << (cuts[i + 1] - cuts[i])) - 1) for i in range(len(cuts) - 1)]
    assert sum(v << c for v, c in zip(pv, cuts)) == x, "lean_nat_u: pieces"
    pc = [hex(int(v)) for v in pv]

    def go(lo, hi):
        if hi - lo == 1:
            return pc[lo]
        m = (lo + hi) // 2
        return f"(cat {cuts[m] - cuts[lo]} {go(lo, m)} {go(m, hi)})"
    return go(0, len(pc))


def lean_st_u(s):
    return "⟨" + ", ".join([str(x) for x in s[:5]] + [lean_nat_u(s[5]), lean_nat_u(s[6])]) + "⟩"


def lean_tree(kr, terms):
    terms = sorted(terms, key=lambda t: (kr.ex(t[0]), t[0]))

    def go(lo, hi):
        if hi - lo == 1:
            (a, b, d), c = terms[lo]
            return f"(.{'pos' if c > 0 else 'neg'} {a} {b} {d} {abs(c)})"
        m = (lo + hi) // 2
        return f"(.nd {go(lo, m)} {go(m, hi)})"
    return go(0, len(terms))


def lean_c1(st):
    kv = st[4]
    return f"({st[0]}, {st[1]}, {st[2]}, {st[3]}, ({kv} : Int))" if kv >= 0 else \
        f"({st[0]}, {st[1]}, {st[2]}, {st[3]}, (-{-kv} : Int))"


NSP = "Kissing5.Cert44"
GEN = "lean/gen/gen_t5.py"


def hdr(meta, what):
    return (f"/-! {what}\n\nGenerated by `{GEN}` from `{meta['cert']}` (sha256 {meta['sha256']}).\n"
            "Do not edit; regenerate. -/\n")


def write(path, text):
    """Write `text` to `path` unless the file already has exactly this content (keeps built modules up to date)."""
    os.makedirs(os.path.dirname(path), exist_ok=True)
    if os.path.exists(path) and open(path, encoding="utf-8").read() == text:
        return
    with open(path, "w", encoding="utf-8") as f:
        f.write(text)


# ------------------------------------------------------------------ emit
def cmd_emit(work, leandir):
    meta = json.load(open(os.path.join(work, "meta.json")))
    n, Lam, eps, K = meta["n"], int(meta["Lam"]), int(meta["eps"]), meta["K"]
    C2 = n * (n - 1) // 2
    budget = int(os.environ.get("TERMS", "8000"))
    Fb = [U.Blk(*x) for x in pickle.load(open(os.path.join(work, "F.pkl"), "rb"))]
    nS = len(meta["S"])
    out = os.path.join(leandir, "Cert44")
    # ---- pass 1: ℓ¹ and degrees (w-independent) -> w, D
    pF = [U.c1FtotK(n, fkB(len(b.D), b, k)) for k, b in enumerate(Fb)]
    lF = [U.stat_l(e) for e in pF]
    lS, rowsS = [], []
    for bi in range(nS):
        S = pickle.load(open(os.path.join(work, f"S{bi}.pkl"), "rb"))
        sq, pr = block_rows(S)
        gl = U.stat_l(gKE(S["codes"]))
        tot = (0, 0, 0, 0)
        for kind, rows in (("Q", sq), ("P", pr)):
            for row in rows:
                x = row_l1_deg(kind, row)
                tot = (tot[0] + x[0], max(tot[1], x[1]), max(tot[2], x[2]), max(tot[3], x[3]))
        lS.append((gl[0] * tot[0], gl[1] + tot[1], gl[2] + tot[2], gl[3] + tot[3]))
        log(f"S{bi}: r = {len(S['z'])}, ℓ¹ {lS[-1][0].bit_length()} bits, degrees {lS[-1][1:]}")
        del S, sq, pr
    tot0 = U.c1Sub(U.c1Sub(U.c1C(-(6 * (n - 1) * eps)), U.c1Smul(C2, U.c1Sum([x + (0,) for x in lF]))),
                   U.c1Smul(6 * (n - 1) * C2, U.c1Sum([x + (0,) for x in lS])))
    w, D = U.chk_params(*tot0[:4])
    kr = Kr(w, D)
    log(f"identity: ℓ¹ {tot0[0].bit_length()} bits, degrees {tot0[1:4]}: w = {w}, D = {D}")
    # ---- pass 2a: the F groups
    stF, fmods = [], []
    for k, b in enumerate(Fb):
        m = len(b.D)
        e = fkB(m, b, k)
        G = [kr.rst(U.sixE(*g, e)) for g in SIX]
        st = c1_ftotK_groups(n, [to_c1(x) for x in G])
        assert st[:4] == lF[k], f"F{k}: ℓ¹/degrees"
        stF.append(st)
        fmods.append(G)
        log(f"F{k} (m = {m}): five groups, values {[max(x[5].bit_length(), x[6].bit_length()) for x in G]} bits")
    # ---- pass 2b: the SOS rows, chunk by chunk (written as they are computed)
    stS, blocks = [], []
    for bi in range(nS):
        S = pickle.load(open(os.path.join(work, f"S{bi}.pkl"), "rb"))
        sq, pr = block_rows(S)
        info = dict(codes=S["codes"], g=S["g"], r=len(S["z"]), Q=[], P=[])
        W, Vs = {}, {}
        for kind, rows in (("Q", sq), ("P", pr)):
            chs = chunk_rows(rows, kind, budget)
            acc = ZERO
            Vs[kind] = []
            for j, ch in enumerate(chs):
                L = [f"import Kissing5.Tree.Core", "", hdr(meta, f"Rows {ch[0][0]}–{ch[-1][0]} ({'squares' if kind == 'Q' else 'remainder rows'}) "
                     f"of the SOS block S{bi} (`{S['g']}`, r = {len(S['z'])}): chunk {j} of {len(chs)}; core Lean only; "
                     f"one `decide +kernel` for the sum of the chunk (`w = {w}`, `D = {D}`)."),
                     "set_option maxRecDepth 100000", "", f"namespace {NSP}", "", "open Kissing5.Tree", ""]
                sts, ents = [], []
                for row in ch:
                    if kind == "Q":
                        q, dq, terms = row
                        sts.append(kr.sq_row(dq, terms))
                        L.append(f"noncomputable def RQ{bi}_{q} : T := {lean_tree(kr, terms)}")
                        ents.append(f"({dq}, RQ{bi}_{q})")
                    else:
                        i, zi, di, terms = row
                        sts.append(kr.pair_row(zi, di, terms))
                        if terms:
                            L.append(f"noncomputable def RP{bi}_{i} : T := {lean_tree(kr, terms)}")
                            ents.append(f"⟨{zi[0]}, {zi[1]}, {zi[2]}, {di}, some RP{bi}_{i}⟩")
                        else:
                            ents.append(f"⟨{zi[0]}, {zi[1]}, {zi[2]}, {di}, none⟩")
                V = sum_st(sts)
                acc = comb(acc, V) if j else V
                Vs[kind].append(V)
                ty = "List (Nat × T)" if kind == "Q" else "List PRow"
                fn = "fun x => sqRow {w} {D} x.1 x.2" if kind == "Q" else "fun p => p.st {w} {D}"
                fn = fn.format(w=w, D=D)
                L += ["", f"noncomputable def C{kind}{bi}_{j} : {ty} :=", "  [" + ",\n   ".join(ents) + "]", "",
                      f"noncomputable def V{kind}{bi}_{j} : St := {lean_st(V)}", "",
                      f"theorem chk{kind}{bi}_{j} : sumSt (C{kind}{bi}_{j}.map {fn}) = V{kind}{bi}_{j} := by",
                      "  decide +kernel", "", f"end {NSP}", ""]
                write(os.path.join(out, f"S{bi}", f"{kind}{j}.lean"), "\n".join(L))
                info[kind].append(dict(rows=[row[0] for row in ch], terms=sum(len(row[2] if kind == 'Q' else row[3]) for row in ch),
                                       bits=max(V[5].bit_length(), V[6].bit_length())))
            W[kind] = acc
            log(f"S{bi} {kind}: {len(rows)} rows in {len(chs)} chunks (≤ {budget} terms), "
                f"chunk values up to {max(c['bits'] for c in info[kind])} bits")
        gst = U.c1Stat(gKE(S["codes"]), w, D)
        stS.append(U.c1Mul(gst, U.c1Add(to_c1(W["Q"]), to_c1(W["P"]))))
        assert stS[-1][:4] == lS[bi], f"S{bi}: ℓ¹/degrees"
        # block sums (core Lean): map and sum theorems
        L = [hdr(meta, f"Chunk sums of the SOS block S{bi}: the statistics of all its rows, summed in groups of "
                       f"{GROUP} chunks (`U…`, one `decide +kernel` each), then the group sums (`W…`)."), ""]
        L = [f"import {NSP}.S{bi}.{kind}{j}" for kind in "QP" for j in range(len(info[kind]))] + [""] + L
        L += ["set_option maxRecDepth 100000", "", f"namespace {NSP}", "", "open Kissing5.Tree", ""]
        for kind in "QP":
            nc = len(info[kind])
            fn = (f"fun x => sqRow {w} {D} x.1 x.2" if kind == "Q" else f"fun p => p.st {w} {D}")
            vn = [f"V{kind}{bi}_{j}" for j in range(nc)]
            grp = [list(range(i, min(i + GROUP, nc))) for i in range(0, nc, GROUP)]
            Us = [sum_st([Vs[kind][j] for j in g]) for g in grp]
            Wu = sum_st(Us)
            assert Wu == W[kind], f"S{bi} {kind}: grouped sum"
            for i, g in enumerate(grp):
                L += [f"noncomputable def U{kind}{bi}_{i} : St := {lean_st_u(Us[i])}", "",
                      f"theorem g{kind}{bi}_{i} : sumSt [{', '.join(vn[j] for j in g)}] = U{kind}{bi}_{i} := by",
                      "  decide +kernel", ""]
            gl = "[" + ", ".join("[" + ", ".join(vn[j] for j in g) + "]" for g in grp) + "]"
            un = [f"U{kind}{bi}_{i}" for i in range(len(grp))]
            L += [f"noncomputable def W{kind}{bi} : St := {lean_st_u(W[kind])}", "",
                  f"theorem map{kind}{bi} : [{', '.join(f'C{kind}{bi}_{j}' for j in range(nc))}].map",
                  f"    (fun c => sumSt (c.map {fn})) = [{', '.join(vn)}] := by",
                  f"  simp only [List.map_cons, List.map_nil, {', '.join(f'chk{kind}{bi}_{j}' for j in range(nc))}]", "",
                  f"theorem flat{kind}{bi} : ({gl} : List (List St)).flatten = [{', '.join(vn)}] := rfl", "",
                  f"theorem grp{kind}{bi} : ({gl} : List (List St)).map sumSt = [{', '.join(un)}] := by",
                  f"  simp only [List.map_cons, List.map_nil, {', '.join(f'g{kind}{bi}_{i}' for i in range(len(grp)))}]", "",
                  f"theorem sum{kind}{bi} : sumSt [{', '.join(un)}] = W{kind}{bi} := by",
                  "  decide +kernel", ""]
        L += [f"end {NSP}", ""]
        write(os.path.join(out, f"S{bi}", "Sum.lean"), "\n".join(L))
        blocks.append(info)
        del S, sq, pr
    # ---- the whole identity
    tot = U.c1Sub(U.c1Sub(U.c1C(-(6 * (n - 1) * eps)), U.c1Smul(C2, U.c1Sum(stF))),
                  U.c1Smul(6 * (n - 1) * C2, U.c1Sum(stS)))
    assert tot[:4] == tot0[:4]
    log(f"identity: Kronecker value {'0: the identity holds' if tot[4] == 0 else 'NONZERO'}")
    assert tot[4] == 0, "the identity does not hold"
    assert U.chk_params(*tot[:4]) == (w, D)
    emit_top(meta, out, Fb, fmods, blocks, w, D, tot, n, Lam, eps)
    rep = dict(w=w, D=D, l1=str(tot[0]), deg=tot[1:4], budget=budget,
               chunks={f"S{bi}": {k: len(b[k]) for k in "QP"} for bi, b in enumerate(blocks)},
               blocks=[{k: v for k, v in b.items()} for b in blocks])
    json.dump(rep, open(os.path.join(work, "emit_report.json"), "w"), indent=1)
    log(f"wrote {out} and {work}/emit_report.json")


def emit_top(meta, out, Fb, fmods, blocks, w, D, tot, n, Lam, eps):
    nS, K = len(blocks), len(Fb)
    # Data
    L = ["import Kissing5.Tree.Cert"] + [f"import {NSP}.S{bi}.Sum" for bi in range(nS)] + [""]
    L.append(hdr(meta, f"The exact kissing certificate for `n = {n}` in the `Kissing5.Tree.CertK5T` format (common "
                       f"denominator `Λ = lam_`): margin `eps_ / lam_ > 0`; kernel blocks `F0..F{K - 1}` "
                       f"(`ThomsonN7.Cert.mkBlk`, `F_k = ent_k / lam_`); SOS blocks `S0..S{nS - 1}` as explicit sums "
                       f"of squares, their rows in the chunks `CQ…`, `CP…` of `{NSP}.S*`."))
    L += [f"namespace {NSP}", "", "open ThomsonN7.Cert Kissing5.Tree", "",
          f"def lam_ : Nat := {Lam}", f"def eps_ : Int := ({eps} : Int)", ""]
    for k, b in enumerate(Fb):
        L.append(U_blk_lean(f"F{k}", b, len(b.D)))
        L.append("")
    for bi, info in enumerate(blocks):
        L += [f"noncomputable def S{bi} : TBlk :=",
              f"  ⟨{info['codes']},",
              f"   [{', '.join(f'CQ{bi}_{j}' for j in range(len(info['Q'])))}].flatten,",
              f"   [{', '.join(f'CP{bi}_{j}' for j in range(len(info['P'])))}].flatten⟩", ""]
    L += ["/-- The certificate. -/",
          f"noncomputable def cf : CertK5T := ⟨{n}, lam_, eps_, [{', '.join(f'F{k}' for k in range(K))}], "
          f"[{', '.join(f'S{bi}' for bi in range(nS))}]⟩", "", f"end {NSP}", ""]
    write(os.path.join(out, "Data.lean"), "\n".join(L))
    # F groups, one module per block
    for k, G in enumerate(fmods):
        L = [f"import {NSP}.Data", "", hdr(meta, f"Kronecker statistics of the `F`-summand of the block F{k} "
             f"(`w = {w}`, `D = {D}`): its five six-fold sums `sixE`, one `decide +kernel` each (`Kissing5.Tree.rst`, "
             f"relative values), then `c1Stat_c1FtotK`."),
             "set_option maxRecDepth 100000", "", f"namespace {NSP}", "",
             "open ThomsonN7.Cert ThomsonN7.Case1 Kissing5.Tree", ""]
        e = f"(fkB (cf.m {k}) (cf.blk {k}) {k})"
        for g, (ijk, V) in enumerate(zip(SIX, G)):
            L += [f"noncomputable def VF{k}_{g} : St := {lean_st_u(V)}", "",
                  f"theorem rstF{k}_{g} : rst {w} {D} (sixE {ijk[0]} {ijk[1]} {ijk[2]} {e}) = VF{k}_{g} := by",
                  "  decide +kernel", ""]
        rw = ", ".join(f"← rst_toC1 {w} {D} (sixE {a} {b} {c} {e}), rstF{k}_{g}" for g, (a, b, c) in enumerate(SIX))
        L += [f"theorem stat_F{k} : c1Stat {w} {D} (c1FtotK cf.n {e}) =",
              f"    c1Add (c1Add (c1Smul (((cf.n : ℤ) - 1) * ((cf.n : ℤ) - 2)) (VF{k}_0).toC1)",
              f"      (c1Smul ((cf.n : ℤ) - 1) (c1Add (c1Add (VF{k}_1).toC1 (VF{k}_2).toC1) (VF{k}_3).toC1)))",
              f"      (VF{k}_4).toC1 := by",
              f"  rw [c1Stat_c1FtotK, {rw}]", "", f"end {NSP}", ""]
        write(os.path.join(out, f"ChkF{k}.lean"), "\n".join(L))
    # S statistics, the identity, F blocks ok, the check
    L = [f"import {NSP}.ChkF{k}" for k in range(K)] + [""]
    L += ["-- Adapted from huwngtran/thomson-n7-lean @ 25f2fa5 (formal/lean/ThomsonN7/Solution.lean, namespace ThomsonN7):",
          "-- `cf_idE_stat` from `Case1.c1_idE_stat`, `cf_chk` from `Case1.cf_chk`, `cf_blocks` from `Case1.cf_blocks`,",
          "-- `cf_ok` from `Case1.cf_ok`, `cf_K`, `cf_S`, `cf_range` from `Case1.c1_K`, `Case1.c1_S`, `Case1.c1_range4`.", ""]
    L.append(hdr(meta, f"The Kronecker check of the identity of the kissing certificate: composition of the piece "
                       f"statistics (ℓ¹ < 2^{w}, degrees < {D}, Kronecker value 0; soundness: "
                       f"`Kron.Ex.ev_eq_zero_of_kev`)."))
    L += ["set_option maxRecDepth 100000", "", f"namespace {NSP}", "", "open ThomsonN7.Cert ThomsonN7.Case1 Kissing5.Tree", "",
          f"theorem cf_K : cf.K = {K} := rfl", "",
          f"theorem cf_S : cf.S = [{', '.join(f'S{bi}' for bi in range(nS))}] := rfl", "",
          f"theorem cf_range : List.range {K} = [{', '.join(str(k) for k in range(K))}] := rfl", ""]
    for bi, info in enumerate(blocks):
        L += [f"theorem stat_S{bi} : c1Stat {w} {D} (tblkE S{bi}) =",
              f"    c1Mul (c1Stat {w} {D} (Kissing.gKE {info['codes']})) (c1Add (WQ{bi}).toC1 (WP{bi}).toC1) :=",
              f"  c1Stat_tblkE_chunks {w} {D} {info['codes']} _ _ _ _ _ _ _ _ _ _",
              f"    mapQ{bi} flatQ{bi} grpQ{bi} sumQ{bi} mapP{bi} flatP{bi} grpP{bi} sumP{bi}", ""]
    L += [f"/-- The statistics of the whole identity expression: `ℓ¹`-norm below `2 ^ {w}`, degrees "
          f"`{tot[1]}, {tot[2]}, {tot[3]}`, Kronecker value `0`. -/",
          f"theorem cf_idE_stat : c1Stat {w} {D} cf.idE = {lean_c1(tot)} := by",
          f"  rw [kStat_idE5T, cf_K, cf_S, cf_range]",
          f"  simp only [List.map_cons, List.map_nil]",
          f"  rw [{', '.join(f'stat_F{k}' for k in range(K))}, {', '.join(f'stat_S{bi}' for bi in range(nS))}]",
          "  decide +kernel", "",
          "/-- The Kronecker check of the identity expression. -/",
          "theorem cf_chk : chk cf.idE = true := by",
          f"  have h := ThomsonN7.Case1.c1Stat_eq {w} {D} cf.idE",
          "  rw [cf_idE_stat] at h",
          "  simp only [Prod.mk.injEq] at h",
          "  obtain ⟨hl, hx, hy, hz, hk⟩ := h",
          "  unfold chk",
          "  rw [← hl, ← hx, ← hy, ← hz]",
          f"  have hW : Nat.log2 {tot[0]} + 1 = {w} := by decide +kernel",
          f"  have hD : max {tot[1]} (max {tot[2]} {tot[3]}) + 1 = {D} := by decide +kernel",
          "  rw [hW, hD]",
          "  exact decide_eq_true hk.symm", "",
          "/-- The positive-semidefiniteness certificates of the `F`-blocks. -/",
          "theorem cf_blocks : (List.range cf.K).all (fun k => (cf.blk k).ok (cf.m k)) = true := by",
          "  decide +kernel", "",
          "/-- The kissing certificate passes the exact check. -/",
          "theorem cf_ok : cf.check = true := by",
          "  unfold CertK5T.check",
          "  rw [cf_chk, cf_blocks]",
          "  decide +kernel", "",
          "/-- The margin is positive. -/",
          "theorem cf_eps_pos : 0 < cf.eps := by decide +kernel", "",
          f"/-- The certificate is for `{n}` points. -/",
          f"theorem cf_n : cf.n = {n} := rfl", "", f"end {NSP}", ""]
    write(os.path.join(out, "Check.lean"), "\n".join(L))


def U_blk_lean(name, b, r):
    """`def name : Blk := mkBlk r Bd Bl BD xd xl xD` (as emit_k5.blk_lean), with the round trip checked."""
    Bd = U.field_width(b.d)
    Bl = U.field_width([v for col in b.l for v in col])
    BD = U.field_width([v for row in b.D for v in row])
    xd, xl, xD = U.packI(Bd, b.d), U.packM(Bl, b.l), U.packM(BD, b.D)
    back = U.mkBlk(r, Bd, Bl, BD, xd, xl, xD)
    assert back.d == b.d and back.l == b.l and back.D == b.D, "mkBlk round trip"
    return f"def {name} : Blk := mkBlk {r} {Bd} {Bl} {BD}\n  {hex(xd)}\n  {hex(xl)}\n  {hex(xD)}"


if __name__ == "__main__":
    cmd = sys.argv[1]
    if cmd == "pack":
        cmd_pack(sys.argv[2], sys.argv[3])
    elif cmd == "emit":
        cmd_emit(sys.argv[2], sys.argv[3])
    else:
        raise SystemExit(__doc__)
