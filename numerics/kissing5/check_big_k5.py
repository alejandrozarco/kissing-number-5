"""Independent exact check of a 5D kissing certificate (round_hp.py / round_k5.py JSON format) that scales to D = 32.

usage: python3 check_big_k5.py CERT.json [--controls]

Same mathematics as check_cert_k5.py (whose kernel definitions are copied verbatim below); shares no code with the
generators round_k3.py, round_k5.py, round_hp.py, sdpa5.py, sym.py or hp_blocks.py. Definitions:
  Q3 0 = 1, Q3 1 = t - uv, Q3 (k+1) = (2(k+1)(t-uv) Q3 k - k (1-u^2)(1-v^2) Q3 (k-1)) / (k+2);
  Y3 m k u v t [a][b] = u^a v^b Q3 k u v t;
  S3 m k u v t = 1/6 (Y3 uvt + Y3 utv + Y3 vut + Y3 vtu + Y3 tuv + Y3 tvu);
  Rk n m k u v t = (n-2) S3 uvt + (S3 uu1 + S3 vv1 + S3 tt1) + 1/(n-1) S3 111;
Checks:
  (1) the identity  -sum_k <F_k, Rk n k u v t> - e/C(n,2) = sum_r g_r(u,v,t) z_r^T B_r z_r :
      (1a) exactly, as polynomials, coefficient by coefficient: the left side is built from the definitions with
           a small polynomial class written here (<F, S3 XYZ> = 1/6 sum over the 6 orders of H(order), where
           H(x,y,z) = f(x,y) Q3(x,y,z) and f(x,y) = sum_ab F[a][b] x^a y^b); the right side by collecting the entries
           of B_r by monomial z_i z_j and multiplying by g_r;
      (1b) cross-check of (1a): at a few random rational points, the left side evaluated directly from the matrix
           definitions (the functions of check_cert_k5.py), the right side as the exact product z^T B z (flint), and
           the polynomial of (1a), must all agree exactly;
  (2) every F_k and B_r symmetric and positive definite: an approximate Cholesky factor L (blocked, 384-bit
      midpoint arithmetic in Arb), W = midpoints of Arb's inverse of L (an exact dyadic matrix), and then
      M' = W B W^T in rigorous ball arithmetic (Arb, via python-flint; every ball contains the exact entry). If
      every row of M' is certainly strictly diagonally dominant with a positive diagonal, M' > 0 (Gershgorin), so W
      is invertible and B > 0. (Plain interval Cholesky of B overestimates its radii exponentially on these
      near-singular matrices, so the rigour is put in the a-posteriori check of M' instead.) Same principle as the
      generator's congruence certificate, different code and arithmetic (Arb balls instead of fixed-point integers
      and an exact flint product);
  (3) e > 0, and each multiplier g_r >= 0 on {GramOK, u, v, t <= 1/2};
  (4) a float sanity check of the claimed inequality on random points of the region.
With --controls, negative controls: the certificate with one B entry perturbed, or with a larger e, must fail (1a);
B - 1.01 lam I must fail (2), also when the rigorous step is given the W of B itself, and B - 0.99 lam I pass, for
the multiplier-1 block (lam ~ its smallest eigenvalue,
estimated here by power iteration on W^T W ~ B^{-1}).
"""
import json, sys, time, random, itertools
from fractions import Fraction as Fr
from math import comb
import flint
from flint import fmpq, fmpq_mat, arb, arb_mat

T0 = time.time()
PREC = 384


def log(s):
    print(f"[{time.time() - T0:8.1f}s] {s}", flush=True)


def fail(msg):
    raise SystemExit(f"CERTIFICATE REJECTED: {msg}")


def q(s):
    a, _, b = s.partition("/")
    return fmpq(int(a), int(b) if b else 1)


# ---------- the definitions, as in check_cert_k5.py (matrix form, for (1b) and (4)) ----------
def Q3(k, u, v, t):
    q0, q1 = fmpq(1), t - u * v
    if k == 0:
        return q0
    for j in range(1, k):
        q0, q1 = q1, (fmpq(2 * (j + 1)) * (t - u * v) * q1 - fmpq(j) * (1 - u * u) * (1 - v * v) * q0) / fmpq(j + 2)
    return q1


def Y3(m, k, u, v, t):
    qq = Q3(k, u, v, t)
    return fmpq_mat(m, m, [u ** a * v ** b * qq for a in range(m) for b in range(m)])


def S3(m, k, u, v, t):
    Y = (Y3(m, k, u, v, t) + Y3(m, k, u, t, v) + Y3(m, k, v, u, t) + Y3(m, k, v, t, u) + Y3(m, k, t, u, v)
         + Y3(m, k, t, v, u))
    return Y * fmpq(1, 6)


def Rk(n, m, k, u, v, t):
    one = fmpq(1)
    return (S3(m, k, u, v, t) * fmpq(n - 2) + (S3(m, k, u, u, one) + S3(m, k, v, v, one) + S3(m, k, t, t, one))
            + S3(m, k, one, one, one) * fmpq(1, n - 1))


def matDot(A, B):
    return sum((A[i, j] * B[i, j] for i in range(A.nrows()) for j in range(A.ncols())), fmpq(0))


def mult_val(name, u, v, t):
    x = {"u": u, "v": v, "t": t}
    if name == "1":
        return fmpq(1)
    if name == "detG":
        return 1 + 2 * u * v * t - u * u - v * v - t * t
    for X in "uvt":
        if name == f"1+{X}":
            return 1 + x[X]
        if name == f"1/2-{X}":
            return fmpq(1, 2) - x[X]
        if name == f"(1+{X})(1/2-{X})":
            return (1 + x[X]) * (fmpq(1, 2) - x[X])
    raise ValueError(name)


# ---------- polynomials in (u, v, t): dict exponent triple -> fmpq ----------
def padd(P, Q_, c=1):
    R = dict(P)
    for m, x in Q_.items():
        y = R.get(m, 0) + c * x
        if y == 0:
            R.pop(m, None)
        else:
            R[m] = y
    return R


def pmul(P, Q_):
    R = {}
    for (a, b, c), x in P.items():
        for (d, e, f), y in Q_.items():
            m = (a + d, b + e, c + f)
            R[m] = R.get(m, 0) + x * y
    return {m: x for m, x in R.items() if x != 0}


def pscale(P, c):
    return {m: x * c for m, x in P.items()} if c != 0 else {}


def psubst(P, slots):
    """P(p1, p2, p3) with p_i = the variable slots[i] (0 = u, 1 = v, 2 = t) or the constant 1 (slots[i] = None)."""
    R = {}
    for ex, x in P.items():
        e = [0, 0, 0]
        for i in range(3):
            if slots[i] is not None:
                e[slots[i]] += ex[i]
        e = tuple(e)
        R[e] = R.get(e, 0) + x
    return {m: x for m, x in R.items() if x != 0}


def peval(P, u, v, t):
    return sum((x * u ** a * v ** b * t ** c for (a, b, c), x in P.items()), fmpq(0))


ONE = {(0, 0, 0): fmpq(1)}
U_, V_, T_ = {(1, 0, 0): fmpq(1)}, {(0, 1, 0): fmpq(1)}, {(0, 0, 1): fmpq(1)}


def Q3poly(k):
    tm = padd(T_, pmul(U_, V_), -1)                                   # t - uv
    a = padd(ONE, pmul(U_, U_), -1); b = padd(ONE, pmul(V_, V_), -1)
    w = pmul(a, b)                                                     # (1-u^2)(1-v^2)
    q0, q1 = ONE, tm
    if k == 0:
        return q0
    for j in range(1, k):
        q0, q1 = q1, pscale(padd(pscale(pmul(tm, q1), fmpq(2 * (j + 1))), pmul(w, q0), -j), fmpq(1, j + 2))
    return q1


def mult_poly(name):
    if name == "1":
        return ONE
    if name == "detG":
        P = padd(ONE, pscale(pmul(pmul(U_, V_), T_), 2))
        for X in (U_, V_, T_):
            P = padd(P, pmul(X, X), -1)
        return P
    x = {"u": U_, "v": V_, "t": T_}
    for X in "uvt":
        if name == f"1+{X}":
            return padd(ONE, x[X])
        if name == f"1/2-{X}":
            return padd({(0, 0, 0): fmpq(1, 2)}, x[X], -1)
        if name == f"(1+{X})(1/2-{X})":
            return pmul(padd(ONE, x[X]), padd({(0, 0, 0): fmpq(1, 2)}, x[X], -1))
    raise ValueError(name)


DEG_G = {"1": 0, "detG": 3}
for _X in "uvt":
    DEG_G.update({f"1+{_X}": 1, f"1/2-{_X}": 1, f"(1+{_X})(1/2-{_X})": 2})


def lhs_poly(F, n, e):
    """-sum_k <F_k, Rk n k u v t> - e/C(n,2) as a polynomial."""
    orders = list(itertools.permutations(range(3)))
    # the argument triples of S3 in Rk, with their weights; slot values: 0 = u, 1 = v, 2 = t, None = 1
    args = [((0, 1, 2), fmpq(n - 2)), ((0, 0, None), fmpq(1)), ((1, 1, None), fmpq(1)), ((2, 2, None), fmpq(1)),
            ((None, None, None), fmpq(1, n - 1))]
    L = {}
    for k, Fk in enumerate(F):
        m = Fk.nrows()
        f = {}
        for a in range(m):
            for b in range(m):
                if Fk[a, b] != 0:
                    f[(a, b, 0)] = f.get((a, b, 0), 0) + Fk[a, b]
        H = pmul(f, Q3poly(k))                                         # H(x, y, z) = f(x, y) Q3(x, y, z)
        for trip, w in args:
            acc = {}
            for o in orders:                                           # H(p_o1, p_o2, p_o3): all 6 orders of trip
                acc = padd(acc, psubst(H, (trip[o[0]], trip[o[1]], trip[o[2]])))
            L = padd(L, pscale(acc, w * fmpq(1, 6)), -1)
    return padd(L, {(0, 0, 0): e / fmpq(comb(n, 2))}, -1)


def rhs_poly(S):
    R = {}
    for g, Z, B in S:
        m = len(Z)
        P = {}
        for i in range(m):
            zi = Z[i]
            for j in range(m):
                x = B[i, j]
                if x != 0:
                    mm = (zi[0] + Z[j][0], zi[1] + Z[j][1], zi[2] + Z[j][2])
                    P[mm] = P.get(mm, 0) + x
        R = padd(R, pmul(mult_poly(g), {mm: x for mm, x in P.items() if x != 0}))
    return R


# ---------- positive definiteness: approximate Cholesky, then a rigorous ball check of W B W^T ----------
def mid_cholesky(M, nb=48):
    """M: fmpq_mat. Approximate lower Cholesky factor (blocked; every entry rounded to its midpoint, so no interval
    blow-up). Returns (L as arb_mat of exact midpoints, None) or (None, message) if an approximate pivot is <= 0."""
    n = M.nrows()
    A = arb_mat(M)
    S = [[A[i, j].mid() for j in range(n)] for i in range(n)]
    Lf = [[arb(0)] * n for _ in range(n)]
    off = 0
    while S:
        r = len(S); b = min(nb, r)
        L11 = [[arb(0)] * b for _ in range(b)]
        for j in range(b):
            s = (S[j][j] - sum((L11[j][k] * L11[j][k] for k in range(j)), arb(0))).mid()
            if not s.mid() > 0:
                return None, f"approximate pivot {off + j} <= 0"
            d = s.sqrt().mid()
            L11[j][j] = d
            for i in range(j + 1, b):
                L11[i][j] = ((S[i][j] - sum((L11[i][k] * L11[j][k] for k in range(j)), arb(0))) / d).mid()
        for i in range(b):
            for j in range(i + 1):
                Lf[off + i][off + j] = L11[i][j]
        if r == b:
            break
        A21T = arb_mat([[S[b + i][j] for i in range(r - b)] for j in range(b)])
        X = arb_mat(L11).solve(A21T)
        Xm = [[X[j, i].mid() for j in range(b)] for i in range(r - b)]                # (r-b) x b = L21
        Xa = arb_mat(Xm)
        Sn = arb_mat([[S[b + i][b + j] for j in range(r - b)] for i in range(r - b)]) - Xa * Xa.transpose()
        for i in range(r - b):
            for j in range(b):
                Lf[off + b + i][off + j] = Xm[i][j]
        S = [[Sn[i, j].mid() for j in range(r - b)] for i in range(r - b)]
        off += b
    return arb_mat(Lf), None


def pd_check(M):
    """Rigorous: W = midpoints of an approximate inverse of the Cholesky factor (an exact matrix); the balls of
    M' = W B W^T contain its exact entries; if every row is certainly strictly diagonally dominant with a positive
    diagonal, then M' > 0 (Gershgorin), so W is invertible and B = W^{-1} M' W^{-T} > 0."""
    L, msg = mid_cholesky(M)
    if L is None:
        return False, msg, None
    n = M.nrows()
    Wi = L.inv()
    W = arb_mat([[Wi[i, j].mid() for j in range(n)] for i in range(n)])
    ok, info = dd_check(M, W)
    return ok, info, W


def dd_check(M, W):
    """the rigorous step: M' = W M W^T in ball arithmetic, each row certainly strictly diagonally dominant."""
    n = M.nrows()
    Mp = W * arb_mat(M) * W.transpose()
    worst = 0.0
    for i in range(n):
        off = sum((abs(Mp[i, j]) for j in range(n) if j != i), arb(0))
        if not (Mp[i, i] - off > 0):
            return False, f"row {i} of W B W^T not certainly diagonally dominant"
        worst = max(worst, float((off / Mp[i, i]).upper()))
    return True, f"W B W^T certainly strictly diagonally dominant (max off/diag {worst:.3g})"


def lam_min_estimate(W, iters=25):
    """smallest eigenvalue of B ~ 1 / largest eigenvalue of W^T W (B^{-1} ~ W^T W); only for the controls."""
    n = W.nrows()
    Wt = W.transpose()
    x = arb_mat([[arb(1)] for _ in range(n)])
    lam = None
    for _ in range(iters):
        y = Wt * (W * x)
        nrm = sum((y[i, 0] * y[i, 0] for i in range(n)), arb(0)).sqrt().mid()
        lam = sum((x[i, 0] * x[i, 0] for i in range(n)), arb(0)).sqrt().mid() / nrm
        x = arb_mat([[(y[i, 0] / nrm).mid()] for i in range(n)])
    return float(lam)


def main(path, controls=False):
    flint.ctx.prec = PREC
    J = json.load(open(path))
    log(f"read {path}")
    if not (isinstance(J.get("n"), int) and J["n"] >= 3 and J.get("dim") == 5):
        fail("n must be an integer >= 3 and dim must be 5")
    n = J["n"]
    if q(J.get("cut", "0")) != fmpq(1, 2):
        fail("cut must be 1/2")
    e = q(J["e"])
    if not e > 0:
        fail("e must be positive")
    if not (isinstance(J.get("F"), list) and J["F"]):
        fail("F must be a non-empty list of blocks")
    for k, Fk in enumerate(J["F"]):
        if not (isinstance(Fk, list) and Fk and all(isinstance(r, list) and len(r) == len(Fk) for r in Fk)):
            fail(f"F{k} is not a non-empty square matrix")
    if not (isinstance(J.get("SOS"), list) and J["SOS"]):
        fail("SOS must be a non-empty list")
    for r, b in enumerate(J["SOS"]):
        if b.get("g") not in DEG_G:
            fail(f"SOS block {r}: unknown multiplier {b.get('g')!r}")
        Z = b.get("basis")
        if not (isinstance(Z, list) and Z and all(isinstance(z, list) and len(z) == 3 and
                                                   all(isinstance(c, int) and c >= 0 for c in z) for z in Z)):
            fail(f"SOS block {r}: basis must be a non-empty list of exponent triples of non-negative integers")
        if len({tuple(z) for z in Z}) != len(Z):
            fail(f"SOS block {r}: repeated basis monomials")
        B = b.get("B")
        if not (isinstance(B, list) and len(B) == len(Z) and all(isinstance(x, list) and len(x) == len(Z) for x in B)):
            fail(f"SOS block {r}: B must be a square matrix of the basis size")
    F = [fmpq_mat(len(Fk), len(Fk), [q(x) for row in Fk for x in row]) for Fk in J["F"]]
    S = []
    for b in J["SOS"]:
        m = len(b["B"])
        S.append((b["g"], [tuple(z) for z in b["basis"]], fmpq_mat(m, m, [q(x) for row in b["B"] for x in row])))
        b["B"] = None                                                  # free the strings
    del J["SOS"]
    log(f"parsed: n = {n}, e = {e}, F sizes {[Fk.nrows() for Fk in F]}, SOS {[(g, B.nrows()) for g, _, B in S]}")
    # (3)
    print("(3) e > 0; multipliers >= 0 on {GramOK, u,v,t <= 1/2}: 1; 1+x (x >= -1 from x^2 <= 1); 1/2-x (the cut); "
          f"their product; detG (GramOK). Used: {sorted({g for g, _, _ in S})}", flush=True)
    # (1a)
    Lp = lhs_poly(F, n, e)
    log(f"(1a) left side: {len(Lp)} monomials, total degree {max(sum(m) for m in Lp)}")
    Rp = rhs_poly(S)
    log(f"(1a) right side: {len(Rp)} monomials")
    diff = padd(Lp, Rp, -1)
    if diff:
        fail(f"(1a) identity fails: {len(diff)} coefficients differ, e.g. {next(iter(diff.items()))}")
    log("(1a) identity holds exactly as polynomials (every coefficient)")
    # (1b)
    rng = random.Random(7)
    for it in range(3):
        u, v, t = (fmpq(rng.randrange(-10 ** 6, 10 ** 6), 10 ** 6 + rng.randrange(1, 999)) for _ in range(3))
        lhs = -sum((matDot(F[k], Rk(n, F[k].nrows(), k, u, v, t)) for k in range(len(F))), fmpq(0)) - e / comb(n, 2)
        rhs = fmpq(0)
        for g, Z, B in S:
            z = fmpq_mat(len(Z), 1, [u ** a * v ** b * t ** c for (a, b, c) in Z])
            rhs += mult_val(g, u, v, t) * (z.transpose() * B * z)[0, 0]
        pl = peval(Lp, u, v, t)
        if not (lhs == rhs == pl):
            fail(f"(1b) cross-check fails at {(u, v, t)}: matrix lhs == rhs {lhs == rhs}, polynomial == lhs {pl == lhs}")
        log(f"(1b) point {it + 1}: matrix-form left side == z^T B z right side == (1a) polynomial, exactly")
    # (2)
    keep = {}
    for nm, M in [(f"F{k}", Fk) for k, Fk in enumerate(F)] + [(f"B{r}:{g}", B) for r, (g, _, B) in enumerate(S)]:
        if M != M.transpose():
            fail(f"{nm} not symmetric")
        ok, info, Wm = pd_check(M)
        if not ok:
            fail(f"(2) {nm} (size {M.nrows()}): {info}")
        if nm.endswith(":1"):
            keep[nm] = (M, Wm)
        if M.nrows() > 20:
            log(f"(2) {nm} size {M.nrows()}: {info}")
    log("(2) all blocks symmetric and positive definite")
    # (4)
    rng = random.Random(1)
    worst, cnt = -1e300, 0
    while cnt < 300:
        u, v, t = (rng.uniform(-1, 0.5) for _ in range(3))
        if 1 + 2 * u * v * t - u * u - v * v - t * t < 0:
            continue
        cnt += 1
        U, V, T = (fmpq(Fr(x).limit_denominator(10 ** 6).numerator, Fr(x).limit_denominator(10 ** 6).denominator)
                   for x in (u, v, t))
        val = sum((matDot(F[j], Rk(n, F[j].nrows(), j, U, V, T)) for j in range(len(F))), fmpq(0))
        worst = max(worst, float(Fr(int(val.p), int(val.q))))
    bound = -float(Fr(int(e.p), int(e.q))) / comb(n, 2)
    if not worst <= bound * (1 - 1e-9):
        fail(f"(4) float sanity: sampled maximum {worst:.6g} violates the claimed bound {bound:.6g}")
    log(f"(4) float sanity: max of sum_k <F_k, Rk> over {cnt} random region points = {worst:.6g} <= -e/C(n,2) = "
        f"{bound:.6g}")
    print(f"CERTIFICATE OK: no {n}-point configuration on S^4 with all angles >= 60 degrees, so kappa(5) <= {n - 1}",
          flush=True)
    if not controls:
        return
    # negative controls
    log("controls:")
    g0, Z0, B0 = S[0]
    Bp = fmpq_mat(B0)
    Bp[0, 1] = Bp[0, 1] + fmpq(1, 10 ** 30); Bp[1, 0] = Bp[0, 1]
    d = padd(Lp, rhs_poly([(g0, Z0, Bp)] + S[1:]), -1)
    log(f"  one B entry + 1e-30: (1a) {'FAILS (expected) -> OK' if d else 'passes -> CONTROL FAILED'}")
    d = padd(lhs_poly(F, n, e * fmpq(2)), Rp, -1)
    log(f"  e doubled: (1a) {'FAILS (expected) -> OK' if d else 'passes -> CONTROL FAILED'}")
    for nm, (M, Wm) in keep.items():
        lam = lam_min_estimate(Wm)
        lf = Fr(lam)
        lq = fmpq(lf.numerator, lf.denominator)
        log(f"  {nm}: smallest eigenvalue ~ {lam:.6g}")
        for c, want in ((fmpq(101, 100), False), (fmpq(99, 100), True)):
            Mc = fmpq_mat(M)
            for i in range(M.nrows()):
                Mc[i, i] = Mc[i, i] - c * lq
            ok, info, _ = pd_check(Mc)
            log(f"  {nm} - {c} lam I: {'PASS' if ok else 'FAIL'} ({info[:70]}); expected "
                f"{'PASS' if want else 'FAIL'} -> {'OK' if ok == want else 'CONTROL FAILED'}")
            if want:
                continue          # (B - 0.99 lam I is positive definite, but W_B (.) W_B^T need not be dominant)
            ok2, info2 = dd_check(Mc, Wm)
            log(f"  {nm} - {c} lam I with the W of {nm}: {'PASS' if ok2 else 'FAIL'} ({info2[:60]}); expected "
                f"{'PASS' if want else 'FAIL'} -> {'OK' if ok2 == want else 'CONTROL FAILED'}")


if __name__ == "__main__":
    main(sys.argv[1], "--controls" in sys.argv[2:])
