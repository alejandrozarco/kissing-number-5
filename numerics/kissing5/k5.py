"""Kissing number in dimension 5: three-point SDP feasibility probe (floating point), reusing ../kissing3/k3.py.

Changes from dimension 4 (Bachoc-Vallentin, kernels for S^4):
  * Q_k(u,v,t) = ((1-u^2)(1-v^2))^{k/2} P_k((t-uv)/sqrt((1-u^2)(1-v^2))) with P_k = U_k/(k+1), the Gegenbauer
    polynomials of the tangent sphere S^3 (normalised to 1 at 1):
    (k+2) Q_{k+1} = 2 (k+1) w Q_k - k g Q_{k-1},  w = t - uv, g = (1-u^2)(1-v^2);
  * the two-point (Delsarte) part uses the Gegenbauer polynomials of S^4, C_j^{3/2}(x)/C_j^{3/2}(1);
  * the region is unchanged: Gram triples of three unit vectors (any dimension >= 3) with u, v, t <= 1/2.
usage: python3 k5.py test | bv D [D2] | fixn D N | mu D N FRAC | check TAG      (outputs in this directory)
"""
import os, sys, math, json, itertools
HERE = os.path.dirname(os.path.abspath(__file__))
K3 = os.path.join(os.path.dirname(HERE), "kissing3")
if len(sys.argv) > 2 and sys.argv[1] != "check":
    os.environ["POLYD"] = sys.argv[2]
sys.path.insert(0, K3)
import numpy as np
import polyk
from polyk import ONE, U, V, T, pmul, peval, SYM_AVG


def Qk5(kmax):
    w = T - pmul(U, V)
    g = pmul(ONE - pmul(U, U), ONE - pmul(V, V))
    Q = [ONE.copy(), w.copy()]
    k = 1
    while len(Q) <= kmax:
        Q.append((2 * (k + 1) * pmul(w, Q[-1]) - k * pmul(g, Q[-2])) / (k + 2))
        k += 1
    return Q


polyk.Qk = Qk5
import k3                                  # noqa: E402  (uses polyk.Yk_columns -> polyk.Qk, now patched)
k3.HERE = HERE


def geg2mono(d2):
    """columns: monomial coefficients (length D+1) of C_j^{3/2}(x)/C_j^{3/2}(1), j = 0..d2."""
    D = polyk.D
    lam = 1.5
    M = np.zeros((D + 1, d2 + 1))
    C = [np.array([1.0]), np.array([0.0, 2 * lam])]
    while len(C) <= d2:
        j = len(C) - 1
        a = np.concatenate([[0.0], 2 * (j + lam) * C[-1]]); b = np.concatenate([(j + 2 * lam - 1) * C[-2], [0.0, 0.0]])
        C.append((a - b) / (j + 1))
    for j in range(d2 + 1):
        M[:len(C[j]), j] = C[j] / ((j + 1) * (j + 2) / 2)
    return M


k3.leg2mono = geg2mono

if os.environ.get("SYM") == "1":           # S3-reduced SOS certificate (sym.py); tags get the suffix _sym
    import sym                             # noqa: E402
    k3.Prob.tri_nonneg = sym.sym_tri_nonneg
    _record = k3.record

    def _record_sym(res, xs=None):
        mt = os.environ.get("MULTS")
        res = dict(res, tag=res["tag"] + "_sym" + (f"_m{mt.replace(',', '+')}" if mt else ""),
                   sym_blocks=sym.block_sizes(), mults=mt or "all")
        return _record(res, xs)
    k3.record = _record_sym

if os.environ.get("SOLVER", "CLARABEL") == "SCS":   # first-order, low memory (Clarabel's dense PSD blocks grow ~n^4)
    import time as _time
    import cvxpy as _cp

    def _solve_scs(pr, obj, sense="max"):
        prob = _cp.Problem(_cp.Maximize(obj) if sense == "max" else _cp.Minimize(obj), pr.cons)
        t0 = _time.time()
        eps = float(os.environ.get("SCS_EPS", "1e-7"))
        prob.solve(solver="SCS", verbose=bool(int(os.environ.get("VERB", "0"))), eps_abs=eps, eps_rel=eps,
                   max_iters=int(os.environ.get("SCS_ITERS", "200000")), acceleration_lookback=10)
        return prob, _time.time() - t0
    k3.solve = _solve_scs
    _record2 = k3.record

    def _record_scs(res, xs=None):
        return _record2(dict(res, tag=res["tag"] + "_scs", solver="SCS"), xs)
    k3.record = _record_scs


def q_rec5(k, u, v, t):
    w, g = t - u * v, (1 - u * u) * (1 - v * v)
    q0, q1 = 1.0, w
    if k == 0:
        return q0
    for j in range(1, k):
        q0, q1 = q1, (2 * (j + 1) * w * q1 - j * g * q0) / (j + 2)
    return q1


def test():
    rng = np.random.default_rng(1)
    D = polyk.D
    sizes = [D // 2 + 1 - k for k in range(D // 2 + 1)]
    # 1. Q_k from polyk equals the closed form with U_k/(k+1); the Delsarte columns equal C_j^{3/2}/C_j^{3/2}(1)
    from scipy.special import eval_chebyu, eval_gegenbauer
    worst = 0.0
    Q = Qk5(D // 2)
    for _ in range(50):
        u, v, t = rng.uniform(-0.95, 0.95, 3)
        g = (1 - u * u) * (1 - v * v)
        for k in range(D // 2 + 1):
            ref = g ** (k / 2) * eval_chebyu(k, (t - u * v) / math.sqrt(g)) / (k + 1)
            worst = max(worst, abs(peval(Q[k], u, v, t)[0] - ref), abs(q_rec5(k, u, v, t) - ref))
    print("Q_k vs U_k/(k+1) closed form: max err", worst)
    M = geg2mono(D)
    xs = np.linspace(-1, 1, 41)
    werr = max(abs(np.polyval(M[::-1, j], x) - eval_gegenbauer(j, 1.5, x) / eval_gegenbauer(j, 1.5, 1.0))
               for j in range(D + 1) for x in xs)
    print("Delsarte columns vs C_j^{3/2}: max err", werr)
    # 2. BV positivity on S^4 and the dsum identity, random configurations of 45 points in R^5
    for trial in range(3):
        n = 45
        X = rng.normal(size=(n, 5)); X /= np.linalg.norm(X, axis=1)[:, None]
        G = X @ X.T; np.fill_diagonal(G, 1.0)
        I, J, K = (a.ravel() for a in np.meshgrid(range(n), range(n), range(n), indexing="ij"))
        mins = []
        for k, m in enumerate(sizes):
            cols = np.asarray(SYM_AVG @ polyk.Yk_columns(k, m))
            M = np.zeros((m, m))
            for c in range(m * m):
                M.flat[c] = peval(cols[:, c], G[I, J], G[I, K], G[J, K]).sum()
            mins.append(np.linalg.eigvalsh((M + M.T) / 2)[0] / max(1.0, abs(M).max()))
        print(f"BV positivity, trial {trial}: min relative eigenvalue of sum_ijl S_k over k:", min(mins))
    s = np.zeros(polyk.N3)
    for k, m in enumerate(sizes):
        A = rng.normal(size=(m, m)); F = A @ A.T / m
        s += np.asarray(SYM_AVG @ polyk.Yk_columns(k, m)) @ F.ravel()
    sub = k3.sub_np
    R = (n - 2) * s + sub(s, (0, 0, 1.0)) + sub(s, (1, 1, 1.0)) + sub(s, (2, 2, 1.0)) + sub(s, (1.0, 1.0, 1.0)) / (n - 1)
    dist = (I != J) & (I != K) & (J != K)
    lhs = peval(R, G[I, J], G[I, K], G[J, K])[dist].sum()
    Sall = peval(s, G[I, J], G[I, K], G[J, K]).sum()
    print("dsum identity rel err", abs(lhs - (n - 2) * Sall) / abs(Sall))
    # 3. the D5 root system: 40 points, max off-diagonal inner product 1/2
    P = [v for v in itertools.product((-1, 0, 1), repeat=5) if sum(abs(x) for x in v) == 2]
    P = np.array(P, float) / math.sqrt(2)
    Gc = P @ P.T
    print("D5 roots: points", len(P), " max off-diagonal inner product", Gc[~np.eye(len(P), dtype=bool)].max())


def check(tag):
    """float check of a fixn/mu solution: max of R over the region by dense sampling; eigenvalues."""
    Z = np.load(os.path.join(HERE, "sol", tag + ".npz"), allow_pickle=True)
    meta = json.loads(str(Z["meta"]))
    D, n = meta["D"], meta["n"]
    os.environ["POLYD"] = str(D)
    assert polyk.D == D, "run check with the same POLYD: python3 k5.py check TAG (sets it from the tag)"
    mu = float(meta.get("mu", 0.0))
    sizes = [D // 2 + 1 - k for k in range(D // 2 + 1)]
    s = np.zeros(polyk.N3)
    mine = []
    for k, m in enumerate(sizes):
        F = Z[f"F{k}"] + mu * np.eye(m)
        mine.append(np.linalg.eigvalsh(F)[0])
        s += np.asarray(SYM_AVG @ polyk.Yk_columns(k, m)) @ F.ravel()
    sub = k3.sub_np
    R = (n - 2) * s + sub(s, (0, 0, 1.0)) + sub(s, (1, 1, 1.0)) + sub(s, (2, 2, 1.0)) + sub(s, (1.0, 1.0, 1.0)) / (n - 1)
    rng = np.random.default_rng(0)
    pts = rng.uniform(-1, 0.5, size=(3_000_000, 3))
    g = pts[:, 0] ** 2 + pts[:, 1] ** 2 + pts[:, 2] ** 2
    ok = 1 + 2 * pts[:, 0] * pts[:, 1] * pts[:, 2] - g >= 0
    pts = pts[ok]
    grid = np.linspace(-1, 0.5, 61)
    gp = np.array([(a, b, c) for a in grid for b in grid for c in grid])
    gp = gp[1 + 2 * gp[:, 0] * gp[:, 1] * gp[:, 2] - (gp ** 2).sum(1) >= -1e-12]
    allp = np.vstack([pts, gp])
    vals = peval(R, allp[:, 0], allp[:, 1], allp[:, 2])
    i = int(np.argmax(vals))
    C = n * (n - 1) / 2
    out = dict(tag=tag, n=n, D=D, e=meta["e"], claimed_maxR=-meta["e"] / C, sampled_maxR=float(vals[i]),
               argmax=[round(float(x), 6) for x in allp[i]], n_samples=int(len(allp)), F_mineig=float(min(mine)),
               OK=bool(vals[i] < 0 and min(mine) > 0))
    print(json.dumps(out))
    with open(os.path.join(HERE, "checks.jsonl"), "a") as fh:
        fh.write(json.dumps(out) + "\n")


def tag_suffix():
    """suffix that the record wrappers (SYM, MULTS, SOLVER) append to k3's tags."""
    sfx = ""
    if os.environ.get("SOLVER", "CLARABEL") == "SCS":
        sfx += "_scs"
    if os.environ.get("SYM") == "1":
        mt = os.environ.get("MULTS")
        sfx += "_sym" + (f"_m{mt.replace(',', '+')}" if mt else "")
    return sfx


def run_mu5(nu, frac, d2):
    """k3.run_mu, but finding the fixn run under the suffixed tag (SYM/MULTS/SOLVER)."""
    D = polyk.D
    tag0 = f"fixn_D{D}_n{nu:g}" + ("" if d2 is None else f"_del{d2}") + ("_noq" if os.environ.get("NOQ") == "1" else "")
    emax = None
    for line in open(os.path.join(HERE, "results.jsonl")):
        r = json.loads(line)
        if r["tag"] == tag0 + tag_suffix() and r["status"].startswith("optimal"):
            emax = r["e"]
    assert emax is not None and emax > 0, "run fixn first"
    pr = k3.Prob(use_mu=True)
    e = k3.build_fixn(pr, nu, d2)
    pr.cons += [e == frac * emax, pr.mu <= 1]
    prob, dt = k3.solve(pr, pr.mu, "max")
    xs = pr.xs(); mu = float(pr.mu.value)
    mineig = min(float(np.linalg.eigvalsh(xs[k] + mu * np.eye(xs[k].shape[0]))[0]) for k in pr.psdnames)
    nblk = {k: xs[k].shape[0] for k in pr.psdnames}
    xs["mu"] = np.array(mu)
    k3.record(dict(tag=tag0 + f"_mu{frac:g}", mode="mu", D=D, n=nu, delsarte=d2, frac=frac, e=frac * emax,
                   status=prob.status, mu=mu, mineig=mineig, time=round(dt, 1), blocks=nblk), xs)


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "test":
        test()
    elif mode == "bv":
        k3.run_bv(int(sys.argv[3]) if len(sys.argv) > 3 else polyk.D)
    elif mode == "fixn":
        dl = os.environ.get("DEL")
        k3.run_fixn(float(sys.argv[3]), None if dl is None else int(dl))
    elif mode == "mu":
        dl = os.environ.get("DEL")
        run_mu5(float(sys.argv[3]), float(sys.argv[4]), None if dl is None else int(dl))
    elif mode == "check":
        check(sys.argv[2])
