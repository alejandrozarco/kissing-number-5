"""Unit tests for sym.py (run: POLYD=D python3 symtest.py): bases and symmetry of the reduced columns."""
import itertools, os, sys
import numpy as np
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "kissing3"))
import polyk
import sym
from polyk import D, N3, EXPS, ONE, U, PERM_M, sos_columns

worst = 0.0
for d in range(0, D // 2 + 1):
    Z, B = sym.iso_bases(d)
    n = len(Z)
    allB = np.hstack([B["triv"], B["sign"], B["std1"], B["std2"]])
    assert allB.shape[1] == n, (d, allB.shape, n)
    worst = max(worst, np.abs(allB.T @ allB - np.eye(n)).max())
    Z, S = sym.stab_bases(d)
    allS = np.hstack([S["even"], S["odd"]])
    assert allS.shape[1] == n
    worst = max(worst, np.abs(allS.T @ allS - np.eye(n)).max())
print("orthonormal and complete bases up to d =", D // 2, ": max err", worst)
print("reduced block sizes at D =", D, sym.block_sizes())

# symmetry: for a random PSD Q_std, the std contribution g * (f^T Q f + f'^T Q f') is S3-invariant
rng = np.random.default_rng(0)
allrows = np.where(EXPS.sum(1) <= D)[0]
d = D // 2
_, B = sym.iso_bases(d)
for part, cols in [("triv", [B["triv"]]), ("sign", [B["sign"]]), ("std", [B["std1"], B["std2"]])]:
    r = cols[0].shape[1]
    A = sum(sym.reduced_columns(ONE, d, N, allrows) for N in cols)
    X = rng.normal(size=(r, r)); Q = X @ X.T
    p = np.zeros(N3); p[allrows] = A @ Q.ravel()
    asym = max(np.abs(PERM_M[o] @ p - p).max() for o in itertools.permutations(range(3)))
    # the same polynomial from the unreduced Gram N Q N^T
    Qf = sum(N @ Q @ N.T for N in cols)
    Mg, n = sos_columns(ONE, d)
    pf = Mg @ Qf.ravel()
    print(f"{part}: r = {r}, asymmetry {asym:.2e}, vs unreduced {np.abs(pf - p).max():.2e}")
