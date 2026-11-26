"""High-precision block diagnostics of an SDPA-GMP solution (yMat): smallest eigenvalue of every block.

usage: python3 hp_blocks.py PROBLEM.dat-s RESULT.out [PBITS]
Parses the printed decimals exactly, converts to fixed point (scale 2^PBITS, default 320), and per block computes an
LDL^T factorisation in fixed-point integer arithmetic (pivots) and the smallest eigenvalue by inverse iteration with
the factors.  Floats are used only for printing."""
import sys, json, math, re
from fractions import Fraction
import numpy as np

def parse_ymat(path):
    txt = open(path).read()
    body = txt[txt.find("yMat ="):]
    s = body[body.find("{"):]
    stack = []; buf = []; out = None
    for ch in s:
        if ch == "{":
            stack.append([]); buf = []
        elif ch == "}" or ch == ",":
            t = "".join(buf).strip(); buf = []
            if t: stack[-1].append(t)
            if ch == "}":
                top = stack.pop()
                if not stack: out = top; break
                stack[-1].append(top)
        else:
            buf.append(ch)
    return out

def fx(tok, P):                       # decimal string -> round(x * 2^P)
    f = Fraction(tok.replace("+", "") if tok.startswith("+") else tok)
    return round(f * (1 << P))

def ldl_fixed(A, P):
    """A: n x n numpy object array of ints (fixed point 2^P). Returns (L unit lower, d) in fixed point."""
    n = A.shape[0]; A = A.copy(); L = np.zeros((n, n), dtype=object); d = [0] * n
    one = 1 << P
    for k in range(n):
        dk = A[k, k]; d[k] = dk
        L[k, k] = one
        if dk <= 0:
            return L, d, k
        col = A[k + 1:, k]
        l = np.array([(c * one) // dk for c in col], dtype=object)    # L[i,k] = A[i,k]/d_k
        L[k + 1:, k] = l
        # A[i,j] -= L[i,k] * A[j,k]   (A[j,k] = L[j,k] d_k)
        A[k + 1:, k + 1:] -= np.outer(l, col) // one
    return L, d, None

def lam_min(L, d, P, iters=30):
    """smallest eigenvalue of L D L^T by inverse iteration (fixed point); float result."""
    n = len(d); one = 1 << P
    x = [one] * n
    lam = None
    for _ in range(iters):
        # solve L y = x, z = y / d, solve L^T w = z
        y = [0] * n
        for i in range(n):
            s = x[i]
            row = L[i, :i]
            if i: s -= int(np.dot(row, np.array(y[:i], dtype=object))) // one
            y[i] = s
        z = [(y[i] * one) // d[i] for i in range(n)]
        w = [0] * n
        for i in range(n - 1, -1, -1):
            s = z[i]
            if i < n - 1: s -= int(np.dot(L[i + 1:, i], np.array(w[i + 1:], dtype=object))) // one
            w[i] = s
        nw = math.isqrt(sum(v * v for v in w)); nx = math.isqrt(sum(v * v for v in x))
        lam = nx / nw                                   # Rayleigh-like ratio |x| / |A^{-1} x|
        x = [(v * one) // nw for v in w]
    return lam

def main(dats, res, P=320):
    meta = json.load(open(dats + ".meta.json"))
    Y = parse_ymat(res)
    out = {}
    for (nm, sz), blk in zip(meta["blocks"], Y):
        if sz < 0 or not isinstance(blk[0], list):
            vals = [float(Fraction(t)) for t in (blk if not isinstance(blk[0], list) else blk[0])]
            print(f"{nm:10s} LP {vals}", flush=True); out[nm] = dict(lp=vals); continue
        n = len(blk)
        A = np.array([[fx(t, P) for t in row] for row in blk], dtype=object)
        A = (A + A.T) // 2
        L, d, bad = ldl_fixed(A, P)
        if bad is not None:
            print(f"{nm:10s} n={n}: NOT positive definite in fixed point at pivot {bad} (value {d[bad] / 2**P:.3e})",
                  flush=True); out[nm] = dict(n=n, bad=bad); continue
        dmin = min(d) / 2 ** P; dmax = max(d) / 2 ** P
        lm = lam_min(L, d, P)
        diag = [A[i, i] / 2 ** P for i in range(n)]
        print(f"{nm:10s} n={n:4d} pivots[min,max]=[{dmin:.3e},{dmax:.3e}] lam_min={lm:.3e} "
              f"diag_max={max(diag):.3e}", flush=True)
        out[nm] = dict(n=n, dmin=dmin, dmax=dmax, lam_min=lm, diag_max=max(diag))
    json.dump(out, open(res + ".hp.json", "w"), indent=1)

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 320)
