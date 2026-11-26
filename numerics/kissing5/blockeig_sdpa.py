import sys, json, numpy as np
sys.path.insert(0, ".")
import sdpa5
meta = json.load(open(sys.argv[1] + ".meta.json"))
res = sdpa5.read_result(sys.argv[2]); ym = res.pop("yMat")
for (nm, sz), blk in zip(meta["blocks"], ym):
    M = np.array(blk, dtype=float)
    if M.ndim != 2: print(nm, "LP", M.ravel()[:3]); continue
    d = np.sqrt(np.abs(np.diag(M))); d[d == 0] = 1
    Ms = M / d[:, None] / d[None, :]
    ev = np.linalg.eigvalsh(M); evs = np.linalg.eigvalsh(Ms)
    print(f"{nm:14s} n={M.shape[0]:4d} maxabs={np.abs(M).max():.2e} diag[min,max]=[{np.diag(M).min():.2e},{np.diag(M).max():.2e}] "
          f"eig[min,max]=[{ev[0]:.2e},{ev[-1]:.2e}] scaled_min={evs[0]:.2e} cond~{ev[-1]/max(ev[0],1e-300):.1e}", flush=True)
