"""Checkpointed SDPA-GMP run (SDPA-GMP has no checkpoint of its own).
The solve runs in chunks of K iterations (maxIteration = K in the parameter file). Each chunk's output (xVec, xMat,
yMat printed with PREC_DIGITS digits) becomes the next chunk's initial point (-id, dense: x, X, Y in that order).
A restart from an iterate is the same iterate, so only the per-chunk start-up is lost. Stops when a chunk ends
before its K iterations (SDPA's own stopping rule: optimal, infeasible, ...), or after MAXCHUNKS chunks.
While a chunk runs, the solver is paused (SIGSTOP) while the 1-minute load average is above LOADMAX (default 10) and
resumed (SIGCONT) below it.
usage: python3 sdpa_ckpt.py DATA.dat-s WORKDIR K [PRECISION_BITS] [MAXCHUNKS]
Resume: rerun the same command; it continues from the last complete chunk in WORKDIR (done.txt)."""
import os, re, subprocess, sys, time, signal, glob
SDPA = os.environ.get("SDPA_BIN") or "sdpa_gmp"   # the SDPA-GMP binary (SDPA_BIN, or sdpa_gmp on PATH)
LOADMAX = float(os.environ.get("LOADMAX", "10"))
data, wd, K = sys.argv[1], sys.argv[2], int(sys.argv[3])
bits = int(sys.argv[4]) if len(sys.argv) > 4 else 256
maxch = int(sys.argv[5]) if len(sys.argv) > 5 else 1000
digits = max(40, int(bits * 0.30103) + 10)
os.makedirs(wd, exist_ok=True)
def log(s):
    with open(os.path.join(wd, "ckpt.log"), "a") as f: f.write(time.strftime("%F %T ") + s + "\n")
param = os.path.join(wd, "param.sdpa")
fmt = f"%+.{digits}Fe"
with open(param, "w") as f:
    f.write(f"{K}\tunsigned int maxIteration;\n1.0E-30\tdouble 0.0 < epsilonStar;\n1.0E4   double 0.0 < lambdaStar;\n"
            "2.0   \tdouble 1.0 < omegaStar;\n-1.0E5  double lowerBound;\n1.0E5   double upperBound;\n"
            "0.1     double 0.0 <= betaStar <  1.0;\n0.3     double 0.0 <= betaBar  <  1.0, betaStar <= betaBar;\n"
            "0.9     double 0.0 < gammaStar  <  1.0;\n1.0E-30\tdouble 0.0 < epsilonDash;\n"
            f"{bits}     precision\n{fmt}     char*  xPrint\n{fmt}     char*  XPrint\n{fmt}     char*  YPrint\n"
            "%+10.16Fe     char*  infPrint\n")
NUM = re.compile(r"[+-]?\d+\.\d*e[+-]?\d+|[+-]?\d+\.\d*|[+-]?\d+")
def block_struct(path):
    vals = []
    with open(path) as f:
        for line in f:
            if line.startswith(("*", '"')): continue
            vals += re.findall(r"[+-]?\d+", line.replace(",", " ").replace("{", " ").replace("}", " ").replace("(", " ").replace(")", " "))
            if len(vals) >= 2 and len(vals) >= 2 + int(vals[1]): break
    m, nb = int(vals[0]), int(vals[1])
    return m, [int(v) for v in vals[2:2 + nb]]
M, BS = block_struct(data)
def to_init(out, ini):
    """SDPA-GMP's dense initial-point reader takes x (m numbers), then X and Y, each as all SDP blocks of size >= 2 (r*r
    numbers, data order) followed by the LP entries (LP blocks and 1x1 blocks, data order); the output prints the blocks in data order."""
    t = open(out).read()
    a, b, c = t.index("\nxVec ="), t.index("\nxMat ="), t.index("\nyMat =")
    end = t.index("main loop time", c)
    x = NUM.findall(t[a + 7:b])
    def mats(sec):
        v = NUM.findall(sec); k = 0; sdp, lp = [], []
        for r in BS:
            n = r * r if r >= 2 else abs(r)          # SDPA treats a 1x1 SDP block as an LP entry (sdpa_main.cpp)
            (sdp if r >= 2 else lp).append(v[k:k + n]); k += n
        assert k == len(v), (k, len(v))
        return [z for blk in sdp for z in blk] + [z for blk in lp for z in blk]
    assert len(x) == M, (len(x), M)
    X, Y = mats(t[b + 7:c]), mats(t[c + 7:end])
    with open(ini + ".tmp", "w") as f:
        # the reader's "%*[^0-9+-]%Fe" needs at least one separator before every number, the first one included
        for part in (x, X, Y): f.write(" " + " ".join(part) + "\n")
    os.replace(ini + ".tmp", ini)
# Disk: an output is ~100-200 MB at D32, so only two are kept: chunk i writes r{i%2}.out, overwriting chunk i-2's
# output, which is no longer needed; done.txt records the last complete chunk (written only after its output is complete).
DONE = os.path.join(wd, "done.txt")
def outp(i): return os.path.join(wd, f"r{i % 2}.out")
last = int(open(DONE).read()) if os.path.exists(DONE) else -1
i = last + 1
log(f"start/resume at chunk {i} (K={K}, {bits} bits, {digits} digits)")
while i < maxch:
    # do not start a chunk while the machine is busy (other work has priority); wait at the checkpoint instead
    if os.getloadavg()[0] > LOADMAX:
        log(f"wait at checkpoint {i - 1} (load {os.getloadavg()[0]:.1f})")
        while os.getloadavg()[0] > LOADMAX: time.sleep(60)
        log(f"go (load {os.getloadavg()[0]:.1f})")
    out = outp(i); ini = os.path.join(wd, "cur.ini")
    cmd = [SDPA, "-ds", data, "-o", out, "-p", param]
    if i > 0:
        to_init(outp(i - 1), ini); cmd += ["-id", ini]
    with open(os.path.join(wd, f"c{i:03d}.log"), "w") as lf:
        p = subprocess.Popen(cmd, stdout=lf, stderr=subprocess.STDOUT)
        paused = False
        while p.poll() is None:
            l1 = os.getloadavg()[0]
            if not paused and l1 > LOADMAX: p.send_signal(signal.SIGSTOP); paused = True; log(f"pause (load {l1:.1f})")
            elif paused and l1 < LOADMAX: p.send_signal(signal.SIGCONT); paused = False; log(f"resume (load {l1:.1f})")
            time.sleep(15)
    rc = p.returncode
    txt = open(out).read() if os.path.exists(out) else ""
    ph = re.search(r"phase.value\s*=\s*(\S+)", txt); ph = ph.group(1) if ph else "?"
    it = re.search(r"Iteration\s*=\s*(\d+)", txt); it = int(it.group(1)) if it else -1
    pd = re.search(r"objValPrimal\s*=\s*(\S+)", txt); dd = re.search(r"objValDual\s*=\s*(\S+)", txt)
    log(f"chunk {i} rc={rc} phase={ph} iters={it} primal={pd.group(1) if pd else '?'} dual={dd.group(1) if dd else '?'}")
    if rc != 0 or "yMat =" not in txt: log("STOP: chunk failed"); sys.exit(1)
    with open(DONE + ".tmp", "w") as f: f.write(str(i))
    os.replace(DONE + ".tmp", DONE)
    i += 1
    if 0 <= it < K: log(f"FINISHED phase={ph}"); break
