#!/usr/bin/env bash
# Clean build test: compile every module of the package one at a time, in dependency order, single-threaded, and
# record wall time and peak RSS per module. Run from a fresh checkout after `lake exe cache get` (and ./regen.sh where
# the package has one).
# Usage: bash scripts/build_test.sh [out.tsv] [roots]  (default: build_test.tsv; roots: the statement, proof and
# axiom check of the lowest dimension present, e.g. "Kissing5.Statement Kissing5.Solution Kissing5.Axioms")
# Needs GNU time (/usr/bin/time) and python3. Optional: BT_WRAP, a command prefix for each module's compile (for
# example a lock on a shared machine).
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"; cd "$ROOT"
OUT="${1:-build_test.tsv}"
if [ -d Kissing ]; then D=Kissing; elif [ -d Kissing4 ]; then D=Kissing4; else D=Kissing8; fi
export BT_ROOTS="${2:-$D.Statement $D.Solution $D.Axioms}"
ORDER=$(python3 - <<'PY'
import os, re
mods = {}
for top in ("Kissing", "Kissing4", "Kissing5", "Kissing8", "ThomsonGen"):
    for d, _, fs in os.walk(top):
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(d, f); m = p[:-5].replace(os.sep, ".")
                mods[m] = [x for x in re.findall(r"^import\s+(\S+)", open(p, encoding="utf-8").read(), re.M)]
roots = os.environ["BT_ROOTS"].split()
seen, order = set(), []
def visit(m):
    if m in seen or m not in mods: return
    seen.add(m)
    for x in mods[m]: visit(x)
    order.append(m)
for r in roots: visit(r)
print("\n".join(order))
PY
)
printf "module\twall_s\tpeak_rss_kB\texit\n" > "$OUT"
for M in $ORDER; do
  F="${M//.//}.lean"; B=".lake/build/lib/lean/${M//.//}"; mkdir -p "$(dirname "$B")"
  set +e
  ${BT_WRAP:-} /usr/bin/time -f "%e %M" -o .bt.time lake env lean -j1 -DElab.async=false -o "$B.olean" -i "$B.ilean" "$F" \
    > ".bt.$M.out" 2>&1
  RC=$?
  set -e
  read W R < .bt.time
  printf "%s\t%s\t%s\t%s\n" "$M" "$W" "$R" "$RC" >> "$OUT"
  echo "$M wall=${W}s peak=${R}kB rc=$RC"
  grep -E "^[^ ]+:[0-9]+:[0-9]+: error" ".bt.$M.out" && { echo "STOP: errors in $M"; exit 1; }
  [ "$RC" = 0 ] || { echo "STOP: $M exited $RC"; exit 1; }
done
AX=$(echo "$BT_ROOTS" | tr " " "\n" | grep Axioms | tr . /).lean
lake env lean -j1 -DElab.async=false "$AX" > axioms.out 2>&1
# Every `#print axioms` of the axiom file must report a subset of the standard three axioms.
python3 - "$AX" axioms.out <<'PY' || { echo "STOP: axiom check failed (axioms.out)"; exit 1; }
import re, sys
want = len(re.findall(r"^#print axioms", open(sys.argv[1], encoding="utf-8").read(), re.M))
got = re.findall(r"depends on axioms: \[(.*)\]", open(sys.argv[2], encoding="utf-8").read())
ok = {"propext", "Classical.choice", "Quot.sound"}
bad = [g for g in got if not {a.strip() for a in g.split(",") if a.strip()} <= ok]
print(f"axioms: {len(got)} of {want} theorems reported, {len(bad)} outside {sorted(ok)}")
sys.exit(0 if want > 0 and len(got) == want and not bad else 1)
PY
echo "BUILD TEST OK"
