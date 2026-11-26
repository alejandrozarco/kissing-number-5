#!/bin/bash
# Regenerate the certificate modules of κ(5) ≤ 44, Kissing5/Cert44/ (472 files, about 516 MB; not stored in the
# repository), from the exact certificate numerics/kissing5/d32/k64/cert.json (stored xz-compressed), and check them
# against gen/cert44.sha256 (the sha256 of the files that were compiled for verification44/).
#   pack: integer data and the LDLᵀ + remainder packing of the 22 blocks (gen/gen_t5.py; Λ = Λ0·2^72, S = 72, and
#         the cached λ_min estimates in numerics/kissing5/d32/t5/lam.json, which fix the shifts); about 15 min
#   emit: the Lean modules, with an exact simulation of every kernel check; about 6 min
# Needs python3 with gmpy2 and numpy, and xz. Peak memory about 1.5 GB.
# Usage: ./regen44.sh   (from lean/; WORK=<dir> sets the scratch directory, default .cert44work)
set -euo pipefail
cd "$(dirname "$0")"
C=../numerics/kissing5/d32/k64/cert.json
CERT_SHA=69d25a7c94fe16e116580b45f2b91e0a3bebed93a7f91f315a3c2a2317eb167d
if command -v sha256sum >/dev/null; then sha() { sha256sum "$@"; }; else sha() { shasum -a 256 "$@"; }; fi
[ -f $C ] || xz -dk $C.xz
[ "$(sha $C | cut -d' ' -f1)" = $CERT_SHA ] || { echo "unexpected $C" >&2; exit 1; }
W=${WORK:-.cert44work}
[ -e "$W" ] && { echo "$W exists; remove it or set WORK" >&2; exit 1; }
mkdir -p "$W"
cp ../numerics/kissing5/d32/t5/lam.json "$W/lam.json"
S=72 python3 gen/gen_t5.py pack $C "$W"
python3 gen/gen_t5.py emit "$W" Kissing5
cmp -s "$W/lam.json" ../numerics/kissing5/d32/t5/lam.json || { echo "lam.json changed: a shift was recomputed" >&2; exit 1; }
sha -c gen/cert44.sha256 > "$W/check.out" || { grep -v ': OK$' "$W/check.out" | head; echo "regen44: files differ" >&2; exit 1; }
echo "regen44 OK ($(wc -l < gen/cert44.sha256 | tr -d " ") files)"
