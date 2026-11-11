#!/usr/bin/env bash
# Second-kernel check: export the theorems named in a Comparator config with lean4export and check the export with
# nanoda (an independent implementation of the Lean 4 type checker, in Rust). Negative control: a copy of the export in
# which one large natural-number literal is changed to a value that does not occur anywhere in the export must be
# rejected. Adapted from scripts/second-kernel.sh of alejandrozarco/thomson-n7-log.
# Needs a built workspace (lake build <solution module>), python3, and, unless NANODA_BIN / COMPARATOR_LEAN4EXPORT are
# set, git, cargo and network for the first clone. Output: $OUT (default logs/second-kernel/<config name>/).
# Usage: bash scripts/second-kernel.sh comparator5.json   (NEG_ONLY=1: only the negative control, on an accepted export)
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="${ROOT:-$(cd "$HERE/.." && pwd)}"; cd "$ROOT"
source "$HERE/tools.sh"
CFG="$1"
[ -n "${COMPARATOR_LEAN4EXPORT:-}" ] || need_lean4export
[ -n "${NANODA_BIN:-}" ] || need_nanoda
NAME="$(basename "$CFG" .json)"
W="${OUT:-$ROOT/logs/second-kernel/$NAME}"; mkdir -p "$W"
read -r MOD THMS_JSON AX_JSON < <(python3 -c 'import json,sys;c=json.load(open(sys.argv[1]))
print(c["solution_module"], json.dumps(c["theorem_names"],separators=(",",":")), json.dumps(c["permitted_axioms"],separators=(",",":")))' "$CFG")
[ -n "${MOD:-}" ] || { echo "could not read $CFG"; exit 1; }
THMS=$(python3 -c 'import json,sys;print(" ".join(json.loads(sys.argv[1])))' "$THMS_JSON")
EXP="$W/export.ndjson"
sha() { python3 -c 'import hashlib,sys;print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest(), sys.argv[1].split("/")[-1])' "$1"; }
cfg() {  # $1 = export path, $2 = pp_declars, $3 = print_axioms
  cat <<JSON
{ "export_file_path": "$1", "use_stdin": false,
  "permitted_axioms": $AX_JSON, "unpermitted_axiom_hard_error": true,
  "nat_extension": true, "string_extension": true,
  "pp_declars": $2, "pp_to_stdout": true, "print_axioms": $3, "print_success_message": true }
JSON
}
if [ -z "${NEG_ONLY:-}" ]; then
echo "== lean4export $MOD -- $THMS"
lake env "$COMPARATOR_LEAN4EXPORT" "$MOD" -- $THMS > "$EXP"
wc -lc "$EXP"; sha "$EXP" | tee "$W/export.sha256"
cfg "$EXP" "$THMS_JSON" true > "$W/config.json"
printf '\n== nanoda on the export (expected: only the permitted axioms %s; "Checked N declarations with no errors")\n' "$AX_JSON"
"$NANODA_BIN" "$W/config.json" | tee "$W/nanoda-accept.out"
grep -q "with no errors" "$W/nanoda-accept.out" || { echo "SECOND KERNEL DID NOT ACCEPT"; exit 1; }
else  # NEG_ONLY=1: rerun only the negative control on the export already accepted in $W (same sha256 required)
  [ "$(sha "$EXP")" = "$(cat "$W/export.sha256")" ] && grep -q "with no errors" "$W/nanoda-accept.out" \
    || { echo "NEG_ONLY: no accepted export with a matching sha256 in $W"; exit 1; }
  echo "== NEG_ONLY: export $(cat "$W/export.sha256") was accepted earlier ($(grep "with no errors" "$W/nanoda-accept.out"))"
fi
# Negative control (see tamper_literal.py): one literal changed to a value that occurs nowhere in the export.
python3 "$HERE/tamper_literal.py" "$EXP" "$W/export.tampered.ndjson"
cfg "$W/export.tampered.ndjson" '[]' false > "$W/config.tampered.json"
if "$NANODA_BIN" "$W/config.tampered.json" > "$W/nanoda-tampered.out" 2> "$W/nanoda-tampered.err"; then
  echo "NEGATIVE CONTROL FAILED: nanoda accepted the tampered export"; exit 1
else
  echo "negative control ok: nanoda rejected the tampered export"; tail -n 3 "$W/nanoda-tampered.err"
fi
printf '\nSECOND KERNEL: OK (export accepted, tampered export rejected)\n'
