#!/usr/bin/env bash
# Second-kernel check with nanoda (an independent Rust implementation of the Lean 4 type checker), on an export of the two
# theorems made by lean4export from the built ThomsonN7/Solution.lean, plus a negative control on a tampered export.
# Needs: a built workspace (run scripts/check.sh first), git, cargo (Rust), about 8 GB RAM for nanoda and 7 GB for the
# export, 400 MB disk for the export (kept under logs/, which is git-ignored), network for the first clone.
# Usage: bash scripts/second-kernel.sh
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"; cd "$ROOT"
source scripts/tools.sh
need_lean4export; need_nanoda
W="$ROOT/logs/second-kernel"; mkdir -p "$W"
THEOREMS="ThomsonN7.thomson_seven ThomsonN7.thomson_seven_unique"
EXP="$W/thomson_n7.ndjson"
lake build ThomsonN7 >/dev/null
lake env "$LEAN4EXPORT" ThomsonN7.Solution -- $THEOREMS > "$EXP"
wc -lc "$EXP"; python3 -c 'import hashlib,sys;print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest(), sys.argv[1])' "$EXP" | tee "$W/export.sha256"
cfg() {  # $1 = export path, $2 = pp_declars, $3 = print_axioms
  cat <<JSON
{ "export_file_path": "$1", "use_stdin": false,
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"], "unpermitted_axiom_hard_error": true,
  "nat_extension": true, "string_extension": true,
  "pp_declars": $2, "pp_to_stdout": true, "print_axioms": $3, "print_success_message": true }
JSON
}
cfg "$EXP" '["ThomsonN7.thomson_seven","ThomsonN7.thomson_seven_unique"]' true > "$W/config.json"
printf '\n== nanoda on the real export (expect: axioms propext, Quot.sound, Classical.choice; "Checked N declarations with no errors")\n'
"$NANODA_BIN" "$W/config.json" | tee "$W/nanoda-accept.out"
grep -q "with no errors" "$W/nanoda-accept.out" || { echo "SECOND KERNEL DID NOT ACCEPT"; exit 1; }
printf '\n== negative control: one certificate integer of Case1Data.cf changed by +1 (first entry of F0_d, 1809389050761 -> 1809389050762)\n'
[ "$(grep -c '"natVal":"1809389050761"' "$EXP")" = 1 ]      # the literal must occur exactly once in the export
sed 's/"natVal":"1809389050761"/"natVal":"1809389050762"/' "$EXP" > "$W/thomson_n7.tampered.ndjson"
cfg "$W/thomson_n7.tampered.ndjson" '[]' false > "$W/config.tampered.json"
if "$NANODA_BIN" "$W/config.tampered.json" > "$W/nanoda-tampered.out" 2> "$W/nanoda-tampered.err"; then
  echo "NEGATIVE CONTROL FAILED: nanoda accepted the tampered export"; exit 1
else
  echo "negative control ok: nanoda rejected the tampered export"; tail -n 3 "$W/nanoda-tampered.err"
fi
printf '\nSECOND KERNEL: OK (real export accepted, tampered export rejected)\n'
