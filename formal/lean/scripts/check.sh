#!/usr/bin/env bash
# One-command check of the Thomson N=7 proof against plain Mathlib (no Physlib; Comparator and the second kernel are separate scripts).
# Needs: elan (Lean toolchain manager), git, python3, network for the first run (Mathlib + its cache),
# about 14 GB RAM and 10 GB disk. Takes about 10 to 25 minutes, almost all of it building ThomsonN7/Solution.lean.
# Usage: bash scripts/check.sh                (run from anywhere)
#        SKIP_BUILD=1 bash scripts/check.sh   (only the checks that need no build: hashes, preamble, token scan, claims)
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
LOGS="$ROOT/logs"; mkdir -p "$LOGS"
CHAL=ComparatorChallenges/ThomsonN7.lean
SOL=ThomsonN7/Solution.lean
step() { printf '\n== %s\n' "$*"; }
sha() { python3 -c 'import hashlib,sys;print(hashlib.sha256(open(sys.argv[1],"rb").read()).hexdigest())' "$1"; }

step "1. file identity (must match SHA256SUMS.txt)"
[ "$(sha $CHAL)" = "2cf12e8ca6bd6ebfb31ae7343ca87ed75a3ba37cbe3d6eb5abbfae483dafbaae" ] || { echo "$CHAL HASH MISMATCH"; exit 1; }
[ "$(sha $SOL)"  = "6545e982abaeb4cae0a906c74ca51cc502621aa2a05783bb8da35d96493cc9ce" ] || { echo "$SOL HASH MISMATCH"; exit 1; }
echo "both hashes ok"

step "2. statement preamble: $SOL lines 1-310 are byte-identical to $CHAL lines 1-310"
diff <(sed -n 1,310p $SOL) <(sed -n 1,310p $CHAL) && echo "identical"

step "3. token scan of $SOL (expect no output between the markers)"
echo "-- begin"
grep -nE 'sorry|native_decide|ofReduceBool|ofReduceNat|trustCompiler|^\s*(private |protected |noncomputable )*(axiom|opaque|unsafe|partial) |set_option|implemented_by|@\[extern|csimp|^\s*(macro|syntax|elab|notation|infix|prefix|postfix|open Lean|initialize|run_cmd)|#eval|#exit' $SOL || true
echo "-- end"
echo "decide +kernel occurrences: $(grep -o 'decide +kernel' $SOL | wc -l) (70 tactic uses + 1 docstring mention; each closes a Lean-proved soundness lemma's boolean check)"

step "3b. claims.tsv: every line number cited by the paper still declares its name"
python3 scripts/check_claims.py

if [ "${SKIP_BUILD:-0}" = "1" ]; then echo; echo "SKIP_BUILD=1: stopping before the build."; exit 0; fi

step "4. toolchain and Mathlib (pinned by lean-toolchain, lakefile.toml, lake-manifest.json)"
cat lean-toolchain
lake exe cache get || echo "cache get failed: continuing, Mathlib will compile from source (hours)"

step "5. lake build (the challenge has 3 expected 'declaration uses sorry' warnings; the solution must have none)"
/usr/bin/time -p lake build ThomsonN7 ComparatorChallenges 2>&1 | tee "$LOGS/build.log" | tail -25
echo "sorry warnings in $CHAL: $(grep -c "$CHAL.*sorry" "$LOGS/build.log" || true) (expect 3)"
echo "sorry warnings in $SOL:  $(grep -c "$SOL.*sorry" "$LOGS/build.log" || true) (expect 0)"

step "6. axioms of the two theorems (expect propext, Classical.choice, Quot.sound only)"
lake env lean scripts/CheckAxioms.lean | tee "$LOGS/axioms.log"
if grep -E 'sorryAx|ofReduceBool|ofReduceNat|trustCompiler' "$LOGS/axioms.log"; then echo "FORBIDDEN AXIOM"; exit 1; fi

step "7. statement fidelity: every challenge constant has the same type (and value, for definitions) in the solution"
dump() {  # $1 = module, $2 = tag
  { printf 'import %s\n' "$1"; sed -e "s/DUMPMOD/$1/g" -e "s#OUTFILE#$LOGS/$2.tsv#" scripts/DumpBody.lean; } > "$LOGS/Dump$2.lean"
  lake env lean "$LOGS/Dump$2.lean"
}
dump ComparatorChallenges.ThomsonN7 Challenge
cut -f1 "$LOGS/Challenge.tsv" > "$LOGS/Challenge.names"
DUMP_ONLY="$LOGS/Challenge.names" dump ThomsonN7.Solution Solution
python3 scripts/compare_statements.py "$LOGS/Challenge.tsv" "$LOGS/Solution.tsv" | tee "$LOGS/statement.log"

step "DONE: all checks above passed (a failing step stops the script)"
