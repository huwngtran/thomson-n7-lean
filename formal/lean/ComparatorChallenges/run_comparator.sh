#!/usr/bin/env bash
# Run leanprover/comparator on this repo: it checks that ThomsonN7.thomson_seven and ThomsonN7.thomson_seven_unique in
# ThomsonN7/Solution.lean have the same statements as the sorry'd ones in ComparatorChallenges/ThomsonN7.lean, use only
# propext / Quot.sound / Classical.choice, and are accepted by the Lean kernel (replayed from a lean4export dump).
#
# Needs what scripts/check.sh needs, plus git and about 15 GB RAM. Takes about 15 minutes after the tools are built.
# Comparator runs the solution under `landrun` (Linux Landlock). If `landrun` is not on PATH, this script uses Comparator's
# own scripts/fake-landrun.sh; set COMPARATOR_LANDRUN to point at a landrun binary to use it instead.
# Usage: bash ComparatorChallenges/run_comparator.sh
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"; cd "$ROOT"
source scripts/tools.sh
export LAKE_ARTIFACT_CACHE=false      # do not let Lake substitute cached artifacts for the modules being checked
need_lean4export; need_comparator
export COMPARATOR_BIN COMPARATOR_LEAN4EXPORT="$LEAN4EXPORT"
if [ -z "${COMPARATOR_LANDRUN:-}" ]; then
  if command -v landrun >/dev/null 2>&1; then COMPARATOR_LANDRUN="$(command -v landrun)"
  else COMPARATOR_LANDRUN="$TOOLS/comparator/scripts/fake-landrun.sh"; echo "WARNING: no landrun found, using the non-sandboxing shim $COMPARATOR_LANDRUN" >&2; fi
fi
export COMPARATOR_LANDRUN
lake exe cache get || true
mkdir -p logs
lake build ThomsonN7 ComparatorChallenges 2>&1 | tail -5
/usr/bin/time -p lake env "$COMPARATOR_BIN" ComparatorChallenges/thomson_n7.comparator.json 2>&1 | tee logs/comparator.log
echo "COMPARATOR EXIT: ${PIPESTATUS[0]}"
