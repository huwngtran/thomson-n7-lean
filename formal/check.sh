#!/usr/bin/env bash
# One command: hashes, statement preamble, token scan, claims index, lake build, axioms, exact statement comparison,
# then the negative control for that comparison. The Comparator and the second kernel are separate (see REPRODUCE.md).
set -euo pipefail
cd -- "$(dirname -- "$0")/lean"
bash scripts/check.sh
bash scripts/negative-control.sh
