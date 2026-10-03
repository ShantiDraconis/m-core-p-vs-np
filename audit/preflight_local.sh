#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

LANE_DIR="lean/P02/LANE4"
AUX_DIR="$LANE_DIR/AUX"
OPEN_DIR="$LANE_DIR/OPEN_MATH"
LOG="${TMPDIR:-/tmp}/p02_lane4_aux_gate.log"

red() {
  echo "RED: $*" >&2
  exit 1
}

echo "== PREFLIGHT L1: STATIC FAIL-FAST =="

# Keep this scan definition aligned with audit/p02_lane4_aux_green.sh.
if grep -R -n -E '(^[[:space:]]*axiom\b|\bsorry\b|\badmit\b|^[[:space:]]*opaque\b)' \
  "$AUX_DIR" "$LANE_DIR/StructuralClosure.lean" "$OPEN_DIR" \
  --include='*.lean'; then
  red "forbidden Lean construct found in P02-LANE-4"
fi

echo "SCAN_OK: 0 axiom/sorry/admit/opaque"

# Manifest/import consistency check.  This catches the RED seen when a source
# imports Mathlib but lakefile.toml has no corresponding package declaration.
if grep -R -q --include='*.lean' '^import Mathlib' lean/; then
  grep -q 'name = "mathlib"' lakefile.toml \
    || red 'import Mathlib present but [[require]] mathlib missing from lakefile.toml'
fi

grep -q 'rev = "v4.19.0"' lakefile.toml \
  || red 'mathlib is not pinned to v4.19.0'

echo "MANIFEST_OK: mathlib declared and pinned"

echo "== PREFLIGHT L2: TOPOLOGICAL BUILD =="

# Remove stale oleans so local success cannot come from an obsolete dependency.
lake clean || true
lake update

# Match CI dependency materialization.  If cache is unavailable, fail here
# rather than allowing later imports to produce misleading missing-olean errors.
lake exe cache get

# Build the registered Lean library topologically.  This is the only reliable
# way to materialize the full import chain
# PNPNTMTableauEncoding -> PNPNTMPathFrontier -> PNPNTMTableauFrontier -> ...
# without depending on stale .olean files.
echo "-- TOPOLOGICAL LIBRARY MCore"
MCORE_LOG="${TMPDIR:-/tmp}/p02_lane4_mcore_build.log"
rm -f "$MCORE_LOG"
lake build MCore 2>&1 | tee "$MCORE_LOG"
echo "PREFLIGHT_MCORE_SUCCESS"

# Once the dependency graph has been built, re-elaborate the critical base
# source directly so its source-level elaboration is independently visible.
echo "-- BASE RECHECK lean/MCore/Real/PNPNTMTableauEncoding.lean"
lake env lean lean/MCore/Real/PNPNTMTableauEncoding.lean
echo "PREFLIGHT_TABLEAU_BASE_SUCCESS"

echo "== PREFLIGHT L3: AUX GATE MIRROR =="

rm -f "$LOG"
bash audit/p02_lane4_aux_green.sh 2>&1 | tee "$LOG"

grep -q 'SCAN_OK: 0 axiom/sorry/admit/opaque' "$LOG" \
  || red "gate did not emit SCAN_OK"

grep -q 'lake build MCore SUCCESS' "$LOG" \
  || red "gate did not confirm lake build MCore SUCCESS"

grep -q 'AUX_GREEN_CANDIDATE: P02-LANE-4' "$LOG" \
  || red "gate did not emit AUX_GREEN_CANDIDATE"

echo "PREFLIGHT_GREEN: P02-LANE-4 AUX"
echo "LOG: $LOG"
echo "DOES_NOT_CERTIFY: T10 | UniversalFailure | SAT_not_in_P | P_ne_NP | FULL_FROZEN_HARD"
