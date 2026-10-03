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

echo "== PREFLIGHT L0: STRUCTURE COMPLETENESS =="
bash audit/p02_lane4_structure_check.sh

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

# The repository may carry a stale pre-Mathlib manifest.  lake update is the
# authoritative regeneration step; verify that it actually records Mathlib
# before attempting cache or compilation.
if [[ -f lake-manifest.json ]] && ! grep -q '"name"[[:space:]]*:[[:space:]]*"mathlib"' lake-manifest.json; then
  echo "MANIFEST_STALE_BEFORE_UPDATE: regenerating dependency manifest"
fi

lake update

grep -q '"name"[[:space:]]*:[[:space:]]*"mathlib"' lake-manifest.json \
  || red "lake update completed but lake-manifest.json still has no mathlib package"

echo "MANIFEST_RESOLVED: mathlib present after lake update"

# Match CI dependency materialization.  If cache is unavailable, fail here
# rather than allowing later imports to produce misleading missing-olean errors.
lake exe cache get

# Build only the registered terminal module for P02-LANE-4.  Lake resolves
# its complete dependency closure topologically while excluding unrelated
# lanes such as P03 that are not dependencies of this module.
echo "-- TOPOLOGICAL MODULE P02Lane4"
LANE_BUILD_LOG="${TMPDIR:-/tmp}/p02_lane4_complete_bundle_build.log"
rm -f "$LANE_BUILD_LOG"
lake build +P02Lane4 2>&1 | tee "$LANE_BUILD_LOG"
echo "PREFLIGHT_LANE4_TARGET_SUCCESS"

# Once the dependency graph has been built, re-elaborate the critical base
# source directly so its source-level elaboration is independently visible.
echo "-- BASE RECHECK lean/MCore/Real/PNPNTMTableauEncoding.lean"
lake env lean lean/MCore/Real/PNPNTMTableauEncoding.lean
echo "PREFLIGHT_TABLEAU_BASE_SUCCESS"

echo "== PREFLIGHT L3: AUX GATE MIRROR =="

rm -f "$LOG"
P02_LANE4_TARGET_ALREADY_GREEN=1 \
  bash audit/p02_lane4_aux_green.sh 2>&1 | tee "$LOG"

grep -q 'SCAN_OK: 0 axiom/sorry/admit/opaque' "$LOG" \
  || red "gate did not emit SCAN_OK"

grep -q 'P02Lane4 SUCCESS' "$LOG" \
  || red "gate did not confirm CompleteBundle topological build"

grep -q 'AUX_GREEN_CANDIDATE: P02-LANE-4' "$LOG" \
  || red "gate did not emit AUX_GREEN_CANDIDATE"

echo "PREFLIGHT_GREEN: P02-LANE-4 AUX"
echo "LOG: $LOG"
echo "DOES_NOT_CERTIFY: T10 | UniversalFailure | SAT_not_in_P | P_ne_NP | FULL_FROZEN_HARD"
