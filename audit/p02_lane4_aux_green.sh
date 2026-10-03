#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

LANE_DIR="lean/P02/LANE4"
AUX_DIR="$LANE_DIR/AUX"
OPEN_DIR="$LANE_DIR/OPEN_MATH"

echo "== P02-LANE-4: L0 STRUCTURE PRECHECK =="
bash audit/p02_lane4_structure_check.sh

echo "== P02-LANE-4: STATIC SCAN =="
if grep -R -n -E '(^[[:space:]]*axiom\b|\bsorry\b|\badmit\b|^[[:space:]]*opaque\b)'   "$AUX_DIR" "$LANE_DIR/StructuralClosure.lean" "$OPEN_DIR"   --include='*.lean'; then
  echo "RED: forbidden Lean construct found in P02-LANE-4"
  exit 1
fi

echo "SCAN_OK: 0 axiom/sorry/admit/opaque"

echo "== P02-LANE-4: TOPOLOGICAL PREREQUISITE =="
if [[ "${P02_LANE4_BUNDLE_ALREADY_GREEN:-0}" == "1" ]]; then
  echo "P02.LANE4.CompleteBundle SUCCESS (reused from preflight L2)"
else
  lake build P02.LANE4.CompleteBundle
  echo "P02.LANE4.CompleteBundle SUCCESS"
fi

echo "== P02-LANE-4: BASE DEPENDENCY KERNEL CHECK =="
lake env lean lean/MCore/Real/PNPNTMTableauEncoding.lean

echo "== P02-LANE-4: AUX FILE KERNEL CHECK =="
FILES=(
  lean/P02/LANE4/AUX/R1_R3_REAL.lean
  lean/P02/LANE4/AUX/R2_R4_RADIUS.lean
  lean/P02/LANE4/AUX/R4_R5_BOUNDED.lean
  lean/P02/LANE4/AUX/R4_TRANSITION_LENGTH.lean
  lean/P02/LANE4/AUX/R4_PREFIX_SIGNATURE.lean
  lean/P02/LANE4/AUX/R4_PREFIX_MAXIMAL.lean
  lean/P02/LANE4/AUX/R4_TRANSITION_HEAD.lean
  lean/P02/LANE4/AUX/R4_TRANSITION_HEAD_FINAL.lean
  lean/P02/LANE4/AUX/R4_INITIAL_INJECTIVE.lean
  lean/P02/LANE4/AUX/R4_INITIAL_CNF_DECODER.lean
  lean/P02/LANE4/AUX/R4_FINAL.lean
  lean/P02/LANE4/AUX/R4_FIXED_FUEL.lean
  lean/P02/LANE4/AUX/R5_PAIR_INJECTIVE.lean
  lean/P02/LANE4/AUX/R5_PAIR.lean
  lean/P02/LANE4/StructuralClosure.lean
  lean/P02/LANE4/AUX/STRUCTURAL_CLOSURE.lean
  lean/P02/LANE4/OPEN_MATH/BehavioralAlignment.lean
  lean/P02/LANE4/OPEN_MATH/FuelCounterexample.lean
  lean/P02/LANE4/OPEN_MATH/SameBehaviorFromPolyBound.lean
  lean/P02/LANE4/StructureBundle.lean
  lean/P02/LANE4/AdvancedCertificateReuse.lean
  lean/P02/LANE4/CompleteBundle.lean
)

for f in "${FILES[@]}"; do
  echo "-- CHECK $f"
  lake env lean "$f"
done

echo "== P02-LANE-4: SCOPED TOPOLOGICAL BUILD STATUS =="
echo "P02.LANE4.CompleteBundle SUCCESS"

echo "== P02-LANE-4: FAIL-CLOSED FRONTIER CHECK =="
if ! grep -q '"state": "OPEN_MATH"' audit/P02_LANE4_STRUCTURAL_CLOSURE_V1.json; then
  echo "RED: T10 OPEN_MATH state missing from structural ledger"
  exit 1
fi
if ! grep -q '"promoted": false' audit/P02_LANE4_STRUCTURAL_CLOSURE_V1.json; then
  echo "RED: fail-closed promotion guard missing"
  exit 1
fi

if ! grep -q '"kernel_verified": false' audit/P02_LANE4_STRUCTURAL_CLOSURE_V1.json; then
  echo "RED: kernel-pending guard missing before AUX promotion"
  exit 1
fi
if ! grep -q '"frozen_hard_aux": false' audit/P02_LANE4_STRUCTURAL_CLOSURE_V1.json; then
  echo "RED: FROZEN_HARD AUX guard missing"
  exit 1
fi
if ! grep -q '"frozen_hard_full": false' audit/P02_LANE4_STRUCTURAL_CLOSURE_V1.json; then
  echo "RED: FROZEN_HARD FULL guard missing"
  exit 1
fi
if ! grep -q '"remaining_terminal": "G21Pointwise"' audit/P02_LANE4_STRUCTURAL_CLOSURE_V1.json; then
  echo "RED: canonical G21 terminal accounting missing"
  exit 1
fi

echo "AUX_GREEN_CANDIDATE: P02-LANE-4"
echo "T10_OPEN_MATH: MCore.Real.P02BehavioralAlignment.TotalBehavioralAlignmentProducer"
echo "DOES_NOT_CERTIFY: UniversalFailure | SAT_not_in_P | P_ne_NP | FULL_FROZEN_HARD"
