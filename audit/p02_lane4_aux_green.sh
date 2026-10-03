#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

LANE_DIR="lean/P02/LANE4"
AUX_DIR="$LANE_DIR/AUX"
OPEN_DIR="$LANE_DIR/OPEN_MATH"

echo "== P02-LANE-4: STATIC SCAN =="
if grep -R -n -E '(^[[:space:]]*axiom\b|\bsorry\b|\badmit\b|^[[:space:]]*opaque\b)'   "$AUX_DIR" "$LANE_DIR/StructuralClosure.lean" "$OPEN_DIR"   --include='*.lean'; then
  echo "RED: forbidden Lean construct found in P02-LANE-4"
  exit 1
fi

echo "== P02-LANE-4: AUX MODULE BUILD =="
lake build   P02.LANE4.AUX.R1_R3_REAL   P02.LANE4.AUX.R2_R4_RADIUS   P02.LANE4.AUX.R4_R5_BOUNDED   P02.LANE4.AUX.R4_TRANSITION_LENGTH   P02.LANE4.AUX.R4_PREFIX_SIGNATURE   P02.LANE4.AUX.R4_PREFIX_MAXIMAL   P02.LANE4.AUX.R4_TRANSITION_HEAD   P02.LANE4.AUX.R4_TRANSITION_HEAD_FINAL   P02.LANE4.AUX.R4_INITIAL_INJECTIVE   P02.LANE4.AUX.R4_INITIAL_CNF_DECODER   P02.LANE4.AUX.R4_FINAL   P02.LANE4.AUX.R4_FIXED_FUEL   P02.LANE4.AUX.R5_PAIR_INJECTIVE   P02.LANE4.AUX.R5_PAIR   P02.LANE4.StructuralClosure   P02.LANE4.AUX.STRUCTURAL_CLOSURE

echo "== P02-LANE-4: OPEN_MATH WRAPPER BUILD =="
lake build   P02.LANE4.OPEN_MATH.BehavioralAlignment   P02.LANE4.OPEN_MATH.FuelCounterexample

echo "== P02-LANE-4: FULL MCORE BUILD =="
lake build MCore

echo "== P02-LANE-4: FAIL-CLOSED FRONTIER CHECK =="
if ! grep -q '"state": "OPEN_MATH"' audit/P02_LANE4_STRUCTURAL_CLOSURE_V1.json; then
  echo "RED: T10 OPEN_MATH state missing from structural ledger"
  exit 1
fi
if ! grep -q '"promoted": false' audit/P02_LANE4_STRUCTURAL_CLOSURE_V1.json; then
  echo "RED: fail-closed promotion guard missing"
  exit 1
fi

echo "AUX_GREEN_CANDIDATE: P02-LANE-4"
echo "T10_OPEN_MATH: MCore.Real.P02BehavioralAlignment.TotalBehavioralAlignmentProducer"
echo "DOES_NOT_CERTIFY: UniversalFailure | SAT_not_in_P | P_ne_NP | FULL_FROZEN_HARD"
