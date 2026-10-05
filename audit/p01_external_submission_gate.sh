#!/usr/bin/env bash
set -euo pipefail

FILES=(
  lean/MCore/Real/P01PreservingUnaryWitnessMarker.lean
  lean/MCore/Real/P01InputNodePreservingPlan.lean
  lean/MCore/Real/P01PreservingMarkerIteration.lean
  lean/MCore/Real/P01PreservingUnaryWitnessMachine.lean
  lean/MCore/Real/P01PreservingUnaryReaderCertificate.lean
  lean/MCore/Real/P01WitnessIndexedReadGlobal.lean
)

echo "== P01 external submission gate =="

for f in "${FILES[@]}"; do
  test -f "$f" || { echo "MISSING: $f"; exit 1; }

  if grep -nE '(^|[[:space:]])(sorry|admit|sorryAx)([[:space:]]|$)' "$f"; then
    echo "FAIL placeholder: $f"
    exit 1
  fi

  if grep -nE '^[[:space:]]*axiom[[:space:]]' "$f"; then
    echo "FAIL axiom declaration: $f"
    exit 1
  fi

  if grep -nE '^[[:space:]]*opaque[[:space:]]' "$f"; then
    echo "FAIL opaque declaration: $f"
    exit 1
  fi

  if grep -nE '(^|[[:space:]])unsafe([[:space:]]|$)|implemented_by|native_decide|IO\.FS\.readFile|Classical\.choice|Classical\.dec' "$f"; then
    echo "FAIL forbidden proof mechanism: $f"
    exit 1
  fi
done

echo "HYGIENE_GREEN"

lake build MCore.Real.P01PreservingUnaryWitnessMarker
lake build MCore.Real.P01InputNodePreservingPlan
lake build MCore.Real.P01PreservingMarkerIteration
lake build MCore.Real.P01PreservingUnaryWitnessMachine
lake build MCore.Real.P01PreservingUnaryReaderCertificate
lake build MCore.Real.P01WitnessIndexedReadGlobal

echo "BUILD_GREEN"
echo "ACTIONS=0"
echo "EXTERNAL_GATE=SOURCE_READY"
