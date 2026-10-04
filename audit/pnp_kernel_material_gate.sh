#!/usr/bin/env bash
set -euo pipefail

CERT="lean/MCore/Real/PNPDiscovery/MaterialClosureCertificate.lean"

echo "[PNP-MATERIAL] exact material gate"
if [[ ! -f "$CERT" ]]; then
  echo "RED: material certificate absent"
  echo "Required theorem payload:"
  echo "  satInNP : SATInNPPhysicalGap"
  echo "  separation : TotalExactDiagonalProducer"
  echo "Expected certificate file: $CERT"
  exit 2
fi

if grep -nE '(^|[^A-Za-z])(sorry|admit)([^A-Za-z]|$)|^[[:space:]]*axiom[[:space:]]' "$CERT"; then
  echo "RED: proof escape in material certificate"
  exit 1
fi

lake env lean "$CERT"

TMP=$(mktemp --suffix=.lean)
OUT=$(mktemp)
trap 'rm -f "$TMP" "$OUT"' EXIT
cat > "$TMP" <<'LEAN'
import MCore.Real.PNPDiscovery.MaterialClosureCertificate

#print axioms MCore.Real.PNPDiscovery.materialClosureCertificate
#print axioms MCore.Real.PNPDiscovery.materialClosureCertificate_closes
LEAN

lake env lean "$TMP" | tee "$OUT"
if grep -E 'sorryAx|(^|[^A-Za-z])axiom([^A-Za-z]|$)' "$OUT"; then
  echo "RED: material certificate depends on proof escape/nonstandard axiom"
  exit 1
fi

echo "GREEN: material certificate kernel-accepted."
