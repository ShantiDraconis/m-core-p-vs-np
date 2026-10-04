#!/usr/bin/env bash
set -euo pipefail

FILES=(
  lean/MCore/Real/PNPDiscovery/KernelTestClosedLayer.lean
  lean/MCore/Real/PNPDiscovery/KernelTestFalsifiedRoutes.lean
  lean/MCore/Real/PNPDiscovery/KernelTestGodelLayer.lean
  lean/MCore/Real/PNPDiscovery/KernelTestOpenFrontier.lean
  lean/MCore/Real/PNPDiscovery/PlusOneSemanticsAudit.lean
  lean/MCore/Real/PNPDiscovery/ExactOpenMathMinCut.lean
  lean/MCore/Real/PNPDiscovery/MaterialClosureCertificateContract.lean
)

echo "[PNP-KERNEL] proof-escape scan"
if grep -nE '(^|[^A-Za-z])(sorry|admit)([^A-Za-z]|$)|^[[:space:]]*axiom[[:space:]]' "${FILES[@]}"; then
  echo "RED: proof escape found"
  exit 1
fi

echo "[PNP-KERNEL] targeted Lean checks"
for f in "${FILES[@]}"; do
  echo "==> $f"
  lake env lean "$f"
done

echo "[PNP-KERNEL] axiom audit"
TMP=$(mktemp --suffix=.lean)
OUT=$(mktemp)
trap 'rm -f "$TMP" "$OUT"' EXIT
cat > "$TMP" <<'LEAN'
import MCore.Real.PNPDiscovery.KernelTestClosedLayer
import MCore.Real.PNPDiscovery.KernelTestFalsifiedRoutes
import MCore.Real.PNPDiscovery.KernelTestGodelLayer
import MCore.Real.PNPDiscovery.KernelTestOpenFrontier

#print axioms MCore.Real.PNPDiscovery.exactMaterialMinCut_closes
#print axioms MCore.Real.PNPDiscovery.exactSeparationOpenAtom_iff_endpoint
#print axioms MCore.Real.PNPDiscovery.strictGrowth_refutes_literalReductionFixedPoint
#print axioms MCore.Real.PNPDiscovery.no_equalLength_positive_odd_pair
#print axioms MCore.Real.PNPDiscovery.canonicalClock_declaredAccepts_iff
#print axioms MCore.Real.PNPDiscovery.decodeNatList_encode
#print axioms MCore.Real.PNPDiscovery.concreteUnpack_pack
LEAN

lake env lean "$TMP" | tee "$OUT"
if grep -E 'sorryAx|(^|[^A-Za-z])axiom([^A-Za-z]|$)' "$OUT"; then
  echo "RED: nonstandard proof axiom detected"
  exit 1
fi

echo "[PNP-KERNEL] no-scaffold-escape guard"
bash audit/pnp_no_scaffold_escape.sh

echo "[PNP-KERNEL] root import check"
lake env lean lean/MCore.lean

echo "GREEN: structural kernel suite passed."
echo "NOTE: this is not a material P!=NP certificate."
