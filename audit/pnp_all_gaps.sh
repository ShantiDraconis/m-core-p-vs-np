#!/usr/bin/env bash
set -euo pipefail

BRANCH_EXPECTED="discovery/pnp-open-math-20261004"

echo "[PNP-DISCOVERY] branch:"
git rev-parse --abbrev-ref HEAD || true
echo "[PNP-DISCOVERY] head:"
git rev-parse HEAD || true

FILES=(
  lean/MCore/Real/PNPDiscovery/OrbitCollision.lean
  lean/MCore/Real/PNPDiscovery/OrbitArithmetic.lean
  lean/MCore/Real/PNPDiscovery/TerminalStateFrontier.lean
  lean/MCore/Real/PNPDiscovery/ReadCone.lean
  lean/MCore/Real/PNPDiscovery/ReadConeFrontier.lean
  lean/MCore/Real/PNPDiscovery/PrefixPressure.lean
  lean/MCore/Real/PNPDiscovery/BarrierPressure.lean
  lean/MCore/Real/PNPDiscovery/EncodingDependencyMap.lean
  lean/MCore/Real/PNPDiscovery/ReductionPrefixFormula.lean
  lean/MCore/Real/PNPDiscovery/ClockVsEncodingLayout.lean
  lean/MCore/Real/PNPDiscovery/ParityDistinguishingBit.lean
  lean/MCore/Real/PNPDiscovery/EncodingSpine.lean
  lean/MCore/Real/PNPDiscovery/HeadBlockFrontier.lean
  lean/MCore/Real/PNPDiscovery/SourceBlockFrontier.lean
  lean/MCore/Real/PNPDiscovery/SourcePrefixFrontier.lean
  lean/MCore/Real/PNPDiscovery/RightCellInjectivity.lean
  lean/MCore/Real/PNPDiscovery/LeftBlockElimination.lean
  lean/MCore/Real/PNPDiscovery/SourceBitOffsets.lean
  lean/MCore/Real/PNPDiscovery/TableauRegionMap.lean
  lean/MCore/Real/PNPDiscovery/BitRegionMap.lean
  lean/MCore/Real/PNPDiscovery/SourcePrefixPressure.lean
)

echo "[PNP-DISCOVERY] proof escape scan"
if grep -nE '(^|[^A-Za-z])(sorry|admit)([^A-Za-z]|$)|^[[:space:]]*axiom[[:space:]]' "${FILES[@]}"; then
  echo "RED: proof escape found"
  exit 1
fi

echo "[PNP-DISCOVERY] targeted kernel build"
for f in "${FILES[@]}"; do
  echo "==> $f"
  lake env lean "$f"
done

echo "[PNP-DISCOVERY] root build"
lake build MCore

TMP=$(mktemp)
cat > "$TMP" <<'LEAN'
import MCore.Real.PNPDiscovery.BarrierPressure
import MCore.Real.PNPDiscovery.ReadConeFrontier
import MCore.Real.PNPDiscovery.PrefixPressure

#print axioms MCore.Real.PNPDiscovery.material_payload_closes
#print axioms MCore.Real.PNPDiscovery.physical_gap_to_sat_in_np
#print axioms MCore.Real.PNPDiscovery.acceptance_collision_gives_exact_witness
#print axioms MCore.Real.PNPDiscovery.orbit_collision_producer_to_exact
#print axioms MCore.Real.PNPDiscovery.terminalStateRecurrence_to_exact
#print axioms MCore.Real.PNPDiscovery.sharedReadConeCollision_to_exact
#print axioms MCore.Real.PNPDiscovery.parityBarrier_forces_sharedCone_difference
#print axioms MCore.Real.PNPDiscovery.parityBarrier_forces_min_clock_ge_three
#print axioms MCore.Real.PNPDiscovery.audited_material_closure
LEAN

echo "[PNP-DISCOVERY] axiom audit"
lake env lean "$TMP" | tee /tmp/pnp_discovery_axioms.txt

if grep -E 'sorryAx|MCore\..*axiom|PNPDiscovery\..*axiom' /tmp/pnp_discovery_axioms.txt; then
  echo "RED: nonstandard/source axiom detected"
  exit 1
fi

echo "[PNP-DISCOVERY] GAP LEDGER"
cat <<'EOF'
MATERIAL_OPEN:
  1. SATInNPPhysicalGap = Nonempty P01MachineConstruction
  2. SATSeparationGap = UniversalFailure canonical SAT

DISCOVERY_SUBFRONTIER:
  state block CLOSED -> head(clock, first symbol) -> left block CLOSED
  -> source-cell offsets / source-prefix alignment
  -> HeadAlignment + state/head prefix coverage
  -> PrefixDominanceProducer
  -> SharedReadConeCollisionProducer
  -> TerminalStateRecurrenceProducer
  -> ObservableRecurrenceProducer
  -> OrbitCollisionProducer
  -> TotalExactDiagonalProducer
  -> SATSeparationGap

OPEN_BRIDGE_REDUCIBLE:
  1. SourcePrefixCoverageGap -- list/encoding prefix transport; not P!=NP mathematics

METHOD_AUDIT_OPEN:
  1. RelativizationFormalizationGap
  2. NaturalProofFormalizationGap
  3. AlgebrizationFormalizationGap

EQUIVALENT_GAP:
  ObservableRecurrenceProducer <-> OrbitCollisionProducer

CLOSED_TRANSPORT:
  MaterialSeparationPayload -> PneqNP
  SATInNPPhysicalGap -> canonical SAT in NP
  OrbitCollisionProducer -> TotalExactDiagonalProducer
EOF

echo "GREEN: discovery kernel/audit layer passes. This does NOT mean P != NP is proved unless MATERIAL_OPEN is empty."
