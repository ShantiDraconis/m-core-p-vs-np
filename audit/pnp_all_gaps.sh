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
  lean/MCore/Real/PNPDiscovery/SourcePrefixEncoderBridge.lean
  lean/MCore/Real/PNPDiscovery/SourcePrefixCoverageClosed.lean
  lean/MCore/Real/PNPDiscovery/SourcePrefixPressureClosed.lean
  lean/MCore/Real/PNPDiscovery/FullSourceDichotomy.lean
  lean/MCore/Real/PNPDiscovery/HeadParityPressure.lean
  lean/MCore/Real/PNPDiscovery/SourceMismatchVisibility.lean
  lean/MCore/Real/PNPDiscovery/SourceMismatchEncodingDichotomy.lean
  lean/MCore/Real/PNPDiscovery/FiniteBitMismatchClosed.lean
  lean/MCore/Real/PNPDiscovery/SourceBitVisibilityPressure.lean
  lean/MCore/Real/PNPDiscovery/SymbolBlockLocalization.lean
  lean/MCore/Real/PNPDiscovery/SourceGlobalBitOffset.lean
  lean/MCore/Real/PNPDiscovery/SourceCellBitTransport.lean
  lean/MCore/Real/PNPDiscovery/SourceCellBitTransportClosed.lean
  lean/MCore/Real/PNPDiscovery/SourcePrefixEndExpansion.lean
  lean/MCore/Real/PNPDiscovery/SourcePrefixEndEnvelope.lean
  lean/MCore/Real/PNPDiscovery/SourceHiddenGrowthExpansion.lean
  lean/MCore/Real/PNPDiscovery/VisibilityOrientationAudit.lean
  lean/MCore/Real/PNPDiscovery/OrbitLevelAlignmentCorrection.lean
  lean/MCore/Real/PNPDiscovery/SuccessorClockEnvelope.lean
  lean/MCore/Real/PNPDiscovery/LengthSourceCompression.lean
  lean/MCore/Real/PNPDiscovery/FirstSourceMismatch.lean
  lean/MCore/Real/PNPDiscovery/FirstGlobalBreak.lean
  lean/MCore/Real/PNPDiscovery/GlobalBreakSandwich.lean
  lean/MCore/Real/PNPDiscovery/SourceOffsetVisibilityLaw.lean
  lean/MCore/Real/PNPDiscovery/SourceOffsetLowerEnvelope.lean
  lean/MCore/Real/PNPDiscovery/BarrierArithmeticFrontier.lean
  lean/MCore/Real/PNPDiscovery/ArithmeticProducerClosure.lean
  lean/MCore/Real/PNPDiscovery/StrictLengthGrowth.lean
  lean/MCore/Real/PNPDiscovery/ArithmeticRouteFalsified.lean
  lean/MCore/Real/PNPDiscovery/StrictGrowthConsistency.lean
  lean/MCore/Real/PNPDiscovery/PerfectFlipRegimeAlignment.lean
  lean/MCore/Real/PNPDiscovery/StrictLengthGrowth.lean
  lean/MCore/Real/PNPDiscovery/ArithmeticBreakerRouteFalsified.lean
  lean/MCore/Real/PNPDiscovery/LayoutDriftFrontier.lean
  lean/MCore/Real/PNPDiscovery/LayoutBoundaryMismatch.lean
  lean/MCore/Real/PNPDiscovery/StrictOrbitLengthGrowth.lean
  lean/MCore/Real/PNPDiscovery/ArithmeticRouteFalsification.lean
  lean/MCore/Real/PNPDiscovery/LayoutLeakage.lean
  lean/MCore/Real/PNPDiscovery/AlphaRenameCore.lean
  lean/MCore/Real/PNPDiscovery/LayoutAlphaEquivalence.lean
  lean/MCore/Real/PNPDiscovery/TableauShapeLeakage.lean
  lean/MCore/Real/PNPDiscovery/TransitionShapeFrontier.lean
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

CLOSED_BRIDGES:
  SourceCellBitTransportGap
  SourceCellMismatchLocalizationGap
  SourceCellNumericLocalization
  SymbolBlock target-length invariance/injectivity
  SourcePrefixClauseCoverageGap
  SourcePrefixCoverageGap
  RightCellBlockInjectivity

BARRIER_FRONTIER:
  length mismatch OR clock mismatch OR head mismatch OR concrete source-cell mismatch

ROUTE_FALSIFIED:
  ArithmeticBarrierBreakerProducer via same-orbit equal-length recurrence
  reason: R_M strictly increases length at every step

CURRENT_FRONTIER:
  1. Single-orbit locality route is blocked by layout/shape leakage
  2. Radius mismatch -> initial CNF clause-count leak (alpha-invariant)
  3. Equal-radius clock compensation -> EqualRadiusTransitionShapeGap (reducible counting)
  4. Explore cross-seed equal-layout recurrence/collision

STRICT_GROWTH:
  R_M_strict_length_growth CLOSED
  no_positive_odd_length_recurrence CLOSED
  Arithmetic equal-length route CLOSED_BY_FALSIFICATION

LAYOUT_LEAKAGE:
  raw ID leakage CLOSED
  HEAD/first LEFT alpha-equivalent modulo ID renaming
  radius mismatch = alpha-invariant shape leakage
  EqualRadiusTransitionShapeGap = REDUCIBLE structural frontier

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
