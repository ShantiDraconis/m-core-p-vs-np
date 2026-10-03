#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

red() { echo "RED: $*" >&2; exit 1; }

echo "== P02-LANE-4 STRUCTURE CHECK =="

FILES=(
  lean/MCore/Real/PNPCookLevinMaterialMinCut.lean
  lean/MCore/Real/PNPNTMTableauFrontier.lean
  lean/MCore/Real/PNPNTMPathFrontier.lean
  lean/MCore/Real/PNPNTMTableauEncoding.lean
  lean/MCore/Real/PNPNTMTableauClosure.lean
  lean/MCore/Real/P02TableauSourceRecovery.lean
  lean/MCore/Real/P02ComplementRunRealization.lean
  lean/MCore/Real/P02BehavioralAlignment.lean
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
  lean/P02/LANE4/StructureBundle.lean
  lean/P02/LANE4/OPEN_MATH/BehavioralAlignment.lean
  lean/P02/LANE4/OPEN_MATH/FuelCounterexample.lean
  lean/P02/LANE4/OPEN_MATH/SameBehaviorFromPolyBound.lean
  audit/P02_LANE4_STRUCTURE_GRAPH_V1.json
)

for f in "${FILES[@]}"; do
  test -f "$f" || red "missing structural file: $f"
done
echo "FILES_OK: ${#FILES[@]} structural files present"

grep -q 'name = "mathlib"' lakefile.toml || red "mathlib dependency missing"
grep -q 'rev = "v4.19.0"' lakefile.toml || red "mathlib pin mismatch"
echo "MANIFEST_STRUCTURE_OK"

# Critical source-level declarations. This is not a proof check; it prevents
# name drift before the kernel is invoked.
grep -q 'theorem initial_dim_extract_real' lean/P02/LANE4/AUX/R2_R4_RADIUS.lean \
  || red "missing initial_dim_extract_real"
grep -q 'theorem boundedExecTableau_pair_injective' lean/P02/LANE4/AUX/R5_PAIR_INJECTIVE.lean \
  || red "missing boundedExecTableau_pair_injective"
grep -q 'theorem boundedExecCircuit_pair_injective' lean/P02/LANE4/AUX/R5_PAIR_INJECTIVE.lean \
  || red "missing boundedExecCircuit_pair_injective"
grep -q 'theorem reduce_M_injective_final' lean/P02/LANE4/AUX/R5_PAIR_INJECTIVE.lean \
  || red "missing reduce_M_injective_final"
grep -q 'theorem total_behavioral_alignment_to_exact' lean/MCore/Real/P02BehavioralAlignment.lean \
  || red "missing total_behavioral_alignment_to_exact"
grep -q 'def auxStructure' lean/P02/LANE4/StructureBundle.lean \
  || red "missing auxStructure aggregate"
grep -q 'abbrev T10OpenMath' lean/P02/LANE4/StructureBundle.lean \
  || red "missing T10OpenMath boundary"
echo "SYMBOLS_OK"

# MCore root must wire every structural facade used by the public aggregate.
grep -q '^import P02.LANE4.AUX.R5_PAIR$' lean/MCore.lean \
  || red "R5_PAIR facade not wired into MCore"
grep -q '^import P02.LANE4.StructureBundle$' lean/MCore.lean \
  || red "StructureBundle not wired into MCore"
echo "ROOT_IMPORTS_OK"

if grep -R -n -E '(^[[:space:]]*axiom\b|\bsorry\b|\badmit\b|^[[:space:]]*opaque\b)' \
  lean/P02/LANE4 --include='*.lean'; then
  red "forbidden construct in LANE4 structure"
fi
echo "STRUCTURE_SCAN_OK: 0 axiom/sorry/admit/opaque"
echo "STRUCTURE_READY_FOR_KERNEL"
