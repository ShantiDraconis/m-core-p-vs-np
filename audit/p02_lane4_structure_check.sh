#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

red() {
  echo "RED: $*" >&2
  exit 1
}

echo "== P02-LANE-4 L0: STRUCTURE COMPLETENESS =="

FILES=(
  lakefile.toml
  lean/MCore.lean
  lean/P02.lean
  lean/P02Lane4.lean

  lean/MCore/Real/PNPCookLevinMaterialMinCut.lean
  lean/MCore/Real/PNPNTMTableauFrontier.lean
  lean/MCore/Real/PNPNTMPathFrontier.lean
  lean/MCore/Real/PNPNTMTableauEncoding.lean
  lean/MCore/Real/PNPNTMTableauClosure.lean
  lean/MCore/Real/P02TableauSourceRecovery.lean
  lean/MCore/Real/P02ComplementRunRealization.lean
  lean/MCore/Real/P02BehavioralAlignment.lean
  lean/MCore/Real/P02ExactDiagonalFrontier.lean

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

  audit/P02_LANE4_STRUCTURE_GRAPH_V1.json
  audit/P02_LANE4_CERTIFICATE_REUSE_V1.json
  audit/P02_LANE4_ADVANCED_CERTIFICATE_REUSE_V1.json
  audit/P02_LANE4_STRUCTURAL_CLOSURE_V1.json
  audit/p02_lane4_aux_green.sh
  audit/preflight_local.sh
)

for f in "${FILES[@]}"; do
  [[ -f "$f" ]] || red "missing required file: $f"
done
echo "FILES_OK: ${#FILES[@]} required files present"

echo "== L0 SCRIPT SYNTAX =="
for s in   audit/p02_lane4_structure_check.sh   audit/preflight_local.sh   audit/p02_lane4_aux_green.sh
do
  bash -n "$s" || red "shell syntax error: $s"
done
echo "SCRIPT_SYNTAX_OK"

echo "== L0 IMPORT DAG =="
if grep -q '^import P02.LANE4.AdvancedCertificateReuse$' lean/P02/LANE4/StructureBundle.lean; then
  red "import cycle risk: StructureBundle imports AdvancedCertificateReuse"
fi
if grep -q '^import P02.LANE4.CompleteBundle$' lean/P02/LANE4/StructureBundle.lean; then
  red "import cycle risk: StructureBundle imports CompleteBundle"
fi
if grep -q '^import P02.LANE4.CompleteBundle$' lean/P02/LANE4/AdvancedCertificateReuse.lean; then
  red "import cycle risk: AdvancedCertificateReuse imports CompleteBundle"
fi
grep -q '^import P02.LANE4.StructureBundle$' lean/P02/LANE4/AdvancedCertificateReuse.lean   || red "AdvancedCertificateReuse must import StructureBundle"
grep -q '^import P02.LANE4.StructureBundle$' lean/P02/LANE4/CompleteBundle.lean   || red "CompleteBundle must import StructureBundle"
grep -q '^import P02.LANE4.AdvancedCertificateReuse$' lean/P02/LANE4/CompleteBundle.lean   || red "CompleteBundle must import AdvancedCertificateReuse"
echo "IMPORT_DAG_OK: StructureBundle -> AdvancedCertificateReuse -> CompleteBundle"

echo "== L0 MANIFEST =="
grep -q 'name = "mathlib"' lakefile.toml   || red "mathlib dependency missing from lakefile.toml"
grep -q 'git = "https://github.com/leanprover-community/mathlib4.git"' lakefile.toml   || red "mathlib repository mismatch"
grep -q 'rev = "v4.19.0"' lakefile.toml   || red "mathlib pin mismatch"
echo "MANIFEST_OK: mathlib v4.19.0"

echo "== L0 CRITICAL DECLARATIONS =="
grep -q 'theorem initial_dim_extract_real' lean/P02/LANE4/AUX/R2_R4_RADIUS.lean   || red "missing initial_dim_extract_real"
grep -q 'theorem boundedExecTableau_pair_injective' lean/P02/LANE4/AUX/R5_PAIR_INJECTIVE.lean   || red "missing boundedExecTableau_pair_injective"
grep -q 'theorem boundedExecCircuit_pair_injective' lean/P02/LANE4/AUX/R5_PAIR_INJECTIVE.lean   || red "missing boundedExecCircuit_pair_injective"
grep -q 'theorem reduce_M_injective_final' lean/P02/LANE4/AUX/R5_PAIR_INJECTIVE.lean   || red "missing reduce_M_injective_final"
grep -q 'theorem total_behavioral_alignment_to_exact' lean/MCore/Real/P02BehavioralAlignment.lean   || red "missing total_behavioral_alignment_to_exact"

grep -q 'def auxStructure' lean/P02/LANE4/StructureBundle.lean   || red "missing auxStructure"
grep -q 'abbrev T10OpenMath' lean/P02/LANE4/StructureBundle.lean   || red "missing T10OpenMath"

grep -q 'def G21Pointwise' lean/P02/LANE4/AdvancedCertificateReuse.lean   || red "missing G21Pointwise"
grep -q 'theorem g21_iff_not_in_p' lean/P02/LANE4/AdvancedCertificateReuse.lean   || red "missing g21_iff_not_in_p"
grep -q 'theorem g21_iff_p02_operator' lean/P02/LANE4/AdvancedCertificateReuse.lean   || red "missing g21_iff_p02_operator"
grep -q 'theorem g21_iff_normalized_adversary' lean/P02/LANE4/AdvancedCertificateReuse.lean   || red "missing g21_iff_normalized_adversary"
grep -q 'theorem p01_side_closed' lean/P02/LANE4/AdvancedCertificateReuse.lean   || red "missing p01_side_closed"
grep -q 'theorem claim_bundle_bridge_iff_g21' lean/P02/LANE4/AdvancedCertificateReuse.lean   || red "missing Claim1-7 firewall"
grep -q 'theorem t10_to_g21' lean/P02/LANE4/AdvancedCertificateReuse.lean   || red "missing t10_to_g21"
grep -q 'theorem effective_coverage_to_g21' lean/P02/LANE4/AdvancedCertificateReuse.lean   || red "missing effective_coverage_to_g21"

grep -q 'def sourceCompletePackage' lean/P02/LANE4/CompleteBundle.lean   || red "missing sourceCompletePackage"
grep -q 'theorem terminal_iff_not_in_p' lean/P02/LANE4/CompleteBundle.lean   || red "missing terminal_iff_not_in_p"
echo "SYMBOLS_OK"

echo "== L0 ROOT WIRING =="
grep -q '^import P02.LANE4.CompleteBundlegrep -q '^import P02.LANE4.AUX.R5_PAIR$' lean/MCore.lean   || red "R5_PAIR facade not wired into MCore"
grep -q '^import P02.LANE4.StructureBundle$' lean/MCore.lean   || red "StructureBundle not wired into MCore"
grep -q '^import P02.LANE4.AdvancedCertificateReuse$' lean/MCore.lean   || red "AdvancedCertificateReuse not wired into MCore"
grep -q '^import P02.LANE4.CompleteBundle$' lean/MCore.lean   || red "CompleteBundle not wired into MCore"
echo "ROOT_IMPORTS_OK"

echo "== L0 FORBIDDEN CONSTRUCT SCAN =="
if grep -R -n -E   '(^[[:space:]]*axiom[[:space:]]|(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)|^[[:space:]]*opaque[[:space:]])'   lean/P02/LANE4 --include='*.lean'
then
  red "forbidden construct in P02-LANE-4"
fi
echo "STRUCTURE_SCAN_OK: 0 axiom/sorry/admit/opaque"

echo "L0_OK: STRUCTURE_CONSTRUCTED_SOURCE_COMPLETE"
echo "KERNEL_VERIFIED: false"
echo "T10: OPEN_MATH"
echo "G21Pointwise: OPEN_MATH"
echo "FROZEN_HARD_AUX: false"
echo "FROZEN_HARD_FULL: false"
 lean/P02.lean \
  || red "P02 root does not import CompleteBundle"
grep -q '^import P02.LANE4.AUX.R5_PAIR$' lean/MCore.lean   || red "R5_PAIR facade not wired into MCore"
grep -q '^import P02.LANE4.StructureBundle$' lean/MCore.lean   || red "StructureBundle not wired into MCore"
grep -q '^import P02.LANE4.AdvancedCertificateReuse$' lean/MCore.lean   || red "AdvancedCertificateReuse not wired into MCore"
grep -q '^import P02.LANE4.CompleteBundle$' lean/MCore.lean   || red "CompleteBundle not wired into MCore"
echo "ROOT_IMPORTS_OK"

echo "== L0 FORBIDDEN CONSTRUCT SCAN =="
if grep -R -n -E   '(^[[:space:]]*axiom[[:space:]]|(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)|^[[:space:]]*opaque[[:space:]])'   lean/P02/LANE4 --include='*.lean'
then
  red "forbidden construct in P02-LANE-4"
fi
echo "STRUCTURE_SCAN_OK: 0 axiom/sorry/admit/opaque"

echo "L0_OK: STRUCTURE_CONSTRUCTED_SOURCE_COMPLETE"
echo "KERNEL_VERIFIED: false"
echo "T10: OPEN_MATH"
echo "G21Pointwise: OPEN_MATH"
echo "FROZEN_HARD_AUX: false"
echo "FROZEN_HARD_FULL: false"
