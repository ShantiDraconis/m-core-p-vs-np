#!/usr/bin/env bash
set -euo pipefail

METHOD_FILES=(
  lean/MCore/Real/PNPDiscovery/UniversalSimulationPrerequisites.lean
  lean/MCore/Real/PNPDiscovery/NormalizedUniversalPrerequisites.lean
  lean/MCore/Real/PNPDiscovery/CanonicalClockNormalization.lean
  lean/MCore/Real/PNPDiscovery/FiniteCandidateDescription.lean
  lean/MCore/Real/PNPDiscovery/UnaryListSerialization.lean
  lean/MCore/Real/PNPDiscovery/FiniteCandidateGodelWords.lean
  lean/MCore/Real/PNPDiscovery/FiniteDescriptionInjectivity.lean
  lean/MCore/Real/PNPDiscovery/ConcreteMachineInputPairing.lean
)

echo "[PNP-NO-SCAFFOLD] proof escapes"
if grep -nE '(^|[^A-Za-z])(sorry|admit)([^A-Za-z]|$)|^[[:space:]]*axiom[[:space:]]' "${METHOD_FILES[@]}"; then
  echo "RED: proof escape in method infrastructure"
  exit 1
fi

echo "[PNP-NO-SCAFFOLD] endpoint promotion"
if grep -nE 'theorem[[:space:]].*PneqNP|def[[:space:]].*:[[:space:]]*PneqNP|theorem[[:space:]].*TotalExactDiagonalProducer|def[[:space:]].*:[[:space:]]*TotalExactDiagonalProducer' "${METHOD_FILES[@]}"; then
  echo "RED: method infrastructure promoted itself to material endpoint"
  exit 1
fi

echo "[PNP-NO-SCAFFOLD] vacuous placeholders"
if grep -nE '∧[[:space:]]*True|:[[:space:]]*True[[:space:]]*:=' "${METHOD_FILES[@]}"; then
  echo "RED: vacuous True scaffold detected"
  exit 1
fi

echo "[PNP-NO-SCAFFOLD] literal fixed-point route is enforced semantically by KernelTestFalsifiedRoutes.lean"
echo "GREEN: no-scaffold-escape guard passed."
