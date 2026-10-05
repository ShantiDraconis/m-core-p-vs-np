#!/usr/bin/env bash
set -euo pipefail

export PATH="$HOME/.elan/bin:$PATH"

lean --version
lake --version

lake build MCore.Real.P02UniversalFailureWitnessMaterial
lake build MCore.Real.P02SequentialCompositionMachine

cat > /tmp/P02RunnerAudit.lean <<'EOF'
import MCore.Real.P02UniversalFailureWitnessMaterial
import MCore.Real.P02SequentialCompositionMachine

#print axioms MCore.Real.P02UniversalFailureWitnessMaterial.witness_implies_universalFailure
#print axioms MCore.Real.P02UniversalFailureWitnessMaterial.witness_implies_notInP
#print axioms MCore.Real.P02UniversalFailureWitnessMaterial.witness_implies_p_ne_np
#print axioms MCore.Real.P02UniversalFailureWitnessMaterial.witness_iff_universalFailure

#print axioms MCore.Real.P02SequentialCompositionMachine.sequential_initial
#print axioms MCore.Real.P02SequentialCompositionMachine.sequential_blank
#print axioms MCore.Real.P02SequentialCompositionMachine.sequential_halting_left
#print axioms MCore.Real.P02SequentialCompositionMachine.sequential_halting_right
#print axioms MCore.Real.P02SequentialCompositionMachine.sequential_bridge_step
EOF

lake env lean /tmp/P02RunnerAudit.lean 2>&1 | tee /tmp/p02-runner-audit.log

if grep -E 'sorryAx' /tmp/p02-runner-audit.log; then
  echo "ERROR: sorryAx detected"
  exit 10
fi

grep -En '(^|[[:space:]])(sorry|admit)([[:space:]]|$)|^[[:space:]]*axiom[[:space:]]'   lean/MCore/Real/P02UniversalFailureWitnessMaterial.lean   lean/MCore/Real/P02SequentialCompositionMachine.lean && exit 11 || true

echo P02_DUAL_KERNEL_GREEN
