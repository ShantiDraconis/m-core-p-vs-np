#!/usr/bin/env bash
set -euo pipefail
lake build MCore.Real.P02UniversalFailureWitnessMaterial
cat > /tmp/P02UniversalFailureWitnessPriorityAudit.lean <<'EOF'
import MCore.Real.P02UniversalFailureWitnessMaterial
#print axioms MCore.Real.P02UniversalFailureWitnessMaterial.witness_implies_universalFailure
#print axioms MCore.Real.P02UniversalFailureWitnessMaterial.witness_implies_notInP
#print axioms MCore.Real.P02UniversalFailureWitnessMaterial.witness_implies_p_ne_np
#print axioms MCore.Real.P02UniversalFailureWitnessMaterial.witness_iff_universalFailure
EOF
lake env lean /tmp/P02UniversalFailureWitnessPriorityAudit.lean 2>&1 | tee /tmp/p02-g2-priority.log
! grep -E 'sorryAx' /tmp/p02-g2-priority.log
! grep -En '(^|[[:space:]])(sorry|admit)([[:space:]]|$)|^[[:space:]]*axiom[[:space:]]' lean/MCore/Real/P02UniversalFailureWitnessMaterial.lean
echo P02_G2_PRIORITY_KERNEL_GREEN

# retrigger-priority-run-20261005-2
