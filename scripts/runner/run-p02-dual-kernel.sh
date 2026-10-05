#!/usr/bin/env bash
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
lean --version
lake --version

lake build MCore.Real.P02UniversalFailureWitnessMaterial

cat > /tmp/P02G2RunnerAudit.lean <<'EOF'
import MCore.Real.P02UniversalFailureWitnessMaterial
#print axioms MCore.Real.P02UniversalFailureWitnessMaterial.witness_implies_universalFailure
#print axioms MCore.Real.P02UniversalFailureWitnessMaterial.witness_implies_notInP
#print axioms MCore.Real.P02UniversalFailureWitnessMaterial.witness_implies_p_ne_np
#print axioms MCore.Real.P02UniversalFailureWitnessMaterial.witness_iff_universalFailure
EOF

lake env lean /tmp/P02G2RunnerAudit.lean 2>&1 | tee /tmp/p02-g2-runner-audit.log
! grep -E 'sorryAx' /tmp/p02-g2-runner-audit.log
! grep -En '(^|[[:space:]])(sorry|admit)([[:space:]]|$)|^[[:space:]]*axiom[[:space:]]'   lean/MCore/Real/P02UniversalFailureWitnessMaterial.lean
echo P02_G2_SELF_HOSTED_GREEN
