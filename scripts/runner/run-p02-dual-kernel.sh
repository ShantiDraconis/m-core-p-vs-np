#!/usr/bin/env bash
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
lean --version
lake --version

lake build MCore.Real.P02SequentialCompositionMachine

cat > /tmp/P02EqualityRunnerAudit.lean <<'EOF'
import MCore.Real.P02SequentialCompositionMachine
#print axioms MCore.Real.P02SequentialCompositionMachine.sequential_initial
#print axioms MCore.Real.P02SequentialCompositionMachine.sequential_blank
#print axioms MCore.Real.P02SequentialCompositionMachine.sequential_halting_left
#print axioms MCore.Real.P02SequentialCompositionMachine.sequential_halting_right
#print axioms MCore.Real.P02SequentialCompositionMachine.sequential_step_left_active
#print axioms MCore.Real.P02SequentialCompositionMachine.sequential_step_right
#print axioms MCore.Real.P02SequentialCompositionMachine.sequential_bridge_step
EOF

lake env lean /tmp/P02EqualityRunnerAudit.lean 2>&1 | tee /tmp/p02-equality-runner-audit.log
! grep -E 'sorryAx' /tmp/p02-equality-runner-audit.log
! grep -En '(^|[[:space:]])(sorry|admit)([[:space:]]|$)|^[[:space:]]*axiom[[:space:]]'   lean/MCore/Real/P02SequentialCompositionMachine.lean
echo P02_EQUALITY_SELF_HOSTED_GREEN
