import Mathlib.Tactic
import MCore.Real.P02RestrictionLowerBoundPattern

namespace MCore
namespace Real
namespace P02CNFEncodingDeficitAudit

open CircuitK1 CircuitC2
open C9 C10 C11
open P02BoundedComputationEncoding
open P02RestrictionLowerBoundPattern

def oneClauseCore : CNF := [[pos 0]]

theorem free_progress_oneClauseCore :
    RestrictionProgress leavesZeroFree (cnfCircuit oneClauseCore) := by
  norm_num [RestrictionProgress, oneClauseCore, cnfCircuit, clauseCircuit,
    literalCircuit, pos, leavesZeroFree, D, vars, freeVarList,
    restrictedSimplified, restrict, simplify, delta, C9.mu,
    CircuitC3.potential, CircuitK1.size, CircuitK1.depth, CircuitK1.μ]

theorem free_cost_zero_oneClauseCore :
    costBits leavesZeroFree (cnfCircuit oneClauseCore) = 0 := by
  norm_num [costBits, fixedVarsCount, fixedVarList, oneClauseCore,
    cnfCircuit, clauseCircuit, literalCircuit, pos, leavesZeroFree]

theorem free_amortizedDrop_pos_oneClauseCore :
    0 < amortizedDrop 1 1 leavesZeroFree (cnfCircuit oneClauseCore) := by
  norm_num [amortizedDrop, Potential, oneClauseCore, cnfCircuit, clauseCircuit,
    literalCircuit, pos, D, vars, freeVarList, stateRank,
    CircuitC8.recurrenceRank, C9.mu, CircuitC3.potential,
    restrictedSimplified, restrict, simplify, leavesZeroFree,
    CircuitK1.size, CircuitK1.depth, CircuitK1.μ]

theorem oneClauseCore_not_deficit (c : Nat) :
    ¬ DeficitAtLeast c oneClauseCore := by
  intro h
  have hd := h leavesZeroFree free_progress_oneClauseCore
  have hcost := free_cost_zero_oneClauseCore
  have hdrop := free_amortizedDrop_pos_oneClauseCore
  omega

#print axioms MCore.Real.P02CNFEncodingDeficitAudit.oneClauseCore_not_deficit

end P02CNFEncodingDeficitAudit
end Real
end MCore
