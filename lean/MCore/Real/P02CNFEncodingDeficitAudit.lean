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
  constructor
  · simp [oneClauseCore, cnfCircuit, clauseCircuit, literalCircuit,
      D, vars, freeVarList, restrictedSimplified, restrict, simplify]
  · right
    simp [oneClauseCore, cnfCircuit, clauseCircuit, literalCircuit,
      D, delta, mu, CircuitC3.potential, restrictedSimplified,
      restrict, simplify, CircuitK1.size, CircuitK1.depth]

theorem free_cost_zero_oneClauseCore :
    costBits leavesZeroFree (cnfCircuit oneClauseCore) = 0 := by
  simp [costBits, fixedVarsCount, fixedVarList, oneClauseCore,
    cnfCircuit, clauseCircuit, literalCircuit, leavesZeroFree]

theorem free_amortizedDrop_pos_oneClauseCore :
    0 < amortizedDrop 1 1 leavesZeroFree (cnfCircuit oneClauseCore) := by
  simp [amortizedDrop, Potential, oneClauseCore, cnfCircuit, clauseCircuit,
    literalCircuit, D, vars, freeVarList, stateRank, recurrenceRank, mu,
    CircuitC3.potential, restrictedSimplified, restrict, simplify,
    CircuitK1.size, CircuitK1.depth]

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
