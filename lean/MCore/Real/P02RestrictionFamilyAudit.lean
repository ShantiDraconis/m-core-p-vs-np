import MCore.Real.CNFStructure
import MCore.C11.BranchingCost
import MCore.C10.RestrictionProgress

namespace MCore
namespace Real
namespace P02RestrictionFamilyAudit

open CircuitK1 CircuitC2
open C9 C10 C11

theorem reducibleExample_isCNF :
    IsCNF reducibleExample := by
  simp [reducibleExample, IsCNF, IsClause]

theorem reducibleExample_paysOff :
    PaysOff 1 1 fixesZeroTrue reducibleExample := by
  simp [PaysOff, Potential, costBits, fixedVarsCount, fixedVarList,
    C9.stateRank, CircuitC8.recurrenceRank, C9.vars, C9.freeVarList,
    C9.mu, C9.D, CircuitC3.potential, CircuitC2.restrictedSimplified,
    CircuitK1.restrict, CircuitC2.simplify, CircuitK1.reducibleExample,
    CircuitK1.fixesZeroTrue, CircuitK1.size, CircuitK1.depth]

theorem reducibleExample_progress :
    RestrictionProgress fixesZeroTrue reducibleExample :=
  reducibleExample_restriction_progress

/-- Therefore any candidate hard family containing every CNF formula cannot
satisfy a universal persistent-deficit condition over all progressing
restrictions. -/
theorem allCNF_universal_deficit_refuted :
    ¬ (∀ (t : FormulaTree),
        IsCNF t →
        ∀ ρ : Restriction,
          RestrictionProgress ρ t →
            ¬ PaysOff 1 1 ρ t) := by
  intro h
  exact (h reducibleExample reducibleExample_isCNF
    fixesZeroTrue reducibleExample_progress) reducibleExample_paysOff

#print axioms MCore.Real.P02RestrictionFamilyAudit.reducibleExample_paysOff
#print axioms MCore.Real.P02RestrictionFamilyAudit.allCNF_universal_deficit_refuted

end P02RestrictionFamilyAudit
end Real
end MCore
