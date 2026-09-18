import MCore.K9

namespace MCore
namespace BackwardAudit

/-- Pure endpoint shape. This is a definition only.
The predicates must later be instantiated by an explicit formalization of the
official deterministic- and nondeterministic-polynomial-time language classes. -/
def FINAL_STATEMENT {Language : Type}
    (officialP officialNP : Language → Prop) : Prop :=
  ¬ ∀ L, officialP L ↔ officialNP L

/-- The same endpoint shape specialized to the repository's abstract interface.
This remains abstract until a concrete-model matching theorem is supplied. -/
def FINAL_STATEMENT_for_interface {Language : Type}
    (C : ClassicalComplexityInterface Language) : Prop :=
  FINAL_STATEMENT C.inP C.inNP

theorem final_statement_unfold {Language : Type}
    (officialP officialNP : Language → Prop) :
    FINAL_STATEMENT officialP officialNP ↔
      ¬ ∀ L, officialP L ↔ officialNP L := Iff.rfl

/-- Audit metadata only: these propositions/results are forbidden as hidden
premises in any attempted endpoint proof. -/
def forbiddenHypotheses : List String :=
  [ "FINAL_STATEMENT itself"
  , "P != NP / separation conclusion"
  , "existence of an NP language outside P"
  , "existence of K10 witness data for arbitrary types treated as the official model"
  , "C12 finite PaysOff measurements treated as an asymptotic theorem"
  , "an unproved quantitative-to-classical transfer bridge"
  ]

end BackwardAudit
end MCore
