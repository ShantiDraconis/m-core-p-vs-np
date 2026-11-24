import MCore.K9

namespace MCore.BackwardAudit

def InterfaceFinalStatement {Language : Type}
    (C : ClassicalComplexityInterface Language) : Prop :=
  ¬ ∀ L, C.inP L ↔ C.inNP L

end MCore.BackwardAudit
