import MCore.BackwardAudit.OrientedWitnessBoundary

namespace MCore.BackwardAudit

/-- Single authoritative abstract shape. MATERIAL_GREEN additionally requires
    binding P/NP/L to the repository's concrete standard complexity model. -/
def MinimalSeparationInhabitant
    {Language : Type}
    (P NP : Language → Prop) : Prop :=
  ∃ L : Language, NP L ∧ ¬ P L

end MCore.BackwardAudit
