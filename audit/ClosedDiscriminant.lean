import MCore.C12.Families

namespace MCore
namespace ClosedDiscriminant

/-- Established external wiring supplied to the closed envelope. -/
def StartClosed {Language : Type}
    (P NP : Language → Prop) : Prop :=
  ∀ L, P L → NP L

/-- The single binary discriminant: reverse inclusion NP ⊆ P. -/
def D {Language : Type}
    (P NP : Language → Prop) : Prop :=
  ∀ L, NP L → P L

/-- The opposite orientation expressed constructively as a witness. -/
def SeparationWitness {Language : Type}
    (P NP : Language → Prop) : Prop :=
  ∃ L, NP L ∧ ¬ P L

/-- Closed middle envelope: one of the two orientations. -/
def MiddleClosed {Language : Type}
    (P NP : Language → Prop) : Prop :=
  D P NP ∨ SeparationWitness P NP

/-- Equality endpoint. -/
def EqualityFinal {Language : Type}
    (P NP : Language → Prop) : Prop :=
  ∀ L, P L ↔ NP L

/-- Separation endpoint. -/
def SeparationFinal {Language : Type}
    (P NP : Language → Prop) : Prop :=
  ¬ EqualityFinal P NP

/-- Closed final envelope. -/
def FinalClosed {Language : Type}
    (P NP : Language → Prop) : Prop :=
  EqualityFinal P NP ∨ SeparationFinal P NP

theorem discriminant_implies_equality
    {Language : Type}
    {P NP : Language → Prop}
    (hStart : StartClosed P NP)
    (hD : D P NP) :
    EqualityFinal P NP := by
  intro L
  constructor
  · exact hStart L
  · exact hD L

theorem equality_implies_discriminant
    {Language : Type}
    {P NP : Language → Prop}
    (hEq : EqualityFinal P NP) :
    D P NP := by
  intro L hNP
  exact (hEq L).mpr hNP

theorem discriminant_iff_equality
    {Language : Type}
    {P NP : Language → Prop}
    (hStart : StartClosed P NP) :
    D P NP ↔ EqualityFinal P NP := by
  constructor
  · exact discriminant_implies_equality hStart
  · exact equality_implies_discriminant

theorem witness_implies_not_discriminant
    {Language : Type}
    {P NP : Language → Prop}
    (hW : SeparationWitness P NP) :
    ¬ D P NP := by
  intro hD
  rcases hW with ⟨L, hNP, hNotP⟩
  exact hNotP (hD L hNP)

theorem not_discriminant_implies_witness
    {Language : Type}
    {P NP : Language → Prop}
    (hNotD : ¬ D P NP) :
    SeparationWitness P NP := by
  exact Classical.byContradiction (fun hNoWitness => by
    apply hNotD
    intro L hNP
    exact Classical.byContradiction (fun hNotP =>
      hNoWitness ⟨L, hNP, hNotP⟩))

theorem not_discriminant_iff_witness
    {Language : Type}
    (P NP : Language → Prop) :
    (¬ D P NP) ↔ SeparationWitness P NP := by
  constructor
  · exact not_discriminant_implies_witness
  · exact witness_implies_not_discriminant

theorem middle_closed
    {Language : Type}
    (P NP : Language → Prop) :
    MiddleClosed P NP := by
  rcases Classical.em (D P NP) with hD | hNotD
  · exact Or.inl hD
  · exact Or.inr (not_discriminant_implies_witness hNotD)

theorem middle_exclusive
    {Language : Type}
    (P NP : Language → Prop) :
    ¬ (D P NP ∧ SeparationWitness P NP) := by
  intro h
  exact witness_implies_not_discriminant h.2 h.1

theorem witness_implies_separation_final
    {Language : Type}
    {P NP : Language → Prop}
    (hW : SeparationWitness P NP) :
    SeparationFinal P NP := by
  intro hEq
  exact witness_implies_not_discriminant hW (equality_implies_discriminant hEq)

theorem not_discriminant_implies_separation_final
    {Language : Type}
    {P NP : Language → Prop}
    (hNotD : ¬ D P NP) :
    SeparationFinal P NP :=
  witness_implies_separation_final (not_discriminant_implies_witness hNotD)

theorem final_closed
    {Language : Type}
    (P NP : Language → Prop) :
    FinalClosed P NP := by
  rcases Classical.em (EqualityFinal P NP) with hEq | hSep
  · exact Or.inl hEq
  · exact Or.inr hSep

theorem middle_to_final
    {Language : Type}
    {P NP : Language → Prop}
    (hStart : StartClosed P NP)
    (hMiddle : MiddleClosed P NP) :
    FinalClosed P NP := by
  rcases hMiddle with hD | hW
  · exact Or.inl (discriminant_implies_equality hStart hD)
  · exact Or.inr (witness_implies_separation_final hW)

/-- Fully closed start-middle-final envelope. This classifies the logical
space; it does not determine which orientation is mathematically true. -/
theorem closed_chain
    {Language : Type}
    {P NP : Language → Prop}
    (hStart : StartClosed P NP) :
    MiddleClosed P NP ∧ FinalClosed P NP := by
  have hMiddle := middle_closed P NP
  exact ⟨hMiddle, middle_to_final hStart hMiddle⟩

#print axioms discriminant_iff_equality
#print axioms not_discriminant_iff_witness
#print axioms middle_closed
#print axioms middle_exclusive
#print axioms middle_to_final
#print axioms closed_chain

end ClosedDiscriminant
end MCore
