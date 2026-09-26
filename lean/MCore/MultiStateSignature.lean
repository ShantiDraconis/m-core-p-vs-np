import MCore.Signature

namespace MCore
namespace SharedSignature

structure MultiStateSignatureShape where
  Phase : Type
  related : Phase → Phase → Prop
  marked : Phase → Prop

structure ProblemManifestation
    (Problem : Type)
    (shape : MultiStateSignatureShape)
    (p : Problem) where
  Value : Type
  State : Type
  value : Value
  observable : State → Value
  phase : State → shape.Phase
  realizes :
    ∃ a b : State,
      a ≠ b ∧
      observable a = value ∧
      observable b = value ∧
      shape.related (phase a) (phase b)

structure SharedMultiStateSignature (Problem : Type) where
  shape : MultiStateSignatureShape
  manifestation : ∀ p : Problem, ProblemManifestation Problem shape p

def UniversalSharedMultiStateSignature (Problem : Type) : Prop :=
  Nonempty (SharedMultiStateSignature Problem)

theorem shared_shape_problem_specific_manifestations
    {Problem : Type}
    (S : SharedMultiStateSignature Problem) :
    ∃ shape : MultiStateSignatureShape,
      ∀ p : Problem,
        Nonempty (ProblemManifestation Problem shape p) := by
  refine ⟨S.shape, ?_⟩
  intro p
  exact ⟨S.manifestation p⟩

theorem universal_shared_signature_iff
    {Problem : Type} :
    UniversalSharedMultiStateSignature Problem ↔
      ∃ shape : MultiStateSignatureShape,
        ∀ p : Problem,
          Nonempty (ProblemManifestation Problem shape p) := by
  constructor
  · rintro ⟨S⟩
    exact shared_shape_problem_specific_manifestations S
  · rintro ⟨shape, h⟩
    classical
    refine ⟨{
      shape := shape
      manifestation := fun p => Classical.choice (h p)
    }⟩

#print axioms MCore.SharedSignature.shared_shape_problem_specific_manifestations
#print axioms MCore.SharedSignature.universal_shared_signature_iff

end SharedSignature
end MCore
