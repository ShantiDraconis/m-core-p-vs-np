import MCore.K10
import MCore.BackwardAudit.OrientedWitnessBoundary

namespace MCore
namespace Real
namespace P02WitnessChain

/--
Canonical importable name for the separation witness needed by the P02 lane.
This is deliberately an alias of the already-audited LowerBoundWitness rather
than a new mathematical assumption.
-/
abbrev UniversalWitness {Language : Type}
    (C : ClassicalComplexityInterface Language) :=
  BackwardAudit.LowerBoundWitness C.inP C.inNP

/-- Exact existence producer for the separation lane. This is a proposition,
not an axiom and not a theorem asserting that a witness exists. -/
def UniversalWitnessExists {Language : Type}
    (C : ClassicalComplexityInterface Language) : Prop :=
  Nonempty (UniversalWitness C)

/-- Pointwise/core form of the G2.1 lower-bound payload for one fixed model. -/
def G21PointwiseCore {Language : Type}
    (C : ClassicalComplexityInterface Language) : Prop :=
  ∃ L : Language, C.inNP L ∧ ¬ C.inP L

/-- Endpoint/core form used locally by this adapter layer. -/
def P02TargetCore {Language : Type}
    (C : ClassicalComplexityInterface Language) : Prop :=
  ¬ (∀ L : Language, C.inP L ↔ C.inNP L)

/--
Importable fixed-model form of the historical audit/EndpointCompression
FixedK10WitnessData structure.
-/
structure FixedK10WitnessDataCore {Language : Type}
    (C : ClassicalComplexityInterface Language) where
  α : Type
  Value : Type
  data : SeparationWitnessData Language α Value
  classical_eq : data.interface.classical = C

/-- K10 witness data already contains exactly the lower-bound witness payload. -/
def k10DataToUniversalWitness
    {Language α Value : Type}
    (W : SeparationWitnessData Language α Value) :
    UniversalWitness W.interface.classical :=
  { language := W.witness
    in_np := W.witness_in_np
    not_in_p := separation_witness_not_in_P W }

/-- Adapter from the fixed-model K10 packaging to the canonical universal witness. -/
def fixedK10ToUniversalWitness
    {Language : Type}
    {C : ClassicalComplexityInterface Language}
    (W : FixedK10WitnessDataCore C) :
    UniversalWitness C := by
  rcases W with ⟨α, Value, data, hclassical⟩
  cases hclassical
  exact k10DataToUniversalWitness data

/-- Existing LowerBoundWitness and UniversalWitness are definitionally the same payload. -/
def lowerBoundWitnessToUniversal
    {Language : Type}
    {C : ClassicalComplexityInterface Language}
    (W : BackwardAudit.LowerBoundWitness C.inP C.inNP) :
    UniversalWitness C :=
  W

theorem universalWitnessExists_iff_g21PointwiseCore
    {Language : Type}
    (C : ClassicalComplexityInterface Language) :
    UniversalWitnessExists C ↔ G21PointwiseCore C := by
  constructor
  · intro h
    rcases h with ⟨W⟩
    exact ⟨W.language, W.in_np, W.not_in_p⟩
  · rintro ⟨L, hNP, hNotP⟩
    exact ⟨{ language := L, in_np := hNP, not_in_p := hNotP }⟩

/-- The pointwise lower-bound payload closes the local P02 endpoint. -/
theorem g21PointwiseCore_to_p02TargetCore
    {Language : Type}
    {C : ClassicalComplexityInterface Language}
    (h : G21PointwiseCore C) :
    P02TargetCore C := by
  rcases h with ⟨L, hNP, hNotP⟩
  intro hEq
  exact hNotP ((hEq L).mpr hNP)

/-- The requested visible chain: existence producer -> G2.1 pointwise -> P02. -/
theorem universalWitnessExists_to_p02TargetCore
    {Language : Type}
    {C : ClassicalComplexityInterface Language}
    (h : UniversalWitnessExists C) :
    P02TargetCore C :=
  g21PointwiseCore_to_p02TargetCore
    ((universalWitnessExists_iff_g21PointwiseCore C).mp h)

/--
The sole open mathematical producer in this adapter chain.
Keeping it as a named proposition makes the missing payload explicit and
prevents the downstream wiring from being mistaken for an existence proof.
-/
def UniversalWitnessProducer {Language : Type}
    (C : ClassicalComplexityInterface Language) : Prop :=
  UniversalWitnessExists C

#print axioms universalWitnessExists_iff_g21PointwiseCore
#print axioms g21PointwiseCore_to_p02TargetCore
#print axioms universalWitnessExists_to_p02TargetCore

end P02WitnessChain
end Real
end MCore
