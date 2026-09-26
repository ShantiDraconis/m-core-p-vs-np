import MCore.Real.P02LowerBoundProducer

namespace MCore
namespace Real
namespace P02OpenMathClosure

open CanonicalFinalProof
open FailProofAllGaps
open CanonicalSATBoundary
open CanonicalCircuitBits
open P02LowerBoundProducer

/-- A route is decided either positively, with a witness, or negatively,
with a refutation. -/
inductive Decided (P : Prop) where
  | positive (h : P)
  | negative (h : ¬ P)

/-- Only the three user-admissible closures exist.
There is deliberately no constructor for TRUE/TRUE. -/
inductive ClosureResult (A B : Prop) where
  | positiveLeft  (ha : A) (hnb : ¬ B)
  | positiveRight (hna : ¬ A) (hb : B)
  | negativeBoth  (hna : ¬ A) (hnb : ¬ B)

/-- The forbidden state is exactly simultaneous truth. -/
def Admissible (A B : Prop) : Prop := ¬ (A ∧ B)

theorem close_decided
    {A B : Prop}
    (a : Decided A)
    (b : Decided B)
    (hAdmissible : Admissible A B) :
    ClosureResult A B := by
  cases a with
  | positive ha =>
      cases b with
      | positive hb =>
          exact False.elim (hAdmissible ⟨ha, hb⟩)
      | negative hnb =>
          exact .positiveLeft ha hnb
  | negative hna =>
      cases b with
      | positive hb =>
          exact .positiveRight hna hb
      | negative hnb =>
          exact .negativeBoth hna hnb

/-- Positive closure payload: at least one route really produces the canonical
SAT failure generator. -/
def ProducesFailure (A B : Prop)
    (left : A → FailureGenerator (SATBits circuitBitEncoding))
    (right : B → FailureGenerator (SATBits circuitBitEncoding))
    (r : ClosureResult A B) : Prop :=
  match r with
  | .positiveLeft ha _ => Nonempty (FailureGenerator (SATBits circuitBitEncoding))
  | .positiveRight _ hb => Nonempty (FailureGenerator (SATBits circuitBitEncoding))
  | .negativeBoth _ _ => False

theorem positiveLeft_produces_failure
    {A B : Prop}
    (left : A → FailureGenerator (SATBits circuitBitEncoding))
    (right : B → FailureGenerator (SATBits circuitBitEncoding))
    (ha : A) (hnb : ¬ B) :
    ProducesFailure A B left right (.positiveLeft ha hnb) := by
  exact ⟨left ha⟩

theorem positiveRight_produces_failure
    {A B : Prop}
    (left : A → FailureGenerator (SATBits circuitBitEncoding))
    (right : B → FailureGenerator (SATBits circuitBitEncoding))
    (hna : ¬ A) (hb : B) :
    ProducesFailure A B left right (.positiveRight hna hb) := by
  exact ⟨right hb⟩

/-- A positive closure enables the existing separation theorem. -/
theorem closure_enables_pneqnp
    {A B : Prop}
    (left : A → FailureGenerator (SATBits circuitBitEncoding))
    (right : B → FailureGenerator (SATBits circuitBitEncoding))
    (hNP : SATInNPGap circuitBitEncoding)
    (r : ClosureResult A B)
    (hProd : ProducesFailure A B left right r) :
    PneqNP := by
  cases r with
  | positiveLeft ha hnb =>
      exact sat_internal_closure_implies_p_ne_np
        { encoding := circuitBitEncoding
          sat_in_np := hNP
          fail_generator := left ha }
  | positiveRight hna hb =>
      exact sat_internal_closure_implies_p_ne_np
        { encoding := circuitBitEncoding
          sat_in_np := hNP
          fail_generator := right hb }
  | negativeBoth hna hnb =>
      exact False.elim hProd

/-- FALSE/FALSE closes the selected two-route search negatively. It does not
assert P != NP and therefore cannot manufacture the final theorem. -/
theorem false_false_is_closed_negative
    {A B : Prop}
    (hna : ¬ A) (hnb : ¬ B) :
    ClosureResult A B :=
  .negativeBoth hna hnb

/-- TRUE/TRUE is excluded by the admissibility invariant. -/
theorem true_true_impossible
    {A B : Prop}
    (hAdmissible : Admissible A B)
    (ha : A) (hb : B) :
    False :=
  hAdmissible ⟨ha, hb⟩

#print axioms MCore.Real.P02OpenMathClosure.close_decided
#print axioms MCore.Real.P02OpenMathClosure.closure_enables_pneqnp
#print axioms MCore.Real.P02OpenMathClosure.false_false_is_closed_negative
#print axioms MCore.Real.P02OpenMathClosure.true_true_impossible

end P02OpenMathClosure
end Real
end MCore
