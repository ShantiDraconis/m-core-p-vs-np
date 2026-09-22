import Mathlib
import MCore.Real.P01FullVerifierPhysicalControl

namespace MCore.Real.OpenMathCore

open P01FullVerifierPhysicalControl

structure TransitionInvariant
    {Q Γ : Type}
    (step : Q → Γ → Q × Γ) where
  invariant : Q → Γ → Prop
  preserved :
    ∀ q g, invariant q g → invariant (step q g).1 (step q g).2

def scannerStateInvariant
    (q : VerifierState) (_ : Option Bool) : Prop :=
  q = scanEncode ∨ q = decodeInstr ∨ q = halt

theorem scanner_transition_preserves_phase_set
    (q : VerifierState) (s : Option Bool)
    (h : scannerStateInvariant q s) :
    scannerStateInvariant
      (physicalControlMachine.transition q s).1
      (physicalControlMachine.transition q s).2 := by
  rcases h with hq | hq | hq
  · subst q
    cases s <;> simp [scannerStateInvariant, physicalControlMachine, scanEncode, decodeInstr, halt]
  · subst q
    simp [scannerStateInvariant, physicalControlMachine, scanEncode, decodeInstr, halt]
  · subst q
    simp [scannerStateInvariant, physicalControlMachine, scanEncode, decodeInstr, halt]

structure ConservationLaw (α : Type) where
  quantity : α → Nat
  transition : α → α
  conserved : ∀ x, quantity (transition x) = quantity x

end MCore.Real.OpenMathCore
