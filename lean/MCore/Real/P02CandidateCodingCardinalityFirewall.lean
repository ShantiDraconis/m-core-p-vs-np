import Mathlib
import MCore.Real.P02CandidateCodingFrontier

namespace MCore.Real.P02CandidateCodingFrontier

open CanonicalFinalProof

def codingFirewallMachine : TM (Fin 1) (Option Bool) where
  initial := 0
  blank := none
  transition := fun s a => (s, a, .stay)
  halting := fun _ => true

def codingFirewallTimeBound (b : Nat → Bool) : TimeBound :=
  fun n => if b n then 1 else 0

theorem codingFirewallTimeBound_poly (b : Nat → Bool) :
    PolynomialTimeBound (codingFirewallTimeBound b) := by
  refine ⟨1, 0, ?_⟩
  intro n
  simp [codingFirewallTimeBound]
  split <;> omega

def codingFirewallCandidate (b : Nat → Bool) : PolyDTMCandidate where
  stateCount := 0
  machine := codingFirewallMachine
  blank_none := rfl
  accepting := fun _ => false
  timeBound := codingFirewallTimeBound b
  time_poly := codingFirewallTimeBound_poly b

theorem codingFirewallCandidate_injective :
    Function.Injective codingFirewallCandidate := by
  intro b c h
  funext n
  have hn := congrFun (congrArg PolyDTMCandidate.timeBound h) n
  change codingFirewallTimeBound b n = codingFirewallTimeBound c n at hn
  cases hb : b n <;> cases hc : c n <;>
    simp_all [codingFirewallTimeBound]

instance boolSequence_uncountable : Uncountable (Nat → Bool) := by
  rw [uncountable_iff_forall_not_surjective]
  intro f hsurj
  let diagonal : Nat → Bool := fun n => !(f n n)
  rcases hsurj diagonal with ⟨n, hn⟩
  have hpoint := congrFun hn n
  simp [diagonal] at hpoint

instance polyDTMCandidate_uncountable : Uncountable PolyDTMCandidate :=
  codingFirewallCandidate_injective.uncountable

theorem candidateCodingInterface_impossible :
    ¬ Nonempty CandidateCodingInterface := by
  rintro ⟨C⟩
  exact not_injective_uncountable_countable C.encode (encode_injective C)

#print axioms MCore.Real.P02CandidateCodingFrontier.candidateCodingInterface_impossible

end MCore.Real.P02CandidateCodingFrontier
