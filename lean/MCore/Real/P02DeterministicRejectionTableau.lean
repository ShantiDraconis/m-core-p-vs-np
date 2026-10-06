import MCore.Real.PNPNTMTableauEncoding
import MCore.Real.CanonicalPSubsetNP

namespace MCore
namespace Real
namespace P02DeterministicRejectionTableau

open CanonicalFinalProof
open CanonicalPSubsetNP
open PNPNTMTableauEncoding

/-- Deterministic embedding with terminal labels swapped.
Transitions and stopping states are unchanged; only accept/reject meaning flips. -/
def complementToNTM
    (M : PolyDTMCandidate) :
    NTM (Fin (M.stateCount + 1)) (Option Bool) :=
  let B := CanonicalPSubsetNP.toNTM M
  { initial := B.initial
    blank := B.blank
    transition := B.transition
    accepting := B.rejecting
    rejecting := B.accepting }

theorem complement_stop_eq_base_stop
    (M : PolyDTMCandidate)
    (q : Fin (M.stateCount + 1)) :
    ((complementToNTM M).accepting q ||
      (complementToNTM M).rejecting q) =
    ((CanonicalPSubsetNP.toNTM M).accepting q ||
      (CanonicalPSubsetNP.toNTM M).rejecting q) := by
  simp [complementToNTM, Bool.or_comm]

theorem complement_successors_eq
    (M : PolyDTMCandidate)
    (config :
      Configuration
        (Fin (M.stateCount + 1))
        (Option Bool)) :
    (complementToNTM M).successors config =
      (CanonicalPSubsetNP.toNTM M).successors config := by
  rfl

theorem complement_runBranches_eq
    (M : PolyDTMCandidate)
    (fuel : Nat)
    (configs :
      List
        (Configuration
          (Fin (M.stateCount + 1))
          (Option Bool))) :
    (complementToNTM M).runBranches fuel configs =
      (CanonicalPSubsetNP.toNTM M).runBranches fuel configs := by
  induction fuel generalizing configs with
  | zero =>
      rfl
  | succ n ih =>
      simp only [NTM.runBranches]
      have hpred :
          (fun c : Configuration (Fin (M.stateCount + 1)) (Option Bool) =>
            ((complementToNTM M).accepting c.state ||
              (complementToNTM M).rejecting c.state)) =
          (fun c : Configuration (Fin (M.stateCount + 1)) (Option Bool) =>
            ((CanonicalPSubsetNP.toNTM M).accepting c.state ||
              (CanonicalPSubsetNP.toNTM M).rejecting c.state)) := by
        funext c
        exact complement_stop_eq_base_stop M c.state
      rw [hpred]
      have hsucc :
          (fun c : Configuration (Fin (M.stateCount + 1)) (Option Bool) =>
            (complementToNTM M).successors c) =
          (fun c : Configuration (Fin (M.stateCount + 1)) (Option Bool) =>
            (CanonicalPSubsetNP.toNTM M).successors c) := by
        funext c
        exact complement_successors_eq M c
      rw [hsucc]
      exact ih _

def complementCandidate
    (M : PolyDTMCandidate) :
    PolyNTMCandidate :=
  { stateCount := M.stateCount
    machine := complementToNTM M
    blank_none := M.blank_none
    timeBound := M.timeBound
    time_poly := M.time_poly }

theorem complement_runBranches_to_tm_run
    (M : PolyDTMCandidate)
    (fuel : Nat)
    (config :
      Configuration
        (Fin (M.stateCount + 1))
        (Option Bool)) :
    (complementToNTM M).runBranches fuel [config] =
      [M.machine.run fuel config] := by
  rw [complement_runBranches_eq]
  exact CanonicalPSubsetNP.runBranches_to_tm_run M fuel config

theorem complement_acceptsWithin_iff_rejects_at_fuel
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) :
    (complementToNTM M).AcceptsWithin t
        (initialNTMConfig (complementToNTM M) x) ↔
      M.machine.HaltsWithin t (initialTMConfig M.machine x) ∧
      M.accepting
        (M.machine.run t (initialTMConfig M.machine x)).state = false := by
  rw [show initialNTMConfig (complementToNTM M) x =
      initialTMConfig M.machine x by rfl]
  constructor
  · rintro ⟨reached, hmem, hacc⟩
    rw [complement_runBranches_to_tm_run M t
      (initialTMConfig M.machine x)] at hmem
    have hreached :
        reached = M.machine.run t (initialTMConfig M.machine x) := by
      simpa using hmem
    subst reached
    have hterm :
        M.machine.halting
          (M.machine.run t (initialTMConfig M.machine x)).state = true ∧
        M.accepting
          (M.machine.run t (initialTMConfig M.machine x)).state = false := by
      simpa [complementToNTM, CanonicalPSubsetNP.toNTM,
        Bool.and_eq_true] using hacc
    exact ⟨hterm.1, hterm.2⟩
  · rintro ⟨hhalt, hrejected⟩
    refine ⟨M.machine.run t (initialTMConfig M.machine x), ?_, ?_⟩
    · rw [complement_runBranches_to_tm_run M t
        (initialTMConfig M.machine x)]
      simp
    · simp [complementToNTM, CanonicalPSubsetNP.toNTM,
        hhalt, hrejected]

/-- Concrete SAT circuit whose satisfiability means that the deterministic
candidate has halted and rejected the supplied input within the given fuel. -/
def boundedRejectCircuit_DTM
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) : Circuit :=
  boundedExecCircuit_NTM (complementCandidate M) x t

theorem rejection_tableau_correctness
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) :
    SATLanguage (boundedRejectCircuit_DTM M x t) ↔
      M.machine.HaltsWithin t (initialTMConfig M.machine x) ∧
      M.accepting
        (M.machine.run t (initialTMConfig M.machine x)).state = false := by
  rw [show boundedRejectCircuit_DTM M x t =
      boundedExecCircuit_NTM (complementCandidate M) x t by rfl]
  rw [tableau_correctness_iff]
  exact complement_acceptsWithin_iff_rejects_at_fuel M x t

theorem rejection_tableau_encoded_length_poly
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) :
    (encodeCircuit (boundedRejectCircuit_DTM M x t)).length ≤
      tableauEncodingCoeff (complementCandidate M) *
        (x.length + t + 1)^4 := by
  exact boundedExec_encoded_length_poly (complementCandidate M) x t

#print axioms MCore.Real.P02DeterministicRejectionTableau.complement_runBranches_eq
#print axioms MCore.Real.P02DeterministicRejectionTableau.complement_acceptsWithin_iff_rejects_at_fuel
#print axioms MCore.Real.P02DeterministicRejectionTableau.rejection_tableau_correctness
#print axioms MCore.Real.P02DeterministicRejectionTableau.rejection_tableau_encoded_length_poly

end P02DeterministicRejectionTableau
end Real
end MCore
