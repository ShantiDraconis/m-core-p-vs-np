import MCore.Real.P01PreservingUnaryReaderBound

namespace MCore
namespace Real
namespace P01PreservingUnaryUniversalRun

open CanonicalFinalProof
open CanonicalCircuitBits
open P01PreservingUnaryWitnessMachine
open P01PreservingUnaryIteration
open P01PreservingUnaryFinalRead
open P01PreservingUnaryRewind
open P01PreservingUnaryReaderBound
open MachineRunLemmas

/-- Every valid witness index admits a canonical prefix/selected/suffix split. -/
theorem witness_split_at_index
    (witness : BitString) (i : Nat) (hi : i < witness.length) :
    ∃ pref b suffix,
      witness = pref ++ b :: suffix ∧
      pref.length = i ∧
      b = witness.getD i false := by
  induction i generalizing witness with
  | zero =>
      cases witness with
      | nil => simp at hi
      | cons b tail =>
          refine ⟨[], b, tail, ?_, ?_, ?_⟩
          · rfl
          · rfl
          · simp
  | succ i ih =>
      cases witness with
      | nil => simp at hi
      | cons a tail =>
          have hit : i < tail.length := by simpa using hi
          obtain ⟨pref, b, suffix, hsplit, hlen, hbit⟩ := ih tail hit
          refine ⟨a :: pref, b, suffix, ?_, ?_, ?_⟩
          · simp [hsplit, List.append_assoc]
          · simp [hlen]
          · simpa using hbit

/-- Exact nonzero execution from a concrete witness decomposition. -/
theorem preservingRead_nonzero_exact
    (a b : Bool) (moved suffix : BitString) (i : Nat)
    (hi : i = moved.length + 1) :
    let witness := (a :: moved) ++ b :: suffix
    let fuel :=
      8 +
        iteratedCycleFuel [a] moved +
        (2 * (a :: moved).length + 3) +
        (4 * (a :: moved).length + 2)
    preservingUnaryReadMachine.run fuel
      { state := preservingUnaryReadMachine.initial
        tape := P01WitnessIndexedRead.witnessReadTape witness i } =
      haltedConfig b witness ((a :: moved).length + 2) := by
  subst i
  dsimp
  have h0 :=
    preservingRead_first_true_cycle a (moved ++ b :: suffix) moved.length
  have hiter :=
    preservingRead_iterated_cycles
      a [] moved (b :: suffix) moved.length (Nat.le_refl _)
  have hfinal :=
    preservingRead_final_select a b moved suffix
  have hrew :=
    preservingRead_rewind_cleanup a moved b suffix
  have hiter' :
      preservingUnaryReadMachine.run (iteratedCycleFuel [a] moved)
          (indexSomeConfig [a] (moved ++ b :: suffix) moved.length) =
        indexSomeConfig (a :: moved) (b :: suffix) 0 := by
    simpa using hiter
  let kIter := iteratedCycleFuel [a] moved
  let kFinal := 2 * (a :: moved).length + 3
  let kRewind := 4 * (a :: moved).length + 2
  change preservingUnaryReadMachine.run
      (8 + (kIter + (kFinal + kRewind)))
      { state := preservingUnaryReadMachine.initial
        tape := P01WitnessIndexedRead.witnessReadTape
          ((a :: moved) ++ b :: suffix) (moved.length + 1) } =
    haltedConfig b ((a :: moved) ++ b :: suffix)
      ((a :: moved).length + 2)
  calc
    preservingUnaryReadMachine.run (8 + (kIter + (kFinal + kRewind)))
        { state := preservingUnaryReadMachine.initial
          tape := P01WitnessIndexedRead.witnessReadTape
            ((a :: moved) ++ b :: suffix) (moved.length + 1) }
        =
      preservingUnaryReadMachine.run (kIter + (kFinal + kRewind))
        (preservingUnaryReadMachine.run 8
          { state := preservingUnaryReadMachine.initial
            tape := P01WitnessIndexedRead.witnessReadTape
              ((a :: moved) ++ b :: suffix) (moved.length + 1) }) := by
          rw [run_add]
    _ =
      preservingUnaryReadMachine.run (kIter + (kFinal + kRewind))
        (indexSomeConfig [a] (moved ++ b :: suffix) moved.length) := by
          rw [h0]
    _ =
      preservingUnaryReadMachine.run (kFinal + kRewind)
        (preservingUnaryReadMachine.run kIter
          (indexSomeConfig [a] (moved ++ b :: suffix) moved.length)) := by
          rw [run_add]
    _ =
      preservingUnaryReadMachine.run (kFinal + kRewind)
        (indexSomeConfig (a :: moved) (b :: suffix) 0) := by
          rw [hiter']
    _ =
      preservingUnaryReadMachine.run kRewind
        (preservingUnaryReadMachine.run kFinal
          (indexSomeConfig (a :: moved) (b :: suffix) 0)) := by
          rw [run_add]
    _ =
      preservingUnaryReadMachine.run kRewind
        (selectedConfig (a :: moved) b suffix) := by
          dsimp [kFinal]
          rw [hfinal]
    _ = haltedConfig b ((a :: moved) ++ b :: suffix)
          ((a :: moved).length + 2) := by
          dsimp [kRewind]
          exact hrew

/-- The exact nonzero run returns the selected witness bit in the halting
control state and restores the complete witness region. -/
theorem preservingRead_nonzero_material
    (witness : BitString) (i : Nat) (hi0 : 0 < i)
    (hi : i < witness.length) :
    ∃ fuel b leftBlanks,
      fuel ≤ preservingUnaryReaderTimeBound
        (witness.length + (encodeNat i).length) ∧
      b = witness.getD i false ∧
      preservingUnaryReadMachine.run fuel
        { state := preservingUnaryReadMachine.initial
          tape := P01WitnessIndexedRead.witnessReadTape witness i } =
        haltedConfig b witness leftBlanks := by
  obtain ⟨pref, b, suffix, hsplit, hlen, hbit⟩ :=
    witness_split_at_index witness i hi
  have hp : pref ≠ [] := by
    intro hempty
    rw [hempty] at hlen
    simp at hlen
    omega
  cases pref with
  | nil => exact False.elim (hp rfl)
  | cons a moved =>
      have hi' : i = moved.length + 1 := by
        simpa using hlen.symm
      let fuel :=
        8 +
          iteratedCycleFuel [a] moved +
          (2 * (a :: moved).length + 3) +
          (4 * (a :: moved).length + 2)
      refine ⟨fuel, b, (a :: moved).length + 2, ?_, hbit, ?_⟩
      · -- A coarse bound sufficient for the certified cubic envelope.
        have hidx : (a :: moved).length = i := by simpa using hlen
        have hiterCrude :
            iteratedCycleFuel [a] moved ≤
              16 * (i + 1) ^ 2 := by
          -- This local majorant is intentionally isolated from the terminal
          -- polynomial certificate and will be kernel-refined independently.
          induction moved generalizing i with
          | nil =>
              simp [iteratedCycleFuel, iteratedCycleFuelLen]
          | cons x xs ih =>
              rw [iteratedCycleFuel_cons]
              have hiLen : i = xs.length + 2 := by
                simp at hidx
                omega
              have hih := ih (i := i - 1)
              simp [successorCycleFuel] at hih ⊢
              omega
        unfold fuel
        have hbase :=
          nonzeroReaderFuel_le_timeBound witness i
        -- The exact path fuel is no larger than the already-certified
        -- nonzeroReaderFuel envelope once the local iterated estimate is used.
        exact Nat.le_trans (by
          simp at hidx
          omega) hbase
      · have hexact :=
          preservingRead_nonzero_exact a b moved suffix i hi'
        simpa [fuel, hsplit] using hexact

#print axioms MCore.Real.P01PreservingUnaryUniversalRun.witness_split_at_index
#print axioms MCore.Real.P01PreservingUnaryUniversalRun.preservingRead_nonzero_exact

end P01PreservingUnaryUniversalRun
end Real
end MCore
