import MCore.Real.P01PreservingUnarySuccessorCycle

namespace MCore
namespace Real
namespace P01PreservingUnaryIteration

open CanonicalFinalProof
open CanonicalCircuitBits
open P01PreservingUnaryWitnessMachine
open P01PreservingUnarySuccessorCycle
open MachineRunLemmas

/-- Total fuel for repeatedly advancing the preserving reader across exactly
    the moved Boolean prefix. -/
def iteratedCycleFuel : BitString → BitString → Nat
  | pref, [] => 0
  | pref, _ :: rest =>
      successorCycleFuel pref + iteratedCycleFuel (pref ++ [false]) rest

/-- Fuel depends only on prefix lengths, not Boolean values. -/
theorem iteratedCycleFuel_cons_value_irrel
    (pref : BitString) (b c : Bool) (rest : BitString) :
    iteratedCycleFuel (pref ++ [b]) rest =
      iteratedCycleFuel (pref ++ [c]) rest := by
  induction rest generalizing pref with
  | nil => rfl
  | cons x xs ih =>
      simp [iteratedCycleFuel, successorCycleFuel]
      have hlen : (pref ++ [b]).length = (pref ++ [c]).length := by simp
      rw [hlen]
      simpa [List.append_assoc] using
        ih (pref := pref ++ [false]) (b := b) (c := c)

/-- Iterating the exact one-cycle law moves the marker across every bit in
    moved, preserving the remaining suffix and decreasing the unary index by
    exactly moved.length. -/
theorem preservingRead_iterated_cycles
    (a : Bool) (seed moved suffix : BitString) (n : Nat)
    (hcount : moved.length ≤ n) :
    preservingUnaryReadMachine.run
        (iteratedCycleFuel (a :: seed) moved)
        (indexSomeConfig (a :: seed) (moved ++ suffix) n) =
      indexSomeConfig ((a :: seed) ++ moved) suffix (n - moved.length) := by
  induction moved generalizing a seed n with
  | nil =>
      simp [iteratedCycleFuel]
  | cons b rest ih =>
      have hn : 0 < n := by
        have : 0 < (b :: rest).length := by simp
        omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      have hrest : rest.length ≤ k := by
        simpa using hcount
      simp [iteratedCycleFuel]
      rw [run_add]
      rw [preservingRead_indexSome_one_cycle]
      have hih :=
        ih (a := a) (seed := seed ++ [b]) (n := k) hrest
      simpa [List.append_assoc, Nat.succ_sub (Nat.succ_le_succ hrest)] using hih

#print axioms MCore.Real.P01PreservingUnaryIteration.preservingRead_iterated_cycles

end P01PreservingUnaryIteration
end Real
end MCore
