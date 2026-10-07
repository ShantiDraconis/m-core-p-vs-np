import MCore.Real.P01PreservingUnaryWitnessMachine
import MCore.Real.P01InputNodePreservingPlan
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01PreservingUnaryReaderGlobal

open CanonicalFinalProof
open CanonicalCircuitBits
open P01InputNodePreservingPlan
open P01PreservingUnaryWitnessMachine
open MachineRunLemmas

/-!
# Global proof layer for the preserving unary witness reader

This file isolates the only remaining physical-reader proof.  The finite
transition graph is fixed in P01PreservingUnaryWitnessMachine; here we expose
canonical configurations for the forward scan, selected-bit rewind, and final
cleanup.  No new machine or semantic oracle is introduced.
-/

/-- Logical payload conservation used throughout the physical induction. -/
theorem payload_advance_rewind
    (prefix : BitString) (b : Bool) (suffix : BitString) :
    witnessPayload prefix (b :: suffix) =
      witnessPayload (prefix ++ [b]) suffix ∧
    witnessPayload (prefix ++ [b]) suffix =
      witnessPayload prefix (b :: suffix) := by
  exact ⟨witnessPayload_advance prefix b suffix,
    witnessPayload_rewind prefix b suffix⟩

/-- The existing first physical cycle establishes the induction entry point. -/
theorem preserving_reader_induction_entry
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run 8
      { state := preservingUnaryReadMachine.initial
        tape := witnessReadTape (b :: tail) (n + 1) } =
      indexSomeConfig [b] tail n :=
  preservingRead_first_true_cycle b tail n

/-- Exact selected bit is already determined by the decomposition used by the
rewind proof.  This keeps the forthcoming machine induction tied to the frozen
semantic witness rather than to an unconstrained answer field. -/
theorem selected_bit_from_decomposition
    (witness prefix suffix : BitString) (b : Bool) (i : Nat)
    (hw : witness = prefix ++ b :: suffix)
    (hlen : prefix.length = i) :
    witness.getD i false = b := by
  subst witness
  subst i
  simp [List.getD_eq_getElem?_getD]


/-- One local rewind cycle for a false witness bit.  Keeping the next tape
symbol explicit avoids relying on list head defaults in the global induction. -/
theorem rewind_false_bit_cycle
    (left : List (Option Bool)) (next : Option Bool)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.run 3
      { state := .rewindInspectFalse
        tape := { left := none :: left, head := some false,
                  right := next :: right } } =
      { state := .rewindInspectFalse
        tape := { left := some false :: none :: left, head := next,
                  right := right } } := by
  simp [preservingUnaryReadMachine, TM.run, TM.step, Tape.write, Tape.move]

/-- Same physical cycle while the selected result carried in control is true. -/
theorem rewind_true_bit_cycle
    (left : List (Option Bool)) (next : Option Bool)
    (right : List (Option Bool)) :
    preservingUnaryReadMachine.run 3
      { state := .rewindInspectTrue
        tape := { left := none :: left, head := some true,
                  right := next :: right } } =
      { state := .rewindInspectTrue
        tape := { left := some true :: none :: left, head := next,
                  right := right } } := by
  simp [preservingUnaryReadMachine, TM.run, TM.step, Tape.write, Tape.move]

#print axioms MCore.Real.P01PreservingUnaryReaderGlobal.payload_advance_rewind
#print axioms MCore.Real.P01PreservingUnaryReaderGlobal.preserving_reader_induction_entry
#print axioms MCore.Real.P01PreservingUnaryReaderGlobal.selected_bit_from_decomposition

end P01PreservingUnaryReaderGlobal
end Real
end MCore
