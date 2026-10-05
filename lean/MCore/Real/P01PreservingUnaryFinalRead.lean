import MCore.Real.P01PreservingUnarySuccessorCycle

namespace MCore
namespace Real
namespace P01PreservingUnaryFinalRead

open CanonicalFinalProof
open CanonicalCircuitBits
open P01PreservingUnaryWitnessMachine
open MachineRunLemmas

/-- Canonical state immediately after the selected witness bit has been read.
The selected bit is preserved on Tape.left; the marker is under the head; the
traversed prefix appears reversed on Tape.right, followed by erased unary
blanks and the original false terminator. -/
def selectedConfig
    (pref : BitString) (b : Bool) (suffix : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  { state := if b then .selectedTrue else .selectedFalse
    tape :=
      { left := some b :: suffix.map some
        head := none
        right :=
          pref.reverse.map some ++
            List.replicate pref.length none ++ [some false] } }

@[simp] theorem finalSeekBlanks_not_halting :
    preservingUnaryReadMachine.halting .finalSeekBlanks = false := rfl

@[simp] theorem finalSeekBits_not_halting :
    preservingUnaryReadMachine.halting .finalSeekBits = false := rfl

@[simp] theorem finalRead_not_halting :
    preservingUnaryReadMachine.halting .finalRead = false := rfl

/-- Exact final-read theorem for every reachable nonempty traversed prefix. -/
theorem preservingRead_final_select
    (a b : Bool) (rest suffix : BitString) :
    preservingUnaryReadMachine.run (2 * (a :: rest).length + 3)
      (indexSomeConfig (a :: rest) (b :: suffix) 0) =
      selectedConfig (a :: rest) b suffix := by
  induction rest generalizing a with
  | nil =>
      cases a <;> cases b <;>
        simp [indexSomeConfig, encodeNat, selectedConfig,
          preservingUnaryReadMachine, TM.run, TM.step,
          Tape.write, Tape.move, List.replicate_succ,
          List.append_assoc]
  | cons c rest ih =>
      cases a <;> cases c <;> cases b <;>
        simp [indexSomeConfig, encodeNat, selectedConfig,
          preservingUnaryReadMachine, TM.run, TM.step,
          Tape.write, Tape.move, List.replicate_succ,
          List.reverse_cons, List.map_append,
          List.append_assoc] at ih ⊢

#print axioms MCore.Real.P01PreservingUnaryFinalRead.preservingRead_final_select

end P01PreservingUnaryFinalRead
end Real
end MCore
