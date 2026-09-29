import MCore.Real.P01WitnessIndexedRead
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01WitnessIndexedReadPreserving

open CanonicalFinalProof
open CanonicalSATWitness
open P01WitnessIndexedRead
open MachineRunLemmas

/-- Fixed finite control for a preserving unary-index witness read.

The machine never stores the unbounded index in control.  Each consumed unary
true marker advances a blank separator one witness cell to the left.  The
already-crossed witness prefix is moved, not erased.  At the false terminator
the selected witness bit is read, then the separator is moved back to its
original position, restoring the witness exactly. -/
inductive PreservingReadState where
  | indexNoMoved
  | indexMoved
  | advanceSep
  | seekMoved
  | scanMoved
  | capture
  | writeMoved : Bool → PreservingReadState
  | returnMoved
  | returnBlanks
  | finalSepNoMoved
  | finalReadNoMoved
  | finalSeekMoved
  | finalScanMoved
  | finalReadMoved
  | restoreStart : Bool → PreservingReadState
  | restoreInspect : Bool → PreservingReadState
  | restoreWrite : Bool → Bool → PreservingReadState
  | restoreHalt : Bool → PreservingReadState
  | halt : Bool → PreservingReadState
  | reject
  deriving DecidableEq, Repr

/-- The preserving reader.  It uses only the canonical tape alphabet
`Option Bool`: no extra marker symbol is introduced. -/
def preservingReadMachine : TM PreservingReadState (Option Bool) where
  initial := .indexNoMoved
  blank := none
  transition := fun q symbol =>
    match q with
    | .indexNoMoved =>
        match symbol with
        | some true => (.advanceSep, none, .left)
        | some false => (.finalSepNoMoved, none, .left)
        | none => (.reject, none, .stay)
    | .indexMoved =>
        match symbol with
        | some true => (.seekMoved, none, .left)
        | some false => (.finalSeekMoved, none, .left)
        | none => (.reject, none, .stay)
    | .advanceSep =>
        match symbol with
        | none => (.capture, none, .left)
        | some b => (.reject, some b, .stay)
    | .seekMoved =>
        match symbol with
        | none => (.seekMoved, none, .left)
        | some b => (.scanMoved, some b, .left)
    | .scanMoved =>
        match symbol with
        | some b => (.scanMoved, some b, .left)
        | none => (.capture, none, .left)
    | .capture =>
        match symbol with
        | some b => (.writeMoved b, none, .right)
        | none => (.reject, none, .stay)
    | .writeMoved b =>
        match symbol with
        | none => (.returnMoved, some b, .right)
        | some c => (.reject, some c, .stay)
    | .returnMoved =>
        match symbol with
        | some b => (.returnMoved, some b, .right)
        | none => (.returnBlanks, none, .right)
    | .returnBlanks =>
        match symbol with
        | none => (.returnBlanks, none, .right)
        | some b => (.indexMoved, some b, .stay)
    | .finalSepNoMoved =>
        match symbol with
        | none => (.finalReadNoMoved, none, .left)
        | some b => (.reject, some b, .stay)
    | .finalReadNoMoved =>
        match symbol with
        | some b => (.restoreHalt b, some b, .right)
        | none => (.reject, none, .stay)
    | .finalSeekMoved =>
        match symbol with
        | none => (.finalSeekMoved, none, .left)
        | some b => (.finalScanMoved, some b, .left)
    | .finalScanMoved =>
        match symbol with
        | some b => (.finalScanMoved, some b, .left)
        | none => (.finalReadMoved, none, .left)
    | .finalReadMoved =>
        match symbol with
        | some b => (.restoreStart b, some b, .right)
        | none => (.reject, none, .stay)
    | .restoreStart result =>
        match symbol with
        | none => (.restoreInspect result, none, .right)
        | some b => (.reject, some b, .stay)
    | .restoreInspect result =>
        match symbol with
        | some b => (.restoreWrite result b, none, .left)
        | none => (.restoreHalt result, none, .left)
    | .restoreWrite result b =>
        match symbol with
        | none => (.restoreStart result, some b, .right)
        | some c => (.reject, some c, .stay)
    | .restoreHalt result =>
        match symbol with
        | none => (.halt result, none, .stay)
        | some b => (.reject, some b, .stay)
    | .halt result => (.halt result, symbol, .stay)
    | .reject => (.reject, symbol, .stay)
  halting := fun q =>
    match q with
    | .halt _ => true
    | .reject => true
    | _ => false

@[simp] theorem preservingReadMachine_blank :
    preservingReadMachine.blank = none := rfl

@[simp] theorem preservingReadMachine_halt (b : Bool) :
    preservingReadMachine.halting (.halt b) = true := rfl

@[simp] theorem preservingReadMachine_reject :
    preservingReadMachine.halting .reject = true := rfl

/-- Canonical input layout for the preserving reader.  The unary index remains
the physical counter; `tail` is arbitrary unread source data and is never part
of finite control. -/
def preservingReadTape
    (witness : BitString) (i : Nat) (tail : BitString) :
    Tape (Option Bool) :=
  match encodeNat i ++ tail with
  | [] =>
      { left := none :: witness.map some, head := none, right := [] }
  | b :: bs =>
      { left := none :: witness.map some,
        head := some b,
        right := bs.map some }

/-- Zero-index read is already completely non-destructive: the false unary
terminator is consumed, while the witness cell itself is only inspected. -/
theorem preservingRead_zero
    (b : Bool) (witnessTail tail : BitString) :
    preservingReadMachine.run 4
      { state := preservingReadMachine.initial,
        tape := preservingReadTape (b :: witnessTail) 0 tail } =
      { state := .halt b,
        tape :=
          { left := (b :: witnessTail).map some,
            head := none,
            right := none :: tail.map some } } := by
  cases b <;>
    simp [preservingReadMachine, preservingReadTape, encodeNat,
      TM.run, TM.step, Tape.write, Tape.move]

/-- The zero-index theorem already shows the key preservation property: the
selected bit and the untouched witness tail remain physically present. -/
theorem preservingRead_zero_value
    (b : Bool) (witnessTail tail : BitString) :
    (preservingReadMachine.run 4
      { state := preservingReadMachine.initial,
        tape := preservingReadTape (b :: witnessTail) 0 tail }).state =
      .halt b := by
  rw [preservingRead_zero]

#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingRead_zero
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingRead_zero_value

end P01WitnessIndexedReadPreserving
end Real
end MCore
