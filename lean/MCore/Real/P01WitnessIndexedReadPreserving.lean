import MCore.Real.P01WitnessIndexedRead
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01WitnessIndexedReadPreserving

open CanonicalFinalProof
open CanonicalCircuitBits
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

/-- Canonical intermediate layout after at least one unary true marker has
been consumed.  `moved` is the witness prefix temporarily shifted across the
separator; `rest` is the untouched witness suffix. -/
def preservingMovedTape
    (moved rest : BitString) (remaining : Nat) (tail : BitString) :
    Tape (Option Bool) :=
  match encodeNat remaining ++ tail with
  | [] =>
      { left := List.replicate moved.length none ++ moved.map some ++
          (none :: rest.map some),
        head := none,
        right := [] }
  | b :: bs =>
      { left := List.replicate moved.length none ++ moved.map some ++
          (none :: rest.map some),
        head := some b,
        right := bs.map some }

/-- Intermediate machine configuration used by the successor induction. -/
def preservingMovedConfig
    (moved rest : BitString) (remaining : Nat) (tail : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .indexMoved,
    tape := preservingMovedTape moved rest remaining tail }

/-- Enter the moved-prefix invariant after the first unary true marker. -/
theorem preservingRead_start_successor
    (b : Bool) (witnessTail tail : BitString) (n : Nat) :
    preservingReadMachine.run 6
      { state := preservingReadMachine.initial,
        tape := preservingReadTape (b :: witnessTail) (n + 1) tail } =
      preservingMovedConfig [b] witnessTail n tail := by
  cases b <;> cases n <;>
    simp [preservingReadMachine, preservingReadTape,
      preservingMovedConfig, preservingMovedTape, encodeNat,
      TM.run, TM.step, Tape.write, Tape.move]

/-- Appending one more blank after a replicated blank block is the same as
increasing the replication count. -/
theorem replicate_none_extend
    (k : Nat) (right : List (Option Bool)) :
    List.replicate (k + 1) none ++ (none :: right) =
      List.replicate (k + 2) none ++ right := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [Nat.succ_add, List.replicate_succ, List.cons_append]
      congr 1

/-- `seekMoved` crosses a finite block of blanks and stops on the first
moved witness bit.  This is the first generic traversal lemma needed by the
successor cycle. -/
theorem seekMoved_over_blanks
    (k : Nat) (b : Bool)
    (left right : List (Option Bool)) :
    preservingReadMachine.run (k + 1)
      { state := .seekMoved,
        tape :=
          { left := List.replicate k none ++ (some b :: left),
            head := none,
            right := right } } =
      { state := .seekMoved,
        tape :=
          { left := left,
            head := some b,
            right := List.replicate (k + 1) none ++ right } } := by
  induction k generalizing right with
  | zero =>
      simp [preservingReadMachine, TM.run, TM.step, Tape.write, Tape.move]
  | succ k ih =>
      rw [show Nat.succ k + 1 = (k + 1) + 1 by omega]
      rw [TM.run]
      simp only [show preservingReadMachine.halting (.seekMoved) = false by rfl,
        Bool.false_eq_true, if_false]
      change preservingReadMachine.run (k + 1)
        { state := .seekMoved,
          tape :=
            { left := List.replicate k none ++ (some b :: left),
              head := none,
              right := none :: right } } =
        { state := .seekMoved,
          tape :=
            { left := left,
              head := some b,
              right := List.replicate (Nat.succ k + 1) none ++ right } }
      rw [ih (none :: right)]
      apply congrArg
        (fun r : List (Option Bool) =>
          ({ state := .seekMoved,
             tape := { left := left, head := some b, right := r } } :
            Configuration PreservingReadState (Option Bool)))
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        replicate_none_extend k right

/-- Tape view used while `scanMoved` walks left across the already-moved
witness prefix.  The blank separator and selected witness bit are immediately
after `bits` in the leftward direction. -/
def scanMovedTape
    (bits : BitString) (b : Bool)
    (left right : List (Option Bool)) :
    Tape (Option Bool) :=
  match bits with
  | [] =>
      { left := some b :: left,
        head := none,
        right := right }
  | x :: xs =>
      { left := xs.map some ++ (none :: some b :: left),
        head := some x,
        right := right }

/-- One physical `scanMoved` step peels the current moved witness bit
and pushes it onto the right side of the tape. -/
theorem scanMoved_step_cons
    (x b : Bool) (xs : BitString)
    (left right : List (Option Bool)) :
    preservingReadMachine.step
      { state := .scanMoved,
        tape := scanMovedTape (x :: xs) b left right } =
      { state := .scanMoved,
        tape := scanMovedTape xs b left (some x :: right) } := by
  cases xs <;>
    simp [scanMovedTape, preservingReadMachine,
      TM.step, Tape.write, Tape.move]

/-- `scanMoved` crosses every moved witness bit and then the separator,
arriving at `capture` with the selected witness bit under the head. -/
theorem scanMoved_over_bits
    (bits : BitString) (b : Bool)
    (left right : List (Option Bool)) :
    preservingReadMachine.run (bits.length + 1)
      { state := .scanMoved,
        tape := scanMovedTape bits b left right } =
      { state := .capture,
        tape :=
          { left := left,
            head := some b,
            right := none :: (bits.reverse.map some ++ right) } } := by
  induction bits generalizing right with
  | nil =>
      simp [scanMovedTape, preservingReadMachine,
        TM.run, TM.step, Tape.write, Tape.move]
  | cons x xs ih =>
      rw [show (x :: xs).length + 1 = (xs.length + 1) + 1 by simp]
      rw [TM.run]
      simp only [show preservingReadMachine.halting (.scanMoved) = false by rfl,
        Bool.false_eq_true, if_false]
      rw [scanMoved_step_cons]
      rw [ih (some x :: right)]
      apply congrArg
        (fun r : List (Option Bool) =>
          ({ state := .capture,
             tape := { left := left, head := some b, right := r } } :
            Configuration PreservingReadState (Option Bool)))
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- Canonical view of a rightward stream under a fixed left tape. -/
def rightStreamTape
    (left stream : List (Option Bool)) :
    Tape (Option Bool) :=
  match stream with
  | [] =>
      { left := left, head := none, right := [] }
  | x :: xs =>
      { left := left, head := x, right := xs }

/-- Tape view while `returnMoved` walks right across the reversed moved
prefix and then crosses its separator blank. -/
def returnMovedTape
    (bits : BitString)
    (left after : List (Option Bool)) :
    Tape (Option Bool) :=
  match bits with
  | [] =>
      rightStreamTape left (none :: after)
  | x :: xs =>
      { left := left,
        head := some x,
        right := xs.map some ++ (none :: after) }

/-- One `returnMoved` step consumes the current moved-prefix bit. -/
theorem returnMoved_step_cons
    (x : Bool) (xs : BitString)
    (left after : List (Option Bool)) :
    preservingReadMachine.step
      { state := .returnMoved,
        tape := returnMovedTape (x :: xs) left after } =
      { state := .returnMoved,
        tape := returnMovedTape xs (some x :: left) after } := by
  cases xs <;>
    simp [returnMovedTape, rightStreamTape, preservingReadMachine,
      TM.step, Tape.write, Tape.move]

/-- `returnMoved` restores all moved-prefix bits on the left and crosses the
separator, entering `returnBlanks` at the first symbol of `after`. -/
theorem returnMoved_over_bits
    (bits : BitString)
    (left after : List (Option Bool)) :
    preservingReadMachine.run (bits.length + 1)
      { state := .returnMoved,
        tape := returnMovedTape bits left after } =
      { state := .returnBlanks,
        tape :=
          rightStreamTape
            (none :: (bits.reverse.map some ++ left))
            after } := by
  induction bits generalizing left with
  | nil =>
      cases after <;>
        simp [returnMovedTape, rightStreamTape, preservingReadMachine,
          TM.run, TM.step, Tape.write, Tape.move]
  | cons x xs ih =>
      rw [show (x :: xs).length + 1 = (xs.length + 1) + 1 by simp]
      rw [TM.run]
      simp only [show preservingReadMachine.halting (.returnMoved) = false by rfl,
        Bool.false_eq_true, if_false]
      rw [returnMoved_step_cons]
      rw [ih (some x :: left)]
      apply congrArg
        (fun l : List (Option Bool) =>
          ({ state := .returnBlanks,
             tape := rightStreamTape l after } :
            Configuration PreservingReadState (Option Bool)))
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- `returnBlanks` crosses a finite blank block and changes back to
`indexMoved` on the first nonblank source bit. -/
theorem returnBlanks_over_blanks
    (k : Nat) (b : Bool)
    (left right : List (Option Bool)) :
    preservingReadMachine.run (k + 2)
      { state := .returnBlanks,
        tape :=
          { left := left,
            head := none,
            right := List.replicate k none ++ (some b :: right) } } =
      { state := .indexMoved,
        tape :=
          { left := List.replicate (k + 1) none ++ left,
            head := some b,
            right := right } } := by
  induction k generalizing left with
  | zero =>
      simp [preservingReadMachine, TM.run, TM.step, Tape.write, Tape.move]
  | succ k ih =>
      rw [show Nat.succ k + 2 = (k + 2) + 1 by omega]
      rw [TM.run]
      simp only [show preservingReadMachine.halting (.returnBlanks) = false by rfl,
        Bool.false_eq_true, if_false]
      change preservingReadMachine.run (k + 2)
        { state := .returnBlanks,
          tape :=
            { left := none :: left,
              head := none,
              right := List.replicate k none ++ (some b :: right) } } =
        { state := .indexMoved,
          tape :=
            { left := List.replicate (Nat.succ k + 1) none ++ left,
              head := some b,
              right := right } }
      rw [ih (none :: left)]
      apply congrArg
        (fun l : List (Option Bool) =>
          ({ state := .indexMoved,
             tape := { left := l, head := some b, right := right } } :
            Configuration PreservingReadState (Option Bool)))
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        replicate_none_extend k left

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


/-- Exact successor checkpoint.  Unary index 1 consumes its true marker
and false terminator, reads the second witness bit, and restores the entire
witness exactly.  The two consumed source symbols remain as blanks immediately
to the right of the canonical witness/source separator. -/
theorem preservingRead_one
    (b0 b1 : Bool) (witnessTail tail : BitString) :
    preservingReadMachine.run 17
      { state := preservingReadMachine.initial,
        tape := preservingReadTape (b0 :: b1 :: witnessTail) 1 tail } =
      { state := .halt b1,
        tape :=
          { left := (b0 :: b1 :: witnessTail).map some,
            head := none,
            right := none :: none :: tail.map some } } := by
  set_option maxHeartbeats 2000000 in
    cases b0 <;> cases b1 <;>
      simp [preservingReadMachine, preservingReadTape, encodeNat,
        TM.run, TM.step, Tape.write, Tape.move]

/-- First successor checkpoint.  For unary index 1 the machine must move one
witness cell across the temporary separator, read the second witness bit, then
restore the moved cell before halting.  Extra fuel is inert after halting. -/
theorem preservingRead_one_value
    (b0 b1 : Bool) (witnessTail tail : BitString) :
    (preservingReadMachine.run 32
      { state := preservingReadMachine.initial,
        tape := preservingReadTape (b0 :: b1 :: witnessTail) 1 tail }).state =
      .halt b1 := by
  set_option maxHeartbeats 2000000 in
    cases b0 <;> cases b1 <;>
      simp [preservingReadMachine, preservingReadTape, encodeNat,
        TM.run, TM.step, Tape.write, Tape.move]


#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingRead_start_successor
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.replicate_none_extend
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.seekMoved_over_blanks
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.scanMoved_step_cons
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.scanMoved_over_bits
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.returnMoved_step_cons
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.returnMoved_over_bits
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.returnBlanks_over_blanks
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingRead_zero
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingRead_zero_value
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingRead_one
#print axioms MCore.Real.P01WitnessIndexedReadPreserving.preservingRead_one_value

end P01WitnessIndexedReadPreserving
end Real
end MCore
