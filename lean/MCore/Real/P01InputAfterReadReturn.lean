import MCore.Real.P01InputReturnMode
import MCore.Real.P01EvalCursorMachine
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01InputAfterReadReturn

open CanonicalFinalProof
open P01EvalCursorMachine
open P01InputReturnMode
open MachineRunLemmas

inductive InputAfterReadReturnState where
  | start : InputReturnMode → InputAfterReadReturnState
  | seekSource
  | scanSource
  | seekFrames
  | scanFrames
  | halt : InputReturnMode → InputAfterReadReturnState
  | reject
  deriving DecidableEq, Repr

/-- Return machine used after the indexed witness reader has restored the
witness and left the head on the witness/source separator.

The finite return mode removes the only ambiguity caused by an all-blank
source tail. -/
def inputAfterReadReturnMachine :
    TM InputAfterReadReturnState (Option Bool) where
  initial := .start .done
  blank := none
  transition := fun q symbol =>
    match q with
    | .start .sourceTail =>
        match symbol with
        | none => (.seekSource, none, .right)
        | some b => (.reject, some b, .stay)
    | .start .frameStack =>
        match symbol with
        | none => (.seekFrames, none, .right)
        | some b => (.reject, some b, .stay)
    | .start .done =>
        (.halt .done, symbol, .stay)
    | .seekSource =>
        match symbol with
        | none => (.seekSource, none, .right)
        | some b => (.scanSource, some b, .right)
    | .scanSource =>
        match symbol with
        | some b => (.scanSource, some b, .right)
        | none => (.scanFrames, none, .right)
    | .seekFrames =>
        match symbol with
        | none => (.seekFrames, none, .right)
        | some b => (.scanFrames, some b, .right)
    | .scanFrames =>
        match symbol with
        | some b => (.scanFrames, some b, .right)
        | none => (.halt .frameStack, none, .stay)
    | .halt mode => (.halt mode, symbol, .stay)
    | .reject => (.reject, symbol, .stay)
  halting := fun q =>
    match q with
    | .halt _ => true
    | .reject => true
    | _ => false

@[simp] theorem inputAfterReadReturnMachine_halt (mode : InputReturnMode) :
    inputAfterReadReturnMachine.halting (.halt mode) = true := rfl

/-- Exact reader-final tape before the mode-aware return phase. -/
def afterIndexedReadTape
    (witness : BitString)
    (consumed : Nat)
    (tail frameStack : BitString)
    (padding : Nat) : Tape (Option Bool) :=
  { left := witness.map some
    head := none
    right :=
      List.replicate consumed none ++
        tail.map some ++
        none :: frameStack.reverse.map some ++
        none :: List.replicate padding none }

/-- Canonical source-scan view for the return machine. -/
def sourceReturnConfig
    (left : List (Option Bool))
    (remaining frameStack : BitString)
    (padding : Nat) :
    Configuration InputAfterReadReturnState (Option Bool) :=
  match remaining with
  | [] =>
      { state := .scanSource
        tape :=
          { left := left
            head := none
            right :=
              frameStack.reverse.map some ++
                none :: List.replicate padding none } }
  | b :: bs =>
      { state := .scanSource
        tape :=
          { left := left
            head := some b
            right :=
              bs.map some ++
                none :: frameStack.reverse.map some ++
                none :: List.replicate padding none } }

@[simp] theorem sourceReturnConfig_state
    (left : List (Option Bool))
    (remaining frameStack : BitString)
    (padding : Nat) :
    (sourceReturnConfig left remaining frameStack padding).state =
      .scanSource := by
  cases remaining <;> rfl

theorem sourceReturn_step_cons
    (left : List (Option Bool))
    (b : Bool) (bs frameStack : BitString)
    (padding : Nat) :
    inputAfterReadReturnMachine.step
      (sourceReturnConfig left (b :: bs) frameStack padding) =
      sourceReturnConfig (some b :: left) bs frameStack padding := by
  cases bs <;>
    simp [sourceReturnConfig, inputAfterReadReturnMachine,
      TM.step, Tape.write, Tape.move, List.append_assoc]

theorem sourceReturn_run
    (left : List (Option Bool))
    (remaining frameStack : BitString)
    (padding : Nat) :
    inputAfterReadReturnMachine.run remaining.length
      (sourceReturnConfig left remaining frameStack padding) =
      sourceReturnConfig
        (remaining.reverse.map some ++ left)
        [] frameStack padding := by
  induction remaining generalizing left with
  | nil =>
      rfl
  | cons b bs ih =>
      rw [List.length_cons]
      rw [TM.run]
      rw [sourceReturnConfig_state]
      simp only [show inputAfterReadReturnMachine.halting (.scanSource) = false by rfl,
        Bool.false_eq_true, if_false]
      rw [sourceReturn_step_cons]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

/-- Frame-stack scan view. -/
def frameReturnConfig
    (left : List (Option Bool))
    (remainingRev : BitString)
    (padding : Nat) :
    Configuration InputAfterReadReturnState (Option Bool) :=
  match remainingRev with
  | [] =>
      { state := .scanFrames
        tape :=
          { left := left
            head := none
            right := List.replicate padding none } }
  | b :: bs =>
      { state := .scanFrames
        tape :=
          { left := left
            head := some b
            right := bs.map some ++ none :: List.replicate padding none } }

@[simp] theorem frameReturnConfig_state
    (left : List (Option Bool))
    (remainingRev : BitString)
    (padding : Nat) :
    (frameReturnConfig left remainingRev padding).state = .scanFrames := by
  cases remainingRev <;> rfl

theorem frameReturn_step_cons
    (left : List (Option Bool))
    (b : Bool) (bs : BitString)
    (padding : Nat) :
    inputAfterReadReturnMachine.step
      (frameReturnConfig left (b :: bs) padding) =
      frameReturnConfig (some b :: left) bs padding := by
  cases bs <;>
    simp [frameReturnConfig, inputAfterReadReturnMachine,
      TM.step, Tape.write, Tape.move, List.append_assoc]

theorem frameReturn_run
    (left : List (Option Bool))
    (remainingRev : BitString)
    (padding : Nat) :
    inputAfterReadReturnMachine.run remainingRev.length
      (frameReturnConfig left remainingRev padding) =
      frameReturnConfig
        (remainingRev.reverse.map some ++ left)
        [] padding := by
  induction remainingRev generalizing left with
  | nil =>
      rfl
  | cons b bs ih =>
      rw [List.length_cons]
      rw [TM.run]
      rw [frameReturnConfig_state]
      simp only [show inputAfterReadReturnMachine.halting (.scanFrames) = false by rfl,
        Bool.false_eq_true, if_false]
      rw [frameReturn_step_cons]
      rw [ih]
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem frameReturn_halt
    (left : List (Option Bool))
    (padding : Nat) :
    inputAfterReadReturnMachine.run 1
      (frameReturnConfig left [] padding) =
      { state := .halt .frameStack
        tape :=
          { left := left
            head := none
            right := List.replicate padding none } } := by
  simp [frameReturnConfig, inputAfterReadReturnMachine,
    TM.run, TM.step, Tape.write, Tape.move]

/-- Skip exactly the reader-created blank block and consume the first source
bit into the left tape. -/
theorem seekSource_over_blanks
    (k : Nat) (b : Bool)
    (left right : List (Option Bool)) :
    inputAfterReadReturnMachine.run (k + 1)
      { state := .seekSource
        tape :=
          match k with
          | 0 =>
              { left := left, head := some b, right := right }
          | n + 1 =>
              { left := left, head := none,
                right := List.replicate n none ++ some b :: right } } =
      { state := .scanSource
        tape := { left := some b :: List.replicate k none ++ left,
                  head := match right with | [] => none | x :: _ => x,
                  right := match right with | [] => [] | _ :: xs => xs } } := by
  induction k generalizing left with
  | zero =>
      cases right <;>
        simp [inputAfterReadReturnMachine, TM.run, TM.step,
          Tape.write, Tape.move]
  | succ k ih =>
      rw [show Nat.succ k + 1 = (k + 1) + 1 by omega]
      rw [TM.run]
      simp only [show inputAfterReadReturnMachine.halting (.seekSource) = false by rfl,
        Bool.false_eq_true, if_false]
      change inputAfterReadReturnMachine.run (k + 1)
        { state := .seekSource,
          tape :=
            match k with
            | 0 =>
                { left := none :: left, head := some b, right := right }
            | n + 1 =>
                { left := none :: left, head := none,
                  right := List.replicate n none ++ some b :: right } } =
        { state := .scanSource,
          tape :=
            { left := some b :: List.replicate (Nat.succ k) none ++ left,
              head := match right with | [] => none | x :: _ => x,
              right := match right with | [] => [] | _ :: xs => xs } }
      rw [ih (none :: left)]
      congr 2
      simp [List.replicate_succ, List.append_assoc]

/-- Main nonempty-source return theorem. -/
theorem return_sourceTail
    (witness : BitString)
    (consumed : Nat)
    (b : Bool) (tail frameStack : BitString)
    (padding : Nat) :
    inputAfterReadReturnMachine.run
      (consumed + (b :: tail).length + frameStack.length + 3)
      { state := .start .sourceTail,
        tape :=
          afterIndexedReadTape witness consumed
            (b :: tail) frameStack padding } =
      { state := .halt .frameStack,
        tape :=
          evalCursorStackEndTape witness consumed
            (b :: tail) frameStack padding } := by
  let left0 : List (Option Bool) := none :: witness.map some
  let left1 : List (Option Bool) :=
    some b :: List.replicate consumed none ++ left0
  have hstart :
      inputAfterReadReturnMachine.run 1
        { state := .start .sourceTail,
          tape := afterIndexedReadTape witness consumed
            (b :: tail) frameStack padding } =
        { state := .seekSource,
          tape :=
            match consumed with
            | 0 =>
                { left := left0, head := some b,
                  right :=
                    tail.map some ++ none :: frameStack.reverse.map some ++
                      none :: List.replicate padding none }
            | n + 1 =>
                { left := left0, head := none,
                  right :=
                    List.replicate n none ++ some b ::
                      (tail.map some ++ none :: frameStack.reverse.map some ++
                        none :: List.replicate padding none) } } := by
    cases consumed <;>
      simp [afterIndexedReadTape, inputAfterReadReturnMachine, left0,
        TM.run, TM.step, Tape.write, Tape.move, List.replicate_succ,
        List.append_assoc]

  rw [show consumed + (b :: tail).length + frameStack.length + 3 =
      1 + ((consumed + 1) + (tail.length +
        (1 + (frameStack.reverse.length + 1)))) by
      simp
      omega]
  rw [run_add, hstart]
  rw [run_add]
  rw [seekSource_over_blanks consumed b left0
    (tail.map some ++ none :: frameStack.reverse.map some ++
      none :: List.replicate padding none)]
  change inputAfterReadReturnMachine.run
      (tail.length + (1 + (frameStack.reverse.length + 1)))
      (sourceReturnConfig left1 tail frameStack padding) =
    _
  rw [run_add]
  rw [sourceReturn_run]
  rw [run_add]
  change inputAfterReadReturnMachine.run
      (frameStack.reverse.length + 1)
      (frameReturnConfig
        (none :: (tail.reverse.map some ++ left1))
        frameStack.reverse padding) = _
  rw [run_add]
  rw [frameReturn_run]
  rw [frameReturn_halt]
  simp [evalCursorStackEndTape, left0, left1,
    List.reverse_reverse, List.map_append, List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Empty source tail with frames remaining. -/
theorem return_frameStack
    (witness : BitString)
    (consumed : Nat)
    (b : Bool) (frameTail : BitString)
    (padding : Nat) :
    inputAfterReadReturnMachine.run
      (consumed + (b :: frameTail).length + 3)
      { state := .start .frameStack,
        tape :=
          afterIndexedReadTape witness consumed
            [] (b :: frameTail) padding } =
      { state := .halt .frameStack,
        tape :=
          evalCursorStackEndTape witness consumed
            [] (b :: frameTail) padding } := by
  let left0 : List (Option Bool) := none :: witness.map some
  have hstart :
      inputAfterReadReturnMachine.run 1
        { state := .start .frameStack,
          tape := afterIndexedReadTape witness consumed
            [] (b :: frameTail) padding } =
        { state := .seekFrames,
          tape :=
            { left := left0,
              head := none,
              right :=
                List.replicate consumed none ++
                  (some ((b :: frameTail).reverse.getD 0 false) :: []) } } := by
    -- The theorem below uses a direct normalized proof instead of this
    -- intermediate shape.
    cases consumed <;> cases b <;> cases frameTail <;>
      simp [afterIndexedReadTape, inputAfterReadReturnMachine, left0,
        TM.run, TM.step, Tape.write, Tape.move, List.replicate_succ,
        List.append_assoc]
  clear hstart
  -- A direct structural proof is simpler because the physical frame stack is
  -- already stored reversed.
  cases hrev : (b :: frameTail).reverse with
  | nil =>
      simp at hrev
  | cons f fs =>
      have hlen : fs.length + 1 = (b :: frameTail).length := by
        have := congrArg List.length hrev
        simp at this
        omega
      let left0 : List (Option Bool) := none :: witness.map some
      have hs :
          inputAfterReadReturnMachine.run (consumed + 2)
            { state := .start .frameStack,
              tape :=
                afterIndexedReadTape witness consumed
                  [] (b :: frameTail) padding } =
            { state := .scanFrames,
              tape :=
                { left := some f :: none :: List.replicate consumed none ++ left0,
                  head := match fs with | [] => none | x :: _ => some x,
                  right :=
                    match fs with
                    | [] => List.replicate padding none
                    | _ :: xs => xs.map some ++ none :: List.replicate padding none } } := by
        cases consumed <;> cases f <;> cases fs <;>
          simp [afterIndexedReadTape, inputAfterReadReturnMachine, left0,
            hrev, TM.run, TM.step, Tape.write, Tape.move,
            List.replicate_succ, List.append_assoc]
      rw [show consumed + (b :: frameTail).length + 3 =
          (consumed + 2) + (fs.length + 1) by omega]
      rw [run_add, hs]
      change inputAfterReadReturnMachine.run (fs.length + 1)
        (frameReturnConfig
          (some f :: none :: List.replicate consumed none ++ left0)
          fs padding) = _
      rw [show fs.length + 1 = fs.length + 1 by rfl]
      rw [run_add]
      rw [frameReturn_run]
      rw [frameReturn_halt]
      simp [evalCursorStackEndTape, left0, hrev,
        List.reverse_reverse, List.map_append, List.append_assoc,
        List.replicate_succ]

/-- Final-value mode needs no cursor normalization. -/
theorem return_done
    (witness : BitString)
    (consumed padding : Nat) :
    inputAfterReadReturnMachine.run 1
      { state := .start .done,
        tape := afterIndexedReadTape witness consumed [] [] padding } =
      { state := .halt .done,
        tape := afterIndexedReadTape witness consumed [] [] padding } := by
  simp [inputAfterReadReturnMachine, TM.run]

#print axioms MCore.Real.P01InputAfterReadReturn.return_sourceTail
#print axioms MCore.Real.P01InputAfterReadReturn.return_frameStack
#print axioms MCore.Real.P01InputAfterReadReturn.return_done

end P01InputAfterReadReturn
end Real
end MCore
