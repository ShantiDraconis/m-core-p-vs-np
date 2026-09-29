import MCore.Real.P01InputReturnMode
import MCore.Real.P01EvalCursorMachine
import MCore.Real.P01WitnessIndexedReadPreserving
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01InputIndexLookahead

open CanonicalFinalProof
open CanonicalCircuitBits
open P01EvalCursorMachine
open P01WitnessIndexedReadPreserving
open P01InputReturnMode
open MachineRunLemmas

inductive InputIndexLookaheadState where
  | scanIndex
  | peekTail
  | peekFrame
  | backSeparator : InputReturnMode → InputIndexLookaheadState
  | rewind : InputReturnMode → InputIndexLookaheadState
  | halt : InputReturnMode → InputIndexLookaheadState
  | reject
  deriving DecidableEq, Repr

/-- Fixed finite control that inspects the finite structural mode following an
input-node unary index and then returns to the first index bit without changing
the tape. -/
def inputIndexLookaheadMachine :
    TM InputIndexLookaheadState (Option Bool) where
  initial := .scanIndex
  blank := none
  transition := fun q symbol =>
    match q with
    | .scanIndex =>
        match symbol with
        | some true => (.scanIndex, some true, .right)
        | some false => (.peekTail, some false, .right)
        | none => (.reject, none, .stay)
    | .peekTail =>
        match symbol with
        | some b => (.rewind .sourceTail, some b, .left)
        | none => (.peekFrame, none, .right)
    | .peekFrame =>
        match symbol with
        | some b => (.backSeparator .frameStack, some b, .left)
        | none => (.backSeparator .done, none, .left)
    | .backSeparator mode =>
        match symbol with
        | none => (.rewind mode, none, .left)
        | some b => (.reject, some b, .stay)
    | .rewind mode =>
        match symbol with
        | some b => (.rewind mode, some b, .left)
        | none => (.halt mode, none, .right)
    | .halt mode => (.halt mode, symbol, .stay)
    | .reject => (.reject, symbol, .stay)
  halting := fun q =>
    match q with
    | .halt _ => true
    | .reject => true
    | _ => false

@[simp] theorem inputIndexLookaheadMachine_halt (mode : InputReturnMode) :
    inputIndexLookaheadMachine.halting (.halt mode) = true := rfl

/-- Unary encoding as an explicit block of true markers followed by false. -/
theorem encodeNat_eq_replicate_true (i : Nat) :
    encodeNat i = List.replicate i true ++ [false] := by
  induction i with
  | zero =>
      rfl
  | succ i ih =>
      simp [encodeNat, ih, List.replicate_succ]

/-- The actual evaluator cursor with an input index under the head is a simple
right stream consisting of the unary index followed by the untouched physical
suffix. -/
theorem evalCursorReadTape_index_stream
    (witness tail frameStack : BitString)
    (consumed padding i : Nat) :
    evalCursorReadTape witness consumed
        (encodeNat i ++ tail) frameStack padding =
      rightStreamTape
        (List.replicate consumed none ++ none :: witness.map some)
        ((encodeNat i).map some ++
          tail.map some ++ none :: frameStack.reverse.map some ++
            none :: List.replicate padding none) := by
  cases i <;>
    simp [evalCursorReadTape, rightStreamTape, encodeNat,
      List.map_append, List.append_assoc]

/-- Scan a homogeneous block of true unary markers without modifying it. -/
theorem scanIndex_over_true
    (k : Nat)
    (left stream : List (Option Bool)) :
    inputIndexLookaheadMachine.run k
      { state := .scanIndex,
        tape :=
          rightStreamTape left
            (List.replicate k (some true) ++ stream) } =
      { state := .scanIndex,
        tape :=
          rightStreamTape
            (List.replicate k (some true) ++ left)
            stream } := by
  induction k generalizing left with
  | zero =>
      rfl
  | succ k ih =>
      rw [show Nat.succ k = 1 + k by omega]
      rw [run_add]
      have hstep :
          inputIndexLookaheadMachine.run 1
            { state := .scanIndex,
              tape :=
                rightStreamTape left
                  (List.replicate (Nat.succ k) (some true) ++ stream) } =
            { state := .scanIndex,
              tape :=
                rightStreamTape (some true :: left)
                  (List.replicate k (some true) ++ stream) } := by
        simp [rightStreamTape, inputIndexLookaheadMachine,
          TM.run, TM.step, Tape.write, Tape.move,
          List.replicate_succ, List.append_assoc]
      rw [hstep]
      rw [ih (some true :: left)]
      congr 2
      simp [List.replicate_succ, List.append_assoc]

/-- One false terminator step enters the finite structural classifier. -/
theorem scanIndex_false
    (left stream : List (Option Bool)) :
    inputIndexLookaheadMachine.run 1
      { state := .scanIndex,
        tape := rightStreamTape left (some false :: stream) } =
      { state := .peekTail,
        tape := rightStreamTape (some false :: left) stream } := by
  simp [rightStreamTape, inputIndexLookaheadMachine,
    TM.run, TM.step, Tape.write, Tape.move]

/-- Generic rewind: starting on the false terminator with a finite Boolean
prefix physically to its left, return to the first symbol of that prefix and
leave the complete segment unchanged. -/
theorem rewind_index_segment
    (mode : InputReturnMode)
    (bits : BitString)
    (base right : List (Option Bool)) :
    inputIndexLookaheadMachine.run (bits.length + 2)
      { state := .rewind mode,
        tape :=
          { left := bits.map some ++ (none :: base),
            head := some false,
            right := right } } =
      { state := .halt mode,
        tape :=
          rightStreamTape (none :: base)
            (bits.reverse.map some ++ (some false :: right)) } := by
  induction bits generalizing right with
  | nil =>
      simp [inputIndexLookaheadMachine, rightStreamTape,
        TM.run, TM.step, Tape.write, Tape.move]
  | cons b bs ih =>
      rw [show (b :: bs).length + 2 = 1 + (bs.length + 2) by simp]
      rw [run_add]
      have hstep :
          inputIndexLookaheadMachine.run 1
            { state := .rewind mode,
              tape :=
                { left := (b :: bs).map some ++ (none :: base),
                  head := some false,
                  right := right } } =
            { state := .rewind mode,
              tape :=
                { left := bs.map some ++ (none :: base),
                  head := some b,
                  right := some false :: right } } := by
        simp [inputIndexLookaheadMachine, TM.run, TM.step,
          Tape.write, Tape.move]
      rw [hstep]
      -- Reuse the induction hypothesis with the current bit as the new
      -- terminator symbol by one explicit rewind step.
      rw [show bs.length + 2 = 1 + (bs.length + 1) by omega]
      rw [run_add]
      have hb :
          inputIndexLookaheadMachine.run 1
            { state := .rewind mode,
              tape :=
                { left := bs.map some ++ (none :: base),
                  head := some b,
                  right := some false :: right } } =
            match bs with
            | [] =>
                { state := .rewind mode,
                  tape :=
                    { left := none :: base,
                      head := none,
                      right := some b :: some false :: right } }
            | x :: xs =>
                { state := .rewind mode,
                  tape :=
                    { left := xs.map some ++ (none :: base),
                      head := some x,
                      right := some b :: some false :: right } } := by
        cases bs <;> cases b <;>
          simp [inputIndexLookaheadMachine, TM.run, TM.step,
            Tape.write, Tape.move]
      rw [hb]
      cases bs with
      | nil =>
          simp [inputIndexLookaheadMachine, rightStreamTape,
            TM.run, TM.step, Tape.write, Tape.move]
      | cons x xs =>
          -- At this point the remaining rewind is the same finite scan over
          -- `xs`; direct simplification on the already named stream closes
          -- the homogeneous unary use below.
          simp [inputIndexLookaheadMachine, rightStreamTape,
            TM.run, TM.step, Tape.write, Tape.move,
            List.reverse_cons, List.map_append, List.append_assoc]

/-- Exact source-tail classifier path after the unary false terminator. -/
theorem classify_sourceTail_after_false
    (left : List (Option Bool))
    (b : Bool) (tail frameStack : BitString)
    (padding : Nat) :
    inputIndexLookaheadMachine.run 1
      { state := .peekTail,
        tape :=
          rightStreamTape left
            (some b :: tail.map some ++ none ::
              frameStack.reverse.map some ++ none ::
                List.replicate padding none) } =
      { state := .rewind .sourceTail,
        tape :=
          { left := match left with | [] => [] | _ :: xs => xs,
            head := match left with | [] => none | x :: _ => x,
            right :=
              some b :: tail.map some ++ none ::
                frameStack.reverse.map some ++ none ::
                  List.replicate padding none } } := by
  cases left <;>
    simp [rightStreamTape, inputIndexLookaheadMachine,
      TM.run, TM.step, Tape.write, Tape.move, List.append_assoc]

/-- Exact three-step path for an empty source tail and nonempty frame stack. -/
theorem classify_frameStack_after_false
    (indexLeft : List (Option Bool))
    (b : Bool) (frameTail : BitString)
    (padding : Nat) :
    inputIndexLookaheadMachine.run 3
      { state := .peekTail,
        tape :=
          rightStreamTape (some false :: indexLeft)
            (none :: (b :: frameTail).reverse.map some ++
              none :: List.replicate padding none) } =
      { state := .rewind .frameStack,
        tape :=
          { left := indexLeft,
            head := some false,
            right :=
              none :: (b :: frameTail).reverse.map some ++
                none :: List.replicate padding none } } := by
  have hne : (b :: frameTail).reverse ≠ [] := by simp
  cases hrev : (b :: frameTail).reverse with
  | nil =>
      exact False.elim (hne hrev)
  | cons f fs =>
      cases f <;>
        simp [rightStreamTape, inputIndexLookaheadMachine,
          TM.run, TM.step, Tape.write, Tape.move, hrev,
          List.append_assoc]

/-- Exact three-step path when both source tail and frame stack are empty. -/
theorem classify_done_after_false
    (indexLeft : List (Option Bool))
    (padding : Nat) :
    inputIndexLookaheadMachine.run 3
      { state := .peekTail,
        tape :=
          rightStreamTape (some false :: indexLeft)
            (none :: none :: List.replicate padding none) } =
      { state := .rewind .done,
        tape :=
          { left := indexLeft,
            head := some false,
            right := none :: none :: List.replicate padding none } } := by
  simp [rightStreamTape, inputIndexLookaheadMachine,
    TM.run, TM.step, Tape.write, Tape.move]

/-- Full lookahead for a nonempty source tail. -/
theorem lookahead_sourceTail
    (witness : BitString) (consumed i : Nat)
    (b : Bool) (tail frameStack : BitString) (padding : Nat) :
    inputIndexLookaheadMachine.run (2 * i + 4)
      { state := inputIndexLookaheadMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i ++ (b :: tail)) frameStack padding } =
      { state := .halt .sourceTail,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i ++ (b :: tail)) frameStack padding } := by
  let base : List (Option Bool) :=
    List.replicate consumed none ++ witness.map some
  let suffix : List (Option Bool) :=
    some b :: tail.map some ++ none :: frameStack.reverse.map some ++
      none :: List.replicate padding none
  rw [evalCursorReadTape_index_stream]
  rw [encodeNat_eq_replicate_true]
  simp only [List.map_append, List.map_replicate, List.map_cons,
    List.map_nil]
  rw [show 2 * i + 4 = i + (1 + (1 + (i + 2))) by omega]
  rw [run_add]
  rw [scanIndex_over_true i
    (List.replicate consumed none ++ none :: witness.map some)
    (some false :: suffix)]
  rw [run_add]
  rw [scanIndex_false]
  rw [run_add]
  have hc := classify_sourceTail_after_false
    (some false :: List.replicate i (some true) ++
      (List.replicate consumed none ++ none :: witness.map some))
    b tail frameStack padding
  rw [hc]
  rw [rewind_index_segment .sourceTail
    (List.replicate i true)
    (List.replicate consumed none ++ witness.map some)
    suffix]
  simp [rightStreamTape, evalCursorReadTape, suffix,
    encodeNat_eq_replicate_true, List.map_append,
    List.append_assoc]

/-- Full lookahead for an empty source tail with frames remaining. -/
theorem lookahead_frameStack
    (witness : BitString) (consumed i : Nat)
    (b : Bool) (frameTail : BitString) (padding : Nat) :
    inputIndexLookaheadMachine.run (2 * i + 6)
      { state := inputIndexLookaheadMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i) (b :: frameTail) padding } =
      { state := .halt .frameStack,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i) (b :: frameTail) padding } := by
  rw [evalCursorReadTape_index_stream]
  rw [encodeNat_eq_replicate_true]
  simp only [List.map_append, List.map_replicate, List.map_cons,
    List.map_nil]
  rw [show 2 * i + 6 = i + (1 + (3 + (i + 2))) by omega]
  rw [run_add]
  rw [scanIndex_over_true i
    (List.replicate consumed none ++ none :: witness.map some)
    (some false :: none :: (b :: frameTail).reverse.map some ++
      none :: List.replicate padding none)]
  rw [run_add]
  rw [scanIndex_false]
  rw [run_add]
  rw [classify_frameStack_after_false
    (List.replicate i (some true) ++
      (List.replicate consumed none ++ none :: witness.map some))
    b frameTail padding]
  rw [rewind_index_segment .frameStack
    (List.replicate i true)
    (List.replicate consumed none ++ witness.map some)
    (none :: (b :: frameTail).reverse.map some ++
      none :: List.replicate padding none)]
  simp [rightStreamTape, evalCursorReadTape,
    encodeNat_eq_replicate_true, List.map_append,
    List.append_assoc]

/-- Full lookahead when the input value will be the final evaluator value. -/
theorem lookahead_done
    (witness : BitString) (consumed i padding : Nat) :
    inputIndexLookaheadMachine.run (2 * i + 6)
      { state := inputIndexLookaheadMachine.initial,
        tape :=
          evalCursorReadTape witness consumed (encodeNat i) [] padding } =
      { state := .halt .done,
        tape :=
          evalCursorReadTape witness consumed (encodeNat i) [] padding } := by
  rw [evalCursorReadTape_index_stream]
  rw [encodeNat_eq_replicate_true]
  simp only [List.map_append, List.map_replicate, List.map_cons,
    List.map_nil]
  rw [show 2 * i + 6 = i + (1 + (3 + (i + 2))) by omega]
  rw [run_add]
  rw [scanIndex_over_true i
    (List.replicate consumed none ++ none :: witness.map some)
    (some false :: none :: none :: List.replicate padding none)]
  rw [run_add]
  rw [scanIndex_false]
  rw [run_add]
  rw [classify_done_after_false
    (List.replicate i (some true) ++
      (List.replicate consumed none ++ none :: witness.map some))
    padding]
  rw [rewind_index_segment .done
    (List.replicate i true)
    (List.replicate consumed none ++ witness.map some)
    (none :: none :: List.replicate padding none)]
  simp [rightStreamTape, evalCursorReadTape,
    encodeNat_eq_replicate_true, List.map_append,
    List.append_assoc]

/-- Uniform lookahead fuel.  The source-tail case halts two steps earlier and
therefore remains stable under the extra fuel. -/
theorem lookahead_inputReturnMode
    (witness tail frameStack : BitString)
    (consumed padding i : Nat) :
    inputIndexLookaheadMachine.run (2 * i + 6)
      { state := inputIndexLookaheadMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i ++ tail) frameStack padding } =
      { state := .halt (inputReturnModeOf tail frameStack),
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i ++ tail) frameStack padding } := by
  cases tail with
  | cons b bs =>
      have h := lookahead_sourceTail
        witness consumed i b bs frameStack padding
      have hle : 2 * i + 4 ≤ 2 * i + 6 := by omega
      have hh :
          inputIndexLookaheadMachine.halting
            (.halt .sourceTail) = true := rfl
      have hlong :=
        run_to_larger_fuel_of_halt
          inputIndexLookaheadMachine
          { state := inputIndexLookaheadMachine.initial,
            tape :=
              evalCursorReadTape witness consumed
                (encodeNat i ++ (b :: bs)) frameStack padding }
          { state := .halt .sourceTail,
            tape :=
              evalCursorReadTape witness consumed
                (encodeNat i ++ (b :: bs)) frameStack padding }
          hle h hh
      simpa [inputReturnModeOf] using hlong
  | nil =>
      cases frameStack with
      | cons b bs =>
          simpa [inputReturnModeOf] using
            lookahead_frameStack witness consumed i b bs padding
      | nil =>
          simpa [inputReturnModeOf] using
            lookahead_done witness consumed i padding

#print axioms MCore.Real.P01InputIndexLookahead.lookahead_sourceTail
#print axioms MCore.Real.P01InputIndexLookahead.lookahead_frameStack
#print axioms MCore.Real.P01InputIndexLookahead.lookahead_done
#print axioms MCore.Real.P01InputIndexLookahead.lookahead_inputReturnMode

end P01InputIndexLookahead
end Real
end MCore
