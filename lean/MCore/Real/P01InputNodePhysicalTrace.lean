import MCore.Real.P01InputIndexLookahead
import MCore.Real.P01EvalInputNodePhysicalRefinement
import MCore.Real.P01InputAfterReadReturn

namespace MCore
namespace Real
namespace P01InputNodePhysicalTrace

open CanonicalFinalProof
open P01EvalCursorMachine
open P01WitnessIndexedReadPreserving
open P01WitnessIndexedReadGap
open P01WitnessIndexedReadGapRaw
open P01EvalInputNodePhysicalRefinement
open P01InputReturnMode
open P01InputIndexLookahead
open P01InputAfterReadReturn

/-- Number of physical blanks present before the unread source after consuming
the unary index. -/
def consumedAfterInputIndex (consumed i : Nat) : Nat :=
  consumed + i + 1

/-- Exact three-phase physical trace for an input node whose unread source tail
is nonempty.

The lookahead determines the finite return mode without changing the tape; the
preserving reader returns the selected witness bit and restores the witness;
the return machine then normalizes the cursor back to the stack-end layout. -/
theorem inputNode000_trace_sourceTail
    (witness : BitString)
    (consumed i : Nat)
    (b : Bool) (tail frameStack : BitString)
    (padding : Nat)
    (hi : i < witness.length) :
    inputIndexLookaheadMachine.run (2 * i + 4)
      { state := inputIndexLookaheadMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i ++ (b :: tail)) frameStack padding } =
      { state := .halt .sourceTail,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i ++ (b :: tail)) frameStack padding } ∧
    preservingReadMachine.run (preservingReadGapFuel consumed i)
      { state := preservingReadMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i ++ (b :: tail)) frameStack padding } =
      { state := .halt (witness.getD i false),
        tape :=
          afterIndexedReadTape witness
            (consumedAfterInputIndex consumed i)
            (b :: tail) frameStack padding } ∧
    inputAfterReadReturnMachine.run
      (consumedAfterInputIndex consumed i +
        (b :: tail).length + frameStack.length + 3)
      { state := .start .sourceTail,
        tape :=
          afterIndexedReadTape witness
            (consumedAfterInputIndex consumed i)
            (b :: tail) frameStack padding } =
      { state := .halt .frameStack,
        tape :=
          evalCursorStackEndTape witness
            (consumedAfterInputIndex consumed i)
            (b :: tail) frameStack padding } := by
  constructor
  · exact lookahead_sourceTail
      witness consumed i b tail frameStack padding
  constructor
  · have hread :=
      inputNode000_full_layout_read
        witness (b :: tail) frameStack consumed padding i hi
    simpa [consumedAfterInputIndex, afterIndexedReadTape,
      inputNodeRawSuffix, Nat.add_assoc] using hread
  · exact return_sourceTail
      witness (consumedAfterInputIndex consumed i)
      b tail frameStack padding

/-- Exact three-phase trace when the source tail is empty but the encoded
continuation stack is nonempty. -/
theorem inputNode000_trace_frameStack
    (witness : BitString)
    (consumed i : Nat)
    (b : Bool) (frameTail : BitString)
    (padding : Nat)
    (hi : i < witness.length) :
    inputIndexLookaheadMachine.run (2 * i + 6)
      { state := inputIndexLookaheadMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i) (b :: frameTail) padding } =
      { state := .halt .frameStack,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i) (b :: frameTail) padding } ∧
    preservingReadMachine.run (preservingReadGapFuel consumed i)
      { state := preservingReadMachine.initial,
        tape :=
          evalCursorReadTape witness consumed
            (encodeNat i) (b :: frameTail) padding } =
      { state := .halt (witness.getD i false),
        tape :=
          afterIndexedReadTape witness
            (consumedAfterInputIndex consumed i)
            [] (b :: frameTail) padding } ∧
    inputAfterReadReturnMachine.run
      (consumedAfterInputIndex consumed i +
        (b :: frameTail).length + 3)
      { state := .start .frameStack,
        tape :=
          afterIndexedReadTape witness
            (consumedAfterInputIndex consumed i)
            [] (b :: frameTail) padding } =
      { state := .halt .frameStack,
        tape :=
          evalCursorStackEndTape witness
            (consumedAfterInputIndex consumed i)
            [] (b :: frameTail) padding } := by
  constructor
  · exact lookahead_frameStack
      witness consumed i b frameTail padding
  constructor
  · have hread :=
      inputNode000_full_layout_read
        witness [] (b :: frameTail) consumed padding i hi
    simpa [consumedAfterInputIndex, afterIndexedReadTape,
      inputNodeRawSuffix, Nat.add_assoc] using hread
  · exact return_frameStack
      witness (consumedAfterInputIndex consumed i)
      b frameTail padding

/-- Exact three-phase trace when the input-node value is already the final
evaluator value: no unread source and no continuation frames remain. -/
theorem inputNode000_trace_done
    (witness : BitString)
    (consumed i padding : Nat)
    (hi : i < witness.length) :
    inputIndexLookaheadMachine.run (2 * i + 6)
      { state := inputIndexLookaheadMachine.initial,
        tape :=
          evalCursorReadTape witness consumed (encodeNat i) [] padding } =
      { state := .halt .done,
        tape :=
          evalCursorReadTape witness consumed (encodeNat i) [] padding } ∧
    preservingReadMachine.run (preservingReadGapFuel consumed i)
      { state := preservingReadMachine.initial,
        tape :=
          evalCursorReadTape witness consumed (encodeNat i) [] padding } =
      { state := .halt (witness.getD i false),
        tape :=
          afterIndexedReadTape witness
            (consumedAfterInputIndex consumed i) [] [] padding } ∧
    inputAfterReadReturnMachine.run 1
      { state := .start .done,
        tape :=
          afterIndexedReadTape witness
            (consumedAfterInputIndex consumed i) [] [] padding } =
      { state := .halt .done,
        tape :=
          afterIndexedReadTape witness
            (consumedAfterInputIndex consumed i) [] [] padding } := by
  constructor
  · exact lookahead_done witness consumed i padding
  constructor
  · have hread :=
      inputNode000_full_layout_read
        witness [] [] consumed padding i hi
    simpa [consumedAfterInputIndex, afterIndexedReadTape,
      inputNodeRawSuffix, Nat.add_assoc] using hread
  · exact return_done
      witness (consumedAfterInputIndex consumed i) padding

#print axioms MCore.Real.P01InputNodePhysicalTrace.inputNode000_trace_sourceTail
#print axioms MCore.Real.P01InputNodePhysicalTrace.inputNode000_trace_frameStack
#print axioms MCore.Real.P01InputNodePhysicalTrace.inputNode000_trace_done

end P01InputNodePhysicalTrace
end Real
end MCore
