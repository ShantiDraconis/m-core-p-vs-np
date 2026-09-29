import MCore.Real.P01EvalInputNodePhysicalRefinement
import MCore.Real.P01InputIndexLookahead
import MCore.Real.P01InputAfterReadReturn

namespace MCore
namespace Real
namespace P01InputNodePhysicalPipeline

open CanonicalFinalProof
open P01EvalCursorMachine
open P01EvalInputNodePhysicalRefinement
open P01InputReturnMode
open P01InputIndexLookahead
open P01InputAfterReadReturn
open P01WitnessIndexedReadPreserving

/-- Exact lookahead fuel.  The nonempty-source case is two transitions shorter
than the two empty-source cases. -/
def inputIndexLookaheadFuel
    (i : Nat) (tail frameStack : BitString) : Nat :=
  match tail with
  | _ :: _ => 2 * i + 4
  | [] =>
      match frameStack with
      | _ :: _ => 2 * i + 6
      | [] => 2 * i + 6

theorem inputIndexLookahead_run_exact
    (witness tail frameStack : BitString)
    (consumed padding i : Nat) :
    inputIndexLookaheadMachine.run
      (inputIndexLookaheadFuel i tail frameStack)
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
      simpa [inputIndexLookaheadFuel, inputReturnModeOf] using
        lookahead_sourceTail witness consumed i b bs frameStack padding
  | nil =>
      cases frameStack with
      | cons b bs =>
          simpa [inputIndexLookaheadFuel, inputReturnModeOf] using
            lookahead_frameStack witness consumed i b bs padding
      | nil =>
          simpa [inputIndexLookaheadFuel, inputReturnModeOf] using
            lookahead_done witness consumed i padding

/-- Exact fuel for returning from the reader-final layout to the evaluator
stack-end layout. -/
def inputAfterReadReturnFuel
    (consumed : Nat) (tail frameStack : BitString) : Nat :=
  match tail with
  | b :: bs => consumed + (b :: bs).length + frameStack.length + 3
  | [] =>
      match frameStack with
      | b :: bs => consumed + (b :: bs).length + 3
      | [] => 1

theorem inputAfterReadReturn_run_exact
    (witness tail frameStack : BitString)
    (consumed padding : Nat) :
    inputAfterReadReturnMachine.run
      (inputAfterReadReturnFuel consumed tail frameStack)
      { state := .start (inputReturnModeOf tail frameStack),
        tape :=
          afterIndexedReadTape witness consumed tail frameStack padding } =
      { state := .halt (inputReturnModeOf tail frameStack),
        tape :=
          match inputReturnModeOf tail frameStack with
          | .done =>
              afterIndexedReadTape witness consumed [] [] padding
          | _ =>
              evalCursorStackEndTape
                witness consumed tail frameStack padding } := by
  cases tail with
  | cons b bs =>
      simpa [inputAfterReadReturnFuel, inputReturnModeOf] using
        return_sourceTail witness consumed b bs frameStack padding
  | nil =>
      cases frameStack with
      | cons b bs =>
          simpa [inputAfterReadReturnFuel, inputReturnModeOf] using
            return_frameStack witness consumed b bs padding
      | nil =>
          simpa [inputAfterReadReturnFuel, inputReturnModeOf] using
            return_done witness consumed padding

/-- The exact tape produced by the full-layout preserving reader is precisely
the mode-aware return machine's canonical input, with the consumed-source
counter enlarged by the complete unary index length `i + 1`. -/
theorem inputNode000_reader_output_eq_afterReadTape
    (witness tail frameStack : BitString)
    (consumed padding i : Nat) :
    ({ left := witness.map some,
       head := none,
       right :=
         List.replicate (consumed + i + 1) none ++
           inputNodeRawSuffix tail frameStack padding } :
      Tape (Option Bool)) =
    afterIndexedReadTape witness (consumed + i + 1)
      tail frameStack padding := by
  simp [afterIndexedReadTape, inputNodeRawSuffix, List.append_assoc]

/-- Three-phase physical input-node certificate, still expressed with the
three already-kernelized fixed machines.  It records no semantic shortcut:
lookahead restores the input tape, the preserving reader consumes the index
and restores the witness, and the return phase restores the evaluator cursor.

The next step is finite-state fusion of these three machines. -/
theorem inputNode000_three_phase
    (witness tail frameStack : BitString)
    (consumed padding i : Nat)
    (hi : i < witness.length) :
    let mode := inputReturnModeOf tail frameStack
    let consumed' := consumed + i + 1
    inputIndexLookaheadMachine.run
        (inputIndexLookaheadFuel i tail frameStack)
        { state := inputIndexLookaheadMachine.initial,
          tape :=
            evalCursorReadTape witness consumed
              (encodeNat i ++ tail) frameStack padding } =
        { state := .halt mode,
          tape :=
            evalCursorReadTape witness consumed
              (encodeNat i ++ tail) frameStack padding } ∧
    preservingReadMachine.run (preservingReadGapFuel consumed i)
        { state := preservingReadMachine.initial,
          tape :=
            evalCursorReadTape witness consumed
              (encodeNat i ++ tail) frameStack padding } =
        { state := .halt (witness.getD i false),
          tape := afterIndexedReadTape witness consumed'
            tail frameStack padding } ∧
    inputAfterReadReturnMachine.run
        (inputAfterReadReturnFuel consumed' tail frameStack)
        { state := .start mode,
          tape := afterIndexedReadTape witness consumed'
            tail frameStack padding } =
        { state := .halt mode,
          tape :=
            match mode with
            | .done =>
                afterIndexedReadTape witness consumed' [] [] padding
            | _ =>
                evalCursorStackEndTape witness consumed'
                  tail frameStack padding } := by
  dsimp
  constructor
  · exact inputIndexLookahead_run_exact
      witness tail frameStack consumed padding i
  constructor
  · rw [inputNode000_full_layout_read
      witness tail frameStack consumed padding i hi]
    exact inputNode000_reader_output_eq_afterReadTape
      witness tail frameStack consumed padding i
  · exact inputAfterReadReturn_run_exact
      witness tail frameStack (consumed + i + 1) padding

#print axioms MCore.Real.P01InputNodePhysicalPipeline.inputIndexLookahead_run_exact
#print axioms MCore.Real.P01InputNodePhysicalPipeline.inputAfterReadReturn_run_exact
#print axioms MCore.Real.P01InputNodePhysicalPipeline.inputNode000_reader_output_eq_afterReadTape
#print axioms MCore.Real.P01InputNodePhysicalPipeline.inputNode000_three_phase

end P01InputNodePhysicalPipeline
end Real
end MCore
