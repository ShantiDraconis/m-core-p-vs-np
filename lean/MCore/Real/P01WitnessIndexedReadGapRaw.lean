import MCore.Real.P01WitnessIndexedReadGap

namespace MCore
namespace Real
namespace P01WitnessIndexedReadGapRaw

open CanonicalFinalProof
open CanonicalCircuitBits
open MachineRunLemmas
open P01WitnessIndexedReadPreserving
open P01WitnessIndexedReadGap

/-- Raw-symbol source view.  Unlike \`gapReadBitsTape\`, the suffix may contain
physical separator blanks, frame bits, and padding. -/
def gapReadRawTape
    (witness : BitString) (gap : Nat)
    (source : List (Option Bool)) :
    Tape (Option Bool) :=
  match source with
  | [] =>
      { left := List.replicate gap none ++ (none :: witness.map some),
        head := none,
        right := [] }
  | x :: xs =>
      { left := List.replicate gap none ++ (none :: witness.map some),
        head := x,
        right := xs }

/-- Canonical unary index followed by an arbitrary physical suffix. -/
def preservingReadGapRawTape
    (witness : BitString) (gap i : Nat)
    (rawTail : List (Option Bool)) :
    Tape (Option Bool) :=
  gapReadRawTape witness gap ((encodeNat i).map some ++ rawTail)

/-- Moved-prefix view with an arbitrary physical source suffix. -/
def movedGapRawBitsTape
    (gap : Nat) (moved rest : BitString)
    (source : List (Option Bool)) :
    Tape (Option Bool) :=
  match source with
  | [] =>
      { left :=
          List.replicate (gap + moved.length) none ++
            moved.map some ++ (none :: rest.map some),
        head := none,
        right := [] }
  | x :: xs =>
      { left :=
          List.replicate (gap + moved.length) none ++
            moved.map some ++ (none :: rest.map some),
        head := x,
        right := xs }

def movedGapRawBitsConfig
    (gap : Nat) (moved rest : BitString)
    (source : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .indexMoved,
    tape := movedGapRawBitsTape gap moved rest source }

def preservingMovedGapRawConfig
    (gap : Nat) (moved rest : BitString)
    (n : Nat) (rawTail : List (Option Bool)) :
    Configuration PreservingReadState (Option Bool) :=
  movedGapRawBitsConfig gap moved rest
    ((encodeNat n).map some ++ rawTail)

/-- Compatibility with the already-certified bit-only gap layout. -/
theorem preservingReadGapRawTape_bits
    (witness tail : BitString) (gap i : Nat) :
    preservingReadGapRawTape witness gap i (tail.map some) =
      preservingReadGapTape witness gap i tail := by
  cases i <;>
    simp [preservingReadGapRawTape, preservingReadGapTape,
      gapReadRawTape, gapReadBitsTape, encodeNat,
      List.map_append, List.append_assoc]

/-- Gap-aware zero-index read with an arbitrary physical suffix. -/
theorem preservingReadGapRaw_zero
    (b : Bool) (witnessTail : BitString)
    (rawTail : List (Option Bool)) (gap : Nat) :
    preservingReadMachine.run (gap + 4)
      { state := preservingReadMachine.initial,
        tape :=
          preservingReadGapRawTape
            (b :: witnessTail) gap 0 rawTail } =
      { state := .halt b,
        tape :=
          { left := (b :: witnessTail).map some,
            head := none,
            right := List.replicate (gap + 1) none ++ rawTail } } := by
  let C0 : Configuration PreservingReadState (Option Bool) :=
    { state := preservingReadMachine.initial,
      tape := preservingReadGapRawTape
        (b :: witnessTail) gap 0 rawTail }
  let C1 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalSepNoMoved,
      tape :=
        { left := List.replicate gap none ++
            (some b :: witnessTail.map some),
          head := none,
          right := none :: rawTail } }
  let C2 : Configuration PreservingReadState (Option Bool) :=
    { state := .restoreHalt b,
      tape :=
        { left := some b :: witnessTail.map some,
          head := none,
          right := List.replicate gap none ++ (none :: rawTail) } }
  let C3 : Configuration PreservingReadState (Option Bool) :=
    { state := .halt b,
      tape :=
        { left := (b :: witnessTail).map some,
          head := none,
          right := List.replicate (gap + 1) none ++ rawTail } }

  have h01 : preservingReadMachine.run 1 C0 = C1 := by
    dsimp [C0, C1, preservingReadGapRawTape, gapReadRawTape]
    rw [replicate_none_cons gap (some b :: witnessTail.map some)]
    simp [preservingReadMachine, encodeNat, TM.run, TM.step,
      Tape.write, Tape.move, List.append_assoc]

  have h12 : preservingReadMachine.run (gap + 2) C1 = C2 := by
    dsimp [C1, C2]
    simpa using
      finalSepNoMoved_over_blanks gap b
        (witnessTail.map some) (none :: rawTail)

  have h23 : preservingReadMachine.run 1 C2 = C3 := by
    dsimp [C2, C3]
    have hr := replicate_none_cons gap rawTail
    simpa [preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.replicate_succ,
      List.append_assoc] using hr

  rw [show gap + 4 = 1 + ((gap + 2) + 1) by omega]
  rw [run_add, h01]
  rw [run_add, h12]
  simpa [C3] using h23

/-- First true unary marker with arbitrary physical suffix after the next unary
symbol. -/
theorem preservingReadGapRaw_start_true
    (b next : Bool) (witnessTail : BitString)
    (rawTail : List (Option Bool)) (gap : Nat) :
    preservingReadMachine.run (2 * gap + 6)
      { state := preservingReadMachine.initial,
        tape :=
          gapReadRawTape (b :: witnessTail) gap
            (some true :: some next :: rawTail) } =
      movedGapRawBitsConfig gap [b] witnessTail
        (some next :: rawTail) := by
  let src : List (Option Bool) := some next :: rawTail
  let L : List (Option Bool) := some b :: none :: witnessTail.map some
  let C0 : Configuration PreservingReadState (Option Bool) :=
    { state := preservingReadMachine.initial,
      tape := gapReadRawTape (b :: witnessTail) gap
        (some true :: some next :: rawTail) }
  let C1 : Configuration PreservingReadState (Option Bool) :=
    { state := .advanceSep,
      tape :=
        { left := List.replicate gap none ++
            (some b :: witnessTail.map some),
          head := none,
          right := none :: src } }
  let C2 : Configuration PreservingReadState (Option Bool) :=
    { state := .writeMoved b,
      tape :=
        { left := none :: witnessTail.map some,
          head := none,
          right := List.replicate gap none ++ (none :: src) } }
  let C3 : Configuration PreservingReadState (Option Bool) :=
    { state := .returnMoved,
      tape := rightStreamTape L
        (List.replicate gap none ++ (none :: src)) }
  let after : List (Option Bool) :=
    List.replicate gap none ++ src
  let C4 : Configuration PreservingReadState (Option Bool) :=
    { state := .returnBlanks,
      tape := rightStreamTape (none :: L) after }
  let C5 : Configuration PreservingReadState (Option Bool) :=
    movedGapRawBitsConfig gap [b] witnessTail
      (some next :: rawTail)

  have h01 : preservingReadMachine.run 1 C0 = C1 := by
    dsimp [C0, C1, gapReadRawTape, src]
    rw [replicate_none_cons gap (some b :: witnessTail.map some)]
    simp [preservingReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.append_assoc]

  have h12 : preservingReadMachine.run (gap + 2) C1 = C2 := by
    dsimp [C1, C2]
    simpa using
      advanceSep_over_blanks gap b
        (witnessTail.map some) (none :: src)

  have h23 : preservingReadMachine.run 1 C2 = C3 := by
    dsimp [C2, C3, L, src, rightStreamTape]
    cases gap <;>
      simp [preservingReadMachine, TM.run, TM.step,
        Tape.write, Tape.move, List.replicate_succ,
        List.append_assoc]

  have h34 : preservingReadMachine.run 1 C3 = C4 := by
    dsimp [C3, C4, L, after, src]
    have hrep := replicate_none_cons gap (some next :: rawTail)
    rw [show List.replicate gap none ++
        (none :: some next :: rawTail) =
        none :: (List.replicate gap none ++
          (some next :: rawTail)) by simpa using hrep]
    simpa [returnMovedTape] using
      returnMoved_over_bits ([] : BitString) L after

  have h45 : preservingReadMachine.run (gap + 1) C4 = C5 := by
    dsimp [C4, C5, after, L, src,
      movedGapRawBitsConfig, movedGapRawBitsTape]
    have h :=
      returnBlanks_from_stream gap next
        (none :: some b :: none :: witnessTail.map some) rawTail
    rw [h]
    congr 2
    have hr :=
      replicate_none_cons gap
        (some b :: none :: witnessTail.map some)
    simpa [List.replicate_succ, List.append_assoc] using hr

  rw [show 2 * gap + 6 =
      1 + ((gap + 2) + (1 + (1 + (gap + 1)))) by omega]
  rw [run_add, h01]
  rw [run_add, h12]
  rw [run_add, h23]
  rw [run_add, h34]
  exact h45

/-- Unary successor specialization with a raw suffix. -/
theorem preservingReadGapRaw_start_successor
    (b : Bool) (witnessTail : BitString)
    (rawTail : List (Option Bool))
    (gap n : Nat) :
    preservingReadMachine.run (2 * gap + 6)
      { state := preservingReadMachine.initial,
        tape := preservingReadGapRawTape
          (b :: witnessTail) gap (n + 1) rawTail } =
      preservingMovedGapRawConfig gap [b] witnessTail n rawTail := by
  cases n with
  | zero =>
      simpa [preservingReadGapRawTape, preservingMovedGapRawConfig,
        gapReadRawTape, encodeNat, List.map_append,
        List.append_assoc] using
        preservingReadGapRaw_start_true
          b false witnessTail rawTail gap
  | succ n =>
      simpa [preservingReadGapRawTape, preservingMovedGapRawConfig,
        gapReadRawTape, encodeNat, List.map_append,
        List.append_assoc] using
        preservingReadGapRaw_start_true
          b true witnessTail
          ((encodeNat n).map some ++ rawTail) gap

#print axioms MCore.Real.P01WitnessIndexedReadGapRaw.preservingReadGapRaw_zero
#print axioms MCore.Real.P01WitnessIndexedReadGapRaw.preservingReadGapRaw_start_successor

end P01WitnessIndexedReadGapRaw
end Real
end MCore
