import MCore.Real.P01WitnessIndexedReadPreserving

namespace MCore
namespace Real
namespace P01WitnessIndexedReadGap

open CanonicalFinalProof
open CanonicalCircuitBits
open MachineRunLemmas
open P01WitnessIndexedReadPreserving

/-- Direct source-bit view of the preserving reader with an arbitrary physical
blank gap between the source cursor and the witness/source separator. -/
def gapReadBitsTape
    (witness : BitString) (gap : Nat) (source : BitString) :
    Tape (Option Bool) :=
  match source with
  | [] =>
      { left := List.replicate gap none ++ (none :: witness.map some),
        head := none,
        right := [] }
  | b :: bs =>
      { left := List.replicate gap none ++ (none :: witness.map some),
        head := some b,
        right := bs.map some }

/-- Unary-index specialization of the gap-aware input layout. -/
def preservingReadGapTape
    (witness : BitString) (gap i : Nat) (tail : BitString) :
    Tape (Option Bool) :=
  gapReadBitsTape witness gap (encodeNat i ++ tail)

/-- Direct moved-prefix representation with the original cursor gap retained.
Each consumed unary marker contributes one additional blank on top of `gap`. -/
def movedGapBitsTape
    (gap : Nat) (moved rest source : BitString) :
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
        head := some x,
        right := xs.map some }

def movedGapBitsConfig
    (gap : Nat) (moved rest source : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .indexMoved,
    tape := movedGapBitsTape gap moved rest source }

def preservingMovedGapConfig
    (gap : Nat) (moved rest : BitString) (n : Nat) (tail : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  movedGapBitsConfig gap moved rest (encodeNat n ++ tail)

@[simp] theorem preservingReadGapTape_zero_gap
    (witness : BitString) (i : Nat) (tail : BitString) :
    preservingReadGapTape witness 0 i tail =
      preservingReadTape witness i tail := by
  cases i <;> rfl

/-- The modified initial-advance state crosses any finite block of physical
blanks and captures the first witness bit. -/
theorem advanceSep_over_blanks
    (k : Nat) (b : Bool)
    (left right : List (Option Bool)) :
    preservingReadMachine.run (k + 2)
      { state := .advanceSep,
        tape :=
          { left := List.replicate k none ++ (some b :: left),
            head := none,
            right := right } } =
      { state := .writeMoved b,
        tape :=
          { left := none :: left,
            head := none,
            right := List.replicate k none ++ right } } := by
  induction k generalizing right with
  | zero =>
      simp [preservingReadMachine, TM.run, TM.step, Tape.write, Tape.move]
  | succ k ih =>
      rw [show Nat.succ k + 2 = (k + 2) + 1 by omega]
      rw [TM.run]
      simp only [show preservingReadMachine.halting (.advanceSep) = false by rfl,
        Bool.false_eq_true, if_false]
      change preservingReadMachine.run (k + 2)
        { state := .advanceSep,
          tape :=
            { left := List.replicate k none ++ (some b :: left),
              head := none,
              right := none :: right } } =
        { state := .writeMoved b,
          tape :=
            { left := none :: left,
              head := none,
              right := List.replicate (Nat.succ k) none ++ right } }
      rw [ih (none :: right)]
      congr 2
      simp [List.replicate_succ, List.append_assoc]

/-- Final zero-index scan across an arbitrary cursor gap. -/
theorem finalSepNoMoved_over_blanks
    (k : Nat) (b : Bool)
    (left right : List (Option Bool)) :
    preservingReadMachine.run (k + 2)
      { state := .finalSepNoMoved,
        tape :=
          { left := List.replicate k none ++ (some b :: left),
            head := none,
            right := right } } =
      { state := .restoreHalt b,
        tape :=
          { left := some b :: left,
            head := none,
            right := List.replicate k none ++ right } } := by
  induction k generalizing right with
  | zero =>
      simp [preservingReadMachine, TM.run, TM.step, Tape.write, Tape.move]
  | succ k ih =>
      rw [show Nat.succ k + 2 = (k + 2) + 1 by omega]
      rw [TM.run]
      simp only [show preservingReadMachine.halting (.finalSepNoMoved) = false by rfl,
        Bool.false_eq_true, if_false]
      change preservingReadMachine.run (k + 2)
        { state := .finalSepNoMoved,
          tape :=
            { left := List.replicate k none ++ (some b :: left),
              head := none,
              right := none :: right } } =
        { state := .restoreHalt b,
          tape :=
            { left := some b :: left,
              head := none,
              right := List.replicate (Nat.succ k) none ++ right } }
      rw [ih (none :: right)]
      congr 2
      simp [List.replicate_succ, List.append_assoc]

/-- `returnBlanks` starting from a stream view. -/
theorem returnBlanks_from_stream
    (k : Nat) (b : Bool)
    (left right : List (Option Bool)) :
    preservingReadMachine.run (k + 1)
      { state := .returnBlanks,
        tape :=
          rightStreamTape left
            (List.replicate k none ++ (some b :: right)) } =
      { state := .indexMoved,
        tape :=
          { left := List.replicate k none ++ left,
            head := some b,
            right := right } } := by
  cases k with
  | zero =>
      simp [rightStreamTape, preservingReadMachine,
        TM.run, TM.step, Tape.write, Tape.move]
  | succ k =>
      simpa [rightStreamTape, List.replicate_succ, List.append_assoc] using
        returnBlanks_over_blanks k b left right

/-- Gap-aware zero-index read.  The witness is unchanged and all pre-existing
cursor blanks remain to the right of the canonical witness/source separator. -/
theorem preservingReadGap_zero
    (b : Bool) (witnessTail tail : BitString) (gap : Nat) :
    preservingReadMachine.run (gap + 4)
      { state := preservingReadMachine.initial,
        tape := preservingReadGapTape (b :: witnessTail) gap 0 tail } =
      { state := .halt b,
        tape :=
          { left := (b :: witnessTail).map some,
            head := none,
            right := List.replicate (gap + 1) none ++ tail.map some } } := by
  let C0 : Configuration PreservingReadState (Option Bool) :=
    { state := preservingReadMachine.initial,
      tape := preservingReadGapTape (b :: witnessTail) gap 0 tail }
  let C1 : Configuration PreservingReadState (Option Bool) :=
    { state := .finalSepNoMoved,
      tape :=
        { left := List.replicate gap none ++ (some b :: witnessTail.map some),
          head := none,
          right := none :: tail.map some } }
  let C2 : Configuration PreservingReadState (Option Bool) :=
    { state := .restoreHalt b,
      tape :=
        { left := some b :: witnessTail.map some,
          head := none,
          right := List.replicate gap none ++ (none :: tail.map some) } }
  let C3 : Configuration PreservingReadState (Option Bool) :=
    { state := .halt b,
      tape :=
        { left := (b :: witnessTail).map some,
          head := none,
          right := List.replicate (gap + 1) none ++ tail.map some } }

  have h01 : preservingReadMachine.run 1 C0 = C1 := by
    dsimp [C0, C1, preservingReadGapTape, gapReadBitsTape]
    cases gap <;>
      simp [preservingReadMachine, encodeNat, TM.run, TM.step,
        Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

  have h12 : preservingReadMachine.run (gap + 2) C1 = C2 := by
    dsimp [C1, C2]
    simpa using
      finalSepNoMoved_over_blanks gap b (witnessTail.map some)
        (none :: tail.map some)

  have h23 : preservingReadMachine.run 1 C2 = C3 := by
    dsimp [C2, C3]
    simp [preservingReadMachine, TM.run, TM.step, Tape.write, Tape.move,
      List.replicate_succ, List.append_assoc]

  rw [show gap + 4 = 1 + ((gap + 2) + 1) by omega]
  rw [run_add, h01]
  rw [run_add, h12]
  simpa [C3] using h23

/-- One first-successor cycle on a direct source beginning in `true`. -/
theorem preservingReadGap_start_true
    (b next : Bool) (witnessTail sourceTail : BitString) (gap : Nat) :
    preservingReadMachine.run (2 * gap + 6)
      { state := preservingReadMachine.initial,
        tape :=
          gapReadBitsTape (b :: witnessTail) gap
            (true :: next :: sourceTail) } =
      movedGapBitsConfig gap [b] witnessTail (next :: sourceTail) := by
  let src : List (Option Bool) := some next :: sourceTail.map some
  let L : List (Option Bool) := some b :: none :: witnessTail.map some
  let C0 : Configuration PreservingReadState (Option Bool) :=
    { state := preservingReadMachine.initial,
      tape := gapReadBitsTape (b :: witnessTail) gap
        (true :: next :: sourceTail) }
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
      tape :=
        rightStreamTape L
          (List.replicate gap none ++ (none :: src)) }
  let after : List (Option Bool) :=
    List.replicate gap none ++ src
  let C4 : Configuration PreservingReadState (Option Bool) :=
    { state := .returnBlanks,
      tape := rightStreamTape (none :: L) after }
  let C5 : Configuration PreservingReadState (Option Bool) :=
    movedGapBitsConfig gap [b] witnessTail (next :: sourceTail)

  have h01 : preservingReadMachine.run 1 C0 = C1 := by
    dsimp [C0, C1, gapReadBitsTape, src]
    cases gap <;>
      simp [preservingReadMachine, TM.run, TM.step,
        Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

  have h12 : preservingReadMachine.run (gap + 2) C1 = C2 := by
    dsimp [C1, C2]
    simpa using
      advanceSep_over_blanks gap b (witnessTail.map some) (none :: src)

  have h23 : preservingReadMachine.run 1 C2 = C3 := by
    dsimp [C2, C3, L, src, rightStreamTape]
    cases gap <;>
      simp [preservingReadMachine, TM.run, TM.step,
        Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

  have h34 : preservingReadMachine.run 1 C3 = C4 := by
    dsimp [C3, C4, L, after, src]
    have hrep :=
      replicate_none_cons gap (some next :: sourceTail.map some)
    rw [show List.replicate gap none ++
        (none :: some next :: sourceTail.map some) =
        none :: (List.replicate gap none ++
          (some next :: sourceTail.map some)) by
      simpa using hrep]
    simpa [returnMovedTape] using
      returnMoved_over_bits ([] : BitString) L after

  have h45 : preservingReadMachine.run (gap + 1) C4 = C5 := by
    dsimp [C4, C5, after, L, src, movedGapBitsConfig, movedGapBitsTape]
    have h :=
      returnBlanks_from_stream gap next
        (none :: some b :: none :: witnessTail.map some)
        (sourceTail.map some)
    rw [h]
    congr 2
    simp [List.replicate_succ, List.append_assoc]

  rw [show 2 * gap + 6 =
      1 + ((gap + 2) + (1 + (1 + (gap + 1)))) by omega]
  rw [run_add, h01]
  rw [run_add, h12]
  rw [run_add, h23]
  rw [run_add, h34]
  exact h45

/-- Unary successor specialization of the first gap-aware cycle. -/
theorem preservingReadGap_start_successor
    (b : Bool) (witnessTail tail : BitString) (gap n : Nat) :
    preservingReadMachine.run (2 * gap + 6)
      { state := preservingReadMachine.initial,
        tape := preservingReadGapTape (b :: witnessTail) gap (n + 1) tail } =
      preservingMovedGapConfig gap [b] witnessTail n tail := by
  cases n with
  | zero =>
      simpa [preservingReadGapTape, preservingMovedGapConfig,
        gapReadBitsTape, encodeNat, List.append_assoc] using
        preservingReadGap_start_true b false witnessTail tail gap
  | succ n =>
      simpa [preservingReadGapTape, preservingMovedGapConfig,
        gapReadBitsTape, encodeNat, List.append_assoc] using
        preservingReadGap_start_true b true witnessTail
          (encodeNat n ++ tail) gap

#print axioms MCore.Real.P01WitnessIndexedReadGap.preservingReadGap_zero
#print axioms MCore.Real.P01WitnessIndexedReadGap.preservingReadGap_start_successor

end P01WitnessIndexedReadGap
end Real
end MCore
