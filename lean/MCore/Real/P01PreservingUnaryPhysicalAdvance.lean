import MCore.Real.P01PreservingUnaryWitnessMachine
import MCore.Real.MachineRunLemmas

namespace MCore.Real.P01PreservingUnaryPhysicalAdvance

open CanonicalFinalProof
open CanonicalCircuitBits
open P01PreservingUnaryWitnessMachine
open MachineRunLemmas

/-- Exact seekBlanks state: `remaining` erased blanks are still to the left,
while `passed` erased blanks have already been crossed and sit to the right.
The current head is itself a blank. -/
def seekBlanksConfig
    (remaining passed : Nat)
    (traversed : BitString)
    (b : Bool) (tail : BitString)
    (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .seekBlanks
    tape :=
      { left :=
          List.replicate remaining none ++
            traversed.map some ++ none :: (b :: tail).map some
        head := none
        right :=
          List.replicate (passed + 1) none ++
            (encodeNat n).map some } }

@[simp] theorem seekBlanksConfig_state
    (remaining passed : Nat) (traversed : BitString)
    (b : Bool) (tail : BitString) (n : Nat) :
    (seekBlanksConfig remaining passed traversed b tail n).state =
      .seekBlanks := rfl

/-- One physical left move transfers one erased blank from remaining to passed. -/
theorem seekBlanks_step_succ
    (remaining passed : Nat) (traversed : BitString)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.step
      (seekBlanksConfig (remaining + 1) passed traversed b tail n) =
      seekBlanksConfig remaining (passed + 1) traversed b tail n := by
  simp [seekBlanksConfig, preservingUnaryReadMachine, TM.step,
    Tape.write, Tape.move, List.replicate_succ, List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Scan all remaining erased blanks. -/
theorem seekBlanks_run
    (remaining passed : Nat) (traversed : BitString)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run remaining
      (seekBlanksConfig remaining passed traversed b tail n) =
      seekBlanksConfig 0 (passed + remaining) traversed b tail n := by
  induction remaining generalizing passed with
  | zero =>
      rfl
  | succ remaining ih =>
      calc
        preservingUnaryReadMachine.run (Nat.succ remaining)
            (seekBlanksConfig (Nat.succ remaining) passed traversed b tail n) =
          preservingUnaryReadMachine.run remaining
            (preservingUnaryReadMachine.step
              (seekBlanksConfig (remaining + 1) passed traversed b tail n)) := by
                simp [TM.run, preservingUnaryReadMachine, Nat.succ_eq_add_one]
        _ = preservingUnaryReadMachine.run remaining
            (seekBlanksConfig remaining (passed + 1) traversed b tail n) := by
              rw [seekBlanks_step_succ]
        _ = seekBlanksConfig 0 ((passed + 1) + remaining) traversed b tail n :=
              ih (passed := passed + 1)
        _ = seekBlanksConfig 0 (passed + Nat.succ remaining) traversed b tail n := by
              have hNat :
                  ((passed + 1) + remaining) =
                    (passed + Nat.succ remaining) := by
                omega
              exact congrArg
                (fun k => seekBlanksConfig 0 k traversed b tail n) hNat

/-- With no erased blank left, the next step sees the first traversed bit. -/
def seekBitsEntryConfig
    (x : Bool) (xs : BitString)
    (passed : Nat)
    (b : Bool) (tail : BitString)
    (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .seekBlanks
    tape :=
      { left := xs.map some ++ none :: (b :: tail).map some
        head := some x
        right :=
          List.replicate (passed + 1) none ++ (encodeNat n).map some } }

theorem seekBlanks_zero_step_to_bits
    (x : Bool) (xs : BitString) (passed : Nat)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run 1
      (seekBlanksConfig 0 passed (x :: xs) b tail n) =
      seekBitsEntryConfig x xs (passed + 1) b tail n := by
  simp [seekBlanksConfig, seekBitsEntryConfig, preservingUnaryReadMachine,
    TM.run, TM.step, Tape.write, Tape.move, List.replicate_succ,
    List.append_assoc, Nat.add_assoc]

/-- seekBits state after one traversed bit has been crossed. -/
def seekBitsConfig
    (remaining : BitString)
    (passedRev : BitString)
    (blankPad : Nat)
    (b : Bool) (tail : BitString)
    (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  match remaining with
  | [] =>
      { state := .seekBits
        tape :=
          { left := (b :: tail).map some
            head := none
            right :=
              passedRev.map some ++
                List.replicate blankPad none ++ (encodeNat n).map some } }
  | y :: ys =>
      { state := .seekBits
        tape :=
          { left := ys.map some ++ none :: (b :: tail).map some
            head := some y
            right :=
              passedRev.map some ++
                List.replicate blankPad none ++ (encodeNat n).map some } }

theorem seekBits_entry_step
    (x : Bool) (xs : BitString) (passed : Nat)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run 1
      (seekBitsEntryConfig x xs passed b tail n) =
      seekBitsConfig xs [x] (passed + 1) b tail n := by
  cases xs <;>
    simp [seekBitsEntryConfig, seekBitsConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move, List.append_assoc]


@[simp] theorem seekBitsConfig_state
    (remaining passedRev : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) (n : Nat) :
    (seekBitsConfig remaining passedRev blankPad b tail n).state = .seekBits := by
  cases remaining <;> rfl

/-- One traversed witness bit is crossed by seekBits. -/
theorem seekBits_step_cons
    (y : Bool) (ys passedRev : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.step
      (seekBitsConfig (y :: ys) passedRev blankPad b tail n) =
      seekBitsConfig ys (y :: passedRev) blankPad b tail n := by
  cases ys <;>
    simp [seekBitsConfig, preservingUnaryReadMachine, TM.step,
      Tape.write, Tape.move, List.append_assoc]

/-- Scan all traversed witness bits until the marker blank is under the head. -/
theorem seekBits_run
    (remaining passedRev : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run remaining.length
      (seekBitsConfig remaining passedRev blankPad b tail n) =
      seekBitsConfig [] (remaining.reverse ++ passedRev) blankPad b tail n := by
  induction remaining generalizing passedRev with
  | nil =>
      rfl
  | cons y ys ih =>
      calc
        preservingUnaryReadMachine.run (y :: ys).length
            (seekBitsConfig (y :: ys) passedRev blankPad b tail n) =
          preservingUnaryReadMachine.run ys.length
            (preservingUnaryReadMachine.step
              (seekBitsConfig (y :: ys) passedRev blankPad b tail n)) := by
                simp [TM.run, preservingUnaryReadMachine]
        _ = preservingUnaryReadMachine.run ys.length
            (seekBitsConfig ys (y :: passedRev) blankPad b tail n) := by
              rw [seekBits_step_cons]
        _ = seekBitsConfig [] (ys.reverse ++ (y :: passedRev)) blankPad b tail n :=
              ih (passedRev := y :: passedRev)
        _ = seekBitsConfig [] ((y :: ys).reverse ++ passedRev) blankPad b tail n := by
              simp [List.reverse_cons, List.append_assoc]

/-- At the marker blank, one physical step enters shiftRead and moves onto the
next witness bit that will be shifted across the marker. -/
def shiftReadConfig
    (passedRev : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .shiftRead
    tape :=
      { left := tail.map some
        head := some b
        right := none :: passedRev.map some ++
          List.replicate blankPad none ++ (encodeNat n).map some } }

theorem seekBits_marker_to_shiftRead
    (passedRev : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run 1
      (seekBitsConfig [] passedRev blankPad b tail n) =
      shiftReadConfig passedRev blankPad b tail n := by
  simp [seekBitsConfig, shiftReadConfig, preservingUnaryReadMachine,
    TM.run, TM.step, Tape.write, Tape.move, List.append_assoc]


/-- Configuration immediately after shiftRead has erased the selected witness
cell and moved right onto the marker blank. -/
def carryConfig
    (selected : Bool)
    (passedRev : BitString) (blankPad : Nat)
    (tail : BitString) (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := if selected then .carryTrue else .carryFalse
    tape :=
      { left := none :: tail.map some
        head := none
        right := passedRev.map some ++
          List.replicate blankPad none ++ (encodeNat n).map some } }

/-- shiftRead performs the physical erase-and-carry step. -/
theorem shiftRead_to_carry
    (passedRev : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run 1
      (shiftReadConfig passedRev blankPad b tail n) =
      carryConfig b passedRev blankPad tail n := by
  cases b <;>
    simp [shiftReadConfig, carryConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move, List.append_assoc]

/-- After carrying the selected bit back onto the marker cell, control enters
returnFromMarker and moves left to the new marker blank. -/
def returnFromMarkerConfig
    (selected : Bool)
    (passedRev : BitString) (blankPad : Nat)
    (tail : BitString) (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .returnFromMarker
    tape :=
      { left := tail.map some
        head := none
        right := some selected :: passedRev.map some ++
          List.replicate blankPad none ++ (encodeNat n).map some } }

theorem carry_to_returnFromMarker
    (selected : Bool)
    (passedRev : BitString) (blankPad : Nat)
    (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run 1
      (carryConfig selected passedRev blankPad tail n) =
      returnFromMarkerConfig selected passedRev blankPad tail n := by
  cases selected <;>
    simp [carryConfig, returnFromMarkerConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move, List.append_assoc]

/-- returnBits scans right across the restored selected bit and the traversed
prefix.  `leftAcc` is the exact physical left stack accumulated so far. -/
def returnBitsConfig
    (remaining : BitString)
    (leftAcc : List (Option Bool))
    (blankPad : Nat) (n : Nat) :
    Configuration PreservingReadState (Option Bool) :=
  match remaining with
  | [] =>
      { state := .returnBits
        tape :=
          { left := leftAcc
            head := none
            right := List.replicate blankPad none ++ (encodeNat n).map some } }
  | x :: xs =>
      { state := .returnBits
        tape :=
          { left := leftAcc
            head := some x
            right := xs.map some ++
              List.replicate blankPad none ++ (encodeNat n).map some } }

/-- returnFromMarker crosses the marker blank.  The selected bit becomes the
first returnBits head and the moved marker blank is now in the left stack. -/
theorem returnFromMarker_to_returnBits
    (selected : Bool)
    (passedRev : BitString) (blankPad : Nat)
    (tail : BitString) (n : Nat) :
    preservingUnaryReadMachine.run 1
      (returnFromMarkerConfig selected passedRev blankPad tail n) =
      returnBitsConfig (selected :: passedRev) (none :: tail.map some)
        blankPad n := by
  simp [returnFromMarkerConfig, returnBitsConfig,
    preservingUnaryReadMachine, TM.run, TM.step,
    Tape.write, Tape.move, List.append_assoc]

@[simp] theorem returnBitsConfig_state
    (remaining : BitString) (leftAcc : List (Option Bool))
    (blankPad : Nat) (n : Nat) :
    (returnBitsConfig remaining leftAcc blankPad n).state = .returnBits := by
  cases remaining <;> rfl

/-- One physical returnBits step preserves the current bit and moves right. -/
theorem returnBits_step_cons
    (x : Bool) (xs : BitString) (leftAcc : List (Option Bool))
    (blankPad : Nat) (n : Nat) :
    preservingUnaryReadMachine.step
      (returnBitsConfig (x :: xs) leftAcc blankPad n) =
      returnBitsConfig xs (some x :: leftAcc) blankPad n := by
  cases xs <;>
    simp [returnBitsConfig, preservingUnaryReadMachine, TM.step,
      Tape.write, Tape.move, List.append_assoc]

/-- Exact physical scan of all restored bits until the blank separator is under
the head.  The scanned sequence is reversed into the physical left stack. -/
theorem returnBits_run
    (remaining : BitString) (leftAcc : List (Option Bool))
    (blankPad : Nat) (n : Nat) :
    preservingUnaryReadMachine.run remaining.length
      (returnBitsConfig remaining leftAcc blankPad n) =
      returnBitsConfig [] (remaining.reverse.map some ++ leftAcc) blankPad n := by
  induction remaining generalizing leftAcc with
  | nil =>
      rfl
  | cons x xs ih =>
      calc
        preservingUnaryReadMachine.run (x :: xs).length
            (returnBitsConfig (x :: xs) leftAcc blankPad n) =
          preservingUnaryReadMachine.run xs.length
            (preservingUnaryReadMachine.step
              (returnBitsConfig (x :: xs) leftAcc blankPad n)) := by
                simp [TM.run, preservingUnaryReadMachine]
        _ = preservingUnaryReadMachine.run xs.length
            (returnBitsConfig xs (some x :: leftAcc) blankPad n) := by
              rw [returnBits_step_cons]
        _ = returnBitsConfig []
            (xs.reverse.map some ++ (some x :: leftAcc)) blankPad n :=
              ih (leftAcc := some x :: leftAcc)
        _ = returnBitsConfig []
            ((x :: xs).reverse.map some ++ leftAcc) blankPad n := by
              simp [List.reverse_cons, List.map_append, List.append_assoc]

#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.returnFromMarker_to_returnBits
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.returnBits_step_cons
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.returnBits_run

#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.shiftRead_to_carry
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.carry_to_returnFromMarker
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.returnFromMarker_to_returnBits

#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBits_step_cons
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBits_run
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBits_marker_to_shiftRead

#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBlanks_step_succ
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBlanks_run
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBlanks_zero_step_to_bits
#print axioms MCore.Real.P01PreservingUnaryPhysicalAdvance.seekBits_entry_step

end MCore.Real.P01PreservingUnaryPhysicalAdvance
