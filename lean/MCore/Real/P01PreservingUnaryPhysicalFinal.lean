import MCore.Real.P01PreservingUnaryWitnessMachine
import MCore.Real.MachineRunLemmas

namespace MCore.Real.P01PreservingUnaryPhysicalFinal

open CanonicalCircuitBits
open P01PreservingUnaryWitnessMachine
open MachineRunLemmas

def finalSeekBlanksConfig
    (remaining passed : Nat)
    (traversed : BitString)
    (b : Bool) (tail : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .finalSeekBlanks
    tape :=
      { left :=
          List.replicate remaining none ++
            traversed.map some ++ none :: (b :: tail).map some
        head := none
        right := List.replicate passed none ++ [some false] } }

@[simp] theorem finalSeekBlanksConfig_state
    (remaining passed : Nat) (traversed : BitString)
    (b : Bool) (tail : BitString) :
    (finalSeekBlanksConfig remaining passed traversed b tail).state =
      .finalSeekBlanks := rfl

theorem indexSome_zero_to_finalSeekBlanks
    (x : Bool) (xs : BitString)
    (b : Bool) (tail : BitString) :
    preservingUnaryReadMachine.run 1
      (indexSomeConfig (x :: xs) (b :: tail) 0) =
      finalSeekBlanksConfig xs.length 0 (x :: xs) b tail := by
  simp [indexSomeConfig, finalSeekBlanksConfig, preservingUnaryReadMachine,
    encodeNat, TM.run, TM.step, Tape.write, Tape.move,
    List.replicate_succ, List.append_assoc]

theorem finalSeekBlanks_step_succ
    (remaining passed : Nat) (traversed : BitString)
    (b : Bool) (tail : BitString) :
    preservingUnaryReadMachine.step
      (finalSeekBlanksConfig (remaining + 1) passed traversed b tail) =
      finalSeekBlanksConfig remaining (passed + 1) traversed b tail := by
  simp [finalSeekBlanksConfig, preservingUnaryReadMachine, TM.step,
    Tape.write, Tape.move, List.replicate_succ, List.append_assoc,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem finalSeekBlanks_run
    (remaining passed : Nat) (traversed : BitString)
    (b : Bool) (tail : BitString) :
    preservingUnaryReadMachine.run remaining
      (finalSeekBlanksConfig remaining passed traversed b tail) =
      finalSeekBlanksConfig 0 (passed + remaining) traversed b tail := by
  induction remaining generalizing passed with
  | zero => rfl
  | succ remaining ih =>
      calc
        preservingUnaryReadMachine.run (Nat.succ remaining)
            (finalSeekBlanksConfig (Nat.succ remaining) passed traversed b tail) =
          preservingUnaryReadMachine.run remaining
            (preservingUnaryReadMachine.step
              (finalSeekBlanksConfig (remaining + 1) passed traversed b tail)) := by
                simp [TM.run, preservingUnaryReadMachine, Nat.succ_eq_add_one]
        _ = preservingUnaryReadMachine.run remaining
            (finalSeekBlanksConfig remaining (passed + 1) traversed b tail) := by
              rw [finalSeekBlanks_step_succ]
        _ = finalSeekBlanksConfig 0 ((passed + 1) + remaining) traversed b tail :=
              ih (passed := passed + 1)
        _ = finalSeekBlanksConfig 0 (passed + Nat.succ remaining) traversed b tail := by
              have h : (passed + 1) + remaining = passed + Nat.succ remaining := by omega
              exact congrArg (fun k => finalSeekBlanksConfig 0 k traversed b tail) h

def finalSeekBitsConfig
    (remaining passedRev : BitString)
    (blankPad : Nat)
    (b : Bool) (tail : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  match remaining with
  | [] =>
      { state := .finalSeekBits
        tape :=
          { left := (b :: tail).map some
            head := none
            right := passedRev.map some ++
              List.replicate blankPad none ++ [some false] } }
  | y :: ys =>
      { state := .finalSeekBits
        tape :=
          { left := ys.map some ++ none :: (b :: tail).map some
            head := some y
            right := passedRev.map some ++
              List.replicate blankPad none ++ [some false] } }

@[simp] theorem finalSeekBitsConfig_state
    (remaining passedRev : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) :
    (finalSeekBitsConfig remaining passedRev blankPad b tail).state =
      .finalSeekBits := by
  cases remaining <;> rfl

theorem finalSeekBlanks_zero_to_bits
    (x : Bool) (xs : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) :
    preservingUnaryReadMachine.run 1
      (finalSeekBlanksConfig 0 blankPad (x :: xs) b tail) =
      finalSeekBitsConfig xs [x] (blankPad + 1) b tail := by
  simp [finalSeekBlanksConfig, finalSeekBitsConfig,
    preservingUnaryReadMachine, TM.run, TM.step,
    Tape.write, Tape.move, List.replicate_succ,
    List.append_assoc, Nat.add_assoc]

theorem finalSeekBits_step_cons
    (y : Bool) (ys passedRev : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) :
    preservingUnaryReadMachine.step
      (finalSeekBitsConfig (y :: ys) passedRev blankPad b tail) =
      finalSeekBitsConfig ys (y :: passedRev) blankPad b tail := by
  cases ys <;>
    simp [finalSeekBitsConfig, preservingUnaryReadMachine,
      TM.step, Tape.write, Tape.move, List.append_assoc]

theorem finalSeekBits_run
    (remaining passedRev : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) :
    preservingUnaryReadMachine.run remaining.length
      (finalSeekBitsConfig remaining passedRev blankPad b tail) =
      finalSeekBitsConfig [] (remaining.reverse ++ passedRev)
        blankPad b tail := by
  induction remaining generalizing passedRev with
  | nil => rfl
  | cons y ys ih =>
      calc
        preservingUnaryReadMachine.run (y :: ys).length
            (finalSeekBitsConfig (y :: ys) passedRev blankPad b tail) =
          preservingUnaryReadMachine.run ys.length
            (preservingUnaryReadMachine.step
              (finalSeekBitsConfig (y :: ys) passedRev blankPad b tail)) := by
                simp [TM.run, preservingUnaryReadMachine]
        _ = preservingUnaryReadMachine.run ys.length
            (finalSeekBitsConfig ys (y :: passedRev) blankPad b tail) := by
              rw [finalSeekBits_step_cons]
        _ = finalSeekBitsConfig []
            (ys.reverse ++ (y :: passedRev)) blankPad b tail :=
              ih (passedRev := y :: passedRev)
        _ = finalSeekBitsConfig []
            ((y :: ys).reverse ++ passedRev) blankPad b tail := by
              simp [List.reverse_cons, List.append_assoc]

def finalReadConfig
    (passedRev : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .finalRead
    tape :=
      { left := tail.map some
        head := some b
        right := none :: passedRev.map some ++
          List.replicate blankPad none ++ [some false] } }

theorem finalSeekBits_marker_to_finalRead
    (passedRev : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) :
    preservingUnaryReadMachine.run 1
      (finalSeekBitsConfig [] passedRev blankPad b tail) =
      finalReadConfig passedRev blankPad b tail := by
  simp [finalSeekBitsConfig, finalReadConfig,
    preservingUnaryReadMachine, TM.run, TM.step,
    Tape.write, Tape.move, List.append_assoc]

def selectedConfig
    (selected : Bool) (passedRev : BitString)
    (blankPad : Nat) (tail : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  { state := if selected then .selectedTrue else .selectedFalse
    tape :=
      { left := some selected :: tail.map some
        head := none
        right := passedRev.map some ++
          List.replicate blankPad none ++ [some false] } }

theorem finalRead_to_selected
    (passedRev : BitString) (blankPad : Nat)
    (b : Bool) (tail : BitString) :
    preservingUnaryReadMachine.run 1
      (finalReadConfig passedRev blankPad b tail) =
      selectedConfig b passedRev blankPad tail := by
  cases b <;>
    simp [finalReadConfig, selectedConfig, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move, List.append_assoc]

theorem finalSelect_run
    (x : Bool) (xs : BitString)
    (b : Bool) (tail : BitString) :
    preservingUnaryReadMachine.run (2 * (x :: xs).length + 2)
      (indexSomeConfig (x :: xs) (b :: tail) 0) =
      selectedConfig b ((x :: xs).reverse) ((x :: xs).length) tail := by
  have h0 := indexSome_zero_to_finalSeekBlanks x xs b tail
  have hb := finalSeekBlanks_run xs.length 0 (x :: xs) b tail
  have he := finalSeekBlanks_zero_to_bits x xs xs.length b tail
  have hs := finalSeekBits_run xs [x] ((x :: xs).length) b tail
  have hm := finalSeekBits_marker_to_finalRead ((x :: xs).reverse)
    ((x :: xs).length) b tail
  have hf := finalRead_to_selected ((x :: xs).reverse)
    ((x :: xs).length) b tail
  rw [show 2 * (x :: xs).length + 2 =
      1 + (xs.length + (1 + (xs.length + (1 + 1)))) by simp; omega]
  rw [run_add, h0]
  rw [run_add, hb]
  rw [run_add, he]
  rw [run_add, hs]
  simp [List.reverse_cons, List.append_assoc] at *
  rw [run_add, hm]
  exact hf

#print axioms MCore.Real.P01PreservingUnaryPhysicalFinal.finalSelect_run

end MCore.Real.P01PreservingUnaryPhysicalFinal
