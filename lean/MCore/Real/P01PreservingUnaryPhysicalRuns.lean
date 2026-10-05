import MCore.Real.P01PreservingUnaryWitnessMachine
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01PreservingUnaryPhysicalRuns

open CanonicalFinalProof
open CanonicalCircuitBits
open P01WitnessIndexedRead
open P01PreservingUnaryWitnessMachine
open MachineRunLemmas

theorem replicate_none_extend
    (k : Nat) (right : List (Option Bool)) :
    List.replicate (k + 1) none ++ (none :: right) =
      List.replicate (k + 2) none ++ right := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [Nat.succ_add, List.replicate_succ, List.cons_append]
      congr 1

theorem seekBlanks_over_blanks
    (k : Nat) (b : Bool)
    (left right : List (Option Bool)) :
    preservingUnaryReadMachine.run (k + 1)
      { state := .seekBlanks
        tape :=
          { left := List.replicate k none ++ (some b :: left)
            head := none
            right := right } } =
      { state := .seekBlanks
        tape :=
          { left := left
            head := some b
            right := List.replicate (k + 1) none ++ right } } := by
  induction k generalizing right with
  | zero =>
      simp [preservingUnaryReadMachine, TM.run, TM.step,
        Tape.write, Tape.move]
  | succ k ih =>
      rw [show Nat.succ k + 1 = (k + 1) + 1 by omega]
      rw [TM.run]
      simp only [show preservingUnaryReadMachine.halting (.seekBlanks) = false by rfl,
        Bool.false_eq_true, if_false]
      change preservingUnaryReadMachine.run (k + 1)
        { state := .seekBlanks
          tape :=
            { left := List.replicate k none ++ (some b :: left)
              head := none
              right := none :: right } } =
        { state := .seekBlanks
          tape :=
            { left := left
              head := some b
              right := List.replicate (Nat.succ k + 1) none ++ right } }
      rw [ih (none :: right)]
      apply congrArg
        (fun r : List (Option Bool) =>
          ({ state := .seekBlanks
             tape := { left := left, head := some b, right := r } } :
            Configuration PreservingReadState (Option Bool)))
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        replicate_none_extend k right

def seekBitsTape
    (bits : BitString) (b : Bool)
    (left right : List (Option Bool)) :
    Tape (Option Bool) :=
  match bits with
  | [] =>
      { left := some b :: left
        head := none
        right := right }
  | x :: xs =>
      { left := xs.map some ++ (none :: some b :: left)
        head := some x
        right := right }

theorem seekBlanks_step_bit
    (first b : Bool) (bits : BitString)
    (left right : List (Option Bool)) :
    preservingUnaryReadMachine.step
      { state := .seekBlanks
        tape :=
          { left := bits.map some ++ (none :: some b :: left)
            head := some first
            right := right } } =
      { state := .seekBits
        tape := seekBitsTape bits b left (some first :: right) } := by
  cases bits <;>
    simp [seekBitsTape, preservingUnaryReadMachine,
      TM.step, Tape.write, Tape.move]

theorem seekBits_step_cons
    (x b : Bool) (xs : BitString)
    (left right : List (Option Bool)) :
    preservingUnaryReadMachine.step
      { state := .seekBits
        tape := seekBitsTape (x :: xs) b left right } =
      { state := .seekBits
        tape := seekBitsTape xs b left (some x :: right) } := by
  cases xs <;>
    simp [seekBitsTape, preservingUnaryReadMachine,
      TM.step, Tape.write, Tape.move]

theorem seekBits_over_bits
    (bits : BitString) (b : Bool)
    (left right : List (Option Bool)) :
    preservingUnaryReadMachine.run (bits.length + 1)
      { state := .seekBits
        tape := seekBitsTape bits b left right } =
      { state := .shiftRead
        tape :=
          { left := left
            head := some b
            right := none :: (bits.reverse.map some ++ right) } } := by
  induction bits generalizing right with
  | nil =>
      simp [seekBitsTape, preservingUnaryReadMachine,
        TM.run, TM.step, Tape.write, Tape.move]
  | cons x xs ih =>
      rw [show (x :: xs).length + 1 = (xs.length + 1) + 1 by simp]
      rw [TM.run]
      simp only [show preservingUnaryReadMachine.halting (.seekBits) = false by rfl,
        Bool.false_eq_true, if_false]
      rw [seekBits_step_cons]
      rw [ih (some x :: right)]
      apply congrArg
        (fun r : List (Option Bool) =>
          ({ state := .shiftRead
             tape := { left := left, head := some b, right := r } } :
            Configuration PreservingReadState (Option Bool)))
      simp [List.reverse_cons, List.map_append, List.append_assoc]

def rightStreamTape
    (left stream : List (Option Bool)) :
    Tape (Option Bool) :=
  match stream with
  | [] =>
      { left := left, head := none, right := [] }
  | x :: xs =>
      { left := left, head := x, right := xs }

theorem shift_carry_return_to_stream
    (b : Bool) (left stream : List (Option Bool)) :
    preservingUnaryReadMachine.run 3
      { state := .shiftRead
        tape := { left := left, head := some b, right := none :: stream } } =
      { state := .returnBits
        tape := rightStreamTape (none :: left) (some b :: stream) } := by
  cases b <;> cases stream <;>
    simp [rightStreamTape, preservingUnaryReadMachine,
      TM.run, TM.step, Tape.write, Tape.move]

def returnBitsTape
    (bits : BitString)
    (left after : List (Option Bool)) :
    Tape (Option Bool) :=
  match bits with
  | [] =>
      rightStreamTape left (none :: after)
  | x :: xs =>
      { left := left
        head := some x
        right := xs.map some ++ (none :: after) }

theorem returnBits_step_cons
    (x : Bool) (xs : BitString)
    (left after : List (Option Bool)) :
    preservingUnaryReadMachine.step
      { state := .returnBits
        tape := returnBitsTape (x :: xs) left after } =
      { state := .returnBits
        tape := returnBitsTape xs (some x :: left) after } := by
  cases xs <;>
    simp [returnBitsTape, rightStreamTape, preservingUnaryReadMachine,
      TM.step, Tape.write, Tape.move]

theorem returnBits_over_bits
    (bits : BitString)
    (left after : List (Option Bool)) :
    preservingUnaryReadMachine.run (bits.length + 1)
      { state := .returnBits
        tape := returnBitsTape bits left after } =
      { state := .returnBlanks
        tape :=
          rightStreamTape
            (none :: (bits.reverse.map some ++ left))
            after } := by
  induction bits generalizing left with
  | nil =>
      cases after <;>
        simp [returnBitsTape, rightStreamTape, preservingUnaryReadMachine,
          TM.run, TM.step, Tape.write, Tape.move]
  | cons x xs ih =>
      rw [show (x :: xs).length + 1 = (xs.length + 1) + 1 by simp]
      rw [TM.run]
      simp only [show preservingUnaryReadMachine.halting (.returnBits) = false by rfl,
        Bool.false_eq_true, if_false]
      rw [returnBits_step_cons]
      rw [ih (some x :: left)]
      apply congrArg
        (fun l : List (Option Bool) =>
          ({ state := .returnBlanks
             tape := rightStreamTape l after } :
            Configuration PreservingReadState (Option Bool)))
      simp [List.reverse_cons, List.map_append, List.append_assoc]

theorem returnBlanks_over_blanks
    (k : Nat) (b : Bool)
    (left right : List (Option Bool)) :
    preservingUnaryReadMachine.run (k + 2)
      { state := .returnBlanks
        tape :=
          { left := left
            head := none
            right := List.replicate k none ++ (some b :: right) } } =
      { state := .indexSome
        tape :=
          { left := List.replicate (k + 1) none ++ left
            head := some b
            right := right } } := by
  induction k generalizing left with
  | zero =>
      simp [preservingUnaryReadMachine, TM.run, TM.step,
        Tape.write, Tape.move]
  | succ k ih =>
      rw [show Nat.succ k + 2 = (k + 2) + 1 by omega]
      rw [TM.run]
      simp only [show preservingUnaryReadMachine.halting (.returnBlanks) = false by rfl,
        Bool.false_eq_true, if_false]
      change preservingUnaryReadMachine.run (k + 2)
        { state := .returnBlanks
          tape :=
            { left := none :: left
              head := none
              right := List.replicate k none ++ (some b :: right) } } =
        { state := .indexSome
          tape :=
            { left := List.replicate (Nat.succ k + 1) none ++ left
              head := some b
              right := right } }
      rw [ih (none :: left)]
      apply congrArg
        (fun l : List (Option Bool) =>
          ({ state := .indexSome
             tape := { left := l, head := some b, right := right } } :
            Configuration PreservingReadState (Option Bool)))
      simpa [Nat.succ_eq_add_one, Nat.add_assoc] using
        replicate_none_extend k left

theorem replicate_none_cons
    (k : Nat) (source : List (Option Bool)) :
    List.replicate k none ++ (none :: source) =
      none :: (List.replicate k none ++ source) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simpa [List.replicate_succ] using
        congrArg (fun xs : List (Option Bool) => none :: xs) ih

theorem rightStreamTape_blank_block
    (k : Nat)
    (left source : List (Option Bool)) :
    rightStreamTape left
        (List.replicate k none ++ (none :: source)) =
      { left := left
        head := none
        right := List.replicate k none ++ source } := by
  rw [replicate_none_cons]
  rfl

def indexSomeBitsTape
    (pref suffix source : BitString) :
    Tape (Option Bool) :=
  match source with
  | [] =>
      { left := List.replicate pref.length none ++
          pref.map some ++ none :: suffix.map some
        head := none
        right := [] }
  | x :: xs =>
      { left := List.replicate pref.length none ++
          pref.map some ++ none :: suffix.map some
        head := some x
        right := xs.map some }

def indexSomeBitsConfig
    (pref suffix source : BitString) :
    Configuration PreservingReadState (Option Bool) :=
  { state := .indexSome
    tape := indexSomeBitsTape pref suffix source }

theorem indexSomeConfig_eq_bits
    (pref suffix : BitString) (n : Nat) :
    indexSomeConfig pref suffix n =
      indexSomeBitsConfig pref suffix (encodeNat n) := by
  cases n <;> rfl

theorem indexSome_cycle_bits
    (first b next : Bool)
    (prefTail witnessTail sourceTail : BitString) :
    preservingUnaryReadMachine.run (4 * (first :: prefTail).length + 8)
      (indexSomeBitsConfig
        (first :: prefTail) (b :: witnessTail)
        (true :: next :: sourceTail)) =
      indexSomeBitsConfig
        ((first :: prefTail) ++ [b]) witnessTail
        (next :: sourceTail) := by
  let m : Nat := prefTail.length
  let pref : BitString := first :: prefTail
  let witnessSuffix : List (Option Bool) := witnessTail.map some
  let src : List (Option Bool) := some next :: sourceTail.map some
  let after : List (Option Bool) :=
    List.replicate m none ++ (none :: src)
  let stream : List (Option Bool) :=
    pref.reverse.map some ++ (none :: after)
  let returnedBits : BitString := b :: pref.reverse
  let restoredLeft : List (Option Bool) :=
    none :: (returnedBits.reverse.map some ++ (none :: witnessSuffix))

  let C0 : Configuration PreservingReadState (Option Bool) :=
    indexSomeBitsConfig pref (b :: witnessTail) (true :: next :: sourceTail)
  let C1 : Configuration PreservingReadState (Option Bool) :=
    { state := .seekBlanks
      tape :=
        { left :=
            List.replicate m none ++
              (some first ::
                (prefTail.map some ++
                  (none :: some b :: witnessSuffix)))
          head := none
          right := none :: src } }
  let C2 : Configuration PreservingReadState (Option Bool) :=
    { state := .seekBlanks
      tape :=
        { left :=
            prefTail.map some ++ (none :: some b :: witnessSuffix)
          head := some first
          right := List.replicate (m + 1) none ++ (none :: src) } }
  let C3 : Configuration PreservingReadState (Option Bool) :=
    { state := .seekBits
      tape := seekBitsTape prefTail b witnessSuffix
        (some first :: (List.replicate (m + 1) none ++ (none :: src))) }
  let C4 : Configuration PreservingReadState (Option Bool) :=
    { state := .shiftRead
      tape :=
        { left := witnessSuffix
          head := some b
          right := none :: stream } }
  let C5 : Configuration PreservingReadState (Option Bool) :=
    { state := .returnBits
      tape := returnBitsTape returnedBits (none :: witnessSuffix) after }
  let C6 : Configuration PreservingReadState (Option Bool) :=
    { state := .returnBlanks
      tape := rightStreamTape restoredLeft after }
  let C6e : Configuration PreservingReadState (Option Bool) :=
    { state := .returnBlanks
      tape :=
        { left := restoredLeft
          head := none
          right := List.replicate m none ++ src } }
  let C7e : Configuration PreservingReadState (Option Bool) :=
    { state := .indexSome
      tape :=
        { left := List.replicate (m + 1) none ++ restoredLeft
          head := some next
          right := sourceTail.map some } }
  let C7 : Configuration PreservingReadState (Option Bool) :=
    indexSomeBitsConfig (pref ++ [b]) witnessTail (next :: sourceTail)

  have h01 : preservingUnaryReadMachine.run 1 C0 = C1 := by
    dsimp [C0, C1, pref, m, witnessSuffix, src,
      indexSomeBitsConfig, indexSomeBitsTape]
    simp [preservingUnaryReadMachine, TM.run, TM.step,
      Tape.write, Tape.move, List.replicate_succ, List.append_assoc]

  have h12 : preservingUnaryReadMachine.run (m + 1) C1 = C2 := by
    dsimp [C1, C2]
    simpa using
      seekBlanks_over_blanks m first
        (prefTail.map some ++ (none :: some b :: witnessSuffix))
        (none :: src)

  have h23 : preservingUnaryReadMachine.run 1 C2 = C3 := by
    dsimp [C2, C3]
    simpa [TM.run] using
      seekBlanks_step_bit first b prefTail witnessSuffix
        (List.replicate (m + 1) none ++ (none :: src))

  have h34 : preservingUnaryReadMachine.run (m + 1) C3 = C4 := by
    dsimp [C3, C4, stream, pref, after, src, m]
    simpa [List.reverse_cons, List.map_append,
      List.replicate_succ, List.append_assoc] using
      seekBits_over_bits prefTail b witnessSuffix
        (some first ::
          (List.replicate (prefTail.length + 1) none ++
            (none :: (some next :: sourceTail.map some))))

  have h45 : preservingUnaryReadMachine.run 3 C4 = C5 := by
    dsimp [C4, C5, stream, returnedBits, pref]
    simpa [returnBitsTape, List.reverse_cons, List.map_append,
      List.append_assoc] using
      shift_carry_return_to_stream b witnessSuffix
        (pref.reverse.map some ++ (none :: after))

  have h56 : preservingUnaryReadMachine.run (m + 3) C5 = C6 := by
    dsimp [C5, C6, returnedBits, restoredLeft, pref, m]
    simpa [List.reverse_cons, List.map_append, List.append_assoc] using
      returnBits_over_bits (b :: pref.reverse)
        (none :: witnessSuffix) after

  have h6eq : C6 = C6e := by
    dsimp [C6, C6e, after]
    exact congrArg
      (fun t : Tape (Option Bool) =>
        ({ state := .returnBlanks, tape := t } :
          Configuration PreservingReadState (Option Bool)))
      (rightStreamTape_blank_block m restoredLeft src)

  have h67 : preservingUnaryReadMachine.run (m + 2) C6e = C7e := by
    dsimp [C6e, C7e, src]
    simpa using
      returnBlanks_over_blanks m next restoredLeft (sourceTail.map some)

  have hleft :
      List.replicate (m + 1) none ++ restoredLeft =
        List.replicate ((pref ++ [b]).length) none ++
          (pref ++ [b]).map some ++ (none :: witnessSuffix) := by
    have h :=
      replicate_none_extend m
        ((pref ++ [b]).map some ++ (none :: witnessSuffix))
    dsimp [restoredLeft, returnedBits, pref, m] at h ⊢
    simpa [List.reverse_cons, List.reverse_reverse,
      List.map_append, List.append_assoc] using h

  have h7eq : C7e = C7 := by
    dsimp [C7e, C7, indexSomeBitsConfig, indexSomeBitsTape, src]
    rw [hleft]

  have h56e : preservingUnaryReadMachine.run (m + 3) C5 = C6e := by
    rw [h56, h6eq]

  have h67t : preservingUnaryReadMachine.run (m + 2) C6e = C7 := by
    rw [h67, h7eq]

  have h02 :
      preservingUnaryReadMachine.run (1 + (m + 1)) C0 = C2 := by
    rw [run_add, h01, h12]
  have h03 :
      preservingUnaryReadMachine.run ((1 + (m + 1)) + 1) C0 = C3 := by
    rw [run_add, h02, h23]
  have h04 :
      preservingUnaryReadMachine.run (((1 + (m + 1)) + 1) + (m + 1)) C0 = C4 := by
    rw [run_add, h03, h34]
  have h05 :
      preservingUnaryReadMachine.run
        ((((1 + (m + 1)) + 1) + (m + 1)) + 3) C0 = C5 := by
    rw [run_add, h04, h45]
  have h06 :
      preservingUnaryReadMachine.run
        (((((1 + (m + 1)) + 1) + (m + 1)) + 3) + (m + 3)) C0 = C6e := by
    rw [run_add, h05, h56e]
  have h07 :
      preservingUnaryReadMachine.run
        ((((((1 + (m + 1)) + 1) + (m + 1)) + 3) + (m + 3)) + (m + 2)) C0 =
        C7 := by
    rw [run_add, h06, h67t]

  have hFuel :
      4 * (first :: prefTail).length + 8 =
        ((((((1 + (m + 1)) + 1) + (m + 1)) + 3) + (m + 3)) + (m + 2)) := by
    dsimp [m]
    omega
  rw [hFuel]
  simpa [C0, C7, pref] using h07

theorem indexSome_run_advance
    (pref : BitString) (b : Bool) (suffix : BitString) (n : Nat)
    (hpref : pref ≠ []) :
    preservingUnaryReadMachine.run (4 * pref.length + 8)
        (indexSomeConfig pref (b :: suffix) (n + 1)) =
      indexSomeConfig (pref ++ [b]) suffix n := by
  rcases pref with _ | ⟨first, prefTail⟩
  · contradiction
  cases n with
  | zero =>
      simpa [indexSomeConfig_eq_bits, encodeNat] using
        indexSome_cycle_bits first b false prefTail suffix []
  | succ n =>
      simpa [indexSomeConfig_eq_bits, encodeNat] using
        indexSome_cycle_bits first b true prefTail suffix (encodeNat n)

#print axioms MCore.Real.P01PreservingUnaryPhysicalRuns.indexSome_run_advance

end P01PreservingUnaryPhysicalRuns
end Real
end MCore
