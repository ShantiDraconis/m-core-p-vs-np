import MCore.Real.P01FullVerifierPhysicalMoves
import MCore.Real.P01FullVerifierPhysical

namespace MCore
namespace Real
namespace P01FullVerifierPhysicalShuttles

open CanonicalFinalProof
open P01FullVerifierPhysicalMoves

/-- Source-end layout reached by the certified physical scanner.  The left
list is nearest-head first: reversed source, separator, then witness bits. -/
def sourceEndTape (witness source : BitString) : Tape (Option Bool) :=
  { left := source.reverse.map some ++ none :: witness.map some
    head := none
    right := [] }

/-- Exact number of primitive left moves from the source-end blank to
witness[i]. -/
def witnessOffset (source : BitString) (i : Nat) : Nat :=
  source.length + 2 + i

def moveToWitnessSeq (source : BitString) (i : Nat) : List Direction :=
  moveLeftSeq (witnessOffset source i)

/-- Returning from witness[i] to the source-end stack position uses the same
number of primitive right moves. -/
def moveToStackSeq (source : BitString) (i : Nat) : List Direction :=
  moveRightSeq (witnessOffset source i)

theorem moveToWitnessSeq_length (source : BitString) (i : Nat) :
    (moveToWitnessSeq source i).length = witnessOffset source i := by
  simp [moveToWitnessSeq, witnessOffset, moveLeftSeq_length]

theorem moveToStackSeq_length (source : BitString) (i : Nat) :
    (moveToStackSeq source i).length = witnessOffset source i := by
  simp [moveToStackSeq, witnessOffset, moveRightSeq_length]

theorem moveToWitnessSeq_legal (source : BitString) (i : Nat) :
    LegalMoveSeq (moveToWitnessSeq source i) := by
  exact moveLeftSeq_legal _

theorem moveToStackSeq_legal (source : BitString) (i : Nat) :
    LegalMoveSeq (moveToStackSeq source i) := by
  exact moveRightSeq_legal _

theorem sourceEndTape_left_length (witness source : BitString) :
    (sourceEndTape witness source).left.length =
      source.length + 1 + witness.length := by
  simp [sourceEndTape]
  omega

theorem witness_map_getD
    (witness : BitString) (i : Nat) (hi : i < witness.length) :
    (witness.map some).getD i none = some witness[i] := by
  induction witness generalizing i with
  | nil =>
      simp at hi
  | cons b bs ih =>
      cases i with
      | zero =>
          simp
      | succ i =>
          have hi' : i < bs.length := by
            simpa using hi
          simpa using ih i hi'

theorem getD_prefix_separator_witness
    (base : List (Option Bool)) (witness : BitString)
    (i : Nat) (hi : i < witness.length) :
    (base ++ none :: witness.map some).getD (base.length + 1 + i) none =
      some witness[i] := by
  induction base with
  | nil =>
      simp only [List.nil_append, List.length_nil, Nat.zero_add]
      change (none :: witness.map some).getD (1 + i) none = some witness[i]
      simpa [Nat.add_comm, List.getD_cons_succ] using
        witness_map_getD witness i hi
  | cons x xs ih =>
      simp only [List.cons_append, List.length_cons]
      change (x :: (xs ++ none :: witness.map some)).getD
        (Nat.succ xs.length + 1 + i) none = some witness[i]
      simpa [List.getD_cons_succ, Nat.succ_eq_add_one, Nat.add_assoc,
        Nat.add_left_comm, Nat.add_comm] using ih

/-- A valid witness index is physically present before the left shuttle can
run off the represented witness region. -/
theorem witnessOffset_le_left_length
    (witness source : BitString) (i : Nat) (hi : i < witness.length) :
    witnessOffset source i ≤ (sourceEndTape witness source).left.length := by
  rw [sourceEndTape_left_length]
  unfold witnessOffset
  omega


/-- Concrete witness targeting: after the exact left shuttle from source-end,
the head contains witness[i].  This replaces any abstract head-position axiom. -/
theorem moveToWitnessSeq_head_correct
    (witness source : BitString) (i : Nat) (hi : i < witness.length) :
    (execMoves none (moveToWitnessSeq source i)
      (sourceEndTape witness source)).head = some witness[i] := by
  unfold moveToWitnessSeq witnessOffset
  rw [show source.length + 2 + i = (source.length + 1 + i) + 1 by omega]
  rw [execMoves_moveLeftSeq_head_getD]
  unfold sourceEndTape
  simpa using
    getD_prefix_separator_witness (source.reverse.map some) witness i hi

/-- The complete witness round-trip has linear shuttle cost in source length
plus the selected witness index. -/
theorem witness_roundTrip_length
    (source : BitString) (i : Nat) :
    (moveToWitnessSeq source i ++ moveToStackSeq source i).length =
      2 * witnessOffset source i := by
  rw [List.length_append, moveToWitnessSeq_length, moveToStackSeq_length]
  omega


/-- Execution distributes over concatenation of primitive move sequences. -/
theorem execMoves_append
    {Symbol : Type}
    (blank : Symbol)
    (xs ys : List Direction)
    (t : Tape Symbol) :
    execMoves blank (xs ++ ys) t =
      execMoves blank ys (execMoves blank xs t) := by
  induction xs generalizing t with
  | nil => rfl
  | cons d ds ih =>
      simp [execMoves, ih]

/-- Pure left/right shuttling is nondestructive. Starting from a tape with at
least n cells on the left, moving left n times and then right n times restores
the exact original tape. -/
theorem moveLeftRight_roundTrip
    (t : Tape (Option Bool)) (n : Nat)
    (h : n ≤ t.left.length) :
    execMoves none (moveRightSeq n)
      (execMoves none (moveLeftSeq n) t) = t := by
  induction n generalizing t with
  | zero =>
      rfl
  | succ n ih =>
      cases t with
      | mk left head right =>
        cases left with
        | nil =>
            simp at h
        | cons x xs =>
            have hn : n ≤ xs.length := by
              simpa using Nat.succ_le_succ_iff.mp h
            let t' : Tape (Option Bool) :=
              { left := xs, head := x, right := head :: right }
            have hleft :
                execMoves none (moveLeftSeq (n + 1))
                  { left := x :: xs, head := head, right := right } =
                execMoves none (moveLeftSeq n) t' := by
              simp [moveLeftSeq, t', execMoves, Tape.move]
            have hright :
                moveRightSeq (n + 1) =
                  moveRightSeq n ++ [Direction.right] := by
              simp [moveRightSeq, List.replicate_succ_eq_append]
            rw [hleft, hright, execMoves_append]
            rw [ih t' hn]
            simp [t', execMoves, Tape.move]

/-- The existing source-end witness shuttle is therefore preserving: it reads
witness[i] and returns to the exact source-end tape without changing witness or
source. -/
theorem witness_roundTrip_tape_exact
    (witness source : BitString) (i : Nat)
    (hi : i < witness.length) :
    execMoves none (moveToStackSeq source i)
      (execMoves none (moveToWitnessSeq source i)
        (sourceEndTape witness source)) =
      sourceEndTape witness source := by
  exact moveLeftRight_roundTrip
    (sourceEndTape witness source)
    (witnessOffset source i)
    (witnessOffset_le_left_length witness source i hi)

#print axioms MCore.Real.P01FullVerifierPhysicalShuttles.moveLeftRight_roundTrip
#print axioms MCore.Real.P01FullVerifierPhysicalShuttles.witness_roundTrip_tape_exact

#print axioms MCore.Real.P01FullVerifierPhysicalShuttles.witnessOffset_le_left_length
#print axioms MCore.Real.P01FullVerifierPhysicalShuttles.moveToWitnessSeq_head_correct
#print axioms MCore.Real.P01FullVerifierPhysicalShuttles.witness_roundTrip_length

end P01FullVerifierPhysicalShuttles
end Real
end MCore
