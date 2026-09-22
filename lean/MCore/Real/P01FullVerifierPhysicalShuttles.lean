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

theorem getD_append_right {α : Type}
    (xs ys : List α) (i : Nat) (d : α) (h : xs.length ≤ i) :
    (xs ++ ys).getD i d = ys.getD (i - xs.length) d := by
  induction xs generalizing i with
  | nil =>
      simp
  | cons x xs ih =>
      cases i with
      | zero =>
          simp at h
      | succ i =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at h
          simp [ih _ h]

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
  rw [getD_append_right]
  · simp [hi]
  · simp

/-- The complete witness round-trip has linear shuttle cost in source length
plus the selected witness index. -/
theorem witness_roundTrip_length
    (source : BitString) (i : Nat) :
    (moveToWitnessSeq source i ++ moveToStackSeq source i).length =
      2 * witnessOffset source i := by
  rw [List.length_append, moveToWitnessSeq_length, moveToStackSeq_length]
  omega

#print axioms MCore.Real.P01FullVerifierPhysicalShuttles.witnessOffset_le_left_length
#print axioms MCore.Real.P01FullVerifierPhysicalShuttles.moveToWitnessSeq_head_correct
#print axioms MCore.Real.P01FullVerifierPhysicalShuttles.witness_roundTrip_length

end P01FullVerifierPhysicalShuttles
end Real
end MCore
