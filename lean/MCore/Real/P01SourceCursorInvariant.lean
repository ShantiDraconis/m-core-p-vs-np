import MCore.Real.P01FullVerifierPhysicalStackV2
import MCore.Real.P01FullVerifierPhysicalMoves

namespace MCore
namespace Real
namespace P01SourceCursorInvariant

open CanonicalFinalProof
open P01FullVerifierPhysicalStackV2
open P01FullVerifierPhysicalMoves

/-- Number of left moves from the canonical V2 stack-end blank to the first
source bit.  The stack is nearest the head, followed by one stack/source blank,
then the reversed source. -/
def sourceStartOffset (stack : List Bool) (source : BitString) : Nat :=
  stack.length + source.length + 1

def moveToSourceStartSeq (stack : List Bool) (source : BitString) :
    List Direction :=
  moveLeftSeq (sourceStartOffset stack source)

def moveBackToStackEndSeq (stack : List Bool) (source : BitString) :
    List Direction :=
  moveRightSeq (sourceStartOffset stack source)

theorem moveToSourceStartSeq_length
    (stack : List Bool) (source : BitString) :
    (moveToSourceStartSeq stack source).length =
      sourceStartOffset stack source := by
  simp [moveToSourceStartSeq, sourceStartOffset, moveLeftSeq_length]

theorem moveBackToStackEndSeq_length
    (stack : List Bool) (source : BitString) :
    (moveBackToStackEndSeq stack source).length =
      sourceStartOffset stack source := by
  simp [moveBackToStackEndSeq, sourceStartOffset, moveRightSeq_length]

/-- On every nonempty canonical source, the exact left shuttle lands on the
first source bit while preserving the represented tape contents. -/
theorem moveToSourceStart_head_correct
    (witness : BitString)
    (b : Bool) (bs : BitString)
    (stack : List Bool) (padding : Nat) :
    (execMoves none (moveToSourceStartSeq stack (b :: bs))
      (physicalStackV2Tape witness (b :: bs) stack padding)).head =
      some b := by
  unfold moveToSourceStartSeq sourceStartOffset
  rw [show stack.length + (b :: bs).length + 1 =
      (stack.length + bs.length + 1) + 1 by simp; omega]
  rw [execMoves_moveLeftSeq_head_getD]
  simp only [physicalStackV2Tape]
  have hstack :
      (stack.map some).length ≤
        stack.length + bs.length + 1 := by
    simp
    omega
  rw [List.getElem?_append_right]
  · have hsub :
        stack.length + bs.length + 1 - (stack.map some).length =
          bs.length + 1 := by
      simp
    rw [hsub]
    rw [List.getElem?_cons_succ]
    have hrev :
        ((bs.map some).reverse).length ≤ bs.length := by
      simp
    rw [List.getElem?_append_right]
    · simp
    · simpa using hrev
  · simpa using hstack

/-- The source cursor motion is legal in the same primitive-move sense used by
all prior certified P01 shuttles. -/
theorem moveToSourceStartSeq_legal
    (stack : List Bool) (source : BitString) :
    LegalMoveSeq (moveToSourceStartSeq stack source) := by
  exact moveLeftSeq_legal _

/-- The return shuttle has exactly the same cost envelope. -/
theorem source_cursor_roundTrip_length
    (stack : List Bool) (source : BitString) :
    (moveToSourceStartSeq stack source ++
      moveBackToStackEndSeq stack source).length =
      2 * sourceStartOffset stack source := by
  rw [List.length_append, moveToSourceStartSeq_length,
    moveBackToStackEndSeq_length]
  omega

#print axioms MCore.Real.P01SourceCursorInvariant.moveToSourceStart_head_correct
#print axioms MCore.Real.P01SourceCursorInvariant.source_cursor_roundTrip_length

end P01SourceCursorInvariant
end Real
end MCore
