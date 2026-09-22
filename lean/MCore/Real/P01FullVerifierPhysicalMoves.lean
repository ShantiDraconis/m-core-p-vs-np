import MCore.Real.P01FullVerifierPhysicalControl

namespace MCore
namespace Real
namespace P01FullVerifierPhysicalMoves

open CanonicalFinalProof

/-- Execute a finite sequence of legal single-cell head moves without writing.
This is the concrete replacement for pseudo-operations such as moveToWitness
and moveToStack. -/
def execMoves {Symbol : Type}
    (blank : Symbol) : List Direction → Tape Symbol → Tape Symbol
  | [], tape => tape
  | d :: ds, tape => execMoves blank ds (Tape.move blank d tape)

def moveLeftSeq (n : Nat) : List Direction :=
  List.replicate n .left

def moveRightSeq (n : Nat) : List Direction :=
  List.replicate n .right

@[simp] theorem execMoves_nil {Symbol : Type}
    (blank : Symbol) (t : Tape Symbol) :
    execMoves blank [] t = t := rfl

@[simp] theorem execMoves_cons {Symbol : Type}
    (blank : Symbol) (d : Direction) (ds : List Direction) (t : Tape Symbol) :
    execMoves blank (d :: ds) t =
      execMoves blank ds (Tape.move blank d t) := rfl

theorem moveLeftSeq_length (n : Nat) :
    (moveLeftSeq n).length = n := by
  simp [moveLeftSeq]

theorem moveRightSeq_length (n : Nat) :
    (moveRightSeq n).length = n := by
  simp [moveRightSeq]

theorem moveLeftSeq_all_legal (n : Nat) :
    ∀ d ∈ moveLeftSeq n, d = .left := by
  induction n with
  | zero =>
      simp [moveLeftSeq]
  | succ n ih =>
      intro d hd
      simp only [moveLeftSeq, List.replicate_succ, List.mem_cons] at hd
      rcases hd with h | h
      · exact h
      · exact ih d h

theorem moveRightSeq_all_legal (n : Nat) :
    ∀ d ∈ moveRightSeq n, d = .right := by
  induction n with
  | zero =>
      simp [moveRightSeq]
  | succ n ih =>
      intro d hd
      simp only [moveRightSeq, List.replicate_succ, List.mem_cons] at hd
      rcases hd with h | h
      · exact h
      · exact ih d h

/-- Structural iteration of one primitive tape move. -/
def repeatMove {Symbol : Type}
    (blank : Symbol) (d : Direction) : Nat → Tape Symbol → Tape Symbol
  | 0, tape => tape
  | n + 1, tape => repeatMove blank d n (Tape.move blank d tape)

/-- Repeated left motion is exactly structural iteration of the primitive move. -/
theorem execMoves_moveLeftSeq {Symbol : Type}
    (blank : Symbol) (n : Nat) (t : Tape Symbol) :
    execMoves blank (moveLeftSeq n) t =
      repeatMove blank .left n t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      simpa [moveLeftSeq, List.replicate_succ, execMoves, repeatMove] using
        ih (Tape.move blank .left t)

/-- Repeated right motion is exactly structural iteration of the primitive move. -/
theorem execMoves_moveRightSeq {Symbol : Type}
    (blank : Symbol) (n : Nat) (t : Tape Symbol) :
    execMoves blank (moveRightSeq n) t =
      repeatMove blank .right n t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
      simpa [moveRightSeq, List.replicate_succ, execMoves, repeatMove] using
        ih (Tape.move blank .right t)


/-- After n+1 left moves, the head contains the n-th cell of the original
left list, defaulting to blank beyond its end. -/
theorem execMoves_moveLeftSeq_head_getD {Symbol : Type}
    (blank : Symbol) (n : Nat) (t : Tape Symbol) :
    (execMoves blank (moveLeftSeq (n + 1)) t).head =
      t.left.getD n blank := by
  induction n generalizing t with
  | zero =>
      cases t with
      | mk left head right =>
          cases left <;>
            simp [moveLeftSeq, execMoves, Tape.move, List.getD_cons_zero]
  | succ n ih =>
      rw [show Nat.succ n + 1 = (n + 1) + 1 by omega]
      simp only [moveLeftSeq, List.replicate_succ, execMoves]
      rw [ih]
      cases t with
      | mk left head right =>
          cases left <;>
            simp [Tape.move, List.getD_cons_succ]

/-- Every shuttle used by the verifier is built solely from legal TM moves. -/
def LegalMoveSeq (ds : List Direction) : Prop :=
  ∀ d ∈ ds, d = .left ∨ d = .right ∨ d = .stay

theorem moveLeftSeq_legal (n : Nat) : LegalMoveSeq (moveLeftSeq n) := by
  intro d hd
  exact Or.inl (moveLeftSeq_all_legal n d hd)

theorem moveRightSeq_legal (n : Nat) : LegalMoveSeq (moveRightSeq n) := by
  intro d hd
  exact Or.inr (Or.inl (moveRightSeq_all_legal n d hd))

/-- Abstract physical shuttle certificate.  Target location is a predicate on
the resulting tape, keeping positional arithmetic on tape rather than finite
control. -/
structure ShuttleCertificate
    (start : Tape (Option Bool))
    (target : Tape (Option Bool) → Prop) where
  moves : List Direction
  legal : LegalMoveSeq moves
  reaches : target (execMoves none moves start)

#print axioms MCore.Real.P01FullVerifierPhysicalMoves.execMoves_moveLeftSeq
#print axioms MCore.Real.P01FullVerifierPhysicalMoves.execMoves_moveRightSeq
#print axioms MCore.Real.P01FullVerifierPhysicalMoves.execMoves_moveLeftSeq_head_getD
#print axioms MCore.Real.P01FullVerifierPhysicalMoves.moveLeftSeq_legal
#print axioms MCore.Real.P01FullVerifierPhysicalMoves.moveRightSeq_legal

end P01FullVerifierPhysicalMoves
end Real
end MCore
