import MCore.Real.CanonicalSATParserBinaryHeadProof
import MCore.Real.CanonicalSATRecursiveParserSimulation

namespace MCore
namespace Real
namespace P01GlobalParserSimulation

open CanonicalFinalProof
open CanonicalSATParserMachine
open CanonicalSATParserHeadProof
open CanonicalSATSlotParserSpec
open CanonicalSATSlotLog
open MachineRunLemmas

/-- Equality of finite right-tape representations modulo finitely many
explicit trailing blank cells. Internal blanks are preserved. -/
def RightBlankEq
    (a b : List (Option Bool)) : Prop :=
  ∃ (core : List (Option Bool)) (ka kb : Nat),
    a = core ++ List.replicate ka none ∧
    b = core ++ List.replicate kb none

theorem rightBlankEq_refl
    (a : List (Option Bool)) :
    RightBlankEq a a := by
  exact ⟨a, 0, 0, by simp, by simp⟩

theorem rightBlankEq_symm
    {a b : List (Option Bool)}
    (h : RightBlankEq a b) :
    RightBlankEq b a := by
  rcases h with ⟨core, ka, kb, ha, hb⟩
  exact ⟨core, kb, ka, hb, ha⟩

theorem rightBlankEq_cons
    (x : Option Bool)
    {a b : List (Option Bool)}
    (h : RightBlankEq a b) :
    RightBlankEq (x :: a) (x :: b) := by
  rcases h with ⟨core, ka, kb, ha, hb⟩
  refine ⟨x :: core, ka, kb, ?_, ?_⟩
  · simp [ha]
  · simp [hb]

theorem rightBlankEq_replicate
    (ka kb : Nat) :
    RightBlankEq
      (List.replicate ka (none : Option Bool))
      (List.replicate kb (none : Option Bool)) := by
  exact ⟨[], ka, kb, by simp, by simp⟩

/-- Configurations represent the same parser tape modulo explicit blank
padding at the far right. -/
def ConfigRightBlankEq
    (c d : Configuration (Fin 25) (Option Bool)) : Prop :=
  c.state = d.state ∧
  c.tape.left = d.tape.left ∧
  c.tape.head = d.tape.head ∧
  RightBlankEq c.tape.right d.tape.right

theorem configRightBlankEq_refl
    (c : Configuration (Fin 25) (Option Bool)) :
    ConfigRightBlankEq c c := by
  exact ⟨rfl, rfl, rfl, rightBlankEq_refl _⟩

theorem configRightBlankEq_symm
    {c d : Configuration (Fin 25) (Option Bool)}
    (h : ConfigRightBlankEq c d) :
    ConfigRightBlankEq d c := by
  rcases h with ⟨hs, hl, hh, hr⟩
  exact ⟨hs.symm, hl.symm, hh.symm, rightBlankEq_symm hr⟩

private theorem move_stay_preserves
    (q : Fin 25)
    {left : List (Option Bool)}
    {head : Option Bool}
    {ra rb : List (Option Bool)}
    (h : RightBlankEq ra rb) :
    ConfigRightBlankEq
      { state := q
        tape := Tape.move none .stay
          { left := left, head := head, right := ra } }
      { state := q
        tape := Tape.move none .stay
          { left := left, head := head, right := rb } } := by
  exact ⟨rfl, rfl, rfl, h⟩

private theorem move_left_preserves
    (q : Fin 25)
    {left : List (Option Bool)}
    {head : Option Bool}
    {ra rb : List (Option Bool)}
    (h : RightBlankEq ra rb) :
    ConfigRightBlankEq
      { state := q
        tape := Tape.move none .left
          { left := left, head := head, right := ra } }
      { state := q
        tape := Tape.move none .left
          { left := left, head := head, right := rb } } := by
  cases left with
  | nil =>
      exact ⟨rfl, rfl, rfl, rightBlankEq_cons head h⟩
  | cons x xs =>
      exact ⟨rfl, rfl, rfl, rightBlankEq_cons head h⟩

private theorem move_right_preserves
    (q : Fin 25)
    {left : List (Option Bool)}
    {head : Option Bool}
    {ra rb : List (Option Bool)}
    (h : RightBlankEq ra rb) :
    ConfigRightBlankEq
      { state := q
        tape := Tape.move none .right
          { left := left, head := head, right := ra } }
      { state := q
        tape := Tape.move none .right
          { left := left, head := head, right := rb } } := by
  rcases h with ⟨core, ka, kb, ha, hb⟩
  rw [ha, hb]
  cases core with
  | nil =>
      simp only [List.nil_append]
      cases ka with
      | zero =>
          cases kb with
          | zero =>
              exact ⟨rfl, rfl, rfl, rightBlankEq_refl []⟩
          | succ kb =>
              simp only [List.replicate_zero, List.replicate_succ, Tape.move]
              exact ⟨rfl, rfl, rfl, rightBlankEq_replicate 0 kb⟩
      | succ ka =>
          cases kb with
          | zero =>
              simp only [List.replicate_zero, List.replicate_succ, Tape.move]
              exact ⟨rfl, rfl, rfl, rightBlankEq_replicate ka 0⟩
          | succ kb =>
              simp only [List.replicate_succ, Tape.move]
              exact ⟨rfl, rfl, rfl, rightBlankEq_replicate ka kb⟩
  | cons x xs =>
      simp only [List.cons_append, Tape.move]
      refine ⟨rfl, rfl, rfl, ?_⟩
      exact ⟨xs, ka, kb, rfl, rfl⟩

private theorem move_preserves
    (q : Fin 25)
    (dir : Direction)
    {left : List (Option Bool)}
    {head : Option Bool}
    {ra rb : List (Option Bool)}
    (h : RightBlankEq ra rb) :
    ConfigRightBlankEq
      { state := q
        tape := Tape.move none dir
          { left := left, head := head, right := ra } }
      { state := q
        tape := Tape.move none dir
          { left := left, head := head, right := rb } } := by
  cases dir with
  | left => exact move_left_preserves q h
  | stay => exact move_stay_preserves q h
  | right => exact move_right_preserves q h

/-- The concrete parser transition is insensitive to explicit blank padding
beyond the represented right-hand tape contents. -/
theorem parser_step_respects_right_blank
    {c d : Configuration (Fin 25) (Option Bool)}
    (h : ConfigRightBlankEq c d) :
    ConfigRightBlankEq
      (parserMachine.step c)
      (parserMachine.step d) := by
  rcases c with ⟨cs, ct⟩
  rcases ct with ⟨cl, ch, cr⟩
  rcases d with ⟨ds, dt⟩
  rcases dt with ⟨dl, dh, dr⟩
  rcases h with ⟨hs, hl, hh, hr⟩
  change cs = ds at hs
  change cl = dl at hl
  change ch = dh at hh
  change RightBlankEq cr dr at hr
  subst ds
  subst dl
  subst dh
  rcases htrans :
      parserMachine.transition cs ch with
      ⟨nextState, nextSymbol, dir⟩
  unfold TM.step
  rw [htrans]
  simp only [Tape.write, parserMachine_blank_none]
  exact move_preserves nextState dir hr

/-- Right-blank equivalence is a bisimulation for every bounded parser run. -/
theorem parser_run_respects_right_blank
    (fuel : Nat)
    {c d : Configuration (Fin 25) (Option Bool)}
    (h : ConfigRightBlankEq c d) :
    ConfigRightBlankEq
      (parserMachine.run fuel c)
      (parserMachine.run fuel d) := by
  induction fuel generalizing c d with
  | zero =>
      exact h
  | succ fuel ih =>
      have hs := h.1
      have hhalt :
          parserMachine.halting c.state =
            parserMachine.halting d.state := by
        rw [hs]
      by_cases hc : parserMachine.halting c.state = true
      · have hd : parserMachine.halting d.state = true := by
          rw [← hhalt]
          exact hc
        simp only [TM.run, hc, hd, if_true]
        exact h
      · have hcf : parserMachine.halting c.state = false := by
          cases hq : parserMachine.halting c.state <;> simp_all
        have hdf : parserMachine.halting d.state = false := by
          rw [← hhalt]
          exact hcf
        simp only [TM.run, hcf, hdf, Bool.false_eq_true, if_false]
        exact ih (parser_step_respects_right_blank h)

theorem parser_run_state_eq_of_right_blank
    (fuel : Nat)
    {c d : Configuration (Fin 25) (Option Bool)}
    (h : ConfigRightBlankEq c d) :
    (parserMachine.run fuel c).state =
      (parserMachine.run fuel d).state :=
  (parser_run_respects_right_blank fuel h).1

/-- Successful head parsing strictly shortens the unread source. -/
theorem parseHead_rest_length_lt
    {bits : BitString}
    {head : Head}
    {rest : BitString}
    (hparse : parseHead bits = some (head, rest)) :
    rest.length < bits.length := by
  have hshape := parseHead_inverse bits head rest hparse
  cases head with
  | input i =>
      rw [hshape]
      simp [Head.encode]
      omega
  | const b =>
      rw [hshape]
      cases b <;> simp [Head.encode] <;> omega
  | not =>
      rw [hshape]
      simp [Head.encode]
      omega
  | and =>
      rw [hshape]
      simp [Head.encode]
      omega
  | or =>
      rw [hshape]
      simp [Head.encode]
      omega

/-- A physical rightmost-slot pop changes only a bit, never the work-log
length. -/
theorem popSlot_length
    {log log' : SlotLog}
    (hpop : popSlot log = some log') :
    log'.length = log.length := by
  induction log generalizing log' with
  | nil =>
      simp [popSlot] at hpop
  | cons b bs ih =>
      cases hbs : popSlot bs with
      | some bs' =>
          simp [popSlot, hbs] at hpop
          subst log'
          simp [ih hbs]
      | none =>
          cases b with
          | false =>
              simp [popSlot, hbs] at hpop
          | true =>
              simp [popSlot, hbs] at hpop
              subst log'
              rfl

/-- Positive abstract slot count guarantees a physical pop witness. -/
theorem popSlot_exists_of_active
    (log : SlotLog)
    (hactive : activeSlots log ≠ 0) :
    ∃ log', popSlot log = some log' := by
  cases h : popSlot log with
  | none =>
      exact False.elim (hactive ((popSlot_none_iff log).mp h))
  | some log' =>
      refine ⟨log', ?_⟩
      simpa using h

#print axioms MCore.Real.P01GlobalParserSimulation.parser_step_respects_right_blank
#print axioms MCore.Real.P01GlobalParserSimulation.parser_run_respects_right_blank
#print axioms MCore.Real.P01GlobalParserSimulation.parseHead_rest_length_lt
#print axioms MCore.Real.P01GlobalParserSimulation.popSlot_length
#print axioms MCore.Real.P01GlobalParserSimulation.popSlot_exists_of_active

end P01GlobalParserSimulation
end Real
end MCore
