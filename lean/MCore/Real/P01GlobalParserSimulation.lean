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
  ∃ core ka kb : Nat,
    a = core ++ List.replicate ka none ∧
    b = core ++ List.replicate kb none

theorem rightBlankEq_refl
    (a : List (Option Bool)) :
    RightBlankEq a a := by
  refine ⟨a, 0, 0, ?_, ?_⟩ <;> simp

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
    {left : List (Option Bool)}
    {head : Option Bool}
    {ra rb : List (Option Bool)}
    (h : RightBlankEq ra rb) :
    ConfigRightBlankEq
      { state := (0 : Fin 25)
        tape := Tape.move none .stay
          { left := left, head := head, right := ra } }
      { state := (0 : Fin 25)
        tape := Tape.move none .stay
          { left := left, head := head, right := rb } } := by
  simp [ConfigRightBlankEq, Tape.move, h, rightBlankEq_refl]

private theorem move_left_preserves
    {left : List (Option Bool)}
    {head : Option Bool}
    {ra rb : List (Option Bool)}
    (h : RightBlankEq ra rb) :
    ConfigRightBlankEq
      { state := (0 : Fin 25)
        tape := Tape.move none .left
          { left := left, head := head, right := ra } }
      { state := (0 : Fin 25)
        tape := Tape.move none .left
          { left := left, head := head, right := rb } } := by
  cases left with
  | nil =>
      simp [ConfigRightBlankEq, Tape.move, rightBlankEq_cons head h]
  | cons x xs =>
      simp [ConfigRightBlankEq, Tape.move, rightBlankEq_cons head h]

private theorem move_right_preserves
    {left : List (Option Bool)}
    {head : Option Bool}
    {ra rb : List (Option Bool)}
    (h : RightBlankEq ra rb) :
    ConfigRightBlankEq
      { state := (0 : Fin 25)
        tape := Tape.move none .right
          { left := left, head := head, right := ra } }
      { state := (0 : Fin 25)
        tape := Tape.move none .right
          { left := left, head := head, right := rb } } := by
  rcases h with ⟨core, ka, kb, ha, hb⟩
  subst ra
  subst rb
  cases core with
  | nil =>
      cases ka <;> cases kb <;>
        simp [ConfigRightBlankEq, Tape.move, RightBlankEq]
  | cons x xs =>
      simp [ConfigRightBlankEq, Tape.move, RightBlankEq]
      exact ⟨xs, ka, kb, rfl, rfl⟩

private theorem move_preserves
    (dir : Direction)
    {left : List (Option Bool)}
    {head : Option Bool}
    {ra rb : List (Option Bool)}
    (h : RightBlankEq ra rb) :
    ConfigRightBlankEq
      { state := (0 : Fin 25)
        tape := Tape.move none dir
          { left := left, head := head, right := ra } }
      { state := (0 : Fin 25)
        tape := Tape.move none dir
          { left := left, head := head, right := rb } } := by
  cases dir with
  | left => exact move_left_preserves h
  | stay => exact move_stay_preserves h
  | right => exact move_right_preserves h

/-- The concrete parser transition is insensitive to explicit blank padding
beyond the represented right-hand tape contents. -/
theorem parser_step_respects_right_blank
    {c d : Configuration (Fin 25) (Option Bool)}
    (h : ConfigRightBlankEq c d) :
    ConfigRightBlankEq
      (parserMachine.step c)
      (parserMachine.step d) := by
  rcases h with ⟨hs, hl, hh, hr⟩
  have ht :
      parserMachine.transition c.state c.tape.head =
        parserMachine.transition d.state d.tape.head := by
    simpa [hs, hh]
  rcases htrans :
      parserMachine.transition c.state c.tape.head with
      ⟨nextState, nextSymbol, dir⟩
  have htrans' :
      parserMachine.transition d.state d.tape.head =
        (nextState, nextSymbol, dir) := by
    rw [← ht]
    exact htrans
  unfold TM.step
  rw [htrans, htrans']
  have hm := move_preserves (dir := dir) (left := c.tape.left)
    (head := nextSymbol) hr
  rcases hm with ⟨_, hleft, hhead, hright⟩
  refine ⟨rfl, ?_, hhead, hright⟩
  simpa [hl] using hleft

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
      simpa [TM.run] using h
  | succ fuel ih =>
      rcases h with ⟨hs, hl, hh, hr⟩
      have hhalt :
          parserMachine.halting c.state =
            parserMachine.halting d.state := by
        simp [hs]
      by_cases hc : parserMachine.halting c.state = true
      · have hd : parserMachine.halting d.state = true := by
          simpa [hhalt] using hc
        simp [TM.run, hc, hd, ConfigRightBlankEq, hs, hl, hh, hr]
      · have hcf : parserMachine.halting c.state = false := by
          cases hq : parserMachine.halting c.state <;> simp_all
        have hdf : parserMachine.halting d.state = false := by
          rw [← hhalt]
          exact hcf
        simp only [TM.run, hcf, hdf, Bool.false_eq_true, if_false]
        exact ih (parser_step_respects_right_blank ⟨hs, hl, hh, hr⟩)

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
      simp [Head.encode, encodeNat_length]
  | const b =>
      rw [hshape]
      cases b <;> simp [Head.encode]
  | not =>
      rw [hshape]
      simp [Head.encode]
  | and =>
      rw [hshape]
      simp [Head.encode]
  | or =>
      rw [hshape]
      simp [Head.encode]

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
      exact ⟨log', h⟩

#print axioms MCore.Real.P01GlobalParserSimulation.parser_step_respects_right_blank
#print axioms MCore.Real.P01GlobalParserSimulation.parser_run_respects_right_blank
#print axioms MCore.Real.P01GlobalParserSimulation.parseHead_rest_length_lt
#print axioms MCore.Real.P01GlobalParserSimulation.popSlot_length
#print axioms MCore.Real.P01GlobalParserSimulation.popSlot_exists_of_active

end P01GlobalParserSimulation
end Real
end MCore
