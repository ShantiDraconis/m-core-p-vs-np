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

theorem activeSlots_reverse
    (log : SlotLog) :
    activeSlots log.reverse = activeSlots log := by
  induction log with
  | nil => rfl
  | cons b bs ih =>
      rw [List.reverse_cons, activeSlots_append, ih]
      cases b <;> simp [activeSlots, Nat.add_comm]

theorem rightBlankEq_append_none
    (right : List (Option Bool)) :
    RightBlankEq (right ++ [none]) right := by
  exact ⟨right, 1, 0, by simp, by simp⟩

/-- State-16/17 source checks differing only by one explicit far-right blank
represent the same infinite blank tape. -/
theorem leafSourceCheck_trailing_blank
    (q : Fin 25)
    (sourceLeft right : List (Option Bool)) :
    ConfigRightBlankEq
      (CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
        q sourceLeft (right ++ [none]))
      (CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
        q sourceLeft right) := by
  unfold CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
  cases sourceLeft with
  | nil =>
      exact ⟨rfl, rfl, rfl,
        rightBlankEq_cons none (rightBlankEq_append_none right)⟩
  | cons x xs =>
      exact ⟨rfl, rfl, rfl,
        rightBlankEq_cons none (rightBlankEq_append_none right)⟩

private theorem map_some_false_suffix
    (suffix : SlotLog)
    (hall : ∀ b ∈ suffix, b = false) :
    suffix.map some =
      List.replicate suffix.length (some false) := by
  have hs :=
    CanonicalSATParserLeafPopProof.all_false_eq_replicate suffix hall
  rw [hs]
  simp

/-- Complete the physical leaf pop and older-active-slot scan.  The exact
output differs from the canonical source-check configuration only by the
explicit far-right blank exposed by scanning to the end of the work region. -/
theorem leaf_afterEnd_active_to_source
    (sourceLeft : List (Option Bool))
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hactive : activeSlots log' ≠ 0) :
    ∃ k : Nat,
      parserMachine.run k
        (CanonicalSATParserWorkScanProof.afterEndMoveLeft
          13 (none :: sourceLeft) log none) =
        CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
          17 sourceLeft (log'.map some ++ [none]) := by
  rcases popSlot_decompose log log' hpop with
    ⟨pre, suffix, hlog, hlog', hsuffix⟩
  have hszero : activeSlots suffix = 0 :=
    (activeSlots_eq_zero_iff_all_false suffix).mpr hsuffix
  have hpre : activeSlots pre ≠ 0 := by
    intro hz
    apply hactive
    rw [hlog', activeSlots_append]
    simp [activeSlots, hz, hszero]
  have hpreRev : activeSlots pre.reverse ≠ 0 := by
    simpa [activeSlots_reverse] using hpre
  have hsmap := map_some_false_suffix suffix hsuffix
  have hright :
      pre.map some ++
          (some false ::
            (List.replicate suffix.length (some false) ++ [none])) =
        log'.map some ++ [none] := by
    rw [hlog']
    simp [List.map_append, hsmap, List.append_assoc]
  refine ⟨(suffix.length + 1) + (pre.length + 1), ?_⟩
  rw [MachineRunLemmas.run_add]
  rw [hlog]
  rw [CanonicalSATParserLeafPopProof.leaf_pop_decomposed
    pre suffix (none :: sourceLeft) hsuffix]
  rw [CanonicalSATParserLeafReturnProof.leafAfterPop_eq_check]
  have hscan :=
    CanonicalSATParserLeafReturnProof.leaf14_active_run
      pre.reverse sourceLeft
      (some false ::
        (List.replicate suffix.length (some false) ++ [none]))
      hpreRev
  calc
    parserMachine.run (pre.length + 1)
        (CanonicalSATParserLeafReturnProof.leafCheckConfig 14
          pre.reverse sourceLeft
          (some false ::
            (List.replicate suffix.length (some false) ++ [none]))) =
      CanonicalSATParserLeafReturnProof.leafSourceCheckConfig 17
        sourceLeft
        (pre.map some ++
          (some false ::
            (List.replicate suffix.length (some false) ++ [none]))) := by
      simpa using hscan
    _ =
      CanonicalSATParserLeafReturnProof.leafSourceCheckConfig 17
        sourceLeft (log'.map some ++ [none]) := by
      exact congrArg
        (CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
          (17 : Fin 25) sourceLeft)
        hright

/-- Same leaf pop path when no active slot remains. -/
theorem leaf_afterEnd_inactive_to_source
    (sourceLeft : List (Option Bool))
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hzero : activeSlots log' = 0) :
    ∃ k : Nat,
      parserMachine.run k
        (CanonicalSATParserWorkScanProof.afterEndMoveLeft
          13 (none :: sourceLeft) log none) =
        CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
          16 sourceLeft (log'.map some ++ [none]) := by
  rcases popSlot_decompose log log' hpop with
    ⟨pre, suffix, hlog, hlog', hsuffix⟩
  have hszero : activeSlots suffix = 0 :=
    (activeSlots_eq_zero_iff_all_false suffix).mpr hsuffix
  have hprezero : activeSlots pre = 0 := by
    rw [hlog', activeSlots_append] at hzero
    simpa [activeSlots, hszero] using hzero
  have hpreall : ∀ b ∈ pre, b = false :=
    (activeSlots_eq_zero_iff_all_false pre).mp hprezero
  have hpreRevAll : ∀ b ∈ pre.reverse, b = false := by
    intro b hb
    exact hpreall b (by simpa using hb)
  have hsmap := map_some_false_suffix suffix hsuffix
  have hright :
      pre.map some ++
          (some false ::
            (List.replicate suffix.length (some false) ++ [none])) =
        log'.map some ++ [none] := by
    rw [hlog']
    simp [List.map_append, hsmap, List.append_assoc]
  refine ⟨(suffix.length + 1) + (pre.length + 1), ?_⟩
  rw [MachineRunLemmas.run_add]
  rw [hlog]
  rw [CanonicalSATParserLeafPopProof.leaf_pop_decomposed
    pre suffix (none :: sourceLeft) hsuffix]
  rw [CanonicalSATParserLeafReturnProof.leafAfterPop_eq_check]
  have hscan :=
    CanonicalSATParserLeafReturnProof.leaf14_all_false_run
      pre.reverse sourceLeft
      (some false ::
        (List.replicate suffix.length (some false) ++ [none]))
      hpreRevAll
  calc
    parserMachine.run (pre.length + 1)
        (CanonicalSATParserLeafReturnProof.leafCheckConfig 14
          pre.reverse sourceLeft
          (some false ::
            (List.replicate suffix.length (some false) ++ [none]))) =
      CanonicalSATParserLeafReturnProof.leafSourceCheckConfig 16
        sourceLeft
        (pre.map some ++
          (some false ::
            (List.replicate suffix.length (some false) ++ [none]))) := by
      simpa using hscan
    _ =
      CanonicalSATParserLeafReturnProof.leafSourceCheckConfig 16
        sourceLeft (log'.map some ++ [none]) := by
      exact congrArg
        (CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
          (16 : Fin 25) sourceLeft)
        hright

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


/-- Complete an active leaf return through the certified source rewind.
The physical source-check carries one explicit far-right blank; the blank-tape
bisimulation transports it to the canonical source-check theorem. -/
theorem leaf_afterEnd_roundtrip_nonempty_active
    (pad : Nat)
    (hpad : 0 < pad)
    (last : Bool)
    (rest : BitString)
    (log log' : SlotLog)
    (hpop : popSlot log = some log')
    (hactive : activeSlots log' ≠ 0) :
    ∃ steps : Nat,
      ConfigRightBlankEq
        (parserMachine.run steps
          (CanonicalSATParserWorkScanProof.afterEndMoveLeft 13
            (none :: some last ::
              (rest.map some ++
                List.replicate pad (none : Option Bool)))
            log none))
        (phaseConfig 4 pad (rest.reverse ++ [last]) log') := by
  let sourceLeft : List (Option Bool) :=
    some last ::
      (rest.map some ++ List.replicate pad (none : Option Bool))
  rcases leaf_afterEnd_active_to_source sourceLeft log log' hpop hactive with
    ⟨k, hk⟩
  refine ⟨k + (rest.length + 2), ?_⟩
  rw [MachineRunLemmas.run_add, hk]
  have hcfg :=
    leafSourceCheck_trailing_blank
      (17 : Fin 25) sourceLeft (log'.map some)
  have hrun :=
    parser_run_respects_right_blank (rest.length + 2) hcfg
  have hcanon :=
    CanonicalSATParserLeafSourceProof.leaf17_roundtrip_to_phase
      pad hpad last rest log'
  have hcanon' :
      parserMachine.run (rest.length + 2)
        (CanonicalSATParserLeafReturnProof.leafSourceCheckConfig
          17 sourceLeft (log'.map some)) =
        phaseConfig 4 pad (rest.reverse ++ [last]) log' := by
    simpa [sourceLeft] using hcanon
  rw [hcanon'] at hrun
  exact hrun

#print axioms MCore.Real.P01GlobalParserSimulation.parser_step_respects_right_blank
#print axioms MCore.Real.P01GlobalParserSimulation.parser_run_respects_right_blank
#print axioms MCore.Real.P01GlobalParserSimulation.parseHead_rest_length_lt
#print axioms MCore.Real.P01GlobalParserSimulation.popSlot_length
#print axioms MCore.Real.P01GlobalParserSimulation.popSlot_exists_of_active

end P01GlobalParserSimulation
end Real
end MCore
