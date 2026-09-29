import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01DeterministicNTMEmbedding

/-- Embed a deterministic TM into the repository's NTM model by giving every
non-halting configuration exactly one successor.  A halted TM state is split
into accepting/rejecting according to the supplied terminal classifier. -/
def tmAsNTM
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool) : NTM State Symbol where
  initial := M.initial
  blank := M.blank
  transition := fun q a =>
    if M.halting q then [] else [M.transition q a]
  accepting := fun q => M.halting q && accepting q
  rejecting := fun q => M.halting q && !accepting q

@[simp] theorem tmAsNTM_initial
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool) :
    (tmAsNTM M accepting).initial = M.initial := rfl

@[simp] theorem tmAsNTM_blank
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool) :
    (tmAsNTM M accepting).blank = M.blank := rfl

/-- On every non-halting state the embedded NTM has exactly the deterministic
TM step as its unique successor. -/
theorem tmAsNTM_successors_of_not_halted
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (c : Configuration State Symbol)
    (h : M.halting c.state = false) :
    (tmAsNTM M accepting).successors c = [M.step c] := by
  simp [tmAsNTM, NTM.successors, NTM.stepBranch, TM.step, h]

/-- A halted TM state is terminal in the embedded NTM. -/
theorem tmAsNTM_terminal_of_halted
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (q : State)
    (h : M.halting q = true) :
    (tmAsNTM M accepting).accepting q = true ∨
      (tmAsNTM M accepting).rejecting q = true := by
  cases ha : accepting q <;> simp [tmAsNTM, h, ha]

/-- Conversely, an NTM terminal state in the embedding is a halted TM state. -/
theorem tmAsNTM_terminal_implies_halted
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (q : State)
    (h :
      (tmAsNTM M accepting).accepting q = true ∨
      (tmAsNTM M accepting).rejecting q = true) :
    M.halting q = true := by
  cases hm : M.halting q with
  | false =>
      rcases h with h | h <;> simp [tmAsNTM, hm] at h
  | true =>
      rfl


/-- One deterministic run step is reproduced by the singleton-branch NTM. -/
theorem runBranches_singleton_of_not_halted
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (c : Configuration State Symbol)
    (h : M.halting c.state = false) :
    (tmAsNTM M accepting).runBranches 1 [c] = [M.step c] := by
  have ha : (tmAsNTM M accepting).accepting c.state = false := by
    simp [tmAsNTM, h]
  have hr : (tmAsNTM M accepting).rejecting c.state = false := by
    simp [tmAsNTM, h]
  have hs := tmAsNTM_successors_of_not_halted M accepting c h
  simp [NTM.runBranches, ha, hr, hs]

/-- A halted TM configuration is already terminal for the embedded NTM. -/
theorem runBranches_singleton_of_halted
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (c : Configuration State Symbol)
    (h : M.halting c.state = true) :
    (tmAsNTM M accepting).runBranches 1 [c] = [c] := by
  have ht := tmAsNTM_terminal_of_halted M accepting c.state h
  rcases ht with ha | hr
  · simp [NTM.runBranches, ha]
  · simp [NTM.runBranches, hr]

/-- The embedded NTM classifies exactly the halted TM states as terminal. -/
theorem tmAsNTM_terminal_iff_halted
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool)
    (q : State) :
    ((tmAsNTM M accepting).accepting q = true ∨
      (tmAsNTM M accepting).rejecting q = true) ↔
      M.halting q = true := by
  constructor
  · exact tmAsNTM_terminal_implies_halted M accepting q
  · exact tmAsNTM_terminal_of_halted M accepting q


/-- The deterministic embedding has exactly the same unique execution as the
underlying TM, at every fuel. -/
theorem runBranches_singleton_eq_run
    {State Symbol : Type}
    (M : TM State Symbol)
    (accepting : State → Bool) :
    ∀ (n : Nat) (c : Configuration State Symbol),
      (tmAsNTM M accepting).runBranches n [c] = [M.run n c] := by
  intro n
  induction n with
  | zero =>
      intro c
      rfl
  | succ n ih =>
      intro c
      cases hhalt : M.halting c.state with
      | true =>
          have hterm :
              P01NTMRunLaws.Halted (tmAsNTM M accepting) c := by
            rw [P01NTMRunLaws.Halted]
            exact (tmAsNTM_terminal_iff_halted M accepting c.state).2 hhalt
          simpa [TM.run, hhalt] using
            P01NTMRunLaws.runBranches_singleton_halted
              (tmAsNTM M accepting) (n + 1) c hterm
      | false =>
          have hacc : (tmAsNTM M accepting).accepting c.state = false := by
            simp [tmAsNTM, hhalt]
          have hrej : (tmAsNTM M accepting).rejecting c.state = false := by
            simp [tmAsNTM, hhalt]
          have hactive :
              ¬ P01NTMRunLaws.Halted (tmAsNTM M accepting) c := by
            simp [P01NTMRunLaws.Halted, hacc, hrej]
          rw [P01NTMRunLaws.runBranches_singleton_active
            (tmAsNTM M accepting) n c hactive]
          rw [tmAsNTM_successors_of_not_halted M accepting c hhalt]
          simpa [TM.run, hhalt] using ih (M.step c)

#print axioms MCore.Real.P01DeterministicNTMEmbedding.tmAsNTM_successors_of_not_halted
#print axioms MCore.Real.P01DeterministicNTMEmbedding.runBranches_singleton_eq_run
#print axioms MCore.Real.P01DeterministicNTMEmbedding.tmAsNTM_terminal_of_halted
#print axioms MCore.Real.P01DeterministicNTMEmbedding.tmAsNTM_terminal_implies_halted

end P01DeterministicNTMEmbedding
end Real
end MCore
