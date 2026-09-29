import MCore.Real.P01EvalRunCompositeNTM
import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01EvalRunLift

open P01NTMRunLaws
open P01EvalStepCompositeNTM
open P01EvalRunCompositeNTM

abbrev StepConfig :=
  Configuration EvalStepCompositeState (Option Bool)

abbrev RunConfig :=
  Configuration EvalRunCompositeState (Option Bool)

def liftRunConfig (c : StepConfig) : RunConfig :=
  { state := evalRunStateEmbed c.state,
    tape := c.tape }

/-- Any active evalStep state embeds as an actual running evalRun state. -/
theorem embed_active_state
    (q : EvalStepCompositeState)
    (tape : Tape (Option Bool))
    (h :
      ¬ Halted evalStepCompositeMachine
        ({ state := q, tape := tape } : StepConfig)) :
    evalRunStateEmbed q = .step q := by
  cases q <;>
    simp [Halted, evalStepCompositeMachine,
      evalRunStateEmbed] at h ⊢

/-- A one-step evalStep successor lifts to a one-step evalRun successor
whenever the source evalStep configuration is active. -/
theorem lift_successor
    (a b : StepConfig)
    (ha : ¬ Halted evalStepCompositeMachine a)
    (hab : b ∈ evalStepCompositeMachine.successors a) :
    liftRunConfig b ∈
      evalRunCompositeMachine.successors (liftRunConfig a) := by
  have hstate :
      evalRunStateEmbed a.state = .step a.state :=
    embed_active_state a.state a.tape ha
  change
    ({ state := evalRunStateEmbed b.state, tape := b.tape } : RunConfig) ∈
      evalRunCompositeMachine.successors
        ({ state := evalRunStateEmbed a.state, tape := a.tape } : RunConfig)
  rw [hstate]
  rw [step_successors a.state a.tape]
  exact List.mem_map.mpr ⟨b, hab, rfl⟩

/-- The lift of an active evalStep configuration is active in evalRun. -/
theorem lift_active
    (a : StepConfig)
    (ha : ¬ Halted evalStepCompositeMachine a) :
    ¬ Halted evalRunCompositeMachine (liftRunConfig a) := by
  have hstate :
      evalRunStateEmbed a.state = .step a.state :=
    embed_active_state a.state a.tape ha
  simp [liftRunConfig, hstate, Halted, evalRunCompositeMachine]

/-- Key restart lemma.

If an evalStep terminal is reachable within `n` branches from an active
evalStep start, then its evalRun restart image is reachable in some `m ≤ n`.
This deliberately weakens exact fuel: an evalStep terminal may have been
reached earlier and then persisted because it was halted, whereas its evalRun
image immediately becomes active again. -/
theorem terminal_reachable_lift :
    ∀ (n : Nat) (a b : StepConfig),
      ¬ Halted evalStepCompositeMachine a →
      Halted evalStepCompositeMachine b →
      b ∈ evalStepCompositeMachine.runBranches n [a] →
      ∃ m ≤ n,
        liftRunConfig b ∈
          evalRunCompositeMachine.runBranches m [liftRunConfig a] := by
  intro n
  induction n with
  | zero =>
      intro a b ha hb hreach
      simp [NTM.runBranches] at hreach
      subst b
      exact False.elim (ha hb)
  | succ n ih =>
      intro a b ha hb hreach
      have hreach' :
          b ∈ evalStepCompositeMachine.runBranches n
            (evalStepCompositeMachine.successors a) := by
        rw [show Nat.succ n = n + 1 by omega] at hreach
        rw [runBranches_singleton_active
          evalStepCompositeMachine n a ha] at hreach
        exact hreach
      rw [mem_runBranches_iff] at hreach'
      rcases hreach' with ⟨c, hca, hcb⟩

      have hstepSucc :
          liftRunConfig c ∈
            evalRunCompositeMachine.successors (liftRunConfig a) :=
        lift_successor a c ha hca
      have hstep :
          liftRunConfig c ∈
            evalRunCompositeMachine.runBranches 1 [liftRunConfig a] := by
        have :=
          mem_runBranches_succ_of_successor
            evalRunCompositeMachine 0 [liftRunConfig a]
            (liftRunConfig a) (liftRunConfig c)
            (by simp [NTM.runBranches])
            (lift_active a ha) hstepSucc
        simpa using this

      by_cases hc : Halted evalStepCompositeMachine c
      · have hcb' :
            b = c := by
          rw [runBranches_singleton_halted
            evalStepCompositeMachine n c hc] at hcb
          simpa using hcb
        subst b
        exact ⟨1, by omega, hstep⟩
      · obtain ⟨m, hm, htail⟩ :=
          ih c b hc hb hcb
        have htrans :=
          mem_runBranches_trans evalRunCompositeMachine
            1 m [liftRunConfig a]
            (liftRunConfig c) (liftRunConfig b)
            hstep htail
        refine ⟨1 + m, by omega, ?_⟩
        exact htrans

#print axioms MCore.Real.P01EvalRunLift.embed_active_state
#print axioms MCore.Real.P01EvalRunLift.lift_successor
#print axioms MCore.Real.P01EvalRunLift.lift_active
#print axioms MCore.Real.P01EvalRunLift.terminal_reachable_lift

end P01EvalRunLift
end Real
end MCore
