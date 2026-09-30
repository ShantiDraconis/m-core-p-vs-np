import MCore.Real.P01CheckedVerifierCompositeNTM
import MCore.Real.P01InputNodeCompositeRun
import MCore.Real.P01NeedExprCompositeNTM
import MCore.Real.P01HaveValueCompositeNTM
import MCore.Real.P01NTMRunLaws

namespace MCore
namespace Real
namespace P01CheckedVerifierDeterminism

open P01NTMRunLaws
open P01InputNodeCompositeNTM
open P01NeedExprCompositeNTM
open P01HaveValueCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedVerifierCompositeNTM

private theorem input_transition_length_le_one
    (q : InputNodeCompositeState) (symbol : Option Bool) :
    (inputNodeCompositeMachine.transition q symbol).length ≤ 1 := by
  let tape : Tape (Option Bool) :=
    { left := [], head := symbol, right := [] }
  have h :=
    inputNodeComposite_successors_length_le_one
      ({ state := q, tape := tape } :
        Configuration InputNodeCompositeState (Option Bool))
  simpa [NTM.successors, tape] using h

theorem needExpr_transition_length_le_one
    (q : NeedExprCompositeState) (symbol : Option Bool) :
    (needExprCompositeMachine.transition q symbol).length ≤ 1 := by
  cases q with
  | seek qs =>
      cases qs <;> simp [needExprCompositeMachine]
  | decode qd =>
      cases qd with
      | start => simp [needExprCompositeMachine]
      | bit1 b1 => cases b1 <;> simp [needExprCompositeMachine]
      | bit2 b1 b2 =>
          cases b1 <;> cases b2 <;> simp [needExprCompositeMachine]
      | halt tag =>
          cases tag <;> simp [needExprCompositeMachine]
      | reject => simp [needExprCompositeMachine]
  | input qi =>
      cases qi with
      | done selected mode => simp [needExprCompositeMachine]
      | reject => simp [needExprCompositeMachine]
      | look ql =>
          simpa [needExprCompositeMachine] using
            input_transition_length_le_one (.look ql) symbol
      | read mode qr =>
          simpa [needExprCompositeMachine] using
            input_transition_length_le_one (.read mode qr) symbol
      | ret mode selected qt =>
          simpa [needExprCompositeMachine] using
            input_transition_length_le_one (.ret mode selected qt) symbol
  | retValue value qr =>
      cases qr <;> simp [needExprCompositeMachine]
  | retPush frame qr =>
      cases qr <;> simp [needExprCompositeMachine]
  | push frame qp =>
      cases qp <;> simp [needExprCompositeMachine]
  | doneValue v => simp [needExprCompositeMachine]
  | doneNeed => simp [needExprCompositeMachine]
  | reject => simp [needExprCompositeMachine]

theorem haveValue_transition_length_le_one
    (q : HaveValueCompositeState) (symbol : Option Bool) :
    (haveValueCompositeMachine.transition q symbol).length ≤ 1 := by
  cases q with
  | start v =>
      cases symbol <;> simp [haveValueCompositeMachine]
  | peek v =>
      cases symbol <;> simp [haveValueCompositeMachine]
  | pop v qp =>
      cases qp <;> simp [haveValueCompositeMachine]
  | push frame qp =>
      cases qp <;> simp [haveValueCompositeMachine]
  | doneValue v => simp [haveValueCompositeMachine]
  | doneNeed => simp [haveValueCompositeMachine]
  | reject => simp [haveValueCompositeMachine]

theorem checkedEval_transition_length_le_one
    (q : CheckedEvalRunState) (symbol : Option Bool) :
    (checkedEvalRunLoopMachine.transition q symbol).length ≤ 1 := by
  cases q with
  | need mode qn =>
      cases qn with
      | input qi =>
          cases qi with
          | done selected retMode =>
              cases retMode <;> simp [checkedEvalRunLoopMachine]
          | reject =>
              simp [checkedEvalRunLoopMachine]
          | look ql =>
              simpa [checkedEvalRunLoopMachine] using
                input_transition_length_le_one (.look ql) symbol
          | read retMode qr =>
              simpa [checkedEvalRunLoopMachine] using
                input_transition_length_le_one (.read retMode qr) symbol
          | ret retMode selected qt =>
              simpa [checkedEvalRunLoopMachine] using
                input_transition_length_le_one (.ret retMode selected qt) symbol
      | decode qd =>
          cases qd with
          | halt tag =>
              cases h : P01CNFMode.tagAllowed mode tag <;>
                simp [checkedEvalRunLoopMachine, h,
                  needExpr_transition_length_le_one]
          | start =>
              simpa [checkedEvalRunLoopMachine] using
                needExpr_transition_length_le_one (.decode .start) symbol
          | bit1 b1 =>
              simpa [checkedEvalRunLoopMachine] using
                needExpr_transition_length_le_one (.decode (.bit1 b1)) symbol
          | bit2 b1 b2 =>
              simpa [checkedEvalRunLoopMachine] using
                needExpr_transition_length_le_one (.decode (.bit2 b1 b2)) symbol
          | reject =>
              simpa [checkedEvalRunLoopMachine] using
                needExpr_transition_length_le_one (.decode .reject) symbol
      | seek qs =>
          simpa [checkedEvalRunLoopMachine] using
            needExpr_transition_length_le_one (.seek qs) symbol
      | retValue value qr =>
          simpa [checkedEvalRunLoopMachine] using
            needExpr_transition_length_le_one (.retValue value qr) symbol
      | retPush frame qr =>
          simpa [checkedEvalRunLoopMachine] using
            needExpr_transition_length_le_one (.retPush frame qr) symbol
      | push frame qp =>
          simpa [checkedEvalRunLoopMachine] using
            needExpr_transition_length_le_one (.push frame qp) symbol
      | doneValue v => simp [checkedEvalRunLoopMachine]
      | doneNeed => simp [checkedEvalRunLoopMachine]
      | reject => simp [checkedEvalRunLoopMachine]
  | have mode qh =>
      cases qh with
      | peek v =>
          cases symbol <;> simp [checkedEvalRunLoopMachine]
      | pop v qp =>
          cases qp with
          | halt frame =>
              simpa [checkedEvalRunLoopMachine] using
                haveValue_transition_length_le_one (.pop v (.halt frame)) symbol
          | start =>
              simpa [checkedEvalRunLoopMachine] using
                haveValue_transition_length_le_one (.pop v .start) symbol
          | bit1 b1 =>
              simpa [checkedEvalRunLoopMachine] using
                haveValue_transition_length_le_one (.pop v (.bit1 b1)) symbol
          | bit2 b1 b2 =>
              simpa [checkedEvalRunLoopMachine] using
                haveValue_transition_length_le_one (.pop v (.bit2 b1 b2)) symbol
          | reject =>
              simpa [checkedEvalRunLoopMachine] using
                haveValue_transition_length_le_one (.pop v .reject) symbol
      | start v =>
          simpa [checkedEvalRunLoopMachine] using
            haveValue_transition_length_le_one (.start v) symbol
      | push frame qp =>
          simpa [checkedEvalRunLoopMachine] using
            haveValue_transition_length_le_one (.push frame qp) symbol
      | doneValue v => simp [checkedEvalRunLoopMachine]
      | doneNeed => simp [checkedEvalRunLoopMachine]
      | reject => simp [checkedEvalRunLoopMachine]
  | checkSource v =>
      cases symbol <;> simp [checkedEvalRunLoopMachine]
  | final v =>
      simp [checkedEvalRunLoopMachine]
  | reject =>
      simp [checkedEvalRunLoopMachine]

theorem checkedVerifier_transition_length_le_one
    (q : CheckedVerifierState) (symbol : Option Bool) :
    (checkedVerifierMachine.transition q symbol).length ≤ 1 := by
  cases q with
  | start =>
      cases symbol <;> simp [checkedVerifierMachine]
  | scan qs =>
      by_cases h : P01FullVerifierTraversal.sourceEndScanner.halting qs
      · simp [checkedVerifierMachine, h]
      · simp [checkedVerifierMachine, h]
  | enter =>
      simp [checkedVerifierMachine]
  | eval qe =>
      cases qe with
      | reject =>
          simp [checkedVerifierMachine]
      | need mode qn =>
          simpa [checkedVerifierMachine] using
            checkedEval_transition_length_le_one (.need mode qn) symbol
      | have mode qh =>
          simpa [checkedVerifierMachine] using
            checkedEval_transition_length_le_one (.have mode qh) symbol
      | checkSource v =>
          simpa [checkedVerifierMachine] using
            checkedEval_transition_length_le_one (.checkSource v) symbol
      | final v =>
          simpa [checkedVerifierMachine] using
            checkedEval_transition_length_le_one (.final v) symbol
  | reject =>
      simp [checkedVerifierMachine]

theorem checkedVerifier_successors_length_le_one
    (c : Configuration CheckedVerifierState (Option Bool)) :
    (checkedVerifierMachine.successors c).length ≤ 1 := by
  rcases c with ⟨q, tape⟩
  simpa [NTM.successors] using
    checkedVerifier_transition_length_le_one q tape.head

theorem checkedVerifier_runBranches_length_le_one :
    ∀ (n : Nat) (c : Configuration CheckedVerifierState (Option Bool)),
      (checkedVerifierMachine.runBranches n [c]).length ≤ 1 := by
  intro n
  induction n with
  | zero =>
      intro c
      simp [NTM.runBranches]
  | succ n ih =>
      intro c
      by_cases hh : Halted checkedVerifierMachine c
      · rw [runBranches_singleton_halted checkedVerifierMachine (n + 1) c hh]
        simp
      · rw [runBranches_singleton_active checkedVerifierMachine n c hh]
        have hlen := checkedVerifier_successors_length_le_one c
        cases hs : checkedVerifierMachine.successors c with
        | nil =>
            simp [hs, runBranches_nil]
        | cons d ds =>
            cases ds with
            | nil =>
                simpa [hs] using ih d
            | cons e es =>
                simp [hs] at hlen

theorem runBranches_eq_singleton_of_mem
    (n : Nat)
    (start terminal :
      Configuration CheckedVerifierState (Option Bool))
    (hmem :
      terminal ∈ checkedVerifierMachine.runBranches n [start]) :
    checkedVerifierMachine.runBranches n [start] = [terminal] := by
  apply P01InputNodeCompositeRun.list_eq_singleton_of_mem_length_le_one
  · exact hmem
  · exact checkedVerifier_runBranches_length_le_one n start

theorem haltsWithin_of_reaches_halted
    (n : Nat)
    (start terminal :
      Configuration CheckedVerifierState (Option Bool))
    (hmem :
      terminal ∈ checkedVerifierMachine.runBranches n [start])
    (hhalt : Halted checkedVerifierMachine terminal) :
    checkedVerifierMachine.HaltsWithin n start := by
  rw [haltsWithin_iff_halted]
  intro z hz
  have heq := runBranches_eq_singleton_of_mem n start terminal hmem
  rw [heq] at hz
  simp only [List.mem_singleton] at hz
  subst z
  exact hhalt

#print axioms MCore.Real.P01CheckedVerifierDeterminism.needExpr_transition_length_le_one
#print axioms MCore.Real.P01CheckedVerifierDeterminism.haveValue_transition_length_le_one
#print axioms MCore.Real.P01CheckedVerifierDeterminism.checkedEval_transition_length_le_one
#print axioms MCore.Real.P01CheckedVerifierDeterminism.checkedVerifier_transition_length_le_one
#print axioms MCore.Real.P01CheckedVerifierDeterminism.checkedVerifier_runBranches_length_le_one
#print axioms MCore.Real.P01CheckedVerifierDeterminism.haltsWithin_of_reaches_halted

end P01CheckedVerifierDeterminism
end Real
end MCore
