import MCore.Real.P01EvalRunLoopRun
import MCore.Real.P01EvalRunInputTag
import MCore.Real.P01EvalRunHaveValue
import MCore.Real.CanonicalSATWitness

namespace MCore
namespace Real
namespace P01EvalRunCircuitCertificate

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open CanonicalSATWitness
open P01NTMRunLaws
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01EvalRunLoopNTM
open P01EvalRunLoopRun
open P01EvalRunInputTag
open P01EvalRunHaveValue
open P01InputNodeCompositeRun
open P01InputNodeRoundTrip

abbrev LoopConfig :=
  Configuration EvalRunLoopState (Option Bool)

/-- Normalized physical result after evaluating one encoded circuit while
preserving an arbitrary external tail/continuation.

When no external work remains, the loop is already in its global final state.
Otherwise it is normalized to the canonical `haveValue` restart state. -/
def LoopOutcome
    (witness : BitString)
    (value : Bool)
    (tail : BitString)
    (frames : List EvalFrame)
    (cfg : LoopConfig) : Prop :=
  match tail, frames with
  | [], [] =>
      ∃ tape : Tape (Option Bool),
        cfg = { state := .final value, tape := tape }
  | _, _ =>
      ∃ consumed padding : Nat,
        cfg =
          { state := .have (.start value),
            tape :=
              evalCursorStackEndTape witness consumed tail
                (encodeEvalFrames frames) padding }

/-- Producer-first certificate for one circuit: starting from the canonical
physical `needExpr` representation of `encodeCircuit phi ++ tail`, the
global loop reaches the exact semantic value while preserving the external
tail and continuation shape.

No complexity bound is claimed yet; this is the semantic/run certificate that
will later receive the polynomial majorant. -/
def CircuitRunCertificate
    (sigma : Assignment)
    (witness : BitString)
    (phi : Circuit) : Prop :=
  ∀ (tail : BitString) (frames : List EvalFrame)
      (consumed padding : Nat),
    varBound phi ≤ witness.length →
    (∀ i, i < varBound phi →
      witness.getD i false = sigma i) →
    ∃ m cfg,
      cfg ∈
        evalRunLoopMachine.runBranches m
          [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit phi ++ tail)
                 (encodeEvalFrames frames) padding }] ∧
      LoopOutcome witness (evalCircuit sigma phi) tail frames cfg

/-- Input nodes inhabit the global circuit-run certificate directly from the
already-certified indexed-input loop. -/
theorem input_certificate
    (sigma : Assignment)
    (witness : BitString)
    (i : Nat) :
    CircuitRunCertificate sigma witness (.input i) := by
  intro tail frames consumed padding hlen hread
  have hiVar : i < varBound (.input i) := by
    simp [varBound]
  have hi : i < witness.length :=
    Nat.lt_of_lt_of_le hiVar hlen
  have hvalue : witness.getD i false = sigma i :=
    hread i hiVar
  obtain ⟨m, hm, hrun⟩ :=
    inputTag_loop_reaches_mode
      witness tail (encodeEvalFrames frames)
      consumed padding i hi
  let cfg : LoopConfig :=
    inputLoopConfig
      ({ state :=
           .done (witness.getD i false)
             (inputNodeFinalMode tail (encodeEvalFrames frames)),
         tape :=
           (inputAfterReadTarget witness
             (consumedAfterInputIndex (consumed + 3) i)
             tail (encodeEvalFrames frames) padding).tape } :
        Configuration P01InputNodeCompositeNTM.InputNodeCompositeState
          (Option Bool))
  refine ⟨m, cfg, ?_, ?_⟩
  · simpa [cfg, encodeCircuit] using hrun
  · change LoopOutcome witness (sigma i) tail frames cfg
    rw [← hvalue]
    cases tail with
    | cons b bs =>
        refine ⟨consumedAfterInputIndex (consumed + 3) i, padding, ?_⟩
        simp [LoopOutcome, cfg, inputLoopConfig, inputLoopEmbed,
          inputNodeFinalMode, inputAfterReadTarget]
    | nil =>
        cases frames with
        | nil =>
            refine ⟨(inputAfterReadTarget witness
              (consumedAfterInputIndex (consumed + 3) i)
              [] [] padding).tape, ?_⟩
            simp [LoopOutcome, cfg, inputLoopConfig, inputLoopEmbed,
              inputNodeFinalMode, inputAfterReadTarget]
        | cons f fs =>
            refine ⟨consumedAfterInputIndex (consumed + 3) i, padding, ?_⟩
            simp [LoopOutcome, cfg, inputLoopConfig, inputLoopEmbed,
              inputNodeFinalMode, inputAfterReadTarget,
              encodeEvalFrames, encodeEvalFrame]

/-- Constant-false nodes inhabit the global circuit-run certificate. -/
theorem constFalse_certificate
    (sigma : Assignment)
    (witness : BitString) :
    CircuitRunCertificate sigma witness (.const false) := by
  intro tail frames consumed padding hlen hread
  obtain ⟨m1, hm1, h1⟩ :=
    constFalse_loop_reaches_have
      witness tail (encodeEvalFrames frames) consumed padding
  let cHave : LoopConfig :=
    { state := .have (.start false),
      tape :=
        evalCursorStackEndTape witness (consumed + 3)
          tail (encodeEvalFrames frames) padding }
  have h1' :
      cHave ∈
        evalRunLoopMachine.runBranches m1
          [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.const false) ++ tail)
                 (encodeEvalFrames frames) padding }] := by
    simpa [cHave, encodeCircuit] using h1
  cases tail with
  | cons b bs =>
      refine ⟨m1, cHave, h1', ?_⟩
      exact ⟨consumed + 3, padding, rfl⟩
  | nil =>
      cases frames with
      | cons f fs =>
          refine ⟨m1, cHave, h1', ?_⟩
          exact ⟨consumed + 3, padding, rfl⟩
      | nil =>
          obtain ⟨m2, hm2, h2⟩ :=
            emptyFrames_loop_reaches_final
              witness [] (consumed + 3) padding false
          let cFinal : LoopConfig :=
            { state := .final false,
              tape :=
                evalCursorStackEndTape witness (consumed + 3)
                  [] [] padding }
          have hall :=
            mem_runBranches_trans evalRunLoopMachine
              m1 m2
              [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.const false))
                     [] padding }]
              cHave cFinal h1' h2
          refine ⟨m1 + m2, cFinal, ?_, ?_⟩
          · simpa using hall
          · exact ⟨cFinal.tape, rfl⟩

/-- Constant-true nodes inhabit the global circuit-run certificate. -/
theorem constTrue_certificate
    (sigma : Assignment)
    (witness : BitString) :
    CircuitRunCertificate sigma witness (.const true) := by
  intro tail frames consumed padding hlen hread
  obtain ⟨m1, hm1, h1⟩ :=
    constTrue_loop_reaches_have
      witness tail (encodeEvalFrames frames) consumed padding
  let cHave : LoopConfig :=
    { state := .have (.start true),
      tape :=
        evalCursorStackEndTape witness (consumed + 3)
          tail (encodeEvalFrames frames) padding }
  have h1' :
      cHave ∈
        evalRunLoopMachine.runBranches m1
          [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.const true) ++ tail)
                 (encodeEvalFrames frames) padding }] := by
    simpa [cHave, encodeCircuit] using h1
  cases tail with
  | cons b bs =>
      refine ⟨m1, cHave, h1', ?_⟩
      exact ⟨consumed + 3, padding, rfl⟩
  | nil =>
      cases frames with
      | cons f fs =>
          refine ⟨m1, cHave, h1', ?_⟩
          exact ⟨consumed + 3, padding, rfl⟩
      | nil =>
          obtain ⟨m2, hm2, h2⟩ :=
            emptyFrames_loop_reaches_final
              witness [] (consumed + 3) padding true
          let cFinal : LoopConfig :=
            { state := .final true,
              tape :=
                evalCursorStackEndTape witness (consumed + 3)
                  [] [] padding }
          have hall :=
            mem_runBranches_trans evalRunLoopMachine
              m1 m2
              [{ state := .need P01NeedExprCompositeNTM.needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.const true))
                     [] padding }]
              cHave cFinal h1' h2
          refine ⟨m1 + m2, cFinal, ?_, ?_⟩
          · simpa using hall
          · exact ⟨cFinal.tape, rfl⟩

theorem const_certificate
    (sigma : Assignment)
    (witness : BitString)
    (b : Bool) :
    CircuitRunCertificate sigma witness (.const b) := by
  cases b
  · exact constFalse_certificate sigma witness
  · exact constTrue_certificate sigma witness

#print axioms MCore.Real.P01EvalRunCircuitCertificate.input_certificate
#print axioms MCore.Real.P01EvalRunCircuitCertificate.constFalse_certificate
#print axioms MCore.Real.P01EvalRunCircuitCertificate.constTrue_certificate
#print axioms MCore.Real.P01EvalRunCircuitCertificate.const_certificate

end P01EvalRunCircuitCertificate
end Real
end MCore
