import MCore.Real.P01CheckedEvalRunTagPrefix
import MCore.Real.CanonicalCircuitBits
import MCore.Real.P01EncodedFrameTape

namespace MCore
namespace Real
namespace P01CheckedEvalReject

open CanonicalFinalProof
open CircuitK1
open CanonicalCircuitBits
open P01CNFMode
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunTagPrefix

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

/-- If the canonical root tag of a circuit is forbidden by the current syntax
mode, the checked evaluator physically rejects after the common
seek/decode/check prefix.

This is the root-rejection producer.  It contains no recursive semantic
assumption about children. -/
theorem root_disallowed_reaches_reject
    (mode : SyntaxMode)
    (witness : BitString)
    (phi : Circuit)
    (tail : BitString)
    (frames : List P01EncodedStackEvaluator.EvalFrame)
    (consumed padding : Nat)
    (hroot :
      tagAllowed mode (circuitTag phi) = false) :
    ∃ m,
      ({ state := .reject,
         tape :=
           evalCursorReadTape witness (consumed + 3)
             ((encodeCircuit phi).drop 3 ++ tail)
             (encodeEvalFrames frames) padding } : CheckedConfig) ∈
        checkedEvalRunLoopMachine.runBranches m
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit phi ++ tail)
                 (encodeEvalFrames frames) padding }] := by
  cases phi with
  | input i =>
      obtain ⟨m, hm, hrun⟩ :=
        disallowed_tag_prefix_reaches_reject
          mode witness (encodeNat i ++ tail)
          (encodeEvalFrames frames) consumed padding
          false false false hroot
      refine ⟨m, ?_⟩
      simpa [encodeCircuit, circuitTag, List.append_assoc] using hrun
  | const v =>
      cases v with
      | false =>
          obtain ⟨m, hm, hrun⟩ :=
            disallowed_tag_prefix_reaches_reject
              mode witness tail (encodeEvalFrames frames)
              consumed padding false false true hroot
          refine ⟨m, ?_⟩
          simpa [encodeCircuit, circuitTag] using hrun
      | true =>
          obtain ⟨m, hm, hrun⟩ :=
            disallowed_tag_prefix_reaches_reject
              mode witness tail (encodeEvalFrames frames)
              consumed padding false true false hroot
          refine ⟨m, ?_⟩
          simpa [encodeCircuit, circuitTag] using hrun
  | not child =>
      obtain ⟨m, hm, hrun⟩ :=
        disallowed_tag_prefix_reaches_reject
          mode witness (encodeCircuit child ++ tail)
          (encodeEvalFrames frames) consumed padding
          false true true hroot
      refine ⟨m, ?_⟩
      simpa [encodeCircuit, circuitTag, List.append_assoc] using hrun
  | and left right =>
      obtain ⟨m, hm, hrun⟩ :=
        disallowed_tag_prefix_reaches_reject
          mode witness
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames frames) consumed padding
          true false false hroot
      refine ⟨m, ?_⟩
      simpa [encodeCircuit, circuitTag, List.append_assoc] using hrun
  | or left right =>
      obtain ⟨m, hm, hrun⟩ :=
        disallowed_tag_prefix_reaches_reject
          mode witness
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames frames) consumed padding
          true false true hroot
      refine ⟨m, ?_⟩
      simpa [encodeCircuit, circuitTag, List.append_assoc] using hrun

#print axioms MCore.Real.P01CheckedEvalReject.root_disallowed_reaches_reject

end P01CheckedEvalReject
end Real
end MCore
