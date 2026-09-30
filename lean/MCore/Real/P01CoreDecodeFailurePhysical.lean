import MCore.Real.P01CoreDecodeFailureBudget
import MCore.Real.P01DecodeFailureLaws
import MCore.Real.P01ExactBoundedAll
import MCore.Real.P01CheckedEvalRejectBounded
import MCore.Real.P01CheckedEvalRunBoundedHelpers
import MCore.Real.P01MalformedRawBoundedReject
import MCore.Real.P01RawVerifierFromCoreReject

namespace MCore
namespace Real
namespace P01CoreDecodeFailurePhysical

open CanonicalFinalProof
open CanonicalCircuitBits
open CircuitK1
open CanonicalSATWitness
open P01CNFMode
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunBaseCases
open P01CheckedEvalRunBoundedHelpers
open P01CheckedEvalRunBoundedCertificate
open P01CheckedVerifierInvariant
open P01CheckedEvalRejectBounded
open P01ExactBoundedAll
open P01MaterialGlobalBudget
open P01MalformedRawBoundedReject
open P01DecodeFailureLaws
open P01CoreDecodeFailureAtoms
open P01CoreDecodeFailureBudget
open P01NTMRunLaws

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

private theorem unterminated_input_within_loop
    (n : Nat)
    (mode : SyntaxMode)
    (witness frameStack : BitString)
    (consumed padding k : Nat)
    (hLayout :
      CheckedLayoutBound n consumed
        (false :: false :: false :: List.replicate k true)
        frameStack) :
    ∃ m ≤ checkedLoopStepEnvelope n,
      ∃ tape : Tape (Option Bool),
        ({ state := .reject, tape := tape } : CheckedConfig) ∈
          checkedEvalRunLoopMachine.runBranches m
            [{ state := .need mode needExprCompositeMachine.initial,
               tape :=
                 evalCursorStackEndTape witness consumed
                   (false :: false :: false :: List.replicate k true)
                   frameStack padding }] := by
  obtain ⟨m, hm, tape, hrun⟩ :=
    P01CheckedEvalRunInputTag.inputTag_unterminated_reaches_reject
      mode witness frameStack consumed padding k
  have hk : k ≤ n := by
    have hs := hLayout.source_le
    simp at hs
    omega
  have hf : frameStack.length ≤ n := hLayout.frames_le
  have hraw :
      P01CheckedEvalRunInputTag.checkedUnterminatedInputFuel k frameStack ≤
        3 * n + 13 := by
    unfold P01CheckedEvalRunInputTag.checkedUnterminatedInputFuel
      P01CheckedEvalRunTagPrefix.checkedTagPrefixFuel
    simp
    omega
  have hbase : n + 1 ≤ (n + 1)^2 := by
    have hp : 1 ≤ n + 1 := by omega
    calc
      n + 1 = (n + 1) * 1 := by simp
      _ ≤ (n + 1) * (n + 1) :=
        Nat.mul_le_mul_left (n + 1) hp
      _ = (n + 1)^2 := by simp [Nat.pow_two]
  have hlinear : 3 * n + 13 ≤ 16 * (n + 1) := by omega
  have h16 :
      16 * (n + 1) ≤ 16 * (n + 1)^2 :=
    Nat.mul_le_mul_left 16 hbase
  have h256 :
      16 * (n + 1)^2 ≤ 256 * (n + 1)^2 :=
    Nat.mul_le_mul_right ((n + 1)^2) (by omega)
  refine ⟨m, Nat.le_trans hm ?_, tape, hrun⟩
  unfold checkedLoopStepEnvelope
  exact Nat.le_trans hraw (Nat.le_trans hlinear (Nat.le_trans h16 h256))

private theorem one_plus_potential_le_parent
    (restLength n : Nat) :
    checkedLoopStepEnvelope n +
        coreRejectPotential restLength n ≤
      coreRejectPotential (restLength + 3) n :=
  tag_plus_recursive_le restLength n

/-- Recursive physical rejection for functional decoder-core failure.

The source-length potential decreases whenever a constructor tag is consumed.
For a binary right-child failure, the potential decrease also pays for exact
evaluation of the already-decoded left child and its continuation step.
-/
theorem coreDecodeFailurePhysicalAux :
    ∀ (fuel : Nat) (source : BitString) (mode : SyntaxMode)
      (witness : BitString) (frames : List EvalFrame)
      (consumed padding n : Nat),
      source.length < fuel →
      n ≤ witness.length →
      CheckedLayoutBound n consumed source (encodeEvalFrames frames) →
      decodeCircuitCore fuel source = none →
      ∃ m ≤ coreRejectPotential source.length n, ∃ cfg,
        cfg ∈
          checkedEvalRunLoopMachine.runBranches m
            [{ state := .need mode needExprCompositeMachine.initial,
               tape :=
                 evalCursorStackEndTape witness consumed source
                   (encodeEvalFrames frames) padding }] ∧
        cfg.state = .reject := by
  intro fuel
  induction fuel with
  | zero =>
      intro source mode witness frames consumed padding n hlt
      omega
  | succ fuel ih =>
      intro source mode witness frames consumed padding n
        hlt hwit hLayout hdecode
      rcases decodeCore_none_cases fuel source hdecode with
        hshort | hinput | hnot | hand | hor | hinvalid

      · obtain ⟨m, hm, tape, hrun⟩ :=
          short_tag_reaches_reject_within_envelope
            n mode witness source (encodeEvalFrames frames)
            consumed padding hshort hLayout.source_le hLayout.frames_le
        refine ⟨m, Nat.le_trans hm (loop_le_potential source.length n),
          { state := .reject, tape := tape }, hrun, rfl⟩

      · rcases hinput with ⟨rest, rfl, hnat⟩
        have hrep := P01DecodeCoreLaws.decodeNat_none_eq_replicate_true rest hnat
        have hLayout' :
            CheckedLayoutBound n consumed
              (false :: false :: false :: List.replicate rest.length true)
              (encodeEvalFrames frames) := by
          simpa [hrep] using hLayout
        obtain ⟨m, hm, tape, hrun⟩ :=
          unterminated_input_within_loop
            n mode witness (encodeEvalFrames frames)
            consumed padding rest.length hLayout'
        refine ⟨m, Nat.le_trans hm ?_,
          { state := .reject, tape := tape }, ?_, rfl⟩
        · simpa [hrep] using
            (loop_le_potential
              (false :: false :: false :: rest).length n)
        · simpa [hrep] using hrun

      · rcases hnot with ⟨rest, rfl, hchild⟩
        cases hallowed : tagAllowed mode .neg with
        | false =>
            obtain ⟨m, hm, hrun⟩ :=
              disallowed_tag_prefix_reaches_reject_within_envelope
                n mode witness rest (encodeEvalFrames frames)
                consumed padding false true true hallowed
                hLayout.source_le hLayout.frames_le
            refine ⟨m, Nat.le_trans hm
              (loop_le_potential
                (false :: true :: true :: rest).length n),
              { state := .reject,
                tape := evalCursorReadTape witness (consumed + 3)
                  rest (encodeEvalFrames frames) padding },
              hrun, rfl⟩
        | true =>
            obtain ⟨m0, hm0, h0⟩ :=
              pushTag_checked_reaches_need_within_envelope
                n mode witness rest (encodeEvalFrames frames)
                consumed padding false true true .neg .neg
                rfl hallowed
                (by simp [P01CheckedEvalRunTagPrefix.postTagState, childMode])
                hLayout.source_le hLayout.frames_le
            let padChild := (((padding - 1) - 1) - 1)
            have hChildLayout :
                CheckedLayoutBound n (consumed + 3) rest
                  (encodeEvalFrames (.neg :: frames)) := by
              simpa [encodeEvalFrames, List.append_assoc] using
                after_push_tag n consumed false true true rest
                  (encodeEvalFrames frames) .neg hLayout
            have hrestFuel : rest.length < fuel := by
              simp at hlt
              omega
            obtain ⟨m1, hm1, cfg1, h1, hrej1⟩ :=
              ih rest .mustInput witness (.neg :: frames)
                (consumed + 3) padChild n
                hrestFuel hwit hChildLayout hchild
            have h0' :
                ({ state := .need .mustInput needExprCompositeMachine.initial,
                   tape :=
                     evalCursorStackEndTape witness (consumed + 3)
                       rest (encodeEvalFrames (.neg :: frames)) padChild } :
                  CheckedConfig) ∈
                checkedEvalRunLoopMachine.runBranches m0
                  [{ state := .need mode needExprCompositeMachine.initial,
                     tape :=
                       evalCursorStackEndTape witness consumed
                         (false :: true :: true :: rest)
                         (encodeEvalFrames frames) padding }] := by
              simpa [padChild, encodeEvalFrames, List.append_assoc,
                childMode] using h0
            have hAll :=
              mem_runBranches_trans checkedEvalRunLoopMachine
                m0 m1
                [{ state := .need mode needExprCompositeMachine.initial,
                   tape :=
                     evalCursorStackEndTape witness consumed
                       (false :: true :: true :: rest)
                       (encodeEvalFrames frames) padding }]
                ({ state := .need .mustInput needExprCompositeMachine.initial,
                   tape :=
                     evalCursorStackEndTape witness (consumed + 3)
                       rest (encodeEvalFrames (.neg :: frames)) padChild } :
                  CheckedConfig)
                cfg1 h0' h1
            have hsum :
                m0 + m1 ≤
                  checkedLoopStepEnvelope n +
                    coreRejectPotential rest.length n :=
              Nat.add_le_add hm0 hm1
            refine ⟨m0 + m1, Nat.le_trans hsum ?_, cfg1, hAll, hrej1⟩
            simpa using one_plus_potential_le_parent rest.length n

      · rcases hand with ⟨rest, rfl, hfail⟩
        cases hallowed : tagAllowed mode .and with
        | false =>
            obtain ⟨m, hm, hrun⟩ :=
              disallowed_tag_prefix_reaches_reject_within_envelope
                n mode witness rest (encodeEvalFrames frames)
                consumed padding true false false hallowed
                hLayout.source_le hLayout.frames_le
            refine ⟨m, Nat.le_trans hm
              (loop_le_potential
                (true :: false :: false :: rest).length n),
              { state := .reject,
                tape := evalCursorReadTape witness (consumed + 3)
                  rest (encodeEvalFrames frames) padding },
              hrun, rfl⟩
        | true =>
            have hmode : childMode mode .and = .cnf := by
              cases mode <;> simp [tagAllowed, childMode] at hallowed ⊢
            obtain ⟨m0, hm0, h0⟩ :=
              pushTag_checked_reaches_need_within_envelope
                n mode witness rest (encodeEvalFrames frames)
                consumed padding true false false .and .andLeft
                rfl hallowed
                (by simp [P01CheckedEvalRunTagPrefix.postTagState, childMode])
                hLayout.source_le hLayout.frames_le
            let padLeft := (((padding - 1) - 1) - 1)
            have hPushLayout :
                CheckedLayoutBound n (consumed + 3) rest
                  (encodeEvalFrames (.andLeft :: frames)) := by
              simpa [encodeEvalFrames, List.append_assoc] using
                after_push_tag n consumed true false false rest
                  (encodeEvalFrames frames) .andLeft hLayout
            have h0' :
                ({ state := .need .cnf needExprCompositeMachine.initial,
                   tape :=
                     evalCursorStackEndTape witness (consumed + 3)
                       rest (encodeEvalFrames (.andLeft :: frames)) padLeft } :
                  CheckedConfig) ∈
                checkedEvalRunLoopMachine.runBranches m0
                  [{ state := .need mode needExprCompositeMachine.initial,
                     tape :=
                       evalCursorStackEndTape witness consumed
                         (true :: false :: false :: rest)
                         (encodeEvalFrames frames) padding }] := by
              simpa [padLeft, hmode, encodeEvalFrames,
                List.append_assoc] using h0
            rcases hfail with hleft | hright
            · have hrestFuel : rest.length < fuel := by
                simp at hlt
                omega
              obtain ⟨m1, hm1, cfg1, h1, hrej1⟩ :=
                ih rest .cnf witness (.andLeft :: frames)
                  (consumed + 3) padLeft n
                  hrestFuel hwit hPushLayout hleft
              have hAll :=
                mem_runBranches_trans checkedEvalRunLoopMachine
                  m0 m1
                  [{ state := .need mode needExprCompositeMachine.initial,
                     tape :=
                       evalCursorStackEndTape witness consumed
                         (true :: false :: false :: rest)
                         (encodeEvalFrames frames) padding }]
                  ({ state := .need .cnf needExprCompositeMachine.initial,
                     tape :=
                       evalCursorStackEndTape witness (consumed + 3)
                         rest (encodeEvalFrames (.andLeft :: frames)) padLeft } :
                    CheckedConfig)
                  cfg1 h0' h1
              have hsum :
                  m0 + m1 ≤ checkedLoopStepEnvelope n +
                    coreRejectPotential rest.length n :=
                Nat.add_le_add hm0 hm1
              refine ⟨m0 + m1, Nat.le_trans hsum ?_,
                cfg1, hAll, hrej1⟩
              simpa using tag_plus_recursive_le rest.length n

            · rcases hright with ⟨a, rest', hleftDec, hrightFail⟩
              have hrestEq :
                  rest = encodeCircuit a ++ rest' :=
                P01DecodeCoreLaws.decodeCircuitCore_sound
                  fuel rest a rest' hleftDec
              have hLayoutA :
                  CheckedLayoutBound n (consumed + 3)
                    (encodeCircuit a ++ rest')
                    (encodeEvalFrames (.andLeft :: frames)) := by
                simpa [hrestEq] using hPushLayout
              have henc : (encodeCircuit a).length ≤ n := by
                exact hLayoutA.source_le.trans (Nat.le_refl n)
              have hvar : varBound a ≤ witness.length :=
                Nat.le_trans (varBound_le_encoded_length a)
                  (Nat.le_trans henc hwit)
              let sigma : Assignment := fun i => witness.getD i false
              have hread :
                  ∀ i, i < varBound a →
                    witness.getD i false = sigma i := by
                intro i hi
                rfl
              cases hcheck : modeCheck .cnf a with
              | false =>
                  obtain ⟨m1, hm1, cfg1, h1, hrej1⟩ :=
                    bounded_circuit_reject_certificate
                      sigma witness a .cnf hcheck rest'
                      (.andLeft :: frames) (consumed + 3) padLeft n
                      hLayoutA hvar hread
                  have h1' :
                      cfg1 ∈ checkedEvalRunLoopMachine.runBranches m1
                        [({ state := .need .cnf needExprCompositeMachine.initial,
                            tape :=
                              evalCursorStackEndTape witness (consumed + 3)
                                rest (encodeEvalFrames (.andLeft :: frames))
                                padLeft } : CheckedConfig)] := by
                    simpa [hrestEq] using h1
                  have hAll :=
                    mem_runBranches_trans checkedEvalRunLoopMachine
                      m0 m1
                      [{ state := .need mode needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumed
                             (true :: false :: false :: rest)
                             (encodeEvalFrames frames) padding }]
                      ({ state := .need .cnf needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness (consumed + 3)
                             rest (encodeEvalFrames (.andLeft :: frames))
                             padLeft } : CheckedConfig)
                      cfg1 h0' h1'
                  have hsum :
                      m0 + m1 ≤
                        checkedLoopStepEnvelope n +
                          checkedCircuitBudget a n :=
                    Nat.add_le_add hm0 hm1
                  have hcap :=
                    binary_left_semantic_reject_le a rest'.length n
                  refine ⟨m0 + m1, Nat.le_trans hsum ?_,
                    cfg1, hAll, hrej1⟩
                  simpa [hrestEq, List.length_append, Nat.add_assoc] using hcap

              | true =>
                  obtain ⟨m1, hm1, cfg1, h1, hout1⟩ :=
                    exact_bounded_all sigma witness a .cnf
                      hcheck rest' (.andLeft :: frames)
                      (consumed + 3) padLeft n hLayoutA hvar hread
                  let consumedA :=
                    (consumed + 3) + (encodeCircuit a).length
                  have hout1' :
                      ∃ padding1,
                        cfg1 =
                          { state := .have (exitMode .cnf a)
                              (.start (evalCircuit sigma a)),
                            tape :=
                              evalCursorStackEndTape witness consumedA rest'
                                (encodeEvalFrames (.andLeft :: frames))
                                padding1 } := by
                    simpa [ExactCheckedLoopOutcome, consumedA] using hout1
                  rcases hout1' with ⟨padding1, hcfg1⟩
                  subst cfg1
                  have h1' :
                      ({ state := .have (exitMode .cnf a)
                           (.start (evalCircuit sigma a)),
                         tape :=
                           evalCursorStackEndTape witness consumedA rest'
                             (encodeEvalFrames (.andLeft :: frames))
                             padding1 } : CheckedConfig) ∈
                        checkedEvalRunLoopMachine.runBranches m1
                          [({ state := .need .cnf needExprCompositeMachine.initial,
                              tape :=
                                evalCursorStackEndTape witness (consumed + 3)
                                  rest (encodeEvalFrames (.andLeft :: frames))
                                  padLeft } : CheckedConfig)] := by
                    simpa [hrestEq, consumedA] using h1
                  obtain ⟨m2, hm2, h2⟩ :=
                    andLeftReturn_checked_reaches_need_within_envelope
                      n (exitMode .cnf a) witness rest'
                      (encodeEvalFrames frames) consumedA padding1
                      (evalCircuit sigma a)
                  let padRight := ((((padding1 + 3) - 1) - 1) - 1)
                  have hLayoutAfterA :
                      CheckedLayoutBound n consumedA rest'
                        (encodeEvalFrames (.andLeft :: frames)) := by
                    simpa [consumedA] using
                      after_circuit n (consumed + 3) a rest'
                        (encodeEvalFrames (.andLeft :: frames)) hLayoutA
                  have hLayoutRight :
                      CheckedLayoutBound n consumedA rest'
                        (encodeEvalFrames
                          (.andRight (evalCircuit sigma a) :: frames)) := by
                    simpa [encodeEvalFrames, List.append_assoc] using
                      replace_top_frame n consumedA rest'
                        (encodeEvalFrames frames) .andLeft
                        (.andRight (evalCircuit sigma a)) hLayoutAfterA
                  have hrestFuel : rest'.length < fuel := by
                    have hf := hlt
                    simp [hrestEq, List.length_append] at hf
                    omega
                  obtain ⟨m3, hm3, cfg3, h3, hrej3⟩ :=
                    ih rest' .cnf witness
                      (.andRight (evalCircuit sigma a) :: frames)
                      consumedA padRight n
                      hrestFuel hwit hLayoutRight hrightFail
                  have h2' :
                      ({ state := .need .cnf needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumedA rest'
                             (encodeEvalFrames
                               (.andRight (evalCircuit sigma a) :: frames))
                             padRight } : CheckedConfig) ∈
                        checkedEvalRunLoopMachine.runBranches m2
                          [({ state := .have (exitMode .cnf a)
                               (.start (evalCircuit sigma a)),
                              tape :=
                                evalCursorStackEndTape witness consumedA rest'
                                  (encodeEvalFrames (.andLeft :: frames))
                                  padding1 } : CheckedConfig)] := by
                    simpa [padRight, encodeEvalFrames, List.append_assoc] using h2
                  have h01 :=
                    mem_runBranches_trans checkedEvalRunLoopMachine
                      m0 m1
                      [{ state := .need mode needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumed
                             (true :: false :: false :: rest)
                             (encodeEvalFrames frames) padding }]
                      ({ state := .need .cnf needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness (consumed + 3)
                             rest (encodeEvalFrames (.andLeft :: frames))
                             padLeft } : CheckedConfig)
                      ({ state := .have (exitMode .cnf a)
                           (.start (evalCircuit sigma a)),
                         tape :=
                           evalCursorStackEndTape witness consumedA rest'
                             (encodeEvalFrames (.andLeft :: frames))
                             padding1 } : CheckedConfig)
                      h0' h1'
                  have h012 :=
                    mem_runBranches_trans checkedEvalRunLoopMachine
                      (m0 + m1) m2
                      [{ state := .need mode needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumed
                             (true :: false :: false :: rest)
                             (encodeEvalFrames frames) padding }]
                      ({ state := .have (exitMode .cnf a)
                           (.start (evalCircuit sigma a)),
                         tape :=
                           evalCursorStackEndTape witness consumedA rest'
                             (encodeEvalFrames (.andLeft :: frames))
                             padding1 } : CheckedConfig)
                      ({ state := .need .cnf needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumedA rest'
                             (encodeEvalFrames
                               (.andRight (evalCircuit sigma a) :: frames))
                             padRight } : CheckedConfig)
                      h01 h2'
                  have hAll :=
                    mem_runBranches_trans checkedEvalRunLoopMachine
                      (m0 + m1 + m2) m3
                      [{ state := .need mode needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumed
                             (true :: false :: false :: rest)
                             (encodeEvalFrames frames) padding }]
                      ({ state := .need .cnf needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumedA rest'
                             (encodeEvalFrames
                               (.andRight (evalCircuit sigma a) :: frames))
                             padRight } : CheckedConfig)
                      cfg3 h012 h3
                  have hsum :
                      m0 + m1 + m2 + m3 ≤
                        checkedLoopStepEnvelope n +
                          checkedCircuitBudget a n +
                          checkedLoopStepEnvelope n +
                          coreRejectPotential rest'.length n := by
                    omega
                  have hcap :=
                    binary_right_path_le a rest'.length n
                  refine ⟨m0 + m1 + m2 + m3,
                    Nat.le_trans hsum ?_, cfg3, hAll, hrej3⟩
                  simpa [hrestEq, List.length_append, Nat.add_assoc] using hcap

      · rcases hor with ⟨rest, rfl, hfail⟩
        cases hallowed : tagAllowed mode .or with
        | false =>
            obtain ⟨m, hm, hrun⟩ :=
              disallowed_tag_prefix_reaches_reject_within_envelope
                n mode witness rest (encodeEvalFrames frames)
                consumed padding true false true hallowed
                hLayout.source_le hLayout.frames_le
            refine ⟨m, Nat.le_trans hm
              (loop_le_potential
                (true :: false :: true :: rest).length n),
              { state := .reject,
                tape := evalCursorReadTape witness (consumed + 3)
                  rest (encodeEvalFrames frames) padding },
              hrun, rfl⟩
        | true =>
            obtain ⟨m0, hm0, h0⟩ :=
              pushTag_checked_reaches_need_within_envelope
                n mode witness rest (encodeEvalFrames frames)
                consumed padding true false true .or .orLeft
                rfl hallowed
                (by simp [P01CheckedEvalRunTagPrefix.postTagState, childMode])
                hLayout.source_le hLayout.frames_le
            let padLeft := (((padding - 1) - 1) - 1)
            have hPushLayout :
                CheckedLayoutBound n (consumed + 3) rest
                  (encodeEvalFrames (.orLeft :: frames)) := by
              simpa [encodeEvalFrames, List.append_assoc] using
                after_push_tag n consumed true false true rest
                  (encodeEvalFrames frames) .orLeft hLayout
            have h0' :
                ({ state := .need .clause needExprCompositeMachine.initial,
                   tape :=
                     evalCursorStackEndTape witness (consumed + 3)
                       rest (encodeEvalFrames (.orLeft :: frames)) padLeft } :
                  CheckedConfig) ∈
                checkedEvalRunLoopMachine.runBranches m0
                  [{ state := .need mode needExprCompositeMachine.initial,
                     tape :=
                       evalCursorStackEndTape witness consumed
                         (true :: false :: true :: rest)
                         (encodeEvalFrames frames) padding }] := by
              simpa [padLeft, childMode, encodeEvalFrames,
                List.append_assoc] using h0
            rcases hfail with hleft | hright
            · have hrestFuel : rest.length < fuel := by
                simp at hlt
                omega
              obtain ⟨m1, hm1, cfg1, h1, hrej1⟩ :=
                ih rest .clause witness (.orLeft :: frames)
                  (consumed + 3) padLeft n
                  hrestFuel hwit hPushLayout hleft
              have hAll :=
                mem_runBranches_trans checkedEvalRunLoopMachine
                  m0 m1
                  [{ state := .need mode needExprCompositeMachine.initial,
                     tape :=
                       evalCursorStackEndTape witness consumed
                         (true :: false :: true :: rest)
                         (encodeEvalFrames frames) padding }]
                  ({ state := .need .clause needExprCompositeMachine.initial,
                     tape :=
                       evalCursorStackEndTape witness (consumed + 3)
                         rest (encodeEvalFrames (.orLeft :: frames)) padLeft } :
                    CheckedConfig)
                  cfg1 h0' h1
              have hsum :
                  m0 + m1 ≤ checkedLoopStepEnvelope n +
                    coreRejectPotential rest.length n :=
                Nat.add_le_add hm0 hm1
              refine ⟨m0 + m1, Nat.le_trans hsum ?_,
                cfg1, hAll, hrej1⟩
              simpa using tag_plus_recursive_le rest.length n

            · rcases hright with ⟨a, rest', hleftDec, hrightFail⟩
              have hrestEq :
                  rest = encodeCircuit a ++ rest' :=
                P01DecodeCoreLaws.decodeCircuitCore_sound
                  fuel rest a rest' hleftDec
              have hLayoutA :
                  CheckedLayoutBound n (consumed + 3)
                    (encodeCircuit a ++ rest')
                    (encodeEvalFrames (.orLeft :: frames)) := by
                simpa [hrestEq] using hPushLayout
              have henc : (encodeCircuit a).length ≤ n :=
                hLayoutA.source_le
              have hvar : varBound a ≤ witness.length :=
                Nat.le_trans (varBound_le_encoded_length a)
                  (Nat.le_trans henc hwit)
              let sigma : Assignment := fun i => witness.getD i false
              have hread :
                  ∀ i, i < varBound a →
                    witness.getD i false = sigma i := by
                intro i hi
                rfl
              cases hcheck : modeCheck .clause a with
              | false =>
                  obtain ⟨m1, hm1, cfg1, h1, hrej1⟩ :=
                    bounded_circuit_reject_certificate
                      sigma witness a .clause hcheck rest'
                      (.orLeft :: frames) (consumed + 3) padLeft n
                      hLayoutA hvar hread
                  have h1' :
                      cfg1 ∈ checkedEvalRunLoopMachine.runBranches m1
                        [({ state := .need .clause needExprCompositeMachine.initial,
                            tape :=
                              evalCursorStackEndTape witness (consumed + 3)
                                rest (encodeEvalFrames (.orLeft :: frames))
                                padLeft } : CheckedConfig)] := by
                    simpa [hrestEq] using h1
                  have hAll :=
                    mem_runBranches_trans checkedEvalRunLoopMachine
                      m0 m1
                      [{ state := .need mode needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumed
                             (true :: false :: true :: rest)
                             (encodeEvalFrames frames) padding }]
                      ({ state := .need .clause needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness (consumed + 3)
                             rest (encodeEvalFrames (.orLeft :: frames))
                             padLeft } : CheckedConfig)
                      cfg1 h0' h1'
                  have hsum :
                      m0 + m1 ≤
                        checkedLoopStepEnvelope n +
                          checkedCircuitBudget a n :=
                    Nat.add_le_add hm0 hm1
                  have hcap :=
                    binary_left_semantic_reject_le a rest'.length n
                  refine ⟨m0 + m1, Nat.le_trans hsum ?_,
                    cfg1, hAll, hrej1⟩
                  simpa [hrestEq, List.length_append, Nat.add_assoc] using hcap

              | true =>
                  obtain ⟨m1, hm1, cfg1, h1, hout1⟩ :=
                    exact_bounded_all sigma witness a .clause
                      hcheck rest' (.orLeft :: frames)
                      (consumed + 3) padLeft n hLayoutA hvar hread
                  let consumedA :=
                    (consumed + 3) + (encodeCircuit a).length
                  have hout1' :
                      ∃ padding1,
                        cfg1 =
                          { state := .have (exitMode .clause a)
                              (.start (evalCircuit sigma a)),
                            tape :=
                              evalCursorStackEndTape witness consumedA rest'
                                (encodeEvalFrames (.orLeft :: frames))
                                padding1 } := by
                    simpa [ExactCheckedLoopOutcome, consumedA] using hout1
                  rcases hout1' with ⟨padding1, hcfg1⟩
                  subst cfg1
                  have h1' :
                      ({ state := .have (exitMode .clause a)
                           (.start (evalCircuit sigma a)),
                         tape :=
                           evalCursorStackEndTape witness consumedA rest'
                             (encodeEvalFrames (.orLeft :: frames))
                             padding1 } : CheckedConfig) ∈
                        checkedEvalRunLoopMachine.runBranches m1
                          [({ state := .need .clause needExprCompositeMachine.initial,
                              tape :=
                                evalCursorStackEndTape witness (consumed + 3)
                                  rest (encodeEvalFrames (.orLeft :: frames))
                                  padLeft } : CheckedConfig)] := by
                    simpa [hrestEq, consumedA] using h1
                  obtain ⟨m2, hm2, h2⟩ :=
                    orLeftReturn_checked_reaches_need_within_envelope
                      n (exitMode .clause a) witness rest'
                      (encodeEvalFrames frames) consumedA padding1
                      (evalCircuit sigma a)
                  let padRight := ((((padding1 + 3) - 1) - 1) - 1)
                  have hLayoutAfterA :
                      CheckedLayoutBound n consumedA rest'
                        (encodeEvalFrames (.orLeft :: frames)) := by
                    simpa [consumedA] using
                      after_circuit n (consumed + 3) a rest'
                        (encodeEvalFrames (.orLeft :: frames)) hLayoutA
                  have hLayoutRight :
                      CheckedLayoutBound n consumedA rest'
                        (encodeEvalFrames
                          (.orRight (evalCircuit sigma a) :: frames)) := by
                    simpa [encodeEvalFrames, List.append_assoc] using
                      replace_top_frame n consumedA rest'
                        (encodeEvalFrames frames) .orLeft
                        (.orRight (evalCircuit sigma a)) hLayoutAfterA
                  have hrestFuel : rest'.length < fuel := by
                    have hf := hlt
                    simp [hrestEq, List.length_append] at hf
                    omega
                  obtain ⟨m3, hm3, cfg3, h3, hrej3⟩ :=
                    ih rest' .clause witness
                      (.orRight (evalCircuit sigma a) :: frames)
                      consumedA padRight n
                      hrestFuel hwit hLayoutRight hrightFail
                  have h2' :
                      ({ state := .need .clause needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumedA rest'
                             (encodeEvalFrames
                               (.orRight (evalCircuit sigma a) :: frames))
                             padRight } : CheckedConfig) ∈
                        checkedEvalRunLoopMachine.runBranches m2
                          [({ state := .have (exitMode .clause a)
                               (.start (evalCircuit sigma a)),
                              tape :=
                                evalCursorStackEndTape witness consumedA rest'
                                  (encodeEvalFrames (.orLeft :: frames))
                                  padding1 } : CheckedConfig)] := by
                    simpa [padRight, encodeEvalFrames, List.append_assoc] using h2
                  have h01 :=
                    mem_runBranches_trans checkedEvalRunLoopMachine
                      m0 m1
                      [{ state := .need mode needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumed
                             (true :: false :: true :: rest)
                             (encodeEvalFrames frames) padding }]
                      ({ state := .need .clause needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness (consumed + 3)
                             rest (encodeEvalFrames (.orLeft :: frames))
                             padLeft } : CheckedConfig)
                      ({ state := .have (exitMode .clause a)
                           (.start (evalCircuit sigma a)),
                         tape :=
                           evalCursorStackEndTape witness consumedA rest'
                             (encodeEvalFrames (.orLeft :: frames))
                             padding1 } : CheckedConfig)
                      h0' h1'
                  have h012 :=
                    mem_runBranches_trans checkedEvalRunLoopMachine
                      (m0 + m1) m2
                      [{ state := .need mode needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumed
                             (true :: false :: true :: rest)
                             (encodeEvalFrames frames) padding }]
                      ({ state := .have (exitMode .clause a)
                           (.start (evalCircuit sigma a)),
                         tape :=
                           evalCursorStackEndTape witness consumedA rest'
                             (encodeEvalFrames (.orLeft :: frames))
                             padding1 } : CheckedConfig)
                      ({ state := .need .clause needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumedA rest'
                             (encodeEvalFrames
                               (.orRight (evalCircuit sigma a) :: frames))
                             padRight } : CheckedConfig)
                      h01 h2'
                  have hAll :=
                    mem_runBranches_trans checkedEvalRunLoopMachine
                      (m0 + m1 + m2) m3
                      [{ state := .need mode needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumed
                             (true :: false :: true :: rest)
                             (encodeEvalFrames frames) padding }]
                      ({ state := .need .clause needExprCompositeMachine.initial,
                         tape :=
                           evalCursorStackEndTape witness consumedA rest'
                             (encodeEvalFrames
                               (.orRight (evalCircuit sigma a) :: frames))
                             padRight } : CheckedConfig)
                      cfg3 h012 h3
                  have hsum :
                      m0 + m1 + m2 + m3 ≤
                        checkedLoopStepEnvelope n +
                          checkedCircuitBudget a n +
                          checkedLoopStepEnvelope n +
                          coreRejectPotential rest'.length n := by
                    omega
                  have hcap :=
                    binary_right_path_le a rest'.length n
                  refine ⟨m0 + m1 + m2 + m3,
                    Nat.le_trans hsum ?_, cfg3, hAll, hrej3⟩
                  simpa [hrestEq, List.length_append, Nat.add_assoc] using hcap

      · rcases hinvalid with ⟨third, rest, rfl⟩
        obtain ⟨m, hm, hrun⟩ :=
          invalid_tag_rejects_material
            n mode witness rest (encodeEvalFrames frames)
            consumed padding third hLayout.source_le hLayout.frames_le
        refine ⟨m, Nat.le_trans hm ?_,
          { state := .reject,
            tape := evalCursorReadTape witness (consumed + 3)
              rest (encodeEvalFrames frames) padding },
          hrun, rfl⟩
        exact Nat.le_trans
          (P01CoreDecodeFailureAtoms.checkedLoopStepEnvelope_le_material n)
          (by
            have hp := loop_le_potential
              (true :: true :: third :: rest).length n
            exact Nat.le_trans
              (P01CoreDecodeFailureAtoms.checkedLoopStepEnvelope_le_material n)
              (Nat.le_trans (material_le_terminal n)
                (by
                  unfold terminalVerifierTimeBound coreRejectPotential
                  checkedLoopStepEnvelope
                  exact Nat.mul_le_mul_right ((n + 1)^3) (by omega))))

/-- The exact remaining malformed-core contract is now inhabited. -/
theorem coreDecodeFailurePhysicalReject :
    CoreDecodeFailurePhysicalReject := by
  intro witness bs hw hcore
  have hLayout : CheckedLayoutBound bs.length 0 bs [] :=
    CheckedLayoutBound.root bs
  obtain ⟨m, hm, cfg, hrun, hrej⟩ :=
    coreDecodeFailurePhysicalAux
      (bs.length + 1) bs .cnf witness [] 0 0 bs.length
      (by omega) (by omega) (by simpa using hLayout) hcore
  refine ⟨m, Nat.le_trans hm ?_, cfg, hrun, hrej⟩
  exact root_potential_le_material bs.length bs.length (Nat.le_refl _)

/-- Consequently the P01 construction gap is inhabited with no remaining
machine-level premise. -/
theorem p01ConstructionGap :
    P01FinalCertificate.P01ConstructionGap :=
  P01RawVerifierFromCoreReject.p01_of_core_decode_failure_physical_reject
    coreDecodeFailurePhysicalReject

#print axioms MCore.Real.P01CoreDecodeFailurePhysical.coreDecodeFailurePhysicalAux
#print axioms MCore.Real.P01CoreDecodeFailurePhysical.coreDecodeFailurePhysicalReject
#print axioms MCore.Real.P01CoreDecodeFailurePhysical.p01ConstructionGap

end P01CoreDecodeFailurePhysical
end Real
end MCore
