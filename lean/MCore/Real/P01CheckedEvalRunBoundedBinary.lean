import MCore.Real.P01CheckedEvalRunBoundedCertificate

namespace MCore
namespace Real
namespace P01CheckedEvalRunBoundedBinary

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATWitness
open P01EncodedStackEvaluator
open P01EncodedFrameTape
open P01EvalCursorMachine
open P01NeedExprCompositeNTM
open P01CheckedEvalRunLoopNTM
open P01CheckedEvalRunBaseCases
open P01CheckedEvalRunNeedTags
open P01CheckedEvalRunHaveValue
open P01CheckedEvalRunBoundedHelpers
open P01CheckedEvalRunBoundedCertificate
open P01CheckedEvalBoundedOutcome
open P01CheckedVerifierInvariant
open P01CheckedVerifierGlobalBudget
open P01NTMRunLaws
open P01CNFMode

abbrev CheckedConfig :=
  Configuration CheckedEvalRunState (Option Bool)

private theorem and_budget
    (left right : CircuitK1.Circuit) (n : Nat) :
    checkedCircuitBudget left n +
        checkedCircuitBudget right n +
        4 * checkedLoopStepEnvelope n ≤
      checkedCircuitBudget (.and left right) n := by
  have hcoef :
      8 * (evalStepCount left + 1) +
          8 * (evalStepCount right + 1) + 4 ≤
        8 * (evalStepCount (.and left right) + 1) := by
    simp [evalStepCount]
    omega
  have hmul :=
    Nat.mul_le_mul_right (checkedLoopStepEnvelope n) hcoef
  simpa [checkedCircuitBudget, Nat.add_mul, Nat.add_assoc] using hmul

private theorem or_budget
    (left right : CircuitK1.Circuit) (n : Nat) :
    checkedCircuitBudget left n +
        checkedCircuitBudget right n +
        4 * checkedLoopStepEnvelope n ≤
      checkedCircuitBudget (.or left right) n := by
  have hcoef :
      8 * (evalStepCount left + 1) +
          8 * (evalStepCount right + 1) + 4 ≤
        8 * (evalStepCount (.or left right) + 1) := by
    simp [evalStepCount]
    omega
  have hmul :=
    Nat.mul_le_mul_right (checkedLoopStepEnvelope n) hcoef
  simpa [checkedCircuitBudget, Nat.add_mul, Nat.add_assoc] using hmul

/-- Bounded physical conjunction.  The strengthened child certificate carries
the layout invariant across the left child, the left-frame handoff, the right
child, and the final frame pop. -/
theorem and_bounded_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (left right : CircuitK1.Circuit)
    (hleft :
      BoundedCheckedCircuitRunCertificate sigma witness .cnf left)
    (hright :
      BoundedCheckedCircuitRunCertificate sigma witness .cnf right) :
    BoundedCheckedCircuitRunCertificate
      sigma witness mode (.and left right) := by
  intro hmode tail frames consumed padding n hLayout hlen hread
  cases mode with
  | clause =>
      rw [modeCheck_and] at hmode
      simp [tagAllowed] at hmode
  | mustInput =>
      rw [modeCheck_and] at hmode
      simp [tagAllowed] at hmode
  | cnf =>
      have hchildren :
          modeCheck .cnf left = true ∧
            modeCheck .cnf right = true := by
        have h := hmode
        rw [modeCheck_and] at h
        simpa [tagAllowed] using h
      have hleftMode := hchildren.1
      have hrightMode := hchildren.2

      have hlenMax :
          max (varBound left) (varBound right) ≤ witness.length := by
        simpa [varBound] using hlen
      have hlenLeft : varBound left ≤ witness.length :=
        Nat.le_trans (Nat.le_max_left _ _) hlenMax
      have hlenRight : varBound right ≤ witness.length :=
        Nat.le_trans (Nat.le_max_right _ _) hlenMax
      have hreadLeft :
          ∀ i, i < varBound left →
            witness.getD i false = sigma i := by
        intro i hi
        exact hread i (by
          simpa [varBound] using
            Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _))
      have hreadRight :
          ∀ i, i < varBound right →
            witness.getD i false = sigma i := by
        intro i hi
        exact hread i (by
          simpa [varBound] using
            Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _))

      have hLayoutTag :
          CheckedLayoutBound n consumed
            (true :: false :: false ::
              (encodeCircuit left ++ encodeCircuit right ++ tail))
            (encodeEvalFrames frames) := by
        simpa [encodeCircuit, List.append_assoc] using hLayout

      have hLayoutLeftRaw :=
        P01CheckedVerifierInvariant.after_push_tag
          n consumed true false false
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames frames) .andLeft hLayoutTag
      have hLayoutLeft :
          CheckedLayoutBound n (consumed + 3)
            (encodeCircuit left ++ (encodeCircuit right ++ tail))
            (encodeEvalFrames (.andLeft :: frames)) := by
        simpa [encodeEvalFrames, List.append_assoc] using hLayoutLeftRaw

      have hsource :
          (true :: false :: false ::
            (encodeCircuit left ++ encodeCircuit right ++ tail)).length ≤ n :=
        hLayoutTag.source_le
      have hframes : (encodeEvalFrames frames).length ≤ n :=
        hLayoutTag.frames_le

      obtain ⟨m0, hm0, h0⟩ :=
        pushTag_checked_reaches_need_within_envelope
          n .cnf witness
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames frames) consumed padding
          true false false .and .andLeft
          (by rfl) (by rfl)
          (by simp [P01CheckedEvalRunTagPrefix.postTagState, childMode])
          hsource hframes

      let padLeft := ((padding - 1) - 1) - 1
      let cNeedLeft : CheckedConfig :=
        { state := .need .cnf needExprCompositeMachine.initial,
          tape :=
            evalCursorStackEndTape witness (consumed + 3)
              (encodeCircuit left ++ encodeCircuit right ++ tail)
              (encodeEvalFrames (.andLeft :: frames)) padLeft }

      have h0' :
          cNeedLeft ∈
            checkedEvalRunLoopMachine.runBranches m0
              [{ state := .need .cnf needExprCompositeMachine.initial,
                 tape :=
                   evalCursorStackEndTape witness consumed
                     (encodeCircuit (.and left right) ++ tail)
                     (encodeEvalFrames frames) padding }] := by
        simpa [cNeedLeft, padLeft, encodeCircuit,
          encodeEvalFrames, List.append_assoc] using h0

      obtain ⟨m1, hm1, cfgLeft, h1, hout1⟩ :=
        hleft hleftMode
          (encodeCircuit right ++ tail) (.andLeft :: frames)
          (consumed + 3) padLeft n hLayoutLeft hlenLeft hreadLeft

      have h1' :
          cfgLeft ∈
            checkedEvalRunLoopMachine.runBranches m1 [cNeedLeft] := by
        simpa [cNeedLeft, encodeEvalFrames, List.append_assoc] using h1

      have h01 :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          m0 m1
          [{ state := .need .cnf needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.and left right) ++ tail)
                 (encodeEvalFrames frames) padding }]
          cNeedLeft cfgLeft h0' h1'

      have hRightTail : encodeCircuit right ++ tail ≠ [] := by
        intro hnil
        have henc : encodeCircuit right = [] :=
          (List.append_eq_nil_iff.mp hnil).1
        exact P01EvalRunCircuitCertificate.encodeCircuit_ne_nil right henc

      obtain ⟨consumed1, padding1, hcfgLeft, hLayoutAfterLeft⟩ :=
        layout_of_tail_ne_nil hout1 hRightTail
      subst cfgLeft

      obtain ⟨m2, hm2, h2⟩ :=
        andLeftReturn_checked_reaches_need
          (exitMode .cnf left)
          witness (encodeCircuit right ++ tail)
          (encodeEvalFrames frames)
          consumed1 padding1 (evalCircuit sigma left)

      let padRight := (((padding1 + 3) - 1) - 1) - 1
      let cNeedRight : CheckedConfig :=
        { state := .need .cnf needExprCompositeMachine.initial,
          tape :=
            evalCursorStackEndTape witness consumed1
              (encodeCircuit right ++ tail)
              (encodeEvalFrames
                (.andRight (evalCircuit sigma left) :: frames))
              padRight }

      have h2' :
          cNeedRight ∈
            checkedEvalRunLoopMachine.runBranches m2
              [{ state := .have (exitMode .cnf left)
                   (.start (evalCircuit sigma left)),
                 tape :=
                   evalCursorStackEndTape witness consumed1
                     (encodeCircuit right ++ tail)
                     (encodeEvalFrames (.andLeft :: frames))
                     padding1 }] := by
        simpa [cNeedRight, padRight, encodeEvalFrames,
          List.append_assoc] using h2

      have hLayoutLeftFrame :
          CheckedLayoutBound n consumed1
            (encodeCircuit right ++ tail)
            (encodeEvalFrame .andLeft ++ encodeEvalFrames frames) := by
        simpa [encodeEvalFrames, List.append_assoc] using hLayoutAfterLeft
      have hLayoutRightFrame :=
        P01CheckedVerifierInvariant.replace_top_frame_exact
          n consumed1 (encodeCircuit right ++ tail)
          (encodeEvalFrames frames) .andLeft
          (.andRight (evalCircuit sigma left)) hLayoutLeftFrame
      have hLayoutRight :
          CheckedLayoutBound n consumed1
            (encodeCircuit right ++ tail)
            (encodeEvalFrames
              (.andRight (evalCircuit sigma left) :: frames)) := by
        simpa [encodeEvalFrames, List.append_assoc] using hLayoutRightFrame

      have h012 :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          (m0 + m1) m2
          [{ state := .need .cnf needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.and left right) ++ tail)
                 (encodeEvalFrames frames) padding }]
          ({ state := .have (exitMode .cnf left)
               (.start (evalCircuit sigma left)),
             tape :=
               evalCursorStackEndTape witness consumed1
                 (encodeCircuit right ++ tail)
                 (encodeEvalFrames (.andLeft :: frames))
                 padding1 } : CheckedConfig)
          cNeedRight h01 h2'

      obtain ⟨m3, hm3, cfgRight, h3, hout3⟩ :=
        hright hrightMode tail
          (.andRight (evalCircuit sigma left) :: frames)
          consumed1 padRight n hLayoutRight hlenRight hreadRight

      have h3' :
          cfgRight ∈
            checkedEvalRunLoopMachine.runBranches m3 [cNeedRight] := by
        simpa [cNeedRight, encodeEvalFrames, List.append_assoc] using h3

      have h0123 :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          (m0 + m1 + m2) m3
          [{ state := .need .cnf needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.and left right) ++ tail)
                 (encodeEvalFrames frames) padding }]
          cNeedRight cfgRight h012 h3'

      obtain ⟨consumed2, padding2, hcfgRight, hLayoutAfterRight⟩ :=
        layout_of_frames_ne_nil hout3 (by simp)
      subst cfgRight

      obtain ⟨m4, hm4, h4⟩ :=
        andRightReturn_checked_reaches_have
          (exitMode .cnf right)
          witness tail (encodeEvalFrames frames)
          consumed2 padding2
          (evalCircuit sigma left) (evalCircuit sigma right)

      let finalValue :=
        Bool.and (evalCircuit sigma left) (evalCircuit sigma right)
      let cHave : CheckedConfig :=
        { state := .have .cnf (.start finalValue),
          tape :=
            evalCursorStackEndTape witness consumed2 tail
              (encodeEvalFrames frames) (padding2 + 3) }

      have h4' :
          cHave ∈
            checkedEvalRunLoopMachine.runBranches m4
              [{ state := .have (exitMode .cnf right)
                   (.start (evalCircuit sigma right)),
                 tape :=
                   evalCursorStackEndTape witness consumed2 tail
                     (encodeEvalFrames
                       (.andRight (evalCircuit sigma left) :: frames))
                     padding2 }] := by
        simpa [cHave, finalValue, encodeEvalFrames,
          List.append_assoc] using h4

      have hLayoutRightFrame' :
          CheckedLayoutBound n consumed2 tail
            (encodeEvalFrame (.andRight (evalCircuit sigma left)) ++
              encodeEvalFrames frames) := by
        simpa [encodeEvalFrames, List.append_assoc] using hLayoutAfterRight
      have hLayoutHave :=
        P01CheckedVerifierInvariant.pop_frame
          n consumed2 tail (encodeEvalFrames frames)
          (.andRight (evalCircuit sigma left)) hLayoutRightFrame'

      have h01234 :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          (m0 + m1 + m2 + m3) m4
          [{ state := .need .cnf needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.and left right) ++ tail)
                 (encodeEvalFrames frames) padding }]
          ({ state := .have (exitMode .cnf right)
               (.start (evalCircuit sigma right)),
             tape :=
               evalCursorStackEndTape witness consumed2 tail
                 (encodeEvalFrames
                   (.andRight (evalCircuit sigma left) :: frames))
                 padding2 } : CheckedConfig)
          cHave h0123 h4'

      obtain ⟨m5, hm5, cfgFinal, h5, hout5⟩ :=
        have_reaches_bounded_outcome
          n .cnf witness finalValue tail frames
          consumed2 (padding2 + 3) hLayoutHave

      have hAll :=
        mem_runBranches_trans checkedEvalRunLoopMachine
          (m0 + m1 + m2 + m3 + m4) m5
          [{ state := .need .cnf needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.and left right) ++ tail)
                 (encodeEvalFrames frames) padding }]
          cHave cfgFinal h01234 h5

      have hm2L : m2 ≤ checkedLoopStepEnvelope n :=
        Nat.le_trans hm2 (thirteen_le_stepEnvelope n)
      have hm4L : m4 ≤ checkedLoopStepEnvelope n :=
        Nat.le_trans hm4 (nine_le_stepEnvelope n)
      have hside :
          m0 + m2 + m4 + m5 ≤ 4 * checkedLoopStepEnvelope n := by
        omega
      have hchildren :
          m1 + m3 ≤
            checkedCircuitBudget left n + checkedCircuitBudget right n :=
        Nat.add_le_add hm1 hm3
      have hpre :
          m0 + m1 + m2 + m3 + m4 + m5 ≤
            checkedCircuitBudget left n +
              checkedCircuitBudget right n +
              4 * checkedLoopStepEnvelope n := by
        calc
          m0 + m1 + m2 + m3 + m4 + m5
              = (m1 + m3) + (m0 + m2 + m4 + m5) := by omega
          _ ≤ (checkedCircuitBudget left n +
                checkedCircuitBudget right n) +
                4 * checkedLoopStepEnvelope n :=
            Nat.add_le_add hchildren hside
      have htotal :
          m0 + m1 + m2 + m3 + m4 + m5 ≤
            checkedCircuitBudget (.and left right) n :=
        Nat.le_trans hpre (and_budget left right n)

      refine ⟨m0 + m1 + m2 + m3 + m4 + m5,
        htotal, cfgFinal, hAll, ?_⟩
      simpa [finalValue, exitMode, childMode,
        circuitTag, evalCircuit] using hout5

/-- Bounded physical disjunction. -/
theorem or_bounded_certificate
    (sigma : Assignment)
    (witness : BitString)
    (mode : SyntaxMode)
    (left right : CircuitK1.Circuit)
    (hleft :
      BoundedCheckedCircuitRunCertificate sigma witness .clause left)
    (hright :
      BoundedCheckedCircuitRunCertificate sigma witness .clause right) :
    BoundedCheckedCircuitRunCertificate
      sigma witness mode (.or left right) := by
  intro hmode tail frames consumed padding n hLayout hlen hread

  have hparts :
      (tagAllowed mode .or = true ∧ modeCheck .clause left = true) ∧
        modeCheck .clause right = true := by
    have h := hmode
    rw [modeCheck_or] at h
    simpa using h
  have hAllowed : tagAllowed mode .or = true := hparts.1.1
  have hleftMode : modeCheck .clause left = true := hparts.1.2
  have hrightMode : modeCheck .clause right = true := hparts.2

  have hlenMax :
      max (varBound left) (varBound right) ≤ witness.length := by
    simpa [varBound] using hlen
  have hlenLeft : varBound left ≤ witness.length :=
    Nat.le_trans (Nat.le_max_left _ _) hlenMax
  have hlenRight : varBound right ≤ witness.length :=
    Nat.le_trans (Nat.le_max_right _ _) hlenMax

  have hreadLeft :
      ∀ i, i < varBound left →
        witness.getD i false = sigma i := by
    intro i hi
    exact hread i (by
      simpa [varBound] using
        Nat.lt_of_lt_of_le hi (Nat.le_max_left _ _))
  have hreadRight :
      ∀ i, i < varBound right →
        witness.getD i false = sigma i := by
    intro i hi
    exact hread i (by
      simpa [varBound] using
        Nat.lt_of_lt_of_le hi (Nat.le_max_right _ _))

  have hLayoutTag :
      CheckedLayoutBound n consumed
        (true :: false :: true ::
          (encodeCircuit left ++ encodeCircuit right ++ tail))
        (encodeEvalFrames frames) := by
    simpa [encodeCircuit, List.append_assoc] using hLayout

  have hLayoutLeftRaw :=
    P01CheckedVerifierInvariant.after_push_tag
      n consumed true false true
      (encodeCircuit left ++ encodeCircuit right ++ tail)
      (encodeEvalFrames frames) .orLeft hLayoutTag
  have hLayoutLeft :
      CheckedLayoutBound n (consumed + 3)
        (encodeCircuit left ++ (encodeCircuit right ++ tail))
        (encodeEvalFrames (.orLeft :: frames)) := by
    simpa [encodeEvalFrames, List.append_assoc] using hLayoutLeftRaw

  have hsource :
      (true :: false :: true ::
        (encodeCircuit left ++ encodeCircuit right ++ tail)).length ≤ n :=
    hLayoutTag.source_le
  have hframes : (encodeEvalFrames frames).length ≤ n :=
    hLayoutTag.frames_le

  obtain ⟨m0, hm0, h0⟩ :=
    pushTag_checked_reaches_need_within_envelope
      n mode witness
      (encodeCircuit left ++ encodeCircuit right ++ tail)
      (encodeEvalFrames frames) consumed padding
      true false true .or .orLeft
      (by rfl) hAllowed
      (by simp [P01CheckedEvalRunTagPrefix.postTagState, childMode])
      hsource hframes

  let padLeft := ((padding - 1) - 1) - 1
  let cNeedLeft : CheckedConfig :=
    { state := .need .clause needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness (consumed + 3)
          (encodeCircuit left ++ encodeCircuit right ++ tail)
          (encodeEvalFrames (.orLeft :: frames)) padLeft }

  have h0' :
      cNeedLeft ∈
        checkedEvalRunLoopMachine.runBranches m0
          [{ state := .need mode needExprCompositeMachine.initial,
             tape :=
               evalCursorStackEndTape witness consumed
                 (encodeCircuit (.or left right) ++ tail)
                 (encodeEvalFrames frames) padding }] := by
    simpa [cNeedLeft, padLeft, encodeCircuit,
      encodeEvalFrames, List.append_assoc] using h0

  obtain ⟨m1, hm1, cfgLeft, h1, hout1⟩ :=
    hleft hleftMode
      (encodeCircuit right ++ tail) (.orLeft :: frames)
      (consumed + 3) padLeft n hLayoutLeft hlenLeft hreadLeft

  have h1' :
      cfgLeft ∈
        checkedEvalRunLoopMachine.runBranches m1 [cNeedLeft] := by
    simpa [cNeedLeft, encodeEvalFrames, List.append_assoc] using h1

  have h01 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      m0 m1
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.or left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      cNeedLeft cfgLeft h0' h1'

  have hRightTail : encodeCircuit right ++ tail ≠ [] := by
    intro hnil
    have henc : encodeCircuit right = [] :=
      (List.append_eq_nil_iff.mp hnil).1
    exact P01EvalRunCircuitCertificate.encodeCircuit_ne_nil right henc

  obtain ⟨consumed1, padding1, hcfgLeft, hLayoutAfterLeft⟩ :=
    layout_of_tail_ne_nil hout1 hRightTail
  subst cfgLeft

  obtain ⟨m2, hm2, h2⟩ :=
    orLeftReturn_checked_reaches_need
      (exitMode .clause left)
      witness (encodeCircuit right ++ tail)
      (encodeEvalFrames frames)
      consumed1 padding1 (evalCircuit sigma left)

  let padRight := (((padding1 + 3) - 1) - 1) - 1
  let cNeedRight : CheckedConfig :=
    { state := .need .clause needExprCompositeMachine.initial,
      tape :=
        evalCursorStackEndTape witness consumed1
          (encodeCircuit right ++ tail)
          (encodeEvalFrames
            (.orRight (evalCircuit sigma left) :: frames))
          padRight }

  have h2' :
      cNeedRight ∈
        checkedEvalRunLoopMachine.runBranches m2
          [{ state := .have (exitMode .clause left)
               (.start (evalCircuit sigma left)),
             tape :=
               evalCursorStackEndTape witness consumed1
                 (encodeCircuit right ++ tail)
                 (encodeEvalFrames (.orLeft :: frames))
                 padding1 }] := by
    simpa [cNeedRight, padRight, encodeEvalFrames,
      List.append_assoc] using h2

  have hLayoutLeftFrame :
      CheckedLayoutBound n consumed1
        (encodeCircuit right ++ tail)
        (encodeEvalFrame .orLeft ++ encodeEvalFrames frames) := by
    simpa [encodeEvalFrames, List.append_assoc] using hLayoutAfterLeft
  have hLayoutRightFrame :=
    P01CheckedVerifierInvariant.replace_top_frame_exact
      n consumed1 (encodeCircuit right ++ tail)
      (encodeEvalFrames frames) .orLeft
      (.orRight (evalCircuit sigma left)) hLayoutLeftFrame
  have hLayoutRight :
      CheckedLayoutBound n consumed1
        (encodeCircuit right ++ tail)
        (encodeEvalFrames
          (.orRight (evalCircuit sigma left) :: frames)) := by
    simpa [encodeEvalFrames, List.append_assoc] using hLayoutRightFrame

  have h012 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + m1) m2
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.or left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      ({ state := .have (exitMode .clause left)
           (.start (evalCircuit sigma left)),
         tape :=
           evalCursorStackEndTape witness consumed1
             (encodeCircuit right ++ tail)
             (encodeEvalFrames (.orLeft :: frames))
             padding1 } : CheckedConfig)
      cNeedRight h01 h2'

  obtain ⟨m3, hm3, cfgRight, h3, hout3⟩ :=
    hright hrightMode tail
      (.orRight (evalCircuit sigma left) :: frames)
      consumed1 padRight n hLayoutRight hlenRight hreadRight

  have h3' :
      cfgRight ∈
        checkedEvalRunLoopMachine.runBranches m3 [cNeedRight] := by
    simpa [cNeedRight, encodeEvalFrames, List.append_assoc] using h3

  have h0123 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + m1 + m2) m3
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.or left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      cNeedRight cfgRight h012 h3'

  obtain ⟨consumed2, padding2, hcfgRight, hLayoutAfterRight⟩ :=
    layout_of_frames_ne_nil hout3 (by simp)
  subst cfgRight

  obtain ⟨m4, hm4, h4⟩ :=
    orRightReturn_checked_reaches_have
      (exitMode .clause right)
      witness tail (encodeEvalFrames frames)
      consumed2 padding2
      (evalCircuit sigma left) (evalCircuit sigma right)

  let finalValue :=
    Bool.or (evalCircuit sigma left) (evalCircuit sigma right)
  let cHave : CheckedConfig :=
    { state := .have .clause (.start finalValue),
      tape :=
        evalCursorStackEndTape witness consumed2 tail
          (encodeEvalFrames frames) (padding2 + 3) }

  have h4' :
      cHave ∈
        checkedEvalRunLoopMachine.runBranches m4
          [{ state := .have (exitMode .clause right)
               (.start (evalCircuit sigma right)),
             tape :=
               evalCursorStackEndTape witness consumed2 tail
                 (encodeEvalFrames
                   (.orRight (evalCircuit sigma left) :: frames))
                 padding2 }] := by
    simpa [cHave, finalValue, encodeEvalFrames,
      List.append_assoc] using h4

  have hLayoutRightFrame' :
      CheckedLayoutBound n consumed2 tail
        (encodeEvalFrame (.orRight (evalCircuit sigma left)) ++
          encodeEvalFrames frames) := by
    simpa [encodeEvalFrames, List.append_assoc] using hLayoutAfterRight
  have hLayoutHave :=
    P01CheckedVerifierInvariant.pop_frame
      n consumed2 tail (encodeEvalFrames frames)
      (.orRight (evalCircuit sigma left)) hLayoutRightFrame'

  have h01234 :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + m1 + m2 + m3) m4
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.or left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      ({ state := .have (exitMode .clause right)
           (.start (evalCircuit sigma right)),
         tape :=
           evalCursorStackEndTape witness consumed2 tail
             (encodeEvalFrames
               (.orRight (evalCircuit sigma left) :: frames))
             padding2 } : CheckedConfig)
      cHave h0123 h4'

  obtain ⟨m5, hm5, cfgFinal, h5, hout5⟩ :=
    have_reaches_bounded_outcome
      n .clause witness finalValue tail frames
      consumed2 (padding2 + 3) hLayoutHave

  have hAll :=
    mem_runBranches_trans checkedEvalRunLoopMachine
      (m0 + m1 + m2 + m3 + m4) m5
      [{ state := .need mode needExprCompositeMachine.initial,
         tape :=
           evalCursorStackEndTape witness consumed
             (encodeCircuit (.or left right) ++ tail)
             (encodeEvalFrames frames) padding }]
      cHave cfgFinal h01234 h5

  have hm2L : m2 ≤ checkedLoopStepEnvelope n :=
    Nat.le_trans hm2 (thirteen_le_stepEnvelope n)
  have hm4L : m4 ≤ checkedLoopStepEnvelope n :=
    Nat.le_trans hm4 (nine_le_stepEnvelope n)
  have hside :
      m0 + m2 + m4 + m5 ≤ 4 * checkedLoopStepEnvelope n := by
    omega
  have hchildren :
      m1 + m3 ≤
        checkedCircuitBudget left n + checkedCircuitBudget right n :=
    Nat.add_le_add hm1 hm3
  have hpre :
      m0 + m1 + m2 + m3 + m4 + m5 ≤
        checkedCircuitBudget left n +
          checkedCircuitBudget right n +
          4 * checkedLoopStepEnvelope n := by
    calc
      m0 + m1 + m2 + m3 + m4 + m5
          = (m1 + m3) + (m0 + m2 + m4 + m5) := by omega
      _ ≤ (checkedCircuitBudget left n +
            checkedCircuitBudget right n) +
            4 * checkedLoopStepEnvelope n :=
        Nat.add_le_add hchildren hside
  have htotal :
      m0 + m1 + m2 + m3 + m4 + m5 ≤
        checkedCircuitBudget (.or left right) n :=
    Nat.le_trans hpre (or_budget left right n)

  refine ⟨m0 + m1 + m2 + m3 + m4 + m5,
    htotal, cfgFinal, hAll, ?_⟩
  simpa [finalValue, exitMode, childMode,
    circuitTag, evalCircuit] using hout5

/-- Every semantically valid checked circuit has one bounded physical
certificate carrying enough layout information for recursive composition. -/
theorem circuit_bounded_certificate
    (sigma : Assignment)
    (witness : BitString) :
    ∀ (phi : CircuitK1.Circuit) (mode : SyntaxMode),
      BoundedCheckedCircuitRunCertificate sigma witness mode phi := by
  intro phi
  induction phi with
  | input i =>
      intro mode
      exact input_bounded_certificate sigma witness mode i
  | const v =>
      intro mode
      exact const_bounded_certificate sigma witness mode v
  | not c ih =>
      intro mode
      exact neg_bounded_certificate
        sigma witness mode c (ih (childMode mode .neg))
  | and left right ihLeft ihRight =>
      intro mode
      exact and_bounded_certificate
        sigma witness mode left right
        (ihLeft .cnf) (ihRight .cnf)
  | or left right ihLeft ihRight =>
      intro mode
      exact or_bounded_certificate
        sigma witness mode left right
        (ihLeft .clause) (ihRight .clause)

#print axioms MCore.Real.P01CheckedEvalRunBoundedBinary.and_bounded_certificate
#print axioms MCore.Real.P01CheckedEvalRunBoundedBinary.or_bounded_certificate
#print axioms MCore.Real.P01CheckedEvalRunBoundedBinary.circuit_bounded_certificate

end P01CheckedEvalRunBoundedBinary
end Real
end MCore
