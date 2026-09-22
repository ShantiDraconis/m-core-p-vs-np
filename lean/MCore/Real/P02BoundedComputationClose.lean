import MCore.Real.P02BoundedComputationSoundness
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P02BoundedComputationClose

open CircuitK1
open CanonicalFinalProof
open P02BoundedComputationEncoding
open P02BoundedComputationSoundness
open P02BoundedComputationLogic

structure TransitionSoundnessCertificate where
  step :
    ∀ (sigma : Assignment) (M : PolyDTMCandidate) (x : BitString)
      (t s : Nat), s < t →
      evalCNF sigma (boundedExecTableauCNF M x t) = true →
      SnapshotMatches sigma M x t s
        (M.machine.run s (initialTMConfig M.machine x)) →
      SnapshotMatches sigma M x t (s + 1)
        (M.machine.run (s + 1) (initialTMConfig M.machine x))

structure TableauCompletenessCertificate where
  assignment :
    ∀ (M : PolyDTMCandidate) (x : BitString) (t : Nat),
      AcceptsAtFuel M x t → Assignment
  satisfies :
    ∀ (M : PolyDTMCandidate) (x : BitString) (t : Nat)
      (hacc : AcceptsAtFuel M x t),
      evalCNF (assignment M x t hacc)
        (boundedExecTableauCNF M x t) = true



/-! Variable-family range separation for the concrete tableau assignment. -/

theorem stateVar_lt_headBase_valid
    (M : PolyDTMCandidate) (t s : Nat)
    (q : Fin (M.stateCount + 1))
    (hs : s ≤ t) :
    stateVar M t s q < headBase M t := by
  let n := stateCount M
  have hn : 0 < n := by
    simp [n, stateCount]
  have hq : q.val < n := by
    simpa [n, stateCount] using q.isLt
  have hlocal : s * n + q.val < (s + 1) * n := by
    calc
      s * n + q.val < s * n + n := Nat.add_lt_add_left hq _
      _ = (s + 1) * n := by
        simp [Nat.add_mul, Nat.add_comm]
  have hstep : (s + 1) * n ≤ (t + 1) * n := by
    exact Nat.mul_le_mul_right n (Nat.succ_le_succ hs)
  unfold stateVar headBase stateSlots
  simpa [n] using Nat.lt_of_lt_of_le hlocal hstep

theorem headVar_ge_headBase
    (M : PolyDTMCandidate) (t s : Nat) (a : Option Bool) :
    headBase M t ≤ headVar M t s a := by
  unfold headVar
  omega

theorem headVar_lt_leftBase_valid
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat)
    (a : Option Bool)
    (hs : s ≤ t) :
    headVar M t s a < leftBase M x t := by
  unfold headVar leftBase
  have ha := symbolCode_lt_three a
  omega

theorem leftVar_ge_leftBase
    (M : PolyDTMCandidate) (x : BitString) (t s i : Nat)
    (a : Option Bool) :
    leftBase M x t ≤ leftVar M x t s i a := by
  unfold leftVar
  omega

theorem leftVar_lt_rightBase_valid
    (M : PolyDTMCandidate) (x : BitString) (t s i : Nat)
    (a : Option Bool)
    (hs : s ≤ t)
    (hi : i < radius x t) :
    leftVar M x t s i a < rightBase M x t := by
  let r := radius x t
  have hr : 0 < r := by
    simpa [r] using radius_pos x t
  have ha : symbolCode a < 3 := symbolCode_lt_three a
  have hcell : s * r + i < (s + 1) * r := by
    calc
      s * r + i < s * r + r := Nat.add_lt_add_left hi _
      _ = (s + 1) * r := by
        simp [Nat.add_mul, Nat.add_comm]
  have htime : (s + 1) * r ≤ (t + 1) * r := by
    exact Nat.mul_le_mul_right r (Nat.succ_le_succ hs)
  have hslot : (s * r + i) * 3 + symbolCode a <
      ((s + 1) * r) * 3 := by
    have hcode :
        (s * r + i) * 3 + symbolCode a <
          (s * r + i) * 3 + 3 :=
      Nat.add_lt_add_left ha _
    have hnext :
        (s * r + i) * 3 + 3 =
          (s * r + i + 1) * 3 := by omega
    have hsucc : s * r + i + 1 ≤ (s + 1) * r :=
      Nat.succ_le_of_lt hcell
    have hmul := Nat.mul_le_mul_right 3 hsucc
    rw [hnext] at hcode
    exact Nat.lt_of_lt_of_le hcode hmul
  have hbound :
      ((s + 1) * r) * 3 ≤ ((t + 1) * r) * 3 :=
    Nat.mul_le_mul_right 3 htime
  unfold leftVar rightBase
  simpa [r, Nat.add_assoc] using
    Nat.add_lt_add_left (Nat.lt_of_lt_of_le hslot hbound) (leftBase M x t)

theorem rightVar_ge_rightBase
    (M : PolyDTMCandidate) (x : BitString) (t s i : Nat)
    (a : Option Bool) :
    rightBase M x t ≤ rightVar M x t s i a := by
  unfold rightVar
  omega


theorem transitionCaseCNF_mem_transitionsCNF
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (hs : s < t)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool)
    (c : Clause)
    (hc : c ∈ transitionCaseCNF M x t s q a) :
    c ∈ transitionsCNF M x t := by
  unfold transitionsCNF
  apply List.mem_flatMap.mpr
  refine ⟨s, by simpa using hs, ?_⟩
  unfold transitionStepCNF
  apply List.mem_flatten.mpr
  let block : List Clause :=
    alphabet.flatMap fun a' => transitionCaseCNF M x t s q a'
  refine ⟨block, ?_, ?_⟩
  · unfold block
    exact List.mem_ofFn.mpr ⟨q, rfl⟩
  · unfold block
    apply List.mem_flatMap.mpr
    refine ⟨a, ?_, hc⟩
    cases a with
    | none => simp [alphabet]
    | some b =>
        cases b <;> simp [alphabet]


theorem active_transition_case_true
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (hs : s < t)
    (htableau : evalCNF sigma (boundedExecTableauCNF M x t) = true)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool)) :
    evalCNF sigma
      (transitionCaseCNF M x t s config.state config.tape.head) = true := by
  apply evalCNF_subset_true sigma
    (transitionCaseCNF M x t s config.state config.tape.head)
    (boundedExecTableauCNF M x t)
    htableau
  intro c hc
  simp only [boundedExecTableauCNF, List.mem_append]
  exact Or.inl (Or.inr
    (transitionCaseCNF_mem_transitionsCNF M x t s hs
      config.state config.tape.head c hc))


theorem stay_case_preserves_snapshot
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (qNext : Fin (M.stateCount + 1))
    (write : Option Bool)
    (hhalt : M.machine.halting config.state = false)
    (htrans :
      M.machine.transition config.state config.tape.head =
        (qNext, write, .stay))
    (hmatch : SnapshotMatches sigma M x t s config)
    (hcase :
      evalCNF sigma
        (transitionCaseCNF M x t s config.state config.tape.head) = true) :
    SnapshotMatches sigma M x t (s + 1) (M.machine.step config) := by
  let guard : Clause :=
    [neg (stateVar M t s config.state),
     neg (headVar M t s config.tape.head)]
  have hguard : evalClause sigma guard = false := by
    simpa [guard] using
      snapshot_transition_guard_false sigma M x t s config hmatch
  have hstay :
      evalCNF sigma
        (stayCaseCNF M x t s config.state config.tape.head qNext write) = true := by
    simpa [transitionCaseCNF, hhalt, htrans] using hcase
  have hstate :
      evalCNF sigma
        (setStateClauses guard M t (s + 1) qNext) = true := by
    apply evalCNF_subset_true sigma _ _ hstay
    intro cl hcl
    simp [stayCaseCNF, guard, hcl]
  have hhead :
      evalCNF sigma
        (setSymbolClauses guard (headVar M t (s + 1)) write) = true := by
    apply evalCNF_subset_true sigma _ _ hstay
    intro cl hcl
    simp [stayCaseCNF, guard, hcl]
  have hleft :
      evalCNF sigma (copyLeftAll guard M x t s) = true := by
    apply evalCNF_subset_true sigma _ _ hstay
    intro cl hcl
    simp [stayCaseCNF, guard, hcl]
  have hright :
      evalCNF sigma (copyRightAll guard M x t s) = true := by
    apply evalCNF_subset_true sigma _ _ hstay
    intro cl hcl
    simp [stayCaseCNF, guard, hcl]
  rcases hmatch with ⟨hstateOld, hheadOld, hleftOld, hrightOld⟩
  unfold SnapshotMatches
  constructor
  · intro q
    have hf :=
      setStateClauses_forces sigma guard M t (s + 1) qNext q
        hguard hstate
    simpa [TM.step, htrans, Tape.write, Tape.move] using hf
  constructor
  · intro a
    have hf :=
      setSymbolClauses_forces sigma guard (headVar M t (s + 1))
        write a hguard hhead
    simpa [TM.step, htrans, Tape.write, Tape.move] using hf
  constructor
  · intro i hi a
    have hcell :
        evalCNF sigma
          (copyLeftCell guard M x t s i (s + 1) i) = true := by
      apply evalCNF_subset_true sigma _ _ hleft
      intro cl hcl
      unfold copyLeftAll
      simp only [List.mem_flatMap, List.mem_range]
      exact ⟨i, hi, hcl⟩
    have hf :=
      copySymbolClauses_forces sigma guard
        (leftVar M x t s i) (leftVar M x t (s + 1) i)
        a hguard hcell
    rw [hf, hleftOld i hi a]
    simp [TM.step, htrans, Tape.write, Tape.move]
  · intro i hi a
    have hcell :
        evalCNF sigma
          (copyRightCell guard M x t s i (s + 1) i) = true := by
      apply evalCNF_subset_true sigma _ _ hright
      intro cl hcl
      unfold copyRightAll
      simp only [List.mem_flatMap, List.mem_range]
      exact ⟨i, hi, hcl⟩
    have hf :=
      copySymbolClauses_forces sigma guard
        (rightVar M x t s i) (rightVar M x t (s + 1) i)
        a hguard hcell
    rw [hf, hrightOld i hi a]
    simp [TM.step, htrans, Tape.write, Tape.move]


theorem halting_case_preserves_snapshot
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (hhalt : M.machine.halting config.state = true)
    (hmatch : SnapshotMatches sigma M x t s config)
    (hcase :
      evalCNF sigma
        (transitionCaseCNF M x t s config.state config.tape.head) = true) :
    SnapshotMatches sigma M x t (s + 1) config := by
  let guard : Clause :=
    [neg (stateVar M t s config.state),
     neg (headVar M t s config.tape.head)]
  have hguard : evalClause sigma guard = false := by
    simpa [guard] using
      snapshot_transition_guard_false sigma M x t s config hmatch
  have hhaltCNF :
      evalCNF sigma
        (haltingCaseCNF M x t s config.state config.tape.head) = true := by
    simpa [transitionCaseCNF, hhalt] using hcase
  have hstate :
      evalCNF sigma
        (setStateClauses guard M t (s + 1) config.state) = true := by
    apply evalCNF_subset_true sigma _ _ hhaltCNF
    intro cl hcl
    simp [haltingCaseCNF, guard, hcl]
  have hhead :
      evalCNF sigma (copyHeadCell guard M t s (s + 1)) = true := by
    apply evalCNF_subset_true sigma _ _ hhaltCNF
    intro cl hcl
    simp [haltingCaseCNF, guard, hcl]
  have hleft :
      evalCNF sigma (copyLeftAll guard M x t s) = true := by
    apply evalCNF_subset_true sigma _ _ hhaltCNF
    intro cl hcl
    simp [haltingCaseCNF, guard, hcl]
  have hright :
      evalCNF sigma (copyRightAll guard M x t s) = true := by
    apply evalCNF_subset_true sigma _ _ hhaltCNF
    intro cl hcl
    simp [haltingCaseCNF, guard, hcl]
  rcases hmatch with ⟨hstateOld, hheadOld, hleftOld, hrightOld⟩
  unfold SnapshotMatches
  constructor
  · intro q
    exact setStateClauses_forces sigma guard M t (s + 1)
      config.state q hguard hstate
  constructor
  · intro a
    have hf :=
      copySymbolClauses_forces sigma guard
        (headVar M t s) (headVar M t (s + 1))
        a hguard hhead
    rw [hf, hheadOld a]
  constructor
  · intro i hi a
    have hcell :
        evalCNF sigma
          (copyLeftCell guard M x t s i (s + 1) i) = true := by
      apply evalCNF_subset_true sigma _ _ hleft
      intro cl hcl
      unfold copyLeftAll
      simp only [List.mem_flatMap, List.mem_range]
      exact ⟨i, hi, hcl⟩
    have hf :=
      copySymbolClauses_forces sigma guard
        (leftVar M x t s i) (leftVar M x t (s + 1) i)
        a hguard hcell
    rw [hf, hleftOld i hi a]
  · intro i hi a
    have hcell :
        evalCNF sigma
          (copyRightCell guard M x t s i (s + 1) i) = true := by
      apply evalCNF_subset_true sigma _ _ hright
      intro cl hcl
      unfold copyRightAll
      simp only [List.mem_flatMap, List.mem_range]
      exact ⟨i, hi, hcl⟩
    have hf :=
      copySymbolClauses_forces sigma guard
        (rightVar M x t s i) (rightVar M x t (s + 1) i)
        a hguard hcell
    rw [hf, hrightOld i hi a]


theorem left_case_preserves_snapshot
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (qNext : Fin (M.stateCount + 1))
    (write : Option Bool)
    (hs : s < t)
    (hhalt : M.machine.halting config.state = false)
    (htrans :
      M.machine.transition config.state config.tape.head =
        (qNext, write, .left))
    (hleftBoundary :
      config.tape.left.getD (radius x t) M.machine.blank =
        M.machine.blank)
    (hmatch : SnapshotMatches sigma M x t s config)
    (hcase :
      evalCNF sigma
        (transitionCaseCNF M x t s config.state config.tape.head) = true) :
    SnapshotMatches sigma M x t (s + 1) (M.machine.step config) := by
  let guard : Clause :=
    [neg (stateVar M t s config.state),
     neg (headVar M t s config.tape.head)]
  have hguard : evalClause sigma guard = false := by
    simpa [guard] using
      snapshot_transition_guard_false sigma M x t s config hmatch
  have hleftCase :
      evalCNF sigma
        (leftMoveCaseCNF M x t s config.state config.tape.head qNext write) = true := by
    simpa [transitionCaseCNF, hhalt, htrans] using hcase
  have hstate :
      evalCNF sigma
        (setStateClauses guard M t (s + 1) qNext) = true := by
    apply evalCNF_subset_true sigma _ _ hleftCase
    intro cl hcl
    simp [leftMoveCaseCNF, guard, hcl]
  have hhead :
      evalCNF sigma
        (copySymbolClauses guard
          (leftVar M x t s 0)
          (headVar M t (s + 1))) = true := by
    apply evalCNF_subset_true sigma _ _ hleftCase
    intro cl hcl
    simp [leftMoveCaseCNF, guard, hcl]
  rcases hmatch with ⟨hstateOld, hheadOld, hleftOld, hrightOld⟩
  unfold SnapshotMatches
  constructor
  · intro q
    have hf :=
      setStateClauses_forces sigma guard M t (s + 1) qNext q hguard hstate
    simpa [TM.step, htrans, Tape.write, Tape.move] using hf
  constructor
  · intro a
    have hf :=
      copySymbolClauses_forces sigma guard
        (leftVar M x t s 0) (headVar M t (s + 1))
        a hguard hhead
    have hmoveHead :
        (M.machine.step config).tape.head =
          config.tape.left.getD 0 M.machine.blank := by
      simpa [TM.step, htrans, Tape.write] using
        P02BoundedComputationTape.move_left_head_getD
          M.machine.blank (config.tape.write write)
    rw [hf, hleftOld 0 (by simp [radius]) a, hmoveHead]
  constructor
  · intro i hi a
    by_cases hlast : i = radius x t - 1
    · subst i
      have hrone : 1 ≤ radius x t := by simp [radius]
      have hidx : radius x t - 1 + 1 = radius x t :=
        Nat.sub_add_cancel hrone
      have hmoveLeft :
          (M.machine.step config).tape.left.getD (radius x t - 1)
            M.machine.blank =
          config.tape.left.getD ((radius x t - 1) + 1)
            M.machine.blank := by
        simpa [TM.step, htrans, Tape.write] using
          P02BoundedComputationTape.move_left_left_getD
            M.machine.blank (config.tape.write write) (radius x t - 1)
      have hblank :
          (M.machine.step config).tape.left.getD (radius x t - 1)
            M.machine.blank = M.machine.blank := by
        rw [hmoveLeft, hidx, hleftBoundary]
      have hset :
          evalCNF sigma
            (setLeftCell guard M x t (s + 1) (radius x t - 1)
              M.machine.blank) = true := by
        apply evalCNF_subset_true sigma _ _ hleftCase
        intro cl hcl
        simp [leftMoveCaseCNF, guard, hcl]
      rw [hblank]
      exact setSymbolClauses_forces sigma guard
        (leftVar M x t (s + 1) (radius x t - 1))
        M.machine.blank a hguard hset
    · have his : i < radius x t - 1 := by
        have hle : i ≤ radius x t - 1 := by
          have hle' : i ≤ x.length + t := by
            exact Nat.le_of_lt_succ (by simpa [radius, Nat.succ_eq_add_one] using hi)
          simpa [radius] using hle'
        rcases Nat.lt_or_eq_of_le hle with hlt | heq
        · exact hlt
        · exact False.elim (hlast heq)
      have hcopy :
          evalCNF sigma
            (copyLeftCell guard M x t s (i + 1) (s + 1) i) = true := by
        apply evalCNF_subset_true sigma _ _ hleftCase
        intro cl hcl
        have hshift :
            cl ∈ (List.range (radius x t - 1)).flatMap (fun j =>
              copyLeftCell guard M x t s (j + 1) (s + 1) j) := by
          exact List.mem_flatMap.mpr ⟨i, by simpa using his, hcl⟩
        simpa [leftMoveCaseCNF, guard, hshift]
      have hf :=
        copySymbolClauses_forces sigma guard
          (leftVar M x t s (i + 1))
          (leftVar M x t (s + 1) i) a hguard hcopy
      have hi1 : i + 1 < radius x t := by
        have hbase : i < x.length + t := by simpa [radius] using his
        simpa [radius, Nat.succ_eq_add_one] using Nat.succ_lt_succ hbase
      have hmoveLeft :
          (M.machine.step config).tape.left.getD i M.machine.blank =
            config.tape.left.getD (i + 1) M.machine.blank := by
        simpa [TM.step, htrans, Tape.write] using
          P02BoundedComputationTape.move_left_left_getD
            M.machine.blank (config.tape.write write) i
      rw [hf, hleftOld (i + 1) hi1 a, hmoveLeft]
  · intro i hi a
    by_cases hz : i = 0
    · subst i
      have hset :
          evalCNF sigma
            (setRightCell guard M x t (s + 1) 0 write) = true := by
        apply evalCNF_subset_true sigma _ _ hleftCase
        intro cl hcl
        simp [leftMoveCaseCNF, guard, hcl]
      have hf :=
        setSymbolClauses_forces sigma guard
          (rightVar M x t (s + 1) 0) write a hguard hset
      have hmoveRightZero :
          (M.machine.step config).tape.right.getD 0 M.machine.blank = write := by
        simpa [TM.step, htrans, Tape.write] using
          P02BoundedComputationTape.move_left_right_zero
            M.machine.blank (config.tape.write write)
      rw [hmoveRightZero]
      exact hf
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
      have hj : j < radius x t - 1 := by
        have hsucclt : j + 1 < x.length + t + 1 := by
          simpa [radius] using hi
        have hbase : j < x.length + t := by
          exact Nat.lt_of_succ_lt_succ (by
            simpa [Nat.succ_eq_add_one] using hsucclt)
        simpa [radius] using hbase
      have hcopy :
          evalCNF sigma
            (copyRightCell guard M x t s j (s + 1) (j + 1)) = true := by
        apply evalCNF_subset_true sigma _ _ hleftCase
        intro cl hcl
        have hshift :
            cl ∈ (List.range (radius x t - 1)).flatMap (fun k =>
              copyRightCell guard M x t s k (s + 1) (k + 1)) := by
          exact List.mem_flatMap.mpr ⟨j, by simpa using hj, hcl⟩
        simpa [leftMoveCaseCNF, guard, hshift]
      have hf :=
        copySymbolClauses_forces sigma guard
          (rightVar M x t s j)
          (rightVar M x t (s + 1) (j + 1))
          a hguard hcopy
      have hjr : j < radius x t := by
        exact Nat.lt_trans hj (by
          have hrone : 1 ≤ radius x t := by simp [radius]
          exact Nat.sub_lt (by simp [radius]) (by decide))
      have hmoveRight :
          (M.machine.step config).tape.right.getD (j + 1)
            M.machine.blank =
          config.tape.right.getD j M.machine.blank := by
        simpa [TM.step, htrans, Tape.write] using
          P02BoundedComputationTape.move_left_right_succ
            M.machine.blank (config.tape.write write) j
      rw [hf, hrightOld j hjr a, hmoveRight]


theorem right_case_preserves_snapshot
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (qNext : Fin (M.stateCount + 1))
    (write : Option Bool)
    (hs : s < t)
    (hhalt : M.machine.halting config.state = false)
    (htrans :
      M.machine.transition config.state config.tape.head =
        (qNext, write, .right))
    (hrightBoundary :
      config.tape.right.getD (radius x t) M.machine.blank =
        M.machine.blank)
    (hmatch : SnapshotMatches sigma M x t s config)
    (hcase :
      evalCNF sigma
        (transitionCaseCNF M x t s config.state config.tape.head) = true) :
    SnapshotMatches sigma M x t (s + 1) (M.machine.step config) := by
  let guard : Clause :=
    [neg (stateVar M t s config.state),
     neg (headVar M t s config.tape.head)]
  have hguard : evalClause sigma guard = false := by
    simpa [guard] using
      snapshot_transition_guard_false sigma M x t s config hmatch
  have hrightCase :
      evalCNF sigma
        (rightMoveCaseCNF M x t s config.state config.tape.head qNext write) = true := by
    simpa [transitionCaseCNF, hhalt, htrans] using hcase
  have hstate :
      evalCNF sigma
        (setStateClauses guard M t (s + 1) qNext) = true := by
    apply evalCNF_subset_true sigma _ _ hrightCase
    intro cl hcl
    simp [rightMoveCaseCNF, guard, hcl]
  have hhead :
      evalCNF sigma
        (copySymbolClauses guard
          (rightVar M x t s 0)
          (headVar M t (s + 1))) = true := by
    apply evalCNF_subset_true sigma _ _ hrightCase
    intro cl hcl
    simp [rightMoveCaseCNF, guard, hcl]
  rcases hmatch with ⟨hstateOld, hheadOld, hleftOld, hrightOld⟩
  unfold SnapshotMatches
  constructor
  · intro q
    have hf :=
      setStateClauses_forces sigma guard M t (s + 1) qNext q hguard hstate
    simpa [TM.step, htrans, Tape.write, Tape.move] using hf
  constructor
  · intro a
    have hf :=
      copySymbolClauses_forces sigma guard
        (rightVar M x t s 0) (headVar M t (s + 1))
        a hguard hhead
    have hmoveHead :
        (M.machine.step config).tape.head =
          config.tape.right.getD 0 M.machine.blank := by
      simpa [TM.step, htrans, Tape.write] using
        P02BoundedComputationTape.move_right_head_getD
          M.machine.blank (config.tape.write write)
    rw [hf, hrightOld 0 (by simp [radius]) a, hmoveHead]
  constructor
  · intro i hi a
    by_cases hz : i = 0
    · subst i
      have hset :
          evalCNF sigma
            (setLeftCell guard M x t (s + 1) 0 write) = true := by
        apply evalCNF_subset_true sigma _ _ hrightCase
        intro cl hcl
        simp [rightMoveCaseCNF, guard, hcl]
      have hf :=
        setSymbolClauses_forces sigma guard
          (leftVar M x t (s + 1) 0) write a hguard hset
      have hmoveLeftZero :
          (M.machine.step config).tape.left.getD 0 M.machine.blank = write := by
        simpa [TM.step, htrans, Tape.write] using
          P02BoundedComputationTape.move_right_left_zero
            M.machine.blank (config.tape.write write)
      rw [hmoveLeftZero]
      exact hf
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hz
      have hj : j < radius x t - 1 := by
        have hsucclt : j + 1 < x.length + t + 1 := by
          simpa [radius] using hi
        have hbase : j < x.length + t := by
          exact Nat.lt_of_succ_lt_succ (by
            simpa [Nat.succ_eq_add_one] using hsucclt)
        simpa [radius] using hbase
      have hcopy :
          evalCNF sigma
            (copyLeftCell guard M x t s j (s + 1) (j + 1)) = true := by
        apply evalCNF_subset_true sigma _ _ hrightCase
        intro cl hcl
        have hshift :
            cl ∈ (List.range (radius x t - 1)).flatMap (fun k =>
              copyLeftCell guard M x t s k (s + 1) (k + 1)) := by
          exact List.mem_flatMap.mpr ⟨j, by simpa using hj, hcl⟩
        simpa [rightMoveCaseCNF, guard, hshift]
      have hf :=
        copySymbolClauses_forces sigma guard
          (leftVar M x t s j)
          (leftVar M x t (s + 1) (j + 1))
          a hguard hcopy
      have hjr : j < radius x t := by
        exact Nat.lt_trans hj (by
          exact Nat.sub_lt (by simp [radius]) (by decide))
      have hmoveLeft :
          (M.machine.step config).tape.left.getD (j + 1)
            M.machine.blank =
          config.tape.left.getD j M.machine.blank := by
        simpa [TM.step, htrans, Tape.write] using
          P02BoundedComputationTape.move_right_left_succ
            M.machine.blank (config.tape.write write) j
      rw [hf, hleftOld j hjr a, hmoveLeft]
  · intro i hi a
    by_cases hlast : i = radius x t - 1
    · subst i
      have hrone : 1 ≤ radius x t := by simp [radius]
      have hidx : radius x t - 1 + 1 = radius x t :=
        Nat.sub_add_cancel hrone
      have hmoveRight :
          (M.machine.step config).tape.right.getD (radius x t - 1)
            M.machine.blank =
          config.tape.right.getD ((radius x t - 1) + 1)
            M.machine.blank := by
        simpa [TM.step, htrans, Tape.write] using
          P02BoundedComputationTape.move_right_right_getD
            M.machine.blank (config.tape.write write) (radius x t - 1)
      have hblank :
          (M.machine.step config).tape.right.getD (radius x t - 1)
            M.machine.blank = M.machine.blank := by
        rw [hmoveRight, hidx, hrightBoundary]
      have hset :
          evalCNF sigma
            (setRightCell guard M x t (s + 1) (radius x t - 1)
              M.machine.blank) = true := by
        apply evalCNF_subset_true sigma _ _ hrightCase
        intro cl hcl
        simp [rightMoveCaseCNF, guard, hcl]
      rw [hblank]
      exact setSymbolClauses_forces sigma guard
        (rightVar M x t (s + 1) (radius x t - 1))
        M.machine.blank a hguard hset
    · have his : i < radius x t - 1 := by
        have hle : i ≤ radius x t - 1 := by
          have hle' : i ≤ x.length + t := by
            exact Nat.le_of_lt_succ (by simpa [radius, Nat.succ_eq_add_one] using hi)
          simpa [radius] using hle'
        rcases Nat.lt_or_eq_of_le hle with hlt | heq
        · exact hlt
        · exact False.elim (hlast heq)
      have hcopy :
          evalCNF sigma
            (copyRightCell guard M x t s (i + 1) (s + 1) i) = true := by
        apply evalCNF_subset_true sigma _ _ hrightCase
        intro cl hcl
        have hshift :
            cl ∈ (List.range (radius x t - 1)).flatMap (fun j =>
              copyRightCell guard M x t s (j + 1) (s + 1) j) := by
          exact List.mem_flatMap.mpr ⟨i, by simpa using his, hcl⟩
        simpa [rightMoveCaseCNF, guard, hshift]
      have hf :=
        copySymbolClauses_forces sigma guard
          (rightVar M x t s (i + 1))
          (rightVar M x t (s + 1) i)
          a hguard hcopy
      have hi1 : i + 1 < radius x t := by
        have hbase : i < x.length + t := by simpa [radius] using his
        simpa [radius, Nat.succ_eq_add_one] using Nat.succ_lt_succ hbase
      have hmoveRight :
          (M.machine.step config).tape.right.getD i M.machine.blank =
            config.tape.right.getD (i + 1) M.machine.blank := by
        simpa [TM.step, htrans, Tape.write] using
          P02BoundedComputationTape.move_right_right_getD
            M.machine.blank (config.tape.write write) i
      rw [hf, hrightOld (i + 1) hi1 a, hmoveRight]


def transitionSoundnessCertificate : TransitionSoundnessCertificate where
  step := by
    intro sigma M x t s hs htableau hmatch
    let init := initialTMConfig M.machine x
    let config := M.machine.run s init
    have hcase :
        evalCNF sigma
          (transitionCaseCNF M x t s config.state config.tape.head) = true :=
      active_transition_case_true sigma M x t s hs htableau config
    have hrunSucc :
        M.machine.run (s + 1) init = M.machine.run 1 config := by
      simpa [config] using
        (MachineRunLemmas.run_add M.machine s 1 init)
    by_cases hhalt : M.machine.halting config.state = true
    · have hpres :=
        halting_case_preserves_snapshot sigma M x t s config
          hhalt hmatch hcase
      have hnext :
          M.machine.run (s + 1) init = config := by
        rw [hrunSucc]
        simpa [TM.run, hhalt]
      simpa [init, config] using (hnext ▸ hpres)
    · have hhaltFalse : M.machine.halting config.state = false := by
        cases hh : M.machine.halting config.state <;> simp_all
      rcases htrans :
          M.machine.transition config.state config.tape.head with
        ⟨qNext, write, dir⟩
      have hnext :
          M.machine.run (s + 1) init = M.machine.step config := by
        rw [hrunSucc]
        simp [TM.run, hhaltFalse]
      cases dir with
      | stay =>
          have hpres :=
            stay_case_preserves_snapshot sigma M x t s config
              qNext write hhaltFalse htrans hmatch hcase
          rw [hnext]
          exact hpres
      | left =>
          have hboundary :
              config.tape.left.getD (radius x t) M.machine.blank =
                M.machine.blank := by
            simpa [config, init] using
              P02BoundedComputationTape.canonical_run_left_radius_blank
                M x t s (Nat.le_of_lt hs)
          have hpres :=
            left_case_preserves_snapshot sigma M x t s config
              qNext write hs hhaltFalse htrans hboundary hmatch hcase
          rw [hnext]
          exact hpres
      | right =>
          have hboundary :
              config.tape.right.getD (radius x t) M.machine.blank =
                M.machine.blank := by
            simpa [config, init] using
              P02BoundedComputationTape.canonical_run_right_radius_blank
                M x t s (Nat.le_of_lt hs)
          have hpres :=
            right_case_preserves_snapshot sigma M x t s config
              qNext write hs hhaltFalse htrans hboundary hmatch hcase
          rw [hnext]
          exact hpres

theorem snapshots_all
    (S : TransitionSoundnessCertificate)
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (hs : s ≤ t)
    (htableau : evalCNF sigma (boundedExecTableauCNF M x t) = true) :
    SnapshotMatches sigma M x t s
      (M.machine.run s (initialTMConfig M.machine x)) := by
  induction s with
  | zero =>
      simpa [TM.run] using
        boundedExecTableau_initial_sound sigma M x t htableau
  | succ s ih =>
      have hslt : s < t := Nat.lt_of_succ_le hs
      exact S.step sigma M x t s hslt htableau
        (ih (Nat.le_trans (Nat.le_succ s) hs))

theorem tableau_sound
    (S : TransitionSoundnessCertificate)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) :
    SATLanguage (boundedExecCircuit M x t) →
      AcceptsAtFuel M x t := by
  intro hsat
  rcases (satLanguage_cnfCircuit_iff
    (boundedExecTableauCNF M x t)).mp hsat with ⟨sigma, htableau⟩
  have hmatch :=
    snapshots_all S sigma M x t t (Nat.le_refl t) htableau
  exact boundedExecTableau_final_acceptance_sound
    sigma M x t
    (M.machine.run t (initialTMConfig M.machine x))
    hmatch htableau

theorem tableau_complete
    (C : TableauCompletenessCertificate)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t : Nat) :
    AcceptsAtFuel M x t →
      SATLanguage (boundedExecCircuit M x t) := by
  intro hacc
  apply (satLanguage_cnfCircuit_iff
    (boundedExecTableauCNF M x t)).mpr
  exact ⟨C.assignment M x t hacc, C.satisfies M x t hacc⟩

theorem certificates_close_boundedExecCorrectness
    (S : TransitionSoundnessCertificate)
    (C : TableauCompletenessCertificate) :
    BoundedExecCorrectness := by
  intro M x t
  constructor
  · exact tableau_sound S M x t
  · exact tableau_complete C M x t

def TransitionSoundnessGap : Prop :=
  Nonempty TransitionSoundnessCertificate

def TableauCompletenessGap : Prop :=
  Nonempty TableauCompletenessCertificate

#print axioms MCore.Real.P02BoundedComputationClose.stateVar_lt_headBase_valid
#print axioms MCore.Real.P02BoundedComputationClose.headVar_lt_leftBase_valid
#print axioms MCore.Real.P02BoundedComputationClose.leftVar_lt_rightBase_valid
#print axioms MCore.Real.P02BoundedComputationClose.transitionCaseCNF_mem_transitionsCNF
#print axioms MCore.Real.P02BoundedComputationClose.active_transition_case_true
#print axioms MCore.Real.P02BoundedComputationClose.stay_case_preserves_snapshot
#print axioms MCore.Real.P02BoundedComputationClose.halting_case_preserves_snapshot
#print axioms MCore.Real.P02BoundedComputationClose.left_case_preserves_snapshot
#print axioms MCore.Real.P02BoundedComputationClose.right_case_preserves_snapshot
#print axioms MCore.Real.P02BoundedComputationClose.transitionSoundnessCertificate
#print axioms MCore.Real.P02BoundedComputationClose.snapshots_all
#print axioms MCore.Real.P02BoundedComputationClose.tableau_sound
#print axioms MCore.Real.P02BoundedComputationClose.tableau_complete
#print axioms MCore.Real.P02BoundedComputationClose.certificates_close_boundedExecCorrectness

end P02BoundedComputationClose
end Real
end MCore
