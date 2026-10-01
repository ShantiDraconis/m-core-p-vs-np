import Mathlib.Tactic
import MCore.Real.P02BoundedComputationClose

namespace MCore
namespace Real
namespace P02TableauCompletenessActive

open CircuitK1
open CanonicalFinalProof
open P02BoundedComputationEncoding
open P02BoundedComputationLogic
open P02BoundedComputationSoundness
open P02BoundedComputationClose

theorem evalClause_append_true_of_guard_true
    (sigma : Assignment)
    (guard suffix : Clause)
    (hguard : evalClause sigma guard = true) :
    evalClause sigma (guard ++ suffix) = true := by
  rw [evalClause_append, hguard]
  simp

theorem inactive_guard_true
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (hmatch : SnapshotMatches sigma M x t s config)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool)
    (hinactive : q ≠ config.state ∨ a ≠ config.tape.head) :
    evalClause sigma
      [neg (stateVar M t s q), neg (headVar M t s a)] = true := by
  rcases hmatch with ⟨hstate, hhead, _, _⟩
  rcases hinactive with hq | ha
  · have hs : sigma (stateVar M t s q) = false := by
      have h := hstate q
      simpa [hq] using h
    simp [evalClause, evalLiteral, neg, hs]
  · have hh : sigma (headVar M t s a) = false := by
      have h := hhead a
      simpa [ha] using h
    simp [evalClause, evalLiteral, neg, hh]

def GuardedCNF (guard : Clause) (F : CNF) : Prop :=
  ∀ clause ∈ F, ∃ suffix : Clause, clause = guard ++ suffix

theorem guardedCNF_append
    (guard : Clause) (A B : CNF)
    (hA : GuardedCNF guard A)
    (hB : GuardedCNF guard B) :
    GuardedCNF guard (A ++ B) := by
  intro clause h
  rw [List.mem_append] at h
  cases h with
  | inl ha => exact hA clause ha
  | inr hb => exact hB clause hb

theorem guarded_setStateClauses
    (guard : Clause)
    (M : PolyDTMCandidate)
    (t s : Nat)
    (target : Fin (M.stateCount + 1)) :
    GuardedCNF guard (setStateClauses guard M t s target) := by
  intro clause h
  unfold setStateClauses at h
  rcases List.mem_ofFn.mp h with ⟨q, rfl⟩
  exact ⟨[litFor (stateVar M t s q) (decide (q = target))], rfl⟩

theorem guarded_setSymbolClauses
    (guard : Clause)
    (varAt : Option Bool → Nat)
    (target : Option Bool) :
    GuardedCNF guard (setSymbolClauses guard varAt target) := by
  intro clause h
  unfold setSymbolClauses at h
  rcases List.mem_map.mp h with ⟨a, _, rfl⟩
  exact ⟨[litFor (varAt a) (decide (a = target))], rfl⟩

theorem guarded_copySymbolClauses
    (guard : Clause)
    (oldVar newVar : Option Bool → Nat) :
    GuardedCNF guard (copySymbolClauses guard oldVar newVar) := by
  intro clause h
  unfold copySymbolClauses at h
  rcases List.mem_flatMap.mp h with ⟨a, _, ha⟩
  simp only [List.mem_cons, List.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact ⟨[neg (oldVar a), pos (newVar a)], rfl⟩
  · exact ⟨[pos (oldVar a), neg (newVar a)], rfl⟩

theorem guarded_copyLeftAll
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat) :
    GuardedCNF guard (copyLeftAll guard M x t s) := by
  intro clause h
  unfold copyLeftAll at h
  rcases List.mem_flatMap.mp h with ⟨i, _, hi⟩
  exact guarded_copySymbolClauses guard
    (leftVar M x t s i) (leftVar M x t (s + 1) i) clause hi

theorem guarded_copyRightAll
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat) :
    GuardedCNF guard (copyRightAll guard M x t s) := by
  intro clause h
  unfold copyRightAll at h
  rcases List.mem_flatMap.mp h with ⟨i, _, hi⟩
  exact guarded_copySymbolClauses guard
    (rightVar M x t s i) (rightVar M x t (s + 1) i) clause hi

theorem guarded_copyLeftCell
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString) (t oldS oldI newS newI : Nat) :
    GuardedCNF guard (copyLeftCell guard M x t oldS oldI newS newI) := by
  unfold copyLeftCell
  exact guarded_copySymbolClauses guard
    (leftVar M x t oldS oldI) (leftVar M x t newS newI)

theorem guarded_copyRightCell
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString) (t oldS oldI newS newI : Nat) :
    GuardedCNF guard (copyRightCell guard M x t oldS oldI newS newI) := by
  unfold copyRightCell
  exact guarded_copySymbolClauses guard
    (rightVar M x t oldS oldI) (rightVar M x t newS newI)

theorem guarded_setLeftCell
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString) (t s i : Nat)
    (target : Option Bool) :
    GuardedCNF guard (setLeftCell guard M x t s i target) := by
  unfold setLeftCell
  exact guarded_setSymbolClauses guard (leftVar M x t s i) target

theorem guarded_setRightCell
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString) (t s i : Nat)
    (target : Option Bool) :
    GuardedCNF guard (setRightCell guard M x t s i target) := by
  unfold setRightCell
  exact guarded_setSymbolClauses guard (rightVar M x t s i) target

theorem guarded_copyHeadCell
    (guard : Clause)
    (M : PolyDTMCandidate) (t oldS newS : Nat) :
    GuardedCNF guard (copyHeadCell guard M t oldS newS) := by
  unfold copyHeadCell
  exact guarded_copySymbolClauses guard
    (headVar M t oldS) (headVar M t newS)

theorem guarded_flatMap_copyLeft
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat) :
    GuardedCNF guard
      ((List.range (radius x t - 1)).flatMap fun i =>
        copyLeftCell guard M x t s (i + 1) (s + 1) i) := by
  intro clause h
  rcases List.mem_flatMap.mp h with ⟨i, _, hi⟩
  exact guarded_copyLeftCell guard M x t s (i + 1) (s + 1) i clause hi

theorem guarded_flatMap_copyRight
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat) :
    GuardedCNF guard
      ((List.range (radius x t - 1)).flatMap fun i =>
        copyRightCell guard M x t s i (s + 1) (i + 1)) := by
  intro clause h
  rcases List.mem_flatMap.mp h with ⟨i, _, hi⟩
  exact guarded_copyRightCell guard M x t s i (s + 1) (i + 1) clause hi

theorem guarded_flatMap_copyLeftRightMove
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat) :
    GuardedCNF guard
      ((List.range (radius x t - 1)).flatMap fun i =>
        copyLeftCell guard M x t s i (s + 1) (i + 1)) := by
  intro clause h
  rcases List.mem_flatMap.mp h with ⟨i, _, hi⟩
  exact guarded_copyLeftCell guard M x t s i (s + 1) (i + 1) clause hi

theorem guarded_flatMap_copyRightRightMove
    (guard : Clause)
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat) :
    GuardedCNF guard
      ((List.range (radius x t - 1)).flatMap fun i =>
        copyRightCell guard M x t s (i + 1) (s + 1) i) := by
  intro clause h
  rcases List.mem_flatMap.mp h with ⟨i, _, hi⟩
  exact guarded_copyRightCell guard M x t s (i + 1) (s + 1) i clause hi

theorem guarded_haltingCaseCNF
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) :
    let guard : Clause := [neg (stateVar M t s q), neg (headVar M t s a)]
    GuardedCNF guard (haltingCaseCNF M x t s q a) := by
  dsimp
  unfold haltingCaseCNF
  exact guardedCNF_append _ _ _
    (guarded_setStateClauses _ M t (s + 1) q)
    (guardedCNF_append _ _ _
      (guarded_copyHeadCell _ M t s (s + 1))
      (guardedCNF_append _ _ _
        (guarded_copyLeftAll _ M x t s)
        (guarded_copyRightAll _ M x t s)))

theorem guarded_stayCaseCNF
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (qNext : Fin (M.stateCount + 1)) (write : Option Bool) :
    let guard : Clause := [neg (stateVar M t s q), neg (headVar M t s a)]
    GuardedCNF guard (stayCaseCNF M x t s q a qNext write) := by
  dsimp
  unfold stayCaseCNF
  exact guardedCNF_append _ _ _
    (guarded_setStateClauses _ M t (s + 1) qNext)
    (guardedCNF_append _ _ _
      (guarded_setSymbolClauses _ (headVar M t (s + 1)) write)
      (guardedCNF_append _ _ _
        (guarded_copyLeftAll _ M x t s)
        (guarded_copyRightAll _ M x t s)))

theorem guarded_leftMoveCaseCNF
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (qNext : Fin (M.stateCount + 1)) (write : Option Bool) :
    let guard : Clause := [neg (stateVar M t s q), neg (headVar M t s a)]
    GuardedCNF guard (leftMoveCaseCNF M x t s q a qNext write) := by
  dsimp
  unfold leftMoveCaseCNF
  exact guardedCNF_append _ _ _
    (guarded_setStateClauses _ M t (s + 1) qNext)
    (guardedCNF_append _ _ _
      (guarded_copySymbolClauses _ (leftVar M x t s 0) (headVar M t (s + 1)))
      (guardedCNF_append _ _ _
        (guarded_flatMap_copyLeft _ M x t s)
        (guardedCNF_append _ _ _
          (guarded_setLeftCell _ M x t (s + 1) (radius x t - 1) M.machine.blank)
          (guardedCNF_append _ _ _
            (guarded_setRightCell _ M x t (s + 1) 0 write)
            (guarded_flatMap_copyRight _ M x t s)))))

theorem guarded_rightMoveCaseCNF
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool)
    (qNext : Fin (M.stateCount + 1)) (write : Option Bool) :
    let guard : Clause := [neg (stateVar M t s q), neg (headVar M t s a)]
    GuardedCNF guard (rightMoveCaseCNF M x t s q a qNext write) := by
  dsimp
  unfold rightMoveCaseCNF
  exact guardedCNF_append _ _ _
    (guarded_setStateClauses _ M t (s + 1) qNext)
    (guardedCNF_append _ _ _
      (guarded_copySymbolClauses _ (rightVar M x t s 0) (headVar M t (s + 1)))
      (guardedCNF_append _ _ _
        (guarded_setLeftCell _ M x t (s + 1) 0 write)
        (guardedCNF_append _ _ _
          (guarded_flatMap_copyLeftRightMove _ M x t s)
          (guardedCNF_append _ _ _
            (guarded_flatMap_copyRightRightMove _ M x t s)
            (guarded_setRightCell _ M x t (s + 1) (radius x t - 1)
              M.machine.blank)))))

theorem guarded_transitionCaseCNF
    (M : PolyDTMCandidate) (x : BitString) (t s : Nat)
    (q : Fin (M.stateCount + 1)) (a : Option Bool) :
    let guard : Clause := [neg (stateVar M t s q), neg (headVar M t s a)]
    GuardedCNF guard (transitionCaseCNF M x t s q a) := by
  dsimp
  by_cases hhalt : M.machine.halting q = true
  · simp only [transitionCaseCNF, dif_pos hhalt]
    exact guarded_haltingCaseCNF M x t s q a
  · rcases htrans : M.machine.transition q a with ⟨qNext, write, dir⟩
    cases dir with
    | stay =>
        simp only [transitionCaseCNF, dif_neg hhalt, htrans]
        exact guarded_stayCaseCNF M x t s q a qNext write
    | left =>
        simp only [transitionCaseCNF, dif_neg hhalt, htrans]
        exact guarded_leftMoveCaseCNF M x t s q a qNext write
    | right =>
        simp only [transitionCaseCNF, dif_neg hhalt, htrans]
        exact guarded_rightMoveCaseCNF M x t s q a qNext write

theorem inactive_transitionCase_true
    (sigma : Assignment)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (config : Configuration (Fin (M.stateCount + 1)) (Option Bool))
    (hmatch : SnapshotMatches sigma M x t s config)
    (q : Fin (M.stateCount + 1))
    (a : Option Bool)
    (hinactive : q ≠ config.state ∨ a ≠ config.tape.head) :
    evalCNF sigma (transitionCaseCNF M x t s q a) = true := by
  let guard : Clause :=
    [neg (stateVar M t s q), neg (headVar M t s a)]
  have hguard : evalClause sigma guard = true := by
    simpa [guard] using inactive_guard_true sigma M x t s config hmatch q a hinactive
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  have hprefix :
      ∃ suffix : Clause, clause = guard ++ suffix :=
    guarded_transitionCaseCNF M x t s q a clause hclause
  rcases hprefix with ⟨suffix, rfl⟩
  exact evalClause_append_true_of_guard_true sigma guard suffix hguard

#print axioms MCore.Real.P02TableauCompletenessActive.inactive_guard_true
#print axioms MCore.Real.P02TableauCompletenessActive.inactive_transitionCase_true

end P02TableauCompletenessActive
end Real
end MCore
