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

theorem mem_setStateClauses_has_prefix
    (guard : Clause) (M : PolyDTMCandidate) (t s : Nat)
    (target : Fin (M.stateCount + 1)) (clause : Clause)
    (h : clause ∈ setStateClauses guard M t s target) :
    ∃ suffix : Clause, clause = guard ++ suffix := by
  unfold setStateClauses at h
  rcases List.mem_ofFn.mp h with ⟨q, rfl⟩
  exact ⟨[litFor (stateVar M t s q) (decide (q = target))], rfl⟩

theorem mem_setSymbolClauses_has_prefix
    (guard : Clause) (varAt : Option Bool → Nat) (target : Option Bool)
    (clause : Clause)
    (h : clause ∈ setSymbolClauses guard varAt target) :
    ∃ suffix : Clause, clause = guard ++ suffix := by
  unfold setSymbolClauses at h
  rcases List.mem_map.mp h with ⟨a, _, rfl⟩
  exact ⟨[litFor (varAt a) (decide (a = target))], rfl⟩

theorem mem_copySymbolClauses_has_prefix
    (guard : Clause) (oldVar newVar : Option Bool → Nat)
    (clause : Clause)
    (h : clause ∈ copySymbolClauses guard oldVar newVar) :
    ∃ suffix : Clause, clause = guard ++ suffix := by
  unfold copySymbolClauses at h
  rcases List.mem_flatMap.mp h with ⟨a, _, ha⟩
  simp only [List.mem_cons, List.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact ⟨[neg (oldVar a), pos (newVar a)], rfl⟩
  · exact ⟨[pos (oldVar a), neg (newVar a)], rfl⟩

theorem mem_copyLeftAll_has_prefix
    (guard : Clause) (M : PolyDTMCandidate) (x : BitString) (t s : Nat)
    (clause : Clause)
    (h : clause ∈ copyLeftAll guard M x t s) :
    ∃ suffix : Clause, clause = guard ++ suffix := by
  unfold copyLeftAll at h
  rcases List.mem_flatMap.mp h with ⟨i, _, hi⟩
  exact mem_copySymbolClauses_has_prefix guard
    (leftVar M x t s i) (leftVar M x t (s + 1) i) clause hi

theorem mem_copyRightAll_has_prefix
    (guard : Clause) (M : PolyDTMCandidate) (x : BitString) (t s : Nat)
    (clause : Clause)
    (h : clause ∈ copyRightAll guard M x t s) :
    ∃ suffix : Clause, clause = guard ++ suffix := by
  unfold copyRightAll at h
  rcases List.mem_flatMap.mp h with ⟨i, _, hi⟩
  exact mem_copySymbolClauses_has_prefix guard
    (rightVar M x t s i) (rightVar M x t (s + 1) i) clause hi

theorem mem_copyLeftCell_has_prefix
    (guard : Clause) (M : PolyDTMCandidate) (x : BitString) (t oldS oldI newS newI : Nat)
    (clause : Clause)
    (h : clause ∈ copyLeftCell guard M x t oldS oldI newS newI) :
    ∃ suffix : Clause, clause = guard ++ suffix := by
  exact mem_copySymbolClauses_has_prefix guard
    (leftVar M x t oldS oldI) (leftVar M x t newS newI) clause h

theorem mem_copyRightCell_has_prefix
    (guard : Clause) (M : PolyDTMCandidate) (x : BitString) (t oldS oldI newS newI : Nat)
    (clause : Clause)
    (h : clause ∈ copyRightCell guard M x t oldS oldI newS newI) :
    ∃ suffix : Clause, clause = guard ++ suffix := by
  exact mem_copySymbolClauses_has_prefix guard
    (rightVar M x t oldS oldI) (rightVar M x t newS newI) clause h

theorem mem_copyHeadCell_has_prefix
    (guard : Clause) (M : PolyDTMCandidate) (t oldS newS : Nat)
    (clause : Clause)
    (h : clause ∈ copyHeadCell guard M t oldS newS) :
    ∃ suffix : Clause, clause = guard ++ suffix := by
  exact mem_copySymbolClauses_has_prefix guard
    (headVar M t oldS) (headVar M t newS) clause h

theorem mem_setLeftCell_has_prefix
    (guard : Clause) (M : PolyDTMCandidate) (x : BitString) (t s i : Nat)
    (target : Option Bool) (clause : Clause)
    (h : clause ∈ setLeftCell guard M x t s i target) :
    ∃ suffix : Clause, clause = guard ++ suffix := by
  exact mem_setSymbolClauses_has_prefix guard (leftVar M x t s i) target clause h

theorem mem_setRightCell_has_prefix
    (guard : Clause) (M : PolyDTMCandidate) (x : BitString) (t s i : Nat)
    (target : Option Bool) (clause : Clause)
    (h : clause ∈ setRightCell guard M x t s i target) :
    ∃ suffix : Clause, clause = guard ++ suffix := by
  exact mem_setSymbolClauses_has_prefix guard (rightVar M x t s i) target clause h

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
  have hprefix : ∃ suffix : Clause, clause = guard ++ suffix := by
    by_cases hhalt : M.machine.halting q = true
    · simp only [transitionCaseCNF, dif_pos hhalt] at hclause
      unfold haltingCaseCNF at hclause
      simp only [List.mem_append] at hclause
      rcases hclause with hs | hrest
      · exact mem_setStateClauses_has_prefix guard M t (s + 1) q clause hs
      · rcases hrest with hh | hrest
        · exact mem_copyHeadCell_has_prefix guard M t s (s + 1) clause hh
        · rcases hrest with hl | hr
          · exact mem_copyLeftAll_has_prefix guard M x t s clause hl
          · exact mem_copyRightAll_has_prefix guard M x t s clause hr
    · rcases htrans : M.machine.transition q a with ⟨qNext, write, dir⟩
      cases dir with
      | stay =>
          simp only [transitionCaseCNF, dif_neg hhalt, htrans] at hclause
          unfold stayCaseCNF at hclause
          simp only [List.mem_append] at hclause
          rcases hclause with hs | hrest
          · exact mem_setStateClauses_has_prefix guard M t (s + 1) qNext clause hs
          · rcases hrest with hh | hrest
            · exact mem_setSymbolClauses_has_prefix guard
                (headVar M t (s + 1)) write clause hh
            · rcases hrest with hl | hr
              · exact mem_copyLeftAll_has_prefix guard M x t s clause hl
              · exact mem_copyRightAll_has_prefix guard M x t s clause hr
      | left =>
          simp only [transitionCaseCNF, dif_neg hhalt, htrans] at hclause
          unfold leftMoveCaseCNF at hclause
          simp only [List.mem_append] at hclause
          rcases hclause with hs | hrest
          · exact mem_setStateClauses_has_prefix guard M t (s + 1) qNext clause hs
          · rcases hrest with hh | hrest
            · exact mem_copySymbolClauses_has_prefix guard
                (leftVar M x t s 0) (headVar M t (s + 1)) clause hh
            · rcases hrest with hshiftL | hrest
              · rcases List.mem_flatMap.mp hshiftL with ⟨i, _, hi⟩
                exact mem_copyLeftCell_has_prefix guard M x t s (i + 1) (s + 1) i clause hi
              · rcases hrest with hblankL | hrest
                · exact mem_setLeftCell_has_prefix guard M x t (s + 1)
                    (radius x t - 1) M.machine.blank clause hblankL
                · rcases hrest with hwriteR | hshiftR
                  · exact mem_setRightCell_has_prefix guard M x t (s + 1) 0 write clause hwriteR
                  · rcases List.mem_flatMap.mp hshiftR with ⟨i, _, hi⟩
                    exact mem_copyRightCell_has_prefix guard M x t s i (s + 1) (i + 1) clause hi
      | right =>
          simp only [transitionCaseCNF, dif_neg hhalt, htrans] at hclause
          unfold rightMoveCaseCNF at hclause
          simp only [List.mem_append] at hclause
          rcases hclause with hs | hrest
          · exact mem_setStateClauses_has_prefix guard M t (s + 1) qNext clause hs
          · rcases hrest with hh | hrest
            · exact mem_copySymbolClauses_has_prefix guard
                (rightVar M x t s 0) (headVar M t (s + 1)) clause hh
            · rcases hrest with hwriteL | hrest
              · exact mem_setLeftCell_has_prefix guard M x t (s + 1) 0 write clause hwriteL
              · rcases hrest with hshiftL | hrest
                · rcases List.mem_flatMap.mp hshiftL with ⟨i, _, hi⟩
                  exact mem_copyLeftCell_has_prefix guard M x t s i (s + 1) (i + 1) clause hi
                · rcases hrest with hshiftR | hblankR
                  · rcases List.mem_flatMap.mp hshiftR with ⟨i, _, hi⟩
                    exact mem_copyRightCell_has_prefix guard M x t s (i + 1) (s + 1) i clause hi
                  · exact mem_setRightCell_has_prefix guard M x t (s + 1)
                      (radius x t - 1) M.machine.blank clause hblankR
  rcases hprefix with ⟨suffix, rfl⟩
  exact evalClause_append_true_of_guard_true sigma guard suffix hguard

#print axioms MCore.Real.P02TableauCompletenessActive.inactive_guard_true
#print axioms MCore.Real.P02TableauCompletenessActive.inactive_transitionCase_true

end P02TableauCompletenessActive
end Real
end MCore
