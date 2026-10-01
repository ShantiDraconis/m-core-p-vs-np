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
      simp only [haltingCaseCNF, List.mem_append] at hclause
      rcases hclause with hstate | hrest
      · unfold setStateClauses at hstate
        rcases List.mem_ofFn.mp hstate with ⟨q', rfl⟩
        exact ⟨[litFor (stateVar M t (s + 1) q') (decide (q' = q))], rfl⟩
      · simp only [List.mem_append] at hrest
        rcases hrest with hhead | hrest
        · unfold copyHeadCell copySymbolClauses at hhead
          rcases List.mem_flatMap.mp hhead with ⟨a', _, hmem⟩
          simp only [List.mem_cons, List.mem_singleton] at hmem
          rcases hmem with rfl | rfl
          · exact ⟨[neg (headVar M t s a'), pos (headVar M t (s + 1) a')], rfl⟩
          · exact ⟨[pos (headVar M t s a'), neg (headVar M t (s + 1) a')], rfl⟩
        · simp only [List.mem_append] at hrest
          rcases hrest with hleft | hright
          · unfold copyLeftAll at hleft
            rcases List.mem_flatMap.mp hleft with ⟨i, _, hi⟩
            unfold copySymbolClauses at hi
            rcases List.mem_flatMap.mp hi with ⟨a', _, hmem⟩
            simp only [List.mem_cons, List.mem_singleton] at hmem
            rcases hmem with rfl | rfl
            · exact ⟨[neg (leftVar M x t s i a'), pos (leftVar M x t (s + 1) i a')], rfl⟩
            · exact ⟨[pos (leftVar M x t s i a'), neg (leftVar M x t (s + 1) i a')], rfl⟩
          · unfold copyRightAll at hright
            rcases List.mem_flatMap.mp hright with ⟨i, _, hi⟩
            unfold copySymbolClauses at hi
            rcases List.mem_flatMap.mp hi with ⟨a', _, hmem⟩
            simp only [List.mem_cons, List.mem_singleton] at hmem
            rcases hmem with rfl | rfl
            · exact ⟨[neg (rightVar M x t s i a'), pos (rightVar M x t (s + 1) i a')], rfl⟩
            · exact ⟨[pos (rightVar M x t s i a'), neg (rightVar M x t (s + 1) i a')], rfl⟩
    · rcases htrans : M.machine.transition q a with ⟨qNext, write, dir⟩
      cases dir <;>
        simp [transitionCaseCNF, hhalt, htrans, stayCaseCNF,
          leftMoveCaseCNF, rightMoveCaseCNF, setStateClauses,
          setSymbolClauses, copySymbolClauses, copyLeftAll, copyRightAll,
          copyLeftCell, copyRightCell, guard] at hclause ⊢
  rcases hprefix with ⟨suffix, rfl⟩
  exact evalClause_append_true_of_guard_true sigma guard suffix hguard

#print axioms MCore.Real.P02TableauCompletenessActive.inactive_guard_true
#print axioms MCore.Real.P02TableauCompletenessActive.inactive_transitionCase_true

end P02TableauCompletenessActive
end Real
end MCore
