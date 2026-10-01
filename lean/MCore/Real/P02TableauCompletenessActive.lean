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

theorem evalCNF_append_true_local
    (sigma : Assignment)
    (a b : CNF)
    (ha : evalCNF sigma a = true)
    (hb : evalCNF sigma b = true) :
    evalCNF sigma (a ++ b) = true := by
  rw [evalCNF_append_eq, ha, hb]
  rfl

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

theorem setStateClauses_true_of_guard_true
    (sigma : Assignment)
    (guard : Clause)
    (M : PolyDTMCandidate)
    (t s : Nat)
    (target : Fin (M.stateCount + 1))
    (hguard : evalClause sigma guard = true) :
    evalCNF sigma (setStateClauses guard M t s target) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  unfold setStateClauses at hclause
  rcases List.mem_ofFn.mp hclause with ⟨q, rfl⟩
  exact evalClause_append_true_of_guard_true sigma guard _ hguard

theorem setSymbolClauses_true_of_guard_true
    (sigma : Assignment)
    (guard : Clause)
    (varAt : Option Bool → Nat)
    (target : Option Bool)
    (hguard : evalClause sigma guard = true) :
    evalCNF sigma (setSymbolClauses guard varAt target) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  unfold setSymbolClauses at hclause
  rcases List.mem_map.mp hclause with ⟨a, _, rfl⟩
  exact evalClause_append_true_of_guard_true sigma guard _ hguard

theorem copySymbolClauses_true_of_guard_true
    (sigma : Assignment)
    (guard : Clause)
    (oldVar newVar : Option Bool → Nat)
    (hguard : evalClause sigma guard = true) :
    evalCNF sigma (copySymbolClauses guard oldVar newVar) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  unfold copySymbolClauses at hclause
  rcases List.mem_flatMap.mp hclause with ⟨a, _, ha⟩
  simp only [List.mem_cons, List.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact evalClause_append_true_of_guard_true sigma guard _ hguard
  · exact evalClause_append_true_of_guard_true sigma guard _ hguard

theorem copyLeftAll_true_of_guard_true
    (sigma : Assignment)
    (guard : Clause)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (hguard : evalClause sigma guard = true) :
    evalCNF sigma (copyLeftAll guard M x t s) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  unfold copyLeftAll at hclause
  rcases List.mem_flatMap.mp hclause with ⟨i, _, hi⟩
  have hcell :=
    copySymbolClauses_true_of_guard_true
      sigma guard
      (leftVar M x t s i)
      (leftVar M x t (s + 1) i)
      hguard
  exact evalCNF_member_true sigma _ clause hi hcell

theorem copyRightAll_true_of_guard_true
    (sigma : Assignment)
    (guard : Clause)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t s : Nat)
    (hguard : evalClause sigma guard = true) :
    evalCNF sigma (copyRightAll guard M x t s) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  unfold copyRightAll at hclause
  rcases List.mem_flatMap.mp hclause with ⟨i, _, hi⟩
  have hcell :=
    copySymbolClauses_true_of_guard_true
      sigma guard
      (rightVar M x t s i)
      (rightVar M x t (s + 1) i)
      hguard
  exact evalCNF_member_true sigma _ clause hi hcell

theorem copyLeftCells_true_of_guard_true
    (sigma : Assignment)
    (guard : Clause)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t oldS newS : Nat)
    (indices : List Nat)
    (oldI newI : Nat → Nat)
    (hguard : evalClause sigma guard = true) :
    evalCNF sigma
      (indices.flatMap fun i =>
        copyLeftCell guard M x t oldS (oldI i) newS (newI i)) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  rcases List.mem_flatMap.mp hclause with ⟨i, _, hi⟩
  unfold copyLeftCell at hi
  have hcell :=
    copySymbolClauses_true_of_guard_true
      sigma guard
      (leftVar M x t oldS (oldI i))
      (leftVar M x t newS (newI i))
      hguard
  exact evalCNF_member_true sigma _ clause hi hcell

theorem copyRightCells_true_of_guard_true
    (sigma : Assignment)
    (guard : Clause)
    (M : PolyDTMCandidate)
    (x : BitString)
    (t oldS newS : Nat)
    (indices : List Nat)
    (oldI newI : Nat → Nat)
    (hguard : evalClause sigma guard = true) :
    evalCNF sigma
      (indices.flatMap fun i =>
        copyRightCell guard M x t oldS (oldI i) newS (newI i)) = true := by
  apply evalCNF_true_of_forall_mem
  intro clause hclause
  rcases List.mem_flatMap.mp hclause with ⟨i, _, hi⟩
  unfold copyRightCell at hi
  have hcell :=
    copySymbolClauses_true_of_guard_true
      sigma guard
      (rightVar M x t oldS (oldI i))
      (rightVar M x t newS (newI i))
      hguard
  exact evalCNF_member_true sigma _ clause hi hcell

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
    simpa [guard] using
      inactive_guard_true sigma M x t s config hmatch q a hinactive
  by_cases hhalt : M.machine.halting q = true
  · have hs :=
      setStateClauses_true_of_guard_true
        sigma guard M t (s + 1) q hguard
    have hh :=
      copySymbolClauses_true_of_guard_true
        sigma guard (headVar M t s) (headVar M t (s + 1)) hguard
    have hl :=
      copyLeftAll_true_of_guard_true sigma guard M x t s hguard
    have hr :=
      copyRightAll_true_of_guard_true sigma guard M x t s hguard
    have htail :=
      evalCNF_append_true_local sigma
        (copyHeadCell guard M t s (s + 1))
        (copyLeftAll guard M x t s ++ copyRightAll guard M x t s)
        (by simpa [copyHeadCell] using hh)
        (evalCNF_append_true_local sigma
          (copyLeftAll guard M x t s)
          (copyRightAll guard M x t s) hl hr)
    have hall :=
      evalCNF_append_true_local sigma
        (setStateClauses guard M t (s + 1) q)
        (copyHeadCell guard M t s (s + 1) ++
          copyLeftAll guard M x t s ++ copyRightAll guard M x t s)
        hs htail
    simpa [transitionCaseCNF, hhalt, haltingCaseCNF, guard] using hall
  · rcases htrans : M.machine.transition q a with ⟨qNext, write, dir⟩
    cases dir with
    | stay =>
        have hs :=
          setStateClauses_true_of_guard_true
            sigma guard M t (s + 1) qNext hguard
        have hh :=
          setSymbolClauses_true_of_guard_true
            sigma guard (headVar M t (s + 1)) write hguard
        have hl :=
          copyLeftAll_true_of_guard_true sigma guard M x t s hguard
        have hr :=
          copyRightAll_true_of_guard_true sigma guard M x t s hguard
        have htail :=
          evalCNF_append_true_local sigma
            (setSymbolClauses guard (headVar M t (s + 1)) write)
            (copyLeftAll guard M x t s ++ copyRightAll guard M x t s)
            hh
            (evalCNF_append_true_local sigma
              (copyLeftAll guard M x t s)
              (copyRightAll guard M x t s) hl hr)
        have hall :=
          evalCNF_append_true_local sigma
            (setStateClauses guard M t (s + 1) qNext)
            (setSymbolClauses guard (headVar M t (s + 1)) write ++
              copyLeftAll guard M x t s ++ copyRightAll guard M x t s)
            hs htail
        simpa [transitionCaseCNF, hhalt, htrans, stayCaseCNF, guard] using hall
    | left =>
        have hs :=
          setStateClauses_true_of_guard_true
            sigma guard M t (s + 1) qNext hguard
        have hh :=
          copySymbolClauses_true_of_guard_true
            sigma guard
            (leftVar M x t s 0)
            (headVar M t (s + 1)) hguard
        have hshiftL :=
          copyLeftCells_true_of_guard_true
            sigma guard M x t s (s + 1)
            (List.range (radius x t - 1))
            (fun i => i + 1) (fun i => i) hguard
        have hsetL :=
          setSymbolClauses_true_of_guard_true
            sigma guard
            (leftVar M x t (s + 1) (radius x t - 1))
            M.machine.blank hguard
        have hsetR :=
          setSymbolClauses_true_of_guard_true
            sigma guard
            (rightVar M x t (s + 1) 0)
            write hguard
        have hshiftR :=
          copyRightCells_true_of_guard_true
            sigma guard M x t s (s + 1)
            (List.range (radius x t - 1))
            (fun i => i) (fun i => i + 1) hguard
        have htail1 :=
          evalCNF_append_true_local sigma
            (setRightCell guard M x t (s + 1) 0 write)
            ((List.range (radius x t - 1)).flatMap fun i =>
              copyRightCell guard M x t s i (s + 1) (i + 1))
            (by simpa [setRightCell] using hsetR) hshiftR
        have htail2 :=
          evalCNF_append_true_local sigma
            (setLeftCell guard M x t (s + 1) (radius x t - 1)
              M.machine.blank)
            (setRightCell guard M x t (s + 1) 0 write ++
              (List.range (radius x t - 1)).flatMap fun i =>
                copyRightCell guard M x t s i (s + 1) (i + 1))
            (by simpa [setLeftCell] using hsetL) htail1
        have htail3 :=
          evalCNF_append_true_local sigma
            ((List.range (radius x t - 1)).flatMap fun i =>
              copyLeftCell guard M x t s (i + 1) (s + 1) i)
            (setLeftCell guard M x t (s + 1) (radius x t - 1)
                M.machine.blank ++
              setRightCell guard M x t (s + 1) 0 write ++
              (List.range (radius x t - 1)).flatMap fun i =>
                copyRightCell guard M x t s i (s + 1) (i + 1))
            hshiftL htail2
        have htail4 :=
          evalCNF_append_true_local sigma
            (copySymbolClauses guard
              (leftVar M x t s 0)
              (headVar M t (s + 1)))
            ((List.range (radius x t - 1)).flatMap (fun i =>
                copyLeftCell guard M x t s (i + 1) (s + 1) i) ++
              setLeftCell guard M x t (s + 1) (radius x t - 1)
                M.machine.blank ++
              setRightCell guard M x t (s + 1) 0 write ++
              (List.range (radius x t - 1)).flatMap fun i =>
                copyRightCell guard M x t s i (s + 1) (i + 1))
            hh htail3
        have hall :=
          evalCNF_append_true_local sigma
            (setStateClauses guard M t (s + 1) qNext)
            (copySymbolClauses guard
                (leftVar M x t s 0)
                (headVar M t (s + 1)) ++
              (List.range (radius x t - 1)).flatMap (fun i =>
                copyLeftCell guard M x t s (i + 1) (s + 1) i) ++
              setLeftCell guard M x t (s + 1) (radius x t - 1)
                M.machine.blank ++
              setRightCell guard M x t (s + 1) 0 write ++
              (List.range (radius x t - 1)).flatMap fun i =>
                copyRightCell guard M x t s i (s + 1) (i + 1))
            hs htail4
        simpa [transitionCaseCNF, hhalt, htrans, leftMoveCaseCNF, guard] using hall
    | right =>
        have hs :=
          setStateClauses_true_of_guard_true
            sigma guard M t (s + 1) qNext hguard
        have hh :=
          copySymbolClauses_true_of_guard_true
            sigma guard
            (rightVar M x t s 0)
            (headVar M t (s + 1)) hguard
        have hsetL :=
          setSymbolClauses_true_of_guard_true
            sigma guard
            (leftVar M x t (s + 1) 0)
            write hguard
        have hshiftL :=
          copyLeftCells_true_of_guard_true
            sigma guard M x t s (s + 1)
            (List.range (radius x t - 1))
            (fun i => i) (fun i => i + 1) hguard
        have hshiftR :=
          copyRightCells_true_of_guard_true
            sigma guard M x t s (s + 1)
            (List.range (radius x t - 1))
            (fun i => i + 1) (fun i => i) hguard
        have hsetR :=
          setSymbolClauses_true_of_guard_true
            sigma guard
            (rightVar M x t (s + 1) (radius x t - 1))
            M.machine.blank hguard
        have htail1 :=
          evalCNF_append_true_local sigma
            ((List.range (radius x t - 1)).flatMap fun i =>
              copyRightCell guard M x t s (i + 1) (s + 1) i)
            (setRightCell guard M x t (s + 1) (radius x t - 1)
              M.machine.blank)
            hshiftR
            (by simpa [setRightCell] using hsetR)
        have htail2 :=
          evalCNF_append_true_local sigma
            ((List.range (radius x t - 1)).flatMap fun i =>
              copyLeftCell guard M x t s i (s + 1) (i + 1))
            ((List.range (radius x t - 1)).flatMap (fun i =>
                copyRightCell guard M x t s (i + 1) (s + 1) i) ++
              setRightCell guard M x t (s + 1) (radius x t - 1)
                M.machine.blank)
            hshiftL htail1
        have htail3 :=
          evalCNF_append_true_local sigma
            (setLeftCell guard M x t (s + 1) 0 write)
            ((List.range (radius x t - 1)).flatMap (fun i =>
                copyLeftCell guard M x t s i (s + 1) (i + 1)) ++
              (List.range (radius x t - 1)).flatMap (fun i =>
                copyRightCell guard M x t s (i + 1) (s + 1) i) ++
              setRightCell guard M x t (s + 1) (radius x t - 1)
                M.machine.blank)
            (by simpa [setLeftCell] using hsetL) htail2
        have htail4 :=
          evalCNF_append_true_local sigma
            (copySymbolClauses guard
              (rightVar M x t s 0)
              (headVar M t (s + 1)))
            (setLeftCell guard M x t (s + 1) 0 write ++
              (List.range (radius x t - 1)).flatMap (fun i =>
                copyLeftCell guard M x t s i (s + 1) (i + 1)) ++
              (List.range (radius x t - 1)).flatMap (fun i =>
                copyRightCell guard M x t s (i + 1) (s + 1) i) ++
              setRightCell guard M x t (s + 1) (radius x t - 1)
                M.machine.blank)
            hh htail3
        have hall :=
          evalCNF_append_true_local sigma
            (setStateClauses guard M t (s + 1) qNext)
            (copySymbolClauses guard
                (rightVar M x t s 0)
                (headVar M t (s + 1)) ++
              setLeftCell guard M x t (s + 1) 0 write ++
              (List.range (radius x t - 1)).flatMap (fun i =>
                copyLeftCell guard M x t s i (s + 1) (i + 1)) ++
              (List.range (radius x t - 1)).flatMap (fun i =>
                copyRightCell guard M x t s (i + 1) (s + 1) i) ++
              setRightCell guard M x t (s + 1) (radius x t - 1)
                M.machine.blank)
            hs htail4
        simpa [transitionCaseCNF, hhalt, htrans, rightMoveCaseCNF, guard] using hall

#print axioms MCore.Real.P02TableauCompletenessActive.inactive_guard_true
#print axioms MCore.Real.P02TableauCompletenessActive.inactive_transitionCase_true

end P02TableauCompletenessActive
end Real
end MCore
