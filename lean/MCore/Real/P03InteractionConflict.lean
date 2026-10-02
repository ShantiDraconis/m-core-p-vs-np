import MCore.Real.P03Lemmas

namespace MCore
namespace Real
namespace P03InteractionConflict

open CanonicalFinalProof
open PNPNTMTableauEncoding
open P03MaterialLaw
open P03Lemmas

/-- Variables occurring in one NTM clause. -/
def ClauseVarSet (clause : NTMClause) : Finset Nat :=
  (clause.map NTMLiteral.var).toFinset

/-- Variables occurring anywhere in an NTM CNF. -/
def CNFVarSet (F : NTMCNF) : Finset Nat :=
  (F.flatMap (fun clause => clause.map NTMLiteral.var)).toFinset

theorem var_mem_CNFVarSet_of_mem
    {F : NTMCNF}
    {clause : NTMClause}
    {lit : NTMLiteral}
    (hcl : clause ∈ F)
    (hl : lit ∈ clause) :
    lit.var ∈ CNFVarSet F := by
  simp [CNFVarSet]
  exact ⟨clause, hcl, lit, hl, rfl⟩

theorem evalNTMLiteral_eq_of_agree
    {sigma1 sigma2 : Assignment}
    {lit : NTMLiteral}
    (h : sigma1 lit.var = sigma2 lit.var) :
    evalNTMLiteral sigma1 lit = evalNTMLiteral sigma2 lit := by
  simp [evalNTMLiteral, h]

theorem evalNTMClause_eq_of_agree_on_varset
    {clause : NTMClause}
    {sigma1 sigma2 : Assignment}
    (h :
      ∀ v ∈ ClauseVarSet clause,
        sigma1 v = sigma2 v) :
    evalNTMClause sigma1 clause = evalNTMClause sigma2 clause := by
  induction clause with
  | nil =>
      rfl
  | cons lit rest ih =>
      have hlit : sigma1 lit.var = sigma2 lit.var := by
        apply h
        simp [ClauseVarSet]
      have hrest :
          ∀ v ∈ ClauseVarSet rest,
            sigma1 v = sigma2 v := by
        intro v hv
        apply h
        simpa [ClauseVarSet] using hv
      simp only [evalNTMClause]
      rw [evalNTMLiteral_eq_of_agree hlit, ih hrest]

theorem evalNTMCNF_eq_of_agree_on_varset
    {F : NTMCNF}
    {sigma1 sigma2 : Assignment}
    (h :
      ∀ v ∈ CNFVarSet F,
        sigma1 v = sigma2 v) :
    evalNTMCNF sigma1 F = evalNTMCNF sigma2 F := by
  induction F with
  | nil =>
      rfl
  | cons clause rest ih =>
      have hclause :
          ∀ v ∈ ClauseVarSet clause,
            sigma1 v = sigma2 v := by
        intro v hv
        apply h
        simp [CNFVarSet, ClauseVarSet] at hv ⊢
        exact Or.inl hv
      have hrest :
          ∀ v ∈ CNFVarSet rest,
            sigma1 v = sigma2 v := by
        intro v hv
        apply h
        simpa [CNFVarSet] using hv
      simp only [evalNTMCNF]
      rw [evalNTMClause_eq_of_agree_on_varset hclause, ih hrest]

theorem mem_CNFVarSet_iff
    {F : NTMCNF}
    {v : Nat} :
    v ∈ CNFVarSet F ↔
      ∃ clause ∈ F, ∃ lit ∈ clause, lit.var = v := by
  simp [CNFVarSet]

theorem terminal_var_classifier
    {M : PolyNTMCandidate}
    {t v : Nat}
    (hv : v ∈ CNFVarSet (ntmFinalAcceptanceCNF M t)) :
    ∃ q : Fin (M.stateCount + 1),
      M.machine.accepting q = true ∧
      v = ntmStateVar M t t q := by
  rcases (mem_CNFVarSet_iff.mp hv) with
    ⟨clause, hclause, lit, hlit, hvar⟩
  have hclauseEq : clause = ntmAcceptingStateLits M t := by
    simpa [ntmFinalAcceptanceCNF] using hclause
  subst clause
  unfold ntmAcceptingStateLits at hlit
  rcases filterMap_mem_exists
      (fun q : Fin (M.stateCount + 1) =>
        if M.machine.accepting q = true then
          some (ntmPos (ntmStateVar M t t q))
        else none)
      (List.ofFn fun q : Fin (M.stateCount + 1) => q)
      lit hlit with
    ⟨q, _hqmem, hq⟩
  by_cases hacc : M.machine.accepting q = true
  · simp [hacc] at hq
    subst lit
    refine ⟨q, hacc, ?_⟩
    simpa [ntmPos] using hvar.symm
  · simp [hacc] at hq

/--
Every variable in the initial block belongs to exactly one of the four
time-zero regions: state, head, left tape, or right tape.
-/
theorem initial_var_classifier
    {M : PolyNTMCandidate}
    {x : BitString}
    {t v : Nat}
    (hv : v ∈ CNFVarSet (ntmInitialCNF M x t)) :
    (∃ q : Fin (M.stateCount + 1),
        v = ntmStateVar M t 0 q) ∨
    (∃ a : Option Bool,
        v = ntmHeadVar M t 0 a) ∨
    (∃ i : Nat, i < ntmRadius x t ∧
      ∃ a : Option Bool,
        v = ntmLeftVar M x t 0 i a) ∨
    (∃ i : Nat, i < ntmRadius x t ∧
      ∃ a : Option Bool,
        v = ntmRightVar M x t 0 i a) := by
  rcases (mem_CNFVarSet_iff.mp hv) with
    ⟨clause, hclause, lit, hlit, hvar⟩
  unfold ntmInitialCNF at hclause
  simp only [List.mem_append] at hclause
  rcases hclause with hState | hclause
  · unfold ntmSetStateClauses at hState
    rw [List.mem_ofFn] at hState
    rcases hState with ⟨q, rfl⟩
    simp at hlit
    subst lit
    left
    refine ⟨q, ?_⟩
    simpa [ntmLitFor_var] using hvar.symm
  · rcases hclause with hHead | hclause
    · unfold ntmSetSymbolClauses at hHead
      rw [List.mem_map] at hHead
      rcases hHead with ⟨a, _ha, rfl⟩
      simp at hlit
      subst lit
      right
      left
      refine ⟨a, ?_⟩
      simpa [ntmLitFor_var] using hvar.symm
    · rcases hclause with hLeft | hRight
      · rw [List.mem_flatMap] at hLeft
        rcases hLeft with ⟨i, hi, hset⟩
        have hir : i < ntmRadius x t := List.mem_range.mp hi
        unfold ntmSetLeftCell ntmSetSymbolClauses at hset
        rw [List.mem_map] at hset
        rcases hset with ⟨a, _ha, rfl⟩
        simp at hlit
        subst lit
        right
        right
        left
        refine ⟨i, hir, a, ?_⟩
        simpa [ntmLitFor_var] using hvar.symm
      · rw [List.mem_flatMap] at hRight
        rcases hRight with ⟨i, hi, hset⟩
        have hir : i < ntmRadius x t := List.mem_range.mp hi
        unfold ntmSetRightCell ntmSetSymbolClauses at hset
        rw [List.mem_map] at hset
        rcases hset with ⟨a, _ha, rfl⟩
        simp at hlit
        subst lit
        right
        right
        right
        refine ⟨i, hir, a, ?_⟩
        simpa [ntmLitFor_var] using hvar.symm

/--
A non-degenerate interaction conflict.

The prefix Init+Transit is satisfiable, Terminal is satisfiable in isolation,
but the complete tableau is unsatisfiable.  Thus the contradiction cannot be
explained by a terminal-empty-clause degeneracy or by an inconsistent physical
prefix alone.
-/
structure OrbitalInteractionConflict
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) where
  h_term_sat :
    CNFSat (ntmFinalAcceptanceCNF M t)
  h_prefix_sat :
    CNFSat (supportedCNF initTransitSupport M x t)
  h_whole_unsat :
    CNFUnsat (boundedExecTableauCNF_NTM M x t)

/-- Degenerate case: Terminal is already contradictory without Init/Transit. -/
def IsTerminalDegenerate
    (M : PolyNTMCandidate)
    (t : Nat) : Prop :=
  CNFUnsat (ntmFinalAcceptanceCNF M t)

/-- Genuine interaction case used by the P03 material route. -/
def IsInteractionConflict
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat) : Prop :=
  Nonempty (OrbitalInteractionConflict M x t)

/-- Every interaction conflict canonically yields the full conflict witness. -/
def OrbitalInteractionConflict.toClauseConflictWitness
    {M : PolyNTMCandidate}
    {x : BitString}
    {t : Nat}
    (C : OrbitalInteractionConflict M x t) :
    ClauseConflictWitness M x t :=
  (fullConflictExtractor M).locate x t C.h_whole_unsat

/--
If Terminal is satisfiable, its accepting-state clause cannot be empty.
This separates genuine interaction conflicts from the [[]] terminal
degeneracy.
-/
theorem terminal_sat_implies_nonempty_lits
    {M : PolyNTMCandidate}
    {t : Nat}
    (h : CNFSat (ntmFinalAcceptanceCNF M t)) :
    ntmAcceptingStateLits M t ≠ [] := by
  intro hEmpty
  rcases h with ⟨sigma, hSat⟩
  simp [ntmFinalAcceptanceCNF, hEmpty, evalNTMCNF, evalNTMClause] at hSat

/--
For positive time, a terminal state variable cannot be the initial state
variable.  This is the only Init/Terminal separation fact that needs t > 0.
-/
theorem terminal_state_ne_initial_state
    (M : PolyNTMCandidate)
    (t : Nat)
    (ht : 0 < t)
    (q0 qt : Fin (M.stateCount + 1)) :
    ntmStateVar M t 0 q0 ≠ ntmStateVar M t t qt := by
  intro hEq
  have h := ntmStateVar_injective M t 0 t q0 qt hEq
  omega

/-- Terminal state variables lie strictly below the head-variable region. -/
theorem terminal_state_ne_initial_head
    (M : PolyNTMCandidate)
    (x : BitString)
    (t : Nat)
    (qt : Fin (M.stateCount + 1))
    (a : Option Bool) :
    ntmStateVar M t t qt ≠ ntmHeadVar M t 0 a := by
  exact stateVar_ne_headVar M x t t 0 qt a (by omega) (by omega)

/-- Terminal state variables cannot collide with initial left-tape variables. -/
theorem terminal_state_ne_initial_left
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat)
    (hi : i < ntmRadius x t)
    (qt : Fin (M.stateCount + 1))
    (a : Option Bool) :
    ntmStateVar M t t qt ≠ ntmLeftVar M x t 0 i a := by
  have hs := ntmStateVar_lt_headBase M t t qt (by omega)
  have hl := (ntmLeftVar_range M x t 0 i a (by omega) hi).1
  have hb : ntmHeadBase M t ≤ ntmLeftBase M x t := by
    simp [ntmLeftBase]
  omega

/-- Terminal state variables cannot collide with initial right-tape variables. -/
theorem terminal_state_ne_initial_right
    (M : PolyNTMCandidate)
    (x : BitString)
    (t i : Nat)
    (hi : i < ntmRadius x t)
    (qt : Fin (M.stateCount + 1))
    (a : Option Bool) :
    ntmStateVar M t t qt ≠ ntmRightVar M x t 0 i a := by
  have hs := ntmStateVar_lt_headBase M t t qt (by omega)
  have hr := (ntmRightVar_range M x t 0 i a (by omega) hi).1
  have hb : ntmHeadBase M t ≤ ntmRightBase M x t := by
    simp [ntmRightBase, ntmLeftBase]
  omega

#print axioms MCore.Real.P03InteractionConflict.mem_CNFVarSet_iff
#print axioms MCore.Real.P03InteractionConflict.terminal_var_classifier
#print axioms MCore.Real.P03InteractionConflict.initial_var_classifier
#print axioms MCore.Real.P03InteractionConflict.var_mem_CNFVarSet_of_mem
#print axioms MCore.Real.P03InteractionConflict.evalNTMClause_eq_of_agree_on_varset
#print axioms MCore.Real.P03InteractionConflict.evalNTMCNF_eq_of_agree_on_varset
#print axioms MCore.Real.P03InteractionConflict.terminal_sat_implies_nonempty_lits
#print axioms MCore.Real.P03InteractionConflict.terminal_state_ne_initial_state
#print axioms MCore.Real.P03InteractionConflict.terminal_state_ne_initial_head
#print axioms MCore.Real.P03InteractionConflict.terminal_state_ne_initial_left
#print axioms MCore.Real.P03InteractionConflict.terminal_state_ne_initial_right

end P03InteractionConflict
end Real
end MCore
