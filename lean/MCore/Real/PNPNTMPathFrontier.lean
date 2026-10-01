
import MCore.Real.PNPNTMTableauFrontier

namespace MCore
namespace Real
namespace PNPNTMPathFrontier

open CanonicalFinalProof

abbrev NTMConfig (M : PolyNTMCandidate) :=
  Configuration (Fin (M.stateCount + 1)) (Option Bool)

def NTMHalted
    (M : PolyNTMCandidate)
    (c : NTMConfig M) : Prop :=
  M.machine.accepting c.state = true \/
    M.machine.rejecting c.state = true

def NTMActive
    (M : PolyNTMCandidate)
    (c : NTMConfig M) : Prop :=
  ¬ NTMHalted M c

/--
One exact runBranches step:
- halted configurations persist unchanged;
- active configurations take one listed nondeterministic successor.
-/
def NTMTableauStep
    (M : PolyNTMCandidate)
    (c c' : NTMConfig M) : Prop :=
  (NTMHalted M c ∧ c' = c) \/
  (NTMActive M c ∧ c' ∈ M.machine.successors c)

/--
Exact-length sequential path matching the runBranches fuel convention.
At fuel t there are t+1 snapshots.
-/
def NTMTableauPath
    (M : PolyNTMCandidate)
    (t : Nat)
    (c0 : NTMConfig M)
    (path : Fin (t + 1) -> NTMConfig M) : Prop :=
  path 0 = c0 ∧
    ∀ i : Fin t,
      NTMTableauStep M (path i.castSucc) (path i.succ)

/--
The endpoint of an exact-length path is accepting.
-/
def NTMTableauAcceptingPath
    (M : PolyNTMCandidate)
    (t : Nat)
    (c0 : NTMConfig M) : Prop :=
  ∃ path : Fin (t + 1) -> NTMConfig M,
    NTMTableauPath M t c0 path ∧
    M.machine.accepting (path (Fin.last t)).state = true

/--
Generic append-distribution lemma for runBranches.
The old repository had a machine-specific version for witnessGuessMachine;
this is the machine-independent form needed by the NTM tableau proof.
-/
theorem mem_runBranches_append
    {State Symbol : Type}
    (M : NTM State Symbol)
    (fuel : Nat)
    (xs ys : List (Configuration State Symbol))
    (z : Configuration State Symbol) :
    z ∈ M.runBranches fuel (xs ++ ys) <->
      z ∈ M.runBranches fuel xs \/
      z ∈ M.runBranches fuel ys := by
  induction fuel generalizing xs ys with
  | zero =>
      simp [NTM.runBranches]
  | succ fuel ih =>
      simp only [NTM.runBranches, List.filter_append, List.flatMap_append]
      rw [ih]
      simp only [ih]
      simpa [or_assoc, or_left_comm, or_comm]



theorem runBranches_halted_singleton
    (M : PolyNTMCandidate)
    (c : NTMConfig M)
    (fuel : Nat)
    (h : NTMHalted M c) :
    M.machine.runBranches fuel [c] = [c] := by
  have hhalt :
      M.machine.accepting c.state || M.machine.rejecting c.state = true := by
    rcases h with ha | hr
    · simp [ha]
    · simp [hr]
  induction fuel with
  | zero =>
      rfl
  | succ fuel ih =>
      simp [NTM.runBranches, hhalt, ih]

theorem mem_runBranches_flatMap
    {State Symbol : Type}
    (M : NTM State Symbol)
    (fuel : Nat)
    (xs : List (Configuration State Symbol))
    (f : Configuration State Symbol -> List (Configuration State Symbol))
    (z : Configuration State Symbol) :
    z ∈ M.runBranches fuel (xs.flatMap f) <->
      ∃ x ∈ xs, z ∈ M.runBranches fuel (f x) := by
  induction xs with
  | nil =>
      simp [NTM.runBranches]
  | cons x xs ih =>
      simp only [List.flatMap_cons]
      rw [mem_runBranches_append M fuel (f x) (xs.flatMap f) z]
      rw [ih]
      constructor
      · intro h
        rcases h with hx | hrest
        · exact ⟨x, by simp, hx⟩
        · rcases hrest with ⟨y, hy, hz⟩
          exact ⟨y, by simp [hy], hz⟩
      · rintro ⟨y, hy, hz⟩
        simp only [List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact Or.inl hz
        · exact Or.inr ⟨y, hy, hz⟩



/--
Recursive exact-fuel path relation matching runBranches.
This is an induction-friendly form used to prove the Fin-indexed tableau path
equivalence without reopening runBranches in later proofs.
-/
inductive NTMRunPath (M : PolyNTMCandidate) :
    Nat -> NTMConfig M -> NTMConfig M -> Prop where
  | zero (c : NTMConfig M) :
      NTMRunPath M 0 c c
  | halted
      {fuel : Nat} {c z : NTMConfig M}
      (hhalt : NTMHalted M c)
      (tail : NTMRunPath M fuel c z) :
      NTMRunPath M (fuel + 1) c z
  | active
      {fuel : Nat} {c c1 z : NTMConfig M}
      (hactive : NTMActive M c)
      (hstep : c1 ∈ M.machine.successors c)
      (tail : NTMRunPath M fuel c1 z) :
      NTMRunPath M (fuel + 1) c z

theorem runBranches_singleton_succ_halted
    (M : PolyNTMCandidate)
    (fuel : Nat)
    (c : NTMConfig M)
    (h : NTMHalted M c) :
    M.machine.runBranches (fuel + 1) [c] =
      M.machine.runBranches fuel [c] := by
  have hhalt :
      M.machine.accepting c.state || M.machine.rejecting c.state = true := by
    rcases h with ha | hr
    · simp [ha]
    · simp [hr]
  simp [NTM.runBranches, hhalt]

theorem runBranches_singleton_succ_active
    (M : PolyNTMCandidate)
    (fuel : Nat)
    (c : NTMConfig M)
    (h : NTMActive M c) :
    M.machine.runBranches (fuel + 1) [c] =
      M.machine.runBranches fuel (M.machine.successors c) := by
  have hnot :
      M.machine.accepting c.state || M.machine.rejecting c.state = false := by
    apply Bool.eq_false_iff.mpr
    intro htrue
    have hor :
        M.machine.accepting c.state = true \/
          M.machine.rejecting c.state = true := by
      exact Bool.or_eq_true.mp htrue
    exact h hor
  simp [NTM.runBranches, hnot]

def RunBranchesPathEquivalence : Prop :=
  ∀ (M : PolyNTMCandidate) (fuel : Nat) (c z : NTMConfig M),
    z ∈ M.machine.runBranches fuel [c] <->
      NTMRunPath M fuel c z


theorem mem_runBranches_list_iff_exists_singleton
    {State Symbol : Type}
    (M : NTM State Symbol)
    (fuel : Nat)
    (xs : List (Configuration State Symbol))
    (z : Configuration State Symbol) :
    z ∈ M.runBranches fuel xs <->
      ∃ x ∈ xs, z ∈ M.runBranches fuel [x] := by
  have hflat :
      xs.flatMap (fun x => [x]) = xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
        simp [ih]
  rw [← hflat]
  exact mem_runBranches_flatMap M fuel xs (fun x => [x]) z

theorem runBranches_iff_runPath
    (M : PolyNTMCandidate)
    (fuel : Nat)
    (c z : NTMConfig M) :
    z ∈ M.machine.runBranches fuel [c] <->
      NTMRunPath M fuel c z := by
  induction fuel generalizing c z with
  | zero =>
      constructor
      · intro h
        simp [NTM.runBranches] at h
        subst z
        exact NTMRunPath.zero c
      · intro h
        cases h with
        | zero =>
            simp [NTM.runBranches]
  | succ fuel ih =>
      by_cases hh : NTMHalted M c
      · rw [runBranches_singleton_succ_halted M fuel c hh]
        constructor
        · intro hz
          exact NTMRunPath.halted hh ((ih c z).mp hz)
        · intro hp
          cases hp with
          | halted _ tail =>
              exact (ih c z).mpr tail
          | active hactive _ _ =>
              exact False.elim (hactive hh)
      · have ha : NTMActive M c := hh
        rw [runBranches_singleton_succ_active M fuel c ha]
        rw [mem_runBranches_list_iff_exists_singleton
              M.machine fuel (M.machine.successors c) z]
        constructor
        · rintro ⟨c1, hc1, hz⟩
          exact NTMRunPath.active ha hc1 ((ih c1 z).mp hz)
        · intro hp
          cases hp with
          | halted hhalt _ =>
              exact False.elim (ha hhalt)
          | active _ hc1 tail =>
              exact ⟨_, hc1, (ih _ _).mpr tail⟩

theorem runBranchesPathEquivalence_closed :
    RunBranchesPathEquivalence := by
  intro M fuel c z
  exact runBranches_iff_runPath M fuel c z

/--
Exact target lemma for the tableau.  It is deliberately stated separately:
the next proof step is the induction relating singleton runBranches membership
to NTMTableauStep paths.
-/
def AcceptsWithinPathEquivalence : Prop :=
  ∀ (M : PolyNTMCandidate) (t : Nat) (c0 : NTMConfig M),
    M.machine.AcceptsWithin t c0 <->
      NTMTableauAcceptingPath M t c0

def PNP_NTM_PATH_OPEN_MATH : Prop :=
  AcceptsWithinPathEquivalence

#print axioms MCore.Real.PNPNTMPathFrontier.mem_runBranches_append

end PNPNTMPathFrontier
end Real
end MCore
