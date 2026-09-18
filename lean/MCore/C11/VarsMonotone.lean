import MCore.C10.RestrictionProgress

namespace MCore
namespace C11

open C9 C10 CircuitK1 CircuitC2

/-- For natural-number variable identifiers, `eraseDups` is duplicate-free.
This local proof keeps C11 independent of any external finite-set library. -/
theorem eraseDups_nodup_nat : ∀ l : List Nat, l.eraseDups.Nodup
  | [] => by simp
  | a :: as => by
      rw [List.eraseDups_cons]
      constructor
      · simp
      · exact eraseDups_nodup_nat (as.filter fun b => !b == a)
termination_by l => l.length
decreasing_by
  simp only [List.length_cons]
  have hle := List.length_filter_le (fun b => !b == a) as
  omega

/-- Inclusion of underlying elements cannot increase the number of distinct
natural-number identifiers. -/
theorem eraseDups_length_le_of_subset
    {l₁ l₂ : List Nat} (h : l₁ ⊆ l₂) :
    l₁.eraseDups.length ≤ l₂.eraseDups.length := by
  apply List.Nodup.length_le_of_subset (eraseDups_nodup_nat l₁)
  intro x hx
  have hx₁ : x ∈ l₁ := by simpa using hx
  have hx₂ : x ∈ l₂ := h hx₁
  simpa using hx₂

/-- Restriction can replace an input by a constant, but cannot introduce a new
syntactic input identifier. -/
theorem mem_freeVarList_restrict
    {x : Nat} (ρ : Restriction) (t : FormulaTree)
    (hx : x ∈ freeVarList (restrict ρ t)) :
    x ∈ freeVarList t := by
  induction t with
  | input i =>
      cases h : ρ i <;> simp [restrict, freeVarList, h] at hx ⊢
      exact hx
  | const b =>
      simp [restrict, freeVarList] at hx
  | not c ih =>
      exact ih (by simpa [restrict, freeVarList] using hx)
  | and a b iha ihb =>
      simp [restrict, freeVarList] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (iha hx)
      · exact Or.inr (ihb hx)
  | or a b iha ihb =>
      simp [restrict, freeVarList] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (iha hx)
      · exact Or.inr (ihb hx)

/-- The certified simplifier can delete branches and constants, but cannot
invent a new syntactic input identifier. -/
theorem mem_freeVarList_simplify
    {x : Nat} (t : FormulaTree)
    (hx : x ∈ freeVarList (simplify t)) :
    x ∈ freeVarList t := by
  induction t with
  | input i =>
      simpa [simplify, freeVarList] using hx
  | const b =>
      simp [simplify, freeVarList] at hx
  | not c ih =>
      simp only [simplify] at hx
      cases h : simplify c with
      | const b =>
          simp [h, freeVarList] at hx
      | input i =>
          apply ih
          rw [h]
          simpa [freeVarList] using hx
      | not d =>
          apply ih
          rw [h]
          simpa [freeVarList] using hx
      | and a b =>
          apply ih
          rw [h]
          simpa [freeVarList] using hx
      | or a b =>
          apply ih
          rw [h]
          simpa [freeVarList] using hx
  | and a b iha ihb =>
      simp only [simplify] at hx
      cases ha : simplify a <;> cases hb : simplify b <;>
        (try split) <;> simp_all [freeVarList]
  | or a b iha ihb =>
      simp only [simplify] at hx
      cases ha : simplify a <;> cases hb : simplify b <;>
        (try split) <;> simp_all [freeVarList]

/-- The full C9 map `D = simplify ∘ restrict` never introduces a free variable. -/
theorem mem_freeVarList_D
    {x : Nat} (ρ : Restriction) (t : FormulaTree)
    (hx : x ∈ freeVarList (D ρ t)) :
    x ∈ freeVarList t := by
  have hs : x ∈ freeVarList (restrict ρ t) := by
    apply mem_freeVarList_simplify (restrict ρ t)
    simpa [D] using hx
  exact mem_freeVarList_restrict ρ t hs

/-- C11 closes the first C10 bridge: the number of distinct syntactic variables
is globally nonincreasing under restriction followed by simplification. -/
theorem vars_D_le (ρ : Restriction) (t : FormulaTree) :
    vars (D ρ t) ≤ vars t := by
  unfold vars
  apply eraseDups_length_le_of_subset
  intro x hx
  exact mem_freeVarList_D ρ t hx

theorem varsNonincrease_closed : VarsNonincreaseObligation := by
  intro ρ t
  exact vars_D_le ρ t

/-- After C11, C10's rank theorem needs only strict progress: either a strict
variable-count decrease or positive certified potential decrement. -/
def StrictRestrictionProgress (ρ : Restriction) (t : FormulaTree) : Prop :=
  vars (D ρ t) < vars t ∨ 0 < delta ρ t

theorem restrictionProgress_of_strict
    (ρ : Restriction) (t : FormulaTree)
    (h : StrictRestrictionProgress ρ t) :
    RestrictionProgress ρ t :=
  ⟨vars_D_le ρ t, h⟩

theorem stateRank_D_decreases_of_strict
    (ρ : Restriction) (t : FormulaTree)
    (h : StrictRestrictionProgress ρ t) :
    stateRank (D ρ t) < stateRank t :=
  stateRank_D_decreases_of_restriction_progress
    ρ t (restrictionProgress_of_strict ρ t h)

theorem c11_classical_endpoint_not_promoted :
    ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  c10_classical_endpoint_not_promoted

theorem c11_k10_not_promoted :
    ¬ Nonempty (ProofCertificate k10_obligation_node) :=
  c10_k10_not_promoted

end C11
end MCore
