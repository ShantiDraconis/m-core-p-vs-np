import MCore.CircuitK1

namespace MCore
namespace CircuitC2

open CircuitK1

abbrev Assignment := Nat → Bool

def eval (σ : Assignment) : Circuit → Bool
  | .input i => σ i
  | .const b => b
  | .not c => !(eval σ c)
  | .and a b => (eval σ a) && (eval σ b)
  | .or a b => (eval σ a) || (eval σ b)

def merge (ρ : Restriction) (σ : Assignment) : Assignment := fun i =>
  match ρ i with
  | some b => b
  | none => σ i

@[simp] theorem merge_some (ρ : Restriction) (σ : Assignment) (i : Nat) (b : Bool)
    (h : ρ i = some b) : merge ρ σ i = b := by simp [merge, h]

@[simp] theorem merge_none (ρ : Restriction) (σ : Assignment) (i : Nat)
    (h : ρ i = none) : merge ρ σ i = σ i := by simp [merge, h]

theorem eval_restrict (ρ : Restriction) (σ : Assignment) (c : Circuit) :
    eval σ (restrict ρ c) = eval (merge ρ σ) c := by
  induction c with
  | input i => cases h : ρ i <;> simp [restrict, eval, merge, h]
  | const b => rfl
  | not c ih => simp [restrict, eval, ih]
  | and a b iha ihb => simp [restrict, eval, iha, ihb]
  | or a b iha ihb => simp [restrict, eval, iha, ihb]

def simplify : Circuit → Circuit
  | .input i => .input i
  | .const b => .const b
  | .not c =>
      match simplify c with
      | .const b => .const (!b)
      | d => .not d
  | .and a b =>
      match simplify a, simplify b with
      | .const false, _ => .const false
      | _, .const false => .const false
      | .const true, d => d
      | d, .const true => d
      | d, e => .and d e
  | .or a b =>
      match simplify a, simplify b with
      | .const true, _ => .const true
      | _, .const true => .const true
      | .const false, d => d
      | d, .const false => d
      | d, e => .or d e

/-- Simplification never increases formula-tree size. -/
theorem size_simplify_le (c : Circuit) : size (simplify c) ≤ size c := by
  induction c with
  | input i => simp [simplify, size]
  | const b => simp [simplify, size]
  | not c ih =>
      simp only [simplify]
      cases h : simplify c <;> simp_all [size]
  | and a b iha ihb =>
      simp only [simplify]
      cases ha : simplify a <;> cases hb : simplify b <;>
        simp_all [size] <;> split <;> simp_all [size] <;> omega
  | or a b iha ihb =>
      simp only [simplify]
      cases ha : simplify a <;> cases hb : simplify b <;>
        simp_all [size] <;> split <;> simp_all [size] <;> omega

/-- Simplification never increases formula-tree depth. -/
theorem depth_simplify_le (c : Circuit) : depth (simplify c) ≤ depth c := by
  induction c with
  | input i => simp [simplify, depth]
  | const b => simp [simplify, depth]
  | not c ih =>
      simp only [simplify]
      cases h : simplify c <;> simp_all [depth] <;> omega
  | and a b iha ihb =>
      simp only [simplify]
      cases ha : simplify a <;> cases hb : simplify b <;>
        simp_all [depth] <;> split <;> simp_all [depth] <;> omega
  | or a b iha ihb =>
      simp only [simplify]
      cases ha : simplify a <;> cases hb : simplify b <;>
        simp_all [depth] <;> split <;> simp_all [depth] <;> omega

/-- The C1 structural potential is monotone under simplification. -/
theorem μ_simplify_le (c : Circuit) : μ (simplify c) ≤ μ c := by
  unfold μ
  exact Nat.add_le_add (size_simplify_le c) (depth_simplify_le c)

/-- Semantic preservation. Boolean payloads of constant children are split
explicitly; this is an audited elaboration requirement, not left to `simp`. -/
theorem eval_simplify (σ : Assignment) (c : Circuit) : eval σ (simplify c) = eval σ c := by
  induction c with
  | input i => rfl
  | const b => rfl
  | not c ih =>
      simp only [simplify]
      cases h : simplify c with
      | input i => simp_all [eval]
      | const b => cases b <;> simp_all [eval]
      | not d => simp_all [eval]
      | and a b => simp_all [eval]
      | or a b => simp_all [eval]
  | and a b iha ihb =>
      simp only [simplify]
      cases ha : simplify a <;> cases hb : simplify b <;>
        simp_all [eval] <;> split <;> simp_all [eval]
  | or a b iha ihb =>
      simp only [simplify]
      cases ha : simplify a <;> cases hb : simplify b <;>
        simp_all [eval] <;> split <;> simp_all [eval]

def restrictedSimplified (ρ : Restriction) (c : Circuit) : Circuit :=
  simplify (restrict ρ c)

theorem eval_restrictedSimplified (ρ : Restriction) (σ : Assignment) (c : Circuit) :
    eval σ (restrictedSimplified ρ c) = eval (merge ρ σ) c := by
  rw [restrictedSimplified, eval_simplify, eval_restrict]

end CircuitC2
end MCore
