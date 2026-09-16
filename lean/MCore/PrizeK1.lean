import MCore.PrizeK0

namespace MCore
namespace PrizeK1

/-- A finite Boolean circuit syntax. `input i` is the i-th input variable. -/
inductive Circuit where
  | input : Nat → Circuit
  | const : Bool → Circuit
  | not : Circuit → Circuit
  | and : Circuit → Circuit → Circuit
  | or : Circuit → Circuit → Circuit
  deriving DecidableEq, Repr

/-- Partial assignments. `none` leaves a variable free. -/
abbrev Restriction := Nat → Option Bool

/-- Restrict a circuit by a partial assignment. This operation substitutes inputs
    but deliberately performs no semantic simplification; that is kept separate
    from the structural theorem certified at K1. -/
def restrict (ρ : Restriction) : Circuit → Circuit
  | .input i => match ρ i with | some b => .const b | none => .input i
  | .const b => .const b
  | .not c => .not (restrict ρ c)
  | .and a b => .and (restrict ρ a) (restrict ρ b)
  | .or a b => .or (restrict ρ a) (restrict ρ b)

/-- Structural gate count. Inputs and constants are leaves of size one. -/
def size : Circuit → Nat
  | .input _ => 1
  | .const _ => 1
  | .not c => size c + 1
  | .and a b => size a + size b + 1
  | .or a b => size a + size b + 1

/-- Depth of the syntax tree. -/
def depth : Circuit → Nat
  | .input _ => 0
  | .const _ => 0
  | .not c => depth c + 1
  | .and a b => max (depth a) (depth b) + 1
  | .or a b => max (depth a) (depth b) + 1

/-- K1's first certified potential is intentionally elementary. It is a
    calibration measure, not the unknown measure needed for a SAT speedup. -/
def μ (c : Circuit) : Nat := size c + depth c

@[simp] theorem restrict_const (ρ : Restriction) (b : Bool) :
    restrict ρ (.const b) = .const b := rfl

@[simp] theorem restrict_not (ρ : Restriction) (c : Circuit) :
    restrict ρ (.not c) = .not (restrict ρ c) := rfl

@[simp] theorem restrict_and (ρ : Restriction) (a b : Circuit) :
    restrict ρ (.and a b) = .and (restrict ρ a) (restrict ρ b) := rfl

@[simp] theorem restrict_or (ρ : Restriction) (a b : Circuit) :
    restrict ρ (.or a b) = .or (restrict ρ a) (restrict ρ b) := rfl

/-- Substitution alone preserves syntactic gate count. -/
theorem size_restrict (ρ : Restriction) (c : Circuit) :
    size (restrict ρ c) = size c := by
  induction c with
  | input i => simp [restrict, size]
  | const b => rfl
  | not c ih => simp [restrict, size, ih]
  | and a b iha ihb => simp [restrict, size, iha, ihb]
  | or a b iha ihb => simp [restrict, size, iha, ihb]

/-- Substitution alone also preserves syntax-tree depth. -/
theorem depth_restrict (ρ : Restriction) (c : Circuit) :
    depth (restrict ρ c) = depth c := by
  induction c with
  | input i => simp [restrict, depth]
  | const b => rfl
  | not c ih => simp [restrict, depth, ih]
  | and a b iha ihb => simp [restrict, depth, iha, ihb]
  | or a b iha ihb => simp [restrict, depth, iha, ihb]

/-- Consequently the calibration potential is invariant under raw substitution.
    Any genuine decrease theorem must therefore include a simplification or a
    stronger structural measure. This is a proved obstruction, not a placeholder. -/
theorem μ_restrict_invariant (ρ : Restriction) (c : Circuit) :
    μ (restrict ρ c) = μ c := by
  simp [μ, size_restrict, depth_restrict]

/-- Concrete falsifier for the overly strong claim that every nonempty
    restriction strictly decreases the raw potential. -/
def fixesZeroTrue : Restriction
  | 0 => some true
  | _ => none

def oneInput : Circuit := .input 0

@[simp] theorem fixesZeroTrue_oneInput :
    restrict fixesZeroTrue oneInput = .const true := rfl

@[simp] theorem raw_potential_does_not_drop :
    μ (restrict fixesZeroTrue oneInput) = μ oneInput :=
  μ_restrict_invariant fixesZeroTrue oneInput

/-- The epistemic boundary from K0 remains intact after adding concrete circuit
    syntax and proved restriction laws. -/
theorem k1_classical_endpoint_not_promoted :
    ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  prize_k0_classical_endpoint_not_promoted

theorem k1_k10_not_promoted :
    ¬ Nonempty (ProofCertificate k10_obligation_node) :=
  prize_k0_k10_not_promoted

end PrizeK1
end MCore
