import MCore.CircuitC2

namespace MCore
namespace CircuitC3

open CircuitK1 CircuitC2

/-- C3 uses the already-audited structural potential from C1. -/
abbrev potential (c : Circuit) : Nat := μ c

/-- Exact decrease, truncated at zero. This is descriptive: it does not assert
that a random restriction has positive expected decrease. -/
def drop (ρ : Restriction) (c : Circuit) : Nat :=
  potential c - potential (restrictedSimplified ρ c)

/-- Predicate isolating the genuinely useful event. -/
def StrictDrop (ρ : Restriction) (c : Circuit) : Prop :=
  potential (restrictedSimplified ρ c) < potential c

/-- A concrete strict-potential-drop witness inherited from C2's reduction. -/
theorem reducibleExample_strict_potential_drop :
    StrictDrop fixesZeroTrue reducibleExample := by
  decide

/-- The strict-drop witness has an exact, independently checkable amount. -/
@[simp] theorem reducibleExample_drop_exact :
    drop fixesZeroTrue reducibleExample = 2 := by decide

/-- A free restriction on a single input is a zero-drop adversary. -/
@[simp] theorem free_oneInput_drop_zero :
    drop leavesZeroFree oneInput = 0 := by decide

/-- Therefore universal positive decrease is false even in the formula-tree model. -/
theorem not_every_restriction_strictly_drops :
    ¬ (∀ (ρ : Restriction) (c : Circuit), StrictDrop ρ c) := by
  intro h
  have hs := h leavesZeroFree oneInput
  simp [StrictDrop, potential, restrictedSimplified, simplify, restrict, μ, size, depth,
    leavesZeroFree, oneInput] at hs

/-- C3 deliberately keeps the endpoint firewalls inherited from C2. -/
theorem c3_classical_endpoint_not_promoted : ¬ Nonempty (ProofCertificate k6_dependency.target) :=
  c2_classical_endpoint_not_promoted

theorem c3_k10_not_promoted : ¬ Nonempty (ProofCertificate k10_obligation_node) :=
  c2_k10_not_promoted

end CircuitC3
end MCore
