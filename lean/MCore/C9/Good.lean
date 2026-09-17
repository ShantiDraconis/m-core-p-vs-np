import MCore.C9.Mu

namespace MCore
namespace C9

abbrev GoodPredicate := FormulaTree → Restriction → Prop

/-- Deliberately overstrong adversarial candidate. -/
def GoodTrue : GoodPredicate := fun _ _ => True

/-- A candidate bridge is useful only through an explicit positive decrement proof. -/
def PositiveOn (Good : GoodPredicate) : Prop :=
  ∀ t ρ, Good t ρ → 0 < delta ρ t

/-- C3/C7 zero-drop adversary survives in C9, so `Good=True` is scientifically refuted. -/
theorem goodTrue_refuted : ¬ PositiveOn GoodTrue := by
  intro h
  have hp : 0 < delta leavesZeroFree oneInput := h oneInput leavesZeroFree trivial
  have hz : delta leavesZeroFree oneInput = 0 := by
    simp [delta, mu, D, potential, restrictedSimplified, leavesZeroFree,
      oneInput, restrict, simplify, CircuitK1.μ, CircuitK1.size, CircuitK1.depth]
  omega

end C9
end MCore
