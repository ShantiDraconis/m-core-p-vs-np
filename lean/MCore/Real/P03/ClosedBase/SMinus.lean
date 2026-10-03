import Mathlib

namespace MCore.Real.P03.ClosedBase.SMinus

def SMinus (X Ai Aj : ℝ) : ℝ :=
  X^2 + Ai^2 + Aj^2

theorem sminus_nonneg (X Ai Aj : ℝ) :
    0 ≤ SMinus X Ai Aj := by
  unfold SMinus
  positivity

theorem sminus_eq_zero_iff (X Ai Aj : ℝ) :
    SMinus X Ai Aj = 0 ↔ X = 0 ∧ Ai = 0 ∧ Aj = 0 := by
  unfold SMinus
  constructor
  · intro h
    have hX : X = 0 := by nlinarith [sq_nonneg X, sq_nonneg Ai, sq_nonneg Aj]
    have hAi : Ai = 0 := by nlinarith [sq_nonneg X, sq_nonneg Ai, sq_nonneg Aj]
    have hAj : Aj = 0 := by nlinarith [sq_nonneg X, sq_nonneg Ai, sq_nonneg Aj]
    exact ⟨hX, hAi, hAj⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

#print axioms MCore.Real.P03.ClosedBase.SMinus.sminus_eq_zero_iff

end MCore.Real.P03.ClosedBase.SMinus
