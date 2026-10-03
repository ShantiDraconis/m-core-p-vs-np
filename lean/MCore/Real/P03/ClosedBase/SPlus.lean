import Mathlib

namespace MCore.Real.P03.ClosedBase.SPlus

def SPlus (X Ai Aj : ℝ) : ℝ :=
  X^2 + (Ai - 1)^2 + (Aj - 1)^2

theorem splus_nonneg (X Ai Aj : ℝ) :
    0 ≤ SPlus X Ai Aj := by
  unfold SPlus
  positivity

theorem splus_eq_zero_iff (X Ai Aj : ℝ) :
    SPlus X Ai Aj = 0 ↔ X = 0 ∧ Ai = 1 ∧ Aj = 1 := by
  unfold SPlus
  constructor
  · intro h
    have hX : X = 0 := by nlinarith [sq_nonneg X, sq_nonneg (Ai - 1), sq_nonneg (Aj - 1)]
    have hAi : Ai = 1 := by nlinarith [sq_nonneg X, sq_nonneg (Ai - 1), sq_nonneg (Aj - 1)]
    have hAj : Aj = 1 := by nlinarith [sq_nonneg X, sq_nonneg (Ai - 1), sq_nonneg (Aj - 1)]
    exact ⟨hX, hAi, hAj⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

#print axioms MCore.Real.P03.ClosedBase.SPlus.splus_eq_zero_iff

end MCore.Real.P03.ClosedBase.SPlus
