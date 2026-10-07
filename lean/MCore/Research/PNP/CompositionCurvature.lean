import Mathlib

namespace MCore.Research.PNP

structure CostedArrow (α : Type) where
  run : α → α
  cost : ℕ

def compose {α : Type} (g f : CostedArrow α) : CostedArrow α where
  run := g.run ∘ f.run
  cost := f.cost + g.cost

def scalarCurvature {α : Type} (g f : CostedArrow α) : ℤ :=
  (compose g f).cost - f.cost - g.cost

theorem scalarCurvature_eq_zero {α : Type} (g f : CostedArrow α) :
    scalarCurvature g f = 0 := by
  unfold scalarCurvature compose
  omega

end MCore.Research.PNP
