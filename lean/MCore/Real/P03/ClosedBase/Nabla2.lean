import Mathlib

namespace MCore.Real.P03.ClosedBase.Nabla2

def X (i j d : ℝ) : ℝ := j - i - 2*d - 1

def v : Fin 3 → ℝ
  | ⟨0, _⟩ => -1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => -2

def Nabla2X2 (a b : Fin 3) : ℝ :=
  2 * v a * v b

theorem hessian_entries :
    Nabla2X2 0 0 = 2 ∧
    Nabla2X2 0 1 = -2 ∧
    Nabla2X2 0 2 = 4 ∧
    Nabla2X2 1 1 = 2 ∧
    Nabla2X2 1 2 = -4 ∧
    Nabla2X2 2 2 = 8 := by
  norm_num [Nabla2X2, v]

theorem rank_one_outer_product (a b : Fin 3) :
    Nabla2X2 a b = 2 * v a * v b := rfl

#print axioms MCore.Real.P03.ClosedBase.Nabla2.hessian_entries
#print axioms MCore.Real.P03.ClosedBase.Nabla2.rank_one_outer_product

end MCore.Real.P03.ClosedBase.Nabla2
