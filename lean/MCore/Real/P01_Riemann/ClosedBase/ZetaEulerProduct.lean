import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

namespace MCore.Real.P01_Riemann.ClosedBase.ZetaEulerProduct

open Complex
open scoped BigOperators

/-- CLOSED SOURCE: Euler product for zeta in the half-plane Re(s) > 1. -/
theorem zeta_euler_product
    {s : ℂ} (hs : 1 < s.re) :
    HasProd
      (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-s))⁻¹)
      (riemannZeta s) :=
  riemannZeta_eulerProduct_hasProd hs

/-- CLOSED SOURCE: nonvanishing consequence on Re(s) > 1. -/
theorem zeta_nonzero_right_half_plane
    {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re hs

#print axioms MCore.Real.P01_Riemann.ClosedBase.ZetaEulerProduct.zeta_euler_product
#print axioms MCore.Real.P01_Riemann.ClosedBase.ZetaEulerProduct.zeta_nonzero_right_half_plane

end MCore.Real.P01_Riemann.ClosedBase.ZetaEulerProduct
