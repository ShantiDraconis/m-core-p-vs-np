import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace MCore.Real.P01_Riemann.ClosedBase.ZetaAnalytic

open Complex

/-- CLOSED SOURCE: the pole-subtracted completed Riemann zeta is entire. -/
theorem completed_zeta0_entire :
    Differentiable ℂ completedRiemannZeta₀ :=
  differentiable_completedZeta₀

/-- CLOSED SOURCE: riemannZeta is differentiable away from its pole at 1. -/
theorem zeta_differentiable_away_from_one
    {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ riemannZeta s :=
  differentiableAt_riemannZeta hs

#print axioms MCore.Real.P01_Riemann.ClosedBase.ZetaAnalytic.completed_zeta0_entire
#print axioms MCore.Real.P01_Riemann.ClosedBase.ZetaAnalytic.zeta_differentiable_away_from_one

end MCore.Real.P01_Riemann.ClosedBase.ZetaAnalytic
