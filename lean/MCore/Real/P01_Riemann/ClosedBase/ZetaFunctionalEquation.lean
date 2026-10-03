import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace MCore.Real.P01_Riemann.ClosedBase.ZetaFunctionalEquation

open Complex

/-- CLOSED SOURCE: functional equation for the completed Riemann zeta. -/
theorem completed_zeta_reflection (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s :=
  completedRiemannZeta_one_sub s

/-- CLOSED SOURCE: entire pole-subtracted completion has the same reflection symmetry. -/
theorem completed_zeta0_reflection (s : ℂ) :
    completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s :=
  completedRiemannZeta₀_one_sub s

#print axioms MCore.Real.P01_Riemann.ClosedBase.ZetaFunctionalEquation.completed_zeta_reflection
#print axioms MCore.Real.P01_Riemann.ClosedBase.ZetaFunctionalEquation.completed_zeta0_reflection

end MCore.Real.P01_Riemann.ClosedBase.ZetaFunctionalEquation
