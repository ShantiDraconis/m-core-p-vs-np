import MCore.Real.P01_Riemann.ClosedBase.ZetaAnalytic
import MCore.Real.P01_Riemann.ClosedBase.ZetaFunctionalEquation
import MCore.Real.P01_Riemann.ClosedBase.ZetaEulerProduct

namespace MCore.Real.P01_Riemann.OpenBridge.BoundedZeroCandidate

open Complex

/--
A nontrivial zeta-zero candidate in a bounded vertical window.
This is a local source-middle type.  It does not assert finiteness of the
candidate type; a separate analytic compact-zero finiteness theorem is still
required before treating the window as an effectively finite search space.
-/
structure Candidate (T : ℝ) where
  s : ℂ
  h_zero : riemannZeta s = 0
  h_window : |s.im| ≤ T
  h_strip : 0 < s.re ∧ s.re < 1

def InWindow (T : ℝ) (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ |s.im| ≤ T ∧ 0 < s.re ∧ s.re < 1

theorem candidate_iff_inWindow
    {T : ℝ} (C : Candidate T) :
    InWindow T C.s := by
  exact ⟨C.h_zero, C.h_window, C.h_strip.1, C.h_strip.2⟩

#print axioms MCore.Real.P01_Riemann.OpenBridge.BoundedZeroCandidate.candidate_iff_inWindow

end MCore.Real.P01_Riemann.OpenBridge.BoundedZeroCandidate
