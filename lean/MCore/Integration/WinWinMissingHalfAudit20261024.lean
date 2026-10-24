import MCore.Integration.WinWinLogic20261024
import MCore.Real.P03PerfectFlipDichotomy

/-!
# Win-win audit of the P03 dichotomy

The only global dichotomy of the P vs NP repository is

  `rangeFailureLaw_or_existsPerfectFlip : RangeFailureLaw ∨ ExistsPerfectFlip`

and its first half `RangeFailureLaw → ¬ InP CanonicalSAT` is present.  The
missing second half `ExistsPerfectFlip → ¬ InP CanonicalSAT` is equivalent to
`¬ InP CanonicalSAT` itself, because every polynomial-time SAT decider is a
perfect-flip candidate (`canonicalSAT_inP_implies_existsPerfectFlip`).

No new hypothesis is introduced and nothing is claimed about
`¬ InP CanonicalSAT`.
-/

namespace MCore
namespace Integration
namespace WinWinMissingHalfAudit20261024

open WinWinLogic20261024
open MCore.Real
open MCore.Real.CanonicalFinalProof
open MCore.Real.P03RangeFailureFrontier
open MCore.Real.P03PerfectFlipDichotomy

/-- The P vs NP target of the repository's final chain. -/
abbrev SATNotInP : Prop :=
  ¬ InP PNPCookLevinMaterialMinCut.CanonicalSAT

/-- The half that exists in the repository. -/
theorem present_half : RangeFailureLaw → SATNotInP :=
  rangeFailureLaw_implies_canonicalSAT_not_inP

/-- The half that is missing is exactly the open target. -/
theorem perfectFlip_missing_half_iff_target :
    (ExistsPerfectFlip → SATNotInP) ↔ SATNotInP :=
  missing_half_iff_target canonicalSAT_inP_implies_existsPerfectFlip Iff.rfl

/-- A win-win over the repository dichotomy is equivalent to the target. -/
theorem winwin_over_p03_iff_target :
    ((RangeFailureLaw → SATNotInP) ∧ (ExistsPerfectFlip → SATNotInP)) ↔
      SATNotInP := by
  constructor
  · rintro ⟨_, hNeg⟩
    exact perfectFlip_missing_half_iff_target.mp hNeg
  · intro h
    exact ⟨present_half, fun _ => h⟩

/-- The closure through the dichotomy is the case split. -/
theorem winwin_over_p03_closes
    (hNeg : ExistsPerfectFlip → SATNotInP) : SATNotInP := by
  rcases rangeFailureLaw_or_existsPerfectFlip with h | h
  · exact present_half h
  · exact hNeg h

end WinWinMissingHalfAudit20261024
end Integration
end MCore

#print axioms MCore.Integration.WinWinMissingHalfAudit20261024.present_half
#print axioms MCore.Integration.WinWinMissingHalfAudit20261024.perfectFlip_missing_half_iff_target
#print axioms MCore.Integration.WinWinMissingHalfAudit20261024.winwin_over_p03_iff_target
#print axioms MCore.Integration.WinWinMissingHalfAudit20261024.winwin_over_p03_closes
