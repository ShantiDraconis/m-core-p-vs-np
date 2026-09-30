import MCore.Real.P01CoreDecodeFailurePhysical
import MCore.Real.P01FinalCertificate

namespace MCore
namespace Real
namespace P01TerminalCertificate

open P01FinalCertificate
open P01CoreDecodeFailurePhysical

/-- Terminal P01 inhabitant.  This theorem adds no premise and merely exposes
the fully constructed machine-level inhabitant from the physical decoder
failure proof chain. -/
theorem p01ConstructionGap :
    P01ConstructionGap :=
  P01CoreDecodeFailurePhysical.p01ConstructionGap

/-- The constructed P01 machine therefore supplies the canonical SAT machine
closure used by the downstream P-vs-NP lane.  This is only the SAT-in-NP/P01
side; it does not assert G21Pointwise or P != NP. -/
theorem canonicalSATMachineClosure :
    CanonicalSATNTMAttack.CanonicalSATMachineClosure :=
  construction_closes_p01 p01ConstructionGap

#print axioms MCore.Real.P01TerminalCertificate.p01ConstructionGap
#print axioms MCore.Real.P01TerminalCertificate.canonicalSATMachineClosure

end P01TerminalCertificate
end Real
end MCore
