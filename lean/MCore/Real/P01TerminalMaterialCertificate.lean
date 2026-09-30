import MCore.Real.P01CoreDecodeFailurePhysical
import MCore.Real.P01RawVerifierFromCoreReject
import MCore.Real.P01MaterialInhabitantFrontier
import MCore.Real.P01FinalCertificate

namespace MCore
namespace Real
namespace P01TerminalMaterialCertificate

open CanonicalFinalProof
open P01FinalCertificate
open P01CoreDecodeFailurePhysical
open P01RawVerifierFromCoreReject
open P01MaterialInhabitantFrontier

/-- Exact no-hypothesis inhabitant of the hardened P01 machine-construction
boundary, obtained from the concrete recursive decoder-rejection producer. -/
theorem p01_closed_no_hypothesis :
    P01ConstructionGap :=
  p01ConstructionGap

/-- The raw checked verifier material core is also inhabited directly from the
same physical decoder-failure producer. -/
theorem raw_verifier_material_core_inhabited :
    Nonempty P01RawVerifierMaterialCore.RawVerifierMaterialCore :=
  ⟨rawVerifierMaterialCoreOfCoreReject coreDecodeFailurePhysicalReject⟩

/-- Material terminal record used only for audit/promotion.  It contains the
actual P01 construction inhabitant rather than an equivalent hypothesis. -/
structure MaterialTerminal : Prop where
  coreReject : P01MalformedRawBoundedReject.CoreDecodeFailurePhysicalReject
  construction : P01ConstructionGap

theorem material_terminal :
    MaterialTerminal where
  coreReject := coreDecodeFailurePhysicalReject
  construction := p01_closed_no_hypothesis

#print axioms MCore.Real.P01TerminalMaterialCertificate.p01_closed_no_hypothesis
#print axioms MCore.Real.P01TerminalMaterialCertificate.raw_verifier_material_core_inhabited
#print axioms MCore.Real.P01TerminalMaterialCertificate.material_terminal

end P01TerminalMaterialCertificate
end Real
end MCore
