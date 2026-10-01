import MCore.Real.P01RawClosureFinal
import MCore.Real.P02OperatorKernel
import MCore.Real.P02TerminalFrontier

namespace MCore
namespace Real
namespace P02FinalCompression

open CanonicalFinalProof
open CanonicalSATBoundary
open CanonicalCircuitBits
open P01FinalCertificate
open P01RawClosureFinal
open P02OperatorKernel
open P02TerminalFrontier

/-- Recovered no-hypothesis P01 inhabitant. -/
theorem p01_closed :
    P01ConstructionGap :=
  p01ConstructionGap_closed

/-- P01 supplies the canonical SAT-in-NP side. -/
theorem canonical_sat_in_np :
    SATInNPGap circuitBitEncoding :=
  construction_closes_p01 p01_closed

/-- A genuine P02 operator plus the recovered P01 construction closes the
internal separation endpoint. -/
theorem canonical_p02_operator_closes
    (P : CanonicalSATP02Producer) :
    PneqNP := by
  have hFail : UniversalFailure (SATBits circuitBitEncoding) :=
    (p02Producer_iff_universalFailure).mp ⟨P⟩
  exact target_failure_implies_p_ne_np canonical_sat_in_np hFail

/-- Exact final residual after all recovered material is incorporated. -/
abbrev FINAL_OPEN_MATH : Prop :=
  Nonempty CanonicalSATP02Producer

theorem final_open_math_iff_sat_not_in_p :
    FINAL_OPEN_MATH ↔
      ¬ InP (SATBits circuitBitEncoding) :=
  canonicalSATProducer_iff_notInP

theorem final_open_math_closes
    (h : FINAL_OPEN_MATH) :
    PneqNP := by
  rcases h with ⟨P⟩
  exact canonical_p02_operator_closes P

end P02FinalCompression
end Real
end MCore
