import MCore.Real.P01FullVerifierStackSemantics
import MCore.Real.CanonicalCircuitBits

namespace MCore
namespace Real
namespace P01FullVerifierReverseDecoderGap

open CircuitK1
open CanonicalCircuitBits
open P01FullVerifierStackSemantics

/-- Exact fail-closed boundary for the still-missing physical reverse decoder.
No inhabitant is asserted here. -/
structure ReverseDecoderCertificate where
  scanReverse : BitString -> List EvalInstr
  correct :
    forall phi : Circuit,
      scanReverse (encodeCircuit phi) = evalProgram phi
  length_bound :
    forall phi : Circuit,
      (scanReverse (encodeCircuit phi)).length <= (encodeCircuit phi).length

def ReverseDecoderGap : Prop :=
  Nonempty ReverseDecoderCertificate

theorem reverse_decoder_length_from_correct
    (R : ReverseDecoderCertificate) (phi : Circuit) :
    (R.scanReverse (encodeCircuit phi)).length <=
      (encodeCircuit phi).length := by
  exact R.length_bound phi

#print axioms MCore.Real.P01FullVerifierReverseDecoderGap.reverse_decoder_length_from_correct

end P01FullVerifierReverseDecoderGap
end Real
end MCore
