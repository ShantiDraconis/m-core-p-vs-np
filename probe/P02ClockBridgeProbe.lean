import MCore.Real.P02TerminalForcingG2
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P02ClockBridgeProbe

open CanonicalFinalProof
open P02UniversalFailureWitnessMaterial
open P02TerminalForcingG2

#print MCore.Real.CanonicalFinalProof.PolyDTMCandidate
#print MCore.Real.CanonicalFinalProof.PolyDTMCandidate.CorrectAt
#print MCore.Real.P02UniversalFailureWitnessMaterial.CanonicalSAT
#print MCore.Real.CanonicalSATBoundary.SATBits
#print MCore.Real.CanonicalCircuitBits.circuitBitEncoding

#check PolyDTMCandidate.timeBound
#check PolyDTMCandidate.time_poly
#check PolyDTMCandidate.blank_none
#check MachineRunLemmas.haltsWithin_mono
#check MachineRunLemmas.run_to_larger_fuel_of_halt

example
    (M : PolyDTMCandidate)
    (L : BitLanguage)
    (x : BitString)
    (T' : TimeBound)
    (hmono : M.timeBound x.length ≤ T' x.length)
    (h : M.CorrectAt L x) :
    M.machine.HaltsWithin (T' x.length) (initialTMConfig M.machine x) := by
  exact MachineRunLemmas.haltsWithin_mono M.machine
    (M.timeBound x.length) (T' x.length)
    (initialTMConfig M.machine x) hmono h.1

end P02ClockBridgeProbe
end Real
end MCore
