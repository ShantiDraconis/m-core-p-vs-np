import MCore.Real.P01FinalProofProducer
import MCore.Real.P02FinalProofProducer
import MCore.Real.CookNormalizedG3Contract
import MCore.Real.FinalExternalCertificate

namespace MCore
namespace Real
namespace FinalProofCleanLane

open CanonicalFinalProof
open CanonicalCircuitBits
open P01FinalProofProducer
open P02FinalProofProducer
open CookNormalizedG3Contract
open FinalExternalCertificate

/-- Minimal live payload. G3 is not a blocker here because the existing
cookNormalizedExternalContract supplies the exact G3ExternalContract. -/
structure LiveTwoProducers where
  p01 : P01FinalProofProducer.Producer
  p02 : P02FinalProofProducer.Producer

def LiveTwoProducers.toFinalExternalInputs
    (D : LiveTwoProducers) :
    FinalExternalInputs := by
  have hP01 : SATInNPGap circuitBitEncoding :=
    D.p01.toSATInNP
  have hP02 : P02TerminalFrontier.P02Target :=
    D.p02.toP02Target
  rcases hP02 with ⟨failureGenerator⟩
  exact {
    g1 := hP01
    g2 := failureGenerator
    g3 := cookNormalizedExternalContract
  }

theorem LiveTwoProducers.toOfficialPneqNP
    (D : LiveTwoProducers) :
    OfficialModel.OfficialPneqNP
      cookNormalizedSelection.model.P
      cookNormalizedSelection.model.NP :=
  final_external_certificate D.toFinalExternalInputs

def CleanFinalExternalGap : Prop :=
  Nonempty LiveTwoProducers

/-
Final clean path:

P01MachineConstruction
-> P01FinalProofProducer.Producer
-> SATInNPGap

EffectiveDiagonalCompiler
+ shared Carrier
+ cook_levin_correct
+ same_input_of_fixed
-> P02FinalProofProducer.Producer
-> flips_of_fixed
-> G21Pointwise
-> P02Target

G3:
cookNormalizedExternalContract (already existing)

P01 producer + P02 producer
-> FinalExternalInputs
-> final_external_certificate
-> OfficialPneqNP for the normalized official selection.

No theorem in this file asserts CleanFinalExternalGap.
-/

#print axioms MCore.Real.FinalProofCleanLane.LiveTwoProducers.toOfficialPneqNP

end FinalProofCleanLane
end Real
end MCore
