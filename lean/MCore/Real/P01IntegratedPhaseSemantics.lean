import MCore.Real.P01IntegratedMachine
import MCore.Real.P01FullVerifierMachine
import MCore.Real.P01FullVerifierPhysical

namespace MCore
namespace Real
namespace P01IntegratedPhaseSemantics

open CanonicalFinalProof
open P01WitnessPreservingPrep
open P01FullVerifierMachine
open P01FullVerifierPhysical

@[simp] theorem verifier_input_is_prepared
    (w source : BitString) :
    verifierInputTape w source = preparedTape w source := by
  rfl

theorem prepared_nonempty_to_scanner_config
    (w : BitString) (b : Bool) (bs : BitString) :
    verifierInputTape w (b :: bs) =
      { left := none :: w.map some
        head := some b
        right := bs.map some ++ [none] } := by
  rfl

theorem verifier_source_end_layout
    (w source : BitString) :
    sourceEndScanner.run (source.length + 1)
      (scanConfig (none :: w.map some) source) =
      { state := (1 : Fin 2),
        tape :=
          { left := source.reverse.map some ++ none :: w.map some,
            head := none,
            right := [] } } := by
  exact source_end_preserves_witness_and_source w source

/-- The semantic phase boundary now has a single canonical tape layout shared
by witness preparation and the full verifier. -/
structure CanonicalPhaseLayoutCertificate where
  witness_to_verifier :
    ∀ w source : BitString,
      verifierInputTape w source = preparedTape w source
  source_end :
    ∀ w source : BitString,
      sourceEndScanner.run (source.length + 1)
        (scanConfig (none :: w.map some) source) =
        { state := (1 : Fin 2),
          tape :=
            { left := source.reverse.map some ++ none :: w.map some,
              head := none,
              right := [] } }

def canonicalPhaseLayoutCertificate : CanonicalPhaseLayoutCertificate where
  witness_to_verifier := verifier_input_is_prepared
  source_end := verifier_source_end_layout

#print axioms MCore.Real.P01IntegratedPhaseSemantics.canonicalPhaseLayoutCertificate

end P01IntegratedPhaseSemantics
end Real
end MCore
