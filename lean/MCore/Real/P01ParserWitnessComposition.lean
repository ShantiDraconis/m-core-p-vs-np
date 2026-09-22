import MCore.Real.CanonicalSATParserNTM
import MCore.Real.CanonicalSATWitnessGuessNTM

namespace MCore
namespace Real
namespace P01ParserWitnessComposition

open CanonicalFinalProof
open CanonicalSATRecursiveParserSimulation
open CanonicalSATParserNTM
open CanonicalSATWitnessGuessNTM

/-- Reuse boundary for T1.B: the parser NTM phase and the concrete witness
guesser both exist without inventing a second parser or guesser. -/
structure ParserWitnessAvailable where
  parserPhase : ParserNTMPhaseCertificate
  guesser : NTM (Fin 2) (Option Bool)
  guesser_is_canonical : guesser = witnessGuessMachine

def available_of_parser_simulation
    (S : SlotParserMachineSimulationCertificate) :
    ParserWitnessAvailable :=
  { parserPhase := simulationToNTMPhase S
    guesser := witnessGuessMachine
    guesser_is_canonical := rfl }

/-- Exact remaining T1.B boundary: a single integrated finite-control NTM
that continues from the certified parser phase into witness generation. -/
def ParserWitnessCompositionGap : Prop :=
  ∃ stateCount : Nat,
    Nonempty (NTM (Fin (stateCount + 1)) (Option Bool))

#print axioms MCore.Real.P01ParserWitnessComposition.available_of_parser_simulation

end P01ParserWitnessComposition
end Real
end MCore
