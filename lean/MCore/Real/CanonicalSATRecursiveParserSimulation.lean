import MCore.Real.CanonicalSATRecursiveParserMachine
import MCore.Real.CanonicalSATSlotParserSpec

namespace MCore
namespace Real
namespace CanonicalSATRecursiveParserSimulation

open CanonicalFinalProof
open CanonicalSATParserAttack
open CanonicalSATSlotParserSpec
open CanonicalSATRecursiveParserMachine

/--
Exact remaining proof payload for the concrete Fin 25 parser machine.

The semantic decoder is no longer mentioned here.  The only machine-specific
correctness theorem required is equality with slotAccept, whose equivalence to
decodeCircuit has already been isolated separately.
-/
structure SlotParserMachineSimulationCertificate where
  halts :
    ∀ bits : BitString,
      parserMachine.HaltsWithin
        (parserTimeBound bits.length)
        (initialTMConfig parserMachine bits)

  realizes_slotAccept :
    ∀ bits : BitString,
      parserAccepting
          (parserMachine.run
            (parserTimeBound bits.length)
            (initialTMConfig parserMachine bits)).state = true
        ↔
      slotAccept bits = true

/-- Machine simulation plus the already-isolated semantic slot theorem gives
the exact hardened parser correctness statement. -/
theorem simulation_correct
    (S : SlotParserMachineSimulationCertificate) :
    ParserCorrect := by
  intro bits
  exact
    (S.realizes_slotAccept bits).trans
      (slotAccept_iff_decodeCircuit bits)

/-- The simulation certificate supplies the previous closure-proof payload. -/
def SlotParserMachineSimulationCertificate.toParserClosureProof
    (S : SlotParserMachineSimulationCertificate) :
    ParserClosureProof :=
  { halts := S.halts
    correct := simulation_correct S }

/-- Therefore this one exact simulation object closes the hardened parser gap. -/
def SlotParserMachineSimulationCertificate.toCanonicalCertificate
    (S : SlotParserMachineSimulationCertificate) :
    CanonicalRecursiveParserMachineCertificate :=
  certificateOfClosure S.toParserClosureProof

theorem simulation_closes_operational_gap
    (S : SlotParserMachineSimulationCertificate) :
    CanonicalRecursiveParserOperationalGap := by
  exact ⟨S.toCanonicalCertificate⟩

/-- Exact current parser frontier. -/
def ParserSimulationGap : Prop :=
  Nonempty SlotParserMachineSimulationCertificate

theorem parserSimulationGap_closes
    (h : ParserSimulationGap) :
    CanonicalRecursiveParserOperationalGap := by
  rcases h with ⟨S⟩
  exact simulation_closes_operational_gap S

#print axioms MCore.Real.CanonicalSATRecursiveParserSimulation.simulation_correct
#print axioms MCore.Real.CanonicalSATRecursiveParserSimulation.simulation_closes_operational_gap
#print axioms MCore.Real.CanonicalSATRecursiveParserSimulation.parserSimulationGap_closes

end CanonicalSATRecursiveParserSimulation
end Real
end MCore
