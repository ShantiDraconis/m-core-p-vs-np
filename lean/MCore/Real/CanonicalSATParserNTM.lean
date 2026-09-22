import MCore.Real.CanonicalSATRecursiveParserSimulation

namespace MCore
namespace Real
namespace CanonicalSATParserNTM

open CanonicalFinalProof
open CanonicalCircuitBits
open CanonicalSATParserMachine
open CanonicalSATSlotParserSpec
open CanonicalSATRecursiveParserSimulation

/-- Deterministic parser embedded as a singleton-branch NTM.
    This introduces no second parser semantics: every active NTM step is
    exactly one step of parserMachine. -/
def parserNTM : NTM (Fin 25) (Option Bool) :=
  { initial := parserMachine.initial
    blank := none
    transition := fun q symbol => [parserMachine.transition q symbol]
    accepting := parserAccepting
    rejecting := fun q => q == 24 }

@[simp] theorem parserNTM_blank_none :
    parserNTM.blank = none := rfl

@[simp] theorem parserNTM_initial :
    parserNTM.initial = (0 : Fin 25) := rfl

@[simp] theorem parserNTM_terminal_eq_parser_halt
    (q : Fin 25) :
    (parserNTM.accepting q || parserNTM.rejecting q) =
      parserMachine.halting q := by
  rfl

theorem parserNTM_stepBranch_eq_parser_step
    (config : Configuration (Fin 25) (Option Bool)) :
    parserNTM.stepBranch config
        (parserMachine.transition config.state config.tape.head) =
      parserMachine.step config := by
  simp [parserNTM, NTM.stepBranch, TM.step]

theorem parserNTM_successors_singleton
    (config : Configuration (Fin 25) (Option Bool)) :
    parserNTM.successors config = [parserMachine.step config] := by
  simp [NTM.successors, parserNTM,
    parserNTM_stepBranch_eq_parser_step]

/-- Singleton-branch execution is extensionally identical to deterministic
    parserMachine.run, including preservation of halted configurations. -/
theorem parserNTM_runBranches_singleton
    (fuel : Nat)
    (config : Configuration (Fin 25) (Option Bool)) :
    parserNTM.runBranches fuel [config] =
      [parserMachine.run fuel config] := by
  induction fuel generalizing config with
  | zero =>
      rfl
  | succ fuel ih =>
      cases hhalt : parserMachine.halting config.state with
      | false =>
          simp [NTM.runBranches, parserNTM_terminal_eq_parser_halt,
            hhalt, parserNTM_successors_singleton, TM.run, ih]
      | true =>
          have hrun :
              parserMachine.run (fuel + 1) config = config := by
            simp [TM.run, hhalt]
          simp [NTM.runBranches, parserNTM_terminal_eq_parser_halt,
            hhalt, ih, hrun]

theorem parserNTM_haltsWithin_iff
    (fuel : Nat)
    (config : Configuration (Fin 25) (Option Bool)) :
    parserNTM.HaltsWithin fuel config ↔
      parserMachine.HaltsWithin fuel config := by
  simp [NTM.HaltsWithin, TM.HaltsWithin,
    parserNTM_runBranches_singleton,
    parserNTM_terminal_eq_parser_halt]

theorem parserNTM_acceptsWithin_iff
    (fuel : Nat)
    (config : Configuration (Fin 25) (Option Bool)) :
    parserNTM.AcceptsWithin fuel config ↔
      parserAccepting (parserMachine.run fuel config).state = true := by
  simp [NTM.AcceptsWithin, parserNTM_runBranches_singleton, parserNTM]

/-- A completed Fin-25 parser simulation can be reused directly as the parser
    phase of an integrated canonical NTM. -/
structure ParserNTMPhaseCertificate where
  halts :
    ∀ bits : BitString,
      parserNTM.HaltsWithin
        (parserTimeBound bits.length)
        (initialNTMConfig parserNTM bits)
  accepts_iff_decode :
    ∀ bits : BitString,
      parserNTM.AcceptsWithin
          (parserTimeBound bits.length)
          (initialNTMConfig parserNTM bits) ↔
        ∃ c : CircuitK1.Circuit,
          decodeCircuit bits = some c

def SlotParserMachineSimulationCertificate.toNTMPhase
    (S : SlotParserMachineSimulationCertificate) :
    ParserNTMPhaseCertificate := by
  refine
    { halts := ?_
      accepts_iff_decode := ?_ }
  · intro bits
    rw [parserNTM_haltsWithin_iff]
    exact S.halts bits
  · intro bits
    rw [parserNTM_acceptsWithin_iff]
    exact
      (S.realizes_slotAccept bits).trans
        (slotAccept_iff_decodeCircuit bits)

theorem parserSimulationGap_to_ntm_phase
    (h : ParserSimulationGap) :
    Nonempty ParserNTMPhaseCertificate := by
  rcases h with ⟨S⟩
  exact ⟨S.toNTMPhase⟩

#print axioms MCore.Real.CanonicalSATParserNTM.parserNTM_runBranches_singleton
#print axioms MCore.Real.CanonicalSATParserNTM.parserNTM_haltsWithin_iff
#print axioms MCore.Real.CanonicalSATParserNTM.parserNTM_acceptsWithin_iff
#print axioms MCore.Real.CanonicalSATParserNTM.SlotParserMachineSimulationCertificate.toNTMPhase
#print axioms MCore.Real.CanonicalSATParserNTM.parserSimulationGap_to_ntm_phase

end CanonicalSATParserNTM
end Real
end MCore
