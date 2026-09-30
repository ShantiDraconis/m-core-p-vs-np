import MCore.Real.P01CheckedVerifierGlobalCoreV2
import MCore.Real.P01ExactVerifierCanonicalRun

namespace MCore
namespace Real
namespace P01RawGlobalMinCut

open CanonicalFinalProof
open CanonicalCircuitBits
open P01GuessedWitnessRelation
open P01WitnessPreservingPrep
open P01CheckedVerifierCompositeNTM
open P01CheckedVerifierGlobalCoreV2
open P01ExactVerifierGlobalBudget
open P01ExactVerifierCanonicalRun

/-- Exact residual P01 mechanical producer.

Everything on a source accepted by decodeCircuit is already discharged by the
exact canonical global run.  Therefore only decoder failure remains: the fixed
physical verifier must halt fail-closed at the same cubic fuel.

No machine, parser, endpoint proposition, or SAT lower bound is stored here. -/
structure RawDecodeNoneCore where
  halts :
    ∀ (bs w : BitString),
      decodeCircuit bs = none →
      checkedVerifierMachine.HaltsWithin
        (checkedVerifierExactTimeBound bs.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape w bs }
  not_accepts :
    ∀ (bs w : BitString),
      decodeCircuit bs = none →
      ¬ checkedVerifierMachine.AcceptsWithin
        (checkedVerifierExactTimeBound bs.length)
        { state := checkedVerifierMachine.initial,
          tape := preparedTape w bs }

/-- Decoder failure makes VerifyBits definitionally impossible. -/
theorem verifyBits_false_of_decode_none
    (bs w : BitString)
    (hdec : decodeCircuit bs = none) :
    ¬ VerifyBits bs w := by
  intro h
  rcases h with ⟨phi, hphi, _, _⟩
  rw [hdec] at hphi
  contradiction

/-- Exact source split used by the final mechanical closure. -/
theorem exact_encoding_or_decode_none
    (bs : BitString) :
    (∃ phi : CircuitK1.Circuit, bs = encodeCircuit phi) ∨
      decodeCircuit bs = none := by
  cases hdec : decodeCircuit bs with
  | none =>
      exact Or.inr hdec
  | some phi =>
      exact Or.inl ⟨phi, decodeCircuit_sound bs phi hdec⟩

/-- Once the raw decoder-failure producer is supplied, the fixed-machine global
execution core is fully inhabited.  Canonical sources use only already-proved
exact global theorems. -/
def globalCoreOfRaw
    (R : RawDecodeNoneCore) :
    CheckedVerifierGlobalCore where
  timeBound := checkedVerifierExactTimeBound
  time_poly := checkedVerifierExactTimeBound_poly
  halts := by
    intro bs w hw
    cases hdec : decodeCircuit bs with
    | none =>
        exact R.halts bs w hdec
    | some phi =>
        have hsrc : bs = encodeCircuit phi :=
          decodeCircuit_sound bs phi hdec
        have hvar : varBound phi ≤ w.length := by
          have hb : varBound phi ≤ bs.length :=
            varBound_le_of_decode bs phi hdec
          omega
        subst bs
        exact prepared_canonical_halts_within_exact_global
          w phi hvar
  correct := by
    intro bs w hw
    cases hdec : decodeCircuit bs with
    | none =>
        constructor
        · intro hacc
          exact (R.not_accepts bs w hdec) hacc
        · intro hver
          exact False.elim
            ((verifyBits_false_of_decode_none bs w hdec) hver)
    | some phi =>
        have hsrc : bs = encodeCircuit phi :=
          decodeCircuit_sound bs phi hdec
        have hvar : varBound phi ≤ w.length := by
          have hb : varBound phi ≤ bs.length :=
            varBound_le_of_decode bs phi hdec
          omega
        subst bs
        exact prepared_canonical_accepts_iff_exact_global
          w phi hvar

abbrev P01RawMechanicalMinCut : Prop :=
  Nonempty RawDecodeNoneCore

/-- The complete P01 construction follows from exactly the raw fail-closed
producer; no further wiring or integration obligation remains. -/
theorem raw_mincut_closes_p01
    (h : P01RawMechanicalMinCut) :
    P01FinalCertificate.P01ConstructionGap := by
  rcases h with ⟨R⟩
  exact p01ConstructionGap_of_core (globalCoreOfRaw R)

#print axioms MCore.Real.P01RawGlobalMinCut.verifyBits_false_of_decode_none
#print axioms MCore.Real.P01RawGlobalMinCut.exact_encoding_or_decode_none
#print axioms MCore.Real.P01RawGlobalMinCut.globalCoreOfRaw
#print axioms MCore.Real.P01RawGlobalMinCut.raw_mincut_closes_p01

end P01RawGlobalMinCut
end Real
end MCore
