import MCore.Real.P01PreservingUnaryWitnessMachine
import MCore.Real.P01PreservingUnaryReaderCertificate
import MCore.Real.P01FinalCertificate
import MCore.Real.MachineRunLemmas

namespace MCore
namespace Real
namespace P01PreservingUnaryReaderFrontier

open CanonicalFinalProof
open CanonicalCircuitBits
open P01WitnessIndexedRead
open P01PreservingUnaryWitnessMachine
open P01PreservingUnaryReaderCertificate

/-!
Exact material frontier for the universal preserving unary reader.

This file intentionally contains definitions of the remaining proposition
shapes only.  It introduces no axiom, theorem-by-decree, sorry, or external
closure claim.
-/

/-- One successor unary marker must advance the preserving machine from one
canonical loop configuration to the next while extending the traversed prefix
by exactly the next witness bit. -/
def SuccessorCycleObligation : Prop :=
  ∀ (pref : BitString) (b : Bool) (suffix : BitString) (n : Nat),
    pref ≠ [] →
    ∃ steps : Nat,
      steps ≤ (pref.length + n + suffix.length + 1)^2 + 16 ∧
      preservingUnaryReadMachine.run steps
          (indexSomeConfig pref (b :: suffix) (n + 1)) =
        indexSomeConfig (pref ++ [b]) suffix n

/-- Exact candidate cost of one reachable successor cycle.  The physical
execution proof is the remaining content; this arithmetic lemma discharges
the frontier's polynomial budget once that equality is established. -/
def successorCycleSteps (pref : BitString) : Nat :=
  4 * pref.length + 8

theorem successorCycleSteps_bound
    (pref suffix : BitString) (n : Nat)
    (hpref : pref ≠ []) :
    successorCycleSteps pref ≤
      (pref.length + n + suffix.length + 1)^2 + 16 := by
  have hlen : 1 ≤ pref.length := by
    cases pref with
    | nil => contradiction
    | cons _ xs => simp
  unfold successorCycleSteps
  nlinarith

/-- Physical equality still to be proved against the real transition graph.
Keeping it separate prevents the polynomial side condition from obscuring the
only remaining machine-level obligation. -/
def SuccessorCyclePhysicalEquality : Prop :=
  ∀ (pref : BitString) (b : Bool) (suffix : BitString) (n : Nat),
    pref ≠ [] →
    preservingUnaryReadMachine.run (successorCycleSteps pref)
        (indexSomeConfig pref (b :: suffix) (n + 1)) =
      indexSomeConfig (pref ++ [b]) suffix n

/-- The terminal target remains the existing universal material contract. -/
def UniversalReaderMaterialTarget : Prop :=
  PreservingUnaryReaderGap

/-- P01 integration may advance only after the universal reader is inhabited. -/
def ReaderBeforeP01Construction : Prop :=
  PreservingUnaryReaderGap → P01FinalCertificate.P01ConstructionGap

end P01PreservingUnaryReaderFrontier
end Real
end MCore
