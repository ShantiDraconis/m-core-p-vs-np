import MCore.Real.P02ComplementRunRealization

namespace MCore
namespace Real
namespace SourceRecovery

open CircuitK1
open CanonicalFinalProof
open CanonicalCircuitBits
open P02TotalCandidateKleeneReduction
open P02ComplementRunRealization
open PNPNTMTableauEncoding
open PNPNTMTableauFrontier
open PNPNTMTableauClosure

/-- Inverse of the literal encoding used by the concrete NTM tableau. -/
def decodeNTMLiteral : Circuit → Option NTMLiteral
  | .input v => some (ntmPos v)
  | .not (.input v) => some (ntmNeg v)
  | _ => none

/-- Inverse of the right-associated clause AST emitted by ntmClauseCircuit. -/
def decodeNTMClause : Circuit → Option NTMClause
  | .const false => some []
  | .or a rest =>
      match decodeNTMLiteral a, decodeNTMClause rest with
      | some l, some ls => some (l :: ls)
      | _, _ => none
  | _ => none

/-- Inverse of ntmCNFCircuit on its range. -/
def decodeNTMCNF : Circuit → Option NTMCNF
  | .const true => some []
  | .and c rest =>
      match decodeNTMClause c, decodeNTMCNF rest with
      | some cl, some cs => some (cl :: cs)
      | _, _ => none
  | _ => none

@[simp] theorem decodeNTMLiteral_ntmLiteralCircuit
    (l : NTMLiteral) :
    decodeNTMLiteral (ntmLiteralCircuit l) = some l := by
  cases l with
  | mk v positive =>
      cases positive <;>
        rfl

@[simp] theorem decodeNTMClause_ntmClauseCircuit
    (c : NTMClause) :
    decodeNTMClause (ntmClauseCircuit c) = some c := by
  induction c with
  | nil =>
      rfl
  | cons l ls ih =>
      simp [ntmClauseCircuit, decodeNTMClause, ih]

@[simp] theorem decodeNTMCNF_ntmCNFCircuit
    (F : NTMCNF) :
    decodeNTMCNF (ntmCNFCircuit F) = some F := by
  induction F with
  | nil =>
      rfl
  | cons c cs ih =>
      simp [ntmCNFCircuit, decodeNTMCNF, ih]

/-- The reduction really encodes the concrete complemented NTM tableau. -/
theorem decodeCircuit_reduce
    (M : PolyDTMCandidate)
    (hTotal : DeclaredClockTotal M)
    (x : BitString) :
    decodeCircuit ((complementSemanticReduction M hTotal).reduce x) =
      some
        (ntmCNFCircuit
          (boundedExecTableauCNF_NTM
            (complementToNTMCandidate M)
            x
            (M.timeBound x.length))) := by
  simpa [complementSemanticReduction,
    PNPNTMTableauFrontier.NTMTableauProducer.toSemanticReduction,
    PNPNTMTableauClosure.concreteNTMTableauProducer,
    PNPNTMTableauClosure.ntmTableauProducerOfCertificates,
    P02ComplementRunRealization.complementRunRealization,
    boundedExecCircuit_NTM] using
      (decodeCircuit_encode
        (boundedExecCircuit_NTM
          (complementToNTMCandidate M)
          x
          (M.timeBound x.length)))

theorem ntmRadius_eq_of_length_eq
    {x y : BitString} {t : Nat}
    (h : x.length = y.length) :
    ntmRadius x t = ntmRadius y t := by
  simp [ntmRadius, h]

theorem ntmRightBase_eq_of_length_eq
    (M : PolyNTMCandidate)
    {x y : BitString} {t : Nat}
    (h : x.length = y.length) :
    ntmRightBase M x t = ntmRightBase M y t := by
  simp [ntmRightBase, ntmLeftBase, ntmRadius, h]

theorem ntmChoiceBase_eq_of_length_eq
    (M : PolyNTMCandidate)
    {x y : BitString} {t : Nat}
    (h : x.length = y.length) :
    ntmChoiceBase M x t = ntmChoiceBase M y t := by
  simp [ntmChoiceBase, ntmRightBase, ntmLeftBase, ntmRadius, h]

theorem ntmLeftVar_eq_of_length_eq
    (M : PolyNTMCandidate)
    {x y : BitString} {t s i : Nat}
    (a : Option Bool)
    (h : x.length = y.length) :
    ntmLeftVar M x t s i a = ntmLeftVar M y t s i a := by
  simp [ntmLeftVar, ntmLeftBase, ntmRadius, h]

theorem ntmRightVar_eq_of_length_eq
    (M : PolyNTMCandidate)
    {x y : BitString} {t s i : Nat}
    (a : Option Bool)
    (h : x.length = y.length) :
    ntmRightVar M x t s i a = ntmRightVar M y t s i a := by
  simp [ntmRightVar, ntmRightBase, ntmLeftBase, ntmRadius, h]

theorem ntmChoiceVar_eq_of_length_eq
    (M : PolyNTMCandidate)
    {x y : BitString} {t s j : Nat}
    (q : Fin (M.stateCount + 1))
    (a : Option Bool)
    (h : x.length = y.length) :
    ntmChoiceVar M x t s q a j = ntmChoiceVar M y t s q a j := by
  simp [ntmChoiceVar, ntmChoiceBase, ntmRightBase, ntmLeftBase, ntmRadius, h]

/-- The canonical input tape representation itself loses no source bits. -/
theorem inputTape_injective :
    Function.Injective inputTape := by
  intro x y h
  cases x with
  | nil =>
      cases y with
      | nil => rfl
      | cons b bs =>
          simp [inputTape] at h
  | cons a as =>
      cases y with
      | nil =>
          simp [inputTape] at h
      | cons b bs =>
          simp [inputTape] at h
          rcases h with ⟨hab, htail⟩
          subst b
          have : as = bs := by
            simpa using htail
          subst bs
          rfl

/-
Next material-free engineering target (not postulated here):
  extractInitialTape :
    PolyNTMCandidate → Nat → Nat → NTMCNF → Option BitString
with a proof that it reads the time-0 head/right unit clauses emitted by
ntmInitialCNF, followed by decodeSource_reduce for the concrete R_M range.
-/

end SourceRecovery
end Real
end MCore
