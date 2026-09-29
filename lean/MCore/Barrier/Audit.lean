import MCore.BackwardAudit.OrientedWitnessBoundary

namespace MCore
namespace Barrier

open BackwardAudit

/-- Human-readable audit state for one representation/language.

This structure is metadata only.  In particular, a value of
`appearsToRelativize`, `appearsNatural`, or `appearsToAlgebrize` is not a
mathematical premise and cannot produce a lower bound. -/
structure BarrierAudit where
  langName : String
  relativization : BarrierStatus := .notAssessed
  naturalProofs : BarrierStatus := .notAssessed
  algebrization : BarrierStatus := .notAssessed
  note : String := ""
  deriving Repr

/-- Fail-closed default: an unaudited language starts with no escape claim. -/
def auditHonestNotAssessed (name : String) : BarrierAudit :=
  { langName := name }

/-- Current Boolean/TM lane audit.

The present machine constructions are ordinary finite-control simulations.
We record that they appear to relativize, but deliberately make no claim of a
barrier escape.  This value has no path to `G21Pointwise`. -/
def auditGapRead : BarrierAudit :=
  { langName := "Bool + preserving gap/read"
    relativization := .appearsToRelativize
    naturalProofs := .notAssessed
    algebrization := .notAssessed
    note :=
      "Metadata only: current det-step/shuttle/seq/relabel constructions do not constitute a proved barrier escape." }

/-- A formal barrier model for a chosen technique type.

The three fields are propositions, not Boolean flags.  A concrete barrier
formalization must supply their meanings before an `EscapeEvidence` term can
be constructed. -/
structure BarrierPredicates (Technique : Type) where
  NonRelativizing : Technique → Prop
  NonNaturalizing : Technique → Prop
  NonAlgebrizing : Technique → Prop

/-- Checked escape evidence.

Unlike a record of three `Bool`s or strings, this object can only be
inhabited after Lean receives proofs of the barrier predicates chosen by the
formal barrier model `B`.

This still does not imply `G21Pointwise`: it is an audit certificate for a
technique, not a lower-bound producer. -/
structure EscapeEvidence
    {Technique : Type}
    (B : BarrierPredicates Technique) where
  technique : Technique
  nonRelativizing : B.NonRelativizing technique
  nonNaturalizing : B.NonNaturalizing technique
  nonAlgebrizing : B.NonAlgebrizing technique
  proofRefs : List String := []

/-- Convert genuinely checked escape evidence into audit metadata.

This is deliberately one-way: audit metadata cannot be converted back into
proofs of the barrier predicates. -/
def EscapeEvidence.toAudit
    {Technique : Type}
    {B : BarrierPredicates Technique}
    (E : EscapeEvidence B)
    (name : String) : BarrierAudit :=
  { langName := name
    relativization := .evidenceOfEscape
    naturalProofs := .evidenceOfEscape
    algebrization := .evidenceOfEscape
    note :=
      "Escape statuses backed by Lean proof fields in EscapeEvidence; proofRefs are documentation only." }

/-- Partial checked evidence, useful while only one or two barriers have been
formalized.  Missing fields stay fail-closed. -/
structure PartialEscapeEvidence
    {Technique : Type}
    (B : BarrierPredicates Technique) where
  technique : Technique
  nonRelativizing : Option (B.NonRelativizing technique) := none
  nonNaturalizing : Option (B.NonNaturalizing technique) := none
  nonAlgebrizing : Option (B.NonAlgebrizing technique) := none
  proofRefs : List String := []

private def statusOfEvidence {P : Prop} : Option P → BarrierStatus
  | some _ => .evidenceOfEscape
  | none => .notAssessed

def PartialEscapeEvidence.toAudit
    {Technique : Type}
    {B : BarrierPredicates Technique}
    (E : PartialEscapeEvidence B)
    (name : String) : BarrierAudit :=
  { langName := name
    relativization := statusOfEvidence E.nonRelativizing
    naturalProofs := statusOfEvidence E.nonNaturalizing
    algebrization := statusOfEvidence E.nonAlgebrizing
    note :=
      "Only fields carrying Lean proof terms are promoted to evidenceOfEscape." }

/-- Barrier evidence is intentionally orthogonal to the actual separation
witness.  The only existing terminal consumer remains the lower-bound content
(`not_in_p`) in `LowerBoundWitness`; this file introduces no theorem from
an audit record to that endpoint. -/
theorem escapeEvidence_is_not_lowerBoundWitness
    {Technique Language : Type}
    {B : BarrierPredicates Technique}
    (E : EscapeEvidence B)
    (P NP : Language → Prop) :
    EscapeEvidence B := by
  exact E

#print axioms MCore.Barrier.auditHonestNotAssessed
#print axioms MCore.Barrier.auditGapRead
#print axioms MCore.Barrier.EscapeEvidence.toAudit
#print axioms MCore.Barrier.PartialEscapeEvidence.toAudit
#print axioms MCore.Barrier.escapeEvidence_is_not_lowerBoundWitness

end Barrier
end MCore
