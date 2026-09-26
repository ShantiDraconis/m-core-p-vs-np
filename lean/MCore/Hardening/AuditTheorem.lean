import MCore.Hardening.Base
import MCore.Hardening.P01StatementFrozen
import MCore.Hardening.SSEStatementFrozen

namespace MCore.Hardening.AuditTheorem

structure StatementNode where
  name : String
  statementHash : String
  deps : List String
  policy : NodePolicy
  axiomsUsed : List Lean.Name
  axiomBase : List Lean.Name
  status : NodeStatus
  namedReduction : Option String
  rejectedReason : Option RejectedReason
  deriving Repr

def subsetNames (xs ys : List Lean.Name) : Bool :=
  xs.all fun x => ys.contains x

def checkPolicy (n : StatementNode) : Bool :=
  subsetNames n.axiomsUsed n.axiomBase

def hasNamedReduction (n : StatementNode) : Bool :=
  match n.status with
  | .open_math => n.namedReduction.isSome
  | _ => true

/-- Statement-level cycle detector for the finite audited DAG. -/
partial def reaches
    (nodes : List StatementNode)
    (seen : List String)
    (source target : String) : Bool :=
  if seen.contains source then false
  else if source == target then true
  else
    match nodes.find? (fun n => n.name == source) with
    | none => false
    | some n =>
        n.deps.any (fun d => reaches nodes (source :: seen) d target)

def detectCycle (nodes : List StatementNode) : Bool :=
  nodes.any fun n => n.deps.any (fun d => reaches nodes [n.name] d n.name)

def auditNode (nodes : List StatementNode) (n : StatementNode) : Bool :=
  checkPolicy n &&
  hasNamedReduction n &&
  !(n.statementHash.isEmpty) &&
  !detectCycle nodes

/-- Negative molds must pin the exact target hash. Equivalence-only paraphrases
are intentionally insufficient. -/
structure NegativeMold where
  targetHash : String
  paraphraseHash : String
  h_same_hash : targetHash = paraphraseHash
  target : Prop
  h_neg : ¬ target

/-- Producer independence audit at the metadata/axiom layer. Structural proof
term comparison is performed by the external miner on elaborated declarations. -/
def disjointExceptBase
    (base a b : List Lean.Name) : Bool :=
  (a.filter fun x => b.contains x).all fun x => base.contains x

#eval checkPolicy {
  name := "P01"
  statementHash := P01StatementFrozen.statementHash
  deps := []
  policy := .classical_ok
  axiomsUsed := []
  axiomBase := declaredBase
  status := .declared
  namedReduction := none
  rejectedReason := none
}

end MCore.Hardening.AuditTheorem
