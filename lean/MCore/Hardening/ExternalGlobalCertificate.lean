import MCore.Hardening.AuditTheorem

namespace MCore.Hardening

structure Provenance where
  repository : String
  commit : String
  runId : Option String
  deriving Repr

structure ExternalGlobalCertificate where
  statementName : String
  statementHash : String
  termName : String
  termHash : String
  axiomBase : List Name
  axiomsUsed : List Name
  deps : List String
  conditionalOn : List String
  policy : NodePolicy
  provenance : Provenance
  deriving Repr

def ExternalGlobalCertificate.unconditional
    (c : ExternalGlobalCertificate) : Bool :=
  c.conditionalOn.isEmpty

def ExternalGlobalCertificate.policyValid
    (c : ExternalGlobalCertificate) : Bool :=
  AuditTheorem.subsetNames c.axiomsUsed c.axiomBase

/-- EGC metadata is emitted only from named declarations. This constructor does
not promote conditional mathematics to an unconditional theorem. -/
def emitConditionalEGC
    (statementName statementHash termName termHash : String)
    (deps conditionalOn : List String)
    (policy : NodePolicy)
    (provenance : Provenance)
    (axiomsUsed : List Name) : ExternalGlobalCertificate :=
  { statementName
    statementHash
    termName
    termHash
    axiomBase := declaredBase
    axiomsUsed
    deps
    conditionalOn
    policy
    provenance }

end MCore.Hardening
