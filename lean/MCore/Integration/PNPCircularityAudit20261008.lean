import Lean
import MCore.Integration.PNPRecoveredFrontier20261008

/-!
# Circularity audit for the recovered P01 producer — 2026-10-08

Walks the full transitive constant-dependency closure (types, values,
constructors) of each audited declaration in the elaborated environment and
fails the build if any forbidden constant is reachable.

For the P01 producer, the forbidden set is every lower-bound / separation
object: if P01 reached any of them, the SAT ∈ NP side would be presupposing
the conclusion. `sorryAx` is forbidden everywhere.
-/

open Lean Elab Command

namespace MCore.Integration.PNPCircularityAudit20261008

/-- Transitive closure of constants used by `root`. -/
def depsOf (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack : Array Name := #[root]
  while !stack.isEmpty do
    let n := stack.back!
    stack := stack.pop
    if seen.contains n then continue
    seen := seen.insert n
    match env.find? n with
    | some ci =>
      for c in ci.type.getUsedConstants do
        stack := stack.push c
      match ci with
      | .defnInfo v => for c in v.value.getUsedConstants do stack := stack.push c
      | .thmInfo v => for c in v.value.getUsedConstants do stack := stack.push c
      | .opaqueInfo v => for c in v.value.getUsedConstants do stack := stack.push c
      | .inductInfo v => for c in v.ctors do stack := stack.push c
      | _ => pure ()
    | none => pure ()
  return seen

/-- Last name components that P01 must never reach. -/
def lowerBoundForbidden : List String :=
  ["PneqNP", "OfficialPneqNP", "UniversalFailure", "FailureGenerator",
   "G21Pointwise", "G22Contradiction", "P02Target", "SATFailGap",
   "SATNotInP", "SeparationCertificate", "SATInternalClosure",
   "FinalGapCertificate", "InP", "PolyDTMRealization", "sorryAx"]

def lastComponent (n : Name) : String :=
  match n with
  | .str _ s => s
  | _ => toString n

/-- Fails if `root` reaches any forbidden constant; otherwise logs the size of
its dependency closure. -/
def auditNoForbidden (root : Name) (forbidden : List String) : CommandElabM Unit := do
  let env ← getEnv
  unless env.contains root do
    throwError "audit target {root} not found"
  let deps := depsOf env root
  let bad := deps.toList.filter fun n => forbidden.contains (lastComponent n)
  if bad.isEmpty then
    logInfo m!"CIRCULARITY_AUDIT PASS {root}: {deps.size} constants in closure, none forbidden"
  else
    throwError "CIRCULARITY_AUDIT FAIL {root}: reaches {bad}"

elab "#audit_p01_no_lower_bound" : command =>
  auditNoForbidden
    `MCore.Real.P01RawTotalizationProducer.p01ConstructionGap_closed
    lowerBoundForbidden

elab "#audit_sat_in_np_no_lower_bound" : command =>
  auditNoForbidden
    `MCore.Integration.PNPRecoveredFrontier20261008.sat_in_np_recovered
    lowerBoundForbidden

elab "#audit_endpoint_no_sorry" : command =>
  auditNoForbidden
    `MCore.Integration.PNPRecoveredFrontier20261008.integration_status
    ["sorryAx"]

/-- Positive control: the detector must find `PneqNP` and `UniversalFailure`
in the closure of the conditional endpoint. If it did not, a PASS above would
be meaningless. -/
elab "#audit_positive_control" : command => do
  let env ← getEnv
  let deps := depsOf env
    `MCore.Integration.PNPRecoveredFrontier20261008.pneqnp_of_g21
  let found := deps.toList.filter fun n =>
    ["PneqNP", "UniversalFailure"].contains (lastComponent n)
  if found.length ≥ 2 then
    logInfo m!"CIRCULARITY_AUDIT CONTROL PASS: detector finds {found} in pneqnp_of_g21"
  else
    throwError "CIRCULARITY_AUDIT CONTROL FAIL: detector missed forbidden constants ({found})"

#audit_positive_control
#audit_p01_no_lower_bound
#audit_sat_in_np_no_lower_bound
#audit_endpoint_no_sorry

end MCore.Integration.PNPCircularityAudit20261008
