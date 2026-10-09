import Lean
import MCore.Real.P01RawTotalizationProducer

/-!
# P01 closure audit (2026-10-09), fail-closed

Checks, inside the Lean kernel environment, that
`P01RawTotalizationProducer.p01ConstructionGap_closed`
* has *exactly* the type `P01FinalCertificate.P01ConstructionGap`
  (no hypotheses, no section variables), and
* depends only on `propext`, `Classical.choice`, `Quot.sound`.
Any deviation is an elaboration error, so the CI step fails.
This file adds no declaration to the library.
-/

open Lean Elab Command

elab "#p01_closure_audit" : command => do
  let env ← getEnv
  let n := ``MCore.Real.P01RawTotalizationProducer.p01ConstructionGap_closed
  let some ci := env.find? n | throwError "P01_CLOSURE_AUDIT FAIL: {n} not found"
  let expected := mkConst ``MCore.Real.P01FinalCertificate.P01ConstructionGap
  unless ci.type == expected do
    throwError "P01_CLOSURE_AUDIT FAIL: type is {ci.type}, expected {expected}"
  let axs ← Lean.collectAxioms n
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := axs.toList.filter (fun a => !allowed.contains a)
  unless bad.isEmpty do
    throwError "P01_CLOSURE_AUDIT FAIL: forbidden axioms {bad}"
  logInfo m!"P01_CLOSURE_AUDIT PASS {n} : {ci.type}; axioms {axs}"

#p01_closure_audit
#print MCore.Real.P01FinalCertificate.P01MachineConstruction
#print axioms MCore.Real.P01RawTotalizationProducer.p01ConstructionGap_closed
