import Lean
import MCore.Real.P01RawTotalizationProducer
import MCore.Real.FailProofAllGaps

/-! Separation audit: the P01 producer does not reach any lower-bound / separation
constant. Fails elaboration otherwise; the positive control must reach some. -/
open Lean Elab Command

def succs (env : Environment) (n : Name) : Array Name := Id.run do
  let mut out := #[]
  if let some ci := env.find? n then
    out := out ++ ci.type.getUsedConstants
    match ci with
    | .defnInfo v => out := out ++ v.value.getUsedConstants
    | .thmInfo v => out := out ++ v.value.getUsedConstants
    | .opaqueInfo v => out := out ++ v.value.getUsedConstants
    | .inductInfo v => out := out ++ v.ctors.toArray ++ v.all.toArray
    | .ctorInfo v => out := out.push v.induct
    | .recInfo v =>
        out := out ++ v.all.toArray
        for r in v.rules do out := out ++ r.rhs.getUsedConstants
    | _ => pure ()
  return out

def closure (env : Environment) (root : Name) : NameSet := Id.run do
  let mut seen : NameSet := NameSet.empty.insert root
  let mut todo := #[root]
  while !todo.isEmpty do
    let n := todo.back!; todo := todo.pop
    for c in succs env n do
      if !seen.contains c then seen := seen.insert c; todo := todo.push c
  return seen

def forbiddenLast : List String :=
  ["PneqNP", "UniversalFailure", "FailureGenerator", "G21Pointwise", "P02Target",
   "SATFailGap", "SATNotInP", "InP", "PolyDTMRealization", "PolyDTMCandidate", "sorryAx"]

def lastStr : Name → String | .str _ s => s | n => toString n

elab "#sep" root:ident ctrl:ident : command => do
  let env ← getEnv
  let r := root.getId
  let c := closure env r
  let bad := c.toList.filter (fun n => forbiddenLast.contains (lastStr n))
  unless bad.isEmpty do throwError "SEPARATION FAIL {r}: {bad}"
  -- positive control: a declaration that does mention P ≠ NP objects must be caught
  let cc := closure env ctrl.getId
  let hit := cc.toList.filter (fun n => forbiddenLast.contains (lastStr n))
  if hit.isEmpty then throwError "CONTROL FAIL: detector found nothing in {ctrl.getId}"
  logInfo m!"SEPARATION PASS {r}: {c.size} constants, none forbidden; control {ctrl.getId} reaches {hit.length} forbidden constants"

#sep MCore.Real.P01RawTotalizationProducer.p01ConstructionGap_closed MCore.Real.FailProofAllGaps.failure_generator_iff_universal_failure
