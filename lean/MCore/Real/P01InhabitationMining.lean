import Lean
import MCore.Real.P01FinalCertificate

open Lean Elab Command Meta

private partial def resultHeadName (e : Expr) : MetaM (Option Name) := do
  let e ← whnf e
  match e with
  | .forallE _ domain body _ =>
      let x ← mkFreshExprMVar domain
      resultHeadName (body.instantiate1 x)
  | _ =>
      return e.getAppFn.constName?

private partial def instantiateForalls (e : Expr) : MetaM Expr := do
  let e ← whnf e
  match e with
  | .forallE _ domain body _ =>
      let x ← mkFreshExprMVar domain
      instantiateForalls (body.instantiate1 x)
  | _ => pure e

private def typeUnifies (target cand : Expr) : MetaM Bool := do
  try
    withoutModifyingState do
      let t ← instantiateForalls target
      let c ← instantiateForalls cand
      isDefEq t c
  catch _ =>
    pure false

elab "#mine_producers " n:ident : command => do
  let env ← getEnv
  let targetName ← resolveGlobalConstNoOverload n
  let mut hits : Array (Name × Expr) := #[]
  for (declName, declInfo) in env.constants.toList do
    if declName != targetName && !(declName.toString.startsWith "_") then
      let h? ← liftTermElabM do resultHeadName declInfo.type
      if h? == some targetName then
        hits := hits.push (declName, declInfo.type)
  logInfo m!"[PRODUCER TARGET] {targetName}"
  if hits.isEmpty then
    logInfo m!"  PRODUCERS: NONE"
  else
    for (declName, ty) in hits.toList.take 40 do
      logInfo m!"  PRODUCER: {declName}"
      logInfo m!"    TYPE: {ty}"

elab "#mine_structure " n:ident : command => do
  let env ← getEnv
  let structName ← resolveGlobalConstNoOverload n
  let some info := getStructureInfo? env structName
    | throwError "not a structure: {structName}"
  logInfo m!"[MINING STRUCTURE] {structName}"
  for field in info.fieldNames do
    let finfo? ←
      try
        pure (some (← getConstInfo field))
      catch _ =>
        let projName := Name.str structName field.toString
        try
          pure (some (← getConstInfo projName))
        catch _ =>
          pure none
    match finfo? with
    | none =>
        logInfo m!"[FIELD-SKIP] {field} (no projection constant)"
    | some finfo =>
        let mut hits : Array Name := #[]
        for (declName, declInfo) in env.constants.toList do
          if !(declName.toString.startsWith "_") then
            let ok ← liftTermElabM do typeUnifies finfo.type declInfo.type
            if ok then hits := hits.push declName
        logInfo m!"[FIELD] {field}"
        logInfo m!"  TYPE: {finfo.type}"
        if hits.isEmpty then
          logInfo m!"  STATUS: NO_PRODUCER_TYPE"
        else
          logInfo m!"  STATUS: COMPOSABLE_TYPE_CANDIDATES ({hits.size})"
          logInfo m!"  CANDIDATES: {hits.toList.take 24}"

#mine_structure MCore.Real.P01FinalCertificate.P01MachineConstruction

#mine_structure MCore.Real.SATLowerBoundCertificate

#mine_producers MCore.Real.P01FinalCertificate.P01MachineConstruction
