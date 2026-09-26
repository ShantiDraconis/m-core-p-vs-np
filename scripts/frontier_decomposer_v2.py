#!/usr/bin/env python3
from __future__ import annotations
import hashlib, json, re, sys
from pathlib import Path
from datetime import datetime, timezone

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/"evidence/frontier_decomposition_v2.json"
MAX_DEPTH=5
MAX_FIELDS=10

def sha256_file(path):
    p=ROOT/path
    return "sha256:"+hashlib.sha256(p.read_bytes()).hexdigest() if p.exists() else None

def atomicity(kind, unfoldable=False, compound=False, has_instance=False):
    reasons=[]
    if kind not in {"structure","and","prod","sigma"}: reasons.append("no_cases")
    if not unfoldable: reasons.append("no_unfold")
    if not compound: reasons.append("not_compound")
    if not has_instance: reasons.append("no_registered_instance")
    return {
      "atomic": len(reasons)==4,
      "atomicity_witness":reasons,
    }

def node(id, area, typ, state, depth, **kw):
    if depth>MAX_DEPTH:
        state="DECOMPOSITION_LIMIT_REACHED"
    d={
      "id":id, "area":area, "type":typ, "state":state,
      "decomposition_depth":depth,
      "max_depth":MAX_DEPTH,
    }
    d.update(kw)
    return d

p01_fields=[
 node("P01.machine","P01","NTM TerminalState (Option Bool)","CONCRETE_WITNESS_PENDING",1,
      atomicity=atomicity("type"),proof_role="producer"),
 node("P01.blank_none","P01","machine.blank = none","PROVABLE_NOW",1,
      atomicity=atomicity("prop"),depends_on=["P01.machine"]),
 node("P01.timeBound","P01","TimeBound","CONCRETE_WITNESS_PENDING",1,
      atomicity=atomicity("type"),depends_on=["P01.machine"]),
 node("P01.time_poly","P01","PolynomialTimeBound timeBound","PROVABLE_NOW",1,
      atomicity=atomicity("prop"),depends_on=["P01.timeBound"]),
 node("P01.halts","P01","forall bs, machine.HaltsWithin (timeBound bs.length) ...","OPEN_MATH_PROOF",1,
      atomicity=atomicity("forall"),depends_on=["P01.machine","P01.timeBound"],
      suggested_strategy="reuse phase bounds; prove integrated fuel bound"),
 node("P01.accepts_iff","P01","forall bs, machine.AcceptsWithin ... iff SATBits ...","OPEN_MATH_PROOF",1,
      atomicity=atomicity("forall"),depends_on=["P01.machine"],
      suggested_strategy="phase refinement / trace correspondence")
]

p01_edges=[
 {"edge":"parserNTM -> witness preparation","output_type":"parser terminal tape/config","input_type":"witness-prep source layout","match":"adapter_required","state":"CONCRETE_WITNESS_PENDING"},
 {"edge":"witness preparation -> physical verifier","output_type":"preparedTape witness source","input_type":"verifierInputTape witness source","match":"exact","evidence":"canonicalPhaseLayoutCertificate"},
 {"edge":"physical verifier -> integrated accept/reject","output_type":"verifier terminal state","input_type":"IntegratedState terminal states","match":"adapter_required","state":"CONCRETE_WITNESS_PENDING"},
]

# P02 pinned source audit. selfInput is explicitly noncomputable in certified source c511da2c.
p02_chain=[
 node("P02.selfInput","P02","Nat.Partrec.Code -> BitString","OPEN_MATH_DEFINITION",1,
      atomicity=atomicity("def",unfoldable=True),
      source_ref="c511da2c0e88bf858a698404e281914752f10e46",
      constructivity={"executable":False,"reason":"source declares noncomputable def selfInput using Part.Dom/get"},
      action="replace by constructive representation/projection or change terminal statement"),
 node("P02.rejectCircuit","P02","PolyDTMCandidate -> BitString -> Circuit","PROVABLE_NOW",1,
      atomicity=atomicity("def",unfoldable=True),
      constructivity={"executable":True,"reason":"syntactic boundedExecCircuit composition"},
      depends_on=["P02.selfInput"]),
 node("P02.encodeCircuit","P02","Circuit -> BitString","REUSED",1,
      atomicity=atomicity("def",unfoldable=True),
      constructivity={"executable":True}),
 node("P02.encodeBitsNat","P02","BitString -> Nat","REUSED",1,
      atomicity=atomicity("def",unfoldable=True),
      constructivity={"executable":True}),
]

p02_edges=[
 {"edge":"selfInput -> rejectCircuit","output_type":"BitString","input_type":"BitString","match":"exact"},
 {"edge":"rejectCircuit -> encodeCircuit","output_type":"Circuit","input_type":"Circuit","match":"exact"},
 {"edge":"encodeCircuit -> encodeBitsNat","output_type":"BitString","input_type":"BitString","match":"exact"},
]

def minimal_cut(nodes, edges):
    # Frontier is unresolved leaves after dependencies/reuse are discounted.
    # Prefer definition blockers over downstream proof obligations.
    defs=[n for n in nodes if n["state"]=="OPEN_MATH_DEFINITION"]
    if defs: return [n["id"] for n in defs]
    hard=[n for n in nodes if n["state"] in {"CONCRETE_WITNESS_PENDING","OPEN_MATH_PROOF"}]
    # Keep only nodes not strictly downstream of another unresolved node.
    ids={n["id"] for n in hard}
    deps={n["id"]:set(n.get("depends_on",[])) for n in hard}
    return [n["id"] for n in hard if not (deps[n["id"]] & ids)]

def fixture_acceptance():
    # Synthetic exact producer: source is kernel-built by workflow.
    states=["DISCOVERED","SOURCE_VERIFIED","TYPE_MATCHED","BUILD_GREEN","AXIOM_GREEN","PRODUCER_INHABITED","FROZEN","CERTIFIED"]
    return {
      "source":"lean/MCore/Research/MetaFormalizerAcceptanceFixture.lean",
      "expected_terminal":"MCore.Research.MetaFormalizerAcceptanceFixture.FixtureCertificate",
      "promotion_path":states,
      "accepts_when_producer_inhabited":True,
      "real_claim_credit":0,
      "purpose":"non-vacuity test only"
    }

p01_cut=minimal_cut(p01_fields,p01_edges)
p02_cut=minimal_cut(p02_chain,p02_edges)

doc={
 "schema":"elyon.frontier-decomposition.v2",
 "generated_at":datetime.now(timezone.utc).isoformat(),
 "policy":{
   "frontier_first":True,
   "max_depth":MAX_DEPTH,
   "max_fields_per_node":MAX_FIELDS,
   "producer_only_reduces_frontier":True,
   "open_math_definition_triggers_rewrite":True,
   "falsified_routes_reopen":False,
 },
 "taxonomy":[
   "REUSED","PROVABLE_NOW","CONCRETE_WITNESS_PENDING",
   "OPEN_MATH_PROOF","OPEN_MATH_DEFINITION","CONDITIONAL","FALSE",
   "STALE","POTENTIALLY_STALE","DECOMPOSITION_LIMIT_REACHED"
 ],
 "P01":{
   "root":{"type":"MCore.Real.P01TerminalDelta.IntegratedExecutionCertificate","state":"CONCRETE_WITNESS_PENDING"},
   "fields":p01_fields,
   "composition_edges":p01_edges,
   "minimal_frontier":p01_cut,
 },
 "P02":{
   "root":{"type":"MCore.Real.P02EffectiveCompilerConstruction.UniformCompilerValueComputable","state":"OPEN_MATH_DEFINITION"},
   "composition_chain":p02_chain,
   "composition_edges":p02_edges,
   "minimal_frontier":p02_cut,
   "pinned_source":{
     "sha":"c511da2c0e88bf858a698404e281914752f10e46",
     "certificate_runs":[35901261874,35902536365,35902546971]
   }
 },
 "global_minimal_frontier":p01_cut+p02_cut,
 "frontier_count":len(p01_cut)+len(p02_cut),
 "linker_acceptance_fixture":fixture_acceptance(),
 "staleness":{
   "fields":["source_hash","statement_hash","toolchain_version","verified_at","stale_check_after"],
   "on_source_change":"POTENTIALLY_STALE cascade to dependents",
   "on_toolchain_change":"STALE then reverify topologically"
 },
 "proof_term_accounting":{
   "enabled":True,
   "gate":False,
   "large_terms":"factorization_review",
   "small_terms":"adapter_or_degenerate_review"
 },
 "conditional_first_class":True,
 "adversarial_rule":"PROVABLE_NOW must pass counterexample/refutation search before promotion",
}

# bounded decomposition invariant
for area in ("P01","P02"):
    items=doc[area].get("fields",doc[area].get("composition_chain",[]))
    if len(items)>MAX_FIELDS:
        raise SystemExit(f"{area}: decomposition exceeds max_fields_per_node")

OUT.parent.mkdir(exist_ok=True)
OUT.write_text(json.dumps(doc,indent=2,sort_keys=True)+"\n")
print(json.dumps({
 "P01_minimal_frontier":p01_cut,
 "P02_minimal_frontier":p02_cut,
 "global_frontier":doc["global_minimal_frontier"],
 "frontier_count":doc["frontier_count"],
 "P02_classification":doc["P02"]["root"]["state"],
 "fixture_acceptance":doc["linker_acceptance_fixture"]["accepts_when_producer_inhabited"],
},indent=2))
