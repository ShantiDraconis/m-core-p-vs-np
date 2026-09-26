#!/usr/bin/env python3
from __future__ import annotations
import json, re, sys
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
PAT=ROOT/"research/patterns/registry.json"
REUSE=ROOT/"final-proof/reuse-index-20260923.json"
FAST=ROOT/"final-proof/external-fastpath-registry.json"
OUT=ROOT/"evidence/meta_formalizer_linker.json"

def load(p):
    return json.loads(p.read_text()) if p.exists() else None

patterns=load(PAT) or []
reuse=load(REUSE) or {}
fast=load(FAST) or {"claims":{}}
claims=fast.get("claims",{})

closed_states={"GREEN","FROZEN","CERTIFIED","CLOSED"}
forbidden_promotions=[]
links=[]
areas={
  "P01":{"patterns":[],"evidence":[],"claims":[]},
  "P02":{"patterns":[],"evidence":[],"claims":[]},
  "G3":{"patterns":[],"evidence":[],"claims":[]},
  "FINAL":{"patterns":[],"evidence":[],"claims":[]},
  "RESEARCH":{"patterns":[],"evidence":[],"claims":[]},
}

def area_of(text):
    t=(text or "").upper()
    if "P01" in t: return "P01"
    if "P02" in t or "G21" in t or "G22" in t or "T5" in t: return "P02"
    if "G3" in t or "MODEL_MATCH" in t or "EXTERNAL_CONTRACT" in t: return "G3"
    if "FINAL" in t or "EXTERNAL" in t: return "FINAL"
    return "RESEARCH"

for p in patterns:
    a=area_of(" ".join(str(p.get(k,"")) for k in ("name","claim","source","lean_file")))
    areas[a]["patterns"].append(p)
    if p.get("status")=="FORMALIZED" and p.get("proof_credit",0)==0:
        links.append({
          "kind":"formalized_needs_bridge",
          "area":a,
          "pattern_id":p.get("pattern_id"),
          "name":p.get("name"),
          "lean_file":p.get("lean_file"),
        })
    if p.get("status")=="OPEN_MATH":
        links.append({
          "kind":"open_math_pattern",
          "area":a,
          "pattern_id":p.get("pattern_id"),
          "name":p.get("name"),
          "lean_file":p.get("lean_file"),
        })

for e in reuse.get("reuse",[]):
    a=area_of(e.get("area",""))
    areas[a]["evidence"].append(e)

for name,c in claims.items():
    a=area_of(name+" "+str(c.get("exact_type",""))+" "+str(c.get("exact_theorem","")))
    areas[a]["claims"].append({"name":name,**c})
    if c.get("state")=="OPEN_MATH" and c.get("promoted"):
        forbidden_promotions.append(name)

# hard exact frontiers from current certified reduction
exact_frontier=[
  {
    "area":"P01",
    "claim":"P01_MACHINE_CONSTRUCTION",
    "exact_type":"MCore.Real.P01FinalCertificate.P01MachineConstruction",
    "current_terminal":"MCore.Real.P01TerminalDelta.IntegratedExecutionCertificate",
    "state":"OPEN_MATH",
    "bridge":"IntegratedExecutionCertificate.toP01",
  },
  {
    "area":"P02",
    "claim":"P02_FAILURE_GENERATOR",
    "exact_type":"FailureGenerator (SATBits circuitBitEncoding)",
    "current_terminal":"MCore.Real.P02EffectiveCompilerConstruction.UniformCompilerValueComputable",
    "state":"OPEN_MATH",
    "bridge":"uniformCompilerValueComputable_closes_P02 / compilerComputable_P01_G3_to_FinalExternalGap",
    "evidence_sha":"c511da2c0e88bf858a698404e281914752f10e46",
    "evidence_runs":[35901261874,35902536365,35902546971],
  },
]

# reusable evidence never closes an exact frontier by provenance alone
candidate_support=[]
for f in exact_frontier:
    ev=areas[f["area"]]["evidence"]
    candidate_support.append({
      "claim":f["claim"],
      "support_count":len(ev),
      "support":[{"area":x.get("area"),"sha":x.get("sha"),"run":x.get("run"),"state":x.get("state")} for x in ev],
      "proof_credit":0,
      "reason":"supporting provenance only; exact inhabitant still required",
    })

# derive final chain without inventing closure
final_chain=[
  "P01TerminalDelta.IntegratedExecutionCertificate",
  "P01MachineConstruction",
  "SATInNPGap",
  "P02EffectiveCompilerConstruction.UniformCompilerValueComputable",
  "P02Target / FailureGenerator-equivalent separation",
  "G3ExternalContract[cookNormalizedExternalContract]",
  "FinalExternalInputs",
  "OfficialPneqNP",
  "FinalExternalCertificate/FINAL_ROOT/FINAL_PROOF"
]

errors=[]
if forbidden_promotions:
    errors.append("OPEN_MATH promoted: "+",".join(forbidden_promotions))
for route in reuse.get("permanently_closed",[]):
    if route.get("state")!="CLOSED_BY_FALSIFICATION":
        errors.append("permanently closed route mutated: "+str(route))

summary={
  "schema":"elyon.meta-formalizer-linker.v1",
  "fail_closed":True,
  "inputs":{
    "pattern_registry":str(PAT.relative_to(ROOT)),
    "reuse_index":str(REUSE.relative_to(ROOT)),
    "external_registry":str(FAST.relative_to(ROOT)),
  },
  "areas":areas,
  "links":links,
  "exact_frontier":exact_frontier,
  "candidate_support":candidate_support,
  "final_chain":final_chain,
  "frontier_count":len(exact_frontier),
  "ready_for_external":False,
  "promotion_rule":"only kernel-checked exact bridge may change OPEN_MATH to GREEN",
  "falsified_routes_reopen":False,
  "validation_errors":errors,
}
OUT.parent.mkdir(exist_ok=True)
OUT.write_text(json.dumps(summary,indent=2,sort_keys=True)+"\n")
print(json.dumps({
  "frontier_count":summary["frontier_count"],
  "exact_frontier":[x["claim"] for x in exact_frontier],
  "pattern_count":len(patterns),
  "reuse_count":len(reuse.get("reuse",[])),
  "validation_errors":errors,
},indent=2))
if errors: sys.exit(2)
