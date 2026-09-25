#!/usr/bin/env python3
import json, re
from pathlib import Path
from collections import defaultdict, deque

ROOT=Path(__file__).resolve().parents[1]
PAT=ROOT/"research/patterns/registry.json"
FAST=ROOT/"final-proof/external-fastpath-registry.json"
REUSE=ROOT/"final-proof/reuse-index-20260923.json"
OUTDIR=ROOT/"research/meta"
OUTDIR.mkdir(parents=True,exist_ok=True)

patterns=json.loads(PAT.read_text()) if PAT.exists() else []
fast=json.loads(FAST.read_text()) if FAST.exists() else {"claims":{}}
reuse=json.loads(REUSE.read_text()) if REUSE.exists() else {"reuse":[]}

AREA_RULES=[
 ("P01", re.compile(r"p01|parser|witness|verifier|physical|sat.*np",re.I)),
 ("P02", re.compile(r"p02|g21|failure|diagonal|semantic|clock|kleene|sameinput",re.I)),
 ("G3", re.compile(r"g3|external.*contract|model.*match|normalized",re.I)),
 ("FINAL", re.compile(r"final|external|root|proof",re.I)),
 ("RESEARCH", re.compile(r"pattern|q3|prime|horizon|research",re.I)),
]

def area_of(text):
    for a,rx in AREA_RULES:
        if rx.search(text or ""): return a
    return "UNMAPPED"

nodes={}
edges=[]
for name,c in fast.get("claims",{}).items():
    nodes[name]={
      "id":name,"kind":"claim","area":area_of(name+" "+json.dumps(c)),
      "state":c.get("state","UNKNOWN"),"exact_type":c.get("exact_type"),
      "exact_term":c.get("exact_term"),"exact_theorem":c.get("exact_theorem"),
      "proof_credit": 1 if c.get("state") in {"CERTIFIED","GREEN","FROZEN"} else 0,
    }
    for dep in c.get("deps",[]) or []:
        edges.append({"from":dep,"to":name,"kind":"depends_on"})

for p in patterns:
    pid="pattern:"+p.get("pattern_id","unknown")
    nodes[pid]={
      "id":pid,"kind":"pattern","area":area_of((p.get("name") or "")+" "+(p.get("claim") or "")),
      "state":p.get("status","UNKNOWN"),"proof_credit":p.get("proof_credit",0),
      "source":p.get("source"),"lean_file":p.get("lean_file"),
    }

for i,e in enumerate(reuse.get("reuse",[])):
    eid=f"evidence:{i}:{e.get('sha','unknown')}"
    nodes[eid]={
      "id":eid,"kind":"evidence","area":area_of((e.get("area") or "")+" "+(e.get("state") or "")),
      "state":e.get("state","UNKNOWN"),"sha":e.get("sha"),"run":e.get("run"),
      "certificate":e.get("certificate"),"proof_credit":0,
    }

exact_targets={
 "P01_MACHINE_CONSTRUCTION":["P01MachineConstruction","P01ConstructionGap"],
 "P02_FAILURE_GENERATOR":["FailureGenerator","G21Pointwise","TotalCandidateSeparationLaw"],
 "G3_EXTERNAL_CONTRACT":["G3ExternalContract","cookNormalizedExternalContract"],
 "FINAL_EXTERNAL_COMPOSITION":["FinalExternalInputs","FinalExternalCertificate","OfficialPneqNP"],
}
for nid,n in list(nodes.items()):
    blob=json.dumps(n)
    for target,keys in exact_targets.items():
        if nid==target: continue
        if any(k.lower() in blob.lower() for k in keys):
            edges.append({"from":nid,"to":target,"kind":"candidate_support"})

# shortest unresolved frontier: unresolved claim whose deps are all closed or absent
closed={"CERTIFIED","GREEN","FROZEN","GREEN_FROZEN_CERTIFIED"}
frontier=[]
for name,c in fast.get("claims",{}).items():
    st=c.get("state","UNKNOWN")
    if st in closed: continue
    deps=c.get("deps",[]) or []
    deps_closed=all(fast.get("claims",{}).get(d,{}).get("state") in closed for d in deps)
    if deps_closed or not deps:
        frontier.append(name)

# area boundaries
areas=defaultdict(lambda:{"claims":[],"patterns":[],"evidence":[],"open_frontier":[]})
for nid,n in nodes.items():
    bucket=areas[n["area"]]
    bucket[n["kind"]+"s" if n["kind"]!="evidence" else "evidence"].append(nid)
for f in frontier:
    if f in nodes:
        areas[nodes[f]["area"]]["open_frontier"].append(f)

out={
 "schema":"atk.meta-formalizer.v1",
 "fail_closed":True,
 "promotion_policy":{
   "metadata_or_pattern_cannot_prove":True,
   "kernel_green_required":True,
   "axiom_audit_required":True,
   "falsified_routes_reopen":False,
 },
 "nodes":nodes,
 "edges":edges,
 "areas":dict(areas),
 "minimal_open_frontier":frontier,
 "permanently_closed":reuse.get("permanently_closed",[]),
}
(OUTDIR/"claim-evidence-graph.json").write_text(json.dumps(out,indent=2,sort_keys=True)+"\n")

lines=["ATK META FORMALIZER v1","FAIL_CLOSED=true","MINIMAL_OPEN_FRONTIER="+",".join(frontier)]
for a in sorted(areas):
    d=areas[a]
    lines.append(f"{a}: claims={len(d['claims'])} patterns={len(d['patterns'])} evidence={len(d['evidence'])} frontier={','.join(d['open_frontier']) or '-'}")
(OUTDIR/"frontier-summary.txt").write_text("\n".join(lines)+"\n")
print("\n".join(lines))
