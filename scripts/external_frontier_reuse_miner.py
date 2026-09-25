#!/usr/bin/env python3
from __future__ import annotations

import json, re, subprocess
from collections import defaultdict
from pathlib import Path

ROOT=Path(".")
OUT=ROOT/"evidence"
OUT.mkdir(exist_ok=True)

TARGETS=[
    "P01MachineConstruction",
    "diagonalCompilerV2",
    "ExternalModelMatch",
]

ALIASES={
    "P01MachineConstruction":[
        "p01MachineConstruction","P01Construction","P01FullVerifierConstruction",
        "P01PhysicalMachineConstruction","PhysicalVerifierRealization"
    ],
    "diagonalCompilerV2":[
        "diagonalCompiler","DiagonalCompiler","candidateCoding","SameInputClosure",
        "universal_witness_exists_no_hypothesis"
    ],
    "ExternalModelMatch":[
        "G3ModelMatch","OfficialModelMatch","EncodingNormalization",
        "ExternalMatch","ModelMatch"
    ],
}

DECL_RE=re.compile(r"^\s*(theorem|lemma|def|structure|class|abbrev|instance)\s+([A-Za-z0-9_'.]+)",re.M)

def sh(*args:str)->str:
    return subprocess.check_output(args,text=True,stderr=subprocess.DEVNULL)

def toks(name:str)->set[str]:
    s=re.sub(r"([a-z0-9])([A-Z])",r"\1_\2",name)
    s=re.sub(r"[^A-Za-z0-9]+","_",s).lower()
    return {x for x in s.split("_") if len(x)>1 and x not in {"theorem","lemma","final","proof"}}

def sim(a:str,b:str)->float:
    aa,bb=toks(a),toks(b)
    return 0.0 if not aa or not bb else len(aa&bb)/len(aa|bb)

refs=[x.strip() for x in sh("git","for-each-ref","--format=%(refname:short)","refs/remotes/origin").splitlines()]
refs=[r for r in refs if r!="origin/HEAD"]

decls=defaultdict(list)
branch_stats={}
for ref in refs:
    try:
        files=[p for p in sh("git","ls-tree","-r","--name-only",ref).splitlines() if p.endswith(".lean")]
    except Exception:
        continue
    count=0
    for path in files:
        try:
            text=sh("git","show",f"{ref}:{path}")
        except Exception:
            continue
        for kind,name in DECL_RE.findall(text):
            count+=1
            decls[name].append({"ref":ref,"file":path,"kind":kind})
    branch_stats[ref]={"lean_files":len(files),"declarations":count}

report={"schema":"mcore-pnp-external-frontier-reuse.v1","branch_count":len(refs),"targets":{},"branch_stats":branch_stats}
for target in TARGETS:
    exact=decls.get(target,[])
    alias_hits=[]
    for alias in ALIASES[target]:
        for loc in decls.get(alias,[]):
            alias_hits.append({"name":alias,**loc})
    scored=[]
    for name,locs in decls.items():
        if name==target: continue
        score=sim(target,name)
        if score>0:
            scored.append({"name":name,"score":round(score,4),"locations":locs[:20]})
    scored.sort(key=lambda x:(-x["score"],x["name"]))
    report["targets"][target]={
        "exact":exact,
        "aliases":alias_hits,
        "similar":scored[:40],
    }

# Branch concentration: prefer refs that contain evidence for >1 target.
coverage=defaultdict(set)
for target,data in report["targets"].items():
    for loc in data["exact"]:
        coverage[loc["ref"]].add(target)
    for loc in data["aliases"]:
        coverage[loc["ref"]].add(target)
    for cand in data["similar"][:10]:
        for loc in cand["locations"]:
            coverage[loc["ref"]].add(target)
report["branch_coverage"]=sorted(
    [{"ref":ref,"targets":sorted(ts),"count":len(ts)} for ref,ts in coverage.items()],
    key=lambda x:(-x["count"],x["ref"])
)

# Minimal port recommendation is evidence-only, never proof acceptance.
unresolved=[t for t,d in report["targets"].items() if not d["exact"]]
report["unresolved_exact"]=unresolved
report["rules"]={
    "cross_branch_declaration_is_candidate_only":True,
    "port_requires_dependency_check":True,
    "port_requires_kernel_build":True,
    "port_requires_axiom_hygiene":True,
    "no_placeholder_theorems":True,
    "no_falsified_route_reopen":True,
}

(OUT/"external_frontier_reuse.json").write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
lines=["ATK_EXTERNAL_FRONTIER_REUSE",f"BRANCHES={len(refs)}"]
for t,d in report["targets"].items():
    lines.append(f"{t}_EXACT={len(d['exact'])}_ALIASES={len(d['aliases'])}_SIMILAR={len(d['similar'])}")
for x in report["branch_coverage"][:20]:
    lines.append("COVERAGE="+x["ref"]+"|"+str(x["count"])+"|"+",".join(x["targets"]))
lines.append("UNRESOLVED_EXACT="+",".join(unresolved))
(OUT/"external_frontier_reuse_summary.txt").write_text("\n".join(lines)+"\n")
print("\n".join(lines))
