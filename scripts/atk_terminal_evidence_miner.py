#!/usr/bin/env python3
import json, os, re, subprocess, pathlib, hashlib, datetime

ROOT=pathlib.Path(__file__).resolve().parents[1]
CFG=ROOT/"audit"/"terminal_targets.json"
OUT=ROOT/"audit"/"generated"
OUT.mkdir(parents=True,exist_ok=True)

cfg=json.loads(CFG.read_text())
sha=subprocess.check_output(["git","rev-parse","HEAD"],cwd=ROOT,text=True).strip()
rows=[]

def run(cmd):
    p=subprocess.run(cmd,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    return p.returncode,p.stdout

for t in cfg["targets"]:
    target=t["lean_target"]
    rc,build=run(["lake","build",target])
    axiom_text=""
    axiom_rc=0
    if rc==0 and t.get("theorems"):
        audit=OUT/(t["id"]+"_AxiomAudit.lean")
        audit.write_text("import "+target+"\n"+"\n".join("#print axioms "+x for x in t["theorems"])+"\n")
        axiom_rc,axiom_text=run(["lake","env","lean",str(audit)])
    unsafe=bool(re.search(r"\b(sorryAx|admit)\b",axiom_text))
    state="GREEN" if rc==0 and axiom_rc==0 and not unsafe else "RED"
    rows.append({
      "id":t["id"],"class":t["class"],"lean_target":target,
      "theorems":t.get("theorems",[]),"commit":sha,"state":state,
      "build_exit":rc,"axiom_exit":axiom_rc,"unsafe_dependency":unsafe,
      "build_sha256":hashlib.sha256(build.encode()).hexdigest(),
      "axiom_sha256":hashlib.sha256(axiom_text.encode()).hexdigest()
    })
    (OUT/(t["id"]+".build.log")).write_text(build)
    (OUT/(t["id"]+".axioms.log")).write_text(axiom_text)

report={
 "schema":"atk.terminal-evidence-ledger.v1",
 "generated_at":datetime.datetime.now(datetime.timezone.utc).isoformat(),
 "commit":sha,
 "summary":{
   "green":sum(x["state"]=="GREEN" for x in rows),
   "red":sum(x["state"]=="RED" for x in rows),
   "total":len(rows)
 },
 "targets":rows
}
(OUT/"terminal_evidence_ledger.json").write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
print(json.dumps(report,indent=2))
if any(x["state"]=="RED" for x in rows):
    raise SystemExit(1)
