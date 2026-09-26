#!/usr/bin/env python3
import hashlib
import json
import re
from collections import defaultdict
from pathlib import Path

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/"research"/"evidence"/"generated"
OUT.mkdir(parents=True,exist_ok=True)

roots=[ROOT/"CERTIFICATES",ROOT/"audit",ROOT/"research"]
status_words=["GREEN","FROZEN","CERTIFIED","OPEN_MATH","RED","BLOCKED","PREPARATORY","NOT_ISSUED","SUCCESS","FAILURE"]
symbol_words=["P01ConstructionGap","P01MachineConstruction","G21Pointwise","P02Target","FinalExternalCertificate","FINAL_ROOT","FINAL_PROOF"]

records=[]
for base in roots:
    if not base.exists(): continue
    for p in sorted(base.rglob("*")):
        if not p.is_file(): continue
        if p.suffix.lower() not in {".md",".json",".yaml",".yml",".txt",".log"}: continue
        if p.stat().st_size>2_000_000: continue
        rel=str(p.relative_to(ROOT))
        txt=p.read_text(encoding="utf-8",errors="replace")
        statuses=sorted({w for w in status_words if re.search(rf"\b{re.escape(w)}\b",txt,re.I)})
        symbols=sorted({w for w in symbol_words if w in txt})
        shas=sorted(set(re.findall(r"\b[0-9a-f]{7,40}\b",txt,re.I)))[:100]
        runs=sorted(set(int(x) for x in re.findall(r"\b(?:run|RUN)[^0-9]{0,8}([0-9]{8,14})\b",txt)))[:100]
        records.append({
            "path":rel,
            "sha256":hashlib.sha256(txt.encode()).hexdigest(),
            "statuses":statuses,
            "symbols":symbols,
            "referenced_shas":shas,
            "referenced_runs":runs,
        })

by_symbol=defaultdict(list)
for rec in records:
    for s in rec["symbols"]:
        by_symbol[s].append(rec)

conflicts=[]
for sym,recs in by_symbol.items():
    seen=set(x for r in recs for x in r["statuses"])
    # Report potentially contradictory certificate language for human/agent review.
    if ("CERTIFIED" in seen or "GREEN" in seen) and ("OPEN_MATH" in seen or "RED" in seen or "BLOCKED" in seen or "NOT_ISSUED" in seen):
        conflicts.append({
            "symbol":sym,
            "statuses":sorted(seen),
            "files":[r["path"] for r in recs],
            "classification":"REVIEW_REQUIRED",
            "proof_credit":0
        })

out={
  "schema":"atk.certificate-corpus-comparison.v1",
  "records":records,
  "symbol_index":{k:[r["path"] for r in v] for k,v in sorted(by_symbol.items())},
  "potential_conflicts":conflicts,
  "note":"Textual status conflicts are audit signals only; exact theorem/run verification decides closure."
}
path=OUT/"certificate-corpus-comparison.json"
path.write_text(json.dumps(out,indent=2,sort_keys=True)+"\n",encoding="utf-8")
print(path)
