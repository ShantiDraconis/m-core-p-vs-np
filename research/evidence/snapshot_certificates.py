#!/usr/bin/env python3
import hashlib
import json
import os
import re
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "research" / "evidence" / "generated"
OUT.mkdir(parents=True, exist_ok=True)

TRACK_DIRS = [
    ROOT / "CERTIFICATES",
    ROOT / "audit",
    ROOT / "research",
    ROOT / "lean" / "MCore" / "Real",
    ROOT / "lean" / "MCore" / "Research",
]

TEXT_SUFFIXES = {".lean",".md",".json",".yaml",".yml",".txt",".log"}

PRODUCERS = {
    "P01ConstructionGap": {
        "symbol":"MCore.Real.P01FinalCertificate.P01ConstructionGap",
        "patterns":[
            r"\bP01ConstructionGap\b",
            r"\bP01MachineConstruction\b",
            r"\bp01_closed_no_hypothesis\b"
        ],
    },
    "G21Pointwise": {
        "symbol":"MCore.Real.P02G21G22Attack.G21Pointwise",
        "patterns":[
            r"\bG21Pointwise\b",
            r"\bCoverage\b",
            r"\bprime2_G21_transfers_full\b"
        ],
    },
    "FinalExternalCertificate": {
        "symbol":"FinalExternalCertificate",
        "patterns":[
            r"\bFinalExternalCertificate\b",
            r"\bFinalExternalLiveTwoProducer\b",
            r"\bFINAL_ROOT\b"
        ],
    },
}

def sha256(path):
    h=hashlib.sha256()
    with path.open("rb") as f:
        for block in iter(lambda:f.read(1024*1024), b""):
            h.update(block)
    return h.hexdigest()

files=[]
texts={}
for base in TRACK_DIRS:
    if not base.exists():
        continue
    for p in sorted(base.rglob("*")):
        if not p.is_file():
            continue
        rel=str(p.relative_to(ROOT))
        files.append({"path":rel,"sha256":sha256(p),"size":p.stat().st_size})
        if p.suffix.lower() in TEXT_SUFFIXES and p.stat().st_size <= 2_000_000:
            try:
                texts[rel]=p.read_text(encoding="utf-8",errors="replace")
            except Exception:
                pass

obs={}
for key,spec in PRODUCERS.items():
    hits=[]
    theorem=False
    cert=False
    for rel,txt in texts.items():
        if any(re.search(pat,txt) for pat in spec["patterns"]):
            hits.append(rel)
            if rel.endswith(".lean") and re.search(r"\b(theorem|def|structure|abbrev)\b",txt):
                theorem=True
            if "CERTIFICATE" in rel.upper() or "certificate" in txt.lower():
                cert=True
    state="NO_EVIDENCE"
    if hits: state="SOURCE_PRESENT"
    if theorem: state="THEOREM_PRESENT"
    if cert: state="CERTIFICATE_REFERENCE"
    obs[key]={"symbol":spec["symbol"],"source_hits":hits[:100],"evidence_state":state}

out={
    "schema":"atk.certificate-snapshot.v1",
    "repository":os.environ.get("GITHUB_REPOSITORY"),
    "sha":os.environ.get("GITHUB_SHA"),
    "run_id":int(os.environ["GITHUB_RUN_ID"]) if os.environ.get("GITHUB_RUN_ID") else None,
    "generated_at":datetime.now(timezone.utc).isoformat(),
    "files":files,
    "producer_observations":obs,
}
path=OUT/"certificate-snapshot.json"
path.write_text(json.dumps(out,indent=2,sort_keys=True)+"\n",encoding="utf-8")
print(path)
