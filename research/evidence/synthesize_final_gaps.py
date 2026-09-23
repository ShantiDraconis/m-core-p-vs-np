#!/usr/bin/env python3
import json
import os
from pathlib import Path
from datetime import datetime, timezone

ROOT=Path(__file__).resolve().parents[2]
GEN=ROOT/"research"/"evidence"/"generated"
SNAP=GEN/"certificate-snapshot.json"
OUT=GEN/"final-gap-report.json"
DISC=ROOT/"research"/"patterns"/"discovered"
DISC.mkdir(parents=True,exist_ok=True)

if not SNAP.exists():
    raise SystemExit("certificate-snapshot.json missing")

snap=json.loads(SNAP.read_text())

required={
  "P01ConstructionGap":{
    "symbol":"MCore.Real.P01FinalCertificate.P01ConstructionGap",
    "formal_prop":"MCore.Real.P01FinalCertificate.P01ConstructionGap",
    "promotion_target":"P01ConstructionGap",
  },
  "G21Pointwise":{
    "symbol":"MCore.Real.P02G21G22Attack.G21Pointwise",
    "formal_prop":"MCore.Real.P02G21G22Attack.G21Pointwise",
    "promotion_target":"G21Pointwise",
  },
  "FinalExternalCertificate":{
    "symbol":"FinalExternalCertificate",
    "formal_prop":None,
    "promotion_target":"FINAL_ROOT / FINAL_PROOF",
  },
}

gaps=[]
for name,spec in required.items():
    obs=snap["producer_observations"].get(name,{})
    state=obs.get("evidence_state","NO_EVIDENCE")
    # Presence of a source/reference is NOT proof of closure.
    # Only exact external CI/certificate verification may upgrade this later.
    gaps.append({
      "gap_id":name,
      "symbol":spec["symbol"],
      "observed_evidence_state":state,
      "status":"NEEDS_VERIFIED_CLOSURE",
      "promotion_target":spec["promotion_target"],
      "source_hits":obs.get("source_hits",[]),
      "proof_credit":0,
      "reason":"Source/certificate references do not establish an inhabitant of the exact producer."
    })
    if spec["formal_prop"]:
        cand={
          "name":f"Gap_{name}",
          "kind":"raw_lean_prop",
          "prop":spec["formal_prop"],
          "claim":f"Exact FINAL_PROOF gap candidate: {name}",
          "lane":"P01_PHYSICAL" if name.startswith("P01") else "G21_SEMANTIC",
          "source":"research/evidence/generated/final-gap-report.json"
        }
        (DISC/f"gap_{name}.json").write_text(json.dumps(cand,indent=2)+"\n")

out={
  "schema":"atk.final-gap-report.v1",
  "repository":snap.get("repository"),
  "sha":snap.get("sha"),
  "run_id":snap.get("run_id"),
  "generated_at":datetime.now(timezone.utc).isoformat(),
  "gaps":gaps,
  "fail_closed":True,
  "note":"A gap is removed only by separately verified exact theorem/certificate evidence."
}
OUT.write_text(json.dumps(out,indent=2,sort_keys=True)+"\n",encoding="utf-8")
print(OUT)
