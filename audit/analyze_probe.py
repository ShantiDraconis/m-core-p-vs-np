#!/usr/bin/env python3
import csv, hashlib, json, sys
from collections import Counter, defaultdict
from pathlib import Path

src = Path(sys.argv[1] if len(sys.argv) > 1 else "c13_probe.csv")
out = Path(sys.argv[2] if len(sys.argv) > 2 else "audit/C13_BIDIRECTIONAL_PROBE.generated.json")
raw = src.read_bytes()
with src.open(newline="", encoding="utf-8") as f:
    rows = list(csv.DictReader(f))

def I(r,k): return int(r[k])
def pays(r): return r["paysOff"].lower() == "true"
def margin(r): return I(r,"potentialBefore") - I(r,"payoffLhs")

by_k = {}
for k in [0,1]:
    rs=[r for r in rows if I(r,"k")==k]
    by_k[str(k)]={
      "rows":len(rs),
      "true":sum(pays(r) for r in rs),
      "false":sum(not pays(r) for r in rs),
      "zero_margin":sum(margin(r)==0 for r in rs),
      "negative_margin":sum(margin(r)<0 for r in rs),
      "min_margin":min(map(margin,rs)),
      "max_margin":max(map(margin,rs)),
    }

groups=defaultdict(list)
for r in rows:
    groups[(r["family"],I(r,"n"),I(r,"seed"))].append(r)

violations_k0=[{
  "family":r["family"],"n":I(r,"n"),"seed":I(r,"seed"),"margin":margin(r)
} for r in rows if I(r,"k")==0 and pays(r)]
violations_k1=[{
  "family":r["family"],"n":I(r,"n"),"seed":I(r,"seed"),"margin":margin(r),
  "deltaRank":I(r,"deltaRank"),"costBits":I(r,"costBits")
} for r in rows if I(r,"k")==1 and not pays(r)]

summary={
 "schema":"C13_BIDIRECTIONAL_PROBE_v1",
 "epistemic_status":"FINITE_COMPUTATIONAL_EVIDENCE_ONLY / NO_ORIENTATION_OF_D",
 "source_sha256":hashlib.sha256(raw).hexdigest(),
 "data_rows":len(rows),
 "n_range":[13,64],
 "k_values":[0,1],
 "random_seeds":8,
 "families":sorted(set(r["family"] for r in rows)),
 "by_k":by_k,
 "k0_unexpected_positive":violations_k0,
 "k1_failures":violations_k1,
 "k0_pattern_holds":not violations_k0,
 "k1_pattern_holds":not violations_k1,
 "family_counts":dict(Counter(r["family"] for r in rows)),
 "guard":[
  "This probe tests an internal C11/C12 potential regularity only.",
  "It does not prove A0 for all n.",
  "It does not imply D, not D, P=NP, or P!=NP."
 ]
}
out.parent.mkdir(parents=True,exist_ok=True)
out.write_text(json.dumps(summary,indent=2,sort_keys=True)+"\n",encoding="utf-8")
print(json.dumps(summary,sort_keys=True))
