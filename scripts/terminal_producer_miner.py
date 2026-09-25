#!/usr/bin/env python3
from __future__ import annotations
import json,re,subprocess
from pathlib import Path
from collections import defaultdict

OUT=Path("evidence"); OUT.mkdir(exist_ok=True)

TARGET_PATTERNS={
  "P01MachineConstruction": [
    r"\b(def|theorem|lemma)\s+([A-Za-z0-9_'.]+)[\s\S]{0,500}:\s*P01MachineConstruction\s*:=",
    r"\b(def|theorem|lemma)\s+([A-Za-z0-9_'.]+)[\s\S]{0,500}:\s*Nonempty\s+P01MachineConstruction\b",
    r"\b(def|theorem|lemma)\s+([A-Za-z0-9_'.]+)[\s\S]{0,500}:\s*P01ConstructionGap\b",
  ],
  "P02UniversalWitness": [
    r"\b(def|theorem|lemma)\s+([A-Za-z0-9_'.]+)[\s\S]{0,500}:\s*UniversalWitnessExists\b",
    r"\b(def|theorem|lemma)\s+([A-Za-z0-9_'.]+)[\s\S]{0,500}:\s*Nonempty\s+UniversalWitness\b",
    r"\b(def|theorem|lemma)\s+([A-Za-z0-9_'.]+)[\s\S]{0,500}:\s*DiagonalFamily\s*:=",
    r"\b(def|theorem|lemma)\s+([A-Za-z0-9_'.]+)[\s\S]{0,500}:\s*DiagonalCompilerV2\s*:=",
  ],
  "G3ExternalContract": [
    r"\b(def|theorem|lemma)\s+([A-Za-z0-9_'.]+)[\s\S]{0,500}:\s*G3ExternalContract\s*:=",
    r"\b(def|theorem|lemma)\s+([A-Za-z0-9_'.]+)[\s\S]{0,500}:\s*G3Gap\b",
  ],
}
PLACEHOLDER=re.compile(r"\b(sorry|admit|sorryAx)\b")
COMMENT_BLOCK=re.compile(r"/-[\s\S]*?-/")
COMMENT_LINE=re.compile(r"--.*?$",re.M)

def sh(*args):
    return subprocess.check_output(args,text=True,stderr=subprocess.DEVNULL)

def strip_comments(s):
    return COMMENT_LINE.sub("",COMMENT_BLOCK.sub("",s))

refs=[x.strip() for x in sh("git","for-each-ref","--format=%(refname:short)","refs/remotes/origin").splitlines()]
refs=[r for r in refs if r!="origin/HEAD"]
hits=defaultdict(list)
for ref in refs:
    try:
        files=[p for p in sh("git","ls-tree","-r","--name-only",ref).splitlines() if p.endswith(".lean")]
    except Exception:
        continue
    for path in files:
        try: raw=sh("git","show",f"{ref}:{path}")
        except Exception: continue
        text=strip_comments(raw)
        unsafe=bool(PLACEHOLDER.search(text))
        for target,pats in TARGET_PATTERNS.items():
            for pat in pats:
                for m in re.finditer(pat,text,re.M):
                    start=max(0,m.start()-120); end=min(len(text),m.end()+500)
                    frag=" ".join(text[start:end].split())
                    name=m.group(2) if m.lastindex and m.lastindex>=2 else "unknown"
                    # Classify obvious conditional producers by presence of explicit arguments
                    header=text[m.start():m.end()]
                    conditional=bool(re.search(r"\([^)]*:\s*[^)]*\)",header))
                    hits[target].append({
                      "ref":ref,"file":path,"name":name,
                      "unsafe_file":unsafe,"conditional_header":conditional,
                      "fragment":frag[:1000]
                    })

# de-duplicate
for k,v in hits.items():
    seen=set(); out=[]
    for x in v:
        key=(x["ref"],x["file"],x["name"])
        if key in seen: continue
        seen.add(key); out.append(x)
    hits[k]=out

report={
  "schema":"mcore-pnp-terminal-producer-miner.v1",
  "branches":len(refs),
  "targets":dict(hits),
  "counts":{k:len(v) for k,v in hits.items()},
  "safe_counts":{k:sum(not x["unsafe_file"] for x in v) for k,v in hits.items()},
  "rules":{
    "candidate_not_accepted_until_kernel_build":True,
    "unsafe_files_rejected":True,
    "falsified_fixed_point_route_excluded":True
  }
}
(OUT/"terminal_producer_miner.json").write_text(json.dumps(report,indent=2,sort_keys=True)+"\n")
lines=["ATK_TERMINAL_PRODUCER_MINER",f"BRANCHES={len(refs)}"]
for k in TARGET_PATTERNS:
    lines.append(f"{k}_HITS={report['counts'].get(k,0)}_SAFE={report['safe_counts'].get(k,0)}")
    for x in [y for y in hits.get(k,[]) if not y["unsafe_file"]][:12]:
        lines.append(f"CANDIDATE={k}|{x['ref']}|{x['file']}|{x['name']}|conditional={x['conditional_header']}")
(OUT/"terminal_producer_summary.txt").write_text("\n".join(lines)+"\n")
print("\n".join(lines))
