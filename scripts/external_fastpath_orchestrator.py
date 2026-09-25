#!/usr/bin/env python3
from __future__ import annotations
import json,sys
from pathlib import Path

p=Path("final-proof/external-fastpath-registry.json")
d=json.loads(p.read_text())
claims=d["claims"]
closed={"GREEN","FROZEN","CERTIFIED","CLOSED"}

def validate():
    errors=[]
    for name,c in claims.items():
        state=c["state"]
        if state in closed:
            ev=c.get("evidence",[])
            if name not in {"G3_EXTERNAL_CONTRACT"} and not ev and not c.get("exact_term"):
                errors.append(f"{name}: closed without evidence")
            for e in ev:
                if not e.get("sha") or not e.get("run"):
                    errors.append(f"{name}: incomplete evidence {e}")
        if state=="OPEN_MATH" and c.get("promoted",False):
            errors.append(f"{name}: OPEN_MATH cannot be promoted")
    if d["policy"].get("falsified_routes_reopen") is not False:
        errors.append("falsified route policy must remain false")
    return errors

def frontier(target):
    seen=set()
    def walk(n):
        if n in seen: return set()
        seen.add(n)
        c=claims[n]
        if c["state"]=="OPEN_MATH":
            return {n}
        if c["state"] in closed:
            return set()
        deps=c.get("deps",[])
        if not deps:
            return {n}
        out=set()
        for x in deps: out |= walk(x)
        return out or {n}
    return sorted(walk(target))

errors=validate()
f=frontier(d["target"])
summary={
  "schema":"elyon.external-fastpath-summary.v1",
  "target":d["target"],
  "minimal_frontier":f,
  "frontier_count":len(f),
  "validation_errors":errors,
  "ready_for_external":not f and not errors,
}
Path("evidence").mkdir(exist_ok=True)
Path("evidence/external_fastpath_summary.json").write_text(json.dumps(summary,indent=2)+"\n")
print(json.dumps(summary,indent=2))
if errors: sys.exit(2)
