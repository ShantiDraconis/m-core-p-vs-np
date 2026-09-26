#!/usr/bin/env python3
import json, pathlib, collections
from atl_graph_loader import load_graph, derive_state

ROOT=pathlib.Path(__file__).resolve().parents[1]

def descendants(start,consumers):
    seen=set(); q=list(consumers.get(start,[]))
    while q:
        x=q.pop()
        if x in seen: continue
        seen.add(x); q.extend(consumers.get(x,[]))
    return seen

def history_cost(node_id,hist):
    vals=[x["cost_cycles"] for x in hist.get("samples",[]) if x.get("node_id")==node_id and x.get("cost_cycles") is not None]
    if vals: return sum(vals)/len(vals)
    return hist.get("heuristic",{}).get("default_cost_cycles",3.0)

def score(node_id,node,consumers,hist):
    p=hist.get("heuristic",{}).get("default_failure_probability",0.5)
    cost=history_cost(node_id,hist)*p
    unlock=max(1,len(descendants(node_id,consumers)))
    return cost/unlock,unlock,cost

if __name__=="__main__":
    data,nodes,logs,consumers=load_graph()
    hist=json.loads((ROOT/"audit"/"cost_history.json").read_text())
    rows=[]
    for nid,n in nodes.items():
        if n.get("attackability")!="ATTACKABLE": continue
        s,u,c=score(nid,n,consumers,hist)
        rows.append({"node_id":nid,"cut_value":s,"downstream_unlock":u,"expected_cost":c})
    rows.sort(key=lambda r:(r["cut_value"],-r["downstream_unlock"],r["node_id"]))
    print(json.dumps(rows,indent=2))
