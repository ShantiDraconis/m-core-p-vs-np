#!/usr/bin/env python3
import json, pathlib, collections

ROOT=pathlib.Path(__file__).resolve().parents[1]

def load_graph(path=ROOT/"audit"/"ATL_GRAPH.json"):
    data=json.loads(path.read_text())
    nodes={n["id"]:n for n in data["nodes"]}
    log_by=collections.defaultdict(list)
    for e in data.get("log",[]): log_by[e["node_id"]].append(e)
    consumers=collections.defaultdict(list)
    for n in nodes.values():
        for d in n.get("declared_dependencies",[]):
            if d in nodes: consumers[d].append(n["id"])
    return data,nodes,log_by,consumers

def derive_replacement_path(node,nodes):
    route=node.get("declared_replacement_nodes",[])
    if not route: return []
    if any(x not in nodes for x in route): return None
    return route

def latest_event(logs):
    return logs[-1] if logs else None

def derive_state(node,logs,nodes,consumers):
    ev=latest_event(logs)
    derived={
      "dependencies":[d for d in node.get("declared_dependencies",[]) if d in nodes],
      "consumers":consumers.get(node["id"],[]),
      "replacement_route":derive_replacement_path(node,nodes),
      "proof_state":"UNKNOWN",
      "build_state":"UNKNOWN",
      "kernel_state":"UNKNOWN",
      "axiom_state":"UNKNOWN",
      "semantic_state":"UNKNOWN",
      "certificate_state":"UNKNOWN",
      "provenance_state": ev.get("provenance_state") if ev else None
    }
    if ev:
        evt=ev.get("event","")
        if evt in {"GREEN","FROZEN","CERTIFIED"}:
            derived["build_state"]="GREEN"
        if evt=="CERTIFIED":
            derived["certificate_state"]="CERTIFIED"
        if evt.startswith("RED"):
            derived["build_state"]="RED"
    return derived

if __name__=="__main__":
    data,nodes,logs,consumers=load_graph()
    out={}
    for nid,node in nodes.items():
        out[nid]={"primitive":node,"derived":derive_state(node,logs[nid],nodes,consumers),"log":logs[nid]}
    print(json.dumps(out,indent=2,sort_keys=True))
