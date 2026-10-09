"""Build the kernel-check target list: one entry per certified SHA of
m-core-p-vs-np that has at least one successful run.
Usage: python3 -I make_targets.py RECORDS RUNS OUT
"""
import json, sys

records = json.load(open(sys.argv[1]))
runs = json.load(open(sys.argv[2]))["runs"]
GENERIC = {"certificate", "fail-proof-all-gaps"}
# Theorem names stated in prose/code blocks that the regex did not capture.
EXTRA = {
    "dfb3e60dc37e96f46a3ca071c428456634ec6dca": ["MCore.Real.P01GlobalParserBound.slot_parser_machine_simulation_certificate"],
}
by_sha = {}
for r in records:
    sha = r["sha"]
    if not sha:
        continue
    for run in r["runs"]:
        info = runs.get(run, {})
        if info.get("repo") != "ShantiDraconis/m-core-p-vs-np" or info.get("head_sha") != sha:
            continue
        e = by_sha.setdefault(sha, {"sha": sha, "runs": [], "theorems": set(), "records": set()})
        e["runs"].append(run)
        e["records"].add(r["record"].split("$")[0])
        e["theorems"] |= {t for t in r["theorems"] if not t.endswith(".lean")}
targets = []
for sha, e in by_sha.items():
    rs = sorted(set(e["runs"]), key=lambda x: (runs[x]["name"] in GENERIC, x))
    best = rs[0]
    targets.append({"sha": sha, "run": best, "all_runs": rs,
                    "workflow_path": runs[best]["workflow_path"], "workflow_name": runs[best]["name"],
                    "theorems": sorted(e["theorems"] | set(EXTRA.get(sha, []))),
                    "record": sorted(e["records"])})
targets.sort(key=lambda t: t["run"])
json.dump(targets, open(sys.argv[3], "w"), indent=1)
for t in targets:
    print(t["sha"][:10], t["run"], t["workflow_name"][:32], len(t["theorems"]), t["record"][0][:60])
print(len(targets), "targets")
