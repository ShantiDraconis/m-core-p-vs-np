"""Collect every (sha, run, theorems, source-record) claim from the
certificate records of m-core-p-vs-np@main and M-Core@main.

Usage: python3 -I collect_certs.py PVSNP_REPO MCORE_REPO OUT_JSON
"""
import json, re, subprocess, sys

pvsnp, mcore, out = sys.argv[1:4]

def show(repo, ref, path):
    return subprocess.run(["git", "-C", repo, "show", f"{ref}:{path}"],
                          capture_output=True, text=True).stdout

def ls(repo, ref, prefix):
    r = subprocess.run(["git", "-C", repo, "ls-tree", "-r", "--name-only", ref, prefix],
                       capture_output=True, text=True).stdout
    return [x for x in r.splitlines() if x]

SHA = re.compile(r"\b[0-9a-f]{40}\b")
RUN = re.compile(r"\b3[4-8]\d{9}\b")
THM = re.compile(r"`((?:MCore\.)?[A-Za-z_][A-Za-z0-9_'.]*)`")

records = []

def add(repo, record, sha, runs, theorems, extra=None):
    records.append({"repository": repo, "record": record, "sha": sha,
                    "runs": sorted(set(runs)), "theorems": sorted(set(theorems)),
                    **(extra or {})})

# 1. Markdown certificates (one SHA per file, runs listed, theorems in backticks)
for repo_name, repo, ref, prefixes in [
        ("ShantiDraconis/m-core-p-vs-np", pvsnp, "origin/main", ["CERTIFICATES", "certificates"]),
        ("ShantiDraconis/M-Core", mcore, "origin/HEAD", ["CERTIFICATES", "certs"])]:
    for pre in prefixes:
        for path in ls(repo, ref, pre):
            if not path.endswith(".md"):
                continue
            text = show(repo, ref, path)
            shas = SHA.findall(text)
            runs = RUN.findall(text)
            if not shas and not runs:
                continue
            thms = [t for t in THM.findall(text)
                    if not SHA.fullmatch(t) and ("_" in t or "." in t) and not t.startswith(("frozen", "cert", "atk"))]
            add(repo_name, path, shas[0] if shas else None, runs, thms,
                {"all_shas_in_record": sorted(set(shas))})

# 2. JSON records: walk objects, pairing sha/run fields that sit together
def walk(obj, path, sink):
    if isinstance(obj, dict):
        s = None
        for k in ("sha", "source_frozen_commit", "commit", "head", "certified_commit", "source_sha"):
            v = obj.get(k)
            if isinstance(v, str) and SHA.fullmatch(v):
                s = v
                break
        runs = []
        for k, v in obj.items():
            if k in ("run", "run_id", "verified_run", "id") and isinstance(v, (int, str)) and RUN.fullmatch(str(v)):
                runs.append(str(v))
            if k in ("runs", "verified_runs") and isinstance(v, list):
                runs += [str(x) for x in v if RUN.fullmatch(str(x))]
            if k == "certifying_runs" and isinstance(v, list):
                runs += [str(x.get("id")) for x in v if isinstance(x, dict) and RUN.fullmatch(str(x.get("id")))]
        thms = []
        for k in ("theorem", "theorems", "object", "machine"):
            v = obj.get(k)
            if isinstance(v, str):
                thms.append(v)
            elif isinstance(v, list):
                thms += [x for x in v if isinstance(x, str)]
        if s or runs:
            sink.append((path, s, runs, thms))
        for k, v in obj.items():
            walk(v, f"{path}.{k}", sink)
    elif isinstance(obj, list):
        for i, v in enumerate(obj):
            walk(v, f"{path}[{i}]", sink)

for repo_name, repo, ref, paths in [
        ("ShantiDraconis/m-core-p-vs-np", pvsnp, "origin/main",
         ["GATE_LEDGER.json", "audit/ATK_P01_MATERIAL_FRONTIER_V1.json"] +
         [p for p in ls(pvsnp, "origin/main", "CERTIFICATES") if p.endswith(".json")]),
        ("ShantiDraconis/M-Core", mcore, "origin/HEAD",
         [p for p in ls(mcore, "origin/HEAD", "certs") if p.endswith(".json")] +
         [p for p in ls(mcore, "origin/HEAD", "evidence") if p.endswith(".json")] +
         [p for p in ls(mcore, "origin/HEAD", "final-proof") if p.endswith(".json")])]:
    for p in paths:
        try:
            data = json.loads(show(repo, ref, p))
        except Exception:
            continue
        sink = []
        walk(data, "$", sink)
        for jpath, s, runs, thms in sink:
            add(repo_name, f"{p}{jpath}", s, runs, thms)

json.dump(records, open(out, "w"), indent=1)
pairs = {(r["sha"], run) for r in records for run in r["runs"]}
print(f"records: {len(records)} | distinct (sha,run) pairs: {len(pairs)} | "
      f"distinct runs: {len({run for r in records for run in r['runs']})} | "
      f"distinct shas: {len({r['sha'] for r in records if r['sha']})}")
