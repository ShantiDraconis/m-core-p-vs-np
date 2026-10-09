"""Look up every run referenced by the certificate records via the GitHub
REST API (repository-scoped), and resolve every claimed SHA to a repository.

Usage: python3 -I verify_runs.py RECORDS_JSON PVSNP_REPO MCORE_REPO OUT_JSON
"""
import json, subprocess, sys

records_path, pvsnp, mcore, out = sys.argv[1:5]
records = json.load(open(records_path))
REPOS = ["ShantiDraconis/m-core-p-vs-np", "ShantiDraconis/M-Core"]

def gh(path):
    p = subprocess.run(["gh", "api", path], capture_output=True, text=True)
    if p.returncode != 0:
        return None
    try:
        return json.loads(p.stdout)
    except Exception:
        return None

runs = {}
for run in sorted({r for rec in records for r in rec["runs"]}):
    info = None
    for repo in REPOS:
        d = gh(f"repos/{repo}/actions/runs/{run}")
        if d and d.get("id"):
            jobs = gh(f"repos/{repo}/actions/runs/{run}/jobs") or {}
            steps = [f"{s['name']}={s['conclusion']}" for j in jobs.get("jobs", []) for s in j.get("steps", [])]
            info = {"repo": repo, "name": d.get("name"), "workflow_path": d.get("path"),
                    "head_sha": d.get("head_sha"), "head_branch": d.get("head_branch"),
                    "status": d.get("status"), "conclusion": d.get("conclusion"),
                    "created_at": d.get("created_at"), "steps": steps}
            break
    runs[run] = info or {"repo": None, "conclusion": "NOT_FOUND"}
    print(run, runs[run].get("repo"), runs[run].get("conclusion"), (runs[run].get("head_sha") or "")[:10], runs[run].get("name"))

def sha_repo(sha):
    hits = []
    for name, path in (("ShantiDraconis/m-core-p-vs-np", pvsnp), ("ShantiDraconis/M-Core", mcore)):
        if subprocess.run(["git", "-C", path, "cat-file", "-e", f"{sha}^{{commit}}"],
                          capture_output=True).returncode == 0:
            hits.append(name)
    if not hits:
        for repo in REPOS:
            d = gh(f"repos/{repo}/commits/{sha}")
            if d and d.get("sha") == sha:
                hits.append(repo + " (api)")
    return hits

shas = {}
for sha in sorted({r["sha"] for r in records if r["sha"]}):
    shas[sha] = sha_repo(sha)

json.dump({"runs": runs, "shas": shas}, open(out, "w"), indent=1)
print("runs:", len(runs), "found:", sum(1 for v in runs.values() if v.get("repo")),
      "| shas:", len(shas), "resolved:", sum(1 for v in shas.values() if v))
