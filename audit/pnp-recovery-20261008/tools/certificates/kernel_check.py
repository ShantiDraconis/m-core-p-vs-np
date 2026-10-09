"""Kernel-check each certified (sha, run) of m-core-p-vs-np locally.

For each target:
  * resolve the certified theorem names to declaring modules at that SHA;
  * read the CI workflow at that SHA and record which modules it builds,
    and whether those builds transitively import the declaring modules;
  * build the declaring modules locally with Lean 4.19.0 and collect the
    `#print axioms` lines the files themselves emit;
  * additionally run an explicit `#print axioms` for each resolved theorem.

Usage: python3 -I kernel_check.py TARGETS_JSON REPO OUT_JSON [START END]
"""
import json, os, re, shutil, subprocess, sys

targets_path, repo, out = sys.argv[1:4]
start = int(sys.argv[4]) if len(sys.argv) > 4 else 0
end = int(sys.argv[5]) if len(sys.argv) > 5 else 10**6
LEAN_BIN = "/home/claude/lean-toolchain/lean-4.19.0-linux/bin"
ENV = dict(os.environ, PATH=LEAN_BIN + ":" + os.environ["PATH"])
CACHE = "/home/claude/wt/integ/.lake"
WT = "/home/claude/wt/kc"
STANDARD = {"propext", "Classical.choice", "Quot.sound"}

def git(*a):
    return subprocess.run(["git", "-C", repo, *a], capture_output=True, text=True).stdout

def files_at(sha):
    return [p for p in git("ls-tree", "-r", "--name-only", sha).splitlines() if p.endswith(".lean")]

def src_dir(sha):
    t = git("show", f"{sha}:lakefile.toml")
    m = re.search(r'srcDir\s*=\s*"([^"]+)"', t)
    return m.group(1) if m else "lean"

def module_of(path, srcdir):
    rel = path[len(srcdir) + 1:] if path.startswith(srcdir + "/") else path
    return rel[:-5].replace("/", ".")

def resolve(sha, short_names, srcdir):
    """Map theorem short names to (module, fully qualified name)."""
    res = {}
    for name in short_names:
        short = name.split(".")[-1]
        out = git("grep", "-nE", rf"^\s*(@\[[^]]*\]\s*)?(private |protected |noncomputable )*(theorem|lemma|def|abbrev|structure|instance)\s+([A-Za-z0-9_.']*\.)?{re.escape(short)}\b", sha, "--", f"{srcdir}/*.lean")
        hits = []
        for line in out.splitlines():
            _, path, ln, _ = line.split(":", 3)
            text = git("show", f"{sha}:{path}")
            ns = []
            for l in text.splitlines()[: int(ln) - 1]:
                m = re.match(r"^namespace\s+(\S+)", l)
                if m: ns.append(m.group(1))
                m = re.match(r"^end\s+(\S+)", l)
                if m and ns and ns[-1] == m.group(1): ns.pop()
            decl = re.search(r"(theorem|lemma|def|abbrev|structure|instance)\s+(\S+)", line.split(":", 3)[3]).group(2)
            fq = ".".join(ns + [decl]) if ns else decl
            hits.append((module_of(path, srcdir), fq))
        if name.startswith("MCore."):
            hits = [h for h in hits if h[1] == name] or hits
        res[name] = hits
    return res

def imports_closure(sha, roots, srcdir):
    seen, stack = set(), list(roots)
    while stack:
        m = stack.pop()
        if m in seen: continue
        seen.add(m)
        text = git("show", f"{sha}:{srcdir}/{m.replace('.', '/')}.lean")
        for imp in re.findall(r"^import\s+(\S+)", text, re.M):
            if imp.startswith("MCore") or imp.startswith(("C1", "P0")):
                stack.append(imp)
    return seen

def workflow_targets(sha, wf_path):
    if not wf_path: return []
    y = git("show", f"{sha}:{wf_path}")
    t = []
    for m in re.finditer(r"lake build([^\n|&;]*)", y):
        t += [x for x in m.group(1).split() if not x.startswith("-") and not x.startswith("$") and x != "\\"]
    for m in re.finditer(r"^\s*import\s+(MCore\S+)", y, re.M):
        t.append(m.group(1))
    return sorted(set(t))

results = json.load(open(out)) if os.path.exists(out) else {}
targets = json.load(open(targets_path))[start:end]
for tgt in targets:
    key = f"{tgt['sha']}:{tgt['run']}"
    if key in results and results[key].get("build_exit") is not None:
        continue
    sha = tgt["sha"]
    srcdir = src_dir(sha)
    uses_mathlib = "mathlib" in git("show", f"{sha}:lakefile.toml").lower()
    wf_yaml = git("show", f"{sha}:{tgt.get('workflow_path')}") if tgt.get("workflow_path") else ""
    wf_printed = sorted({n.rstrip("\\") for n in re.findall(r"#print axioms\s+((?:MCore\.)?[A-Za-z_][A-Za-z0-9_'.]*)", wf_yaml)})
    resolved = resolve(sha, sorted(set(tgt["theorems"]) | set(wf_printed)), srcdir)
    decl_mods = sorted({m for hits in resolved.values() for m, _ in hits} | set(tgt.get("modules", [])))
    wf_t = workflow_targets(sha, tgt.get("workflow_path"))
    wf_t = [x for x in wf_t if re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*(\.[A-Za-z0-9_]+)*", x)]
    wf_mods = [x for x in wf_t if x.startswith("MCore")]
    if "MCore" in wf_t or not wf_t and False:
        wf_mods.append("MCore")
    if not decl_mods:
        decl_mods = sorted(set(wf_mods))
        rec_note = "no theorem names in record; checking the modules the certifying workflow builds"
    else:
        rec_note = ""
    closure = imports_closure(sha, [m for m in wf_mods if m != "MCore"] + (["MCore"] if "MCore" in wf_mods else []), srcdir) if wf_mods else set()
    ci_covers = {m: (m in closure) for m in decl_mods}
    rec = {"sha": sha, "run": tgt["run"], "record": tgt["record"], "lakefile_requires_mathlib": uses_mathlib,
           "resolved": resolved, "declaring_modules": decl_mods, "workflow_path": tgt.get("workflow_path"),
           "workflow_build_targets": wf_t, "workflow_audited_names": wf_printed, "ci_build_covers_declaring_module": ci_covers,
           "note": rec_note}
    if uses_mathlib or not decl_mods:
        rec["build_exit"] = None
        rec["note"] = "skipped: requires Mathlib" if uses_mathlib else "skipped: no declaring module resolved"
        results[key] = rec
        json.dump(results, open(out, "w"), indent=1)
        print(key[:20], rec["note"], flush=True)
        continue
    if os.path.exists(WT):
        subprocess.run(["git", "-C", repo, "worktree", "remove", "--force", WT], capture_output=True)
    subprocess.run(["git", "-C", repo, "worktree", "add", "-q", "--detach", WT, sha], check=True, capture_output=True)
    shutil.copytree(CACHE, f"{WT}/.lake", symlinks=True)
    p = subprocess.run(["timeout", "1500", "lake", "build", *decl_mods], cwd=WT, env=ENV, capture_output=True, text=True)
    log = p.stdout + p.stderr
    rec["build_exit"] = p.returncode
    rec["build_errors"] = [l for l in log.splitlines() if "error:" in l][:8]
    # explicit axiom audit for every resolved fully-qualified theorem
    fqs = sorted({fq for hits in resolved.values() for _, fq in hits})
    axioms = {}
    if p.returncode == 0 and fqs:
        probe = "\n".join(f"import {m}" for m in decl_mods) + "\n" + "\n".join(f"#print axioms {fq}" for fq in fqs) + "\n"
        open(f"{WT}/KcProbe.lean", "w").write(probe)
        q = subprocess.run(["timeout", "600", "lake", "env", "lean", "KcProbe.lean"], cwd=WT, env=ENV, capture_output=True, text=True)
        text = q.stdout + q.stderr
        for m in re.finditer(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text, re.S):
            ax = [a.strip() for a in (m.group(3) or "").split(",") if a.strip()]
            axioms[m.group(1)] = ax
        rec["probe_errors"] = [l for l in text.splitlines() if "error" in l][:6]
    # axiom reports the declaring modules emit themselves during the build
    mod_paths = {f"{srcdir}/{m.replace('.', '/')}.lean" for m in decl_mods}
    file_axioms = {}
    open(os.path.join(os.path.dirname(out), f"kc_build_{sha[:12]}.log"), "w").write(log)
    for m in re.finditer(r"(?:info|warning): (?:\./)*([^:\s]+\.lean):\d+:\d+: '([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log, re.S):
        if m.group(1) in mod_paths:
            file_axioms[m.group(2)] = [a.strip() for a in (m.group(4) or "").split(",") if a.strip()]
    for k, v in file_axioms.items():
        axioms.setdefault(k, v)
    rec["axioms"] = axioms
    rec["axiom_reports_from_module_files"] = len(file_axioms)
    rec["all_axioms_standard"] = p.returncode == 0 and bool(axioms) and all(set(v) <= STANDARD for v in axioms.values())
    rec["sorry_detected"] = any("sorryAx" in v for v in axioms.values()) or "sorryAx" in log
    results[key] = rec
    json.dump(results, open(out, "w"), indent=1)
    print(key[:20], "exit", p.returncode, "| mods", len(decl_mods), "| thms", len(fqs), "| axioms ok" if rec["all_axioms_standard"] else "| axioms ?", "| CI covers:", ci_covers, flush=True)

subprocess.run(["git", "-C", repo, "worktree", "remove", "--force", WT], capture_output=True)
