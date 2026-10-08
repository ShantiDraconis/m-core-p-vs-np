#!/usr/bin/env python3
"""Generate a kernel-derived per-module inventory; never infer math closure from builds."""
import json, os, pathlib, re, subprocess, sys, datetime
ROOT = pathlib.Path(__file__).resolve().parents[1]
SRC = ROOT / "lean"
OUT = ROOT / "artifacts" / "kernel-inventory.json"
OUT.parent.mkdir(parents=True, exist_ok=True)
modules = sorted(p for p in SRC.rglob("*.lean"))
records = []
for p in modules:
    module = ".".join(p.relative_to(SRC).with_suffix("").parts)
    command = ["lake", "build", module]
    try:
        run = subprocess.run(command, cwd=ROOT, capture_output=True, text=True, timeout=900)
        state = "BUILD_GREEN" if run.returncode == 0 else "BUILD_RED"
        output = (run.stdout + "\n" + run.stderr)[-5000:]
    except subprocess.TimeoutExpired:
        state, output = "BUILD_TIMEOUT", "Exceeded 900 seconds"
    source = p.read_text(encoding="utf-8")
    flags = []
    if re.search(r"\\b(?:sorry|admit|sorryAx)\\b", source):
        flags.append("PLACEHOLDER_TOKEN_REVIEW")
    if re.search(r"(?:→|->)\\s*True\\b", source):
        flags.append("TRIVIAL_TRUE_CODOMAIN_REVIEW")
    if re.search(r"\\b(?:theorem|lemma)\\s+\\w+[\\s\\S]{0,300}?:\\s*True\\s*:=", source):
        flags.append("TRIVIAL_THEOREM_REVIEW")
    records.append({"module": module, "path": str(p.relative_to(ROOT)),
                    "build": state, "lint_flags": flags, "diagnostics": output if state != "BUILD_GREEN" else "",
                    "axiom_audit": "NOT_CHECKED", "math_terminal": "NOT_ASSESSED"})
    print(f"{state} {module}", flush=True)
data = {"schema": 1, "commit": os.environ.get("GITHUB_SHA", "LOCAL"),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "generated_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "total": len(records), "modules": records,
        "warning": "BUILD_GREEN is not a terminal mathematical proof. Axiom audit is NOT_CHECKED."}
OUT.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")
print(f"Inventory: {OUT}; {sum(r['build'] == 'BUILD_RED' for r in records)} red")
if any(r["build"] != "BUILD_GREEN" for r in records):
    sys.exit(1)
