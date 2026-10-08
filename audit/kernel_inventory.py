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
    # Kernel-checked declaration audit: query Lean for every named theorem/lemma.
    # An empty list means no named theorem was discovered, not that axioms are absent.
    declarations = re.findall(r"(?m)^\\s*(?:private\\s+|protected\\s+)?(?:theorem|lemma)\\s+([A-Za-z_][A-Za-z_0-9']*)", source)
    namespace_stack = []
    for line in source.splitlines():
        match = re.match(r"^\\s*namespace\\s+([A-Za-z_][A-Za-z_0-9.]*)", line)
        if match:
            namespace_stack.append(match.group(1))
    # The declarations may be nested in sections; if resolution fails, record that fact.
    axiom_checks = []
    if state == "BUILD_GREEN" and declarations:
        full_prefix = ".".join(namespace_stack)
        query = "import " + module + "\\n" + "\\n".join(
            "#print axioms " + (full_prefix + "." if full_prefix else "") + name
            for name in declarations) + "\\n"
        import tempfile
        with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", dir=ROOT, delete=False) as temp:
            temp.write(query)
            probe = pathlib.Path(temp.name)
        try:
            result = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT,
                                    capture_output=True, text=True, timeout=240)
            lines = (result.stdout + "\\n" + result.stderr).splitlines()
            for name in declarations:
                matches = [line for line in lines if name in line and "depends on axioms:" in line]
                axiom_checks.append({"declaration": name, "status": "CHECKED" if matches else "UNRESOLVED",
                                     "kernel_output": matches[-1] if matches else ""})
            if result.returncode != 0:
                flags.append("AXIOM_PROBE_FAILED")
        except subprocess.TimeoutExpired:
            flags.append("AXIOM_PROBE_TIMEOUT")
        finally:
            probe.unlink(missing_ok=True)
    elif state != "BUILD_GREEN":
        flags.append("AXIOM_AUDIT_BLOCKED_BY_BUILD")
    records.append({"module": module, "path": str(p.relative_to(ROOT)),
                    "build": state, "lint_flags": flags, "diagnostics": output if state != "BUILD_GREEN" else "",
                    "axiom_audit": axiom_checks, "math_terminal": "NOT_ASSESSED"})
    print(f"{state} {module}", flush=True)
data = {"schema": 1, "commit": os.environ.get("GITHUB_SHA", "LOCAL"),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "generated_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "total": len(records), "modules": records,
        "warning": "BUILD_GREEN and axiom checks are not terminal mathematical proof; inspect each theorem statement."}
OUT.write_text(json.dumps(data, indent=2, ensure_ascii=False) + "\n")
print(f"Inventory: {OUT}; {sum(r['build'] == 'BUILD_RED' for r in records)} red")
if any(r["build"] != "BUILD_GREEN" for r in records):
    sys.exit(1)
