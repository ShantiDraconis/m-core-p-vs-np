#!/usr/bin/env python3
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DISCOVERED = ROOT / "research" / "patterns" / "discovered"
GENERATED = ROOT / "lean" / "MCore" / "Research" / "Generated"
OPEN = ROOT / "research" / "patterns" / "open"
REGISTRY = ROOT / "research" / "patterns" / "registry.json"

DISCOVERED.mkdir(parents=True, exist_ok=True)
GENERATED.mkdir(parents=True, exist_ok=True)
OPEN.mkdir(parents=True, exist_ok=True)

def slug(s):
    return re.sub(r"[^A-Za-z0-9_]", "_", s)

def stable_id(obj):
    canon = json.dumps(obj, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(canon).hexdigest()[:16]

def proposition(c):
    kind = c["kind"]
    if kind == "nat_eq":
        return f'{int(c["lhs"])} = {int(c["rhs"])}'
    if kind == "nat_le":
        return f'{int(c["lhs"])} ≤ {int(c["rhs"])}'
    if kind == "nat_lt":
        return f'{int(c["lhs"])} < {int(c["rhs"])}'
    if kind == "int_eq":
        return f'({int(c["lhs"])} : Int) = {int(c["rhs"])}'
    if kind == "prime":
        return f'Nat.Prime {int(c["n"])}'
    if kind == "divides":
        return f'{int(c["a"])} ∣ {int(c["b"])}'
    if kind == "not_divides":
        return f'¬ ({int(c["a"])} ∣ {int(c["b"])})'
    if kind == "raw_lean_prop":
        prop = str(c["prop"]).strip()
        forbidden = [
            "\n", "\r", "axiom", "constant", "constants", "sorry", "admit",
            "unsafe", "import", "namespace", "theorem", "lemma", "def ", "#"
        ]
        low = prop.lower()
        if any(tok in low for tok in forbidden):
            raise ValueError("unsafe raw_lean_prop")
        return prop
    raise ValueError(f"unsupported kind: {kind}")

def safe_autoprove(c):
    return c["kind"] in {
        "nat_eq", "nat_le", "nat_lt", "int_eq",
        "prime", "divides", "not_divides"
    }

def lean_source(c, pid, attempt_proof):
    ns = slug(c.get("name", f"Pattern_{pid}"))
    prop = proposition(c)
    lines = [
        "import Mathlib",
        "import MCore.Research.PatternCalculator",
        "",
        "namespace MCore",
        "namespace Research",
        "namespace Generated",
        "",
        f"/-- Auto-discovered research pattern. Stable id: {pid}. -/",
        f"def {ns}_statement : Prop := {prop}",
        "",
    ]
    if attempt_proof:
        lines += [
            f"theorem {ns}_verified : {ns}_statement := by",
            "  native_decide",
            "",
            f"#print axioms MCore.Research.Generated.{ns}_verified",
        ]
    else:
        lines += [
            "/-- OPEN_MATH: proposition formalized, no proof asserted. -/",
            f'def {ns}_status : String := "OPEN_MATH"',
        ]
    lines += ["", "end Generated", "end Research", "end MCore", ""]
    return "\n".join(lines)

def lean_check(path):
    p = subprocess.run(
        ["lake", "env", "lean", str(path)],
        cwd=ROOT,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
    )
    return p.returncode == 0, p.stdout

registry = []
if REGISTRY.exists():
    try:
        registry = json.loads(REGISTRY.read_text())
    except Exception:
        registry = []

known = {
    x.get("pattern_id")
    for x in registry
    if isinstance(x, dict)
}

for src in sorted(DISCOVERED.glob("*.json")):
    candidate = json.loads(src.read_text())
    pid = stable_id(candidate)
    if pid in known:
        continue

    name = slug(candidate.get("name", f"Pattern_{pid}"))
    out = GENERATED / f"{name}_{pid}.lean"

    attempted = safe_autoprove(candidate)
    out.write_text(lean_source(candidate, pid, attempted), encoding="utf-8")

    formalized = False
    proof_log = ""
    if attempted:
        formalized, proof_log = lean_check(out)

    if not formalized:
        out.write_text(lean_source(candidate, pid, False), encoding="utf-8")
        ok, open_log = lean_check(out)
        if not ok:
            raise SystemExit(
                f"Generated OPEN_MATH Lean file did not compile: {out}\n{open_log}"
            )
        open_record = {
            "pattern_id": pid,
            "name": candidate.get("name", name),
            "status": "OPEN_MATH",
            "source": str(src.relative_to(ROOT)),
            "lean_file": str(out.relative_to(ROOT)),
            "claim": candidate.get("claim"),
            "kind": candidate["kind"],
            "proof_credit": 0,
            "proof_attempt_log_tail": proof_log[-4000:] if proof_log else None,
        }
        (OPEN / f"{name}_{pid}.json").write_text(
            json.dumps(open_record, indent=2, sort_keys=True) + "\n"
        )
        status = "OPEN_MATH"
    else:
        status = "FORMALIZED"

    registry.append({
        "pattern_id": pid,
        "name": candidate.get("name", name),
        "status": status,
        "source": str(src.relative_to(ROOT)),
        "lean_file": str(out.relative_to(ROOT)),
        "claim": candidate.get("claim"),
        "kind": candidate["kind"],
        "proof_credit": 0,
    })
    known.add(pid)
    print(f"{pid} {status} {out.relative_to(ROOT)}")

REGISTRY.parent.mkdir(parents=True, exist_ok=True)
REGISTRY.write_text(
    json.dumps(registry, indent=2, sort_keys=True) + "\n",
    encoding="utf-8",
)
