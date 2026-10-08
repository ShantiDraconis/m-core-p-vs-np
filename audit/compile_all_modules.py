#!/usr/bin/env python3
"""Compile all Lean modules individually and together using a generated import root."""
import pathlib, subprocess, sys
root = pathlib.Path(__file__).resolve().parents[1]
source = root / "lean"
modules = sorted(".".join(p.relative_to(source).with_suffix("").parts)
                 for p in source.rglob("*.lean"))
generated = root / "artifacts" / "AllModulesIntegration.lean"
generated.parent.mkdir(exist_ok=True)
generated.write_text("-- Generated non-conflicting library integration root.\n" +
                     "".join(f"import {name}\n" for name in modules if name.startswith("MCore.") and
                             name != "MCore.BackwardAudit.HypotheticalClosureOracle"))
print(f"Compiling {len(modules)} Lean modules; integration excludes known conflicting oracle module", flush=True)
# Build every module before importing them together.
for name in modules:
    result = subprocess.run(["lake", "build", name], cwd=root)
    if result.returncode:
        print(f"BUILD_RED {name}", flush=True)
        sys.exit(result.returncode)
result = subprocess.run(["lake", "env", "lean", str(generated)], cwd=root)
print("INTEGRATION_GREEN" if result.returncode == 0 else "INTEGRATION_RED", flush=True)
sys.exit(result.returncode)
