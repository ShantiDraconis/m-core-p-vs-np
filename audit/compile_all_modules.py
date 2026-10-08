#!/usr/bin/env python3
"""Compile all Lean modules individually and together using a generated import root."""
import pathlib, subprocess, sys
root = pathlib.Path(__file__).resolve().parents[1]
source = root / "lean"
modules = sorted(".".join(p.relative_to(source).with_suffix("").parts)
                 for p in source.rglob("*.lean"))
generated = root / "artifacts" / "AllModulesIntegration.lean"
generated.parent.mkdir(exist_ok=True)
generated.write_text("-- Generated integration root; no mathematical claims.\n" +
                     "".join(f"import {name}\n" for name in modules))
print(f"Integrating {len(modules)} Lean modules", flush=True)
# Build every module before importing them together.
for name in modules:
    result = subprocess.run(["lake", "build", name], cwd=root)
    if result.returncode:
        print(f"BUILD_RED {name}", flush=True)
        sys.exit(result.returncode)
result = subprocess.run(["lake", "env", "lean", str(generated)], cwd=root)
print("INTEGRATION_GREEN" if result.returncode == 0 else "INTEGRATION_RED", flush=True)
sys.exit(result.returncode)
