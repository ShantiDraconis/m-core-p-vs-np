#!/usr/bin/env python3
from __future__ import annotations
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]

def run(label: str, cmd: list[str]) -> None:
    print(f"[{label}] {' '.join(cmd)}")
    subprocess.run(cmd, cwd=ROOT, check=True)

def main() -> int:
    try:
        run("CERT-0", [
            sys.executable, "certificado-runner/01_lean_audit.py",
            "lean/MCore/Real"
        ])
        run("CERT-1", [
            "lake", "build",
            "MCore.Real.CanonicalSATFrameMachineV2",
            "MCore.Real.P01VerifiedRelation",
            "MCore.Real.P01ComponentFailProof",
            "MCore.Real.P01RecursiveFiniteControlFrontier",
        ])
        run("CERT-2", [
            "lake", "env", "lean",
            "certificado-runner/02_frame_machine_audit.lean"
        ])
    except (subprocess.CalledProcessError, FileNotFoundError) as exc:
        print(f"[CERT-RUNNER] RED_INFRA: {exc}")
        return 2

    final_cert = ROOT / "lean/MCore/Real/P01FinalCertificate.lean"
    if not final_cert.exists():
        print("[CERT-3] P01 FRONTIER = OPEN")
        print("  frame finite-control/fixed-alphabet source: audited")
        print("  recursive parser + full CanonicalSATMachineClosure: NOT CERTIFIED")
        print("  required future file: lean/MCore/Real/P01FinalCertificate.lean")
        print("[CERTIFICADO FINAL P01] RED/OPEN")
        return 1

    try:
        run("CERT-3", ["lake", "env", "lean", str(final_cert.relative_to(ROOT))])
    except subprocess.CalledProcessError as exc:
        print(f"[CERTIFICADO FINAL P01] RED: {exc}")
        return 1

    text = final_cert.read_text(encoding="utf-8")
    required = "p01_final_certificate"
    if required not in text:
        print(f"[CERTIFICADO FINAL P01] RED: missing theorem marker {required}")
        return 1

    print("[CERTIFICADO FINAL P01] GREEN_CANDIDATE")
    print("This certifies only the repository P01 target; it does not certify P02 or official P != NP.")
    return 0

if __name__ == "__main__":
    raise SystemExit(main())
