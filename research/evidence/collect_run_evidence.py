#!/usr/bin/env python3
import json
import os
from pathlib import Path
from datetime import datetime, timezone

sha = os.environ.get("GITHUB_SHA")
run_id = os.environ.get("GITHUB_RUN_ID")
workflow = os.environ.get("GITHUB_WORKFLOW")
ref = os.environ.get("GITHUB_REF_NAME")
repo = os.environ.get("GITHUB_REPOSITORY")

items = [
    {
        "evidence_id": f"run-{run_id}-prime2-conservative",
        "lane": "PRIME2",
        "status": "OBSERVED",
        "claim": "Prime2 conservative layer compiled in this run if workflow succeeds.",
        "exact_scope": "Prime2 metadata is separated from standard SAT/machine semantics.",
        "source_repository": repo,
        "source_sha": sha,
        "source_path": "lean/MCore/Research/Prime2ConservativeTransfer.lean",
        "workflow_run": int(run_id) if run_id else None,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "evidence_kind": "CI_RUN",
        "assumptions": [],
        "observed_result": "pending-workflow-conclusion",
        "counterexample_if_any": None,
        "transfer_target": "G21Pointwise",
        "transfer_status": "INTERFACE_ONLY",
        "proof_credit": 0,
        "notes": "Coverage remains required."
    },
    {
        "evidence_id": f"run-{run_id}-horizon-prime",
        "lane": "HORIZON_PRIME",
        "status": "OBSERVED",
        "claim": "Prime/Horizon calculator and boundary facts were included in this run.",
        "exact_scope": "Finite prime-shell and gap patterns only.",
        "source_repository": repo,
        "source_sha": sha,
        "source_path": "lean/MCore/Research/PatternCalculator.lean",
        "workflow_run": int(run_id) if run_id else None,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "evidence_kind": "COMPUTATIONAL_PROBE",
        "assumptions": [],
        "observed_result": "q=3 kernel gap numerator 4; q=3 odd-pure gap numerator 10",
        "counterexample_if_any": None,
        "transfer_target": "ConservativePrime2Interpretation / Coverage",
        "transfer_status": "RESEARCH_ONLY",
        "proof_credit": 0,
        "notes": "Finite patterns do not imply an asymptotic theorem."
    },
    {
        "evidence_id": f"run-{run_id}-certificate-provenance",
        "lane": "CERTIFICATE_PROVENANCE",
        "status": "OBSERVED",
        "claim": "Run provenance snapshot.",
        "exact_scope": "Repository/run metadata only.",
        "source_repository": repo,
        "source_sha": sha,
        "source_path": None,
        "workflow_run": int(run_id) if run_id else None,
        "created_at": datetime.now(timezone.utc).isoformat(),
        "evidence_kind": "CERTIFICATE_METADATA",
        "assumptions": [],
        "observed_result": json.dumps({"workflow": workflow, "ref": ref}),
        "counterexample_if_any": None,
        "transfer_target": None,
        "transfer_status": "NONE",
        "proof_credit": 0,
        "notes": "Final conclusion is determined by GitHub Actions, not this record."
    }
]

out = {
    "schema": "final-proof-research-evidence.v1",
    "repository": repo,
    "sha": sha,
    "run_id": int(run_id) if run_id else None,
    "workflow": workflow,
    "ref": ref,
    "generated_at": datetime.now(timezone.utc).isoformat(),
    "items": items
}

Path("research/evidence/generated").mkdir(parents=True, exist_ok=True)
path = Path("research/evidence/generated/run-evidence.json")
path.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(path)
