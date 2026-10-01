#!/usr/bin/env bash
set -euo pipefail

mkdir -p audit

TARGETS=(
  MCore.Real.P02OperatorKernel
  MCore.Real.P02FinalCompression
  MCore.Real.P02KleeneKernel
  MCore.Real.P02EffectiveAlignment
  MCore.Real.P02UniversalLowerBound
  MCore.Real.P02UniversalKernel
)

FILES=(
  lean/MCore/Real/P02OperatorKernel.lean
  lean/MCore/Real/P02FinalCompression.lean
  lean/MCore/Real/P02KleeneKernel.lean
  lean/MCore/Real/P02EffectiveAlignment.lean
  lean/MCore/Real/P02UniversalLowerBound.lean
  lean/MCore/Real/P02UniversalKernel.lean
  audit/P02TargetedAxiomAudit.lean
)

echo "[P02] source hygiene"
if grep -n -E '(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)' "${FILES[@]}"; then
  echo "ERROR: sorry/admit found in targeted P02 sources"
  exit 1
fi

if grep -n -E '^[[:space:]]*(@\[[^]]*\][[:space:]]*)?(axiom|constant|constants)[[:space:]]' "${FILES[@]}"; then
  echo "ERROR: explicit axiom/constant declaration found in targeted P02 sources"
  exit 1
fi

echo "[P02] targeted build"
lake build "${TARGETS[@]}" 2>&1 | tee audit/P02-targeted-build.log

echo "[P02] axiom audit"
lake env lean audit/P02TargetedAxiomAudit.lean 2>&1 | tee audit/P02-targeted-axioms.log

if grep -q 'sorryAx' audit/P02-targeted-axioms.log; then
  echo "ERROR: sorryAx detected"
  exit 1
fi

python3 - <<'PY'
from pathlib import Path
import re, sys

text = Path("audit/P02-targeted-axioms.log").read_text()
allowed = {"propext", "Classical.choice", "Quot.sound"}
bad = set()

for line in text.splitlines():
    m = re.search(r"depends on axioms:\s*\[(.*)\]", line)
    if not m:
        continue
    deps = {x.strip() for x in m.group(1).split(",") if x.strip()}
    bad |= deps - allowed

if bad:
    print("ERROR: unexpected axioms:", sorted(bad))
    sys.exit(1)
PY

echo "[P02] certificate"
python3 - <<'PY'
from pathlib import Path
import json, subprocess, datetime

sha = subprocess.check_output(["git","rev-parse","HEAD"], text=True).strip()
payload = {
  "schema": "atk-p02-targeted-certificate.v1",
  "status": "GREEN",
  "scope": "P02_TARGETED_STRUCTURAL_AND_KERNEL_VALIDATION",
  "head_sha": sha,
  "generated_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
  "validated_modules": [
    "MCore.Real.P02OperatorKernel",
    "MCore.Real.P02FinalCompression",
    "MCore.Real.P02KleeneKernel",
    "MCore.Real.P02EffectiveAlignment",
    "MCore.Real.P02UniversalLowerBound",
    "MCore.Real.P02UniversalKernel"
  ],
  "checks": {
    "targeted_build": "PASS",
    "sorry_admit_scan": "PASS",
    "explicit_axiom_constant_scan": "PASS",
    "axiom_audit": "PASS"
  },
  "allowed_kernel_axioms": [
    "propext",
    "Classical.choice",
    "Quot.sound"
  ],
  "does_not_certify": [
    "Nonempty MCore.Real.P02UniversalKernel.SemanticDiagonalFamily",
    "MCore.Real.P02UniversalKernel.PointwiseSemanticDiagonal",
    "MCore.Real.P02FinalCompression.FINAL_OPEN_MATH",
    "unconditional P != NP"
  ],
  "open_math": "construct the D3 semantic diagonal family / universal SAT lower-bound producer"
}
Path("audit/P02_TARGETED_CERTIFICATE.generated.json").write_text(
    json.dumps(payload, indent=2, sort_keys=True) + "\n"
)
PY

python3 -m json.tool audit/P02_TARGETED_CERTIFICATE.generated.json >/dev/null

echo "[P02] GREEN: targeted validation passed"
