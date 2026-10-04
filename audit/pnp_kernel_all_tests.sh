#!/usr/bin/env bash
set -euo pipefail

echo "=== PNP STRUCTURAL SUITE ==="
bash audit/pnp_kernel_structural_suite.sh

echo
echo "=== EXISTING DISCOVERY SUITE ==="
bash audit/pnp_all_gaps.sh

echo
echo "=== MATERIAL GATE ==="
set +e
bash audit/pnp_kernel_material_gate.sh
STATUS=$?
set -e

if [[ $STATUS -eq 2 ]]; then
  echo "EXPECTED OPEN: structural suite GREEN; material endpoint still OPEN."
  exit 2
fi
exit $STATUS
