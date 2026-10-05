#!/usr/bin/env bash
set -euo pipefail

echo "== system =="
uname -a

echo "== lean =="
command -v lean
lean --version

echo "== lake =="
command -v lake
lake --version

echo "== git =="
git --version

echo "== repo =="
git rev-parse --show-toplevel
git rev-parse HEAD

echo "== toolchain =="
cat lean-toolchain

echo "P02_RUNNER_HEALTH_GREEN"
