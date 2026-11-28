#!/bin/sh
set -eu
repo=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo"
lean --version | grep -F 'version 4.19.0,' >/dev/null
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
cp -R lean "$build/"
cat > "$build/lakefile.toml" <<'TOML'
name = "p01-replay"
[[lean_lib]]
name = "MCore"
srcDir = "lean"
TOML
cd "$build"
lake build MCore.Real.P01MachineConstructionAttempt
