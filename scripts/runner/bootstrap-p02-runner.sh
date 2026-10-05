#!/usr/bin/env bash
set -euo pipefail

ROOT="${RUNNER_ROOT:-$HOME/actions-runner-p02}"
REPO_URL="${REPO_URL:-https://github.com/ShantiDraconis/m-core-p-vs-np}"
LABELS="${RUNNER_LABELS:-p02,lean419,mcore}"
RUNNER_NAME="${RUNNER_NAME:-p02-$(hostname)}"

if [ -z "${RUNNER_TOKEN:-}" ]; then
  echo "ERROR: set RUNNER_TOKEN to a fresh GitHub Actions registration token."
  exit 2
fi

mkdir -p "$ROOT"
cd "$ROOT"

ARCH="$(uname -m)"
case "$ARCH" in
  x86_64) PKG_ARCH="x64" ;;
  aarch64|arm64) PKG_ARCH="arm64" ;;
  *) echo "Unsupported arch: $ARCH"; exit 3 ;;
esac

RUNNER_VERSION="${RUNNER_VERSION:-2.329.0}"
PKG="actions-runner-linux-${PKG_ARCH}-${RUNNER_VERSION}.tar.gz"
URL="https://github.com/actions/runner/releases/download/v${RUNNER_VERSION}/${PKG}"

if [ ! -x ./run.sh ]; then
  curl -fL "$URL" -o "$PKG"
  tar xzf "$PKG"
fi

if ! command -v elan >/dev/null 2>&1; then
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y
fi
export PATH="$HOME/.elan/bin:$PATH"

elan toolchain install leanprover/lean4:v4.19.0
elan default leanprover/lean4:v4.19.0

lean --version
lake --version

if [ ! -f .runner ]; then
  ./config.sh --unattended     --url "$REPO_URL"     --token "$RUNNER_TOKEN"     --name "$RUNNER_NAME"     --labels "$LABELS"     --work "_work"
fi

echo "Runner configured: $RUNNER_NAME labels=$LABELS"
echo "Start interactively: cd $ROOT && ./run.sh"
echo "Install service: sudo ./svc.sh install && sudo ./svc.sh start"
