#!/usr/bin/env bash
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd -- "$repo_root"
scripts/verify.sh
# Lean 4.36 bundles the matching comparator, exporter, and independent checkers.
# Sandbox opt-out is never automatic; an expert local caller must pass it explicitly.
# lake env exposes this toolchain's bundled kernel executables on PATH.
exec lake env lake comparator --paranoid "$@"
