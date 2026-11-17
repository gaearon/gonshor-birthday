#!/usr/bin/env bash
set -euo pipefail
repo_root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd -- "$repo_root"
scripts/check-palomar-challenge.sh
lake build --iofail
lake exe palomar-compatibility
lake exe axioms
