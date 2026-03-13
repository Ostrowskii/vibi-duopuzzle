#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
mkdir -p generated
bend src/Runtime.bend --to-js --no-strict > generated/runtime.generated.js
