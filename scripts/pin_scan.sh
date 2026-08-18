#!/usr/bin/env bash
# `lean-toolchain` and the mathlib entry of `lake-manifest.json` must name the
# same release.  A mismatch still builds, but it silently breaks the claim that
# the development is reproducible against one published mathlib version.
set -euo pipefail

toolchain=$(tr -d '[:space:]' < lean-toolchain)
expected="leanprover/lean4:$(python3 - <<'PY'
import json
m = json.load(open('lake-manifest.json'))
pkg = next(p for p in m['packages'] if p['name'] == 'mathlib')
print(pkg['inputRev'])
PY
)"

if [ "$toolchain" != "$expected" ]; then
  echo "::error::lean-toolchain is '$toolchain' but mathlib is pinned to '$expected'"
  exit 1
fi
echo "pin scan: $toolchain matches the pinned mathlib revision"
