#!/usr/bin/env bash
# Production modules import the exact mathlib files they use.  A bare
# `import Mathlib` hides the dependency surface and makes the layering claim
# in DESIGN.md unverifiable.
set -euo pipefail

if grep -rnE --include='*.lean' '^\s*(public\s+)?import\s+Mathlib\s*$' . \
     --exclude-dir=.lake; then
  echo "::error::bare 'import Mathlib' is not allowed in production code"
  exit 1
fi
echo "import scan: no bare 'import Mathlib'"
