#!/usr/bin/env bash
# Local hygiene check.  This is *not* a trust check: it only rules out the
# syntactic forms that would let an unproved statement enter the build.  The
# transitive trust check is the `#print axioms` audit in `Audit.lean`.
set -euo pipefail

roots=(AffineCorrection AffineCorrection.lean Erdos289 Erdos289.lean
       Erdos289Test Erdos289Test.lean Audit.lean
       IndependentTransversals IndependentTransversals.lean
       LeanPool LeanPool.lean)

pattern='\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern)\b'

if grep -rnE --include='*.lean' "$pattern" "${roots[@]}"; then
  echo "::error::forbidden declaration form found (see matches above)"
  exit 1
fi
echo "source scan: no sorry, admit, axiom, native_decide or unsafe"
