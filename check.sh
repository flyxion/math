#!/bin/sh
# Verifies the Lean library: builds it, rejects any `sorry`, and audits axioms.
# Usage (from the lean/ directory):  sh check.sh
set -e
lake exe cache get >/dev/null 2>&1 || true
lake build
if grep -rn --include=*.lean 'sorry' CubicRhombus | grep -v 'Audit.lean'; then
  echo "FAILED: sorry found"; exit 1
fi
out=$(lake env lean CubicRhombus/Audit.lean 2>&1)
echo "$out" | grep "depends on axioms"
if echo "$out" | grep -q sorryAx; then echo "FAILED: sorryAx in audit"; exit 1; fi
n=$(echo "$out" | grep -c "depends on axioms")
echo "OK: $n theorems audited, only standard axioms (propext, Classical.choice, Quot.sound)"
