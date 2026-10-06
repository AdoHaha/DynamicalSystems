#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build DynamicalSystems.Mathlib.Analysis.Convex.MeasureInequalityMultipliers \
  DynamicalSystems.Mathlib.MeasureTheory.MeasureTail
log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean DynamicalSystemsTest/StateConstraints.lean | tee "$log"
if grep -E 'sorryAx|Lean.ofReduceBool' "$log"; then
  echo 'Unexpected proof escape in state-constraint declarations.' >&2
  exit 1
fi
