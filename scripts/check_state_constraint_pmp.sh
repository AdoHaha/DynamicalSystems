#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
files=(
  DynamicalSystems/Mathlib/MeasureTheory/PositiveFunctionalMeasure.lean
  DynamicalSystems/OptimalControl/ContinuousTime/PathConstraintMultipliers.lean
  DynamicalSystemsTest/PathConstraintMultipliers.lean
)
if grep -nE '\b(sorry|admit|axiom|proof_wanted|native_decide)\b' "${files[@]}"; then
  echo 'Forbidden proof escape in state-constraint modules.' >&2
  exit 1
fi
lake build DynamicalSystems.OptimalControl.ContinuousTime.PathConstraintMultipliers
log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean DynamicalSystemsTest/PathConstraintMultipliers.lean | tee "$log"
if grep -E 'sorryAx|Lean.ofReduceBool' "$log"; then
  echo 'Unexpected axiom in state-constraint regression audit.' >&2
  exit 1
fi
