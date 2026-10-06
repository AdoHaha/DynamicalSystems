#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

# Explicit targets ensure development modules are checked even before they are
# added to the umbrella import. Reject source-level proof escapes as well.
files=(
  DynamicalSystems/Mathlib/Analysis/Analytic/FiniteZeros.lean
  DynamicalSystems/OptimalControl/ContinuousTime/LinearSwitching.lean
  DynamicalSystems/OptimalControl/ContinuousTime/FiniteSwitching.lean
  DynamicalSystemsTest/FiniteSwitching.lean
)
if grep -nE '\b(sorry|admit|axiom|proof_wanted|native_decide)\b' "${files[@]}"; then
  echo 'Forbidden proof escape in extension files.' >&2
  exit 1
fi
lake build DynamicalSystems.OptimalControl.ContinuousTime.FiniteSwitching
log=$(mktemp)
trap 'rm -f "$log"' EXIT
lake env lean DynamicalSystemsTest/FiniteSwitching.lean | tee "$log"
if grep -E 'sorryAx|Lean.ofReduceBool' "$log"; then
  echo 'Unexpected axiom in extension regression audit.' >&2
  exit 1
fi
