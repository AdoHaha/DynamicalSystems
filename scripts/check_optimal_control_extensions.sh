#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

files=(
  DynamicalSystems/Mathlib/Analysis/Analytic/FiniteZeros.lean
  DynamicalSystems/Mathlib/Topology/LipschitzPaths.lean
  DynamicalSystems/OptimalControl/ContinuousTime/LinearSwitching.lean
  DynamicalSystems/OptimalControl/ContinuousTime/FiniteSwitching.lean
  DynamicalSystems/OptimalControl/ContinuousTime/RelaxedControls.lean
  DynamicalSystems/OptimalControl/ContinuousTime/BarycentricRecovery.lean
  DynamicalSystems/OptimalControl/ContinuousTime/OccupationIntegral.lean
  DynamicalSystems/OptimalControl/ContinuousTime/ControlHorizon.lean
  DynamicalSystems/OptimalControl/ContinuousTime/RelaxedTrajectories.lean
  DynamicalSystems/OptimalControl/ContinuousTime/Existence.lean
  DynamicalSystems/OptimalControl/ContinuousTime/OrdinaryControlExistence.lean
  DynamicalSystemsTest/FiniteSwitching.lean
  DynamicalSystemsTest/RelaxedControls.lean
  DynamicalSystemsTest/ControlExistence.lean
)
if grep -nE '\b(sorry|admit|axiom|proof_wanted|native_decide)\b' "${files[@]}"; then
  echo 'Forbidden proof escape in extension files.' >&2
  exit 1
fi
lake build DynamicalSystems.OptimalControl.ContinuousTime.FiniteSwitching \
  DynamicalSystems.OptimalControl.ContinuousTime.OrdinaryControlExistence
log=$(mktemp)
trap 'rm -f "$log"' EXIT
for test in FiniteSwitching RelaxedControls ControlExistence; do
  lake env lean "DynamicalSystemsTest/$test.lean" | tee -a "$log"
done
if grep -E 'sorryAx|Lean.ofReduceBool' "$log"; then
  echo 'Unexpected axiom in extension regression audit.' >&2
  exit 1
fi
bash scripts/check_state_constraint_pmp.sh
