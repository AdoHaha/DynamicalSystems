#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

modules=(
  Mathlib.Analysis.Calculus.IntegralAffineVariation
  Mathlib.Analysis.Convex.AbnormalSeparation
  Mathlib.Analysis.Convex.ContinuousInequalityMultipliers
  Mathlib.Analysis.Convex.MeasureInequalityMultipliers
  Mathlib.Analysis.ODE.MeasureAdjoint
  Mathlib.MeasureTheory.MeasureTail
  Mathlib.MeasureTheory.PositiveFunctionalMeasure
  Mathlib.MeasureTheory.VectorMeasureTail
  OptimalControl.ContinuousTime.EndpointMultipliers
  OptimalControl.ContinuousTime.IntegralControlPath
  OptimalControl.ContinuousTime.IntegratorStateMinimumPrinciple
  OptimalControl.ContinuousTime.LinearGrowthControlExistence
  OptimalControl.ContinuousTime.LinearTerminalCost
  OptimalControl.ContinuousTime.LocalizedControlExistence
  OptimalControl.ContinuousTime.MeasurableHamiltonian
  OptimalControl.ContinuousTime.StateConstraintMultipliers
)
files=()
targets=()
for module in "${modules[@]}"; do
  files+=("DynamicalSystems/${module//./\/}.lean")
  targets+=("DynamicalSystems.$module")
done
tests=(StateConstraints StateConstraintNecessity MeasureAdjoint EndpointMultipliers
  LinearGrowthExistence
  Mathlib/Analysis/Calculus/IntegralAffineVariation StateConstraintAtoms)
for test in "${tests[@]}"; do
  files+=("DynamicalSystemsTest/$test.lean")
done
if rg -n '\b(sorry|admit|axiom|proof_wanted|native_decide)\b' "${files[@]}"; then
  echo 'Forbidden proof escape in remaining extension files.' >&2
  exit 1
fi
lake build "${targets[@]}" DynamicalSystems
log=$(mktemp)
trap 'rm -f "$log"' EXIT
for test in "${tests[@]}"; do
  lake env lean "DynamicalSystemsTest/$test.lean" | tee -a "$log"
done
if rg 'sorryAx|Lean.ofReduceBool' "$log"; then
  echo 'Unexpected proof escape in axiom audit.' >&2
  exit 1
fi
python3 - "$log" <<'AUDIT'
import re
import sys
allowed = {"propext", "Classical.choice", "Quot.sound"}
content = open(sys.argv[1]).read()
records = re.findall(r"depends on axioms:\s*\[([^]]*)\]", content)
if not records:
    raise SystemExit("Missing axiom audit output")
for deps in records:
    names = {name.strip() for name in deps.split(",") if name.strip()}
    unexpected = names - allowed
    if unexpected:
        raise SystemExit(f"Unexpected axioms: {unexpected}")
AUDIT
