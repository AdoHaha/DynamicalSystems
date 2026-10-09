#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

modules=(
  Mathlib.Analysis.BoundedVariation.Add
  Mathlib.Analysis.ODE.AffineIntegralResponse
  Mathlib.Analysis.ODE.MeasureAdjointBalance
  Mathlib.Analysis.ODE.MeasureAdjointPairing
  OptimalControl.ContinuousTime.AffineControlPath
  OptimalControl.ContinuousTime.AffineStateMinimumPrinciple
  OptimalControl.ContinuousTime.StateConstrainedMinimumPrinciple
  OptimalControl.ContinuousTime.StateControlAdjointPairing
  OptimalControl.ContinuousTime.StateControlFirstVariation
  Mathlib.Analysis.Calculus.IntegralAffineVariation
  Mathlib.Analysis.Convex.AbnormalSeparation
  Mathlib.Analysis.Convex.ContinuousInequalityMultipliers
  Mathlib.Analysis.Convex.MeasureInequalityMultipliers
  Mathlib.Analysis.ODE.MeasureAdjoint
  Mathlib.MeasureTheory.MeasureTail
  Mathlib.MeasureTheory.PositiveFunctionalMeasure
  Mathlib.MeasureTheory.VectorMeasureTail
  OptimalControl.ContinuousTime.EndpointMultipliers
  OptimalControl.ContinuousTime.EndpointTransversalityConditions
  OptimalControl.ContinuousTime.IntegralControlPath
  OptimalControl.ContinuousTime.IntegratorStateMinimumPrinciple
  OptimalControl.ContinuousTime.LinearGrowthControlExistence
  OptimalControl.ContinuousTime.NonconvexControlExistence
  OptimalControl.ContinuousTime.CesariCompactnessArgument
  OptimalControl.ContinuousTime.CesariExistence
  OptimalControl.ContinuousTime.CesariExistenceArgument
  OptimalControl.ContinuousTime.LinearTerminalCost
  OptimalControl.ContinuousTime.LocalizedControlExistence
  OptimalControl.ContinuousTime.MaximumPrincipleSufficiency
  OptimalControl.ContinuousTime.StateConstrainedSufficiency
  OptimalControl.ContinuousTime.UnconstrainedMaximumPrinciple
  OptimalControl.ContinuousTime.MeasurableHamiltonian
  OptimalControl.ContinuousTime.EpsilonOptimality
  OptimalControl.ContinuousTime.ControlAveragedRegularity
  OptimalControl.ContinuousTime.PenaltyBoundaryPositivity
  OptimalControl.ContinuousTime.VelocityEpsilonOptimality
  OptimalControl.ContinuousTime.VelocityPenaltyMinimizer
  OptimalControl.ContinuousTime.VelocityPointwiseBoundaryPositivity
  OptimalControl.ContinuousTime.VelocityPointwisePenaltyMinimizer
  OptimalControl.ContinuousTime.VelocityTrajectories
  OptimalControl.ContinuousTime.StateConstraintMultipliers
  OptimalControl.ContinuousTime.StateMultiplierCurve
  Mathlib.Analysis.BoundedVariation.HellySelection
  Mathlib.Analysis.Calculus.ACIntegrationByParts
  Mathlib.Analysis.Calculus.ACEulerLagrange
  Mathlib.MeasureTheory.MeasurableArgmin
  Mathlib.MeasureTheory.MeasurableEpigraphLift
  Mathlib.MeasureTheory.MeasurableSigmaCompactLift
  Mathlib.MeasureTheory.RelaxedHamiltonianMinimum
  Mathlib.MeasureTheory.EquiIntegrableTrajectories
  Mathlib.MeasureTheory.WeakL1Compactness
  Mathlib.MeasureTheory.WeakL2Compactness
  OptimalControl.ContinuousTime.StatePenalisedVelocityFunctional
  OptimalControl.ContinuousTime.StateMultiplierCostate
  OptimalControl.ContinuousTime.StateMultiplierLimit
  OptimalControl.ContinuousTime.StateMultiplierMassBound
  OptimalControl.ContinuousTime.VelocityEndpointTransversality
  OptimalControl.ContinuousTime.VelocityPointwiseEndpointConditions
  OptimalControl.ContinuousTime.VelocityPointwiseMinimizerEndpointConditions
  OptimalControl.ContinuousTime.MinimumTimeMaximumPrinciple
  OptimalControl.ContinuousTime.MinimumTimeTransversality
  OptimalControl.ContinuousTime.StateConstraintComplementarity
  Mathlib.Topology.ClusterPointLimit
)
files=()
targets=()
for module in "${modules[@]}"; do
  files+=("DynamicalSystems/${module//./\/}.lean")
  targets+=("DynamicalSystems.$module")
done
tests=(AffineIntegralResponse AffineStateNecessity MeasureAdjointBalance
  StateControlFirstVariation StateConstraints StateConstraintNecessity MeasureAdjoint EndpointMultipliers
  LinearGrowthExistence NonconvexExistence UnconstrainedMaximumPrinciple MinimumTimeMaximumPrinciple
  Mathlib/Analysis/Calculus/IntegralAffineVariation StateConstraintAtoms HardOptimalControl
  R4CCompactness)
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
hard_modules=(
  Mathlib/MeasureTheory/MeasurableEpigraphLift
  Mathlib/MeasureTheory/WeakL1Compactness
  Mathlib/MeasureTheory/EquiIntegrableTrajectories
  OptimalControl/ContinuousTime/CesariCompactnessArgument
  Mathlib/MeasureTheory/MeasurableSigmaCompactLift
  OptimalControl/ContinuousTime/CesariExistenceArgument
  OptimalControl/ContinuousTime/MinimumTimeTransversality
  OptimalControl/ContinuousTime/StateConstraintComplementarity
)
for module in "${hard_modules[@]}"; do
  file="DynamicalSystems/$module.lean"
  if rg -n '@\[\s*nolint|set_option.*linter' "$file"; then
    echo 'Forbidden linter suppression in hard extension files.' >&2
    exit 1
  fi
  lake env lean "$file" 2>&1 | tee -a "$log"
done
if rg 'warning:' "$log"; then
  echo 'Warning in hard extension files.' >&2
  exit 1
fi
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
