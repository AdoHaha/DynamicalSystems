#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

modules=(
  OptimalControl.ContinuousTime.CesariRelaxedMinimizer
  OptimalControl.ContinuousTime.IntegralCostShift
  OptimalControl.ContinuousTime.FiniteRelaxedRelativeEpigraph
  OptimalControl.ContinuousTime.FiniteRelaxedConvexHull
  OptimalControl.ContinuousTime.FiniteRelaxedAdmissible
  Mathlib.MeasureTheory.MeasurableRelativeEpigraphLift
  Mathlib.MeasureTheory.MeasureContinuityFromSemiring
  Mathlib.MeasureTheory.IntegralTrajectoryExtension
  Mathlib.MeasureTheory.ClassicalEquiAbsoluteContinuityUniformIntegrable
  Mathlib.MeasureTheory.ClassicalEquiAbsoluteContinuityVariation
  Mathlib.MeasureTheory.ClassicalEquiAbsoluteContinuity
  Mathlib.Analysis.Convex.FiniteCaratheodory
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
  Mathlib.MeasureTheory.MovingIntervalCompactness
  Mathlib.MeasureTheory.MovingIntervalStateConstraints
  Mathlib.MeasureTheory.PositiveFunctionalMeasure
  Mathlib.MeasureTheory.VectorMeasureTail
  OptimalControl.ContinuousTime.EndpointMultipliers
  OptimalControl.ContinuousTime.EndpointTransversalityConditions
  OptimalControl.ContinuousTime.IntegralControlPath
  OptimalControl.ContinuousTime.IntegratorStateMinimumPrinciple
  OptimalControl.ContinuousTime.LinearGrowthControlExistence
  OptimalControl.ContinuousTime.NonconvexControlExistence
  OptimalControl.ContinuousTime.CesariCompactnessArgument
  OptimalControl.ContinuousTime.CesariCostShift
  OptimalControl.ContinuousTime.FiniteRelaxedEpigraph
  OptimalControl.ContinuousTime.FiniteRelaxedExistence
  OptimalControl.ContinuousTime.FiniteRelaxedSourceSequence
  OptimalControl.ContinuousTime.CesariExistence
  OptimalControl.ContinuousTime.CesariExistenceArgument
  OptimalControl.ContinuousTime.CesariMovingInterval
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
  R4CCompactness R4CMovingInterval R4CFiniteRelaxed R4CStateConstraints R4CMinimizer)
for test in "${tests[@]}"; do
  files+=("DynamicalSystemsTest/$test.lean")
done
# Scan Lean code, excluding nested block comments and line comments. In particular,
# prose such as "constraints admit a realization" is not the `admit` tactic.
python3 - "${files[@]}" <<'PROOF_SCAN'
import re
import sys
for path in sys.argv[1:]:
    source = open(path).read()
    code = []
    i, depth, quoted = 0, 0, False
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                code.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif quoted:
            code.append(source[i])
            if source[i] == "\\" and i + 1 < len(source):
                i += 1
                code.append(source[i])
            elif source[i] == '"':
                quoted = False
            i += 1
        elif source.startswith("/-", i):
            depth = 1
            code.append(" ")
            i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end < 0 else end
        else:
            code.append(source[i])
            quoted = source[i] == '"'
            i += 1
    match = re.search(r"\b(sorry|admit|axiom|proof_wanted|native_decide)\b", "".join(code))
    if match:
        raise SystemExit(f"Forbidden proof escape in {path}: {match.group()}")
PROOF_SCAN
lake build "${targets[@]}" DynamicalSystems
log=$(mktemp)
trap 'rm -f "$log"' EXIT
hard_modules=(
  OptimalControl/ContinuousTime/CesariRelaxedMinimizer
  OptimalControl/ContinuousTime/IntegralCostShift
  OptimalControl/ContinuousTime/FiniteRelaxedRelativeEpigraph
  OptimalControl/ContinuousTime/FiniteRelaxedConvexHull
  OptimalControl/ContinuousTime/FiniteRelaxedAdmissible
  Mathlib/MeasureTheory/MeasurableRelativeEpigraphLift
  Mathlib/MeasureTheory/MeasureContinuityFromSemiring
  Mathlib/MeasureTheory/IntegralTrajectoryExtension
  Mathlib/MeasureTheory/ClassicalEquiAbsoluteContinuityUniformIntegrable
  Mathlib/MeasureTheory/ClassicalEquiAbsoluteContinuityVariation
  Mathlib/MeasureTheory/ClassicalEquiAbsoluteContinuity
  Mathlib/Analysis/Convex/FiniteCaratheodory
  Mathlib/MeasureTheory/MovingIntervalStateConstraints
  OptimalControl/ContinuousTime/FiniteRelaxedSourceSequence
  OptimalControl/ContinuousTime/CesariCostShift
  OptimalControl/ContinuousTime/FiniteRelaxedEpigraph
  OptimalControl/ContinuousTime/FiniteRelaxedExistence
  Mathlib/MeasureTheory/MovingIntervalCompactness
  OptimalControl/ContinuousTime/CesariMovingInterval
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
