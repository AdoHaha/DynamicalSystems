#!/usr/bin/env bash
# Check the library, foundational regression examples, and transitive axiom audit.
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.."

python3 scripts/check_foundation_placeholders.py
lake build DynamicalSystems

foundation_options=(
  -DautoImplicit=false
  -DrelaxedAutoImplicit=false
  -DmaxSynthPendingDepth=3
  -Dlinter.flexible=true
  -Dlinter.mathlibStandardSet=true
  -Dwarn.sorry=true
)

# Tests are deliberately outside the production lean_lib. Compile their imports
# before the aggregate audit, using the same options as the library.
foundation_modules=(
  Basic/ComparisonFunctions
  InputOutput/ClosedLoopCausality
  InputOutput/ClosedLoopCausalityCounterexample
  Mathlib/Dynamics/FlowCongruence
  Mathlib/Analysis/ODE/CompleteFlow
  Mathlib/Analysis/ODE/Duhamel
  Mathlib/Analysis/ODE/GlobalExistenceGrowth
  Mathlib/Analysis/ODE/PointwiseGrowthObstruction
  Foundations/Axioms
)

for foundation_module in "${foundation_modules[@]}"; do
  foundation_source="DynamicalSystemsTest/${foundation_module}.lean"
  foundation_artifact=".lake/build/lib/lean/DynamicalSystemsTest/${foundation_module}"
  mkdir -p -- "$(dirname -- "$foundation_artifact")"
  lake env lean "${foundation_options[@]}" --root=. \
    -o "${foundation_artifact}.olean" -i "${foundation_artifact}.ilean" \
    "$foundation_source"
done
