#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build DynamicalSystems.Mathlib.Analysis.Convex.ContinuousInequalityMultipliers \
  DynamicalSystems.Mathlib.MeasureTheory.PositiveFunctionalMeasure
lake env lean DynamicalSystemsTest/StateConstraints.lean
