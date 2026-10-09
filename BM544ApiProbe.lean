import Mathlib

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let exactNames := ["MeasureTheory.HasFiniteIntegral", "MeasureTheory.Integrable",
    "MeasureTheory.measure_biUnion_finset", "MeasureTheory.Measure.withDensity_apply",
    "MeasureTheory.Measure.variation_withDensityᵥ", "Function.Continuous.rightLim_eq",
    "MeasureTheory.setIntegral_congr_set", "MeasureTheory.integral_Icc_eq_integral_Ioc"]
  for (name, info) in env.constants.toList do
    let s := name.toString
    let has (p : String) := (s.splitOn p).length > 1
    if !s.startsWith "_private" &&
        ((has "sum_iSup" && (s.startsWith "ENNReal" || s.startsWith "Finset")) ||
        (has "Lim_eq" && has "Continuous") ||
        (s.startsWith "intervalIntegral" && has "continuous_primitive") ||
        (s.startsWith "eVariationOn" && has "sum") ||
        (s.startsWith "MeasureTheory.VectorMeasure" && has "boundedVariation") ||
        exactNames.contains s) then
      logInfo m!"{name}: {info.type}"

#print eVariationOn
#print BoundedVariationOn
