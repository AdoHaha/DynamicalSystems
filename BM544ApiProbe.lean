import Mathlib

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let exactNames := ["MeasureTheory.HasFiniteIntegral", "MeasureTheory.Integrable",
    "MeasureTheory.measure_biUnion_finset", "MeasureTheory.Measure.withDensity_apply",
    "MeasureTheory.Measure.variation_withDensityᵥ", "MeasureTheory.Measure.withDensityᵥ_apply",
    "MeasureTheory.setIntegral_congr_set", "MeasureTheory.integral_Icc_eq_integral_Ioc",
    "Fin.sum_univ_eq_sum_range", "Finset.sum_range_sub", "Finset.sum_range_sub'",
    "ENNReal.finsetSum_iSup", "MeasureTheory.VectorMeasure.enorm_measure_le_variation"]
  for (name, info) in env.constants.toList do
    let s := name.toString
    let has (p : String) := (s.splitOn p).length > 1
    if !s.startsWith "_private" &&
        ((has "Lim_eq" && has "Continuous") || has "continuous_primitive" ||
        (has "ofReal" && has "norm" && !has "nnnorm") ||
        (s.startsWith "eVariationOn" && has "sum") ||
        (s.startsWith "MeasureTheory.VectorMeasure" && has "boundedVariation") ||
        exactNames.contains s) then
      logInfo m!"{name}: {info.type}"

#print eVariationOn
#print BoundedVariationOn
