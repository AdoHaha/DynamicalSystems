import Mathlib

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let exactNames := ["eq_pos_convex_span_of_mem_convexHull", "Finset.convexHull_eq",
    "mem_convexHull_of_exists_fintype", "Finset.centerMass_eq_of_sum_1",
    "Finset.sum_subtype", "Fintype.sum_extend_by_zero", "Convex.sum_mem",
    "MeasureTheory.exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring"]
  for (name, info) in env.constants.toList do
    let s := name.toString
    let has (p : String) := (s.splitOn p).length > 1
    if !s.startsWith "_private" &&
        ((has "variation" && has "Density") ||
        (has "card_le" && has "finrank") ||
        (has "integral" && has "Variation") ||
        (has "convexHull" && has "finrank") || exactNames.contains s) then
      logInfo m!"{name}: {info.type}"
