import Mathlib

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, info) in env.constants.toList do
    let s := name.toString
    let has (p : String) := (s.splitOn p).length > 1
    if (has "variation" && has "Density") ||
        (has "card_le" && has "finrank") ||
        (has "integral" && has "Variation") ||
        (has "integral" && has "variation") ||
        (has "norm" && has "Semivariation") ||
        (has "convexHull" && has "finrank") then
      logInfo m!"{name}: {info.type}"

#check eq_pos_convex_span_of_mem_convexHull
#check Finset.mem_convexHull
#check Finset.centerMass_eq_of_sum_1
#check Fintype.sum_extend_by_zero
#check Finset.sum_dite
#check Finset.sum_subtype
#check IsSetSemiring.mem_supClosure_iff
#check MeasureTheory.exists_measure_symmDiff_lt_of_generateFrom_isSetSemiring
