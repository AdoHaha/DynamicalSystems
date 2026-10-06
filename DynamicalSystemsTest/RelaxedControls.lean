import DynamicalSystems.OptimalControl.ContinuousTime.BarycentricRecovery
import DynamicalSystems.OptimalControl.ContinuousTime.OccupationIntegral

open MeasureTheory OptimalControl

local instance : Nonempty (Set.Icc (-1 : ℝ) 1) := ⟨⟨0, by norm_num⟩⟩

-- Compactness is derived for the fixed-marginal space; it is not a hypothesis.
example (ν : ProbabilityMeasure (Set.Icc (0 : ℝ) 1)) :
    CompactSpace (RelaxedControl (Set.Icc (0 : ℝ) 1) (Set.Icc (-1 : ℝ) 1) ν) :=
  inferInstance

example (ν : ProbabilityMeasure (Set.Icc (0 : ℝ) 1))
    (ρ : RelaxedControl (Set.Icc (0 : ℝ) 1) (Set.Icc (-1 : ℝ) 1) ν) (t : Set.Icc (0 : ℝ) 1) :
    ρ.barycenter t ∈ Set.Icc (-1 : ℝ) 1 :=
  ρ.barycenter_mem (convex_Icc _ _) t

example (ν : ProbabilityMeasure (Set.Icc (0 : ℝ) 1))
    (ρ : RelaxedControl (Set.Icc (0 : ℝ) 1) (Set.Icc (-1 : ℝ) 1) ν) :
    Measurable (ρ.recoveredControl (convex_Icc _ _)) :=
  ρ.measurable_recoveredControl _

#print axioms OptimalControl.RelaxedControl.isClosed_fixedMarginal
#print axioms OptimalControl.RelaxedControl.disintegrate
#print axioms OptimalControl.RelaxedControl.continuous_setIntegral_param
#print axioms OptimalControl.RelaxedControl.measurable_recoveredControl
#print axioms OptimalControl.RelaxedControl.setIntegral_affine_eq_recovered
#print axioms OptimalControl.RelaxedControl.integral_convex_cost_recovered_le
