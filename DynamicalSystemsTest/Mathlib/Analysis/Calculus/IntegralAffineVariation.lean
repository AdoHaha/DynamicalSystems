import DynamicalSystems.Mathlib.Analysis.Calculus.IntegralAffineVariation
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic.NormNum

open Set MeasureTheory IntegralAffineVariation
open scoped NNReal

namespace IntegralAffineVariationTests

abbrev Time := Icc (0 : ℝ) 2

def middle : Time := ⟨1, by norm_num⟩

/-- A measurable reference path with an isolated point spike; the atom sees this spike. -/
noncomputable def spike : Time → ℝ := ({middle} : Set Time).indicator (fun _ ↦ 1)

/-- Actual differentiation for the square integrand with a Dirac measure and a measurable
spiked reference. The measure is singular and the reference need not be continuous. -/
theorem derivative_square_spike_dirac :
    HasDerivAt (fun θ : ℝ ↦ ∫ s, (spike s + θ) ^ 2 ∂Measure.dirac middle) 2 0 := by
  let D : Time → ℝ → ℝ →L[ℝ] ℝ := fun _ x ↦ (2 * x) • ContinuousLinearMap.id ℝ ℝ
  have hD : Continuous (fun p : Time × ℝ ↦ D p.1 p.2) :=
    (continuous_const.mul continuous_snd).smul continuous_const
  have hderiv (s : Time) (x : ℝ) : HasFDerivAt (fun x : ℝ ↦ x ^ 2) (D s x) x := by
    convert (hasDerivAt_pow 2 x).hasFDerivAt using 1
    ext
    simp [D]
  have hspike : Measurable spike := measurable_const.indicator (measurableSet_singleton middle)
  have hbound : ∀ s, ‖spike s‖ ≤ (1 : ℝ≥0) := by
    intro s
    by_cases hs : s = middle <;> simp [spike, Set.indicator, hs]
  have h := hasDerivAt_integral_affine_of_bounded
    (μ := Measure.dirac middle) (fun (_ : Time) (x : ℝ) ↦ x ^ 2) D
    (continuous_snd.pow 2) hD hderiv spike (fun _ ↦ 1)
    hspike measurable_const 1 hbound (fun _ ↦ by norm_num)
  simpa [D, spike, Set.indicator, smul_eq_mul] using h.2

#print axioms IntegralAffineVariation.integrable_continuous_of_bounded
#print axioms IntegralAffineVariation.hasDerivAt_integral_affine
#print axioms IntegralAffineVariation.hasDerivAt_integral_affine_of_bounded
#print axioms derivative_square_spike_dirac

end IntegralAffineVariationTests
