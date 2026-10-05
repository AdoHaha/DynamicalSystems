import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistence
import DynamicalSystems.Mathlib.Analysis.ODE.UniformlyLocallyLipschitzUniqueness
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Pointwise growth bounds do not prevent finite-time escape

This smooth scalar field is bounded in the state at each fixed time. Its
solution through `(0, 1)` is `1 / (1 - t)` for `t < 1`, so growth bounds must
have some uniformity or integrability in time in a completeness theorem.
-/

open Set Filter Topology

namespace PointwiseGrowthObstruction

noncomputable section

def field (t x : ℝ) : ℝ :=
  2 * (1 - t) ^ 2 * x ^ 4 / (1 + (1 - t) ^ 4 * x ^ 4)

def curve (t : ℝ) : ℝ := (1 - t)⁻¹

theorem denominator_pos (t x : ℝ) : 0 < 1 + (1 - t) ^ 4 * x ^ 4 := by
  positivity

theorem smooth : ContDiff ℝ 1 field.uncurry := by
  unfold field Function.uncurry
  apply ContDiff.div
  · fun_prop
  · fun_prop
  · intro z
    exact ne_of_gt (denominator_pos z.1 z.2)

theorem locally_lipschitz : UniformlyLocallyLipschitz field :=
  smooth.uniformlyLocallyLipschitz

theorem continuous : Continuous field := by
  apply continuous_pi
  intro x
  exact smooth.continuous.comp (continuous_id.prodMk continuous_const)

theorem nonneg (t x : ℝ) : 0 ≤ field t x := by
  unfold field
  positivity

/-- In fact every time slice is bounded, a stronger property than the old
pointwise-in-time linear-growth premise. -/
theorem bounded_at_each_time (t : ℝ) : ∃ C, ∀ x, ‖field t x‖ ≤ C := by
  by_cases ht : t = 1
  · subst t
    exact ⟨0, by intro x; simp [field]⟩
  · have hu : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
    refine ⟨2 / (1 - t) ^ 2, fun x ↦ ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (nonneg t x)]
    unfold field
    apply (div_le_div_iff₀ (denominator_pos t x) (sq_pos_of_ne_zero hu)).2
    nlinarith

theorem pointwise_linear_growth : ∀ t, ∃ a b, ∀ x, ‖field t x‖ ≤ a + b * ‖x‖ := by
  intro t
  obtain ⟨C, hC⟩ := bounded_at_each_time t
  exact ⟨C, 0, by simpa using hC⟩

theorem field_on_curve {t : ℝ} (ht : t ≠ 1) : field t (curve t) = (1 - t)⁻¹ ^ 2 := by
  have hu : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  unfold field curve
  field_simp [hu]
  ring

theorem curve_derivative {t : ℝ} (ht : t ≠ 1) :
    HasDerivAt curve (field t (curve t)) t := by
  have hu : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  rw [field_on_curve ht]
  unfold curve
  convert ((hasDerivAt_id t).const_sub 1).inv hu using 1
  · rfl
  · simp [div_eq_mul_inv]

theorem curve_isIntegralCurveOn : IsIntegralCurveOn curve field (Iio 1) := by
  intro t ht
  exact (curve_derivative (ne_of_lt ht)).hasDerivWithinAt

theorem curve_initial : curve 0 = 1 := by simp [curve]

/-- The supplied solution has no continuous extension across its escape time. -/
theorem no_continuous_extension (γ : ℝ → ℝ) (hγ : Continuous γ)
    (heq : EqOn γ curve (Iio 1)) : False := by
  have hclosed : IsClosed {t : ℝ | (1 - t) * γ t = 1} :=
    isClosed_eq (by fun_prop) continuous_const
  have hsubset : Iio (1 : ℝ) ⊆ {t : ℝ | (1 - t) * γ t = 1} := by
    intro t ht
    change (1 - t) * γ t = 1
    rw [heq ht]
    exact mul_inv_cancel₀ (sub_ne_zero.mpr (ne_of_gt ht))
  have hmem : (1 : ℝ) ∈ closure (Iio (1 : ℝ)) := by simp
  have hcontra := closure_minimal hsubset hclosed hmem
  norm_num at hcontra

/-- The original H5 statement is false even for a smooth field on the real line. -/
theorem not_complete : ¬ IsCompleteVectorField field := by
  intro hcomplete
  obtain ⟨γ, hγ0, hγ⟩ := hcomplete 0 1
  apply no_continuous_extension γ hγ.continuous
  intro t ht
  have hzero : (0 : ℝ) ∈ Ioo (min t 0 - 1) 1 :=
    ⟨by linarith [min_le_right t (0 : ℝ)], by norm_num⟩
  have ht' : t ∈ Ioo (min t 0 - 1) 1 :=
    ⟨by linarith [min_le_left t (0 : ℝ)], ht⟩
  exact IsIntegralCurveOn.eqOn_Ioo_of_uniformlyLocallyLipschitz locally_lipschitz hzero
    (hγ.isIntegralCurveOn _) (curve_isIntegralCurveOn.mono (fun _ h ↦ h.2))
    (by simpa only [curve_initial] using hγ0) ht'

end

end PointwiseGrowthObstruction
