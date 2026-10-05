/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
import DynamicalSystems.OptimalControl.ContinuousTime.K3IsoperimetricEulerLagrange
import DynamicalSystems.OptimalControl.ContinuousTime.TimeReparametrizationFamily

/-!
# Weak time variations for a nonautonomous Lagrangian

Affine changes of duration also move the time argument of a nonautonomous
Lagrangian. The actual density derivative contains the corresponding time
partial, derived by the chain rule. Compactness differentiates its integral
using only continuous state and velocity, without differentiating velocity.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace NonautonomousTimeReparametrization

open TimeReparametrization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual time partial is the time component of the joint derivative. -/
theorem time_deriv_eq (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (t : ℝ) (x v : E) :
    deriv (fun s ↦ L s x v) t =
      fderiv ℝ (uncurryLagrangian L) (t, x, v) (1, 0, 0) := by
  have hi : HasDerivAt (fun s : ℝ ↦ (s, x, v)) (1, 0, 0) t :=
    (hasDerivAt_id t).prodMk ((hasDerivAt_const t x).prodMk (hasDerivAt_const t v))
  exact ((hL.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t hi).deriv

/-- Restrict the actual joint derivative to the velocity coordinate. -/
theorem velocity_fderiv_eq (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (t : ℝ) (x v w : E) :
    fderiv ℝ (L t x) v w =
      fderiv ℝ (uncurryLagrangian L) (t, x, v) (0, 0, w) := by
  rw [velocity_fderiv_apply (L t) x v w (differentiableAt_lagrangian_slice L hL t x v)]
  change fderiv ℝ (fun q : E × E ↦ L t q.1 q.2) (x, v) (0, w) = _
  rw [fderiv_lagrangian_slice_eq L hL t x v]
  rfl

/-- Duration rescaling with an affine movement of the physical time argument. -/
noncomputable def movingDensity (L : ℝ → E → E → ℝ) (t α : ℝ) (x v : E)
    (r : ℝ) : ℝ :=
  r * L (t + (r - 1) * α) x (r⁻¹ • v)

/-- The chain-rule derivative at a nonzero scale. -/
noncomputable def movingDensityDerivative (L : ℝ → E → E → ℝ) (t α : ℝ)
    (x v : E) (r : ℝ) : ℝ :=
  L (t + (r - 1) * α) x (r⁻¹ • v) +
    r * fderiv ℝ (uncurryLagrangian L) (t + (r - 1) * α, x, r⁻¹ • v)
      (α, 0, (-(r⁻¹) ^ 2) • v)

/-- Ordinary product and chain rules give the actual moving-density derivative. -/
theorem hasDerivAt_movingDensity (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (t α : ℝ) (x v : E)
    {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (movingDensity L t α x v) (movingDensityDerivative L t α x v r) r := by
  have ht : HasDerivAt (fun s : ℝ ↦ t + (s - 1) * α) α r := by
    simpa using (((hasDerivAt_id r).sub_const 1).mul_const α).const_add t
  have hi : HasDerivAt (fun s : ℝ ↦ (t + (s - 1) * α, x, s⁻¹ • v))
      (α, 0, (-(r⁻¹) ^ 2) • v) r := by
    simpa only [inv_pow] using
      ht.prodMk ((hasDerivAt_const r x).prodMk ((hasDerivAt_inv hr).smul_const v))
  have h := (hasDerivAt_id r).mul
    ((hL.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt r hi)
  convert h using 1
  · rfl
  · simp only [movingDensityDerivative, one_mul, id_eq, Function.comp_apply,
      uncurryLagrangian]

/-- At the original scale the derivative is the time shift times `L_t`, minus energy. -/
theorem movingDensityDerivative_one (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (t α : ℝ) (x v : E) :
    movingDensityDerivative L t α x v 1 =
      α * deriv (fun s ↦ L s x v) t - (fderiv ℝ (L t x) v v - L t x v) := by
  have hd : (α, (0 : E), -v) =
      α • ((1 : ℝ), (0 : E), (0 : E)) - ((0 : ℝ), (0 : E), v) := by
    simp
  simp only [movingDensityDerivative, sub_self, zero_mul, add_zero, inv_one,
    one_smul, one_pow, neg_smul, one_mul]
  rw [hd, map_sub, map_smul, ← time_deriv_eq L hL t x v,
    ← velocity_fderiv_eq L hL t x v v]
  simp only [smul_eq_mul]
  ring

/-- The fixed-reference-interval integral of the moving density. -/
noncomputable def movingArcCost (L : ℝ → E → E → ℝ) (θ α : ℝ → ℝ)
    (x v : ℝ → E) (d r : ℝ) : ℝ :=
  ∫ t in 0..d, movingDensity L (θ t) (α t) (x t) (v t) r

/-- The derivative density is jointly continuous on a compact strip of positive scales. -/
theorem continuousOn_movingDensityDerivative (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) {θ α : ℝ → ℝ} {x v : ℝ → E}
    (hθ : Continuous θ) (hα : Continuous α) (hx : Continuous x) (hv : Continuous v)
    (d : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ ↦
      movingDensityDerivative L (θ q.2) (α q.2) (x q.2) (v q.2) q.1)
      (Icc (1 / 2 : ℝ) (3 / 2) ×ˢ Icc 0 d) := by
  let S := Icc (1 / 2 : ℝ) (3 / 2) ×ˢ Icc 0 d
  have hi : ContinuousOn (fun q : ℝ × ℝ ↦ q.1⁻¹) S :=
    continuous_fst.continuousOn.inv₀ (fun q hq ↦ ne_of_gt (by
      have : (1 / 2 : ℝ) ≤ q.1 := hq.1.1
      linarith))
  have hp : ContinuousOn (fun q : ℝ × ℝ ↦
      (θ q.2 + (q.1 - 1) * α q.2, x q.2, q.1⁻¹ • v q.2)) S :=
    ((hθ.comp continuous_snd).continuousOn.add
      ((continuous_fst.sub continuous_const).continuousOn.mul
        (hα.comp continuous_snd).continuousOn)).prodMk
      ((hx.comp continuous_snd).continuousOn.prodMk
        (hi.smul (hv.comp continuous_snd).continuousOn))
  have hw : ContinuousOn (fun q : ℝ × ℝ ↦
      (α q.2, (0 : E), (-(q.1⁻¹) ^ 2) • v q.2)) S :=
    (hα.comp continuous_snd).continuousOn.prodMk
      (continuous_const.continuousOn.prodMk
        ((hi.pow 2).neg.smul (hv.comp continuous_snd).continuousOn))
  exact (hL.continuous.comp_continuousOn hp).add
    (continuous_fst.continuousOn.mul
      (((hL.continuous_fderiv one_ne_zero).comp_continuousOn hp).clm_apply hw))

/-- Compactness supplies domination for the actual scale derivative of the integral. -/
theorem hasDerivAt_movingArcCost (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) {θ α : ℝ → ℝ} {x v : ℝ → E}
    (hθ : Continuous θ) (hα : Continuous α) (hx : Continuous x) (hv : Continuous v)
    {d : ℝ} (hd : 0 ≤ d) :
    HasDerivAt (movingArcCost L θ α x v d)
      (∫ t in 0..d, α t * deriv (fun s ↦ L s (x t) (v t)) (θ t) -
        (fderiv ℝ (L (θ t) (x t)) (v t) (v t) - L (θ t) (x t) (v t))) 1 := by
  let F : ℝ → ℝ → ℝ := fun r t ↦ movingDensity L (θ t) (α t) (x t) (v t) r
  let D : ℝ → ℝ → ℝ :=
    fun r t ↦ movingDensityDerivative L (θ t) (α t) (x t) (v t) r
  let μ : Measure ℝ := volume.restrict (Ioc 0 d)
  have hFc : ∀ r, Continuous (F r) := by
    intro r
    exact continuous_const.mul (hL.continuous.comp
      ((hθ.add (continuous_const.mul hα)).prodMk
        (hx.prodMk (continuous_const.smul hv))))
  have hDc : Continuous (D 1) := by
    have hp : Continuous (fun t ↦ (θ t, x t, v t)) := hθ.prodMk (hx.prodMk hv)
    have hw : Continuous (fun t ↦ (α t, (0 : E), -v t)) :=
      hα.prodMk (continuous_const.prodMk hv.neg)
    convert (hL.continuous.comp hp).add
      (((hL.continuous_fderiv one_ne_zero).comp hp).clm_apply hw) using 1
    ext t
    simp [D, movingDensityDerivative, uncurryLagrangian]
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (continuousOn_movingDensityDerivative L hL hθ hα hx hv d)
  have hbound : ∀ᵐ t ∂μ, ∀ r ∈ Ioo (1 / 2 : ℝ) (3 / 2), ‖D r t‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro r hr
    exact hB (r, t) ⟨⟨hr.1.le, hr.2.le⟩, ⟨ht.1.le, ht.2⟩⟩
  have hdiff : ∀ᵐ t ∂μ, ∀ r ∈ Ioo (1 / 2 : ℝ) (3 / 2),
      HasDerivAt (F · t) (D r t) r := by
    exact Filter.Eventually.of_forall fun t r hr ↦
      hasDerivAt_movingDensity L hL (θ t) (α t) (x t) (v t)
        (ne_of_gt (by linarith [hr.1]))
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (μ := μ) (bound := fun _ ↦ B)
    (show Ioo (1 / 2 : ℝ) (3 / 2) ∈ 𝓝 (1 : ℝ) from
      Ioo_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun r ↦ (hFc r).aestronglyMeasurable)
    ((hFc 1).integrableOn_Ioc) hDc.aestronglyMeasurable hbound
    ((continuous_const : Continuous (fun _ : ℝ ↦ B)).integrableOn_Ioc) hdiff
  have hraw : HasDerivAt (movingArcCost L θ α x v d) (∫ t in 0..d, D 1 t) 1 := by
    change HasDerivAt (fun r ↦ ∫ t in 0..d, F r t) (∫ t in 0..d, D 1 t) 1
    simpa only [μ, intervalIntegral.integral_of_le hd] using h.2
  have heq : (fun t ↦ D 1 t) = fun t ↦
      α t * deriv (fun s ↦ L s (x t) (v t)) (θ t) -
        (fderiv ℝ (L (θ t) (x t)) (v t) (v t) - L (θ t) (x t) (v t)) := by
    funext t
    exact movingDensityDerivative_one L hL (θ t) (α t) (x t) (v t)
  rw [heq] at hraw
  exact hraw

end NonautonomousTimeReparametrization
