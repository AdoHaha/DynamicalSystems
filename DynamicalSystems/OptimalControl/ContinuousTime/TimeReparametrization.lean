import DynamicalSystems.OptimalControl.ContinuousTime.CalculusOfVariations
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Actual cost derivatives under affine time rescaling

An arc with state `x(t)` and velocity `v(t)` is traversed in `r` times its original
length by the curve `t ↦ x(t/r)`. Its velocity is `r⁻¹ • v(t/r)`, and substitution
writes its actual Lagrangian integral as `∫ r * L (x t) (r⁻¹ • v t)` over the fixed
reference interval. This file derives the parameter derivative of this integral.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace TimeReparametrization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lagrangian density after an affine change of the time scale. -/
noncomputable def rescaledDensity (L : E → E → ℝ) (x v : E) (r : ℝ) : ℝ :=
  r * L x (r⁻¹ • v)

/-- Derivative expression for the rescaled density at a nonzero scale. -/
noncomputable def rescaledDensityDerivative (L : E → E → ℝ) (x v : E) (r : ℝ) : ℝ :=
  L x (r⁻¹ • v) - r⁻¹ * (fderiv ℝ L.uncurry (x, r⁻¹ • v)) (0, v)

/-- Differentiate the actual rescaled Lagrangian density by the product and chain rules. -/
theorem hasDerivAt_rescaledDensity (L : E → E → ℝ) (x v : E) {r : ℝ} (hr : r ≠ 0)
    (hL : DifferentiableAt ℝ L.uncurry (x, r⁻¹ • v)) :
    HasDerivAt (rescaledDensity L x v) (rescaledDensityDerivative L x v r) r := by
  have hi : HasDerivAt (fun s : ℝ ↦ (x, s⁻¹ • v))
      (0, -(r ^ 2)⁻¹ • v) r :=
    (hasDerivAt_const r x).prodMk ((hasDerivAt_inv hr).smul_const v)
  have hcomp := hL.hasFDerivAt.comp_hasDerivAt r hi
  have h := (hasDerivAt_id r).mul hcomp
  have hv : ((0 : E), -(r ^ 2)⁻¹ • v) = -(r ^ 2)⁻¹ • ((0 : E), v) := by simp
  convert h using 1
  · rfl
  · simp only [rescaledDensityDerivative, hv, map_smul, smul_eq_mul, id_eq, one_mul,
      Function.comp_apply, Function.uncurry_apply_pair]
    field_simp
    ring

/-- Restrict the joint derivative to the velocity direction. -/
theorem velocity_fderiv_apply (L : E → E → ℝ) (x v w : E)
    (hL : DifferentiableAt ℝ L.uncurry (x, v)) :
    fderiv ℝ (L x) v w = fderiv ℝ L.uncurry (x, v) (0, w) := by
  have hi : HasFDerivAt (fun z : E ↦ (x, z))
      (ContinuousLinearMap.inr ℝ E E) v := by
    convert (hasFDerivAt_const x v).prodMk (hasFDerivAt_id v) using 1 <;> rfl
  have h := hL.hasFDerivAt.comp v hi
  have heq : fderiv ℝ (L x) v = (fderiv ℝ L.uncurry (x, v)).comp
      (ContinuousLinearMap.inr ℝ E E) := by
    exact h.fderiv
  rw [heq]
  rfl

/-- At unit duration scale the density derivative is minus the project's actual energy. -/
theorem rescaledDensityDerivative_one (L : E → E → ℝ) (x v : ℝ → E) (t : ℝ)
    (hL : DifferentiableAt ℝ L.uncurry (x t, v t)) :
    rescaledDensityDerivative L (x t) (v t) 1 = -energyCurve L x v t := by
  simp only [rescaledDensityDerivative, inv_one, one_smul, one_mul, energyCurve]
  rw [velocity_fderiv_apply L (x t) (v t) (v t) hL]
  ring

/-- Rescaled density integrated over the original arc parameter interval. -/
noncomputable def rescaledArcCost (L : E → E → ℝ) (x v : ℝ → E) (d r : ℝ) : ℝ :=
  ∫ t in 0..d, rescaledDensity L (x t) (v t) r

/-- The time-rescaled reference arc has the expected actual derivative. -/
theorem hasDerivAt_rescaledArc {x v : ℝ → E} (hx : ∀ t, HasDerivAt x (v t) t)
    (r t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ x (s / r)) (r⁻¹ • v (t / r)) t := by
  simpa only [one_div, Function.comp_def, id_eq] using
    (hx (t / r)).scomp t ((hasDerivAt_id t).div_const r)

/-- Substitution identifies the fixed-interval formula with the actual rescaled-curve cost. -/
theorem rescaledArcCost_eq_actual (L : E → E → ℝ) {x v : ℝ → E}
    (hx : ∀ t, HasDerivAt x (v t) t) (d : ℝ) {r : ℝ} (hr : r ≠ 0) :
    rescaledArcCost L x v d r =
      ∫ t in 0..r * d, L (x (t / r)) (deriv (fun s : ℝ ↦ x (s / r)) t) := by
  have hd : ∀ t, deriv (fun s : ℝ ↦ x (s / r)) t = r⁻¹ • v (t / r) :=
    fun t ↦ (hasDerivAt_rescaledArc hx r t).deriv
  simp_rw [hd]
  have hsub := intervalIntegral.integral_comp_div
    (fun s : ℝ ↦ L (x s) (r⁻¹ • v s)) (a := 0) (b := r * d) hr
  calc
    rescaledArcCost L x v d r = r * ∫ t in 0..d, L (x t) (r⁻¹ • v t) :=
      intervalIntegral.integral_const_mul r _
    _ = ∫ t in 0..r * d, L (x (t / r)) (r⁻¹ • v (t / r)) := by
      simpa only [zero_div, mul_div_cancel_left₀ d hr, smul_eq_mul] using hsub.symm

/-- The derivative density is continuous on a compact strip bounded away from zero. -/
theorem continuousOn_rescaledDensityDerivative (L : E → E → ℝ)
    (hL : ContDiff ℝ 1 L.uncurry) {x v : ℝ → E} (hx : Continuous x) (hv : Continuous v)
    (d : ℝ) :
    ContinuousOn (fun q : ℝ × ℝ ↦ rescaledDensityDerivative L (x q.2) (v q.2) q.1)
      (Icc (1 / 2 : ℝ) (3 / 2) ×ˢ Icc 0 d) := by
  let S := Icc (1 / 2 : ℝ) (3 / 2) ×ˢ Icc 0 d
  have hi : ContinuousOn (fun q : ℝ × ℝ ↦ q.1⁻¹) S :=
    continuous_fst.continuousOn.inv₀ (fun q hq ↦ ne_of_gt (by
      have : (1 / 2 : ℝ) ≤ q.1 := hq.1.1
      linarith))
  have hp : ContinuousOn (fun q : ℝ × ℝ ↦ (x q.2, q.1⁻¹ • v q.2)) S :=
    (hx.comp continuous_snd).continuousOn.prodMk
      (hi.smul (hv.comp continuous_snd).continuousOn)
  have hd : ContinuousOn (fun q : ℝ × ℝ ↦
      (fderiv ℝ L.uncurry (x q.2, q.1⁻¹ • v q.2)) (0, v q.2)) S :=
    ((hL.continuous_fderiv one_ne_zero).comp_continuousOn hp).clm_apply
      (continuous_const.prodMk (hv.comp continuous_snd)).continuousOn
  exact (hL.continuous.comp_continuousOn hp).sub (hi.mul hd)

/-- The fixed-interval cost is differentiated from ordinary C1 Lagrangian data and
continuous reference state/velocity. Compactness supplies the dominating bound. -/
theorem hasDerivAt_rescaledArcCost (L : E → E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {x v : ℝ → E} (hx : Continuous x) (hv : Continuous v) {d : ℝ} (hd : 0 ≤ d) :
    HasDerivAt (rescaledArcCost L x v d)
      (∫ t in 0..d, rescaledDensityDerivative L (x t) (v t) 1) 1 := by
  let F : ℝ → ℝ → ℝ := fun r t ↦ rescaledDensity L (x t) (v t) r
  let D : ℝ → ℝ → ℝ := fun r t ↦ rescaledDensityDerivative L (x t) (v t) r
  let μ : Measure ℝ := volume.restrict (Ioc 0 d)
  have hFc : ∀ r, Continuous (F r) := by
    intro r
    exact continuous_const.mul (hL.continuous.comp (hx.prodMk (continuous_const.smul hv)))
  have hDc : Continuous (D 1) := by
    change Continuous (fun t ↦ L (x t) (1⁻¹ • v t) -
      1⁻¹ * (fderiv ℝ L.uncurry (x t, 1⁻¹ • v t)) (0, v t))
    simp only [inv_one, one_smul, one_mul]
    convert (hL.continuous.comp (hx.prodMk hv)).sub
      (((hL.continuous_fderiv one_ne_zero).comp (hx.prodMk hv)).clm_apply
        (continuous_const.prodMk hv)) using 1 <;> rfl
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (continuousOn_rescaledDensityDerivative L hL hx hv d)
  have hbound : ∀ᵐ t ∂μ, ∀ r ∈ Ioo (1 / 2 : ℝ) (3 / 2), ‖D r t‖ ≤ B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    intro r hr
    exact hB (r, t) ⟨⟨hr.1.le, hr.2.le⟩, ⟨ht.1.le, ht.2⟩⟩
  have hdiff : ∀ᵐ t ∂μ, ∀ r ∈ Ioo (1 / 2 : ℝ) (3 / 2), HasDerivAt (F · t) (D r t) r := by
    exact Filter.Eventually.of_forall fun t r hr ↦
      hasDerivAt_rescaledDensity L (x t) (v t) (ne_of_gt (by linarith [hr.1]))
        (hL.differentiable one_ne_zero _)
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := D) (μ := μ) (bound := fun _ ↦ B)
    (show Ioo (1 / 2 : ℝ) (3 / 2) ∈ 𝓝 (1 : ℝ) from Ioo_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun r ↦ (hFc r).aestronglyMeasurable)
    ((hFc 1).integrableOn_Ioc) hDc.aestronglyMeasurable hbound
    ((continuous_const : Continuous (fun _ : ℝ ↦ B)).integrableOn_Ioc) hdiff
  change HasDerivAt (fun r ↦ ∫ t in 0..d, F r t) (∫ t in 0..d, D 1 t) 1
  simpa only [intervalIntegral.integral_of_le hd] using h.2

/-- The actual rescaling derivative is the negative integral of the energy. -/
theorem hasDerivAt_rescaledArcCost_energy (L : E → E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {x v : ℝ → E} (hx : Continuous x) (hv : Continuous v) {d : ℝ} (hd : 0 ≤ d) :
    HasDerivAt (rescaledArcCost L x v d) (-(∫ t in 0..d, energyCurve L x v t)) 1 := by
  have h := hasDerivAt_rescaledArcCost L hL hx hv hd
  have heq : (fun t ↦ rescaledDensityDerivative L (x t) (v t) 1) =
      fun t ↦ -energyCurve L x v t := by
    funext t
    exact rescaledDensityDerivative_one L x v t (hL.differentiable one_ne_zero _)
  rw [heq, intervalIntegral.integral_neg] at h
  exact h

/-- Original Lagrangian cost of a rescaled curve over its physical duration. -/
noncomputable def actualArcCost (L : E → E → ℝ) (x : ℝ → E) (d r : ℝ) : ℝ :=
  ∫ t in 0..r * d, L (x (t / r)) (deriv (fun s : ℝ ↦ x (s / r)) t)

/-- The derivative theorem holds for the actual cost functional of the rescaled curve. -/
theorem hasDerivAt_actualArcCost_energy (L : E → E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {x v : ℝ → E} (hx : ∀ t, HasDerivAt x (v t) t) (hv : Continuous v)
    {d : ℝ} (hd : 0 ≤ d) :
    HasDerivAt (actualArcCost L x d) (-(∫ t in 0..d, energyCurve L x v t)) 1 := by
  have hxc : Continuous x := continuous_iff_continuousAt.mpr fun t ↦ (hx t).continuousAt
  apply (hasDerivAt_rescaledArcCost_energy L hL hxc hv hd).congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds (one_ne_zero : (1 : ℝ) ≠ 0)] with r hr
  exact (rescaledArcCost_eq_actual L hx d hr).symm

/-- Restrict the joint derivative to the state direction. -/
theorem state_fderiv_apply (L : E → E → ℝ) (x v w : E)
    (hL : DifferentiableAt ℝ L.uncurry (x, v)) :
    fderiv ℝ (fun y ↦ L y v) x w = fderiv ℝ L.uncurry (x, v) (w, 0) := by
  have hi : HasFDerivAt (fun z : E ↦ (z, v))
      (ContinuousLinearMap.inl ℝ E E) x := by
    convert (hasFDerivAt_id x).prodMk (hasFDerivAt_const v x) using 1 <;> rfl
  have h := hL.hasFDerivAt.comp x hi
  have heq : fderiv ℝ (fun y ↦ L y v) x = (fderiv ℝ L.uncurry (x, v)).comp
      (ContinuousLinearMap.inl ℝ E E) := by
    exact h.fderiv
  rw [heq]
  rfl

/-- The autonomous energy derivative is zero along a smooth Euler–Lagrange arc.
Both partial derivatives are actual Frechet derivatives of the Lagrangian. -/
theorem hasDerivAt_energy_zero (L : E → E → ℝ) {x v : ℝ → E} {t : ℝ} {a : E}
    (hL : DifferentiableAt ℝ L.uncurry (x t, v t))
    (hx : HasDerivAt x (v t) t) (hv : HasDerivAt v a t)
    (hEL : HasDerivAt (fun s ↦ fderiv ℝ (L (x s)) (v s))
      (fderiv ℝ (fun y ↦ L y (v t)) (x t)) t) :
    HasDerivAt (energyCurve L x v) 0 t := by
  have hcost := hL.hasFDerivAt.comp_hasDerivAt t (hx.prodMk hv)
  have h := (hEL.clm_apply hv).sub hcost
  have heq : fderiv ℝ (fun y ↦ L y (v t)) (x t) (v t) +
      fderiv ℝ (L (x t)) (v t) a -
      fderiv ℝ L.uncurry (x t, v t) (v t, a) = 0 := by
    rw [state_fderiv_apply L (x t) (v t) (v t) hL,
      velocity_fderiv_apply L (x t) (v t) a hL,
      ← map_add]
    simp
  rw [heq] at h
  convert h using 1
  rfl

/-- Energy conservation on the closed reference interval follows from the actual
Euler–Lagrange derivative and differentiability of velocity on each smooth arc. -/
theorem energy_eq_of_eulerLagrange (L : E → E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {x v : ℝ → E} (hx : ∀ t, HasDerivAt x (v t) t) (hv : Continuous v)
    {d : ℝ}
    (hvd : ∀ t ∈ Ico 0 d, DifferentiableAt ℝ v t)
    (hEL : ∀ t ∈ Ico 0 d, HasDerivAt (fun s ↦ fderiv ℝ (L (x s)) (v s))
      (fderiv ℝ (fun y ↦ L y (v t)) (x t)) t) :
    ∀ t ∈ Icc 0 d, energyCurve L x v t = energyCurve L x v 0 := by
  have hxc : Continuous x := continuous_iff_continuousAt.mpr fun t ↦ (hx t).continuousAt
  have hE : Continuous (energyCurve L x v) := by
    have hD : Continuous (fun t ↦ rescaledDensityDerivative L (x t) (v t) 1) := by
      have hDf : Continuous (fun t ↦ (fderiv ℝ L.uncurry (x t, v t)) (0, v t)) :=
        ((hL.continuous_fderiv one_ne_zero).comp (hxc.prodMk hv)).clm_apply
          ((continuous_const : Continuous (fun _ : ℝ ↦ (0 : E))).prodMk hv)
      convert (hL.continuous.comp (hxc.prodMk hv)).sub hDf using 1
      ext t
      simp [rescaledDensityDerivative]
    have heq : energyCurve L x v = fun t ↦ -rescaledDensityDerivative L (x t) (v t) 1 := by
      funext t
      rw [rescaledDensityDerivative_one L x v t (hL.differentiable one_ne_zero _)]
      simp
    rw [heq]
    exact hD.neg
  exact constant_of_has_deriv_right_zero hE.continuousOn fun t ht ↦
    (hasDerivAt_energy_zero L (hL.differentiable one_ne_zero _) (hx t)
      (hvd t ht).hasDerivAt (hEL t ht)).hasDerivWithinAt

/-- The two arcs exchange physical duration while the total duration remains fixed. -/
noncomputable def actualCornerCost (L : E → E → ℝ) (x₁ x₂ : ℝ → E)
    (d₁ d₂ ε : ℝ) : ℝ :=
  actualArcCost L x₁ d₁ (1 + ε / d₁) + actualArcCost L x₂ d₂ (1 - ε / d₂)

/-- Differentiate the actual two-arc cost, including the change in each duration. -/
theorem hasDerivAt_actualCornerCost (L : E → E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : Continuous v₁)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : Continuous v₂)
    {d₁ d₂ : ℝ} (hd₁ : 0 ≤ d₁) (hd₂ : 0 ≤ d₂) :
    HasDerivAt (actualCornerCost L x₁ x₂ d₁ d₂)
      ((∫ t in 0..d₂, energyCurve L x₂ v₂ t) / d₂ -
       (∫ t in 0..d₁, energyCurve L x₁ v₁ t) / d₁) 0 := by
  have hleft : HasDerivAt (fun ε : ℝ ↦ 1 + ε / d₁) (1 / d₁) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).div_const d₁).const_add 1
  have hright : HasDerivAt (fun ε : ℝ ↦ 1 - ε / d₂) (-(1 / d₂)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).div_const d₂).const_sub 1
  have h₁ := (hasDerivAt_actualArcCost_energy L hL hx₁ hv₁ hd₁).comp_of_eq 0 hleft (by simp)
  have h₂ := (hasDerivAt_actualArcCost_energy L hL hx₂ hv₂ hd₂).comp_of_eq 0 hright (by simp)
  convert h₁.add h₂ using 1
  · rfl
  · ring

/-- With constant energy on each arc, a genuine local minimum of the exchanged-duration
cost forces the two corner energies to agree. No first-variation identity is assumed. -/
theorem corner_energy_eq_of_actual_min (L : E → E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : Continuous v₁)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : Continuous v₂)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hE₁ : ∀ t ∈ Icc 0 d₁, energyCurve L x₁ v₁ t = energyCurve L x₁ v₁ d₁)
    (hE₂ : ∀ t ∈ Icc 0 d₂, energyCurve L x₂ v₂ t = energyCurve L x₂ v₂ 0)
    (hmin : IsLocalMin (actualCornerCost L x₁ x₂ d₁ d₂) 0) :
    energyCurve L x₁ v₁ d₁ = energyCurve L x₂ v₂ 0 := by
  have hz := hmin.hasDerivAt_eq_zero
    (hasDerivAt_actualCornerCost L hL hx₁ hv₁ hx₂ hv₂ hd₁.le hd₂.le)
  have h₁ : (∫ t in 0..d₁, energyCurve L x₁ v₁ t) = d₁ * energyCurve L x₁ v₁ d₁ := by
    calc
      (∫ t in 0..d₁, energyCurve L x₁ v₁ t) = ∫ _t in 0..d₁, energyCurve L x₁ v₁ d₁ :=
        intervalIntegral.integral_congr fun t ht ↦ hE₁ t (by simpa [uIcc_of_le hd₁.le] using ht)
      _ = _ := by simp
  have h₂ : (∫ t in 0..d₂, energyCurve L x₂ v₂ t) = d₂ * energyCurve L x₂ v₂ 0 := by
    calc
      (∫ t in 0..d₂, energyCurve L x₂ v₂ t) = ∫ _t in 0..d₂, energyCurve L x₂ v₂ 0 :=
        intervalIntegral.integral_congr fun t ht ↦ hE₂ t (by simpa [uIcc_of_le hd₂.le] using ht)
      _ = _ := by simp
  rw [h₁, h₂, mul_div_cancel_left₀ _ (ne_of_gt hd₁), mul_div_cancel_left₀ _ (ne_of_gt hd₂)] at hz
  exact (sub_eq_zero.mp hz).symm

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The rescaled arcs have fixed endpoints and hence preserve an existing corner join. -/
theorem rescaled_arcs_preserve_join (x₁ x₂ : ℝ → E) (d₁ : ℝ)
    (hjoin : x₁ d₁ = x₂ 0) {r₁ r₂ : ℝ} (hr₁ : r₁ ≠ 0) :
    x₁ ((r₁ * d₁) / r₁) = x₂ (0 / r₂) := by
  simpa only [mul_div_cancel_left₀ d₁ hr₁, zero_div] using hjoin

/-- The affine scaling factors exchange epsilon units of duration and preserve total time. -/
theorem exchanged_durations {d₁ d₂ : ℝ} (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (ε : ℝ) :
    (1 + ε / d₁) * d₁ = d₁ + ε ∧
    (1 - ε / d₂) * d₂ = d₂ - ε ∧
    (1 + ε / d₁) * d₁ + (1 - ε / d₂) * d₂ = d₁ + d₂ := by
  constructor
  · field_simp
  constructor
  · field_simp
  · field_simp
    ring

/-- A complete two-arc energy condition from actual Euler–Lagrange equations and a
local minimum of the genuine duration-exchange cost. The reference arcs have classical
extensions and have differentiable velocity on their open-ended reference intervals. -/
theorem corner_energy_eq_of_eulerLagrange_min (L : E → E → ℝ)
    (hL : ContDiff ℝ 1 L.uncurry) {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : Continuous v₁)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : Continuous v₂)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hvd₁ : ∀ t ∈ Ico 0 d₁, DifferentiableAt ℝ v₁ t)
    (hvd₂ : ∀ t ∈ Ico 0 d₂, DifferentiableAt ℝ v₂ t)
    (hEL₁ : ∀ t ∈ Ico 0 d₁, HasDerivAt (fun s ↦ fderiv ℝ (L (x₁ s)) (v₁ s))
      (fderiv ℝ (fun y ↦ L y (v₁ t)) (x₁ t)) t)
    (hEL₂ : ∀ t ∈ Ico 0 d₂, HasDerivAt (fun s ↦ fderiv ℝ (L (x₂ s)) (v₂ s))
      (fderiv ℝ (fun y ↦ L y (v₂ t)) (x₂ t)) t)
    (hmin : IsLocalMin (actualCornerCost L x₁ x₂ d₁ d₂) 0) :
    energyCurve L x₁ v₁ d₁ = energyCurve L x₂ v₂ 0 := by
  have hE₁ := energy_eq_of_eulerLagrange L hL hx₁ hv₁ hvd₁ hEL₁
  have hE₂ := energy_eq_of_eulerLagrange L hL hx₂ hv₂ hvd₂ hEL₂
  apply corner_energy_eq_of_actual_min L hL hx₁ hv₁ hx₂ hv₂ hd₁ hd₂ _ hE₂ hmin
  intro t ht
  exact (hE₁ t ht).trans (hE₁ d₁ ⟨hd₁.le, le_rfl⟩).symm

/-- Positive reference durations give an open interval of physically valid corner shifts. -/
theorem rescaling_factors_pos {d₁ d₂ ε : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hε : ε ∈ Ioo (-d₁) d₂) : 0 < 1 + ε / d₁ ∧ 0 < 1 - ε / d₂ := by
  constructor
  · have h : (-1 : ℝ) < ε / d₁ := (lt_div_iff₀ hd₁).mpr (by simpa using hε.1)
    linarith
  · have h : ε / d₂ < 1 := (div_lt_iff₀ hd₂).mpr (by simpa using hε.2)
    linarith

/-- Optimality among all positive-duration exchanges implies the required local minimum,
including any fixed endpoint penalty because these variations preserve the final state. -/
theorem actualCornerCost_isLocalMin_of_optimal_duration
    (L : E → E → ℝ) (K : E → ℝ) (x₁ x₂ : ℝ → E)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hmin : ∀ ε ∈ Ioo (-d₁) d₂,
      actualCornerCost L x₁ x₂ d₁ d₂ 0 + K (x₂ d₂) ≤
      actualCornerCost L x₁ x₂ d₁ d₂ ε + K (x₂ d₂)) :
    IsLocalMin (actualCornerCost L x₁ x₂ d₁ d₂) 0 := by
  filter_upwards [Ioo_mem_nhds (neg_neg_of_pos hd₁) hd₂] with ε hε
  exact (add_le_add_iff_right (K (x₂ d₂))).mp (hmin ε hε)

end TimeReparametrization
