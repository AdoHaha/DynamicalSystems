/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.FlowCommutator
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # The first time derivative of the spatial flow derivative

The two-point estimate below follows directly from the flow equation and strict
differentiability of the vector field. It does not assume spatial differentiability
of the flow. Consequently, once spatial derivatives exist for times sufficiently
close to zero, their first-order time expansion follows without a further continuity
or variational-equation hypothesis.

The remaining hypothesis of `flow_deriv_firstOrder_of_eventually_differentiableAt`
is precisely existence of those spatial derivatives. This file does not construct
them and does not establish smooth dependence of solutions on their initial data.

The argument is classical; see Hartman, *Ordinary Differential Equations*, Chapter V
(differentiable dependence on initial conditions).
-/

@[expose] public section

open Set Filter Metric
open scoped Topology NNReal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- A two-point first-order spatial increment estimate for the local flow.

For every positive error constant, a common time and space neighbourhood makes the
remainder bounded by that constant times `|t| * ‖y - x₀‖`. The estimate requires no
spatial derivative of the flow. -/
theorem localFlow_increment_firstOrder_small {f : X → X} {x₀ : X}
    (hf : ContDiffAt ℝ 1 f x₀) {c : ℝ} (hc : 0 < c) :
    ∃ δ > 0, ∀ t : ℝ, |t| < δ → ∀ y : X, dist y x₀ < δ →
      ‖localFlow hf t y - localFlow hf t x₀ - (y - x₀) -
          t • fderiv ℝ f x₀ (y - x₀)‖ ≤ c * |t| * ‖y - x₀‖ := by
  let data := getLocalFlowData hf
  let B : X →L[ℝ] X := fderiv ℝ f x₀
  let η : ℝ := (c / 2) / ((data.L' : ℝ) + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hstrict : HasStrictFDerivAt f B x₀ := hf.hasStrictFDerivAt (by norm_num)
  have hrem : ∀ᶠ p : X × X in 𝓝 (x₀, x₀),
      ‖f p.1 - f p.2 - B (p.1 - p.2)‖ ≤ η * ‖p.1 - p.2‖ :=
    Asymptotics.isLittleO_iff.mp hstrict.isLittleO hη
  obtain ⟨δf, hδf, hfsmall⟩ := Metric.eventually_nhds_iff.mp hrem
  let ρ := min δf data.a
  have hρ : 0 < ρ := lt_min hδf data.ha
  have hflow : Tendsto (fun p : ℝ × X ↦ data.ϕ p.1 p.2) (𝓝 (0, x₀)) (𝓝 x₀) :=
    tendsto_flow_aux data.hε data.hr data.ϕ_zero
      (fun t ht ↦ data.ϕ_hasDerivAt t ht x₀
        (mem_closedBall_self data.hr.le)) data.ϕ_lipschitz
  rw [Metric.tendsto_nhds_nhds] at hflow
  obtain ⟨δϕ, hδϕ, hϕsmall⟩ := hflow ρ hρ
  let M : ℝ := ‖B‖ * (data.K : ℝ) * (data.L' : ℝ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let δ := min δϕ (min data.ε (min data.r ((c / 2) / (M + 1))))
  have hδ : 0 < δ :=
    lt_min hδϕ (lt_min data.hε (lt_min data.hr (by positivity)))
  have hδϕle : δ ≤ δϕ := min_le_left _ _
  have hδε : δ ≤ data.ε := (min_le_right _ _).trans (min_le_left _ _)
  have hδr : δ ≤ data.r :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδM : δ ≤ (c / 2) / (M + 1) :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have h0ball : (0 : ℝ) ∈ ball (0 : ℝ) δ := mem_ball_self hδ
  have htime : ∀ {u : ℝ}, |u| < δ → u ∈ Ioo (-data.ε) data.ε := by
    intro u hu
    exact abs_lt.mp (hu.trans_le hδε)
  have hinterval : ∀ {u : ℝ}, |u| < δ → ∀ v ∈ uIcc 0 u, |v| < δ := by
    intro u hu v hv
    have hub : u ∈ ball (0 : ℝ) δ := by simpa using hu
    simpa using mem_ball_zero_of_mem_uIcc h0ball hub hv
  have hsmall : ∀ {u : ℝ}, |u| < δ → ∀ {z : X}, dist z x₀ < δ →
      dist (data.ϕ u z) x₀ < ρ := by
    intro u hu z hz
    apply hϕsmall (x := (u, z))
    rw [Prod.dist_eq, Real.dist_0_eq_abs]
    exact max_lt (hu.trans_le hδϕle) (hz.trans_le hδϕle)
  have hstay : ∀ {u : ℝ}, |u| < δ → ∀ {z : X}, dist z x₀ < δ →
      data.ϕ u z ∈ closedBall x₀ data.a := by
    intro u hu z hz
    exact mem_closedBall.mpr ((hsmall hu hz).trans_le (min_le_right _ _)).le
  have hηL : η * (data.L' : ℝ) ≤ c / 2 := by
    calc
      η * (data.L' : ℝ) ≤ η * ((data.L' : ℝ) + 1) := by gcongr; linarith
      _ = c / 2 := by dsimp [η]; field_simp
  have hMu : ∀ {u : ℝ}, |u| < δ → M * |u| ≤ c / 2 := by
    intro u hu
    calc
      M * |u| ≤ (M + 1) * |u| := by gcongr; linarith
      _ ≤ (M + 1) * ((c / 2) / (M + 1)) := by gcongr; exact (hu.trans_le hδM).le
      _ = c / 2 := mul_div_cancel₀ _ (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro t ht y hy
  have hyball : y ∈ closedBall x₀ data.r := mem_closedBall.mpr (hy.trans_le hδr).le
  have hxball : x₀ ∈ closedBall x₀ data.r := mem_closedBall_self data.hr.le
  have hxδ : dist x₀ x₀ < δ := by simpa using hδ
  have hincrement : ∀ {u : ℝ}, |u| < δ →
      ‖data.ϕ u y - data.ϕ u x₀ - (y - x₀)‖ ≤
        ((data.K : ℝ) * (data.L' : ℝ) * |u|) * ‖y - x₀‖ := by
    intro u hu
    have hi : uIcc 0 u ⊆ Ioo (-data.ε) data.ε :=
      fun v hv ↦ htime (hinterval hu v hv)
    exact flow_mvt_space data.ϕ_hasDerivAt data.ϕ_lipschitz data.f_lipschitz
      hyball hxball (data.ϕ_zero y hyball) (data.ϕ_zero x₀ hxball) hi
      (fun v hv ↦ Ioo_subset_Icc_self (hi hv))
      (fun v hv ↦ hstay (hinterval hu v hv) hy)
      (fun v hv ↦ hstay (hinterval hu v hv) hxδ)
  let R : ℝ → X := fun u ↦ data.ϕ u y - data.ϕ u x₀ - u • B (y - x₀)
  have hRderiv : ∀ u ∈ uIcc 0 t,
      HasDerivWithinAt R (f (data.ϕ u y) - f (data.ϕ u x₀) - B (y - x₀))
        (uIcc 0 t) u := by
    intro u hu
    have hut := htime (hinterval ht u hu)
    have hlin : HasDerivAt (fun v : ℝ ↦ v • B (y - x₀)) (B (y - x₀)) u := by
      simpa using (hasDerivAt_id u).smul_const (B (y - x₀))
    exact (((data.ϕ_hasDerivAt u hut y hyball).sub
      (data.ϕ_hasDerivAt u hut x₀ hxball)).sub hlin).hasDerivWithinAt
  have hRbound : ∀ u ∈ uIcc 0 t,
      ‖f (data.ϕ u y) - f (data.ϕ u x₀) - B (y - x₀)‖ ≤ c * ‖y - x₀‖ := by
    intro u hu
    have huδ := hinterval ht u hu
    have hpair : dist (data.ϕ u y, data.ϕ u x₀) (x₀, x₀) < δf := by
      rw [Prod.dist_eq]
      exact max_lt ((hsmall huδ hy).trans_le (min_le_left _ _))
        ((hsmall huδ hxδ).trans_le (min_le_left _ _))
    have hfrem := hfsmall hpair
    have hlip := (data.ϕ_lipschitz u (Ioo_subset_Icc_self (htime huδ))).dist_le_mul
      y hyball x₀ hxball
    rw [dist_eq_norm, dist_eq_norm] at hlip
    have he₁ : ‖f (data.ϕ u y) - f (data.ϕ u x₀) -
        B (data.ϕ u y - data.ϕ u x₀)‖ ≤ (c / 2) * ‖y - x₀‖ := by
      calc
        _ ≤ η * ‖data.ϕ u y - data.ϕ u x₀‖ := hfrem
        _ ≤ η * ((data.L' : ℝ) * ‖y - x₀‖) := by gcongr
        _ = (η * (data.L' : ℝ)) * ‖y - x₀‖ := by ring
        _ ≤ (c / 2) * ‖y - x₀‖ := by gcongr
    have he₂ : ‖B (data.ϕ u y - data.ϕ u x₀ - (y - x₀))‖ ≤
        (c / 2) * ‖y - x₀‖ := by
      calc
        _ ≤ ‖B‖ * ‖data.ϕ u y - data.ϕ u x₀ - (y - x₀)‖ := B.le_opNorm _
        _ ≤ ‖B‖ * (((data.K : ℝ) * (data.L' : ℝ) * |u|) * ‖y - x₀‖) := by
          gcongr
          exact hincrement huδ
        _ = (M * |u|) * ‖y - x₀‖ := by dsimp [M]; ring
        _ ≤ (c / 2) * ‖y - x₀‖ := by gcongr; exact hMu huδ
    have heq : f (data.ϕ u y) - f (data.ϕ u x₀) - B (y - x₀) =
        (f (data.ϕ u y) - f (data.ϕ u x₀) - B (data.ϕ u y - data.ϕ u x₀)) +
          B (data.ϕ u y - data.ϕ u x₀ - (y - x₀)) := by
      simp only [map_sub]
      abel
    rw [heq]
    calc
      _ ≤ ‖f (data.ϕ u y) - f (data.ϕ u x₀) - B (data.ϕ u y - data.ϕ u x₀)‖ +
          ‖B (data.ϕ u y - data.ϕ u x₀ - (y - x₀))‖ := norm_add_le _ _
      _ ≤ (c / 2) * ‖y - x₀‖ + (c / 2) * ‖y - x₀‖ := add_le_add he₁ he₂
      _ = c * ‖y - x₀‖ := by ring
  have hmvt := (convex_uIcc 0 t).norm_image_sub_le_of_norm_hasDerivWithin_le hRderiv hRbound
    left_mem_uIcc right_mem_uIcc
  have hRsub : R t - R 0 = data.ϕ t y - data.ϕ t x₀ - (y - x₀) - t • B (y - x₀) := by
    dsimp [R]
    rw [data.ϕ_zero y hyball, data.ϕ_zero x₀ hxball, zero_smul, sub_zero]
    abel
  rw [hRsub, sub_zero, Real.norm_eq_abs] at hmvt
  calc
    _ ≤ (c * ‖y - x₀‖) * |t| := hmvt
    _ = c * |t| * ‖y - x₀‖ := by ring

/-- Existence of the spatial derivatives near time zero suffices for their first-order
time expansion. No continuity of these derivatives or variational identity is assumed.

The spatial differentiability hypothesis remains an explicit analytical prerequisite;
this theorem supplies the time derivative once that prerequisite has been established. -/
theorem flow_deriv_firstOrder_of_eventually_differentiableAt {f : X → X} {x₀ : X}
    (hf : ContDiffAt ℝ 1 f x₀)
    (hdiff : ∀ᶠ t : ℝ in 𝓝 0, DifferentiableAt ℝ (localFlow hf t) x₀) :
    HasDerivAt (fun t : ℝ ↦ fderiv ℝ (localFlow hf t) x₀) (fderiv ℝ f x₀) 0 := by
  apply HasDerivAt.of_isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hsmall⟩ := localFlow_increment_firstOrder_small hf hc
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ, hdiff] with t ht htdiff
  have htδ : |t| < δ := by simpa using ht
  let B : X →L[ℝ] X := fderiv ℝ f x₀
  let R : X → X := fun y ↦ localFlow hf t y - y - t • B y
  have hRderiv : HasFDerivAt R
      (fderiv ℝ (localFlow hf t) x₀ - ContinuousLinearMap.id ℝ X - t • B) x₀ :=
    (htdiff.hasFDerivAt.sub (hasFDerivAt_id x₀)).sub (B.hasFDerivAt.const_smul t)
  have hbound : ‖fderiv ℝ (localFlow hf t) x₀ - ContinuousLinearMap.id ℝ X - t • B‖ ≤
      c * |t| := by
    apply hRderiv.le_of_lip' (by positivity)
    filter_upwards [Metric.ball_mem_nhds x₀ hδ] with y hy
    have heq : R y - R x₀ = localFlow hf t y - localFlow hf t x₀ - (y - x₀) -
        t • B (y - x₀) := by
      dsimp [R]
      rw [map_sub, smul_sub]
      abel
    rw [heq]
    exact hsmall t htδ y (mem_ball.mp hy)
  simpa only [flow_deriv_at_zero f x₀ hf, sub_zero, Real.norm_eq_abs] using hbound
