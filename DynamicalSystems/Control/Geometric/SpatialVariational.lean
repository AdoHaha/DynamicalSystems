/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.TangentSolution
public import DynamicalSystems.Control.Geometric.UniformTaylor
public import DynamicalSystems.Control.Geometric.FlowGronwall
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Spatial differentiability of a local flow

The solution of the linear tangent equation is the derivative of the flow with
respect to its initial condition. The proof estimates the nonlinear Taylor
remainder uniformly on a small ball and applies the differential Grönwall
inequality to the difference between the nonlinear increment and its linear
approximation. All flow domains are reduced to a common neighborhood of the
initial point.

This is the classical differentiable-dependence argument; see Hartman,
*Ordinary Differential Equations*, Chapter V.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology NNReal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [CompleteSpace X] [FiniteDimensional ℝ X]

/-- A solution of the linear tangent equation starting at the identity is the
spatial derivative of the given local flow at every sufficiently small time. -/
theorem localFlow_hasFDerivAt_of_tangent
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀)
    {J : ℝ → X →L[ℝ] X} {Tj : ℝ} (hTj : 0 < Tj)
    (hJ₀ : J 0 = ContinuousLinearMap.id ℝ X)
    (hJ : ∀ t, |t| < Tj → HasDerivAt J
      ((fderiv ℝ f (localFlow hf t x₀)).comp (J t)) t) :
    ∀ᶠ t in 𝓝 (0 : ℝ), HasFDerivAt (localFlow hf t) (J t) x₀ := by
  let d := getLocalFlowData hf
  let Φ := localFlow hf
  let A : ℝ → X →L[ℝ] X := fun t ↦ fderiv ℝ f (Φ t x₀)
  have hx₀ : x₀ ∈ closedBall x₀ d.r := mem_closedBall_self d.hr.le
  have hΦ₀ : Φ 0 x₀ = x₀ := d.ϕ_zero x₀ hx₀
  obtain ⟨r, hr, hTaylor⟩ := hf.exists_uniform_fderiv_remainder
  have hflow : Tendsto (fun p : ℝ × X ↦ Φ p.1 p.2)
      (𝓝 (0, x₀)) (𝓝 x₀) := by
    change Tendsto (fun p : ℝ × X ↦ localFlow hf p.1 p.2)
      (𝓝 (0, x₀)) (𝓝 x₀)
    have h := (flowStrictFDerivAt hf).continuousAt.tendsto
    change Tendsto (fun p : ℝ × X ↦ localFlow hf p.1 p.2)
      (𝓝 (0, x₀)) (𝓝 (Φ 0 x₀)) at h
    rwa [hΦ₀] at h
  obtain ⟨b, hb, hbflow⟩ := Metric.eventually_nhds_iff_ball.mp
    (hflow.eventually (ball_mem_nhds x₀ hr))
  let K : ℝ := ‖fderiv ℝ f x₀‖ + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hAc : ContinuousAt A 0 :=
    mem_of_mem_nhds (eventually_continuousAt_fderiv_localFlow hf)
  have hA₀ : A 0 = fderiv ℝ f x₀ := by simp only [A, hΦ₀]
  have hAbdd : ∀ᶠ t in 𝓝 (0 : ℝ), ‖A t‖ ≤ K := by
    have h := hAc.norm.eventually (Iio_mem_nhds
      (show ‖A 0‖ < K by rw [hA₀]; dsimp [K]; linarith))
    filter_upwards [h] with t ht using le_of_lt ht
  obtain ⟨bA, hbA, hbAbdd⟩ := Metric.eventually_nhds_iff_ball.mp hAbdd
  let T : ℝ := min b (min d.ε (min Tj bA))
  have hT : 0 < T := lt_min hb (lt_min d.hε (lt_min hTj hbA))
  have hTb : T ≤ b := min_le_left _ _
  have hTε : T ≤ d.ε := (min_le_right _ _).trans (min_le_left _ _)
  have hTTj : T ≤ Tj := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hTbA : T ≤ bA := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  let ρ : ℝ := min b d.r
  have hρ : 0 < ρ := lt_min hb d.hr
  have hρb : ρ ≤ b := min_le_left _ _
  have hρr : ρ ≤ d.r := min_le_right _ _
  have htime : ∀ t ∈ Ioo (-T) T, t ∈ Ioo (-d.ε) d.ε := by
    intro t ht
    exact ⟨lt_of_le_of_lt (neg_le_neg hTε) ht.1, ht.2.trans_le hTε⟩
  have hbox : ∀ t ∈ Ioo (-T) T, ∀ y ∈ ball x₀ ρ, Φ t y ∈ ball x₀ r := by
    intro t ht y hy
    apply hbflow (t, y)
    rw [Metric.mem_ball, Prod.dist_eq, Real.dist_0_eq_abs]
    exact max_lt ((abs_lt.mpr ht).trans_le hTb) ((mem_ball.mp hy).trans_le hρb)
  have hcoeff : ∀ t ∈ Ioo (-T) T, ‖A t‖ ≤ K := by
    intro t ht
    apply hbAbdd t
    rw [Metric.mem_ball, Real.dist_0_eq_abs]
    exact (abs_lt.mpr ht).trans_le hTbA
  let L : ℝ := d.L'
  have hL : 0 ≤ L := NNReal.coe_nonneg d.L'
  have hL₁ : 0 < L + 1 := by linarith
  let C : ℝ := (Real.exp (K * T) - 1) / K
  have hC : 0 < C := gronwall_symmetric_multiplier_pos hT hK
  have hzeroρ : x₀ ∈ ball x₀ ρ := mem_ball_self hρ
  filter_upwards [Ioo_mem_nhds (by linarith : -T < (0 : ℝ)) hT] with t ht
  apply HasFDerivAt.of_isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  let η : ℝ := c / (C * (L + 1))
  have hη : 0 < η := div_pos hc (mul_pos hC hL₁)
  obtain ⟨δ, hδ, hrem⟩ := hTaylor η hη
  let σ : ℝ := min ρ (δ / (L + 1))
  have hσ : 0 < σ := lt_min hρ (div_pos hδ hL₁)
  filter_upwards [ball_mem_nhds x₀ hσ] with y hy
  have hyρ : y ∈ ball x₀ ρ :=
    mem_ball.mpr ((mem_ball.mp hy).trans_le (min_le_left _ _))
  have hyr : y ∈ closedBall x₀ d.r :=
    mem_closedBall.mpr ((mem_ball.mp hyρ).le.trans hρr)
  have hdist : ‖y - x₀‖ < δ / (L + 1) := by
    rw [← dist_eq_norm]
    exact (mem_ball.mp hy).trans_le (min_le_right _ _)
  have hΦdist : ∀ u ∈ Ioo (-T) T,
      ‖Φ u y - Φ u x₀‖ ≤ L * ‖y - x₀‖ := by
    intro u hu
    have h := (d.ϕ_lipschitz u (Ioo_subset_Icc_self (htime u hu))).dist_le_mul
      y hyr x₀ hx₀
    simpa only [dist_eq_norm, Φ, localFlow, d, L] using h
  have hΦclose : ∀ u ∈ Ioo (-T) T, dist (Φ u y) (Φ u x₀) < δ := by
    intro u hu
    rw [dist_eq_norm]
    calc
      ‖Φ u y - Φ u x₀‖ ≤ L * ‖y - x₀‖ := hΦdist u hu
      _ ≤ (L + 1) * ‖y - x₀‖ := by gcongr; linarith
      _ < δ := by
        have h := (mul_lt_mul_iff_right₀ hL₁).mpr hdist
        simpa only [mul_div_cancel₀ _ (ne_of_gt hL₁)] using h
  let e : ℝ → X := fun u ↦ Φ u y - Φ u x₀ - J u (y - x₀)
  let e' : ℝ → X := fun u ↦ f (Φ u y) - f (Φ u x₀) - A u (J u (y - x₀))
  have he₀ : e 0 = 0 := by
    have hy₀ : Φ 0 y = y := d.ϕ_zero y hyr
    simp only [e, hy₀, hΦ₀, hJ₀, ContinuousLinearMap.id_apply, sub_self]
  have he : ∀ u ∈ Ioo (-T) T, HasDerivAt e (e' u) u := by
    intro u hu
    have h₁ : HasDerivAt (fun u ↦ Φ u y) (f (Φ u y)) u :=
      d.ϕ_hasDerivAt u (htime u hu) y hyr
    have h₂ : HasDerivAt (fun u ↦ Φ u x₀) (f (Φ u x₀)) u :=
      d.ϕ_hasDerivAt u (htime u hu) x₀ hx₀
    have h₃ : HasDerivAt (fun u ↦ J u (y - x₀)) (A u (J u (y - x₀))) u := by
      simpa using (hJ u ((abs_lt.mpr hu).trans_le hTTj)).clm_apply
        (hasDerivAt_const u (y - x₀))
    exact (h₁.sub h₂).sub h₃
  have hbound : ∀ u ∈ Ioo (-T) T,
      ‖e' u‖ ≤ K * ‖e u‖ + η * L * ‖y - x₀‖ := by
    intro u hu
    have herr : e' u =
        (f (Φ u y) - f (Φ u x₀) - A u (Φ u y - Φ u x₀)) + A u (e u) := by
      dsimp [e', e]
      simp only [map_sub]
      abel
    have hR : ‖f (Φ u y) - f (Φ u x₀) - A u (Φ u y - Φ u x₀)‖
        ≤ η * ‖Φ u y - Φ u x₀‖ :=
      hrem (Φ u y) (hbox u hu y hyρ) (Φ u x₀) (hbox u hu x₀ hzeroρ) (hΦclose u hu)
    rw [herr]
    calc
      ‖(f (Φ u y) - f (Φ u x₀) - A u (Φ u y - Φ u x₀)) + A u (e u)‖
          ≤ ‖f (Φ u y) - f (Φ u x₀) - A u (Φ u y - Φ u x₀)‖ + ‖A u (e u)‖ := norm_add_le _ _
      _ ≤ η * ‖Φ u y - Φ u x₀‖ + ‖A u‖ * ‖e u‖ :=
        add_le_add hR ((A u).le_opNorm _)
      _ ≤ η * (L * ‖y - x₀‖) + K * ‖e u‖ := by
        gcongr
        · exact hΦdist u hu
        · exact hcoeff u hu
      _ = K * ‖e u‖ + η * L * ‖y - x₀‖ := by ring
  have hE := norm_le_gronwall_symmetric_uniform hT hK
    (show 0 ≤ η * L * ‖y - x₀‖ by positivity) he₀ he hbound ht
  change ‖e t‖ ≤ c * ‖y - x₀‖
  calc
    ‖e t‖ ≤ C * (η * L * ‖y - x₀‖) := hE
    _ ≤ C * (η * (L + 1) * ‖y - x₀‖) := by gcongr; linarith
    _ = c * ‖y - x₀‖ := by
      dsimp [η]
      field_simp

/-- The local flow of a `C¹` field is differentiable in its initial point at
every sufficiently small time. -/
theorem eventually_differentiableAt_localFlow
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ (localFlow hf t) x₀ := by
  obtain ⟨δ, hδ, J, hJ₀, hJ⟩ := exists_localFlow_tangent_solution hf
  filter_upwards [localFlow_hasFDerivAt_of_tangent hf hδ hJ₀ hJ] with t ht
  exact ht.differentiableAt
