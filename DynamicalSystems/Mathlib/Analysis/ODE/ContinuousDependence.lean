/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistence
public import Mathlib.Topology.Compactness.Compact

/-!
# Continuous dependence of supplied integral curves

Uniform local Lipschitz bounds become uniform on a fixed compact reference
trajectory. A differential fencing estimate then controls all nearby supplied
solutions. No completeness assumption, finite-dimensionality, differentiability
of the vector field, or local-flow construction is needed.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E]

namespace UniformlyLocallyLipschitz

/-- Pointwise continuity in time together with uniform local Lipschitz continuity
in the state gives joint continuity. Here `Continuous f` uses the Pi topology. -/
theorem continuous_uncurry {f : ℝ → E → E} (hf : UniformlyLocallyLipschitz f)
    (ht : Continuous f) : Continuous f.uncurry := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t, x⟩
  obtain ⟨K, U, hU, hK⟩ := hf t x
  have hcont : ContinuousOn f.uncurry
      ({s | LipschitzOnWith K (f s) U} ×ˢ U) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith' _ K
      (fun _ hs ↦ hs) (fun y _ ↦ (continuous_apply y |>.comp ht).continuousOn)
  exact hcont.continuousAt (prod_mem_nhds hK hU)

/-- Along a continuous reference curve on a compact time set, one radius and
one Lipschitz constant work for every time. Compactness is used only in the
time variable, so the state space may be infinite-dimensional or incomplete. -/
theorem exists_lipschitzOnWith_closedBall_along {f : ℝ → E → E}
    (hf : UniformlyLocallyLipschitz f) {γ : ℝ → E} {I : Set ℝ}
    (hI : IsCompact I) (hγ : ContinuousOn γ I) :
    ∃ (K : ℝ≥0) (r : ℝ), 0 < r ∧
      ∀ t ∈ I, LipschitzOnWith K (f t) (closedBall (γ t) r) := by
  let P : Set ℝ → Prop := fun S ↦ ∃ (K : ℝ≥0) (r : ℝ), 0 < r ∧
    ∀ t ∈ S, LipschitzOnWith K (f t) (closedBall (γ t) r)
  apply hI.induction_on (p := P)
  · exact ⟨0, 1, zero_lt_one, by simp⟩
  · rintro S T hST ⟨K, r, hr, h⟩
    exact ⟨K, r, hr, fun t ht ↦ h t (hST ht)⟩
  · rintro S T ⟨K₁, r₁, hr₁, h₁⟩ ⟨K₂, r₂, hr₂, h₂⟩
    refine ⟨max K₁ K₂, min r₁ r₂, lt_min hr₁ hr₂, ?_⟩
    intro t ht
    rcases ht with ht | ht
    · exact ((h₁ t ht).mono (closedBall_subset_closedBall (min_le_left _ _))).weaken
        (le_max_left _ _)
    · exact ((h₂ t ht).mono (closedBall_subset_closedBall (min_le_right _ _))).weaken
        (le_max_right _ _)
  · intro t ht
    obtain ⟨K, U, hU, hK⟩ := hf t (γ t)
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hU
    let V : Set ℝ := {s | LipschitzOnWith K (f s) U ∧ γ s ∈ ball (γ t) (r / 2)}
    refine ⟨V, ?_, K, r / 2, half_pos hr, ?_⟩
    · exact inter_mem (mem_nhdsWithin_of_mem_nhds hK)
        ((hγ t ht).eventually_mem (ball_mem_nhds _ (half_pos hr)))
    · intro s hs
      apply hs.1.mono
      intro y hy
      apply hball
      have hys : dist y (γ s) ≤ r / 2 := hy
      have hst : dist (γ s) (γ t) < r / 2 := hs.2
      calc
        dist y (γ t) ≤ dist y (γ s) + dist (γ s) (γ t) := dist_triangle _ _ _
        _ < r := by linarith

end UniformlyLocallyLipschitz

variable [NormedSpace ℝ E]

/-- A differential fencing estimate with a state-local derivative bound. The
bound is assumed only while the curve lies in the radius-`r` ball. The barrier
itself stays inside that ball, so the conclusion does not assume confinement. -/
theorem norm_le_mul_exp_of_norm_deriv_le_on_closedBall
    {e e' : ℝ → E} {a b K r δ : ℝ}
    (hK : 0 ≤ K) (hδ : 0 < δ)
    (he : ContinuousOn e (Icc a b))
    (he' : ∀ t ∈ Ico a b, HasDerivWithinAt e (e' t) (Ici t) t)
    (ha : ‖e a‖ ≤ δ)
    (hbound : ∀ t ∈ Ico a b, ‖e t‖ ≤ r → ‖e' t‖ ≤ K * ‖e t‖)
    (hsmall : δ * Real.exp ((K + 1) * (b - a)) ≤ r) :
    ∀ t ∈ Icc a b, ‖e t‖ ≤ δ * Real.exp ((K + 1) * (b - a)) := by
  have hbarrier : ∀ t, HasDerivAt (fun s ↦ δ * Real.exp ((K + 1) * (s - a)))
      ((K + 1) * (δ * Real.exp ((K + 1) * (t - a)))) t := by
    intro t
    convert hasDerivAt_gronwallBound_shift δ (K + 1) 0 t a using 1 <;>
      simp [gronwallBound_ε0]
  have hmono : ∀ t ≤ b,
      δ * Real.exp ((K + 1) * (t - a)) ≤ δ * Real.exp ((K + 1) * (b - a)) := by
    intro t ht
    gcongr
  have hfence := image_norm_le_of_norm_deriv_right_lt_deriv_boundary he he'
    (B := fun s ↦ δ * Real.exp ((K + 1) * (s - a)))
    (B' := fun t ↦ (K + 1) * (δ * Real.exp ((K + 1) * (t - a))))
    (by simpa using ha) hbarrier (by
      intro t ht hEq
      have htube : ‖e t‖ ≤ r := hEq.trans_le ((hmono t ht.2.le).trans hsmall)
      have hpos : 0 < δ * Real.exp ((K + 1) * (t - a)) :=
        mul_pos hδ (Real.exp_pos _)
      calc
        ‖e' t‖ ≤ K * ‖e t‖ := hbound t ht htube
        _ < (K + 1) * (δ * Real.exp ((K + 1) * (t - a))) := by rw [hEq]; nlinarith)
  exact fun t ht ↦ (hfence ht).trans (hmono t ht.2)

/-- The same local differential estimate on a symmetric time interval, in both
time directions. -/
theorem norm_le_mul_exp_of_norm_deriv_le_on_closedBall_symmetric
    {e e' : ℝ → E} {t₀ T K r δ : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hδ : 0 < δ)
    (he : ∀ t, HasDerivAt e (e' t) t) (h₀ : ‖e t₀‖ ≤ δ)
    (hbound : ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      ‖e t‖ ≤ r → ‖e' t‖ ≤ K * ‖e t‖)
    (hsmall : δ * Real.exp ((K + 1) * T) ≤ r) :
    ∀ t ∈ Icc (t₀ - T) (t₀ + T), ‖e t‖ ≤ δ * Real.exp ((K + 1) * T) := by
  have hcont : Continuous e := continuous_iff_continuousAt.mpr
    (fun t ↦ (he t).continuousAt)
  have hfwd : ∀ t ∈ Icc t₀ (t₀ + T),
      ‖e t‖ ≤ δ * Real.exp ((K + 1) * T) := by
    simpa using norm_le_mul_exp_of_norm_deriv_le_on_closedBall
      (a := t₀) (b := t₀ + T) hK hδ hcont.continuousOn
      (fun t _ ↦ (he t).hasDerivWithinAt) h₀
      (fun t ht ↦ hbound t ⟨by linarith [ht.1], ht.2.le⟩) (by simpa using hsmall)
  have hbwd : ∀ t ∈ Icc t₀ (t₀ + T),
      ‖e (2 * t₀ - t)‖ ≤ δ * Real.exp ((K + 1) * T) := by
    have hreflect : ∀ t,
        HasDerivAt (fun s ↦ e (2 * t₀ - s)) (-e' (2 * t₀ - t)) t := by
      intro t
      have ht : HasDerivAt (fun s : ℝ ↦ 2 * t₀ - s) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (2 * t₀)
      simpa [Function.comp_def] using (he (2 * t₀ - t)).scomp t ht
    simpa using norm_le_mul_exp_of_norm_deriv_le_on_closedBall
      (e := fun t ↦ e (2 * t₀ - t)) (e' := fun t ↦ -e' (2 * t₀ - t))
      (a := t₀) (b := t₀ + T) hK hδ
      ((hcont.comp (by fun_prop)).continuousOn)
      (fun t _ ↦ (hreflect t).hasDerivWithinAt)
      (by simpa [show 2 * t₀ - t₀ = t₀ by ring] using h₀)
      (by
        intro t ht hsmall'
        simpa using hbound (2 * t₀ - t)
          ⟨by linarith [ht.2], by linarith [ht.1]⟩ hsmall')
      (by simpa using hsmall)
  intro t ht
  rcases le_or_gt t₀ t with h | h
  · exact hfwd t ⟨h, ht.2⟩
  · have hb := hbwd (2 * t₀ - t) ⟨by linarith, by linarith [ht.1]⟩
    simpa [show 2 * t₀ - (2 * t₀ - t) = t by ring] using hb

/-- Nearby supplied integral curves stay close to a reference trajectory on
an arbitrary compact interval. The local Lipschitz tube is obtained from
`UniformlyLocallyLipschitz.exists_lipschitzOnWith_closedBall_along`. -/
theorem IsIntegralCurve.dist_le_mul_exp_of_mem_closedBall
    {f : ℝ → E → E} {γ η : ℝ → E} {t₀ T r δ : ℝ} {K : ℝ≥0}
    (hγ : IsIntegralCurve γ f) (hη : IsIntegralCurve η f)
    (hT : 0 ≤ T) (hδ : 0 < δ)
    (hK : ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      LipschitzOnWith K (f t) (closedBall (γ t) r))
    (h₀ : dist (η t₀) (γ t₀) ≤ δ)
    (hsmall : δ * Real.exp (((K : ℝ) + 1) * T) ≤ r) :
    ∀ t ∈ Icc (t₀ - T) (t₀ + T),
      dist (η t) (γ t) ≤ δ * Real.exp (((K : ℝ) + 1) * T) := by
  have hr : 0 ≤ r := (by positivity : 0 ≤ δ * Real.exp (((K : ℝ) + 1) * T)).trans hsmall
  simpa only [dist_eq_norm] using norm_le_mul_exp_of_norm_deriv_le_on_closedBall_symmetric
    (e := fun t ↦ η t - γ t) (e' := fun t ↦ f t (η t) - f t (γ t))
    hT K.coe_nonneg hδ (fun t ↦ (hη t).sub (hγ t))
    (by simpa only [dist_eq_norm] using h₀)
    (by
      intro t ht htr
      exact (hK t ht).norm_sub_le (by simpa only [mem_closedBall_iff_norm] using htr)
        (mem_closedBall_self hr)) hsmall

/-- A family of supplied global integral curves depends jointly continuously
on its parameter and on time whenever its initial values are continuous and
the vector field is uniformly locally Lipschitz in the state.

No continuity in time of the vector field is required: each supplied integral
curve is already differentiable, and the difference of its derivatives is
controlled by the local state Lipschitz bound. -/
theorem continuous_uncurry_of_isIntegralCurve
    {P : Type*} [TopologicalSpace P] {f : ℝ → E → E} {α : P → ℝ → E}
    (hf : UniformlyLocallyLipschitz f) (hα : ∀ x, IsIntegralCurve (α x) f)
    (t₀ : ℝ) (h₀ : Continuous (fun x ↦ α x t₀)) :
    Continuous α.uncurry := by
  rw [continuous_iff_continuousAt]
  rintro ⟨x₀, t₁⟩
  rw [Metric.continuousAt_iff']
  intro ε hε
  let T : ℝ := |t₁ - t₀| + 1
  have hT : 0 < T := by dsimp [T]; positivity
  have ht₁ : t₁ ∈ Ioo (t₀ - T) (t₀ + T) := by
    dsimp [T]
    constructor <;> linarith [le_abs_self (t₁ - t₀), neg_abs_le (t₁ - t₀)]
  obtain ⟨K, r, hr, hK⟩ := hf.exists_lipschitzOnWith_closedBall_along
    (γ := α x₀) (I := Icc (t₀ - T) (t₀ + T))
    isCompact_Icc (hα x₀).continuous.continuousOn
  let C : ℝ := Real.exp (((K : ℝ) + 1) * T)
  have hC : 0 < C := Real.exp_pos _
  let δ : ℝ := min r (ε / 2) / (2 * C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδC : δ * C = min r (ε / 2) / 2 := by
    dsimp [δ]
    field_simp [ne_of_gt hC]
  have hsmall : δ * C ≤ r := by rw [hδC]; linarith [min_le_left r (ε / 2)]
  have hε' : δ * C < ε / 2 := by rw [hδC]; linarith [min_le_right r (ε / 2)]
  have hinitial : ∀ᶠ p : P × ℝ in 𝓝 (x₀, t₁),
      dist (α p.1 t₀) (α x₀ t₀) < δ := by
    exact Metric.tendsto_nhds.mp
      ((h₀.comp continuous_fst).continuousAt) δ hδ
  have htime : ∀ᶠ p : P × ℝ in 𝓝 (x₀, t₁),
      p.2 ∈ Icc (t₀ - T) (t₀ + T) :=
    continuous_snd.continuousAt.eventually_mem (Icc_mem_nhds ht₁.1 ht₁.2)
  have href : ∀ᶠ p : P × ℝ in 𝓝 (x₀, t₁),
      dist (α x₀ p.2) (α x₀ t₁) < ε / 2 :=
    Metric.tendsto_nhds.mp (((hα x₀).continuous.comp continuous_snd).continuousAt)
      (ε / 2) (half_pos hε)
  filter_upwards [hinitial, htime, href] with p hp ht hpt
  have hclose := (hα x₀).dist_le_mul_exp_of_mem_closedBall (hα p.1)
    hT.le hδ hK hp.le hsmall p.2 ht
  change dist (α p.1 p.2) (α x₀ t₁) < ε
  calc
    dist (α p.1 p.2) (α x₀ t₁) ≤
        dist (α p.1 p.2) (α x₀ p.2) + dist (α x₀ p.2) (α x₀ t₁) := dist_triangle _ _ _
    _ < ε := by change _ ≤ δ * C at hclose; linarith

namespace IsFundamentalSolution

/-- A supplied fundamental solution is jointly continuous in its initial state
and its terminal time under uniform local state Lipschitz continuity alone. -/
theorem continuous_of_uniformlyLocallyLipschitz
    {Φ : ℝ → E → ℝ → E} {f : ℝ → E → E}
    (hΦ : IsFundamentalSolution Φ f) (hf : UniformlyLocallyLipschitz f) (t₀ : ℝ) :
    Continuous (Φ t₀).uncurry := by
  apply continuous_uncurry_of_isIntegralCurve hf (hΦ.isIntegralCurve t₀) t₀
  convert (continuous_id : Continuous (id : E → E)) using 1
  ext x
  exact hΦ.initial t₀ x

/-- Compatibility form of fundamental-solution continuity. The time
continuity premise is unnecessary once the integral curves are supplied. -/
theorem continuous {Φ : ℝ → E → ℝ → E} {f : ℝ → E → E}
    (hΦ : IsFundamentalSolution Φ f) (hf : UniformlyLocallyLipschitz f)
    (_hf' : Continuous f) (t₀ : ℝ) : Continuous (Φ t₀).uncurry :=
  hΦ.continuous_of_uniformlyLocallyLipschitz hf t₀

end IsFundamentalSolution
