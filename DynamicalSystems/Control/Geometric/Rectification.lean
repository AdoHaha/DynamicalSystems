/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki, Antigravity
-/
module

public import Mathlib.Analysis.ODE.PicardLindelof
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-! # Local rectification of nonsingular vector fields (flow-box theorem)

This file formalises the local rectification theorem (also known as the flow-box or
straightening theorem) for a continuously differentiable vector field on a
finite-dimensional real normed space.

## References

* Krener, A. J., *Differential Geometric Methods in Nonlinear Control*, in
  *Encyclopedia of Systems and Control*, Springer, 2015, pp. 563–570.
* Sontag, E. D., *Mathematical Control Theory: Deterministic Finite Dimensional Systems*,
  2nd ed., Springer, 1998, Ch. 4 §4.2–§4.4 (printed pp. 141–176, especially Lemma 4.4.16).
-/

open Set Filter Metric
open scoped Topology NNReal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma tendsto_flow_aux {ϕ : ℝ → X → X} {x₀ : X} {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    {L' : NNReal} (hϕ0 : ∀ x ∈ closedBall x₀ r, ϕ 0 x = x)
    {f : X → X} (hderiv : ∀ t ∈ Ioo (-ε) ε, HasDerivAt (ϕ · x₀) (f (ϕ t x₀)) t)
    (hlip : ∀ t ∈ Icc (-ε) ε, LipschitzOnWith L' (ϕ t ·) (closedBall x₀ r)) :
    Tendsto (fun p : ℝ × X ↦ ϕ p.1 p.2) (𝓝 (0, x₀)) (𝓝 x₀) := by
  rw [Metric.tendsto_nhds_nhds]
  intro η hη
  have hϕ0_x0 : ϕ 0 x₀ = x₀ := hϕ0 x₀ (mem_closedBall_self (le_of_lt hr))
  have h0_mem : (0 : ℝ) ∈ Ioo (-ε) ε := by
    rw [mem_Ioo]
    exact ⟨by linarith, hε⟩
  have hcont : ContinuousAt (ϕ · x₀) 0 := (hderiv 0 h0_mem).continuousAt
  have htend : Tendsto (ϕ · x₀) (𝓝 0) (𝓝 x₀) := by
    have := hcont.tendsto
    rwa [hϕ0_x0] at this
  rw [Metric.tendsto_nhds_nhds] at htend
  obtain ⟨δt, hδt_pos, hδt⟩ := htend (η / 2) (half_pos hη)
  set δt' := min δt ε with hδt'_def
  have hδt'_pos : 0 < δt' := lt_min hδt_pos hε
  have hL_pos : 0 < (L' : ℝ) + 1 := by positivity
  set δx := min r (η / 2 / ((L' : ℝ) + 1)) with hδx_def
  have hδx_pos : 0 < δx := lt_min hr (div_pos (half_pos hη) hL_pos)
  refine ⟨min δt' δx, lt_min hδt'_pos hδx_pos, ?_⟩
  rintro ⟨t, x⟩ htx
  rw [Prod.dist_eq] at htx
  have ht_lt : dist t 0 < δt' := lt_of_le_of_lt (le_max_left (dist t 0) (dist x x₀)) (lt_of_lt_of_le htx (min_le_left _ _))
  have hx_lt : dist x x₀ < δx := lt_of_le_of_lt (le_max_right (dist t 0) (dist x x₀)) (lt_of_lt_of_le htx (min_le_right _ _))
  rw [Real.dist_0_eq_abs] at ht_lt
  have ht_mem_Icc : t ∈ Icc (-ε) ε := by
    rw [mem_Icc]
    have ht_le_ε : |t| ≤ ε := le_of_lt (lt_of_lt_of_le ht_lt (min_le_right _ _))
    rw [abs_le] at ht_le_ε
    exact ht_le_ε
  have hx_mem : x ∈ closedBall x₀ r := by
    rw [Metric.mem_closedBall]
    exact le_of_lt (lt_of_lt_of_le hx_lt (min_le_left _ _))
  have hx0_mem : x₀ ∈ closedBall x₀ r := mem_closedBall_self (le_of_lt hr)
  have hlip_apply := (hlip t ht_mem_Icc).dist_le_mul x hx_mem x₀ hx0_mem
  have ht_dist : dist (ϕ t x₀) x₀ < η / 2 := by
    apply hδt
    rw [Real.dist_0_eq_abs]
    exact lt_of_lt_of_le ht_lt (min_le_left _ _)
  calc
    dist (ϕ t x) x₀ ≤ dist (ϕ t x) (ϕ t x₀) + dist (ϕ t x₀) x₀ := dist_triangle _ _ _
    _ ≤ (L' : ℝ) * dist x x₀ + dist (ϕ t x₀) x₀ := by
      gcongr
    _ < (L' : ℝ) * (η / 2 / ((L' : ℝ) + 1)) + η / 2 := by
      have h1 : dist x x₀ < η / 2 / ((L' : ℝ) + 1) := lt_of_lt_of_le hx_lt (min_le_right r _)
      by_cases hL0 : (L' : ℝ) = 0
      · simp [hL0, ht_dist]
      · have hL_pos' : 0 < (L' : ℝ) := lt_of_le_of_ne (NNReal.coe_nonneg L') (Ne.symm hL0)
        have h_mul := (mul_lt_mul_iff_of_pos_left hL_pos').mpr h1
        exact add_lt_add_of_le_of_lt (le_of_lt h_mul) ht_dist
    _ ≤ η / 2 + η / 2 := by
      gcongr
      have h1 : (L' : ℝ) ≤ (L' : ℝ) + 1 := by linarith
      have h2 : 0 ≤ η / 2 / ((L' : ℝ) + 1) := by positivity
      calc
        (L' : ℝ) * (η / 2 / ((L' : ℝ) + 1)) ≤ ((L' : ℝ) + 1) * (η / 2 / ((L' : ℝ) + 1)) := by
          gcongr
        _ = η / 2 := mul_div_cancel₀ (η / 2) (ne_of_gt hL_pos)
    _ = η := add_halves η

lemma flow_mvt_time {ϕ : ℝ → X → X} {x₀ : X} {ε r : ℝ}
    {f : X → X} (hderiv : ∀ t ∈ Ioo (-ε) ε, ∀ x ∈ closedBall x₀ r, HasDerivAt (ϕ · x) (f (ϕ t x)) t)
    {y : X} (hy : y ∈ closedBall x₀ r) {s t : ℝ}
    (h_sub : uIcc s t ⊆ Ioo (-ε) ε)
    {η : ℝ} (hη : ∀ τ ∈ uIcc s t, ‖f (ϕ τ y) - f x₀‖ ≤ η) :
    ‖ϕ t y - ϕ s y - (t - s) • f x₀‖ ≤ η * |t - s| := by
  let g : ℝ → X := fun τ ↦ ϕ τ y - τ • f x₀
  have hg_deriv : ∀ τ ∈ uIcc s t, HasDerivWithinAt g (f (ϕ τ y) - f x₀) (uIcc s t) τ := by
    intro τ hτ
    have hτ_Ioo : τ ∈ Ioo (-ε) ε := h_sub hτ
    have hd1 : HasDerivAt (ϕ · y) (f (ϕ τ y)) τ := hderiv τ hτ_Ioo y hy
    have hd2 : HasDerivAt (fun u : ℝ ↦ u • f x₀) (f x₀) τ := by
      simpa using (hasDerivAt_id τ).smul_const (f x₀)
    exact (hd1.sub hd2).hasDerivWithinAt
  have h_mvi := (convex_uIcc s t).norm_image_sub_le_of_norm_hasDerivWithin_le hg_deriv hη
    left_mem_uIcc right_mem_uIcc
  have hg_sub : g t - g s = ϕ t y - ϕ s y - (t - s) • f x₀ := by
    dsimp [g]
    module
  rw [hg_sub] at h_mvi
  rw [Real.norm_eq_abs] at h_mvi
  exact h_mvi

lemma flow_mvt_space {ϕ : ℝ → X → X} {x₀ : X} {ε r : ℝ}
    {f : X → X} (hderiv : ∀ t ∈ Ioo (-ε) ε, ∀ x ∈ closedBall x₀ r, HasDerivAt (ϕ · x) (f (ϕ t x)) t)
    {L' : NNReal} (hlip : ∀ t ∈ Icc (-ε) ε, LipschitzOnWith L' (ϕ t ·) (closedBall x₀ r))
    {K : NNReal} {W : Set X} (hf_lip : LipschitzOnWith K f W)
    {y z : X} (hy : y ∈ closedBall x₀ r) (hz : z ∈ closedBall x₀ r)
    (hϕ0y : ϕ 0 y = y) (hϕ0z : ϕ 0 z = z)
    {s : ℝ} (h_sub : uIcc 0 s ⊆ Ioo (-ε) ε)
    (h_sub_Icc : uIcc 0 s ⊆ Icc (-ε) ε)
    (hW_y : ∀ u ∈ uIcc 0 s, ϕ u y ∈ W)
    (hW_z : ∀ u ∈ uIcc 0 s, ϕ u z ∈ W) :
    ‖ϕ s y - ϕ s z - (y - z)‖ ≤ ((K : ℝ) * (L' : ℝ) * |s|) * ‖y - z‖ := by
  let h : ℝ → X := fun u ↦ ϕ u y - ϕ u z
  have hh_deriv : ∀ u ∈ uIcc 0 s, HasDerivWithinAt h (f (ϕ u y) - f (ϕ u z)) (uIcc 0 s) u := by
    intro u hu
    have hu_Ioo : u ∈ Ioo (-ε) ε := h_sub hu
    have hd1 : HasDerivAt (ϕ · y) (f (ϕ u y)) u := hderiv u hu_Ioo y hy
    have hd2 : HasDerivAt (ϕ · z) (f (ϕ u z)) u := hderiv u hu_Ioo z hz
    exact (hd1.sub hd2).hasDerivWithinAt
  have hbound : ∀ u ∈ uIcc 0 s, ‖f (ϕ u y) - f (ϕ u z)‖ ≤ ((K : ℝ) * (L' : ℝ)) * ‖y - z‖ := by
    intro u hu
    have hu_Icc : u ∈ Icc (-ε) ε := h_sub_Icc hu
    have h2 := (hlip u hu_Icc).dist_le_mul y hy z hz
    have h_le := hf_lip.dist_le_mul (ϕ u y) (hW_y u hu) (ϕ u z) (hW_z u hu)
    rw [dist_eq_norm, dist_eq_norm] at h_le
    rw [dist_eq_norm, dist_eq_norm] at h2
    calc
      ‖f (ϕ u y) - f (ϕ u z)‖ ≤ (K : ℝ) * ‖ϕ u y - ϕ u z‖ := h_le
      _ ≤ (K : ℝ) * ((L' : ℝ) * ‖y - z‖) := by
        gcongr
      _ = ((K : ℝ) * (L' : ℝ)) * ‖y - z‖ := by ring
  have h_mvi := (convex_uIcc 0 s).norm_image_sub_le_of_norm_hasDerivWithin_le hh_deriv hbound
    left_mem_uIcc right_mem_uIcc
  have hh_sub : h s - h 0 = ϕ s y - ϕ s z - (y - z) := by
    dsimp [h]
    rw [hϕ0y, hϕ0z]
  rw [hh_sub] at h_mvi
  rw [Real.norm_eq_abs, sub_zero] at h_mvi
  calc
    ‖ϕ s y - ϕ s z - (y - z)‖ ≤ ((K : ℝ) * (L' : ℝ)) * ‖y - z‖ * |s| := h_mvi
    _ = ((K : ℝ) * (L' : ℝ) * |s|) * ‖y - z‖ := by ring

structure LocalFlowData (f : X → X) (x₀ : X) where
  ε : ℝ
  hε : 0 < ε
  r : ℝ
  hr : 0 < r
  a : ℝ
  ha : 0 < a
  hra : r ≤ a
  L' : NNReal
  K : NNReal
  ϕ : ℝ → X → X
  ϕ_zero : ∀ x ∈ closedBall x₀ r, ϕ 0 x = x
  ϕ_hasDerivAt : ∀ t ∈ Ioo (-ε) ε, ∀ x ∈ closedBall x₀ r, HasDerivAt (ϕ · x) (f (ϕ t x)) t
  ϕ_lipschitz : ∀ t ∈ Icc (-ε) ε, LipschitzOnWith L' (ϕ t ·) (closedBall x₀ r)
  f_lipschitz : LipschitzOnWith K f (closedBall x₀ a)

lemma exists_localFlowData [CompleteSpace X] {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    Nonempty (LocalFlowData f x₀) := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf
  have pl0 := hpl 0
  have h_le := pl0.mul_max_le
  simp only [zero_sub, sub_neg_eq_add, zero_add, sub_zero, max_self] at h_le
  have hr_le_a : (r : ℝ) ≤ (a : ℝ) := by
    have h_nonneg : 0 ≤ (L : ℝ) * ε := by positivity
    linarith
  have ha_pos : 0 < (a : ℝ) := lt_of_lt_of_le hr hr_le_a
  obtain ⟨α, hα, L', hL'⟩ := pl0.exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  have hf_lip : LipschitzOnWith K f (closedBall x₀ (a : ℝ)) := by
    have h0_mem : (0 : ℝ) ∈ Icc (0 - ε) (0 + ε) := by
      rw [mem_Icc]
      constructor <;> linarith
    exact pl0.lipschitzOnWith 0 h0_mem
  refine ⟨⟨ε, hε, r, hr, a, ha_pos, hr_le_a, L', K, fun t x ↦ α x t, ?_, ?_, ?_, hf_lip⟩⟩
  · intro x hx
    exact (hα x hx).1
  · intro t ht x hx
    have ht' : t ∈ Ioo (0 - ε) (0 + ε) := by
      rwa [zero_sub, zero_add]
    have hwithin := (hα x hx).2 t (Ioo_subset_Icc_self ht')
    have hnhds : Icc (0 - ε) (0 + ε) ∈ 𝓝 t := Icc_mem_nhds ht'.1 ht'.2
    exact hwithin.hasDerivAt hnhds
  · intro t ht
    have ht' : t ∈ Icc (0 - ε) (0 + ε) := by
      rwa [zero_sub, zero_add]
    exact hL' t ht'


lemma toSpanSingleton_ker (v : X) (hv : v ≠ 0) :
    (ContinuousLinearMap.toSpanSingleton ℝ v).ker = ⊥ := by
  ext t
  simp only [LinearMap.mem_ker, Submodule.mem_bot, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.toSpanSingleton_apply]
  exact smul_eq_zero_iff_left hv

lemma toSpanSingleton_range (v : X) :
    (ContinuousLinearMap.toSpanSingleton ℝ v).range = Submodule.span ℝ {v} := by
  ext x
  simp only [LinearMap.mem_range, Submodule.mem_span_singleton, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.toSpanSingleton_apply]

/-- A complementary subspace to `ℝ • f x₀` in `X`. -/
noncomputable def flowComplement [FiniteDimensional ℝ X] (v : X) : Submodule ℝ X :=
  (Submodule.exists_isCompl (Submodule.span ℝ {v})).choose

theorem isCompl_flowComplement [FiniteDimensional ℝ X] (v : X) :
    IsCompl (Submodule.span ℝ {v}) (flowComplement v) :=
  (Submodule.exists_isCompl (Submodule.span ℝ {v})).choose_spec

/-- The continuous linear equivalence between `ℝ × flowComplement v` and `X`. -/
noncomputable def flowEquiv [FiniteDimensional ℝ X] (v : X) (hv : v ≠ 0) :
    (ℝ × flowComplement v) ≃L[ℝ] X :=
  ContinuousLinearMap.coprodSubtypeLEquivOfIsCompl
    (ContinuousLinearMap.toSpanSingleton ℝ v)
    (by rw [toSpanSingleton_range]; exact isCompl_flowComplement v)
    (toSpanSingleton_ker v hv)


@[simp] theorem flowEquiv_apply [FiniteDimensional ℝ X] (v : X) (hv : v ≠ 0)
    (p : ℝ × flowComplement v) :
    flowEquiv v hv p = p.1 • v + (p.2 : X) := by
  dsimp [flowEquiv, ContinuousLinearMap.coprodSubtypeLEquivOfIsCompl]
  simp [ContinuousLinearMap.toSpanSingleton_apply]


lemma tendsto_flow_f [CompleteSpace X] {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀)
    (data : LocalFlowData f x₀) :
    Tendsto (fun p : ℝ × X ↦ f (data.ϕ p.1 p.2)) (𝓝 (0, x₀)) (𝓝 (f x₀)) := by
  have h1 : Tendsto (fun p : ℝ × X ↦ data.ϕ p.1 p.2) (𝓝 (0, x₀)) (𝓝 x₀) :=
    tendsto_flow_aux data.hε data.hr data.ϕ_zero (fun t ht ↦ data.ϕ_hasDerivAt t ht x₀
      (mem_closedBall_self (le_of_lt data.hr))) data.ϕ_lipschitz
  exact hf.continuousAt.tendsto.comp h1


noncomputable def getLocalFlowData [CompleteSpace X] {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    LocalFlowData f x₀ :=
  Classical.choice (exists_localFlowData hf)

/-- The local flow of `f` near `(0, x₀)` obtained via Picard-Lindelöf. -/
noncomputable def localFlow [CompleteSpace X] {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    ℝ → X → X :=
  (getLocalFlowData hf).ϕ


lemma mem_ball_zero_of_mem_uIcc {s t : ℝ} {δ : ℝ} (hs : s ∈ ball (0 : ℝ) δ) (ht : t ∈ ball (0 : ℝ) δ)
    {τ : ℝ} (hτ : τ ∈ uIcc s t) : τ ∈ ball (0 : ℝ) δ := by
  rw [Metric.mem_ball, Real.dist_0_eq_abs] at hs ht ⊢
  rw [uIcc, mem_Icc] at hτ
  have hs' : -δ < s ∧ s < δ := abs_lt.mp hs
  have ht' : -δ < t ∧ t < δ := abs_lt.mp ht
  have hmin : -δ < min s t := lt_min hs'.1 ht'.1
  have hmax : max s t < δ := max_lt hs'.2 ht'.2
  rw [abs_lt]
  exact ⟨lt_of_lt_of_le hmin hτ.1, lt_of_le_of_lt hτ.2 hmax⟩

/-- The strict derivative of the local flow at `(0, x₀)`, via integral remainders. -/
theorem flowStrictFDerivAt [CompleteSpace X] {f : X → X} {x₀ : X}
    (hf : ContDiffAt ℝ 1 f x₀) :
    HasStrictFDerivAt (fun p : ℝ × X ↦ localFlow hf p.1 p.2)
      ((ContinuousLinearMap.snd ℝ ℝ X) + ((ContinuousLinearMap.fst ℝ ℝ X).smulRight (f x₀))) (0, x₀) := by
  set data := getLocalFlowData hf with hdata
  have hloc : (fun p : ℝ × X ↦ localFlow hf p.1 p.2)
      = (fun p : ℝ × X ↦ data.ϕ p.1 p.2) := rfl
  rw [hloc]
  set F' : ℝ × X →L[ℝ] X := (ContinuousLinearMap.snd ℝ ℝ X) +
    ((ContinuousLinearMap.fst ℝ ℝ X).smulRight (f x₀)) with hF'def
  have hF'apply : ∀ d : ℝ × X, F' d = d.2 + d.1 • f x₀ := by
    intro d
    simp [hF'def]
  have hfc : ContinuousAt f x₀ := hf.continuousAt
  have hflow : Tendsto (fun q : ℝ × X ↦ data.ϕ q.1 q.2) (𝓝 (0, x₀)) (𝓝 x₀) :=
    tendsto_flow_aux data.hε data.hr data.ϕ_zero
      (fun t ht ↦ data.ϕ_hasDerivAt t ht x₀
        (mem_closedBall_self (le_of_lt data.hr)))
      data.ϕ_lipschitz
  rw [Metric.continuousAt_iff] at hfc
  rw [Metric.tendsto_nhds_nhds] at hflow
  apply HasStrictFDerivAt.of_isLittleO
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δf, hδf_pos, hδf⟩ := hfc (c / 2) (half_pos hc)
  set ρ := min δf (min data.r data.a) with hρdef
  have hρ_pos : 0 < ρ := lt_min hδf_pos (lt_min data.hr data.ha)
  have hρ_f : ρ ≤ δf := min_le_left _ _
  have hρ_r : ρ ≤ data.r := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ_a : ρ ≤ data.a := le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨δϕ, hδϕ_pos, hδϕ⟩ := hflow ρ hρ_pos
  set M : ℝ := (data.K : ℝ) * (data.L' : ℝ) + 1 with hMdef
  have hM_pos : 0 < M := by simp only [hMdef]; linarith [mul_nonneg (NNReal.coe_nonneg data.K) (NNReal.coe_nonneg data.L')]
  set δ := min δϕ (min data.ε (min data.r ((c / 2) / M))) with hδdef
  have hδ_pos : 0 < δ :=
    lt_min hδϕ_pos (lt_min data.hε (lt_min data.hr (div_pos (half_pos hc) hM_pos)))
  have hδ_ϕ : δ ≤ δϕ := min_le_left _ _
  have hδ_ε : δ ≤ data.ε := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ_r : δ ≤ data.r :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ_M : δ ≤ (c / 2) / M :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine Metric.eventually_nhds_iff_ball.mpr ⟨δ, hδ_pos, ?_⟩
  rintro ⟨⟨t, y⟩, ⟨s, z⟩⟩ hp
  rw [mem_ball, Prod.dist_eq] at hp
  have h1 : dist (t, y) (0, x₀) < δ := lt_of_le_of_lt (le_max_left _ _) hp
  have h2 : dist (s, z) (0, x₀) < δ := lt_of_le_of_lt (le_max_right _ _) hp
  rw [Prod.dist_eq] at h1 h2
  have ht0 : dist t 0 < δ := lt_of_le_of_lt (le_max_left _ _) h1
  have hy0 : dist y x₀ < δ := lt_of_le_of_lt (le_max_right _ _) h1
  have hs0 : dist s 0 < δ := lt_of_le_of_lt (le_max_left _ _) h2
  have hz0 : dist z x₀ < δ := lt_of_le_of_lt (le_max_right _ _) h2
  rw [Real.dist_0_eq_abs] at ht0 hs0
  rw [dist_eq_norm] at hy0 hz0
  have hy0d : dist y x₀ < δ := by rwa [dist_eq_norm]
  have hz0d : dist z x₀ < δ := by rwa [dist_eq_norm]
  have hy_mem : y ∈ closedBall x₀ data.r :=
    mem_closedBall.mpr (le_of_lt (lt_of_lt_of_le hy0d hδ_r))
  have hz_mem : z ∈ closedBall x₀ data.r :=
    mem_closedBall.mpr (le_of_lt (lt_of_lt_of_le hz0d hδ_r))
  have ht_ball : t ∈ ball (0 : ℝ) δ := by rwa [mem_ball, Real.dist_0_eq_abs]
  have hs_ball : s ∈ ball (0 : ℝ) δ := by rwa [mem_ball, Real.dist_0_eq_abs]
  have h0_ball : (0 : ℝ) ∈ ball (0 : ℝ) δ := by
    rw [mem_ball, Real.dist_0_eq_abs, abs_zero]; exact hδ_pos
  have hts_le : |t - s| ≤ ‖((t, y) - (s, z) : ℝ × X)‖ := by
    have h := norm_fst_le ((t, y) - (s, z) : ℝ × X)
    rwa [Prod.fst_sub, Real.norm_eq_abs] at h
  have hyz_le : ‖y - z‖ ≤ ‖((t, y) - (s, z) : ℝ × X)‖ := by
    have h := norm_snd_le ((t, y) - (s, z) : ℝ × X)
    rwa [Prod.snd_sub] at h
  have herr : data.ϕ t y - data.ϕ s z - F' ((t, y) - (s, z))
      = (data.ϕ t y - data.ϕ s y - (t - s) • f x₀)
        + (data.ϕ s y - data.ϕ s z - (y - z)) := by
    rw [hF'apply, Prod.fst_sub, Prod.snd_sub]
    abel
  have hsub_st : uIcc s t ⊆ Ioo (-data.ε) data.ε := by
    intro τ hτ
    have hτb : τ ∈ ball (0 : ℝ) δ := mem_ball_zero_of_mem_uIcc hs_ball ht_ball hτ
    rw [mem_ball, Real.dist_0_eq_abs] at hτb
    have habs : |τ| < data.ε := lt_of_lt_of_le hτb hδ_ε
    rw [mem_Ioo]
    exact abs_lt.mp habs
  have hbound_time : ∀ τ ∈ uIcc s t, ‖f (data.ϕ τ y) - f x₀‖ ≤ c / 2 := by
    intro τ hτ
    have hτb : τ ∈ ball (0 : ℝ) δ := mem_ball_zero_of_mem_uIcc hs_ball ht_ball hτ
    have hτδ : dist τ 0 < δϕ := lt_of_lt_of_le (mem_ball.mp hτb) hδ_ϕ
    have hyδ : dist y x₀ < δϕ := lt_of_lt_of_le hy0d hδ_ϕ
    have hq : dist (τ, y) (0, x₀) < δϕ := by
      rw [Prod.dist_eq]
      exact max_lt hτδ hyδ
    have hϕρ := hδϕ hq
    have hϕδf : dist (data.ϕ τ y) x₀ < δf := lt_of_lt_of_le hϕρ hρ_f
    have hlt := hδf hϕδf
    rw [dist_eq_norm] at hlt
    exact le_of_lt hlt
  have hE1 : ‖data.ϕ t y - data.ϕ s y - (t - s) • f x₀‖ ≤ (c / 2) * |t - s| :=
    flow_mvt_time (fun τ hτ x hx ↦ data.ϕ_hasDerivAt τ hτ x hx) hy_mem hsub_st
      hbound_time
  have hE1' : ‖data.ϕ t y - data.ϕ s y - (t - s) • f x₀‖
      ≤ (c / 2) * ‖((t, y) - (s, z) : ℝ × X)‖ :=
    le_trans hE1 (mul_le_mul_of_nonneg_left hts_le (le_of_lt (half_pos hc)))
  have hsub_0s_Ioo : uIcc 0 s ⊆ Ioo (-data.ε) data.ε := by
    intro u hu
    have hub : u ∈ ball (0 : ℝ) δ := mem_ball_zero_of_mem_uIcc h0_ball hs_ball hu
    rw [mem_ball, Real.dist_0_eq_abs] at hub
    have habs : |u| < data.ε := lt_of_lt_of_le hub hδ_ε
    rw [mem_Ioo]
    exact abs_lt.mp habs
  have hsub_0s_Icc : uIcc 0 s ⊆ Icc (-data.ε) data.ε :=
    fun u hu ↦ Ioo_subset_Icc_self (hsub_0s_Ioo hu)
  have hWy : ∀ u ∈ uIcc 0 s, data.ϕ u y ∈ closedBall x₀ data.a := by
    intro u hu
    have hub : u ∈ ball (0 : ℝ) δ := mem_ball_zero_of_mem_uIcc h0_ball hs_ball hu
    have huδ : dist u 0 < δϕ := lt_of_lt_of_le (mem_ball.mp hub) hδ_ϕ
    have hyδ : dist y x₀ < δϕ := lt_of_lt_of_le hy0d hδ_ϕ
    have hq : dist (u, y) (0, x₀) < δϕ := by
      rw [Prod.dist_eq]
      exact max_lt huδ hyδ
    have hϕρ := hδϕ hq
    have hlt : dist (data.ϕ u y) x₀ < data.a := lt_of_lt_of_le hϕρ hρ_a
    exact mem_closedBall.mpr (le_of_lt hlt)
  have hWz : ∀ u ∈ uIcc 0 s, data.ϕ u z ∈ closedBall x₀ data.a := by
    intro u hu
    have hub : u ∈ ball (0 : ℝ) δ := mem_ball_zero_of_mem_uIcc h0_ball hs_ball hu
    have huδ : dist u 0 < δϕ := lt_of_lt_of_le (mem_ball.mp hub) hδ_ϕ
    have hzδ : dist z x₀ < δϕ := lt_of_lt_of_le hz0d hδ_ϕ
    have hq : dist (u, z) (0, x₀) < δϕ := by
      rw [Prod.dist_eq]
      exact max_lt huδ hzδ
    have hϕρ := hδϕ hq
    have hlt : dist (data.ϕ u z) x₀ < data.a := lt_of_lt_of_le hϕρ hρ_a
    exact mem_closedBall.mpr (le_of_lt hlt)
  have hϕ0y : data.ϕ 0 y = y := data.ϕ_zero y hy_mem
  have hϕ0z : data.ϕ 0 z = z := data.ϕ_zero z hz_mem
  have hE2 := flow_mvt_space (fun τ hτ x hx ↦ data.ϕ_hasDerivAt τ hτ x hx)
    data.ϕ_lipschitz data.f_lipschitz hy_mem hz_mem hϕ0y hϕ0z hsub_0s_Ioo
    hsub_0s_Icc hWy hWz
  have hKs : (data.K : ℝ) * (data.L' : ℝ) * |s| ≤ c / 2 := by
    have hsM : |s| ≤ (c / 2) / M := le_of_lt (lt_of_lt_of_le hs0 hδ_M)
    calc (data.K : ℝ) * (data.L' : ℝ) * |s| ≤ M * |s| := by
            gcongr
            simp only [hMdef]
            linarith [mul_nonneg (NNReal.coe_nonneg data.K) (NNReal.coe_nonneg data.L')]
      _ ≤ M * ((c / 2) / M) := mul_le_mul_of_nonneg_left hsM (le_of_lt hM_pos)
      _ = c / 2 := mul_div_cancel₀ _ (ne_of_gt hM_pos)
  have hE2' : ‖data.ϕ s y - data.ϕ s z - (y - z)‖
      ≤ (c / 2) * ‖((t, y) - (s, z) : ℝ × X)‖ := by
    calc ‖data.ϕ s y - data.ϕ s z - (y - z)‖
        ≤ ((data.K : ℝ) * (data.L' : ℝ) * |s|) * ‖y - z‖ := hE2
      _ ≤ (c / 2) * ‖y - z‖ := by gcongr
      _ ≤ (c / 2) * ‖((t, y) - (s, z) : ℝ × X)‖ := by gcongr
  have hEnorm : ‖data.ϕ t y - data.ϕ s z - F' ((t, y) - (s, z))‖
      ≤ c * ‖((t, y) - (s, z) : ℝ × X)‖ := by
    rw [herr]
    calc ‖(data.ϕ t y - data.ϕ s y - (t - s) • f x₀)
            + (data.ϕ s y - data.ϕ s z - (y - z))‖
        ≤ ‖data.ϕ t y - data.ϕ s y - (t - s) • f x₀‖
            + ‖data.ϕ s y - data.ϕ s z - (y - z)‖ := norm_add_le _ _
      _ ≤ (c / 2) * ‖((t, y) - (s, z) : ℝ × X)‖
            + (c / 2) * ‖((t, y) - (s, z) : ℝ × X)‖ := by gcongr
      _ = c * ‖((t, y) - (s, z) : ℝ × X)‖ := by ring
  simpa using hEnorm


/-- The rectifying map `Φ (z₁, z') = localFlow z₁ (x₀ + ι z')`. -/
noncomputable def rectifyingChartΦ [FiniteDimensional ℝ X]
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    (ℝ × ↥(flowComplement (f x₀))) → X :=
  fun p ↦ localFlow hf p.1 (x₀ + (flowComplement (f x₀)).subtypeL p.2)

theorem rectifyingChartStrict [CompleteSpace X] [FiniteDimensional ℝ X]
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) (hv : f x₀ ≠ 0) :
    HasStrictFDerivAt (rectifyingChartΦ hf)
      (↑(flowEquiv (f x₀) hv) : (ℝ × ↥(flowComplement (f x₀))) →L[ℝ] X) 0 := by
  let C := flowComplement (f x₀)
  let ι : ↥C →L[ℝ] X := C.subtypeL
  let A : (ℝ × ↥C) → ℝ × X := fun p ↦ (p.1, x₀ + ι p.2)
  let A' : (ℝ × ↥C) →L[ℝ] (ℝ × X) := (ContinuousLinearMap.fst ℝ ℝ ↥C).prod
    (ι.comp (ContinuousLinearMap.snd ℝ ℝ ↥C))
  let F : ℝ × X → X := fun q ↦ localFlow hf q.1 q.2
  let F' : ℝ × X →L[ℝ] X := (ContinuousLinearMap.snd ℝ ℝ X) +
    ((ContinuousLinearMap.fst ℝ ℝ X).smulRight (f x₀))
  have h1 : HasStrictFDerivAt (fun p : ℝ × ↥C ↦ p.1)
      (ContinuousLinearMap.fst ℝ ℝ ↥C) 0 :=
    (ContinuousLinearMap.fst ℝ ℝ ↥C).hasStrictFDerivAt
  have h2lin : HasStrictFDerivAt (fun p : ℝ × ↥C ↦ ι p.2)
      (ι.comp (ContinuousLinearMap.snd ℝ ℝ ↥C)) 0 :=
    (ι.comp (ContinuousLinearMap.snd ℝ ℝ ↥C)).hasStrictFDerivAt
  have h2 : HasStrictFDerivAt (fun p : ℝ × ↥C ↦ x₀ + ι p.2)
      (ι.comp (ContinuousLinearMap.snd ℝ ℝ ↥C)) 0 :=
    h2lin.const_add x₀
  have hA : HasStrictFDerivAt A A' 0 := h1.prodMk h2
  have hA0 : A 0 = (0, x₀) := by simp [A]
  have hF0 : HasStrictFDerivAt F F' (A 0) := hA0 ▸ flowStrictFDerivAt hf
  have hcomp : HasStrictFDerivAt (fun p ↦ F (A p)) (F'.comp A') 0 :=
    hF0.comp _ hA
  have hDeq : F'.comp A'
      = (↑(flowEquiv (f x₀) hv) : (ℝ × ↥(flowComplement (f x₀))) →L[ℝ] X) := by
    apply ContinuousLinearMap.ext
    rintro ⟨a, w⟩
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.smulRight_apply, add_apply,
      ContinuousLinearEquiv.coe_coe, A', F']
    rw [flowEquiv_apply]
    exact add_comm _ _
  have hΦeq : (fun p ↦ F (A p)) = rectifyingChartΦ hf := rfl
  rw [hΦeq, hDeq] at hcomp
  exact hcomp

/-- The rectifying chart as an `OpenPartialHomeomorph`, via the inverse function theorem. -/
noncomputable def rectifyingChart [CompleteSpace X] [FiniteDimensional ℝ X]
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) (hv : f x₀ ≠ 0) :
    OpenPartialHomeomorph (ℝ × ↥(flowComplement (f x₀))) X :=
  (rectifyingChartStrict hf hv).toOpenPartialHomeomorph _

theorem rectifyingChart_rectifies [CompleteSpace X] [FiniteDimensional ℝ X]
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) (hv : f x₀ ≠ 0)
    (z' : ↥(flowComplement (f x₀))) (t : ℝ)
    (ht : t ∈ Ioo (-(getLocalFlowData hf).ε) (getLocalFlowData hf).ε)
    (hz : x₀ + (flowComplement (f x₀)).subtypeL z'
      ∈ closedBall x₀ (getLocalFlowData hf).r)
    (_hmem : ((t, z') : ℝ × ↥(flowComplement (f x₀))) ∈ (rectifyingChart hf hv).source) :
    HasDerivAt (fun s ↦ (rectifyingChart hf hv) (s, z'))
      (f ((rectifyingChart hf hv) (t, z'))) t := by
  have hcoe : ⇑(rectifyingChart hf hv) = rectifyingChartΦ hf :=
    HasStrictFDerivAt.toOpenPartialHomeomorph_coe (rectifyingChartStrict hf hv)
  rw [hcoe]
  show HasDerivAt (fun s ↦ localFlow hf s (x₀ + (flowComplement (f x₀)).subtypeL z'))
    (f (localFlow hf t (x₀ + (flowComplement (f x₀)).subtypeL z'))) t
  exact (getLocalFlowData hf).ϕ_hasDerivAt t ht _ hz
