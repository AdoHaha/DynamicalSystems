/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.SlidingMode.Basic
public import DynamicalSystems.Control.SlidingMode.Relay
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Basic.Real.Sign
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.UniformSpace.UniformConvergence

/-! # Boundary-layer regularization of the sliding-mode relay

This file records the boundary-layer regularization of the discontinuous relay
feedback of G. Bartolini, E. Punta and T. Zolezzi, *Regularization of Second
Order Sliding Mode Control Systems*, Chapter 1 in G. Bartolini, L. Fridman,
A. Pisano and E. Usai (eds.), *Modern Sliding Mode Control Theory: New
Perspectives and Applications*, LNCIS 375, Springer 2008 (printed pp. 3–21,
PDF pp. 19–37).

The discontinuous relay `relay k s = k * Real.sign s` of
`DynamicalSystems.Control.SlidingMode.Relay` is replaced, inside the boundary
layer `{|s| < ε}`, by the saturated relay
`boundaryLayerRelay k ε s = k * unitSat (s / ε)`, where
`unitSat s = max (-1) (min 1 s)` clamps its argument into `[-1, 1]`. The
saturation `unitSat` is the metric projection of `ℝ` onto the interval
`[-1, 1]`: it is `1`-Lipschitz and hence continuous. Away from the switching
level the regularized relay is *exactly* the ideal relay once `ε` is smaller than
`|s|`, and it converges to the ideal relay pointwise for every `s`, including
`s = 0`. The regularized values always lie in the Filippov convexification
`[-k, k] = filippovSet (relay k) 0` at the switching level, which is the bridge
to the discontinuous-feedback semantics of
`DynamicalSystems.Control.SlidingMode.Filippov`.

## Main definitions

* `unitSat s`: the scalar saturation `max (-1) (min 1 s)`, the projection of `ℝ`
  onto `Set.Icc (-1) 1`.
* `boundaryLayerRelay k ε s`: the boundary-layer regularized relay
  `k * unitSat (s / ε)`.

## Main statements

* `unitSat_of_one_le`, `unitSat_of_le_neg_one`, `unitSat_of_mem_Icc`: the three
  value rules of the saturation, `unitSat_zero`: `unitSat 0 = 0`, and
  `abs_unitSat_le_one`, `unitSat_neg`: the range and the odd symmetry.
* `lipschitzWith_unitSat`, `continuous_unitSat`: `unitSat` is `1`-Lipschitz,
  hence continuous.
* `abs_boundaryLayerRelay_le`: the regularized relay is bounded by `|k|`.
* `tendsto_sat_div_sign`: pointwise convergence `unitSat (s / ε) → Real.sign s`
  along `𝓝[>] 0`, for every `s` (the family is eventually constant).
* `tendsto_boundaryLayerRelay`: pointwise convergence of the regularized relay to
  the ideal relay.
* `unitSat_div_eq_sign_of_abs_ge`: outside the layer `{|s| ≥ δ}` the saturation
  agrees with `Real.sign s` exactly, for `0 < ε ≤ δ`.
* `boundaryLayerRelay_mem_filippovSet`: the regularized relay values lie in
  `filippovSet (relay k) 0 = Set.Icc (-k) k`.

On top of the boundary-layer regularization the file records the *first-order
approximability* transfer theorem of the same chapter: conditional stability
`‖x'ε - y'‖ ≤ K ‖xε - y‖ + L |σ(xε)|` together with uniform decay `σ(xε) ⇉ 0` of
the sliding variable and matching initial conditions forces `xε ⇉ y` on `[0, T]`.
The quantitative input is Mathlib's Grönwall inequality (`gronwallBound`),
packaged as the trajectory-error estimate `trajectory_error_le_gronwallBound`; the
abstract property itself is `IsFirstOrderApproximable`.

## Main statements (approximability)

* `trajectory_error_le_gronwallBound`: the Grönwall trajectory-error estimate on
  `[0, T]`.
* `tendstoUniformlyOn_of_conditional_stability`: conditional stability plus
  `σ(xε) ⇉ 0` gives uniform convergence `xε ⇉ y`.
* `tendstoUniformlyOn_of_boundaryLayer`: the boundary-layer closed-loop corollary
  `|σ(xε)| ≤ ε`.
* `isFirstOrderApproximable_of_conditional_stability`: the conditional-stability
  class of trajectory families is first-order approximable.
* `IsFirstOrderApproximable`: the abstract first-order approximability predicate
  for an admissible family class (printed p. 5).
-/

@[expose] public section

open Filter Set
open scoped Topology

/-! ### The scalar saturation -/

/-- The scalar saturation `unitSat s = max (-1) (min 1 s)`: the metric projection
of `ℝ` onto the interval `Set.Icc (-1) 1`. It clamps every real number into
`[-1, 1]` and is the identity there. -/
def unitSat (s : ℝ) : ℝ := max (-1) (min 1 s)

/-- The saturation of a number at least `1` is `1`. -/
theorem unitSat_of_one_le {s : ℝ} (h : 1 ≤ s) : unitSat s = 1 := by
  simp [unitSat, min_eq_left h]

/-- The saturation of a number at most `-1` is `-1`. -/
theorem unitSat_of_le_neg_one {s : ℝ} (h : s ≤ -1) : unitSat s = -1 := by
  have h1 : s ≤ 1 := by linarith
  simp [unitSat, min_eq_right h1, max_eq_left h]

/-- The saturation is the identity on `Set.Icc (-1) 1`. -/
theorem unitSat_of_mem_Icc {s : ℝ} (h : s ∈ Set.Icc (-1 : ℝ) 1) : unitSat s = s := by
  simp [unitSat, min_eq_right h.2, max_eq_right h.1]

/-- `unitSat 0 = 0`. -/
@[simp] theorem unitSat_zero : unitSat 0 = 0 :=
  unitSat_of_mem_Icc ⟨by norm_num, by norm_num⟩

/-- The saturation takes values in `[-1, 1]`. -/
theorem abs_unitSat_le_one (s : ℝ) : |unitSat s| ≤ 1 := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

/-- The saturation is odd: `unitSat (-s) = -unitSat s`. -/
theorem unitSat_neg (s : ℝ) : unitSat (-s) = -unitSat s := by
  rcases le_total s (-1) with h | h
  · rw [unitSat_of_le_neg_one h, unitSat_of_one_le (by linarith), neg_neg]
  rcases le_total s 1 with h1 | h1
  · rw [unitSat_of_mem_Icc ⟨h, h1⟩, unitSat_of_mem_Icc ⟨by linarith, by linarith⟩]
  · rw [unitSat_of_one_le h1, unitSat_of_le_neg_one (by linarith)]

/-- The saturation is `1`-Lipschitz, being the metric projection onto
`Set.Icc (-1) 1`. -/
theorem lipschitzWith_unitSat : LipschitzWith 1 unitSat :=
  (LipschitzWith.id.const_min (1 : ℝ)).const_max (-1)

/-- The saturation is continuous. -/
theorem continuous_unitSat : Continuous unitSat :=
  lipschitzWith_unitSat.continuous

/-! ### Boundary-layer regularization of the relay -/

/-- The boundary-layer regularized relay
`boundaryLayerRelay k ε s = k * unitSat (s / ε)`. Inside the layer `{|s| < ε}` it
interpolates linearly between `-k` and `k`, and outside it agrees with the ideal
relay `relay k s = k * Real.sign s`. -/
noncomputable def boundaryLayerRelay (k ε : ℝ) (s : ℝ) : ℝ := k * unitSat (s / ε)

/-- The pointwise unfolding of `boundaryLayerRelay` (a `simp` lemma). -/
@[simp] theorem boundaryLayerRelay_apply (k ε s : ℝ) :
    boundaryLayerRelay k ε s = k * unitSat (s / ε) := rfl

/-- The regularized relay is bounded in magnitude by `|k|`. -/
theorem abs_boundaryLayerRelay_le (k ε s : ℝ) : |boundaryLayerRelay k ε s| ≤ |k| := by
  rw [boundaryLayerRelay_apply, abs_mul]
  calc |k| * |unitSat (s / ε)| ≤ |k| * 1 :=
        mul_le_mul_of_nonneg_left (abs_unitSat_le_one _) (abs_nonneg k)
    _ = |k| := mul_one _

/-- Pointwise convergence of the saturation `unitSat (s / ε)` to `Real.sign s`
along `𝓝[>] 0`, for **every** `s` including `s = 0`: the family is eventually
constant with value `Real.sign s`. -/
theorem tendsto_sat_div_sign (s : ℝ) :
    Tendsto (fun ε : ℝ ↦ unitSat (s / ε)) (𝓝[>] 0) (𝓝 (Real.sign s)) := by
  rcases lt_trichotomy s 0 with hneg | rfl | hpos
  · have heq : (fun ε : ℝ ↦ unitSat (s / ε)) =ᶠ[𝓝[>] 0] (fun _ ↦ Real.sign s) := by
      change ∀ᶠ ε in 𝓝[>] (0 : ℝ), unitSat (s / ε) = Real.sign s
      rw [eventually_nhdsWithin_iff]
      filter_upwards [isOpen_Iio.mem_nhds (neg_pos.mpr hneg)] with ε hε hεpos
      rw [Set.mem_Iio] at hε
      rw [Set.mem_Ioi] at hεpos
      have hdiv : s / ε ≤ -1 := by
        rw [div_le_iff₀ hεpos]
        linarith
      rw [unitSat_of_le_neg_one hdiv, Real.sign_of_neg hneg]
    exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  · have heq : (fun ε : ℝ ↦ unitSat ((0 : ℝ) / ε)) =ᶠ[𝓝[>] 0]
        (fun _ ↦ Real.sign (0 : ℝ)) := by
      change ∀ᶠ ε in 𝓝[>] (0 : ℝ), unitSat ((0 : ℝ) / ε) = Real.sign 0
      filter_upwards with ε
      rw [zero_div, unitSat_zero, Real.sign_zero]
    exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  · have heq : (fun ε : ℝ ↦ unitSat (s / ε)) =ᶠ[𝓝[>] 0] (fun _ ↦ Real.sign s) := by
      change ∀ᶠ ε in 𝓝[>] (0 : ℝ), unitSat (s / ε) = Real.sign s
      rw [eventually_nhdsWithin_iff]
      filter_upwards [isOpen_Iio.mem_nhds hpos] with ε hε hεpos
      rw [Set.mem_Iio] at hε
      rw [Set.mem_Ioi] at hεpos
      have hdiv : 1 ≤ s / ε := by
        rw [le_div_iff₀ hεpos]
        linarith
      rw [unitSat_of_one_le hdiv, Real.sign_of_pos hpos]
    exact Filter.Tendsto.congr' heq.symm tendsto_const_nhds

/-- Pointwise convergence of the regularized relay to the ideal relay `relay k s`
along `𝓝[>] 0`, for every `s`. -/
theorem tendsto_boundaryLayerRelay (k s : ℝ) :
    Tendsto (fun ε : ℝ ↦ boundaryLayerRelay k ε s) (𝓝[>] 0) (𝓝 (relay k s)) := by
  simp only [boundaryLayerRelay_apply, relay_apply]
  exact (tendsto_sat_div_sign s).const_mul k

/-- Outside the boundary layer `{|s| ≥ δ}` the saturation `unitSat (s / ε)` equals
`Real.sign s` exactly, for every `0 < ε ≤ δ`. -/
theorem unitSat_div_eq_sign_of_abs_ge {δ : ℝ} (hδ : 0 < δ) {ε : ℝ} (hε0 : 0 < ε)
    (hεδ : ε ≤ δ) {s : ℝ} (hs : δ ≤ |s|) : unitSat (s / ε) = Real.sign s := by
  rcases le_total 0 s with hspos | hsneg
  · have hs' : δ ≤ s := by rwa [abs_of_nonneg hspos] at hs
    have h1 : 1 ≤ s / ε := by
      rw [le_div_iff₀ hε0, one_mul]
      exact hεδ.trans hs'
    rw [unitSat_of_one_le h1, Real.sign_of_pos (hδ.trans_le hs')]
  · have hs' : δ ≤ -s := by rwa [abs_of_nonpos hsneg] at hs
    have h1 : s / ε ≤ -1 := by
      rw [div_le_iff₀ hε0]
      linarith
    rw [unitSat_of_le_neg_one h1, Real.sign_of_neg (by linarith)]

/-- **S6 bridge.** The regularized relay value always lies in the Filippov
convexification of the ideal relay at the switching level,
`filippovSet (relay k) 0 = Set.Icc (-k) k`, for every `ε`. The previously present
hypothesis `0 < ε` was unused and has been removed. -/
theorem boundaryLayerRelay_mem_filippovSet (k ε s : ℝ) (hk : 0 ≤ k) :
    boundaryLayerRelay k ε s ∈ filippovSet (relay k) 0 := by
  rcases eq_or_lt_of_le hk with hk0 | hkpos
  · subst hk0
    rw [show relay 0 = fun _ : ℝ ↦ (0 : ℝ) from by funext t; simp [relay_apply],
      filippovSet_of_continuous continuous_const]
    simp [boundaryLayerRelay_apply]
  · rw [filippovSet_relay_zero hkpos, Set.mem_Icc, boundaryLayerRelay_apply]
    have hsat := abs_unitSat_le_one (s / ε)
    rw [abs_le] at hsat
    constructor <;> nlinarith [hsat.1, hsat.2]

/-! ### First-order approximability

The *first-order approximability property* of Chapter 1 asks that an ideal
sliding state `y` be the unique uniform limit on `[0, T]` of every family of real
trajectories whose sliding variable decays uniformly and whose initial value
converges to `y 0`. The quantitative engine is the conditional-stability
inequality `‖x'ε - y'‖ ≤ K ‖xε - y‖ + L |σ(xε)|`, which is turned into a uniform
estimate by Grönwall's inequality. -/

/-- **Abstract first-order approximability** of the ideal sliding state `y` on
`[0, T]` with respect to the scalar sliding variable `σ` for a class of
*admissible* trajectory families `realFamilies` (printed p. 5 of Chapter 1).
Every admissible family of trajectories `x ε` whose sliding variable
`σ (x ε ·)` converges to `0` uniformly on `[0, T]` and whose initial values
`x ε 0` converge to `y 0` converges to `y` uniformly on `[0, T]`. The control
system, the uniqueness of the sliding control law and the existence of the
equivalent control are abstracted into the predicate `realFamilies`; without
such an admissibility constraint the property would quantify over arbitrary
functions `x` and be refutable (any family sliding along `ker σ`). The lemma
`isFirstOrderApproximable_of_conditional_stability` shows that the class of
families satisfying the conditional-stability inequality is admissible. -/
def IsFirstOrderApproximable {E : Type*} [NormedAddCommGroup E]
    (realFamilies : (ℝ → ℝ → E) → Prop) (σ : E → ℝ) (y : ℝ → E) (T : ℝ) : Prop :=
  ∀ x : ℝ → ℝ → E,
    realFamilies x →
    Tendsto (fun ε ↦ x ε 0) (𝓝[>] 0) (𝓝 (y 0)) →
    (∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0, ∀ t ∈ Set.Icc 0 T, |σ (x ε t)| ≤ δ) →
    TendstoUniformlyOn x y (𝓝[>] 0) (Set.Icc 0 T)

/-- The elementary exponential inequality `e ^ y - 1 ≤ y * e ^ y`, valid for
every real `y` (it is the rearrangement of `1 - y ≤ e ^ (-y)`). It bounds the
`ε / K * (e ^ (K * x) - 1)` term of `gronwallBound` by the corresponding
`ε * x * e ^ (K * x)`. -/
theorem exp_sub_one_le_mul_exp (y : ℝ) :
    Real.exp y - 1 ≤ y * Real.exp y := by
  have h1 : 1 - Real.exp (-y) ≤ y := by
    have := Real.one_sub_le_exp_neg y
    linarith
  have h2 : (1 - Real.exp (-y)) * Real.exp y ≤ y * Real.exp y :=
    mul_le_mul_of_nonneg_right h1 (Real.exp_pos y).le
  have h3 : (1 - Real.exp (-y)) * Real.exp y = Real.exp y - 1 := by
    simp only [sub_mul, one_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rwa [h3] at h2

/-- A uniform, `K`-free bound for the Grönwall kernel: for non-negative `δ`, `K`,
`m`, `T`,
`gronwallBound δ K m T ≤ (δ + m) * (e ^ (K * T) * (1 + T))`.
It linearizes the dependence of the Grönwall estimate on the initial error `δ`
and the perturbation rate `m`, which lets the transfer theorems drive both to `0`
through the two small parameters of the regularized problem. -/
theorem gronwallBound_le_mul_exp {δ K m T : ℝ} (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hm : 0 ≤ m)
    (hT : 0 ≤ T) :
    gronwallBound δ K m T ≤ (δ + m) * (Real.exp (K * T) * (1 + T)) := by
  have hkey : δ + m * T ≤ (δ + m) * (1 + T) := by nlinarith [hδ, hm, hT]
  rcases eq_or_lt_of_le hK with hK0 | hKpos
  · rw [← hK0, gronwallBound_K0]
    simpa using hkey
  · rw [gronwallBound_of_K_ne_0 hKpos.ne']
    have h1 : m / K * (Real.exp (K * T) - 1) ≤ m * T * Real.exp (K * T) := by
      have hbase := exp_sub_one_le_mul_exp (K * T)
      have hdiv : 0 ≤ m / K := div_nonneg hm hKpos.le
      calc m / K * (Real.exp (K * T) - 1)
          ≤ m / K * ((K * T) * Real.exp (K * T)) := by gcongr
        _ = m * T * Real.exp (K * T) := by field_simp
    have h2 : δ * Real.exp (K * T) + m * T * Real.exp (K * T)
        ≤ (δ + m) * (Real.exp (K * T) * (1 + T)) := by
      have heq : δ * Real.exp (K * T) + m * T * Real.exp (K * T)
          = (δ + m * T) * Real.exp (K * T) := by ring
      rw [heq]
      have h3 := mul_le_mul_of_nonneg_right hkey (Real.exp_pos (K * T)).le
      calc (δ + m * T) * Real.exp (K * T)
          ≤ (δ + m) * (1 + T) * Real.exp (K * T) := h3
        _ = (δ + m) * (Real.exp (K * T) * (1 + T)) := by ring
    linarith

/-- **Grönwall trajectory-error estimate on `[0, T]`.** If `x` and `y` are two
trajectories on `[0, T]` with right derivatives `x'` and `y'`, if the derivative
gap is dominated by `K ‖x t - y t‖ + m` for `t ∈ [0, T)`, and if the initial gap
is at most `δ₀`, then `‖x t - y t‖ ≤ gronwallBound δ₀ K m t` for every
`t ∈ [0, T]`. The constant `m` is the uniform bound for the sliding-variable
perturbation `L |σ (x t)|` of the conditional-stability inequality, so this is the
error estimate behind first-order approximability. -/
theorem trajectory_error_le_gronwallBound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {x y : ℝ → E} {x' y' : ℝ → E}
    {K δ₀ m T : ℝ}
    (hx_cont : ContinuousOn x (Set.Icc 0 T)) (hy_cont : ContinuousOn y (Set.Icc 0 T))
    (hx_deriv : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt x (x' t) (Set.Ici t) t)
    (hy_deriv : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt y (y' t) (Set.Ici t) t)
    (hineq : ∀ t ∈ Set.Ico 0 T, ‖x' t - y' t‖ ≤ K * ‖x t - y t‖ + m)
    (hinit : ‖x 0 - y 0‖ ≤ δ₀) :
    ∀ t ∈ Set.Icc 0 T, ‖x t - y t‖ ≤ gronwallBound δ₀ K m t := by
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    (a := 0) (b := T) (f := fun t ↦ x t - y t) (f' := fun t ↦ x' t - y' t)
    (δ := δ₀) (K := K) (ε := m) (hx_cont.sub hy_cont)
    (fun t ht ↦ (hx_deriv t ht).sub (hy_deriv t ht))
    (by simpa using hinit) (fun t ht ↦ by simpa using hineq t ht)
  intro t ht
  simpa using h t ht

/-- **Master approximability theorem.** If the family `x ε` is conditionally
stable about the ideal state `y` on `[0, T]`,
`‖x'ε - y'‖ ≤ K ‖xε - y‖ + L |σ(xε)|`, if the sliding variable decays uniformly
`σ(x ε) ⇉ 0`, and if the initial states converge `x ε 0 → y 0`, then
`x ε ⇉ y` uniformly on `[0, T]` along `ε → 0⁺`. This is the first-order
approximability property of printed p. 5, at the level of a single family. -/
theorem tendstoUniformlyOn_of_conditional_stability
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {σ : E → ℝ}
    {x : ℝ → ℝ → E} {y : ℝ → E} {x' : ℝ → ℝ → E} {y' : ℝ → E}
    {T K L : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hx_cont : ∀ ε > 0, ContinuousOn (x ε) (Set.Icc 0 T))
    (hy_cont : ContinuousOn y (Set.Icc 0 T))
    (hx_deriv : ∀ ε > 0, ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt (x ε) (x' ε t) (Set.Ici t) t)
    (hy_deriv : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt y (y' t) (Set.Ici t) t)
    (hineq : ∀ ε > 0, ∀ t ∈ Set.Ico 0 T,
      ‖x' ε t - y' t‖ ≤ K * ‖x ε t - y t‖ + L * |σ (x ε t)|)
    (hinit : Tendsto (fun ε ↦ x ε 0) (𝓝[>] 0) (𝓝 (y 0)))
    (hlayer : ∀ δ > 0, ∀ᶠ ε in 𝓝[>] 0, ∀ t ∈ Set.Icc 0 T, |σ (x ε t)| ≤ δ) :
    TendstoUniformlyOn x y (𝓝[>] 0) (Set.Icc 0 T) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  have hL1 : 0 < 1 + L := by linarith
  have hMpos : 0 < Real.exp (K * T) * (1 + T) :=
    mul_pos (Real.exp_pos _) (by linarith)
  set c : ℝ := η / (2 * (1 + L) * (Real.exp (K * T) * (1 + T))) with hc
  have hcpos : 0 < c := by
    rw [hc]
    exact div_pos hη (mul_pos (mul_pos (by norm_num) hL1) hMpos)
  have hinit_ev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖x ε 0 - y 0‖ ≤ c := by
    have hnorm : Tendsto (fun ε : ℝ ↦ ‖x ε 0 - y 0‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hsub : Tendsto (fun ε : ℝ ↦ x ε 0 - y 0) (𝓝[>] (0 : ℝ)) (𝓝 (y 0 - y 0)) :=
        hinit.sub tendsto_const_nhds
      simpa using hsub.norm
    filter_upwards [hnorm.eventually_mem (Iio_mem_nhds hcpos)] with ε hε
    exact le_of_lt hε
  filter_upwards [self_mem_nhdsWithin, hinit_ev, hlayer c hcpos] with ε hεmem hεinit hεlayer
  intro t ht
  have hεpos : 0 < ε := hεmem
  have hbound : ∀ s ∈ Set.Ico 0 T, ‖x' ε s - y' s‖ ≤ K * ‖x ε s - y s‖ + L * c := by
    intro s hs
    have h1 := hineq ε hεpos s hs
    have h2 : L * |σ (x ε s)| ≤ L * c :=
      mul_le_mul_of_nonneg_left (hεlayer s (Set.Ico_subset_Icc_self hs)) hL
    linarith
  have herr := trajectory_error_le_gronwallBound (hx_cont ε hεpos) hy_cont
    (hx_deriv ε hεpos) hy_deriv hbound hεinit
  have hmono := gronwallBound_mono (δ := c) (K := K) (ε := L * c)
    hcpos.le (mul_nonneg hL hcpos.le) hK
  have hMle : gronwallBound c K (L * c) T
      ≤ (c + L * c) * (Real.exp (K * T) * (1 + T)) :=
    gronwallBound_le_mul_exp hcpos.le hK (mul_nonneg hL hcpos.le) hT
  have hc_eq : (c + L * c) * (Real.exp (K * T) * (1 + T)) ≤ η / 2 := by
    have hval : c * (1 + L) * (Real.exp (K * T) * (1 + T)) = η / 2 := by
      rw [hc]
      field_simp
    rw [show (c + L * c) * (Real.exp (K * T) * (1 + T))
        = c * (1 + L) * (Real.exp (K * T) * (1 + T)) from by ring]
    exact hval.le
  rw [dist_comm, dist_eq_norm]
  calc ‖x ε t - y t‖ ≤ gronwallBound c K (L * c) t := herr t ht
    _ ≤ gronwallBound c K (L * c) T := hmono ht.2
    _ ≤ (c + L * c) * (Real.exp (K * T) * (1 + T)) := hMle
    _ ≤ η / 2 := hc_eq
    _ < η := by linarith

/-- **Constructor for abstract approximability from conditional stability.** The
class of trajectory families `x ε` whose members are continuous on `[0, T]`,
right-differentiable on `[0, T)`, and satisfy the conditional-stability
inequality `‖x'ε - y'‖ ≤ K ‖xε - y‖ + L |σ(xε)|` (with `K, L ≥ 0`) is
first-order approximable in the sense of `IsFirstOrderApproximable`: uniform
decay of the sliding variable together with matching initial conditions forces
`x ε ⇉ y` on `[0, T]`. This is the bridge that makes the abstract predicate of
printed p. 5 a theorem-backed concept rather than an arbitrary quantification,
by discharging its admissibility hypothesis with
`tendstoUniformlyOn_of_conditional_stability`. -/
theorem isFirstOrderApproximable_of_conditional_stability
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (σ : E → ℝ) (y : ℝ → E)
    {x' : ℝ → ℝ → E} {y' : ℝ → E} {T K L : ℝ}
    (hT : 0 ≤ T) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hy_cont : ContinuousOn y (Set.Icc 0 T))
    (hy_deriv : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt y (y' t) (Set.Ici t) t) :
    IsFirstOrderApproximable
      (fun x ↦ (∀ ε > 0, ContinuousOn (x ε) (Set.Icc 0 T)) ∧
               (∀ ε > 0, ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt (x ε) (x' ε t) (Set.Ici t) t) ∧
               (∀ ε > 0, ∀ t ∈ Set.Ico 0 T,
                 ‖x' ε t - y' t‖ ≤ K * ‖x ε t - y t‖ + L * |σ (x ε t)|))
      σ y T := by
  intro x ⟨hx_cont, hx_deriv, hineq⟩ hinit hlayer
  exact tendstoUniformlyOn_of_conditional_stability hT hK hL hx_cont hy_cont hx_deriv
    hy_deriv hineq hinit hlayer

/-- **Boundary-layer closed-loop corollary.** For a family `x ε` in the boundary
layer of the sliding variable, `|σ (x ε t)| ≤ ε` for all `t ∈ [0, T]` and all
sufficiently small `ε > 0`, conditional stability forces `x ε ⇉ y` on `[0, T]`.
The hypothesis `|σ| ≤ ε` is the quantitative form of the regularized relay
`boundaryLayerRelay k ε` of this file: inside the layer the regularized feedback
keeps the sliding variable within the layer, so this discharges the formal
decay hypothesis `hlayer` of `tendstoUniformlyOn_of_conditional_stability`. -/
theorem tendstoUniformlyOn_of_boundaryLayer
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {σ : E → ℝ}
    {x : ℝ → ℝ → E} {y : ℝ → E} {x' : ℝ → ℝ → E} {y' : ℝ → E}
    {T K L : ℝ} (hT : 0 ≤ T) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hx_cont : ∀ ε > 0, ContinuousOn (x ε) (Set.Icc 0 T))
    (hy_cont : ContinuousOn y (Set.Icc 0 T))
    (hx_deriv : ∀ ε > 0, ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt (x ε) (x' ε t) (Set.Ici t) t)
    (hy_deriv : ∀ t ∈ Set.Ico 0 T, HasDerivWithinAt y (y' t) (Set.Ici t) t)
    (hineq : ∀ ε > 0, ∀ t ∈ Set.Ico 0 T,
      ‖x' ε t - y' t‖ ≤ K * ‖x ε t - y t‖ + L * |σ (x ε t)|)
    (hinit : Tendsto (fun ε ↦ x ε 0) (𝓝[>] 0) (𝓝 (y 0)))
    (hlayer : ∀ᶠ ε in 𝓝[>] 0, ∀ t ∈ Set.Icc 0 T, |σ (x ε t)| ≤ ε) :
    TendstoUniformlyOn x y (𝓝[>] 0) (Set.Icc 0 T) :=
  tendstoUniformlyOn_of_conditional_stability hT hK hL hx_cont hy_cont hx_deriv hy_deriv
    hineq hinit fun δ hδ ↦ by
      have hδev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < δ :=
        (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
      filter_upwards [hlayer, hδev] with ε hε hεδ
      exact fun t ht ↦ (hε t ht).trans hεδ.le
