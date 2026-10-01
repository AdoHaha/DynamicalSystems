/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Basic.NonAutonomous
public import DynamicalSystems.Stability.Equilibrium
public import DynamicalSystems.Stability.Comparison
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.ODE.Gronwall

/-!
# Uniform boundedness from Grönwall dissipation

This file is slice L6a of the formalization of J. Kabziński and P. Mosiołek,
*Projektowanie nieliniowych układów sterowania*, Komitet Automatyki i Robotyki PAN,
Monografie tom 22. It bridges the scalar Grönwall comparison estimates in
`DynamicalSystems.Stability.Comparison` to the non-autonomous flow boundedness predicates
`IsUniformlyBoundedAt` of `DynamicalSystems.Stability.Equilibrium`.

The key input is a Lyapunov function `V : E → ℝ` whose value along every trajectory
`s ↦ V (Φ t₀ x s)` satisfies the dissipative differential inequality
`deriv (V ∘ Φ) t ≤ -(c * V (Φ t₀ x t)) + d`, with `c > 0`. Comparing against the scalar
Grönwall solution shows that the energy along a trajectory is bounded by
`max (V x) (d / c)`, uniformly in the initial time `t₀` and the elapsed time. When `V` is
sandwiched between monotone comparison functions `g₁ ‖x‖ ≤ V x ≤ g₂ ‖x‖` with `g₁` radially
unbounded, this yields `IsUniformlyBoundedAt Φ`.

## Main statements

* `gronwall_bound_le_max`: the affine Grönwall bound is at most
  `max v₀ (d / c)`, since it is a convex combination of `v₀` and `d / c`.
* `gronwall_isUniformlyBoundedAt`: Grönwall dissipation with radially unbounded sandwich
  bounds implies `IsUniformlyBoundedAt Φ`.
* `gronwall_decay_lt_of_tau`: the affine Grönwall bound drops below any level `L > d / c`
  after an explicitly computed uniform time `τ`, independent of the initial value `v₀ ≤ Vmax`.
* `gronwall_isUltimatelyUniformlyBoundedAt`: Grönwall dissipation with a sandwich
  `g₁ ‖x‖ ≤ V x ≤ g₂ ‖x‖` and `d / c < g₁ B` implies `IsUltimatelyUniformlyBoundedAt Φ B`.
-/

open Set Filter Real
open scoped Topology

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E]

/-- The affine Grönwall bound `v₀ * exp (-c * s) + d / c * (1 - exp (-c * s))` is a convex
combination of `v₀` and `d / c` with coefficients `exp (-c * s) ∈ (0, 1]` and
`1 - exp (-c * s) ∈ [0, 1)`, hence it is at most `max v₀ (d / c)` for every `s ≥ 0`. -/
theorem gronwall_bound_le_max (v₀ c d s : ℝ) (hc : 0 < c) (hs : 0 ≤ s) :
    v₀ * Real.exp (-c * s) + d / c * (1 - Real.exp (-c * s)) ≤ max v₀ (d / c) := by
  have hpos : 0 < Real.exp (-c * s) := Real.exp_pos _
  have hle : Real.exp (-c * s) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  rcases le_total v₀ (d / c) with h | h
  · have hmul : Real.exp (-c * s) * (v₀ - d / c) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hpos.le (sub_nonpos.mpr h)
    have hbound : v₀ * Real.exp (-c * s) + d / c * (1 - Real.exp (-c * s)) ≤ d / c := by
      nlinarith [hmul]
    exact hbound.trans (le_max_right _ _)
  · have hmul : (d / c - v₀) * (1 - Real.exp (-c * s)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (sub_nonneg.mpr hle)
    have hbound : v₀ * Real.exp (-c * s) + d / c * (1 - Real.exp (-c * s)) ≤ v₀ := by
      nlinarith [hmul]
    exact hbound.trans (le_max_left _ _)

/-- Uniform boundedness of a non-autonomous flow from a radially unbounded Lyapunov sandwich
and Grönwall dissipation.

Let `Φ` be a non-autonomous flow and `V : E → ℝ` an energy function satisfying the dissipative
differential inequality `deriv (V ∘ Φ) t ≤ -(c * V (Φ t₀ x t)) + d` along every trajectory with
`c > 0`, with a two-sided derivative at every `t ≥ t₀ ≥ 0`. Suppose further that `V` is
sandwiched between comparison functions `g₁ ‖x‖ ≤ V x ≤ g₂ ‖x‖`, where `g₁` is strictly monotone
on `[0, ∞)` and radially unbounded while `g₂` is monotone on `[0, ∞)`. Then the trajectories of
`Φ` are uniformly bounded, i.e. `IsUniformlyBoundedAt Φ`.

The bound for an initial ball of radius `α` is `β ≥ 1` chosen so that
`max (g₂ α) (d / c) < g₁ β`; it is selected before the initial time and initial state, which is
what makes the bound uniform. -/
theorem gronwall_isUniformlyBoundedAt
    (Φ : NonautonomousFlow ℝ E) (V : E → ℝ)
    (c d : ℝ) (hc : 0 < c)
    (g1 g2 : ℝ → ℝ)
    (hg1_mono : StrictMonoOn g1 (Set.Ici 0))
    (hg2_mono : MonotoneOn g2 (Set.Ici 0))
    (hg1 : ∀ x, g1 ‖x‖ ≤ V x)
    (hg2 : ∀ x, V x ≤ g2 ‖x‖)
    (hg1_unbounded : Tendsto g1 atTop atTop)
    (hderiv : ∀ t0 ≥ 0, ∀ x, ∀ t ≥ t0,
      HasDerivAt (fun s ↦ V (Φ t0 x s)) (deriv (fun s ↦ V (Φ t0 x s)) t) t)
    (hineq : ∀ t0 ≥ 0, ∀ x, ∀ t ≥ t0,
      deriv (fun s ↦ V (Φ t0 x s)) t ≤ -(c * V (Φ t0 x t)) + d) :
    IsUniformlyBoundedAt Φ := by
  intro α hα
  let M : ℝ := max (g2 α) (d / c)
  have hβ : ∃ β, 1 ≤ β ∧ M < g1 β := by
    have h1 : ∀ᶠ β in atTop, (1 : ℝ) ≤ β := eventually_ge_atTop 1
    have h2 : ∀ᶠ β in atTop, M < g1 β :=
      hg1_unbounded.eventually (eventually_gt_atTop M)
    exact (h1.and h2).exists
  obtain ⟨β, hβ1, hβM⟩ := hβ
  refine ⟨β, by linarith, ?_⟩
  intro t0 ht0 x hx t ht
  have hxα : ‖x‖ ≤ α := le_of_lt hx
  have hVxα : V x ≤ g2 α := by
    have h1 : g2 ‖x‖ ≤ g2 α := hg2_mono (norm_nonneg x) hα.le hxα
    linarith [hg2 x, h1]
  have hVx : V x ≤ M := hVxα.trans (le_max_left _ _)
  have hbound : V (Φ t0 x t) ≤
      V x * Real.exp (-c * (t - t0)) + d / c * (1 - Real.exp (-c * (t - t0))) := by
    have := le_gronwallBound_of_hasDerivAt_le_Ici (v := fun s ↦ V (Φ t0 x s)) (t₀ := t0) hc
      (fun t ht ↦ hderiv t0 ht0 x t ht) (fun t ht ↦ hineq t0 ht0 x t ht) t ht
    simpa using this
  have hmax := gronwall_bound_le_max (V x) c d (t - t0) hc (by linarith)
  have hVt : V (Φ t0 x t) ≤ M := by
    have hM : max (V x) (d / c) ≤ M := max_le_max hVxα le_rfl
    linarith
  have hlt : g1 ‖Φ t0 x t‖ < g1 β :=
    lt_of_le_of_lt (hg1 _) (lt_of_le_of_lt hVt hβM)
  have hnorm : ‖Φ t0 x t‖ ∈ Set.Ici (0 : ℝ) := norm_nonneg _
  have hβmem : β ∈ Set.Ici (0 : ℝ) := by
    simp only [Set.mem_Ici]
    linarith
  exact (hg1_mono.lt_iff_lt hnorm hβmem).mp hlt

/-- Uniform decay time threshold for the affine Grönwall bound.

Given `c > 0` and a target level `L > d / c`, there is a single time `τ > 0` such that the
Grönwall comparison solution `v₀ * exp (-c * s) + d / c * (1 - exp (-c * s))` is below `L` for
every elapsed time `s ≥ τ` and every initial value `v₀ ≤ Vmax`.

If `Vmax ≤ d / c` the bound is a convex combination of `v₀ ≤ Vmax` and `d / c`, hence at most
`d / c < L` for *every* `s ≥ 0`, and `τ := 1` works. Otherwise `Vmax - d / c > 0` and
`L - d / c > 0`, and we take
`τ := max 1 ((log ((Vmax - d / c) / (L - d / c)) + 1) / c)`, so that for `s ≥ τ`
`exp (-c * s) < (L - d / c) / (Vmax - d / c)`, whence
`(Vmax - d / c) * exp (-c * s) < L - d / c`. -/
theorem gronwall_decay_lt_of_tau (c d L Vmax : ℝ) (hc : 0 < c) (hL : d / c < L) :
    ∃ τ > 0, ∀ v₀ ≤ Vmax, ∀ s ≥ τ,
      v₀ * Real.exp (-c * s) + d / c * (1 - Real.exp (-c * s)) < L := by
  by_cases hV : Vmax ≤ d / c
  · refine ⟨1, one_pos, ?_⟩
    intro v₀ hv₀ s _
    have hb := gronwall_bound_le_max v₀ c d s hc (by linarith)
    have hv : v₀ ≤ d / c := hv₀.trans hV
    have hmax : max v₀ (d / c) ≤ d / c := max_le hv le_rfl
    linarith
  · refine ⟨max 1 ((Real.log ((Vmax - d / c) / (L - d / c)) + 1) / c), ?_, ?_⟩
    · exact lt_of_lt_of_le one_pos (le_max_left _ _)
    · intro v₀ hv₀ s hs
      have hV' : d / c < Vmax := lt_of_not_ge hV
      have hA : 0 < Vmax - d / c := by linarith
      have hE : 0 < L - d / c := by linarith
      have hdiv : 0 < (Vmax - d / c) / (L - d / c) := div_pos hA hE
      have hτle : (Real.log ((Vmax - d / c) / (L - d / c)) + 1) / c ≤ s :=
        (le_max_right _ _).trans hs
      have hmulc : Real.log ((Vmax - d / c) / (L - d / c)) + 1 ≤ c * s := by
        have h := (div_le_iff₀ hc).mp hτle
        rwa [mul_comm s c] at h
      have hlog_lt : Real.log ((Vmax - d / c) / (L - d / c)) < c * s := by linarith
      have hexp_lt : Real.exp (-c * s) < (L - d / c) / (Vmax - d / c) := by
        have h1 : Real.exp (-c * s) <
            Real.exp (-(Real.log ((Vmax - d / c) / (L - d / c)))) :=
          Real.exp_lt_exp.mpr (by linarith)
        rwa [Real.exp_neg, Real.exp_log hdiv, inv_div] at h1
      have h2 : (Vmax - d / c) * Real.exp (-c * s) < L - d / c := by
        have hthis := mul_lt_mul_of_pos_left hexp_lt hA
        have hcancel : (Vmax - d / c) * ((L - d / c) / (Vmax - d / c)) = L - d / c := by
          rw [← mul_div_assoc]
          exact mul_div_cancel_left₀ _ (ne_of_gt hA)
        linarith [hthis, hcancel]
      have hle : v₀ - d / c ≤ Vmax - d / c := by linarith
      have hpos : 0 < Real.exp (-c * s) := Real.exp_pos _
      have h3 : (v₀ - d / c) * Real.exp (-c * s) < L - d / c :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle hpos.le) h2
      have hrewrite : v₀ * Real.exp (-c * s) + d / c * (1 - Real.exp (-c * s))
          = d / c + (v₀ - d / c) * Real.exp (-c * s) := by ring
      rw [hrewrite]
      linarith

/-- Ultimate uniform boundedness of a non-autonomous flow from a Lyapunov sandwich and
Grönwall dissipation.

Let `Φ` be a non-autonomous flow and `V : E → ℝ` an energy function satisfying the dissipative
differential inequality `deriv (V ∘ Φ) t ≤ -(c * V (Φ t₀ x t)) + d` along every trajectory with
`c > 0`, with a two-sided derivative at every `t ≥ t₀ ≥ 0`. Suppose further that `V` is
sandwiched between comparison functions `g₁ ‖x‖ ≤ V x ≤ g₂ ‖x‖`, where `g₁` is strictly monotone
on `[0, ∞)` and `g₂` is monotone on `[0, ∞)`. If the ultimate bound `B > 0` satisfies
`d / c < g₁ B`, then the trajectories of `Φ` are ultimately uniformly bounded with ultimate bound
`B`, i.e. `IsUltimatelyUniformlyBoundedAt Φ B`.

Given a radius `α > 0` the intermediate energy level `L := (d / c + g₁ B) / 2` lies strictly
between `d / c` and `g₁ B`. The uniform decay time `τ` produced by `gronwall_decay_lt_of_tau`
for `Vmax := g₂ α` depends only on `α, B, c, d, g₁, g₂`, not on the initial time `t₀` or the
initial state `x`, which is what makes the bound uniform. -/
theorem gronwall_isUltimatelyUniformlyBoundedAt
    (Φ : NonautonomousFlow ℝ E) (V : E → ℝ)
    (c d : ℝ) (hc : 0 < c)
    (B : ℝ) (hB_pos : 0 < B)
    (g1 g2 : ℝ → ℝ)
    (hg1_mono : StrictMonoOn g1 (Set.Ici 0))
    (hg2_mono : MonotoneOn g2 (Set.Ici 0))
    (hg1 : ∀ x, g1 ‖x‖ ≤ V x)
    (hg2 : ∀ x, V x ≤ g2 ‖x‖)
    (hB : d / c < g1 B)
    (hderiv : ∀ t0 ≥ 0, ∀ x, ∀ t ≥ t0,
      HasDerivAt (fun s ↦ V (Φ t0 x s)) (deriv (fun s ↦ V (Φ t0 x s)) t) t)
    (hineq : ∀ t0 ≥ 0, ∀ x, ∀ t ≥ t0,
      deriv (fun s ↦ V (Φ t0 x s)) t ≤ -(c * V (Φ t0 x t)) + d) :
    IsUltimatelyUniformlyBoundedAt Φ B := by
  intro α hα
  have hL_lt : d / c < (d / c + g1 B) / 2 := by linarith
  obtain ⟨τ, hτ_pos, hτ⟩ :=
    gronwall_decay_lt_of_tau c d ((d / c + g1 B) / 2) (g2 α) hc hL_lt
  refine ⟨τ, hτ_pos, ?_⟩
  intro t0 ht0 x hx t ht
  have hVx : V x ≤ g2 α := by
    have h1 : g2 ‖x‖ ≤ g2 α := hg2_mono (norm_nonneg x) hα.le (le_of_lt hx)
    linarith [hg2 x, h1]
  have hs : t - t0 ≥ τ := by linarith
  have hv0 : V (Φ t0 x t0) ≤ g2 α := by
    simpa only [NonautonomousFlow.map_id] using hVx
  have hdecay := hτ (V (Φ t0 x t0)) hv0 (t - t0) hs
  have hbound : V (Φ t0 x t) ≤
      V (Φ t0 x t0) * Real.exp (-c * (t - t0))
        + d / c * (1 - Real.exp (-c * (t - t0))) :=
    le_gronwallBound_of_hasDerivAt_le_Ici (v := fun s ↦ V (Φ t0 x s)) (t₀ := t0) hc
      (fun s hs' ↦ hderiv t0 ht0 x s hs') (fun s hs' ↦ hineq t0 ht0 x s hs') t (by linarith)
  have hVt_lt : V (Φ t0 x t) < (d / c + g1 B) / 2 := lt_of_le_of_lt hbound hdecay
  have hmid_lt : (d / c + g1 B) / 2 < g1 B := by linarith
  have hg1_lt : g1 ‖Φ t0 x t‖ < g1 B :=
    lt_of_le_of_lt (hg1 _) (lt_trans hVt_lt hmid_lt)
  have hnorm : ‖Φ t0 x t‖ ∈ Set.Ici (0 : ℝ) := norm_nonneg _
  have hBmem : B ∈ Set.Ici (0 : ℝ) := by
    simp only [Set.mem_Ici]
    linarith
  exact (hg1_mono.lt_iff_lt hnorm hBmem).mp hg1_lt

/-- State-norm bridge for a Lyapunov-level eventual bound.

Suppose the Lyapunov function `V` is eventually bounded by `B` along the trajectory
`t ↦ x t`, and `V` dominates `k₁ ‖x t‖²` with `k₁ > 0`. Then the state norm is eventually
bounded by `√(B / k₁)`. This is the quantitative final step of the Kabziński–Mosiołek
ultimate-boundedness arguments (Theorems 7.4–7.6): the Lyapunov sublevel set
`{x | V x < B}` is contained in the ball of radius `√(B / k₁)`. -/
theorem eventually_norm_lt_sqrt_of_lyapunov_le
    {E : Type*} [NormedAddCommGroup E] {V : E → ℝ} {x : ℝ → E} {B k1 : ℝ}
    (hk1 : 0 < k1)
    (hV : ∀ᶠ t in Filter.atTop, V (x t) < B)
    (hle : ∀ t, k1 * ‖x t‖ ^ 2 ≤ V (x t)) :
    ∀ᶠ t in Filter.atTop, ‖x t‖ < Real.sqrt (B / k1) := by
  filter_upwards [hV] with t ht
  have hsq : ‖x t‖ ^ 2 < B / k1 := by
    rw [lt_div_iff₀ hk1]
    calc ‖x t‖ ^ 2 * k1 = k1 * ‖x t‖ ^ 2 := by ring
      _ < B := lt_of_le_of_lt (hle t) ht
  exact (Real.lt_sqrt (norm_nonneg (x t))).mpr hsq
