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
