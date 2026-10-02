/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Stability.Definitions

/-! # Finite-time attractivity and finite-time stability

This file records the finite-time stability vocabulary of A. Levant and L. Alelishvili,
*Discontinuous Homogeneous Control*, Chapter 4 of G. Bartolini, L. Fridman, A. Pisano and
E. Usai (eds.), *Modern Sliding Mode Control Theory: New Perspectives and Applications*,
LNCIS 375, Springer 2008. Definition 1° (printed p. 72, PDF p. 88) calls a differential
inclusion (or equation) *globally uniformly finite-time stable* at `0` when it is Lyapunov
stable and every disk `‖x‖ < R` settles at `0` within a uniform time `T(R)`.

The definitions mirror `DynamicalSystems.Stability.Definitions`: the pointwise predicate is
the local building block, while the global uniform predicate is the one Levant's
homogeneity theorem (Theorem 1) is stated over. The finite-time attractivity condition is
filter-quantified, exactly as `Filter.IsAttractive`: it asks that *every state sufficiently
close to* `x₀` reaches `x₀` in finite time and stays there. Pulling the settling time
outside the neighbourhood filter would force a globally defined settling-time function and
is deliberately avoided.

## Main definitions

* `IsFiniteTimeAttractiveAt`: every nearby state reaches `x₀` in finite time and stays there.
* `IsFiniteTimeStableAt`: Lyapunov stability together with finite-time attractivity.
* `IsGloballyUniformlyFiniteTimeStable`: Lyapunov stability plus a settling time that is
  uniform over each ball `dist x x₀ < R` (Levant definition 1°).

## Main statements

* `IsFiniteTimeAttractiveAt.isAttractive`: finite-time attractivity implies attractivity.
* `IsFiniteTimeStableAt.isAsymptoticallyStable`: finite-time stability implies asymptotic
  stability.
* `IsGloballyUniformlyFiniteTimeStable.isFiniteTimeStableAt`: the global uniform notion
  implies the pointwise one.
* `IsFiniteTimeStableAt.isLyapunovStable` and `IsFiniteTimeStableAt.isFiniteTimeAttractiveAt`:
  the two halves of the defining conjunction.
* `IsFiniteTimeAttractiveAt.eventually_eq_self`: a finite-time-attractive equilibrium is
  eventually a fixed point.
-/

open Filter
open scoped Topology

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E]

/-- A flow is *finite-time attractive at* `x₀` if every state in a neighbourhood of `x₀`
reaches `x₀` in finite time and stays there. -/
def IsFiniteTimeAttractiveAt (Φ : ℝ → E → E) (x₀ : E) : Prop :=
  ∀ᶠ x in 𝓝 x₀, ∃ T : ℝ, 0 ≤ T ∧ ∀ t, T ≤ t → Φ t x = x₀

/-- Finite-time stability of `x₀`: Lyapunov stability together with finite-time
attractivity. -/
def IsFiniteTimeStableAt (Φ : ℝ → E → E) (x₀ : E) : Prop :=
  IsLyapunovStable Φ x₀ ∧ IsFiniteTimeAttractiveAt Φ x₀

/-- **Global uniform finite-time stability** (Levant & Alelishvili, Chapter 4, definition 1°,
printed p. 72): Lyapunov stability plus a settling time uniform over each ball
`dist x x₀ < R`. This is the predicate Levant's Theorem 1 is stated over. -/
def IsGloballyUniformlyFiniteTimeStable (Φ : ℝ → E → E) (x₀ : E) : Prop :=
  IsLyapunovStable Φ x₀ ∧
    ∀ R > 0, ∃ T : ℝ, 0 ≤ T ∧ ∀ x, dist x x₀ < R → ∀ t, T ≤ t → Φ t x = x₀

/-- Finite-time attractivity implies (ordinary) attractivity: a trajectory that equals `x₀`
for all sufficiently large times converges to `x₀`. -/
theorem IsFiniteTimeAttractiveAt.isAttractive {Φ : ℝ → E → E} {x₀ : E}
    (h : IsFiniteTimeAttractiveAt Φ x₀) :
    Filter.IsAttractive (l := 𝓝 x₀) (Φ := Φ) (l' := Filter.atTop) := by
  unfold Filter.IsAttractive
  filter_upwards [h] with x hx
  obtain ⟨T, _hT, hTx⟩ := hx
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop T] with t ht
  exact (hTx t ht).symm

/-- Finite-time stability implies asymptotic stability: the Lyapunov-stability half is kept
and the finite-time-attractivity half is weakened to attractiveness. -/
theorem IsFiniteTimeStableAt.isAsymptoticallyStable {Φ : ℝ → E → E} {x₀ : E}
    (h : IsFiniteTimeStableAt Φ x₀) : IsAsymptoticallyStable Φ x₀ :=
  ⟨h.1, h.2.isAttractive⟩

/-- Global uniform finite-time stability implies finite-time stability: the uniform settling
time for the unit ball witnesses finite-time attractivity. -/
theorem IsGloballyUniformlyFiniteTimeStable.isFiniteTimeStableAt {Φ : ℝ → E → E} {x₀ : E}
    (h : IsGloballyUniformlyFiniteTimeStable Φ x₀) : IsFiniteTimeStableAt Φ x₀ := by
  refine ⟨h.1, ?_⟩
  obtain ⟨T, hT0, hT⟩ := h.2 1 one_pos
  exact Filter.mem_of_superset (Metric.ball_mem_nhds x₀ one_pos) fun x hx =>
    ⟨T, hT0, fun t ht => hT x (Metric.mem_ball.mp hx) t ht⟩

/-- The Lyapunov-stability half of finite-time stability. -/
theorem IsFiniteTimeStableAt.isLyapunovStable {Φ : ℝ → E → E} {x₀ : E}
    (h : IsFiniteTimeStableAt Φ x₀) : IsLyapunovStable Φ x₀ :=
  h.1

/-- The finite-time-attractivity half of finite-time stability. -/
theorem IsFiniteTimeStableAt.isFiniteTimeAttractiveAt {Φ : ℝ → E → E} {x₀ : E}
    (h : IsFiniteTimeStableAt Φ x₀) : IsFiniteTimeAttractiveAt Φ x₀ :=
  h.2

/-- A finite-time-attractive equilibrium is eventually a fixed point: since `x₀` lies in every
neighbourhood of itself, the settling time supplied for nearby states applies to `x₀`. -/
theorem IsFiniteTimeAttractiveAt.eventually_eq_self {Φ : ℝ → E → E} {x₀ : E}
    (h : IsFiniteTimeAttractiveAt Φ x₀) : ∃ T : ℝ, ∀ t, T ≤ t → Φ t x₀ = x₀ := by
  obtain ⟨T, _hT0, hT⟩ := h.self_of_nhds
  exact ⟨T, hT⟩
