/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Stability.Lyapunov
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Discrete-time Lyapunov stability

This file is a thin bridge between the discrete-time iterate `fun n x ↦ f^[n] x` of a
self-map `f : E → E` and the time-generic Lyapunov theory of
`DynamicalSystems.Stability.Lyapunov`. That theory is already generic in the time
index `ι`; instantiating `ι = ℕ` and `Φ = fun n x ↦ f^[n] x` recovers the
discrete-time notions, so no parallel predicates are introduced here.

## Main results

* `isLyapunov_discreteFlow`: a one-step non-increasing function is a Lyapunov
  function for the discrete flow.
* `isStableOn_discreteFlow`: the discrete Lyapunov stability theorem, obtained by
  instantiating `IsLyapunov.isStableOn_nhds` at `ι = ℕ` and `t₀ = 0`.
* `sum_le_of_succ_le_sub`, `summable_of_succ_le_sub`, `tendsto_zero_of_succ_le_sub`,
  `le_of_succ_le_sub`: the scalar dissipation / telescoping bridge turning the rate
  inequality `v (t + 1) ≤ v t − w t` into `Summable w` and `w → 0`.
-/

@[expose] public section

open scoped Topology

/-- If a non-negative continuous function `V` does not increase at each step of `f`,
then it is a Lyapunov function for the discrete flow `fun n x ↦ f^[n] x`.

The monotonicity along the flow follows from `hV` by induction on the iterate:
`V (f^[n] x) ≤ V x`, and then `f^[n + m] x = f^[m] (f^[n] x)`. -/
theorem isLyapunov_discreteFlow {E : Type*} [TopologicalSpace E] {f : E → E} {V : E → ℝ}
    (hpos : ∀ x, 0 ≤ V x) (hcont : Continuous V) (hV : ∀ x, V (f x) ≤ V x) :
    IsLyapunov V (fun n x ↦ f^[n] x) where
  pos := hpos
  cont := hcont
  antitone := by
    have hiter : ∀ (n : ℕ) (x : E), V (f^[n] x) ≤ V x := by
      intro n
      induction n with
      | zero => intro x; simp
      | succ n ih =>
          intro x
          calc V (f^[n.succ] x) = V (f (f^[n] x)) := by rw [Function.iterate_succ_apply']
            _ ≤ V (f^[n] x) := hV _
            _ ≤ V x := ih x
    intro x t₀ t₁ ht
    have hk : t₁ - t₀ + t₀ = t₁ := Nat.sub_add_cancel ht
    rw [← hk, Function.iterate_add_apply]
    exact hiter (t₁ - t₀) (f^[t₀] x)

/-- Discrete Lyapunov stability: if a continuous, positive-definite `V` with
`∀ x, V x = 0 ↔ x = x₀` is non-increasing along `f`, then `x₀` is stable for the
discrete flow `fun n x ↦ f^[n] x`.

This is `IsLyapunov.isStableOn_nhds` instantiated at `ι = ℕ` and `t₀ = 0`, using
`Set.Ici (0 : ℕ) = Set.univ`.

Only `TopologicalSpace E` and `FirstCountableTopology E` are needed, exactly as in
`IsLyapunov.isStableOn_nhds`; the compactness of the sublevel set is an explicit
hypothesis `hcpt`. -/
theorem isStableOn_discreteFlow {E : Type*} [TopologicalSpace E] [FirstCountableTopology E]
    {f : E → E} {V : E → ℝ} {x₀ : E}
    (hVcont : Continuous V) (hpos : ∀ x, 0 ≤ V x) (hmono : ∀ x, V (f x) ≤ V x)
    (hVx₀ : ∀ x, V x = 0 ↔ x = x₀) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hcpt : IsCompact {p | V p ≤ δ₀}) :
    (𝓝 x₀).IsStableOn (fun n x ↦ f^[n] x) Set.univ := by
  have hlyap : IsLyapunov V (fun n x ↦ f^[n] x) :=
    isLyapunov_discreteFlow hpos hVcont hmono
  have hstab := hlyap.isStableOn_nhds hVx₀ (t₀ := 0)
    (fun x ↦ Function.iterate_zero_apply f x) hδ₀ hcpt
  simpa using hstab

/-! ## Scalar dissipation / telescoping bridge

`IsLyapunov` only gives the monotonicity `V (t + 1) ≤ V t`. The parameter adaptation and
direct adaptive control convergence theorems need the *rate* form
`V (t + 1) ≤ V t − W t` summed to `W ∈ ℓ¹`, hence `W → 0`. The lemmas below provide that
scalar telescoping bridge. -/

/-- Partial-sum bound for a non-negative sequence with a telescoping decrease: if
`v` is non-negative and `v (t + 1) ≤ v t − w t` for all `t`, then the partial sums of
`w` up to `n` are bounded by `v 0`. -/
theorem sum_le_of_succ_le_sub {v w : ℕ → ℝ} (hv : ∀ t, 0 ≤ v t)
    (h : ∀ t, v (t + 1) ≤ v t - w t) (n : ℕ) :
    (Finset.sum (Finset.range n) w) ≤ v 0 := by
  have key : ∀ n, (Finset.sum (Finset.range n) w) ≤ v 0 - v n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ]
        have ht : w n ≤ v n - v (n + 1) := by linarith [h n]
        linarith
  exact (key n).trans (by linarith [hv n])

/-- A non-negative decay rate that decreases a non-negative Lyapunov sequence is
summable. -/
theorem summable_of_succ_le_sub {v w : ℕ → ℝ} (hv : ∀ t, 0 ≤ v t) (hw : ∀ t, 0 ≤ w t)
    (h : ∀ t, v (t + 1) ≤ v t - w t) : Summable w :=
  summable_of_sum_range_le hw (fun n ↦ sum_le_of_succ_le_sub hv h n)

/-- The discrete dissipation bridge (discrete analogue of Barbălat): the decay rate
of a non-negative Lyapunov sequence with a telescoping decrease tends to `0`. -/
theorem tendsto_zero_of_succ_le_sub {v w : ℕ → ℝ} (hv : ∀ t, 0 ≤ v t) (hw : ∀ t, 0 ≤ w t)
    (h : ∀ t, v (t + 1) ≤ v t - w t) : Filter.Tendsto w Filter.atTop (𝓝 0) :=
  (summable_of_succ_le_sub hv hw h).tendsto_atTop_zero

/-- The Lyapunov sequence is bounded by its initial value: if `w` is non-negative and
`v (t + 1) ≤ v t − w t`, then `v t ≤ v 0` for all `t`. -/
theorem le_of_succ_le_sub {v w : ℕ → ℝ} (hw : ∀ t, 0 ≤ w t)
    (h : ∀ t, v (t + 1) ≤ v t - w t) (t : ℕ) : v t ≤ v 0 := by
  have hmono : ∀ t, v (t + 1) ≤ v t := fun t ↦ by linarith [h t, hw t]
  induction t with
  | zero => exact le_refl _
  | succ t ih => exact (hmono t).trans ih
