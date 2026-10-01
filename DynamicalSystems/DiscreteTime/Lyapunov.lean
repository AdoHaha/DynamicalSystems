/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Stability.Lyapunov

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

`NormedSpace ℝ E` and `ProperSpace E` are kept in the signature to match the
discrete-time stability statement (and to place the result in the standard setting
for the campaign); the proof itself only needs `NormedAddCommGroup E` and the
compactness hypothesis `hcpt`. -/
@[nolint unusedArguments]
theorem isStableOn_discreteFlow {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] {f : E → E} {V : E → ℝ} {x₀ : E}
    (hVcont : Continuous V) (hpos : ∀ x, 0 ≤ V x) (hmono : ∀ x, V (f x) ≤ V x)
    (hVx₀ : ∀ x, V x = 0 ↔ x = x₀) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hcpt : IsCompact {p | V p ≤ δ₀}) :
    (𝓝 x₀).IsStableOn (fun n x ↦ f^[n] x) Set.univ := by
  have hlyap : IsLyapunov V (fun n x ↦ f^[n] x) :=
    isLyapunov_discreteFlow hpos hVcont hmono
  have hstab := hlyap.isStableOn_nhds hVx₀ (t₀ := 0)
    (fun x ↦ Function.iterate_zero_apply f x) hδ₀ hcpt
  simpa using hstab
