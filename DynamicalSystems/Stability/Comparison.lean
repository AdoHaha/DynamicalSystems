/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.ODE.Gronwall

/-!
# Scalar comparison (Grönwall) estimates

This file records the elementary scalar comparison estimates that underpin the
ultimate-boundedness and exponential-stability arguments of the book. They are
direct corollaries of Mathlib's Grönwall inequality
`le_gronwallBound_of_liminf_deriv_right_le`; no integrating factor is re-derived
here.

## Main statements

* `le_gronwallBound_of_hasDerivAt_le_neg_mul_add`: if the right derivative of a
  continuous scalar function `v` satisfies the differential *inequality*
  `v' t ≤ -(c * v t) + d` for `t ≥ 0`, with `c > 0`, then
  `v t ≤ v 0 * exp (-c * t) + d / c * (1 - exp (-c * t))`.
* `exponential_decay_of_hasDerivAt_le`: the specialization `d = 0`, giving the
  exponential decay bound `v t ≤ v 0 * exp (-c * t)`.
-/

@[expose] public section

open Set Filter Real
open scoped Topology

/-- Scalar comparison (Grönwall) estimate for a one-dimensional differential
inequality.

If `v : ℝ → ℝ` is continuous on `[0, ∞)`, has a right derivative `deriv v t` at
every `t ≥ 0`, and satisfies the differential *inequality*
`deriv v t ≤ -(c * v t) + d` for all `t ≥ 0`, with `c > 0`, then for every
`t ≥ 0`

`v t ≤ v 0 * exp (-c * t) + d / c * (1 - exp (-c * t))`.

The right-hand side is (up to rewriting) Mathlib's `gronwallBound (v 0) (-c) d t`,
so this is a direct corollary of `le_gronwallBound_of_liminf_deriv_right_le`. -/
theorem le_gronwallBound_of_hasDerivAt_le_neg_mul_add
    {v : ℝ → ℝ} {c d : ℝ} (hc : 0 < c)
    (hv : ContinuousOn v (Set.Ici 0))
    (hderiv : ∀ t, 0 ≤ t → HasDerivWithinAt v (deriv v t) (Set.Ici t) t)
    (hineq : ∀ t, 0 ≤ t → deriv v t ≤ -(c * v t) + d) :
    ∀ t, 0 ≤ t → v t ≤ v 0 * Real.exp (-c * t) + d / c * (1 - Real.exp (-c * t)) := by
  intro t ht
  have hK : (-c : ℝ) ≠ 0 := by linarith
  have hmain : v t ≤ gronwallBound (v 0) (-c) d (t - 0) :=
    le_gronwallBound_of_liminf_deriv_right_le (a := 0) (b := t) (f := v) (f' := deriv v)
      (δ := v 0) (K := -c) (ε := d) (hv.mono fun _ hx ↦ hx.1)
      (fun x hx r hr ↦ (hderiv x hx.1).liminf_right_slope_le hr)
      (le_refl _) (fun x hx ↦ by simpa only [neg_mul] using hineq x hx.1) t ⟨ht, le_refl t⟩
  rw [sub_zero, gronwallBound_of_K_ne_0 hK] at hmain
  refine hmain.trans_eq ?_
  field_simp
  ring

/-- Exponential decay from a homogeneous scalar differential inequality.

If `v : ℝ → ℝ` is continuous on `[0, ∞)`, has a right derivative `deriv v t` at
every `t ≥ 0`, and satisfies `deriv v t ≤ -(c * v t)` for all `t ≥ 0`, with
`c > 0`, then `v t ≤ v 0 * exp (-c * t)` for every `t ≥ 0`.

This is the `d = 0` specialization of
`le_gronwallBound_of_hasDerivAt_le_neg_mul_add`. -/
theorem exponential_decay_of_hasDerivAt_le
    {v : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hv : ContinuousOn v (Set.Ici 0))
    (hderiv : ∀ t, 0 ≤ t → HasDerivWithinAt v (deriv v t) (Set.Ici t) t)
    (hineq : ∀ t, 0 ≤ t → deriv v t ≤ -(c * v t)) :
    ∀ t, 0 ≤ t → v t ≤ v 0 * Real.exp (-c * t) := by
  intro t ht
  have h0 : ∀ t, 0 ≤ t → deriv v t ≤ -(c * v t) + 0 := fun t ht ↦ by
    simpa using hineq t ht
  simpa using le_gronwallBound_of_hasDerivAt_le_neg_mul_add hc hv hderiv h0 t ht
