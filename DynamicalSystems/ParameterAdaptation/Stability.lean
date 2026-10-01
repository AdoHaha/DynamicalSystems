/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.DiscreteTime.Lyapunov
public import Mathlib.Analysis.Real.Sqrt

/-! # Stability of parameter adaptation algorithms

This file records the scalar stability corollary of the parameter adaptation
algorithm (PAA) Lyapunov identity. For a non-negative Lyapunov sequence `V` with a
non-negative telescoping decrease rate `w`,

`V (t + 1) ≤ V t - w t`,

the dissipation bridge of `DynamicalSystems.DiscreteTime.Lyapunov` makes `w`
summable. Any adaptation error `ν` whose square is dominated by the decay rate,
`ν t ^ 2 ≤ w t`, therefore has square-summable samples and converges to zero. This
is the deterministic convergence statement `lim ε(t + 1) = 0` of Theorem 3.2 in
Landau–Lozano–M'Saad–Karimi, *Adaptive Control*, 2nd ed. (Springer 2011).

## Main results

* `paa_adaptation_error_summable_sq`: `ν ^ 2` is summable.
* `paa_adaptation_error_tendsto_zero`: `ν → 0`.
-/

@[expose] public section

open scoped Topology

/-- If a non-negative Lyapunov sequence `V` decreases at least by the non-negative
rate `w` and the adaptation error `ν` satisfies `ν t ^ 2 ≤ w t`, then the squared
adaptation error is summable.

The decay rate is summable by `summable_of_succ_le_sub`, and a non-negative sequence
dominated termwise by a summable sequence is summable
(`Summable.of_nonneg_of_le`). -/
theorem paa_adaptation_error_summable_sq {V w ν : ℕ → ℝ} (hV : ∀ t, 0 ≤ V t)
    (hw : ∀ t, 0 ≤ w t) (hstep : ∀ t, V (t + 1) ≤ V t - w t) (hsq : ∀ t, ν t ^ 2 ≤ w t) :
    Summable (fun t ↦ ν t ^ 2) :=
  Summable.of_nonneg_of_le (fun t ↦ sq_nonneg (ν t)) hsq (summable_of_succ_le_sub hV hw hstep)

/-- PAA adaptation-error convergence: under the Lyapunov dissipation hypotheses of
`paa_adaptation_error_summable_sq`, the adaptation error tends to zero.

Since `ν ^ 2` is summable it tends to zero along `atTop`; taking square roots gives
`|ν| → 0` (`Real.sqrt_sq_eq_abs`), which is equivalent to `ν → 0`
(`tendsto_zero_iff_abs_tendsto_zero`). -/
theorem paa_adaptation_error_tendsto_zero {V w ν : ℕ → ℝ} (hV : ∀ t, 0 ≤ V t)
    (hw : ∀ t, 0 ≤ w t) (hstep : ∀ t, V (t + 1) ≤ V t - w t) (hsq : ∀ t, ν t ^ 2 ≤ w t) :
    Filter.Tendsto ν Filter.atTop (𝓝 0) := by
  have hsqsum : Summable (fun t ↦ ν t ^ 2) :=
    paa_adaptation_error_summable_sq hV hw hstep hsq
  have hsqrt : Filter.Tendsto (fun t ↦ Real.sqrt (ν t ^ 2)) Filter.atTop (𝓝 0) := by
    simpa using hsqsum.tendsto_atTop_zero.sqrt
  have habs : Filter.Tendsto (fun t ↦ |ν t|) Filter.atTop (𝓝 0) := by
    simpa only [Real.sqrt_sq_eq_abs] using hsqrt
  exact (tendsto_zero_iff_abs_tendsto_zero ν).2
    (by simpa only [Function.comp_def] using habs)
