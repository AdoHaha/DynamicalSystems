/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.Calculus.Barbalat
public import DynamicalSystems.Stability.Lyapunov
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Barbălat's lemma for the Hou–Duan–Guo adaptive control system

This file applies Barbălat's lemma to the adaptive control system of
[Hou-Duan-Guo, Example 3.1], which is reproduced as Example 10 in
[Farkas-Wegner2016]. The system is

```
e'(t) = -e(t) + θ(t) ω(t)
θ'(t) = -e(t) ω(t)
```

with `ω` continuous and bounded on `[0, ∞)`. The Lyapunov function `V = e² + θ²` satisfies
`V' = -2 e² ≤ 0` along solutions, so `V` is nonincreasing, `e` and `θ` are bounded,
and the primitive `t ↦ ∫ x in 0..t, e x ^ 2` is nondecreasing and bounded by `V 0`.
Hence `e ^ 2` has a convergent improper integral and, being Lipschitz on `[0, ∞)` because
the derivative `2 e e'` is bounded, it is uniformly continuous. Barbălat's lemma then
yields `e² → 0`, hence `e → 0`.

The ordinary differential equations are taken as hypotheses, together with the
differentiability they assert; no existence or uniqueness of trajectories is formalized.

## Main statements

* `Barbalat.adaptiveControl_error_tendsto_zero`: for any trajectory `(e, θ)` of the
  Hou–Duan–Guo system with `ω` continuous and bounded on `[0, ∞)`, the error `e t`
  tends to `0` as `t → ∞`.

## References

* [B. Farkas and S.-A. Wegner, *Variations on Barbălat's Lemma*][Farkas-Wegner2016]
* M. Hou, G. Duan, L. Guo, *New versions of Barbălat's lemma with applications*,
  J. Control Theory Appl. (2010).

[Farkas-Wegner2016]: https://arxiv.org/abs/1411.1611
-/

@[expose] public noncomputable section

open Filter Set MeasureTheory
open scoped Topology

namespace Barbalat

-- `hx` belongs to the flow-level interface but is not needed by the scalar bridge lemma, which
-- only uses the nonnegativity supplied by `h.pos`.
set_option linter.unusedVariables false

/-- **Lyapunov/Barbălat bridge.** Let `v` be a Lyapunov function for the flow `Φ` on a set `s`,
let `x` be a point whose trajectory stays in `s` for `t ≥ 0`, and let `w : ℝ → ℝ` be the decay
rate along the trajectory: `t ↦ v (Φ t x)` has derivative `-w t` for every `t ≥ 0`. If `w` is
nonnegative and uniformly continuous on `[0, ∞)`, then `w t → 0` as `t → ∞`.

`IsLyapunovOn` supplies the nonnegativity of `t ↦ v (Φ t x)` through `IsLyapunovOn.pos`. This
refines `IsLyapunovOn.exists_tendsto`, which only gives convergence of the Lyapunov function
`t ↦ v (Φ t x)` to *some* limit: here the limit of the decay rate `w`, not just of `v ∘ Φ`, is
identified as `0`. This is the flow-level form of
`Barbalat.tendsto_zero_of_hasDerivAt_neg_of_nonneg_of_uniformContinuousOn`. -/
@[nolint unusedArguments]
theorem tendsto_zero_of_isLyapunovOn_of_hasDerivAt_neg
    {E : Type*} [TopologicalSpace E]
    {v : E → ℝ} {Φ : ℝ → E → E} {s : Set E} {x : E} (h : IsLyapunovOn v Φ s)
    (hx : ∀ t, 0 ≤ t → Φ t x ∈ s) {w : ℝ → ℝ} (hw : ∀ t, 0 ≤ t → 0 ≤ w t)
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt (fun s ↦ v (Φ s x)) (-(w t)) t)
    (huc : UniformContinuousOn w (Set.Ici 0)) : Tendsto w atTop (𝓝 0) :=
  tendsto_zero_of_hasDerivAt_neg_of_nonneg_of_uniformContinuousOn
    (fun t _ ↦ h.pos (Φ t x)) hw hderiv huc

set_option linter.unusedVariables true

/-- **Example 10 of Farkas–Wegner** (Hou–Duan–Guo adaptive control). Let
`e θ ω : ℝ → ℝ` satisfy the adaptive control equations
`e'(t) = -e(t) + θ(t) ω(t)` and `θ'(t) = -e(t) ω(t)` for all `t ≥ 0`, with `ω`
continuous on `[0, ∞)` and bounded there. Then the error `e t` tends to `0` as
`t → ∞`.

The ODEs and the differentiability they assert are hypotheses; only the asymptotic
behaviour of the trajectory is proved. -/
theorem adaptiveControl_error_tendsto_zero
    {e theta omega : ℝ → ℝ}
    (hω : ContinuousOn omega (Set.Ici 0) ∧
      ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → |omega t| ≤ C)
    (he : ∀ t : ℝ, 0 ≤ t → HasDerivAt e (-e t + theta t * omega t) t)
    (hθ : ∀ t : ℝ, 0 ≤ t → HasDerivAt theta (-(e t) * omega t) t) :
    Tendsto e atTop (𝓝 0) := by
  obtain ⟨Cω, hCω⟩ := hω.2
  have hCω_nonneg : 0 ≤ Cω := le_trans (abs_nonneg (omega 0)) (hCω 0 le_rfl)
  -- The Lyapunov function `V = e ^ 2 + theta ^ 2`.
  let V : ℝ → ℝ := fun t ↦ e t ^ 2 + theta t ^ 2
  have hVnonneg : ∀ t : ℝ, 0 ≤ V t := by
    intro t
    change 0 ≤ e t ^ 2 + theta t ^ 2
    nlinarith [sq_nonneg (e t), sq_nonneg (theta t)]
  -- `V` is differentiable on the half-line, with derivative `-2 e ^ 2`.
  have hVderiv : ∀ t : ℝ, 0 ≤ t → HasDerivAt V (-(2 * e t ^ 2)) t := by
    intro t ht
    have h1 : HasDerivAt (fun s : ℝ ↦ e s ^ 2)
        (2 * e t * (-e t + theta t * omega t)) t := by
      refine HasDerivAt.congr_deriv ((he t ht).pow 2) ?_
      ring_nf
    have h2 : HasDerivAt (fun s : ℝ ↦ theta s ^ 2)
        (2 * theta t * (-(e t) * omega t)) t := by
      refine HasDerivAt.congr_deriv ((hθ t ht).pow 2) ?_
      ring_nf
    change HasDerivAt (fun s : ℝ ↦ e s ^ 2 + theta s ^ 2) (-(2 * e t ^ 2)) t
    exact HasDerivAt.congr_deriv (HasDerivAt.add h1 h2) (by ring)
  have hcont_e : ContinuousOn e (Set.Ici 0) :=
    fun x hx ↦ (he x hx).continuousAt.continuousWithinAt
  have hcont_θ : ContinuousOn theta (Set.Ici 0) :=
    fun x hx ↦ (hθ x hx).continuousAt.continuousWithinAt
  -- **Step 1.** `V` is nonincreasing on `[0, ∞)`.
  have hVanti : AntitoneOn V (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
    · change ContinuousOn (fun t : ℝ ↦ e t ^ 2 + theta t ^ 2) (Set.Ici 0)
      exact (hcont_e.pow 2).add (hcont_θ.pow 2)
    · intro x hx
      rw [interior_Ici] at hx ⊢
      have hx0 : 0 ≤ x := le_of_lt hx
      change DifferentiableWithinAt ℝ (fun t : ℝ ↦ e t ^ 2 + theta t ^ 2) (Set.Ioi 0) x
      exact (((he x hx0).pow 2).add ((hθ x hx0).pow 2)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hx0 : 0 ≤ x := le_of_lt hx
      rw [(hVderiv x hx0).deriv]
      nlinarith [sq_nonneg (e x)]
  have hVle : ∀ t : ℝ, 0 ≤ t → V t ≤ V 0 :=
    fun t ht ↦ hVanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  -- **Step 2.** Boundedness of `e` and `theta`.
  have he_sq_le : ∀ t : ℝ, 0 ≤ t → e t ^ 2 ≤ V 0 := by
    intro t ht
    have h1 : e t ^ 2 ≤ V t := by
      change e t ^ 2 ≤ e t ^ 2 + theta t ^ 2
      nlinarith [sq_nonneg (theta t)]
    exact le_trans h1 (hVle t ht)
  have hθ_sq_le : ∀ t : ℝ, 0 ≤ t → theta t ^ 2 ≤ V 0 := by
    intro t ht
    have h1 : theta t ^ 2 ≤ V t := by
      change theta t ^ 2 ≤ e t ^ 2 + theta t ^ 2
      nlinarith [sq_nonneg (e t)]
    exact le_trans h1 (hVle t ht)
  let A : ℝ := Real.sqrt (V 0)
  have hA : 0 ≤ A := Real.sqrt_nonneg (V 0)
  have he_abs_le : ∀ t : ℝ, 0 ≤ t → |e t| ≤ A := by
    intro t ht
    have h := Real.sqrt_le_sqrt (he_sq_le t ht)
    rwa [Real.sqrt_sq_eq_abs] at h
  have hθ_abs_le : ∀ t : ℝ, 0 ≤ t → |theta t| ≤ A := by
    intro t ht
    have h := Real.sqrt_le_sqrt (hθ_sq_le t ht)
    rwa [Real.sqrt_sq_eq_abs] at h
  -- **Step 3.** A uniform bound for the derivative of `e ^ 2`.
  let B : ℝ := A + A * Cω
  let M : ℝ := 2 * A * B
  have hB : 0 ≤ B := add_nonneg hA (mul_nonneg hA hCω_nonneg)
  have hM : 0 ≤ M := mul_nonneg (mul_nonneg (by norm_num) hA) hB
  have hderiv_e2 : ∀ x : ℝ, 0 ≤ x →
      deriv (fun t : ℝ ↦ e t ^ 2) x = 2 * e x * (-e x + theta x * omega x) := by
    intro x hx
    have h2 : HasDerivAt (fun t : ℝ ↦ e t ^ 2)
        (2 * e x * (-e x + theta x * omega x)) x := by
      refine HasDerivAt.congr_deriv ((he x hx).pow 2) ?_
      ring_nf
    exact h2.deriv
  have hderiv_bound : ∀ x ∈ Set.Ici (0 : ℝ),
      ‖deriv (fun t : ℝ ↦ e t ^ 2) x‖ ≤ M := by
    intro x hx
    rw [hderiv_e2 x hx, Real.norm_eq_abs]
    have he1 : |e x| ≤ A := he_abs_le x hx
    have hθ1 : |theta x| ≤ A := hθ_abs_le x hx
    have hx_ω : |omega x| ≤ Cω := hCω x hx
    have hinside : |(-e x + theta x * omega x)| ≤ B := by
      calc |(-e x + theta x * omega x)|
          ≤ |-e x| + |theta x * omega x| := abs_add_le _ _
        _ = |e x| + |theta x| * |omega x| := by rw [abs_neg, abs_mul]
        _ ≤ A + A * Cω := add_le_add he1 (mul_le_mul hθ1 hx_ω (abs_nonneg _) hA)
        _ = B := rfl
    calc |2 * e x * (-e x + theta x * omega x)|
        = 2 * |e x| * |(-e x + theta x * omega x)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ 2 * A * B := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left he1 (by norm_num)) hinside
            (abs_nonneg _) (mul_nonneg (by norm_num) hA)
      _ = M := rfl
  -- **Step 4.** `e ^ 2` is uniformly continuous on `[0, ∞)`.
  have huc : UniformContinuousOn (fun t : ℝ ↦ e t ^ 2) (Set.Ici 0) := by
    have hderiv : ∀ z ∈ Set.Ici (0 : ℝ),
        DifferentiableAt ℝ (fun t : ℝ ↦ e t ^ 2) z :=
      fun z hz ↦ ((he z hz).pow 2).differentiableAt
    have hbound : ∀ z ∈ Set.Ici (0 : ℝ),
        ‖deriv (fun t : ℝ ↦ e t ^ 2) z‖₊ ≤ ⟨M, hM⟩ :=
      fun z hz ↦ by exact_mod_cast hderiv_bound z hz
    exact (Convex.lipschitzOnWith_of_nnnorm_deriv_le hderiv hbound
      (convex_Ici 0)).uniformContinuousOn
  -- **Step 5.** Apply the Lyapunov/Barbălat bridge to `V` and the decay rate `w = 2 * e ^ 2`.
  have hw_nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ 2 * e t ^ 2 := fun _ _ ↦ by positivity
  have hw_uc : UniformContinuousOn (fun t : ℝ ↦ 2 * e t ^ 2) (Set.Ici 0) :=
    (Real.uniformContinuous_const_mul (x := 2)).comp_uniformContinuousOn huc
  have hw_tend : Tendsto (fun t : ℝ ↦ 2 * e t ^ 2) atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_neg_of_nonneg_of_uniformContinuousOn (fun t _ ↦ hVnonneg t)
      hw_nonneg hVderiv hw_uc
  -- **Step 6.** Halve the decay rate and extract `e → 0`.
  have hmain : Tendsto (fun t : ℝ ↦ e t ^ 2) atTop (𝓝 0) := by
    have hfun : (fun t : ℝ ↦ (1 / 2) * (2 * e t ^ 2)) = fun t : ℝ ↦ e t ^ 2 := by
      funext t
      ring
    have h := hw_tend.const_mul (1 / 2)
    rw [hfun, mul_zero] at h
    exact h
  have habs : Tendsto (fun t : ℝ ↦ |e t|) atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun t : ℝ ↦ Real.sqrt (e t ^ 2)) atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hmain
      rw [Real.sqrt_zero] at h
      exact h
    simpa only [Real.sqrt_sq_eq_abs] using hsqrt
  rw [Metric.tendsto_nhds] at habs ⊢
  intro ε hε
  filter_upwards [habs ε hε] with t ht
  simpa only [Real.dist_eq, sub_zero, abs_abs] using ht

/-- **The Slotine–Li theorem** (Kabziński–Mosiołek, Theorem 3.6, scalar trajectory form).
Let `V : ℝ → ℝ` be bounded below, differentiable on `[0, ∞)` with nonpositive derivative
`deriv V` there, and suppose that the decay rate `deriv V` is uniformly continuous on
`[0, ∞)`. Then `deriv V t → 0` as `t → ∞`.

The book's assumption is only that the candidate `V` is bounded below (forward in time, on
`[0, ∞)`), whereas the core Barbălat lemma
`tendsto_zero_of_hasDerivAt_neg_of_nonneg_of_uniformContinuousOn` requires it to be
nonnegative. Subtracting a lower bound `c` from `V` produces the nonnegative
`V' = V - c` with the same derivative `deriv V`, and the decay rate `w = -deriv V` is
nonnegative, uniformly continuous, and has `V'` as an antiderivative there; applying the core
lemma to `V'` and `w` and negating the conclusion gives the result. -/
theorem tendsto_deriv_zero_of_boundedBelow_of_uniformContinuousOn
    {V : ℝ → ℝ} (hV : BddBelow (V '' Set.Ici 0))
    (hderiv : ∀ t, 0 ≤ t → HasDerivAt V (deriv V t) t)
    (hmono : ∀ t, 0 ≤ t → deriv V t ≤ 0)
    (huc : UniformContinuousOn (deriv V) (Set.Ici 0)) :
    Tendsto (deriv V) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := hV
  have hc' : ∀ t : ℝ, 0 ≤ t → c ≤ V t :=
    fun t ht ↦ hc (mem_image_of_mem V ht)
  let V' : ℝ → ℝ := fun t ↦ V t - c
  let w : ℝ → ℝ := fun t ↦ -(deriv V t)
  have hV'nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ V' t := fun t ht ↦ sub_nonneg.mpr (hc' t ht)
  have hw_nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ w t := fun t ht ↦ neg_nonneg.mpr (hmono t ht)
  have hV'deriv : ∀ t : ℝ, 0 ≤ t → HasDerivAt V' (-(w t)) t := by
    intro t ht
    simpa only [V', w, neg_neg] using (hderiv t ht).sub_const c
  have hw_uc : UniformContinuousOn w (Set.Ici 0) :=
    Real.uniformContinuous_neg.comp_uniformContinuousOn huc
  have hw_tend : Tendsto w atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_neg_of_nonneg_of_uniformContinuousOn
      hV'nonneg hw_nonneg hV'deriv hw_uc
  have hneg : Tendsto (fun t : ℝ ↦ -w t) atTop (𝓝 0) := by
    simpa using hw_tend.neg
  have hfun : (fun t : ℝ ↦ -w t) = deriv V := by
    funext t
    simp only [w, neg_neg]
  rwa [hfun] at hneg

/-- **Quadratic squeeze.** If `w → 0` and `c * (e t) ^ 2 ≤ w t` for all `t ≥ 0` with `c > 0`,
then `e → 0`.

This is the form in which Barbălat-type conclusions are consumed: a Lyapunov argument
establishes `V̇ ≤ -(c * ‖e‖ ^ 2)` and hence `c * (e t) ^ 2 ≤ w t` for the decay rate `w`, and this
lemma turns `w → 0` into `e → 0`. On `t ≥ 0` the hypothesis gives
`0 ≤ (e t) ^ 2 ≤ w t / c`, so `(e t) ^ 2 → 0` by squeezing against the convergent `w t / c`; taking
square roots via `Real.sqrt_sq_eq_abs` yields `|e t| → 0`, hence `e t → 0`. -/
theorem tendsto_zero_of_tendsto_zero_of_sq_le {e w : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hw : Tendsto w atTop (𝓝 0)) (hle : ∀ t, 0 ≤ t → c * (e t) ^ 2 ≤ w t) :
    Tendsto e atTop (𝓝 0) := by
  have hsq : Tendsto (fun t : ℝ ↦ (e t) ^ 2) atTop (𝓝 0) := by
    have hwdiv : Tendsto (fun t : ℝ ↦ w t / c) atTop (𝓝 0) := by
      simpa using hw.div_const c
    refine squeeze_zero' (Eventually.of_forall fun t ↦ sq_nonneg (e t)) ?_ hwdiv
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    rw [le_div_iff₀ hc]
    simpa only [mul_comm] using hle t ht
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have habs : Tendsto (fun t : ℝ ↦ |e t|) atTop (𝓝 0) := by
    have hsqrt : Tendsto (fun t : ℝ ↦ Real.sqrt ((e t) ^ 2)) atTop (𝓝 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).comp hsq
      rwa [Real.sqrt_zero] at h
    simpa only [Real.sqrt_sq_eq_abs] using hsqrt
  simpa only [Real.norm_eq_abs] using habs

end Barbalat
