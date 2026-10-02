/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Data.Set.Insert

/-! # The Clarke generalized gradient

For a function `f : E → ℝ` on a real normed space and a point `x : E`, the
**Clarke generalized gradient** is the closed convex hull of the limits of the
Fréchet derivatives `∇f(xₙ)` along sequences `xₙ → x` of differentiability
points. It is the standard substitute for the gradient when `f` is locally
Lipschitz but not differentiable: by Rademacher's theorem such an `f` is
differentiable almost everywhere on a finite-dimensional space, so
differentiability points are dense and the limit set is nonempty.

The definition is stated for an arbitrary normed space and an arbitrary `f`.
Local Lipschitzness and finite dimensionality are not used by the closure,
convexity and derivative-reduction statements below; they enter only when one
wants Rademacher's theorem to guarantee that the limit set is nonempty and to
recover the usual non-smooth calculus (chain rule, Lyapunov arguments).

## Main definitions

* `clarkeGradient f x`: the closed convex hull of the limits of `fderiv ℝ f`
  along differentiability points converging to `x`.

## Main statements

* `clarkeGradient_isClosed`: the Clarke generalized gradient is closed.
* `clarkeGradient_convex`: the Clarke generalized gradient is convex.
* `clarkeGradient_of_hasFDerivAt`: if `f` has Fréchet derivative `f'` at `x`
  and `fderiv ℝ f` is continuous at `x`, then the Clarke generalized gradient at
  `x` is the singleton `{f'}`.

## Implementation notes

The continuity hypothesis in `clarkeGradient_of_hasFDerivAt` cannot be dropped,
so it is kept. For the locally Lipschitz function `f y = y ^ 2 * Real.sin y⁻¹`
(with `f 0 = 0`) one has `HasFDerivAt f 0 0`, but `fderiv ℝ f` has no limit at
`0` and the Clarke generalized gradient at `0` is the interval `[-1, 1]`, not
`{0}`.
-/

@[expose] public section

open Filter Set

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **Clarke generalized gradient** of `f : E → ℝ` at `x : E`: the closure
of the convex hull of the limits of `fderiv ℝ f (u n)` along sequences `u n` of
differentiability points tending to `x`. -/
noncomputable def clarkeGradient (f : E → ℝ) (x : E) : Set (E →L[ℝ] ℝ) :=
  closure (convexHull ℝ {g : E →L[ℝ] ℝ |
    ∃ u : ℕ → E,
      (∀ n, DifferentiableAt ℝ f (u n)) ∧
      Tendsto u atTop (𝓝 x) ∧
      Tendsto (fun n ↦ fderiv ℝ f (u n)) atTop (𝓝 g)})

/-- The Clarke generalized gradient is closed, being the closure of a set. -/
theorem clarkeGradient_isClosed (f : E → ℝ) (x : E) : IsClosed (clarkeGradient f x) := by
  unfold clarkeGradient
  exact isClosed_closure

/-- The Clarke generalized gradient is convex, being the closure of the convex
hull of the limit set. -/
theorem clarkeGradient_convex (f : E → ℝ) (x : E) : Convex ℝ (clarkeGradient f x) := by
  unfold clarkeGradient
  exact (convex_convexHull ℝ _).closure

/-- At a differentiability point `x`, the Fréchet derivative `fderiv ℝ f x`
belongs to the Clarke generalized gradient at `x`; the constant sequence at `x`
witnesses it. -/
theorem fderiv_mem_clarkeGradient {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ f x ∈ clarkeGradient f x := by
  unfold clarkeGradient
  apply subset_closure
  apply subset_convexHull
  exact ⟨fun _ ↦ x, fun _ ↦ hf, tendsto_const_nhds, tendsto_const_nhds⟩

/-- If `f` has Fréchet derivative `f'` at `x` and `fderiv ℝ f` is continuous at
`x`, then the Clarke generalized gradient of `f` at `x` is the singleton `{f'}`.

The continuity hypothesis is necessary: `HasFDerivAt` alone does not prevent the
nearby derivatives from having further limit points. -/
theorem clarkeGradient_of_hasFDerivAt {f : E → ℝ} {x : E} {f' : E →L[ℝ] ℝ}
    (hf : HasFDerivAt f f' x) (hcont : ContinuousAt (fderiv ℝ f) x) :
    clarkeGradient f x = {f'} := by
  have hfderiv : fderiv ℝ f x = f' := hf.fderiv
  have hS : {g : E →L[ℝ] ℝ |
      ∃ u : ℕ → E,
        (∀ n, DifferentiableAt ℝ f (u n)) ∧
        Tendsto u atTop (𝓝 x) ∧
        Tendsto (fun n ↦ fderiv ℝ f (u n)) atTop (𝓝 g)} = {f'} := by
    rw [Set.eq_singleton_iff_unique_mem]
    refine ⟨?_, ?_⟩
    · exact ⟨fun _ ↦ x, fun _ ↦ hf.differentiableAt, tendsto_const_nhds, by simp [hfderiv]⟩
    · rintro g ⟨u, _hu, hut, hug⟩
      have hlim : Tendsto (fun n ↦ fderiv ℝ f (u n)) atTop (𝓝 (fderiv ℝ f x)) :=
        hcont.tendsto.comp hut
      rw [hfderiv] at hlim
      exact tendsto_nhds_unique hug hlim
  unfold clarkeGradient
  rw [hS, convexHull_singleton, closure_singleton]
