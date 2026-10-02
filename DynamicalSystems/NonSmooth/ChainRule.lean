/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.NonSmooth.Clarke
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! # The non-smooth chain rule

For a locally Lipschitz `V : E → ℝ` on a finite-dimensional real normed space and an
absolutely continuous curve `γ : ℝ → E`, the composition `V ∘ γ` is absolutely
continuous, hence differentiable almost everywhere, and at almost every `t` its
derivative is bounded by the support function of the Clarke generalized gradient of
`V` at `γ t`:

`deriv (V ∘ γ) t ≤ sSup ((fun ξ ↦ ξ (deriv γ t)) '' clarkeGradient V (γ t))`.

This is the almost-everywhere form of the Clarke chain rule. The proof decomposes as
follows: `V ∘ γ` is absolutely continuous because `V` is Lipschitz on the compact image
of `γ`; an absolutely continuous function is differentiable a.e. (bounded variation);
and at a point where both `γ` and `V` are differentiable the ordinary chain rule applies,
with the derivative of `V` lying in its Clarke gradient by
`fderiv_mem_clarkeGradient`.

The chain rule is stated under the honest hypothesis `hV_diff`, that `V` is differentiable
at `γ t` for almost every `t`. This is **not** a consequence of the absolute continuity of
`γ`: for `n ≥ 2` the image of an absolutely continuous curve is Lebesgue-null, and a null
image contained in the non-differentiability set of `V` defeats the hypothesis. For example,
with `E = ℝ²`, `V (x₁, x₂) = |x₂|` and `γ t = (t, 0)`, the locally Lipschitz `V` is
non-differentiable at every `γ t`, while `V ∘ γ` is absolutely continuous. The hypothesis is
instead forced by the Fréchet-derivative route taken here: the reduction rewrites the
derivative of `V ∘ γ` through `fderiv ℝ V (γ t)` (via `fderiv_mem_clarkeGradient`), which
requires `V` to be differentiable at `γ t`. Clarke's theorem avoids Fréchet derivatives and
needs no such hypothesis; Mathlib does not currently provide the Clarke-derivative machinery
that would remove it, so it is assumed rather than proved.

## Main statements

* `absolutelyContinuousOnInterval_comp_locallyLipschitz`: `V ∘ γ` is absolutely continuous
  when `V` is locally Lipschitz and `γ` is absolutely continuous.
* `exists_bound_clarkeGradient_apply`: the Clarke generalized gradient has bounded support
  function, so the `sSup` on the right is well behaved.
* `clarke_chain_rule_ae`: the non-smooth chain rule almost everywhere.
-/

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- If `V` is locally Lipschitz and `γ` is absolutely continuous, then `V ∘ γ` is
absolutely continuous: `V` is Lipschitz on the compact image `γ '' uIcc a b`, and a
Lipschitz function precomposed with an absolutely continuous one is absolutely continuous. -/
theorem absolutelyContinuousOnInterval_comp_locallyLipschitz
    {V : E → ℝ} (hV : LocallyLipschitz V) {γ : ℝ → E} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    AbsolutelyContinuousOnInterval (V ∘ γ) a b := by
  have hcompact : IsCompact (γ '' Set.uIcc a b) :=
    isCompact_uIcc.image_of_continuousOn hγ.continuousOn
  obtain ⟨K, hK⟩ :=
    (hV.locallyLipschitzOn (s := γ '' Set.uIcc a b)).exists_lipschitzOnWith_of_compact hcompact
  exact hK.comp_absolutelyContinuousOnInterval (mapsTo_image γ (Set.uIcc a b)) hγ

omit [FiniteDimensional ℝ E] in
/-- The support function of the Clarke generalized gradient is bounded above: for a locally
Lipschitz `V` at `x` there is `M` with `ξ v ≤ M` for every `ξ ∈ clarkeGradient V x`. This is
what makes the `sSup` in the chain rule well behaved. -/
theorem exists_bound_clarkeGradient_apply {V : E → ℝ} (hV : LocallyLipschitz V) (x v : E) :
    ∃ M : ℝ, ∀ ξ ∈ clarkeGradient V x, ξ v ≤ M := by
  obtain ⟨K, t, ht, hK⟩ := hV x
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp ht
  have hK' : LipschitzOnWith K V (Metric.ball x ε) := hK.mono hball
  refine ⟨K * ‖v‖, ?_⟩
  -- Every limit of derivatives of `V` near `x` satisfies the bound, then so does its convex
  -- hull and closure.
  have hKL : {g : E →L[ℝ] ℝ |
      ∃ u : ℕ → E,
        (∀ n, DifferentiableAt ℝ V (u n)) ∧
        Tendsto u atTop (𝓝 x) ∧
        Tendsto (fun n ↦ fderiv ℝ V (u n)) atTop (𝓝 g)} ⊆
      {g : E →L[ℝ] ℝ | g v ≤ K * ‖v‖} := by
    rintro g ⟨u, _hu, hux, hug⟩
    have hle : ∀ᶠ n in atTop, (fderiv ℝ V (u n)) v ≤ K * ‖v‖ := by
      filter_upwards [hux.eventually (Metric.ball_mem_nhds x hε)] with n hn
      have hnorm : ‖fderiv ℝ V (u n)‖ ≤ K :=
        norm_fderiv_le_of_lipschitzOn (𝕜 := ℝ) (Metric.isOpen_ball.mem_nhds hn) hK'
      calc (fderiv ℝ V (u n)) v ≤ ‖(fderiv ℝ V (u n)) v‖ := by
            rw [Real.norm_eq_abs]; exact le_abs_self _
        _ ≤ ‖fderiv ℝ V (u n)‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ K * ‖v‖ := by gcongr
    have hcont : Tendsto (fun n ↦ (fderiv ℝ V (u n)) v) atTop (𝓝 (g v)) :=
      ((ContinuousLinearMap.apply ℝ ℝ v).continuous.tendsto g).comp hug
    exact le_of_tendsto hcont hle
  have hconv : Convex ℝ {g : E →L[ℝ] ℝ | g v ≤ K * ‖v‖} := by
    intro g hg g' hg' a b ha hb hab
    simp only [Set.mem_ofPred_eq] at hg hg' ⊢
    rw [add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
    calc a * (g v) + b * (g' v) ≤ a * (K * ‖v‖) + b * (K * ‖v‖) := by gcongr
      _ = K * ‖v‖ := by rw [← add_mul, hab, one_mul]
  have hclosed : IsClosed {g : E →L[ℝ] ℝ | g v ≤ K * ‖v‖} :=
    isClosed_le (ContinuousLinearMap.apply ℝ ℝ v).continuous continuous_const
  have hC : clarkeGradient V x ⊆ {g : E →L[ℝ] ℝ | g v ≤ K * ‖v‖} := by
    rw [clarkeGradient]
    rw [hclosed.closure_subset_iff]
    exact convexHull_min hKL hconv
  exact fun ξ hξ ↦ hC hξ

/-- **The non-smooth chain rule, almost everywhere.** For a locally Lipschitz `V : E → ℝ`
and an absolutely continuous curve `γ`, the composition `V ∘ γ` is differentiable for
almost every `t` and its derivative is bounded by the support function of the Clarke
generalized gradient of `V` at `γ t`, written as the supremum of `ξ (deriv γ t)` over
`ξ ∈ clarkeGradient V (γ t)`. The hypothesis `hV_diff` records that `V` is
differentiable at `γ t` for almost every `t`; it is forced by the Fréchet-derivative route
taken here (`fderiv_mem_clarkeGradient`) and does not follow from absolute continuity of `γ`
for `n ≥ 2`, whereas Clarke's theorem avoids Fréchet derivatives. -/
theorem clarke_chain_rule_ae {V : E → ℝ} (hV : LocallyLipschitz V) {γ : ℝ → E} {a b : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hV_diff : ∀ᵐ t ∂volume.restrict (Set.uIcc a b), DifferentiableAt ℝ V (γ t)) :
    ∀ᵐ t ∂volume.restrict (Set.uIcc a b),
      DifferentiableAt ℝ (V ∘ γ) t ∧
      deriv (V ∘ γ) t ≤ sSup ((fun ξ ↦ ξ (deriv γ t)) '' clarkeGradient V (γ t)) := by
  have hcomp_ac : AbsolutelyContinuousOnInterval (V ∘ γ) a b :=
    absolutelyContinuousOnInterval_comp_locallyLipschitz hV hγ
  have hcomp : ∀ᵐ t ∂volume.restrict (Set.uIcc a b), DifferentiableAt ℝ (V ∘ γ) t := by
    rw [ae_restrict_iff' measurableSet_uIcc]
    filter_upwards [hcomp_ac.ae_differentiableAt] with t ht hts
    exact ht hts
  have hγdiff : ∀ᵐ t ∂volume.restrict (Set.uIcc a b), DifferentiableAt ℝ γ t := by
    rw [ae_restrict_iff' measurableSet_uIcc]
    filter_upwards [hγ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht hts
    exact ht hts
  filter_upwards [hcomp, hV_diff, hγdiff] with t hcomp hVt hγt
  refine ⟨hcomp, ?_⟩
  have hchain : HasDerivAt (V ∘ γ) (fderiv ℝ V (γ t) (deriv γ t)) t :=
    hVt.hasFDerivAt.comp_hasDerivAt t hγt.hasDerivAt
  rw [hchain.deriv]
  have hmem : fderiv ℝ V (γ t) ∈ clarkeGradient V (γ t) := fderiv_mem_clarkeGradient hVt
  obtain ⟨M, hM⟩ := exists_bound_clarkeGradient_apply hV (γ t) (deriv γ t)
  have hbdd : BddAbove ((fun ξ : E →L[ℝ] ℝ ↦ ξ (deriv γ t)) ''
      clarkeGradient V (γ t)) := by
    refine ⟨M, ?_⟩
    rintro w ⟨ξ, hξ, rfl⟩
    exact hM ξ hξ
  exact le_csSup hbdd (mem_image_of_mem (fun ξ : E →L[ℝ] ℝ ↦ ξ (deriv γ t)) hmem)
