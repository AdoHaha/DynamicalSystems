/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.SlidingMode.Filippov
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.UniformSpace.Ascoli

/-! # Local existence of Filippov solutions

This file develops the elementary local infrastructure for the existence theory of
Filippov differential inclusions `ẋ ∈ F x` in a finite-dimensional real normed space,
following Shtessel, Edwards, Fridman and Levant, *Sliding Mode Control and Observation*,
§2.1. The right-hand side is a set-valued map `F : E → Set E` recorded by
`IsFilippovInclusion`: nonempty, closed and convex values, locally bounded, and upper
semicontinuous.

## Main definitions

* `IsFilippovInclusion.exists_local_bound`: from local boundedness one extracts a radius
  `r > 0` and a uniform bound `M ≥ 0` on `‖v‖` for `v ∈ F y`, `dist y x₀ ≤ r`. This is the
  local a priori bound on the vector field used to build Euler polygonal approximations.
* `IsFilippovInclusion.mem_of_tendsto`: upper semicontinuity together with closed values
  forces the graph `{(x, v) | v ∈ F x}` to be closed. This is the closed-graph form of
  upper semicontinuity used when passing to limits of approximate solutions.
* `IsFilippovInclusion.eventually_mem_add_ball`: the neighbourhood form of one-sided upper
  semicontinuity. The set `⋃ w ∈ F x, ball w ε` is open and contains `F x`, so for `y` near
  `x` every `v ∈ F y` is within `ε` of some point of `F x`.
* `IsFilippovInclusion.isCompact_value`: in finite dimension local boundedness upgrades the
  closed values of a Filippov inclusion to compact values.
* `IsLocallyAbsolutelyContinuousOn.of_lipschitzOn` / `of_lipschitzWith`: Lipschitz curves
  (such as the Euler polygonal approximations and their uniform limit) are locally
  absolutely continuous.

## Main statements

The local existence theorem `exists_filippovSolution_local` itself is *not* proved in this
file yet; see the module note below. It is recorded as the target statement of the
surrounding campaign.

## Implementation notes

The existence proof proceeds through an Euler polygonal scheme: using
`exists_local_bound`, one builds `M`-Lipschitz polygonal curves that satisfy the inclusion
at the polygonal nodes, extracts a uniformly convergent subsequence via the Arzelà–Ascoli
compactness result, and shows that the limit (which is `M`-Lipschitz, hence locally absolutely
continuous) is a Filippov solution. The difficult step is the a.e. identification of the
limit derivative: one averages the polygonal derivatives over a shrinking time window, uses
convexity of `F (γ t)` to keep those averages inside `F (γ t) + ball ε`, and invokes upper
semicontinuity together with closedness of the values (`mem_of_tendsto`, and
`eventually_mem_add_ball`) to pass the inclusion to the limit. Note that one *cannot* use a
uniform-in-a-compact-set form of upper semicontinuity: that statement is false for upper
semicontinuous maps (e.g. `F 0 = [0,1]`, `F x = {0}` for `x ≠ 0` is upper semicontinuous,
but the value `F 0` is not approximated by the small values `F y` for `y` near `0`); upper
semicontinuity only controls `F y` in terms of the fixed value `F x`. Mathlib does not
currently contain an ODE existence theorem that avoids a Lipschitz hypothesis (Peano or
Carathéodory), so this Euler-plus-compactness machinery has to be built on top of the
existing Picard–Lindelöf and Carathéodory–Lipschitz existence theories.

-/

@[expose] public section

open Filter MeasureTheory Set
open scoped NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Local bound for a Filippov inclusion.** For a locally bounded set-valued map, near
any point `x₀` there is a radius `r > 0` and a uniform bound `M ≥ 0` such that every
`v ∈ F y` with `dist y x₀ ≤ r` satisfies `‖v‖ ≤ M`.

This is the local a priori estimate used in the Euler polygonal construction: as long as
the approximate trajectory stays within `dist · x₀ ≤ r`, its slope is bounded by `M`. -/
theorem IsFilippovInclusion.exists_local_bound {F : E → Set E} (hF : IsFilippovInclusion F)
    (x₀ : E) : ∃ r > 0, ∃ M : ℝ, 0 ≤ M ∧ ∀ y, dist y x₀ ≤ r → ∀ v ∈ F y, ‖v‖ ≤ M := by
  obtain ⟨U, hU, hB⟩ := hF.locallyBounded x₀
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hU
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E)).mp hB
  refine ⟨ρ / 2, half_pos hρ, max C 0, le_max_right _ _, ?_⟩
  intro y hy v hv
  have hyU : y ∈ U := hball (by rw [Metric.mem_ball]; linarith)
  have hvU : v ∈ ⋃ z ∈ U, F z := by
    simp only [mem_iUnion]
    exact ⟨y, hyU, hv⟩
  have hbound : dist v (0 : E) ≤ C := hC hvU
  rw [dist_zero_right] at hbound
  exact le_trans hbound (le_max_left _ _)

/-- **Closed graph of a Filippov inclusion.** If `xₙ → x`, `vₙ → v` and `vₙ ∈ F xₙ` for all
`n`, then `v ∈ F x`. Upper semicontinuity supplies, for every open set `U ⊇ F x`, that
`F xₙ ⊆ U` eventually; combined with closedness of `F x` this rules out a limit point
outside `F x`.

This is the closed-graph form of upper semicontinuity, the basic limit tool for the
existence argument: a limit of values of the inclusion along converging states is a value
of the inclusion at the limit state. -/
theorem IsFilippovInclusion.mem_of_tendsto {F : E → Set E} (hF : IsFilippovInclusion F)
    {xs vs : ℕ → E} {x v : E} (hx : Tendsto xs atTop (𝓝 x)) (hv : Tendsto vs atTop (𝓝 v))
    (hmem : ∀ n, vs n ∈ F (xs n)) : v ∈ F x := by
  by_contra hnotmem
  have hne : (F x).Nonempty := hF.nonempty x
  have hδ : 0 < Metric.infDist v (F x) :=
    (hF.isClosed x).notMem_iff_infDist_pos hne |>.mp hnotmem
  set U : Set E := {z | Metric.infDist z (F x) < Metric.infDist v (F x) / 2} with hU_def
  have hU_open : IsOpen U :=
    isOpen_lt (Metric.continuous_infDist_pt (F x)) continuous_const
  have hFU : F x ⊆ U := fun z hz => by
    rw [hU_def, mem_ofPred_eq, Metric.infDist_zero_of_mem hz]
    linarith
  have hev : ∀ᶠ z in 𝓝 x, F z ⊆ U :=
    hF.upperSemicontinuous.forall_isOpen x U hU_open hFU
  have hev_n : ∀ᶠ n in atTop, F (xs n) ⊆ U := hx.eventually hev
  have hmemU : ∀ᶠ n in atTop, vs n ∈ U :=
    hev_n.mono fun n hn => hn (hmem n)
  have hv_closure : v ∈ closure U := mem_closure_of_tendsto hv hmemU
  have hclosed : IsClosed {z : E | Metric.infDist z (F x) ≤ Metric.infDist v (F x) / 2} :=
    isClosed_le (Metric.continuous_infDist_pt (F x)) continuous_const
  have hsub : U ⊆ {z : E | Metric.infDist z (F x) ≤ Metric.infDist v (F x) / 2} :=
    fun z hz => by
      have hz' : Metric.infDist z (F x) < Metric.infDist v (F x) / 2 := by
        rw [hU_def] at hz; simpa using hz
      exact le_of_lt hz'
  have hclsub : closure U ⊆ {z : E | Metric.infDist z (F x) ≤ Metric.infDist v (F x) / 2} :=
    hclosed.closure_subset_iff.mpr hsub
  have hle : Metric.infDist v (F x) ≤ Metric.infDist v (F x) / 2 := hclsub hv_closure
  linarith

/-- **One-sided upper semicontinuity.** For a Filippov inclusion `F`, near any `x` every value
`F y` is contained in the `ε`-neighbourhood of `F x`. Equivalently, each `v ∈ F y` for `y` close
to `x` is within `ε` of some point of `F x`. This is the form of upper semicontinuity used when
showing that the slopes of approximate trajectories are eventually admissible at the limit.

The set `⋃ w ∈ F x, ball w ε` is open and contains `F x`, so upper semicontinuity applies. -/
theorem IsFilippovInclusion.eventually_mem_add_ball {F : E → Set E} (hF : IsFilippovInclusion F)
    {x : E} {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x, ∀ v ∈ F y, ∃ w ∈ F x, dist v w < ε := by
  have hU : IsOpen {v : E | ∃ w ∈ F x, dist v w < ε} := by
    have : {v : E | ∃ w ∈ F x, dist v w < ε} = ⋃ w ∈ F x, Metric.ball w ε := by
      ext v
      simp only [mem_ofPred_eq, mem_iUnion, Metric.mem_ball, exists_prop]
    rw [this]
    exact isOpen_biUnion fun w _ => Metric.isOpen_ball
  have hsub : F x ⊆ {v : E | ∃ w ∈ F x, dist v w < ε} :=
    fun v hv => ⟨v, hv, by simpa using hε⟩
  exact (hF.upperSemicontinuous.forall_isOpen x _ hU hsub).mono fun _ hy v hv => hy hv

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- **Compactness of the values of a Filippov inclusion.** In a finite-dimensional space a
closed and locally bounded set is compact, so local boundedness upgrades the closed values of
a Filippov inclusion to compact values. This is what makes the inclusion well behaved when
taking limits (closed convex hulls of value sets, minimisers, and the like). -/
theorem IsFilippovInclusion.isCompact_value {F : E → Set E} (hF : IsFilippovInclusion F)
    (x : E) : IsCompact (F x) := by
  obtain ⟨U, hU, hB⟩ := hF.locallyBounded x
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hU
  have hxU : x ∈ U := hball (Metric.mem_ball_self hρ)
  have hsub : F x ⊆ ⋃ y ∈ U, F y := fun v hv => by
    simp only [mem_iUnion]
    exact ⟨x, hxU, hv⟩
  exact Metric.isCompact_of_isClosed_isBounded (hF.isClosed x) (hB.subset hsub)

end FiniteDimensional

section AbsoluteContinuous

omit [NormedSpace ℝ E] in
/-- A curve that is Lipschitz on every closed interval `uIcc a b ⊆ s` is locally absolutely
continuous on `s`. This is the regularity transfer used at the limit step of the existence
argument: the Euler polygonal approximations are `M`-Lipschitz, and so is their uniform limit,
which is therefore an admissible Filippov-solution candidate. -/
theorem IsLocallyAbsolutelyContinuousOn.of_lipschitzOn {γ : ℝ → E} {s : Set ℝ} {K : ℝ≥0}
    (h : ∀ a b, Set.uIcc a b ⊆ s → LipschitzOnWith K γ (Set.uIcc a b)) :
    IsLocallyAbsolutelyContinuousOn γ s :=
  fun a b hab => (h a b hab).absolutelyContinuousOnInterval

omit [NormedSpace ℝ E] in
/-- A globally `K`-Lipschitz curve is locally absolutely continuous on every set. -/
theorem IsLocallyAbsolutelyContinuousOn.of_lipschitzWith {γ : ℝ → E} {s : Set ℝ} {K : ℝ≥0}
    (h : LipschitzWith K γ) : IsLocallyAbsolutelyContinuousOn γ s :=
  .of_lipschitzOn fun _ _ _ => h.lipschitzOnWith

end AbsoluteContinuous

/-! ## The remaining target

The statement the existence theory has to establish is

```
  exists_filippovSolution_local [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] {F : E → Set E} (hF : IsFilippovInclusion F) (x₀ : E) :
      ∃ (T : ℝ) (_ : 0 < T) (γ : ℝ → E), γ 0 = x₀ ∧
        IsFilippovSolutionOn γ F (Set.Icc 0 T)
```

The build-up above supplies `exists_local_bound` (the slope bound `M`), `isCompact_value`
(compact values), `mem_of_tendsto` and `eventually_mem_add_ball` (the two limit forms of
upper semicontinuity), and the Lipschitz-to-absolutely-continuous transfers. What is still
missing is the a.e. inclusion of the limit derivative, obtained by averaging the polygonal
derivatives over a shrinking window and using convexity of `F (γ t)`. -/

