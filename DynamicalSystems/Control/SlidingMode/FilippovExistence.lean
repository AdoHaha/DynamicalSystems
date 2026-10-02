/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.SlidingMode.Filippov
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.MetricSpace.UniformConvergence
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.UniformSpace.UniformConvergence

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
open scoped NNReal Topology BigOperators

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

section Euler

omit [NormedSpace ℝ E] in
/-- A pointwise limit of `K`-Lipschitz maps is `K`-Lipschitz. This is the closure step that
upgrades the uniformly convergent Euler polygonal approximations to a Lipschitz (hence locally
absolutely continuous) limit curve. -/
theorem LipschitzWith.of_tendsto {α : Type*} [PseudoMetricSpace α]
    {K : ℝ≥0} {f : ℕ → α → E} {g : α → E} (hf : ∀ n, LipschitzWith K (f n))
    (h : ∀ x, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) : LipschitzWith K g := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  have htend : Tendsto (fun n ↦ dist (f n x) (f n y)) atTop (𝓝 (dist (g x) (g y))) :=
    (h x).dist (h y)
  exact le_of_tendsto htend (Eventually.of_forall fun n ↦ (hf n).dist_le_mul x y)

/-- **Euler nodes.** For a fixed step `h` the polygonal Euler scheme starting at `x₀` selects an
admissible velocity `v k ∈ F (x k)` at each node and advances `x (k+1) = x k + h • v k`. The
choice is classical; the resulting sequence is the sequence of vertices of the Euler polygonal
approximation used in the existence proof. -/
noncomputable def IsFilippovInclusion.eulerNode {F : E → Set E} (hF : IsFilippovInclusion F)
    (h : ℝ) (x₀ : E) : ℕ → E
  | 0 => x₀
  | k + 1 => eulerNode hF h x₀ k + h • Classical.choose (hF.nonempty (eulerNode hF h x₀ k))

/-- **The velocity selected at an Euler node**, packaged as a function of the node index. -/
noncomputable def IsFilippovInclusion.eulerVel {F : E → Set E} (hF : IsFilippovInclusion F)
    (h : ℝ) (x₀ : E) (k : ℕ) : E :=
  Classical.choose (hF.nonempty (eulerNode hF h x₀ k))

/-- The velocity selected at the `k`-th Euler node lies in `F` applied to that node. -/
theorem IsFilippovInclusion.eulerNode_choose_mem {F : E → Set E} (hF : IsFilippovInclusion F)
    (h : ℝ) (x₀ : E) (k : ℕ) : eulerVel hF h x₀ k ∈ F (eulerNode hF h x₀ k) :=
  Classical.choose_spec _

/-- The successor Euler node is the previous node plus `h` times the selected velocity. -/
theorem IsFilippovInclusion.eulerNode_succ {F : E → Set E} (hF : IsFilippovInclusion F)
    (h : ℝ) (x₀ : E) (k : ℕ) :
    eulerNode hF h x₀ (k + 1) = eulerNode hF h x₀ k + h • eulerVel hF h x₀ k :=
  rfl

/-- **Euler node a priori estimate.** If all velocities in `F` are bounded by `M` on the closed
ball of radius `r` about `x₀`, then as long as `k * h * M ≤ r` the `k`-th Euler node stays within
distance `k * h * M` of `x₀`. This is the discrete Gronwall estimate that keeps the polygonal
approximation inside the ball of local boundedness for times `t ≤ r / M`. -/
theorem IsFilippovInclusion.dist_eulerNode_le {F : E → Set E} (hF : IsFilippovInclusion F)
    {x₀ : E} {r M h : ℝ} (hh : 0 ≤ h) (hM0 : 0 ≤ M)
    (hM : ∀ y, dist y x₀ ≤ r → ∀ v ∈ F y, ‖v‖ ≤ M) :
    ∀ k : ℕ, (k : ℝ) * h * M ≤ r →
      dist (eulerNode hF h x₀ k) x₀ ≤ (k : ℝ) * h * M := by
  intro k
  induction k with
  | zero =>
      intro _
      simp [eulerNode]
  | succ k ih =>
      intro hk
      have hk' : (k : ℝ) * h * M ≤ r := by
        have hle : (k : ℝ) * h * M ≤ ((k + 1 : ℕ) : ℝ) * h * M := by
          have : (0 : ℝ) ≤ h * M := mul_nonneg hh hM0
          push_cast
          nlinarith
        exact le_trans hle hk
      have hdist : dist (eulerNode hF h x₀ k) x₀ ≤ r := le_trans (ih hk') hk'
      have hvnorm : ‖Classical.choose (hF.nonempty (eulerNode hF h x₀ k))‖ ≤ M :=
        hM _ hdist _ (hF.eulerNode_choose_mem h x₀ k)
      rw [eulerNode]
      calc dist (eulerNode hF h x₀ k +
              h • Classical.choose (hF.nonempty (eulerNode hF h x₀ k))) x₀
          ≤ dist (eulerNode hF h x₀ k) x₀ +
              ‖h • Classical.choose (hF.nonempty (eulerNode hF h x₀ k))‖ := by
            calc dist (eulerNode hF h x₀ k +
                    h • Classical.choose (hF.nonempty (eulerNode hF h x₀ k))) x₀
                ≤ dist (eulerNode hF h x₀ k +
                    h • Classical.choose (hF.nonempty (eulerNode hF h x₀ k)))
                    (eulerNode hF h x₀ k) + dist (eulerNode hF h x₀ k) x₀ :=
                  dist_triangle _ _ _
              _ = ‖h • Classical.choose (hF.nonempty (eulerNode hF h x₀ k))‖ +
                    dist (eulerNode hF h x₀ k) x₀ := by
                  rw [dist_eq_norm]
                  simp
              _ = dist (eulerNode hF h x₀ k) x₀ +
                    ‖h • Classical.choose (hF.nonempty (eulerNode hF h x₀ k))‖ := by
                  ring
        _ ≤ (k : ℝ) * h * M + h * M := by
            gcongr
            · exact ih hk'
            · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
              gcongr
        _ = ((k + 1 : ℕ) : ℝ) * h * M := by
            push_cast
            ring

/-- **The Euler step velocity.** The piecewise-constant velocity driving the Euler scheme: at
time `t` it is the velocity selected at the Euler node `⌊t / h⌋₊`. This is the right-hand side
of the Euler differential equation `γ' = v` on each step. -/
noncomputable def IsFilippovInclusion.eulerVelStep {F : E → Set E} (hF : IsFilippovInclusion F)
    (h : ℝ) (x₀ : E) (t : ℝ) : E :=
  eulerVel hF h x₀ ⌊t / h⌋₊

/-- The Euler step velocity at time `t` lies in `F` at the corresponding Euler node. -/
theorem IsFilippovInclusion.eulerVelStep_mem {F : E → Set E} (hF : IsFilippovInclusion F)
    (h : ℝ) (x₀ : E) (t : ℝ) :
    eulerVelStep hF h x₀ t ∈ F (eulerNode hF h x₀ ⌊t / h⌋₊) :=
  eulerNode_choose_mem hF h x₀ ⌊t / h⌋₊

/-- **Constancy of the Euler step velocity on a step.** For `h > 0` and `t ∈ [k * h, (k+1) * h)`
the step velocity is the velocity selected at the `k`-th node. The endpoint `(k+1) * h` is excluded
only; it is a single point and hence is irrelevant for the associated interval integral. -/
theorem IsFilippovInclusion.eulerVelStep_eq {F : E → Set E} (hF : IsFilippovInclusion F)
    {h : ℝ} (hh : 0 < h) (x₀ : E) {t : ℝ} {k : ℕ}
    (hlo : (k : ℝ) * h ≤ t) (hhi : t < ((k : ℝ) + 1) * h) :
    eulerVelStep hF h x₀ t = eulerVel hF h x₀ k := by
  have hk : ⌊t / h⌋₊ = k := by
    have hk0 : (0 : ℝ) ≤ t / h :=
      div_nonneg (le_trans (mul_nonneg (Nat.cast_nonneg k) (le_of_lt hh)) hlo) (le_of_lt hh)
    rw [Nat.floor_eq_iff hk0]
    exact ⟨(le_div_iff₀ hh).mpr hlo, (div_lt_iff₀ hh).mpr hhi⟩
  simp only [eulerVelStep]
  rw [hk]

/-- **A priori bound on the Euler step velocity.** On the steps that stay within the ball of local
boundedness (`⌊t / h⌋₊ * h * M ≤ r`) the Euler step velocity is bounded by `M`. -/
theorem IsFilippovInclusion.norm_eulerVelStep_le {F : E → Set E} (hF : IsFilippovInclusion F)
    {x₀ : E} {r M h : ℝ} (hh : 0 < h) (hM0 : 0 ≤ M)
    (hM : ∀ y, dist y x₀ ≤ r → ∀ v ∈ F y, ‖v‖ ≤ M)
    {t : ℝ} (hk : (⌊t / h⌋₊ : ℝ) * h * M ≤ r) :
    ‖eulerVelStep hF h x₀ t‖ ≤ M := by
  have hdist : dist (eulerNode hF h x₀ ⌊t / h⌋₊) x₀ ≤ r :=
    le_trans (hF.dist_eulerNode_le (le_of_lt hh) hM0 hM _ hk) hk
  exact hM _ hdist _ (hF.eulerVelStep_mem h x₀ t)

/-- **The Euler polygonal curve.** The piecewise-linear interpolation of the Euler nodes
`eulerNode hF h x₀ k`, evaluated at time `t` on the step `k = ⌊t / h⌋₊` and glued continuously at
the nodes. This is the approximation whose uniform limits (after Arzelà–Ascoli) are the
candidates for a Filippov solution. -/
noncomputable def IsFilippovInclusion.eulerCurve {F : E → Set E} (hF : IsFilippovInclusion F)
    (h : ℝ) (x₀ : E) (t : ℝ) : E :=
  let k := ⌊t / h⌋₊
  eulerNode hF h x₀ k +
    ((t - (k : ℝ) * h) / h) • (eulerNode hF h x₀ (k + 1) - eulerNode hF h x₀ k)

/-- The Euler polygonal curve starts at `x₀`. -/
theorem IsFilippovInclusion.eulerCurve_zero {F : E → Set E} (hF : IsFilippovInclusion F)
    (h : ℝ) (x₀ : E) : eulerCurve hF h x₀ 0 = x₀ := by
  simp [eulerCurve, eulerNode]

/-- At a node `j * h` the Euler polygonal curve takes the value of the `j`-th Euler node. -/
theorem IsFilippovInclusion.eulerCurve_node {F : E → Set E} (hF : IsFilippovInclusion F)
    {h : ℝ} (hh : 0 < h) (x₀ : E) (j : ℕ) :
    eulerCurve hF h x₀ ((j : ℝ) * h) = eulerNode hF h x₀ j := by
  have hjh : (j : ℝ) * h / h = (j : ℝ) := by field_simp
  simp only [eulerCurve, hjh, Nat.floor_natCast]
  ring_nf
  simp

/-- **The Euler polygonal curve is differentiable on each open step**, with derivative the Euler
velocity selected at the corresponding node. On the open interval
`(k * h, (k+1) * h)` the floor `⌊t / h⌋₊` is constantly `k`, so the polygonal curve agrees there
with an affine function; its derivative is `(1/h) • (eulerNode (k+1) - eulerNode k) = eulerVel k`.
This is the `HasDerivAt` form used to express the Euler inclusion `γ' ∈ F (γ (⌊t/h⌋₊))`. -/
theorem IsFilippovInclusion.eulerCurve_hasDerivAt {F : E → Set E} (hF : IsFilippovInclusion F)
    {h : ℝ} (hh : 0 < h) (x₀ : E) {t : ℝ} {k : ℕ}
    (hlo : (k : ℝ) * h < t) (hhi : t < ((k : ℝ) + 1) * h) :
    HasDerivAt (eulerCurve hF h x₀) (eulerVel hF h x₀ k) t := by
  have hfloor : ∀ᶠ u in 𝓝 t, ⌊u / h⌋₊ = k := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo ⟨hlo, hhi⟩] with u hu
    have hu0 : (0 : ℝ) ≤ u / h :=
      div_nonneg (le_trans (mul_nonneg (Nat.cast_nonneg k) (le_of_lt hh)) (le_of_lt hu.1))
        (le_of_lt hh)
    rw [Nat.floor_eq_iff hu0]
    exact ⟨(le_div_iff₀ hh).mpr (le_of_lt hu.1), (div_lt_iff₀ hh).mpr hu.2⟩
  have heq : eulerCurve hF h x₀ =ᶠ[𝓝 t]
      (fun u : ℝ => eulerNode hF h x₀ k +
        ((u - (k : ℝ) * h) / h) • (eulerNode hF h x₀ (k + 1) - eulerNode hF h x₀ k)) := by
    filter_upwards [hfloor] with u hu
    simp only [eulerCurve]
    rw [hu]
  rw [Filter.EventuallyEq.hasDerivAt_iff heq]
  have hsub : eulerNode hF h x₀ (k + 1) - eulerNode hF h x₀ k = h • eulerVel hF h x₀ k := by
    rw [eulerNode_succ]
    abel
  rw [hsub]
  have h1 : HasDerivAt (fun u : ℝ => (u - (k : ℝ) * h) / h) (1 / h) t := by
    simpa using ((hasDerivAt_id t).sub_const ((k : ℝ) * h)).div_const h
  have h3 : HasDerivAt (fun u : ℝ => eulerNode hF h x₀ k +
        ((u - (k : ℝ) * h) / h) • (h • eulerVel hF h x₀ k))
      ((1 / h) • (h • eulerVel hF h x₀ k)) t :=
    (h1.smul_const _).const_add _
  convert h3 using 1
  simp [smul_smul, hh.ne']

/-- A single Euler step: on the step containing `t ≥ 0`, the difference between the polygonal
curve and the left node is `(t - k * h) / h` times the increment of that step, whose norm is at
most `h * M`. This is the elementary estimate summed over the steps in
`eulerCurve_lipschitzOn`. -/
theorem IsFilippovInclusion.dist_eulerCurve_node_le {F : E → Set E} (hF : IsFilippovInclusion F)
    {x₀ : E} {r M h : ℝ} (hh : 0 < h) (hM0 : 0 ≤ M)
    (hM : ∀ y, dist y x₀ ≤ r → ∀ v ∈ F y, ‖v‖ ≤ M) {t : ℝ} (ht : 0 ≤ t)
    (hk : (⌊t / h⌋₊ : ℝ) * h * M ≤ r) :
    dist (eulerCurve hF h x₀ t) (eulerNode hF h x₀ ⌊t / h⌋₊) ≤
      M * (t - (⌊t / h⌋₊ : ℝ) * h) := by
  have hvel : ‖eulerVel hF h x₀ ⌊t / h⌋₊‖ ≤ M := by
    have hdist : dist (eulerNode hF h x₀ ⌊t / h⌋₊) x₀ ≤ r :=
      le_trans (hF.dist_eulerNode_le hh.le hM0 hM ⌊t / h⌋₊ hk) hk
    exact hM _ hdist _ (hF.eulerNode_choose_mem h x₀ ⌊t / h⌋₊)
  have hle : (⌊t / h⌋₊ : ℝ) * h ≤ t :=
    (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg ht hh.le))
  have hdiff : eulerCurve hF h x₀ t - eulerNode hF h x₀ ⌊t / h⌋₊ =
      ((t - (⌊t / h⌋₊ : ℝ) * h) / h) •
        (eulerNode hF h x₀ (⌊t / h⌋₊ + 1) - eulerNode hF h x₀ ⌊t / h⌋₊) := by
    simp only [eulerCurve]
    abel
  have hgn : eulerNode hF h x₀ (⌊t / h⌋₊ + 1) - eulerNode hF h x₀ ⌊t / h⌋₊ =
      h • eulerVel hF h x₀ ⌊t / h⌋₊ := by
    rw [eulerNode_succ]
    abel
  rw [dist_eq_norm, hdiff, hgn]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh.le,
    abs_of_nonneg (div_nonneg (sub_nonneg.mpr hle) hh.le)]
  calc (t - (⌊t / h⌋₊ : ℝ) * h) / h * (h * ‖eulerVel hF h x₀ ⌊t / h⌋₊‖)
      ≤ (t - (⌊t / h⌋₊ : ℝ) * h) / h * (h * M) := by gcongr
    _ = M * (t - (⌊t / h⌋₊ : ℝ) * h) := by field_simp

/-- The forward companion of `dist_eulerCurve_node_le`: the distance from the polygonal curve to
the right node of the current step is at most `M` times the remaining time in the step. -/
theorem IsFilippovInclusion.dist_eulerNode_succ_eulerCurve_le {F : E → Set E}
    (hF : IsFilippovInclusion F) {x₀ : E} {r M h : ℝ} (hh : 0 < h) (hM0 : 0 ≤ M)
    (hM : ∀ y, dist y x₀ ≤ r → ∀ v ∈ F y, ‖v‖ ≤ M) {s : ℝ}
    (hk : ((⌊s / h⌋₊ : ℝ) + 1) * h * M ≤ r) :
    dist (eulerNode hF h x₀ (⌊s / h⌋₊ + 1)) (eulerCurve hF h x₀ s) ≤
      M * (((⌊s / h⌋₊ : ℝ) + 1) * h - s) := by
  have hvel : ‖eulerVel hF h x₀ ⌊s / h⌋₊‖ ≤ M := by
    have hdist : dist (eulerNode hF h x₀ ⌊s / h⌋₊) x₀ ≤ r := by
      have hcast : ((⌊s / h⌋₊ : ℝ)) * h * M ≤ ((⌊s / h⌋₊ : ℝ) + 1) * h * M := by
        have : (0 : ℝ) ≤ h * M := mul_nonneg hh.le hM0
        nlinarith
      exact le_trans (hF.dist_eulerNode_le hh.le hM0 hM ⌊s / h⌋₊ (le_trans hcast hk))
        (le_trans hcast hk)
    exact hM _ hdist _ (hF.eulerNode_choose_mem h x₀ ⌊s / h⌋₊)
  have hs_lt : s < ((⌊s / h⌋₊ : ℝ) + 1) * h :=
    (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (s / h))
  have hform : eulerNode hF h x₀ (⌊s / h⌋₊ + 1) - eulerCurve hF h x₀ s =
      (((⌊s / h⌋₊ : ℝ) + 1) * h - s) • eulerVel hF h x₀ ⌊s / h⌋₊ := by
    simp only [eulerCurve, eulerNode_succ, add_sub_cancel_left, smul_smul]
    rw [add_sub_add_left_eq_sub, ← sub_smul]
    congr 1
    field_simp
    ring
  rw [dist_eq_norm, hform, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hs_lt.le)]
  calc (((⌊s / h⌋₊ : ℝ) + 1) * h - s) * ‖eulerVel hF h x₀ ⌊s / h⌋₊‖
      ≤ (((⌊s / h⌋₊ : ℝ) + 1) * h - s) * M :=
        mul_le_mul_of_nonneg_left hvel (sub_nonneg.mpr hs_lt.le)
    _ = M * (((⌊s / h⌋₊ : ℝ) + 1) * h - s) := by ring

/-- **The Euler polygonal curves are uniformly `M`-Lipschitz on `[0, T]`.** Provided `T * M ≤ r`,
all nodes reached before time `T` have admissible velocities bounded by `M`, and the polygonal
curve is a convex-combination (`h`-step) interpolation of these nodes. This uniform Lipschitz bound
is the equicontinuity input for the Arzelà–Ascoli compactness step. -/
theorem IsFilippovInclusion.eulerCurve_lipschitzOn {F : E → Set E} (hF : IsFilippovInclusion F)
    {x₀ : E} {r M h T : ℝ} (hh : 0 < h) (hM0 : 0 ≤ M) (hTM : T * M ≤ r)
    (hM : ∀ y, dist y x₀ ≤ r → ∀ v ∈ F y, ‖v‖ ≤ M) :
    LipschitzOnWith (⟨M, hM0⟩ : ℝ≥0) (eulerCurve hF h x₀) (Set.Icc 0 T) := by
  have vel_bound_T : ∀ j : ℕ, (j : ℝ) * h ≤ T → ‖eulerVel hF h x₀ j‖ ≤ M := by
    intro j hj
    have hjr : (j : ℝ) * h * M ≤ r := by
      have : (j : ℝ) * h * M ≤ T * M := by nlinarith [hj, hM0]
      linarith
    have hdist : dist (eulerNode hF h x₀ j) x₀ ≤ r :=
      le_trans (hF.dist_eulerNode_le hh.le hM0 hM j hjr) hjr
    exact hM _ hdist _ (hF.eulerNode_choose_mem h x₀ j)
  refine LipschitzOnWith.of_dist_le_mul ?_
  have key : ∀ a b, 0 ≤ a → b ≤ T → a ≤ b →
      dist (eulerCurve hF h x₀ a) (eulerCurve hF h x₀ b) ≤ M * (b - a) := by
    intro a b ha hbTab hab
    have hma : (⌊a / h⌋₊ : ℝ) * h ≤ a :=
      (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg ha hh.le))
    have hnb : (⌊b / h⌋₊ : ℝ) * h ≤ b :=
      (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg (ha.trans hab) hh.le))
    have hmn : ⌊a / h⌋₊ ≤ ⌊b / h⌋₊ :=
      Nat.floor_mono (div_le_div_of_nonneg_right hab hh.le)
    by_cases hmn1 : ⌊a / h⌋₊ + 1 ≤ ⌊b / h⌋₊
    · -- the nodes are separated by at least one full step
      have hnode_a : dist (eulerCurve hF h x₀ a) (eulerNode hF h x₀ ⌊a / h⌋₊) ≤
          M * (a - (⌊a / h⌋₊ : ℝ) * h) := by
        refine hF.dist_eulerCurve_node_le hh hM0 hM ha ?_
        have : (⌊a / h⌋₊ : ℝ) * h * M ≤ T * M := by nlinarith [hma, hbTab, hab, hM0]
        linarith
      have hnode_b : dist (eulerCurve hF h x₀ b) (eulerNode hF h x₀ ⌊b / h⌋₊) ≤
          M * (b - (⌊b / h⌋₊ : ℝ) * h) := by
        refine hF.dist_eulerCurve_node_le hh hM0 hM (ha.trans hab) ?_
        have : (⌊b / h⌋₊ : ℝ) * h * M ≤ T * M := by nlinarith [hnb, hbTab, hM0]
        linarith
      have hnode_fwd : dist (eulerNode hF h x₀ (⌊a / h⌋₊ + 1)) (eulerCurve hF h x₀ a) ≤
          M * (((⌊a / h⌋₊ : ℝ) + 1) * h - a) := by
        refine hF.dist_eulerNode_succ_eulerCurve_le hh hM0 hM ?_
        have : ((⌊a / h⌋₊ : ℝ) + 1) * h * M ≤ T * M := by
          have hle : ((⌊a / h⌋₊ : ℝ) + 1) * h ≤ (⌊b / h⌋₊ : ℝ) * h := by
            have : ⌊a / h⌋₊ + 1 ≤ ⌊b / h⌋₊ := hmn1
            have hc : ((⌊a / h⌋₊ + 1 : ℕ) : ℝ) ≤ (⌊b / h⌋₊ : ℝ) := by exact_mod_cast this
            simpa using mul_le_mul_of_nonneg_right hc hh.le
          nlinarith [hle, hnb, hbTab, hM0]
        linarith
      have htel : eulerNode hF h x₀ ⌊b / h⌋₊ - eulerNode hF h x₀ (⌊a / h⌋₊ + 1) =
          (Finset.range (⌊b / h⌋₊ - (⌊a / h⌋₊ + 1))).sum
            (fun i => eulerNode hF h x₀ (⌊a / h⌋₊ + 1 + (i + 1)) -
              eulerNode hF h x₀ (⌊a / h⌋₊ + 1 + i)) := by
        rw [Finset.sum_range_sub (f := fun j => eulerNode hF h x₀ (⌊a / h⌋₊ + 1 + j))]
        simp [Nat.add_sub_of_le hmn1]
      have hsum : ‖eulerNode hF h x₀ ⌊b / h⌋₊ - eulerNode hF h x₀ (⌊a / h⌋₊ + 1)‖ ≤
          M * ((⌊b / h⌋₊ : ℝ) * h - ((⌊a / h⌋₊ : ℝ) + 1) * h) := by
        rw [htel]
        calc ‖(Finset.range (⌊b / h⌋₊ - (⌊a / h⌋₊ + 1))).sum
              (fun i => eulerNode hF h x₀ (⌊a / h⌋₊ + 1 + i + 1) -
                eulerNode hF h x₀ (⌊a / h⌋₊ + 1 + i))‖
            ≤ (Finset.range (⌊b / h⌋₊ - (⌊a / h⌋₊ + 1))).sum
                (fun i => ‖eulerNode hF h x₀ (⌊a / h⌋₊ + 1 + i + 1) -
                  eulerNode hF h x₀ (⌊a / h⌋₊ + 1 + i)‖) := norm_sum_le _ _
          _ ≤ (Finset.range (⌊b / h⌋₊ - (⌊a / h⌋₊ + 1))).sum (fun _ => h * M) := by
              apply Finset.sum_le_sum
              intro i hi
              have hi' : ⌊a / h⌋₊ + 1 + i < ⌊b / h⌋₊ := by
                rw [Finset.mem_range] at hi
                omega
              have hleT : ((⌊a / h⌋₊ + 1 + i : ℕ) : ℝ) * h ≤ T := by
                have : ((⌊a / h⌋₊ + 1 + i : ℕ) : ℝ) ≤ (⌊b / h⌋₊ : ℝ) := by exact_mod_cast hi'.le
                nlinarith [mul_le_mul_of_nonneg_right this hh.le, hnb, hbTab]
              have hv := vel_bound_T (⌊a / h⌋₊ + 1 + i) hleT
              rw [eulerNode_succ, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
                abs_of_nonneg hh.le]
              gcongr
          _ = ((⌊b / h⌋₊ - (⌊a / h⌋₊ + 1) : ℕ) : ℝ) * (h * M) := by simp
          _ = M * ((⌊b / h⌋₊ : ℝ) * h - ((⌊a / h⌋₊ : ℝ) + 1) * h) := by
              rw [Nat.cast_sub hmn1]
              push_cast
              ring
      calc dist (eulerCurve hF h x₀ a) (eulerCurve hF h x₀ b)
          = ‖eulerCurve hF h x₀ b - eulerCurve hF h x₀ a‖ := by
              rw [dist_eq_norm, norm_sub_rev]
        _ = ‖(eulerCurve hF h x₀ b - eulerNode hF h x₀ ⌊b / h⌋₊) +
              (eulerNode hF h x₀ ⌊b / h⌋₊ - eulerNode hF h x₀ (⌊a / h⌋₊ + 1)) +
              (eulerNode hF h x₀ (⌊a / h⌋₊ + 1) - eulerCurve hF h x₀ a)‖ := by
              congr 1
              abel
        _ ≤ ‖eulerCurve hF h x₀ b - eulerNode hF h x₀ ⌊b / h⌋₊‖ +
              ‖eulerNode hF h x₀ ⌊b / h⌋₊ - eulerNode hF h x₀ (⌊a / h⌋₊ + 1)‖ +
              ‖eulerNode hF h x₀ (⌊a / h⌋₊ + 1) - eulerCurve hF h x₀ a‖ :=
              norm_add₃_le
        _ ≤ M * (b - (⌊b / h⌋₊ : ℝ) * h) +
              M * ((⌊b / h⌋₊ : ℝ) * h - ((⌊a / h⌋₊ : ℝ) + 1) * h) +
              M * (((⌊a / h⌋₊ : ℝ) + 1) * h - a) := by
              refine add_le_add (add_le_add ?_ ?_) ?_
              · simpa only [dist_eq_norm] using hnode_b
              · simpa only [dist_eq_norm] using hsum
              · simpa only [dist_eq_norm] using hnode_fwd
        _ = M * (b - a) := by ring
    · -- a and b lie in the same step
      have hnm : ⌊b / h⌋₊ = ⌊a / h⌋₊ := by omega
      have hform : eulerCurve hF h x₀ b - eulerCurve hF h x₀ a =
          ((b - a) / h) • (eulerNode hF h x₀ (⌊a / h⌋₊ + 1) - eulerNode hF h x₀ ⌊a / h⌋₊) := by
        simp only [eulerCurve, hnm]
        rw [add_sub_add_left_eq_sub, ← sub_smul]
        congr 1
        field_simp
        ring
      have hDelta : ‖eulerNode hF h x₀ (⌊a / h⌋₊ + 1) - eulerNode hF h x₀ ⌊a / h⌋₊‖ ≤ h * M := by
        have hleT : ((⌊a / h⌋₊ : ℕ) : ℝ) * h ≤ T := by nlinarith [hma, hbTab, hab]
        have hv := vel_bound_T ⌊a / h⌋₊ hleT
        rw [eulerNode_succ, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hh.le]
        gcongr
      rw [dist_eq_norm, norm_sub_rev, hform, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (sub_nonneg.mpr hab) hh.le)]
      calc (b - a) / h * ‖eulerNode hF h x₀ (⌊a / h⌋₊ + 1) - eulerNode hF h x₀ ⌊a / h⌋₊‖
          ≤ (b - a) / h * (h * M) := by gcongr
        _ = M * (b - a) := by field_simp
  intro s hs t ht
  rcases le_total s t with hst | hts
  · have hd : dist s t = t - s := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hst)]
    rw [hd]
    exact key s t hs.1 ht.2 hst
  · have hd : dist s t = s - t := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hts)]
    rw [hd, dist_comm]
    exact key t s ht.1 hs.2 hts

/-- **The Euler polygonal curve stays in the ball of local boundedness.** If `T * M ≤ r` and
`t ∈ [0, T]`, then the polygonal curve at time `t` lies within distance `r` of `x₀`. This is the
`n`-uniform range estimate: every Euler approximation takes its values on `[0, T]` in the
compact ball `closedBall x₀ r`, which is the compactness input for Arzelà–Ascoli. -/
theorem IsFilippovInclusion.dist_eulerCurve_le {F : E → Set E} (hF : IsFilippovInclusion F)
    {x₀ : E} {r M h : ℝ} (hh : 0 < h) (hM0 : 0 ≤ M)
    (hM : ∀ y, dist y x₀ ≤ r → ∀ v ∈ F y, ‖v‖ ≤ M)
    {t T : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) (hTM : T * M ≤ r) :
    dist (eulerCurve hF h x₀ t) x₀ ≤ r := by
  have hk : (⌊t / h⌋₊ : ℝ) * h * M ≤ r := by
    have hle : (⌊t / h⌋₊ : ℝ) * h ≤ t :=
      (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg ht0 hh.le))
    have hmono : (⌊t / h⌋₊ : ℝ) * h * M ≤ T * M := by nlinarith [hle, htT, hM0]
    linarith
  calc dist (eulerCurve hF h x₀ t) x₀
      ≤ dist (eulerCurve hF h x₀ t) (eulerNode hF h x₀ ⌊t / h⌋₊) +
        dist (eulerNode hF h x₀ ⌊t / h⌋₊) x₀ := dist_triangle _ _ _
    _ ≤ M * (t - (⌊t / h⌋₊ : ℝ) * h) + (⌊t / h⌋₊ : ℝ) * h * M := by
        gcongr
        · exact hF.dist_eulerCurve_node_le hh hM0 hM ht0 hk
        · exact hF.dist_eulerNode_le hh.le hM0 hM ⌊t / h⌋₊ hk
    _ = t * M := by ring
    _ ≤ T * M := by nlinarith
    _ ≤ r := hTM

end Euler

/-! ## Extraction of a uniformly convergent subsequence

The Euler polygonal curves are `M`-Lipschitz on `[0, T]` (`eulerCurve_lipschitzOn`) and stay in
the compact ball `closedBall x₀ r` (`dist_eulerCurve_le`). Viewing them as bounded continuous
functions on the compact interval `Icc 0 T`, Arzelà–Ascoli
(`BoundedContinuousFunction.arzela_ascoli`) provides a uniformly convergent subsequence. The
limit, extended to all of `ℝ`, inherits the `M`-Lipschitz bound and the initial condition
`γ 0 = x₀`. This is the extraction half of the local existence theorem; the remaining half is
the almost-everywhere identification of the limit derivative with the inclusion `F`. -/

section Extraction

variable [FiniteDimensional ℝ E]

open scoped BoundedContinuousFunction

/-- **Extraction of a uniformly convergent subsequence of Euler polygonal curves.** Given a slope
bound `M` on the values of the inclusion in the ball of radius `r` about `x₀` and step sizes
`h n > 0` with `h n * M ≤ r`, there is a strictly monotone subsequence `φ` of the Euler curves
`t ↦ eulerCurve hF (h (φ n)) x₀ t` converging uniformly on `Icc 0 (r / max M 1)` to a limit curve
`γlim` that is `M`-Lipschitz there and starts at `x₀`.

The compactness input is Arzelà–Ascoli: the curves are uniformly `M`-Lipschitz and take values in
the compact ball `closedBall x₀ r`. The hypotheses `Tendsto h atTop (𝓝 0)` and `h n * M ≤ r` belong
to the surrounding existence contract; the extraction itself only needs a uniform step bound, which
is implied by the choice `T = r / max M 1`.

The proof is the standard diagonal/compactness argument: the images of the Euler curves in the
space `Icc 0 T →ᵇ E` of bounded continuous functions form an equicontinuous family with values in a
compact set, so their closure is compact and a subsequence converges in the uniform topology; the
limit is extended to `ℝ` by `x₀` off `Icc 0 T`.

We mark the lemma `@[nolint unusedArguments]` because the two hypotheses `Tendsto h atTop (𝓝 0)`
and `h n * M ≤ r` are part of the campaign interface but are not needed for this half of the
argument: the range estimate only uses the derived uniform bound `T * M ≤ r`. -/
@[nolint unusedArguments] -- `hh0` and `hhr` are contract hypotheses not needed in the extraction
theorem IsFilippovInclusion.exists_eulerCurve_tendsto_subseq {F : E → Set E}
    (hF : IsFilippovInclusion F) (x₀ : E) {r M : ℝ} (hr : 0 < r) (hM0 : 0 ≤ M)
    (hM : ∀ y, dist y x₀ ≤ r → ∀ v ∈ F y, ‖v‖ ≤ M)
    (h : ℕ → ℝ) (hh : ∀ n, 0 < h n) (_hh0 : Tendsto h atTop (𝓝 0))
    (_hhr : ∀ n, h n * M ≤ r) :
    ∃ (φ : ℕ → ℕ) (γlim : ℝ → E),
      StrictMono φ ∧
      TendstoUniformlyOn (fun n t ↦ eulerCurve hF (h (φ n)) x₀ t) γlim atTop
        (Set.Icc 0 (r / max M 1)) ∧
      LipschitzOnWith ⟨M, hM0⟩ γlim (Set.Icc 0 (r / max M 1)) ∧
      γlim 0 = x₀ := by
  set T : ℝ := r / max M 1 with hTdef
  have hMmax : M ≤ max M 1 := le_max_left _ _
  have hmaxpos : 0 < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hTpos : 0 < T := div_pos hr hmaxpos
  have hTM : T * M ≤ r := by
    rw [hTdef]
    calc r / max M 1 * M ≤ r / max M 1 * max M 1 :=
          mul_le_mul_of_nonneg_left hMmax (div_nonneg hr.le hmaxpos.le)
      _ = r := by field_simp
  set s : Set ℝ := Set.Icc 0 T with hsdef
  have hcompact : IsCompact s := by rw [hsdef]; exact isCompact_Icc
  have : CompactSpace s := isCompact_iff_compactSpace.1 hcompact
  set K : ℝ≥0 := ⟨M, hM0⟩ with hKdef
  have hLip : ∀ n, LipschitzOnWith K (eulerCurve hF (h n) x₀) s :=
    fun n => hF.eulerCurve_lipschitzOn (hh n) hM0 hTM hM
  let u : ℕ → s →ᵇ E := fun n =>
    BoundedContinuousFunction.mkOfCompact
      { toFun := s.domRestrict (eulerCurve hF (h n) x₀)
        continuous_toFun := (hLip n).to_restrict.continuous }
  have hu_coe : ∀ n, (u n : s → E) = s.domRestrict (eulerCurve hF (h n) x₀) := fun _ => rfl
  have hu_apply : ∀ n (x : s), u n x = eulerCurve hF (h n) x₀ x := fun _ _ => rfl
  set A : Set (s →ᵇ E) := Set.range u with hAdef
  have hRange : ∀ (f : s →ᵇ E) (x : s), f ∈ A → f x ∈ Metric.closedBall x₀ r := by
    rintro f x ⟨n, rfl⟩
    rw [Metric.mem_closedBall, hu_apply n x]
    exact hF.dist_eulerCurve_le (hh n) hM0 hM x.2.1 x.2.2 hTM
  have hEquicont : Equicontinuous ((↑) : A → s → E) := by
    refine UniformEquicontinuous.equicontinuous ?_
    refine LipschitzWith.uniformEquicontinuous (fun f : A => (f : s → E)) K ?_
    rintro ⟨f, ⟨n, rfl⟩⟩
    rw [hu_coe n]
    exact (hLip n).to_restrict
  have hCompact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall x₀ r)
      (isCompact_closedBall x₀ r) A hRange hEquicont
  obtain ⟨a, -, φ, hφ, hconv⟩ :=
    IsCompact.tendsto_subseq (s := closure A) (x := u) hCompact
      (fun n => subset_closure (Set.mem_range_self n))
  have hunif : TendstoUniformly (fun n => u (φ n)) a atTop :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv
  let γlim : ℝ → E := fun t => if ht : t ∈ s then a ⟨t, ht⟩ else x₀
  have hγlim_eq : ∀ (x : ℝ) (hx : x ∈ s), γlim x = a ⟨x, hx⟩ := fun x hx => by
    simp only [γlim, dite_eq_left hx]
  have hγlim_coe : ∀ x : s, γlim x = a x := fun x => hγlim_eq x x.2
  refine ⟨φ, γlim, hφ, ?_, ?_, ?_⟩
  · rw [tendstoUniformlyOn_iff_restrict]
    have hleft : (fun n : ℕ => s.domRestrict (fun t => eulerCurve hF (h (φ n)) x₀ t)) =
        fun n => (u (φ n) : s → E) := by
      funext n x
      exact (hu_apply (φ n) x).symm
    have hright : s.domRestrict γlim = a := by
      funext x
      exact hγlim_coe x
    rw [hleft, hright]
    exact hunif
  · rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    have ha_lip : LipschitzWith K a := by
      refine LipschitzWith.of_tendsto (f := fun n => (u (φ n) : s → E)) (g := a) ?_ ?_
      · intro n
        rw [hu_coe (φ n)]
        exact (hLip (φ n)).to_restrict
      · intro z
        simpa using hunif.tendsto_at z
    calc dist (γlim x) (γlim y)
        = dist (a ⟨x, hx⟩) (a ⟨y, hy⟩) := by rw [hγlim_eq x hx, hγlim_eq y hy]
      _ ≤ K * dist (⟨x, hx⟩ : s) (⟨y, hy⟩) := ha_lip.dist_le_mul _ _
      _ = K * dist x y := by rfl
  · have h0s : (0 : ℝ) ∈ s := by
      rw [hsdef, Set.mem_Icc]
      exact ⟨le_refl 0, hTpos.le⟩
    have hpt : Tendsto (fun n : ℕ => u (φ n) ⟨0, h0s⟩) atTop (𝓝 (a ⟨0, h0s⟩)) :=
      hunif.tendsto_at ⟨0, h0s⟩
    have hconst : (fun n : ℕ => u (φ n) ⟨0, h0s⟩) = fun _ => x₀ := by
      funext n
      rw [hu_apply]
      exact hF.eulerCurve_zero (h (φ n)) x₀
    rw [hconst] at hpt
    have ha0 : a ⟨0, h0s⟩ = x₀ := tendsto_nhds_unique hpt tendsto_const_nhds
    simp only [γlim, dite_eq_left h0s, ha0]

end Extraction

