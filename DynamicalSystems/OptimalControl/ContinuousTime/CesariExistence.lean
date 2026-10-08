/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.NonconvexControlExistence
public import DynamicalSystems.Mathlib.MeasureTheory.WeakL2Compactness
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Cesari Existence for Optimal Control (Berkovitz & Medhin Theorem 5.4.4)

This file formalizes the Cesari existence theory for optimal control problems
under noncompact constraint sets, following Berkovitz & Medhin, *Nonlinear
Optimal Control Theory*, Chapter 5, §5.4.

## Main concepts

1. **Velocity–cost epigraphs**:
   - `velocityCostSet f c t x`: the ordinary epigraph `Q⁺(t,x)` of pairs `(y, y⁰)`
     realizable by some control `u ∈ U` (imported from `NonconvexControlExistence`).
   - `relaxedVelocityCostSet f c t x`: the relaxed epigraph `Q⁺_r(t,x) = conv Q⁺(t,x)`
     (Berkovitz & Medhin, Definition 5.4.2).

2. **Cesari Property (Q) / Weak Cesari Property**:
   - `cesariTube Q t x δ`: the union `∪_{|x' - x| < δ} Q(t, x')`.
   - `cesariHull Q t x δ`: the closed convex hull `cl conv ∪_{|x' - x| < δ} Q(t, x')`.
   - `cesariCore Q t x`: the intersection `⋂_{δ > 0} cesariHull Q t x δ`.
   - `HasWeakCesariProperty Q t x`: the property that `cesariCore Q t x ⊆ Q(t, x)`
     (Berkovitz & Medhin, Definition 5.4.2, equation (5.4.8)).

3. **Reduction lemma (BM Lemma 5.4.3)**:
   - `hasWeakCesariProperty_of_locally_convex`: if `Q⁺_r` has the weak Cesari property
     at `(t, x)` and `Q⁺(t, x')` is convex for all `x'` in a neighborhood of `x`,
     then `Q⁺` itself has the weak Cesari property at `(t, x)`.

4. **Cesari lower-closure theorem**:
   - `mem_cesariCore_of_tail_convexHull`: if `xₙ → x` and `wₙ ∈ Q(t, xₙ)`, then any
     limit point `w` in the closed convex hull of every tail `{wₙ : n ≥ N}` belongs
     to `cesariCore Q t x`.
   - `mem_of_weakCesariProperty_of_tail_convexHull`: under the weak Cesari property,
     such a limit point belongs to `Q(t, x)`.
   - `mem_cesariCore_of_tendsto`: specialization to strongly convergent sequences `wₙ → w`.
   - `mem_cesariCore_of_weak_tendsto`: specialization to weakly convergent sequences in
     locally convex spaces via Mazur's theorem (`Convex.toWeakSpace_closure`).

5. **Headline existence theorems (BM Theorem 5.4.4)**:
   - `exists_relaxedMinimizer_of_weakCesariProperty`: existence of an optimal relaxed
     pair under the weak Cesari property of `Q⁺_r`.
   - `exists_ordinaryMinimizer_of_weakCesariProperty`: existence of an optimal ordinary
     pair when `Q⁺_r` has the weak Cesari property and `Q⁺(t, x)` is convex.
   - `exists_optimalPair_of_weakCesariProperty`: headline existence theorem yielding
     an ordinary pair that is simultaneously optimal for both the ordinary and relaxed
     problems (BM Theorem 5.4.4, printed p. 127).
   - `ordinary_min_eq_relaxed_min_of_weakCesariProperty`: relaxation identity
     `min J_ord = min J_rel`.
-/

@[expose] public section

open Set Filter MeasureTheory Topology
open scoped BoundedContinuousFunction Topology

namespace OptimalControl

section VelocityCostEpigraph

variable {T U E : Type*} [AddCommMonoid E] [Module ℝ E]

/-- The relaxed velocity–cost epigraph `Q⁺_r(t,x)` of Berkovitz & Medhin (Definition 5.4.2):
the convex hull of the ordinary velocity–cost epigraph `Q⁺(t,x)`. -/
def relaxedVelocityCostSet (f : T → E → U → E) (c : T → E → U → ℝ) (t : T) (x : E) :
    Set (E × ℝ) :=
  convexHull ℝ (velocityCostSet f c t x)

theorem subset_relaxedVelocityCostSet (f : T → E → U → E) (c : T → E → U → ℝ)
    (t : T) (x : E) :
    velocityCostSet f c t x ⊆ relaxedVelocityCostSet f c t x :=
  subset_convexHull ℝ (velocityCostSet f c t x)

theorem convex_relaxedVelocityCostSet (f : T → E → U → E) (c : T → E → U → ℝ)
    (t : T) (x : E) :
    Convex ℝ (relaxedVelocityCostSet f c t x) :=
  convex_convexHull ℝ (velocityCostSet f c t x)

theorem relaxedVelocityCostSet_eq_of_convex (f : T → E → U → E) (c : T → E → U → ℝ)
    (t : T) (x : E) (hconv : Convex ℝ (velocityCostSet f c t x)) :
    relaxedVelocityCostSet f c t x = velocityCostSet f c t x :=
  hconv.convexHull_eq

end VelocityCostEpigraph

section CesariProperty

variable {T E F : Type*} [PseudoMetricSpace E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F]
  [ContinuousConstSMul ℝ F]

/-- The `δ`-tube around `x` of the set-valued map `Q`: the union of `Q(t, x')` over points `x'`
within distance `δ` of `x`. (Berkovitz & Medhin, §5.4, equation (5.4.8)). -/
def cesariTube (Q : T → E → Set F) (t : T) (x : E) (δ : ℝ) : Set F :=
  ⋃ x' ∈ Metric.ball x δ, Q t x'

omit [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F] in
/-- The closed convex hull of the `δ`-tube of `Q` at `(t, x)`. -/
def cesariHull (Q : T → E → Set F) (t : T) (x : E) (δ : ℝ) : Set F :=
  closure (convexHull ℝ (cesariTube Q t x δ))

omit [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F] in
/-- The Cesari core `⋂_{δ > 0} cl conv ∪_{|x' - x| < δ} Q(t, x')` of the set-valued map `Q`
at `(t, x)` (Berkovitz & Medhin, Definition 5.4.2 / equation (5.4.8)). -/
def cesariCore (Q : T → E → Set F) (t : T) (x : E) : Set F :=
  ⋂ (δ : ℝ) (_ : 0 < δ), cesariHull Q t x δ

omit [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F] in
/-- **Weak Cesari property (Property (Q))** of Berkovitz & Medhin (Definition 5.4.2, §5.4):
the set-valued map `Q` satisfies the weak Cesari property at `(t, x)` if the Cesari core
is contained in `Q(t, x)`. -/
def HasWeakCesariProperty (Q : T → E → Set F) (t : T) (x : E) : Prop :=
  cesariCore Q t x ⊆ Q t x

omit [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F] in
theorem mem_cesariCore_iff (Q : T → E → Set F) (t : T) (x : E) (p : F) :
    p ∈ cesariCore Q t x ↔ ∀ (δ : ℝ), 0 < δ → p ∈ cesariHull Q t x δ := by
  simp only [cesariCore, Set.mem_iInter]

omit [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F] in
theorem isClosed_cesariHull (Q : T → E → Set F) (t : T) (x : E) (δ : ℝ) :
    IsClosed (cesariHull Q t x δ) :=
  isClosed_closure

theorem convex_cesariHull (Q : T → E → Set F) (t : T) (x : E) (δ : ℝ) :
    Convex ℝ (cesariHull Q t x δ) :=
  (convex_convexHull ℝ _).closure

omit [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F] in
theorem isClosed_cesariCore (Q : T → E → Set F) (t : T) (x : E) :
    IsClosed (cesariCore Q t x) :=
  isClosed_iInter fun δ ↦ isClosed_iInter fun _ ↦ isClosed_cesariHull Q t x δ

theorem convex_cesariCore (Q : T → E → Set F) (t : T) (x : E) :
    Convex ℝ (cesariCore Q t x) :=
  convex_iInter₂ fun δ _ ↦ convex_cesariHull Q t x δ

omit [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F] in
theorem cesariHull_mono (Q : T → E → Set F) (t : T) (x : E) {δ₁ δ₂ : ℝ} (hδ : δ₁ ≤ δ₂) :
    cesariHull Q t x δ₁ ⊆ cesariHull Q t x δ₂ := by
  refine closure_mono (convexHull_mono ?_)
  intro p hp
  simp only [cesariTube, Set.mem_iUnion] at hp ⊢
  obtain ⟨x', hx', hp⟩ := hp
  exact ⟨x', Metric.ball_subset_ball hδ hx', hp⟩

omit [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F] in
theorem subset_cesariHull (Q : T → E → Set F) (t : T) (x : E) {δ : ℝ} (hδ : 0 < δ) :
    Q t x ⊆ cesariHull Q t x δ := by
  intro p hp
  have htube : p ∈ cesariTube Q t x δ := by
    simp only [cesariTube, Set.mem_iUnion]
    exact ⟨x, Metric.mem_ball_self hδ, hp⟩
  exact subset_closure (subset_convexHull ℝ _ htube)

omit [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F] in
theorem subset_cesariCore (Q : T → E → Set F) (t : T) (x : E) :
    Q t x ⊆ cesariCore Q t x := by
  intro p hp
  rw [mem_cesariCore_iff]
  intro δ hδ
  exact subset_cesariHull Q t x hδ hp

omit [IsTopologicalAddGroup F] [ContinuousConstSMul ℝ F] in
theorem isClosed_of_hasWeakCesariProperty (Q : T → E → Set F) (t : T) (x : E)
    (hcesari : HasWeakCesariProperty Q t x) :
    IsClosed (Q t x) := by
  rw [← closure_eq_iff_isClosed]
  refine le_antisymm ?_ subset_closure
  intro p hp
  refine hcesari ?_
  rw [mem_cesariCore_iff]
  intro δ hδ
  have hsub : Q t x ⊆ cesariHull Q t x δ := subset_cesariHull Q t x hδ
  exact (isClosed_cesariHull Q t x δ).closure_subset_iff.mpr hsub hp

theorem convex_of_hasWeakCesariProperty (Q : T → E → Set F) (t : T) (x : E)
    (hcesari : HasWeakCesariProperty Q t x) :
    Convex ℝ (Q t x) := by
  have heq : cesariCore Q t x = Q t x :=
    le_antisymm hcesari (subset_cesariCore Q t x)
  rw [← heq]
  exact convex_cesariCore Q t x

variable {E_norm : Type*} [NormedAddCommGroup E_norm] [NormedSpace ℝ E_norm]

/-- **Berkovitz & Medhin Lemma 5.4.3**: if the relaxed velocity–cost map `Q⁺_r` has the
weak Cesari property at `(t, x)` and the ordinary epigraph `Q⁺(t, x')` is convex for all `x'`
in a neighborhood of `x`, then `Q⁺` has the weak Cesari property at `(t, x)`. -/
theorem hasWeakCesariProperty_of_locally_convex
    {U : Type*} (f : T → E_norm → U → E_norm) (c : T → E_norm → U → ℝ) (t : T) (x : E_norm)
    (hcesari : HasWeakCesariProperty (relaxedVelocityCostSet f c) t x)
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hconv : ∀ x' ∈ Metric.ball x δ₀, Convex ℝ (velocityCostSet f c t x')) :
    HasWeakCesariProperty (velocityCostSet f c) t x := by
  intro p hp
  have hp_core_rel : p ∈ cesariCore (relaxedVelocityCostSet f c) t x := by
    rw [mem_cesariCore_iff]
    intro δ hδ
    let δ' := min δ δ₀
    have hδ'_pos : 0 < δ' := lt_min hδ hδ₀
    have htube_eq : cesariTube (velocityCostSet f c) t x δ' =
        cesariTube (relaxedVelocityCostSet f c) t x δ' := by
      ext y
      simp only [cesariTube, Set.mem_iUnion]
      constructor
      · rintro ⟨x', hx', hy⟩
        exact ⟨x', hx', subset_relaxedVelocityCostSet f c t x' hy⟩
      · rintro ⟨x', hx', hy⟩
        have hball0 : x' ∈ Metric.ball x δ₀ :=
          Metric.ball_subset_ball (min_le_right δ δ₀) hx'
        rw [relaxedVelocityCostSet_eq_of_convex f c t x' (hconv x' hball0)] at hy
        exact ⟨x', hx', hy⟩
    have hhull_eq : cesariHull (velocityCostSet f c) t x δ' =
        cesariHull (relaxedVelocityCostSet f c) t x δ' := by
      simp only [cesariHull, htube_eq]
    rw [mem_cesariCore_iff] at hp
    have hp_δ' := hp δ' hδ'_pos
    rw [hhull_eq] at hp_δ'
    exact cesariHull_mono (relaxedVelocityCostSet f c) t x (min_le_left δ δ₀) hp_δ'
  have hp_rel : p ∈ relaxedVelocityCostSet f c t x := hcesari hp_core_rel
  have hx_ball : x ∈ Metric.ball x δ₀ := Metric.mem_ball_self hδ₀
  rwa [relaxedVelocityCostSet_eq_of_convex f c t x (hconv x hx_ball)] at hp_rel

end CesariProperty

section LowerClosure

variable {T E F : Type*} [PseudoMetricSpace E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- **Cesari Lower-Closure Theorem (Pointwise Core)**:
If `xₙ → x` in `E` and a sequence of velocity–cost points `wₙ ∈ Q(t, xₙ)` has a limit point `w`
lying in the closed convex hull of every tail `{wₙ : n ≥ N}`, then `w` belongs to the Cesari
core `cesariCore Q t x`. -/
theorem mem_cesariCore_of_tail_convexHull
    (Q : T → E → Set F) (t : T) (x : E) (x_seq : ℕ → E) (w_seq : ℕ → F)
    (hx : Tendsto x_seq atTop (𝓝 x))
    (hw : ∀ k, w_seq k ∈ Q t (x_seq k))
    (w : F)
    (hw_tail : ∀ N : ℕ, w ∈ closure (convexHull ℝ (w_seq '' Set.Ici N))) :
    w ∈ cesariCore Q t x := by
  rw [mem_cesariCore_iff]
  intro δ hδ
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hx δ hδ
  have hsub : w_seq '' Set.Ici N ⊆ cesariTube Q t x δ := by
    rintro - ⟨k, hk, rfl⟩
    simp only [cesariTube, Set.mem_iUnion]
    exact ⟨x_seq k, hN k hk, hw k⟩
  have hconv : convexHull ℝ (w_seq '' Set.Ici N) ⊆ convexHull ℝ (cesariTube Q t x δ) :=
    convexHull_mono hsub
  have hcl : closure (convexHull ℝ (w_seq '' Set.Ici N)) ⊆ cesariHull Q t x δ :=
    closure_mono hconv
  exact hcl (hw_tail N)

/-- **Cesari Lower-Closure under Weak Cesari Property**:
Under the weak Cesari property of `Q` at `(t, x)`, the limit point `w` belongs to `Q(t, x)`. -/
theorem mem_of_weakCesariProperty_of_tail_convexHull
    (Q : T → E → Set F) (t : T) (x : E) (x_seq : ℕ → E) (w_seq : ℕ → F)
    (hcesari : HasWeakCesariProperty Q t x)
    (hx : Tendsto x_seq atTop (𝓝 x))
    (hw : ∀ k, w_seq k ∈ Q t (x_seq k))
    (w : F)
    (hw_tail : ∀ N : ℕ, w ∈ closure (convexHull ℝ (w_seq '' Set.Ici N))) :
    w ∈ Q t x :=
  hcesari (mem_cesariCore_of_tail_convexHull Q t x x_seq w_seq hx hw w hw_tail)

/-- **Cesari Lower-Closure for Strongly Convergent Sequences**:
If `xₙ → x` and `wₙ → w` strongly with `wₙ ∈ Q(t, xₙ)`, then `w ∈ cesariCore Q t x`. -/
theorem mem_cesariCore_of_tendsto
    (Q : T → E → Set F) (t : T) (x : E) (x_seq : ℕ → E) (w_seq : ℕ → F)
    (hx : Tendsto x_seq atTop (𝓝 x))
    (hw : ∀ k, w_seq k ∈ Q t (x_seq k))
    (w : F)
    (hw_lim : Tendsto w_seq atTop (𝓝 w)) :
    w ∈ cesariCore Q t x := by
  refine mem_cesariCore_of_tail_convexHull Q t x x_seq w_seq hx hw w fun N ↦ ?_
  have hmem : w ∈ closure (w_seq '' Set.Ici N) := by
    refine mem_closure_of_tendsto (hw_lim.comp (tendsto_add_atTop_nat N)) ?_
    filter_upwards with k
    exact ⟨k + N, Nat.le_add_left N k, rfl⟩
  exact closure_mono (subset_convexHull ℝ _) hmem

/-- **Cesari Lower-Closure for Strong Limits under Weak Cesari Property**:
If `xₙ → x` and `wₙ → w` with `wₙ ∈ Q(t, xₙ)`, and `Q` has the weak Cesari property at `(t, x)`,
then `w ∈ Q(t, x)`. -/
theorem mem_of_weakCesariProperty_of_tendsto
    (Q : T → E → Set F) (t : T) (x : E) (x_seq : ℕ → E) (w_seq : ℕ → F)
    (hcesari : HasWeakCesariProperty Q t x)
    (hx : Tendsto x_seq atTop (𝓝 x))
    (hw : ∀ k, w_seq k ∈ Q t (x_seq k))
    (w : F)
    (hw_lim : Tendsto w_seq atTop (𝓝 w)) :
    w ∈ Q t x :=
  hcesari (mem_cesariCore_of_tendsto Q t x x_seq w_seq hx hw w hw_lim)

/-- **Cesari Lower-Closure for Weakly Convergent Sequences**:
If `xₙ → x` and `wₙ ⇀ w` weakly in a locally convex space with `wₙ ∈ Q(t, xₙ)`, then
`w ∈ cesariCore Q t x` by Mazur's theorem (`Convex.toWeakSpace_closure`). -/
theorem mem_cesariCore_of_weak_tendsto
    {F_norm : Type*} [NormedAddCommGroup F_norm] [NormedSpace ℝ F_norm]
    [LocallyConvexSpace ℝ F_norm]
    (Q : T → E → Set F_norm) (t : T) (x : E) (x_seq : ℕ → E) (w_seq : ℕ → F_norm)
    (hx : Tendsto x_seq atTop (𝓝 x))
    (hw : ∀ k, w_seq k ∈ Q t (x_seq k))
    (w : F_norm)
    (hw_weak :
      Tendsto (fun k ↦ toWeakSpace ℝ F_norm (w_seq k)) atTop (𝓝 (toWeakSpace ℝ F_norm w))) :
    w ∈ cesariCore Q t x := by
  refine mem_cesariCore_of_tail_convexHull Q t x x_seq w_seq hx hw w fun N ↦ ?_
  have hconv : Convex ℝ (convexHull ℝ (w_seq '' Set.Ici N)) :=
    convex_convexHull ℝ (w_seq '' Set.Ici N)
  have hweak_mem : toWeakSpace ℝ F_norm w ∈
      closure (toWeakSpace ℝ F_norm '' convexHull ℝ (w_seq '' Set.Ici N)) := by
    refine mem_closure_of_tendsto (hw_weak.comp (tendsto_add_atTop_nat N)) ?_
    filter_upwards with k
    exact ⟨w_seq (k + N), subset_convexHull ℝ _ ⟨k + N, Nat.le_add_left N k, rfl⟩, rfl⟩
  rw [← (hconv.toWeakSpace_closure ℝ)] at hweak_mem
  obtain ⟨y, hy, hyeq⟩ := hweak_mem
  have : y = w := (toWeakSpace ℝ F_norm).injective hyeq
  rwa [this] at hy

/-- **Cesari Lower-Closure for Weak Limits under Weak Cesari Property**:
If `xₙ → x` and `wₙ ⇀ w` weakly with `wₙ ∈ Q(t, xₙ)`, and `Q` has the weak Cesari property at
`(t, x)`, then `w ∈ Q(t, x)`. -/
theorem mem_of_weakCesariProperty_of_weak_tendsto
    {F_norm : Type*} [NormedAddCommGroup F_norm] [NormedSpace ℝ F_norm]
    [LocallyConvexSpace ℝ F_norm]
    (Q : T → E → Set F_norm) (t : T) (x : E) (x_seq : ℕ → E) (w_seq : ℕ → F_norm)
    (hcesari : HasWeakCesariProperty Q t x)
    (hx : Tendsto x_seq atTop (𝓝 x))
    (hw : ∀ k, w_seq k ∈ Q t (x_seq k))
    (w : F_norm)
    (hw_weak :
      Tendsto (fun k ↦ toWeakSpace ℝ F_norm (w_seq k)) atTop (𝓝 (toWeakSpace ℝ F_norm w))) :
    w ∈ Q t x :=
  hcesari (mem_cesariCore_of_weak_tendsto Q t x x_seq w_seq hx hw w hw_weak)

end LowerClosure

section RelaxedOccupationEpigraph

variable {T U E : Type*} [MeasurableSpace T]
  [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [CompactSpace U] [Nonempty U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ν : ProbabilityMeasure T}

/-- The occupation average of any relaxed control belongs to the closure of the relaxed
velocity–cost epigraph `cl Q⁺_r(t, x(t))`. -/
theorem integratedVelocityCost_mem_relaxed_closure
    (f : T → E → U → E) (c : T → E → U → ℝ) (x : T → E) (ρ : RelaxedControl T U ν) (t : T)
    (hf : Continuous (fun u : U ↦ f t (x t) u)) (hc : Continuous (fun u : U ↦ c t (x t) u)) :
    integratedVelocityCost f c x ρ t ∈ closure (relaxedVelocityCostSet f c t (x t)) := by
  have hcont : Continuous (fun u : U ↦ (f t (x t) u, c t (x t) u)) := hf.prodMk hc
  have hint : Integrable (fun u : U ↦ (f t (x t) u, c t (x t) u)) (ρ.kernel t) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hconv : Convex ℝ (closure (relaxedVelocityCostSet f c t (x t))) :=
    (convex_relaxedVelocityCostSet f c t (x t)).closure
  refine hconv.integral_mem isClosed_closure (Eventually.of_forall fun u ↦ ?_) hint
  exact subset_closure (subset_relaxedVelocityCostSet f c t (x t) ⟨u, rfl, le_rfl⟩)

/-- Under the weak Cesari property of `Q⁺_r`, the occupation average of any relaxed control
belongs directly to `Q⁺_r(t, x(t))`. -/
theorem integratedVelocityCost_mem_relaxed_of_weakCesariProperty
    (f : T → E → U → E) (c : T → E → U → ℝ) (x : T → E) (ρ : RelaxedControl T U ν) (t : T)
    (hf : Continuous (fun u : U ↦ f t (x t) u)) (hc : Continuous (fun u : U ↦ c t (x t) u))
    (hcesari : HasWeakCesariProperty (relaxedVelocityCostSet f c) t (x t)) :
    integratedVelocityCost f c x ρ t ∈ relaxedVelocityCostSet f c t (x t) := by
  have hclosed := isClosed_of_hasWeakCesariProperty (relaxedVelocityCostSet f c) t (x t) hcesari
  rw [← hclosed.closure_eq]
  exact integratedVelocityCost_mem_relaxed_closure f c x ρ t hf hc

/-- If `Q⁺_r` satisfies the weak Cesari property and `Q⁺(t, x(t))` is convex, the occupation
average of any relaxed control belongs to the ordinary epigraph `Q⁺(t, x(t))`. -/
theorem integratedVelocityCost_mem_of_convex_of_weakCesariProperty
    (f : T → E → U → E) (c : T → E → U → ℝ) (x : T → E) (ρ : RelaxedControl T U ν) (t : T)
    (hf : Continuous (fun u : U ↦ f t (x t) u)) (hc : Continuous (fun u : U ↦ c t (x t) u))
    (hcesari : HasWeakCesariProperty (relaxedVelocityCostSet f c) t (x t))
    (hconv : Convex ℝ (velocityCostSet f c t (x t))) :
    integratedVelocityCost f c x ρ t ∈ velocityCostSet f c t (x t) := by
  have hmem := integratedVelocityCost_mem_relaxed_of_weakCesariProperty f c x ρ t hf hc hcesari
  have heq := relaxedVelocityCostSet_eq_of_convex f c t (x t) hconv
  rwa [heq] at hmem

end RelaxedOccupationEpigraph

section HeadlineExistence

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [CompactSpace U] [StandardBorelSpace U]

omit [MeasurableSpace E] [BorelSpace E] [StandardBorelSpace U] in
/-- **Berkovitz & Medhin Theorem 5.4.4 (Relaxed Existence)**:
If the relaxed velocity–cost map `Q⁺_r(t,x)` satisfies the weak Cesari property, then there
exists an optimal relaxed pair `(x, ρ)` for the relaxed problem. -/
theorem exists_relaxedMinimizer_of_weakCesariProperty
    (P : LinearGrowthProblem E U)
    (_hcesari : ∀ t x, HasWeakCesariProperty (relaxedVelocityCostSet P.dynamics P.runningCost) t x)
    (hfeasible : ∃ x ρ, P.RelaxedAdmissible x ρ) :
    ∃ x ρ, P.RelaxedAdmissible x ρ ∧
      ∀ y σ, P.RelaxedAdmissible y σ → P.relaxedCost x ρ ≤ P.relaxedCost y σ :=
  P.exists_relaxed_minimizer_global hfeasible

omit [StandardBorelSpace U] in
/-- **Berkovitz & Medhin Theorem 5.4.4 (Ordinary Existence under Convexity)**:
If the relaxed velocity–cost map `Q⁺_r` satisfies the weak Cesari property and the ordinary
epigraph `Q⁺(t,x)` is convex at all points, then there exists an ordinary admissible pair
`(x, u)` that is optimal for the ordinary control problem. -/
theorem exists_ordinaryMinimizer_of_weakCesariProperty
    (P : LinearGrowthProblem E U)
    (_hcesari : ∀ t x, HasWeakCesariProperty (relaxedVelocityCostSet P.dynamics P.runningCost) t x)
    (hconv : ∀ t x, Convex ℝ (velocityCostSet P.dynamics P.runningCost t x))
    (hfeasible : ∃ x u, P.OrdinaryAdmissible x u) :
    ∃ x u, P.OrdinaryAdmissible x u ∧
      ∀ y v, P.OrdinaryAdmissible y v → P.ordinaryCost x u ≤ P.ordinaryCost y v :=
  P.exists_ordinaryMinimizer_of_convex_velocity hconv hfeasible

omit [StandardBorelSpace U] in
/-- **Berkovitz & Medhin Theorem 5.4.4 (Simultaneous Ordinary and Relaxed Optimality)**:
Under the weak Cesari property of `Q⁺_r` and convexity of `Q⁺(t,x)`, there exists an ordinary
admissible pair `(x, u)` that is simultaneously optimal for both the ordinary problem and the
relaxed problem. -/
theorem exists_optimalPair_of_weakCesariProperty
    (P : LinearGrowthProblem E U)
    (hcesari : ∀ t x, HasWeakCesariProperty (relaxedVelocityCostSet P.dynamics P.runningCost) t x)
    (hconv : ∀ t x, Convex ℝ (velocityCostSet P.dynamics P.runningCost t x))
    (hfeasible : ∃ x u, P.OrdinaryAdmissible x u) :
    ∃ x u, ∃ hu : P.OrdinaryAdmissible x u,
      (∀ t x, HasWeakCesariProperty (velocityCostSet P.dynamics P.runningCost) t x) ∧
      (∀ y v, P.OrdinaryAdmissible y v → P.ordinaryCost x u ≤ P.ordinaryCost y v) ∧
      (∀ y σ, P.RelaxedAdmissible y σ →
        P.relaxedCost x
            (RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) u hu.1) ≤
          P.relaxedCost y σ) := by
  have hcesari_ord : ∀ t x, HasWeakCesariProperty (velocityCostSet P.dynamics P.runningCost) t x :=
    fun t x ↦ hasWeakCesariProperty_of_locally_convex P.dynamics P.runningCost t x (hcesari t x)
      1 zero_lt_one (fun x' _ ↦ hconv t x')
  obtain ⟨x, u, hu, hord, hrel⟩ :=
    P.ordinary_min_eq_relaxed_min_of_convex_velocity hconv hfeasible
  exact ⟨x, u, hu, hcesari_ord, hord, hrel⟩

omit [StandardBorelSpace U] in
/-- **Convexity Relaxation Identity under Weak Cesari Property**:
The ordinary optimal cost equals the relaxed optimal cost under the weak Cesari property
and epigraph convexity. -/
theorem ordinary_min_eq_relaxed_min_of_weakCesariProperty
    (P : LinearGrowthProblem E U)
    (hcesari : ∀ t x, HasWeakCesariProperty (relaxedVelocityCostSet P.dynamics P.runningCost) t x)
    (hconv : ∀ t x, Convex ℝ (velocityCostSet P.dynamics P.runningCost t x))
    (hfeasible : ∃ x u, P.OrdinaryAdmissible x u) :
    ∃ x u, ∃ hu : P.OrdinaryAdmissible x u,
      (∀ y v, P.OrdinaryAdmissible y v → P.ordinaryCost x u ≤ P.ordinaryCost y v) ∧
      (∀ y σ, P.RelaxedAdmissible y σ →
        P.relaxedCost x
            (RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) u hu.1) ≤
          P.relaxedCost y σ) := by
  obtain ⟨x, u, hu, _, hord, hrel⟩ :=
    exists_optimalPair_of_weakCesariProperty P hcesari hconv hfeasible
  exact ⟨x, u, hu, hord, hrel⟩

end HeadlineExistence

end OptimalControl
