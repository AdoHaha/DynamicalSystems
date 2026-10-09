/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.MeasureTheory.ClassicalEquiAbsoluteContinuity
public import Mathlib.MeasureTheory.VectorMeasure.IntegrationByParts
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Total variation of trajectories satisfying an integral law

The variation of the vector measure with density `v` is the measure with
density `‖v‖`. Identifying that vector measure with the Stieltjes measure of a
continuous trajectory gives the no-cancellation bridge needed for classical
equi-absolute continuity. A norm of a single integral is not substituted for
an integral of norms.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace DynamicalSystems.ClassicalEquiAC

private theorem finsetSum_iSup_pi {κ : Type*} [Fintype κ] {P : κ → Type*}
    [∀ i, Nonempty (P i)] (f : ∀ i, P i → ℝ≥0∞) :
    (∑ i, ⨆ p : P i, f i p) = ⨆ p : ∀ i, P i, ∑ i, f i (p i) := by
  classical
  have hsup (i : κ) : (⨆ p : ∀ j, P j, f i (p i)) = ⨆ p : P i, f i p := by
    apply le_antisymm
    · exact iSup_le (fun p ↦ le_iSup (f i) (p i))
    · refine iSup_le (fun p ↦ ?_)
      let q : ∀ j, P j := Function.update (fun j ↦ Classical.choice inferInstance) i p
      exact le_iSup_of_le q (by simp [q])
  calc
    _ = ∑ i, ⨆ p : ∀ j, P j, f i (p i) :=
      Finset.sum_congr rfl (fun i _ ↦ (hsup i).symm)
    _ = _ := ENNReal.finsetSum_iSup (by
      intro p q
      refine ⟨fun i ↦ if f i (p i) ≤ f i (q i) then q i else p i, ?_⟩
      intro i
      dsimp only
      split_ifs with h
      · exact ⟨h, le_rfl⟩
      · exact ⟨le_rfl, (le_total (f i (p i)) (f i (q i))).resolve_left h⟩)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {μ : Measure ℝ}

/-- An integrable velocity bounds the total variation of any trajectory with
its actual integral law. The estimate uses disjoint interval measures. -/
theorem eVariationOn_le_lintegral_enorm_of_integral_law
    (x v : ℝ → E) (hv : Integrable v μ)
    (hlaw : ∀ s t, s ≤ t → x t - x s = ∫ z in Ioc s t, v z ∂μ) :
    eVariationOn x univ ≤ ∫⁻ t, ‖v t‖ₑ ∂μ := by
  let ν := μ.withDensity (fun t ↦ ‖v t‖ₑ)
  have hν : (μ.withDensityᵥ v).variation = ν := Measure.variation_withDensityᵥ hv
  apply iSup_le
  rintro ⟨n, ⟨u, hu, _⟩⟩
  calc
    (∑ i ∈ Finset.range n, edist (x (u (i + 1))) (x (u i))) =
        ∑ i ∈ Finset.range n, ‖(μ.withDensityᵥ v) (Ioc (u i) (u (i + 1)))‖ₑ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [edist_eq_enorm_sub, hlaw _ _ (hu (Nat.le_succ i)),
        withDensityᵥ_apply hv measurableSet_Ioc]
    _ ≤ ∑ i ∈ Finset.range n, ν (Ioc (u i) (u (i + 1))) := by
      apply Finset.sum_le_sum
      intro i _
      rw [← hν]
      exact VectorMeasure.enorm_measure_le_variation _ _
    _ = ν (⋃ i ∈ Finset.range n, Ioc (u i) (u (i + 1))) := by
      rw [measure_biUnion_finset ?_ (fun _ _ ↦ measurableSet_Ioc)]
      rintro i - j - hij
      simp only [Function.onFun]
      grind [Monotone]
    _ ≤ ν univ := measure_mono (subset_univ _)
    _ = ∫⁻ t, ‖v t‖ₑ ∂μ := by simp [ν, withDensity_apply]

/-- The integral law proves bounded variation; it is not an additional
compactness assumption on the trajectory. -/
theorem boundedVariationOn_of_integral_law (x v : ℝ → E) (hv : Integrable v μ)
    (hlaw : ∀ s t, s ≤ t → x t - x s = ∫ z in Ioc s t, v z ∂μ) :
    BoundedVariationOn x univ :=
  ne_of_lt ((eVariationOn_le_lintegral_enorm_of_integral_law x v hv hlaw).trans_lt
    hv.hasFiniteIntegral)

/-- For a continuous trajectory with an integrable velocity, interval total
variation is exactly the integral of the velocity norm. This identity retains
all oscillations and is the quantitative no-cancellation step. -/
theorem withDensity_enorm_Ioc_eq_eVariationOn [NullSingletonClass μ]
    (x v : ℝ → E) (hv : Integrable v μ) (hx : Continuous x)
    (hlaw : ∀ s t, s ≤ t → x t - x s = ∫ z in Ioc s t, v z ∂μ) (a b : ℝ) :
    μ.withDensity (fun t ↦ ‖v t‖ₑ) (Ioc a b) = eVariationOn x (Ioc a b) := by
  have hBV := boundedVariationOn_of_integral_law x v hv hlaw
  have hr : x.rightLim = x := by
    funext t
    exact tendsto_nhds_unique (hBV.tendsto_rightLim t)
      ((hx.tendsto t).mono_left nhdsWithin_le_nhds)
  have hl : x.leftLim = x := by
    funext t
    exact tendsto_nhds_unique (hBV.tendsto_leftLim t)
      ((hx.tendsto t).mono_left nhdsWithin_le_nhds)
  have heq : hBV.vectorMeasure = μ.withDensityᵥ v := by
    apply VectorMeasure.ext_of_Icc _ _
    intro s t hst
    rw [hBV.vectorMeasure_Icc hst, hr, hl,
      withDensityᵥ_apply hv measurableSet_Icc, integral_Icc_eq_integral_Ioc]
    exact hlaw s t hst
  calc
    _ = (μ.withDensityᵥ v).variation (Ioc a b) := by
      rw [Measure.variation_withDensityᵥ hv]
    _ = hBV.vectorMeasure.variation (Ioc a b) := by rw [heq]
    _ = eVariationOn x.rightLim (Ioc a b) := hBV.variation_vectorMeasure_Ioc
    _ = eVariationOn x (Ioc a b) := by rw [hr]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- The classical modulus controls the sum of the *full variations* on a finite
family of disjoint intervals. All the refining partitions are flattened into
one finite family before the modulus is applied. Thus oscillations cannot
cancel, and the modulus is still independent of the trajectory index. -/
theorem EquiAbsolutelyContinuousOn.sum_variation_le
    {ι : Type*} {x : ι → ℝ → E} {l r : ι → ℝ}
    (hx : EquiAbsolutelyContinuousOn x l r) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (i : ι) (κ : Type) [Fintype κ] (s t : κ → ℝ),
        (∀ j, l i ≤ s j ∧ s j ≤ t j ∧ t j ≤ r i) →
        Pairwise (fun j k ↦ Disjoint (Ioc (s j) (t j)) (Ioc (s k) (t k))) →
        (∑ j, (t j - s j)) < δ →
        (∑ j, eVariationOn (x i) (Icc (s j) (t j))) ≤ ENNReal.ofReal ε := by
  classical
  obtain ⟨δ, hδ, H⟩ := hx ε hε
  refine ⟨δ, hδ, ?_⟩
  intro i κ inst s t hst hdisj hlength
  let P (j : κ) := ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ k, u k ∈ Icc (s j) (t j)}
  let (j : κ) : Nonempty (P j) :=
    ⟨⟨0, ⟨fun _ ↦ s j, monotone_const, fun _ ↦ ⟨le_rfl, (hst j).2.1⟩⟩⟩⟩
  change (∑ j, ⨆ p : P j,
    ∑ k ∈ Finset.range p.1, edist (x i (p.2.1 (k + 1))) (x i (p.2.1 k))) ≤ _
  rw [finsetSum_iSup_pi]
  apply iSup_le
  intro p
  let S (q : Σ j, Fin (p j).1) := (p q.1).2.1 q.2.val
  let T (q : Σ j, Fin (p j).1) := (p q.1).2.1 (q.2.val + 1)
  have hST (q : Σ j, Fin (p j).1) : l i ≤ S q ∧ S q ≤ T q ∧ T q ≤ r i := by
    exact ⟨(hst q.1).1.trans ((p q.1).2.2.2 _).1,
      (p q.1).2.2.1 (Nat.le_succ _),
      ((p q.1).2.2.2 _).2.trans (hst q.1).2.2⟩
  have hSTdisj : Pairwise (fun q q' : Σ j, Fin (p j).1 ↦
      Disjoint (Ioc (S q) (T q)) (Ioc (S q') (T q'))) := by
    rintro ⟨j, k⟩ ⟨j', k'⟩ hne
    by_cases hj : j = j'
    · subst j'
      have hk : k ≠ k' := by
        intro h
        subst k'
        exact hne rfl
      have horder : k.val + 1 ≤ k'.val ∨ k'.val + 1 ≤ k.val := by
        have : k.val ≠ k'.val := fun h ↦ hk (Fin.ext h)
        omega
      apply Set.disjoint_left.mpr
      intro y hy hy'
      rcases horder with h | h
      · have hm := (p j).2.2.1 h
        exact (not_lt_of_ge (hy.2.trans hm)) hy'.1
      · have hm := (p j).2.2.1 h
        exact (not_lt_of_ge (hy'.2.trans hm)) hy.1
    · apply (hdisj hj).mono
      · exact Ioc_subset_Ioc ((p j).2.2.2 _).1 ((p j).2.2.2 _).2
      · exact Ioc_subset_Ioc ((p j').2.2.2 _).1 ((p j').2.2.2 _).2
  have telescope (u : ℕ → ℝ) (n : ℕ) :
      (∑ k ∈ Finset.range n, (u (k + 1) - u k)) = u n - u 0 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; ring
  have hSTlength : (∑ q : Σ j, Fin (p j).1, (T q - S q)) ≤
      ∑ j, (t j - s j) := by
    rw [Fintype.sum_sigma]
    apply Finset.sum_le_sum
    intro j _
    dsimp only [S, T]
    rw [Fin.sum_univ_eq_sum_range
      (fun k ↦ (p j).2.1 (k + 1) - (p j).2.1 k), telescope]
    exact sub_le_sub ((p j).2.2.2 _).2 ((p j).2.2.2 _).1
  have hbound := H i (Σ j, Fin (p j).1) S T hST hSTdisj
    (hSTlength.trans_lt hlength)
  calc
    (∑ j, ∑ k ∈ Finset.range (p j).1,
        edist (x i ((p j).2.1 (k + 1))) (x i ((p j).2.1 k))) =
        ∑ q : Σ j, Fin (p j).1, ENNReal.ofReal ‖x i (T q) - x i (S q)‖ := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only [S, T]
      rw [Fin.sum_univ_eq_sum_range
        (fun k ↦ ENNReal.ofReal ‖x i ((p j).2.1 (k + 1)) - x i ((p j).2.1 k)‖)]
      simp only [edist_dist, dist_eq_norm]
    _ = ENNReal.ofReal (∑ q : Σ j, Fin (p j).1, ‖x i (T q) - x i (S q)‖) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ norm_nonneg _)]
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hbound.le

/-- Classical equi-absolute continuity bounds finite disjoint sums of integrals
of velocity norms, with one common modulus. This is the interval version of
uniform integrability, derived from the actual integral laws. -/
theorem EquiAbsolutelyContinuousOn.sum_withDensity_enorm_le [NullSingletonClass μ]
    {ι : Type*} {x v : ι → ℝ → E} {l r : ι → ℝ}
    (hx : EquiAbsolutelyContinuousOn x l r) (hv : ∀ i, Integrable (v i) μ)
    (hcont : ∀ i, Continuous (x i))
    (hlaw : ∀ i s t, s ≤ t → x i t - x i s = ∫ z in Ioc s t, v i z ∂μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (i : ι) (κ : Type) [Fintype κ] (s t : κ → ℝ),
        (∀ j, l i ≤ s j ∧ s j ≤ t j ∧ t j ≤ r i) →
        Pairwise (fun j k ↦ Disjoint (Ioc (s j) (t j)) (Ioc (s k) (t k))) →
        (∑ j, (t j - s j)) < δ →
        (∑ j, μ.withDensity (fun z ↦ ‖v i z‖ₑ) (Ioc (s j) (t j))) ≤
          ENNReal.ofReal ε := by
  obtain ⟨δ, hδ, H⟩ := hx.sum_variation_le hε
  refine ⟨δ, hδ, ?_⟩
  intro i κ inst s t hst hdisj hlength
  calc
    _ = ∑ j, eVariationOn (x i) (Ioc (s j) (t j)) := by
      apply Finset.sum_congr rfl
      intro j _
      exact withDensity_enorm_Ioc_eq_eVariationOn (x i) (v i) (hv i) (hcont i)
        (hlaw i) (s j) (t j)
    _ ≤ ∑ j, eVariationOn (x i) (Icc (s j) (t j)) := by
      exact Finset.sum_le_sum (fun j _ ↦ eVariationOn.mono _ Ioc_subset_Icc_self)
    _ ≤ ENNReal.ofReal ε := H i κ s t hst hdisj hlength

end DynamicalSystems.ClassicalEquiAC
