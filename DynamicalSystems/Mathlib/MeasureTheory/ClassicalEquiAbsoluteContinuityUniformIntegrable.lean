/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.MeasureTheory.ClassicalEquiAbsoluteContinuityVariation
public import DynamicalSystems.Mathlib.MeasureTheory.MeasureContinuityFromSemiring
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Interval

/-!
# Classical equi-absolute continuity implies uniform integrability

The hypothesis is the classical common modulus for sums of actual trajectory
increments. Refining partitions first gives a bound on full variations. Finite
unions of intervals then approximate a measurable set in the sum of Lebesgue
measure and the velocity-norm measure. Thus the approximation controls both
errors without requiring any uniform choice of approximants.

The resulting `UnifIntegrable` conclusion concerns the actual velocities in the
integral laws, not a redefinition of equi-absolute continuity.
-/

@[expose] public section

open Set MeasureTheory MeasurableSpace
open scoped ENNReal BigOperators Topology symmDiff

namespace DynamicalSystems.ClassicalEquiAC

private theorem intervalRing_bound {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ)
    (ν : Measure ℝ) (hν : ν.restrict (Ioc a b) = ν) {ε : ℝ≥0∞}
    (H : ∀ (κ : Type) [Fintype κ] (s t : κ → ℝ),
      (∀ j, a ≤ s j ∧ s j ≤ t j ∧ t j ≤ b) →
      Pairwise (fun j k ↦ Disjoint (Ioc (s j) (t j)) (Ioc (s k) (t k))) →
      (∑ j, (t j - s j)) < δ → (∑ j, ν (Ioc (s j) (t j))) ≤ ε)
    {A : Set ℝ} (hA : A ∈ supClosure {s | ∃ u v : ℝ, u ≤ v ∧ s = Ioc u v})
    (hsmall : (volume.restrict (Ioc a b)) A < ENNReal.ofReal δ) : ν A ≤ ε := by
  classical
  obtain ⟨P, hP⟩ := IsSetSemiring.Ioc.mem_supClosure_iff.mp hA
  choose s t hst heq using fun j : P.parts ↦ hP j.property
  have hdisj : Pairwise (fun j k : P.parts ↦
      Disjoint (Ioc (s j) (t j)) (Ioc (s k) (t k))) := by
    intro j k hjk
    rw [← heq j, ← heq k]
    exact P.supIndep.pairwiseDisjoint j.property k.property
      (fun h ↦ hjk (Subtype.ext h))
  have hunion : (⋃ j : P.parts, Ioc (s j) (t j)) = A := by
    calc
      _ = ⋃ j : P.parts, (j : Set ℝ) := by simp_rw [← heq]
      _ = ⋃₀ (P.parts : Set (Set ℝ)) := by ext z; simp
      _ = A := by rw [← Finset.sup_id_set_eq_sUnion, P.sup_parts]
  have hAm : MeasurableSet A := by
    rw [← hunion]
    exact MeasurableSet.iUnion (fun _ ↦ measurableSet_Ioc)
  let S (j : P.parts) := clampTime a b (s j)
  let T (j : P.parts) := clampTime a b (t j)
  have hST (j : P.parts) : a ≤ S j ∧ S j ≤ T j ∧ T j ≤ b :=
    ⟨(clampTime_mem_Icc _ _ _ hab).1, clampTime_mono _ _ (hst j),
      (clampTime_mem_Icc _ _ _ hab).2⟩
  have hSTdisj : Pairwise (fun j k : P.parts ↦
      Disjoint (Ioc (S j) (T j)) (Ioc (S k) (T k))) := by
    intro j k hjk
    dsimp only [S, T]
    rw [Ioc_clampTime _ _ _ _ hab, Ioc_clampTime _ _ _ _ hab]
    exact (hdisj hjk).mono inter_subset_left inter_subset_left
  have hSTunion : (⋃ j : P.parts, Ioc (S j) (T j)) = A ∩ Ioc a b := by
    simp_rw [S, T, Ioc_clampTime _ _ _ _ hab]
    rw [← iUnion_inter, hunion]
  have hmeasure : (volume.restrict (Ioc a b)) A =
      ENNReal.ofReal (∑ j : P.parts, (T j - S j)) := by
    rw [Measure.restrict_apply hAm, ← hSTunion,
      measure_iUnion hSTdisj (fun _ ↦ measurableSet_Ioc), tsum_fintype]
    simp only [Real.volume_Ioc]
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ ↦ sub_nonneg.mpr (hST j).2.1)]
  have hlength : (∑ j : P.parts, (T j - S j)) < δ := by
    rw [hmeasure] at hsmall
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).mp hsmall
  calc
    ν A = ν (A ∩ Ioc a b) := by rw [← Measure.restrict_apply hAm, hν]
    _ = ∑ j : P.parts, ν (Ioc (S j) (T j)) := by
      rw [← hSTunion, measure_iUnion hSTdisj (fun _ ↦ measurableSet_Ioc), tsum_fintype]
    _ ≤ ε := H P.parts S T hST hSTdisj hlength

/-- The classical disjoint-interval equi-AC condition implies uniform
integrability of the actual integrable velocities. The trajectories are
constant extensions to the real line and satisfy their original integral laws
with respect to restricted Lebesgue measure. No norm bound or weak convergence
is assumed. The result also applies to infinite-dimensional Banach spaces. -/
theorem EquiAbsolutelyContinuousOn.unifIntegrable_Ioc
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a ≤ b) {x v : ι → ℝ → E}
    (hx : EquiAbsolutelyContinuousOn x (fun _ ↦ a) (fun _ ↦ b))
    (hv : ∀ i, Integrable (v i) (volume.restrict (Ioc a b)))
    (hcont : ∀ i, Continuous (x i))
    (hlaw : ∀ i s t, s ≤ t → x i t - x i s =
      ∫ z in Ioc s t, v i z ∂volume.restrict (Ioc a b)) :
    UnifIntegrable v 1 (volume.restrict (Ioc a b)) := by
  classical
  let μ := volume.restrict (Ioc a b)
  apply unifIntegrable_iff.mpr
  intro ε hε
  obtain ⟨e, he, heε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  have hepos : 0 < (e : ℝ) := by exact_mod_cast he
  obtain ⟨δ, hδ, H⟩ := hx.sum_withDensity_enorm_le hv hcont hlaw (half_pos hepos)
  refine ⟨ENNReal.ofReal (δ / 4), ENNReal.ofReal_pos.mpr (by positivity), ?_⟩
  intro i s hs
  let ν := μ.withDensity (fun z ↦ ‖v i z‖ₑ)
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity (hv i).hasFiniteIntegral.ne
  have hμnull : μ (Ioc a b)ᶜ = 0 := by
    simp [μ, Measure.restrict_apply]
  have hνnull : ν (Ioc a b)ᶜ = 0 := withDensity_absolutelyContinuous _ _ hμnull
  have hν : ν.restrict (Ioc a b) = ν :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hνnull)
  let C : Set (Set ℝ) := {s | ∃ u v : ℝ, u ≤ v ∧ s = Ioc u v}
  have hgen : (inferInstance : MeasurableSpace ℝ) = generateFrom C := by
    borelize ℝ
    convert! borel_eq_generateFrom_Ioc_le ℝ using 2
    grind only
  have hcover : ∃ D : Set (Set ℝ), D.Countable ∧ D ⊆ C ∧ (μ + ν) (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Ioc a b}, countable_singleton _, ?_, ?_⟩
    · intro A hA
      rcases mem_singleton_iff.mp hA with rfl
      exact ⟨a, b, hab, rfl⟩
    · simp only [sUnion_singleton, Measure.add_apply, hμnull, hνnull, add_zero]
  obtain ⟨A, hsA, hAm, hμA⟩ := exists_measurable_superset μ s
  have hsmall : μ A < ENNReal.ofReal δ / 2 := by
    rw [hμA]
    have heq : ENNReal.ofReal δ / 2 = ENNReal.ofReal (δ / 2) := by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num
    rw [heq]
    exact hs.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (half_pos hδ)).mpr (by linarith))
  calc
    eLpNorm (v i) 1 (μ.restrict s) ≤ eLpNorm (v i) 1 (μ.restrict A) :=
      eLpNorm_mono_measure _ (μ.restrict_mono_set hsA)
    _ = ν A := by
      rw [eLpNorm_one_eq_lintegral_enorm (hv i).aestronglyMeasurable.restrict,
        withDensity_apply _ hAm]
    _ ≤ ENNReal.ofReal ((e : ℝ) / 2) + ENNReal.ofReal ((e : ℝ) / 2) := by
      apply MeasureContinuity.measure_le_of_small_on_semiring IsSetSemiring.Ioc hcover hgen
        (ENNReal.ofReal_pos.mpr (half_pos hepos)) (ENNReal.ofReal_pos.mpr hδ) ?_ hAm hsmall
      intro A hA hsize
      exact intervalRing_bound hab hδ ν hν (H i) hA hsize
    _ = (e : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_add (half_pos hepos).le (half_pos hepos).le, add_halves]
      simp
    _ ≤ ε := heε.le

/-- Closed-interval version of the classical equi-AC to uniform-integrability
bridge. The endpoint convention makes no difference for Lebesgue measure. -/
theorem EquiAbsolutelyContinuousOn.unifIntegrable_Icc
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a ≤ b) {x v : ι → ℝ → E}
    (hx : EquiAbsolutelyContinuousOn x (fun _ ↦ a) (fun _ ↦ b))
    (hv : ∀ i, Integrable (v i) (volume.restrict (Icc a b)))
    (hcont : ∀ i, Continuous (x i))
    (hlaw : ∀ i s t, s ≤ t → x i t - x i s =
      ∫ z in Ioc s t, v i z ∂volume.restrict (Icc a b)) :
    UnifIntegrable v 1 (volume.restrict (Icc a b)) := by
  have heq : volume.restrict (Ioc a b) = volume.restrict (Icc a b) :=
    Measure.restrict_congr_set Ioc_ae_eq_Icc
  rw [← heq] at hv hlaw ⊢
  exact hx.unifIntegrable_Ioc hab hv hcont hlaw

end DynamicalSystems.ClassicalEquiAC
