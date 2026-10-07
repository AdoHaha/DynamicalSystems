/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.RelaxedControlDistanceSemicontinuity
public import DynamicalSystems.OptimalControl.ContinuousTime.RelaxedControls
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Measure.MeasuredSets
public import Mathlib.MeasureTheory.SetAlgebra

/-!
# The book's kernel-wise control distance `‖ν − ν₀‖_L`

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.2):
`‖ν − ν₀‖_L = ess-sup_t |ν_t − ν₀t|(Ω)`.  For relaxed controls with fixed time marginal `ν` this is
rendered without disintegration as

`d_L(ρ,σ) = sup { |ρ(A) − σ(A)| / ν(S) : S ⊆ τ open, ν(S) > 0, A ⊆ S × U measurable }`

and compared with the conditional kernels (`kernelDistance_le_iff_ae`).  It is weakly lower
semicontinuous (portmanteau, with the enlargement of `A` to an open set *inside* `S × U`), so its
sublevel sets are compact in the compact space of relaxed controls, and it dominates the
joint-measure total variation (`relaxedControlDistance`).

Book citations live in docstrings only.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace OptimalControl.RelaxedControl

variable {τ U : Type*} [MeasurableSpace τ] [MeasurableSpace U] {ν : ProbabilityMeasure τ}

/-- The kernel-wise control distance `d_L` of two relaxed controls with the same time marginal. -/
noncomputable def kernelDistance [TopologicalSpace τ] (ρ σ : RelaxedControl τ U ν) : ℝ :=
  sSup {r : ℝ | ∃ S : Set τ, IsOpen S ∧ 0 < ν.toMeasure.real S ∧
    ∃ A : Set (τ × U), MeasurableSet A ∧ A ⊆ S ×ˢ univ ∧
      r = |ρ.measure.real A - σ.measure.real A| / ν.toMeasure.real S}


/-- A set inside `S × U` has occupation mass at most `ν(S)`. -/
theorem measureReal_le_of_subset_prod_univ (ρ : RelaxedControl τ U ν) {S : Set τ}
    (hS : MeasurableSet S) {A : Set (τ × U)} (hAS : A ⊆ S ×ˢ univ) :
    ρ.measure.real A ≤ ν.toMeasure.real S := by
  calc ρ.measure.real A ≤ ρ.measure.real (S ×ˢ univ) := measureReal_mono hAS
    _ = ν.toMeasure.real S := by rw [measureReal_def, measureReal_def, ρ.measure_prod_univ hS]

section Ratios

variable [TopologicalSpace τ] [OpensMeasurableSpace τ]

/-- Each ratio in the definition of `d_L` is at most one. -/
theorem abs_sub_div_le_one (ρ σ : RelaxedControl τ U ν) {S : Set τ} (hS : IsOpen S)
    (hνS : 0 < ν.toMeasure.real S) {A : Set (τ × U)} (hAS : A ⊆ S ×ˢ univ) :
    |ρ.measure.real A - σ.measure.real A| / ν.toMeasure.real S ≤ 1 := by
  rw [div_le_one hνS, abs_le]
  have h1 := measureReal_le_of_subset_prod_univ ρ hS.measurableSet hAS
  have h2 := measureReal_le_of_subset_prod_univ σ hS.measurableSet hAS
  have h3 : 0 ≤ ρ.measure.real A := measureReal_nonneg
  have h4 : 0 ≤ σ.measure.real A := measureReal_nonneg
  constructor <;> linarith

theorem bddAbove_kernelDistance_set (ρ σ : RelaxedControl τ U ν) :
    BddAbove {r : ℝ | ∃ S : Set τ, IsOpen S ∧ 0 < ν.toMeasure.real S ∧
      ∃ A : Set (τ × U), MeasurableSet A ∧ A ⊆ S ×ˢ univ ∧
        r = |ρ.measure.real A - σ.measure.real A| / ν.toMeasure.real S} := by
  refine ⟨1, ?_⟩
  rintro r ⟨S, hS, hνS, A, -, hAS, rfl⟩
  exact abs_sub_div_le_one ρ σ hS hνS hAS

omit [OpensMeasurableSpace τ] in
theorem zero_mem_kernelDistance_set (ρ σ : RelaxedControl τ U ν) :
    (0 : ℝ) ∈ {r : ℝ | ∃ S : Set τ, IsOpen S ∧ 0 < ν.toMeasure.real S ∧
      ∃ A : Set (τ × U), MeasurableSet A ∧ A ⊆ S ×ˢ univ ∧
        r = |ρ.measure.real A - σ.measure.real A| / ν.toMeasure.real S} :=
  ⟨univ, isOpen_univ, by simp, ∅, MeasurableSet.empty, empty_subset _, by simp⟩

end Ratios

/-- A finite measure moves by at most the mass of a symmetric difference. -/
theorem abs_measureReal_sub_le_measureReal_symmDiff {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (s t : Set α) :
    |μ.real s - μ.real t| ≤ μ.real (symmDiff s t) := by
  have key : ∀ a b : Set α, μ.real a ≤ μ.real b + μ.real (symmDiff a b) := fun a b => by
    have hsub : a ⊆ b ∪ symmDiff a b := fun x hx => by
      by_cases hb : x ∈ b
      · exact Or.inl hb
      · exact Or.inr (Set.mem_symmDiff.2 (Or.inl ⟨hx, hb⟩))
    exact (measureReal_mono hsub).trans (measureReal_union_le _ _)
  rw [abs_sub_le_iff]
  have h1 := key s t
  have h2 := key t s
  rw [symmDiff_comm] at h2
  constructor <;> linarith

/-- Two probability measures that differ by at most `ε` on every measurable set have integrals of a
measurable integrand bounded by `C` differing by at most `2 ε C` (layer-cake formula). -/
theorem abs_integral_sub_le_of_forall_abs_measureReal_sub_le {α : Type*} [MeasurableSpace α]
    (μ μ' : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] {ε C : ℝ}
    (h : ∀ B : Set α, MeasurableSet B → |μ.real B - μ'.real B| ≤ ε) {f : α → ℝ}
    (hf : Measurable f) (hC : ∀ u, |f u| ≤ C) (hC0 : 0 ≤ C) :
    |∫ u, f u ∂μ - ∫ u, f u ∂μ'| ≤ 2 * ε * C := by
  set g : α → ℝ := fun u => f u + C with hg
  have hgm : Measurable g := hf.add_const C
  have hg0 : ∀ u, 0 ≤ g u := fun u => by
    have := (abs_le.1 (hC u)).1
    simp only [hg]
    linarith
  have hg2 : ∀ u, g u ≤ 2 * C := fun u => by
    have := (abs_le.1 (hC u)).2
    simp only [hg]
    linarith
  have hfi : ∀ m : Measure α, IsFiniteMeasure m → Integrable f m := fun m _ =>
    Integrable.of_bound hf.aestronglyMeasurable C
      (Eventually.of_forall fun u => (Real.norm_eq_abs _).trans_le (hC u))
  have hgi : ∀ m : Measure α, IsFiniteMeasure m → Integrable g m := fun m hm =>
    (hfi m hm).add (integrable_const C)
  have hshift : ∀ m : Measure α, IsProbabilityMeasure m →
      ∫ u, g u ∂m = ∫ u, f u ∂m + C := fun m hm => by
    simp only [hg]
    rw [integral_add (hfi m inferInstance) (integrable_const C), integral_const, probReal_univ,
      one_smul]
  set φ : Measure α → ℝ → ℝ := fun m s => m.real {a | s < g a} with hφ
  have hφanti : ∀ m : Measure α, IsFiniteMeasure m → Antitone (φ m) := fun m _ s s' hss' =>
    measureReal_mono (fun a ha => lt_of_le_of_lt hss' ha)
  have hlayer : ∀ m : Measure α, IsProbabilityMeasure m →
      ∫ u, g u ∂m = ∫ s in Ioc 0 (2 * C), φ m s := fun m hm => by
    rw [Integrable.integral_eq_integral_meas_lt (hgi m inferInstance) (Eventually.of_forall hg0)]
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
      fun s hs => ?_
    have hs2 : 2 * C < s := by
      rcases hs with ⟨hs0, hs1⟩
      simp only [mem_Ioc, not_and, not_le] at hs1
      exact hs1 hs0
    have hempty : {a | s < g a} = ∅ :=
      eq_empty_of_forall_notMem fun a ha => absurd (lt_of_lt_of_le ha (hg2 a)) (by linarith)
    simp only [hempty, measureReal_empty]
  have hφi : ∀ m : Measure α, IsProbabilityMeasure m →
      IntegrableOn (φ m) (Ioc 0 (2 * C)) := fun m hm =>
    IntegrableOn.of_bound measure_Ioc_lt_top
      (hφanti m inferInstance).measurable.aestronglyMeasurable 1
      (Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
        exact measureReal_le_one)
  have hdiff : ∫ u, f u ∂μ - ∫ u, f u ∂μ' = ∫ s in Ioc 0 (2 * C), (φ μ s - φ μ' s) := by
    rw [integral_sub (hφi μ inferInstance) (hφi μ' inferInstance), ← hlayer μ inferInstance,
      ← hlayer μ' inferInstance, hshift μ inferInstance, hshift μ' inferInstance]
    ring
  rw [hdiff, ← Real.norm_eq_abs]
  calc ‖∫ s in Ioc 0 (2 * C), (φ μ s - φ μ' s)‖
      ≤ ε * volume.real (Ioc (0 : ℝ) (2 * C)) :=
        norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top fun s _ => by
          rw [Real.norm_eq_abs]
          exact h _ (measurableSet_lt measurable_const hgm)
    _ = 2 * ε * C := by
      rw [Real.volume_real_Ioc_of_le (by linarith)]
      ring

section Compact

variable [MetricSpace τ] [BorelSpace τ] [CompactSpace τ]
  [MetricSpace U] [BorelSpace U] [CompactSpace U]

omit [CompactSpace τ] [MetricSpace U] [BorelSpace U] [CompactSpace U] in
theorem kernelDistance_nonneg (ρ σ : RelaxedControl τ U ν) : 0 ≤ kernelDistance ρ σ :=
  le_csSup (bddAbove_kernelDistance_set ρ σ) (zero_mem_kernelDistance_set ρ σ)

omit [CompactSpace τ] [MetricSpace U] [BorelSpace U] [CompactSpace U] in
theorem kernelDistance_le_one (ρ σ : RelaxedControl τ U ν) : kernelDistance ρ σ ≤ 1 := by
  refine csSup_le ⟨0, zero_mem_kernelDistance_set ρ σ⟩ ?_
  rintro r ⟨S, hS, hνS, A, -, hAS, rfl⟩
  exact abs_sub_div_le_one ρ σ hS hνS hAS

omit [CompactSpace τ] [MetricSpace U] [BorelSpace U] [CompactSpace U] in
theorem kernelDistance_self (ρ : RelaxedControl τ U ν) : kernelDistance ρ ρ = 0 := by
  refine le_antisymm (csSup_le ⟨0, zero_mem_kernelDistance_set ρ ρ⟩ ?_) (kernelDistance_nonneg ρ ρ)
  rintro r ⟨S, -, -, A, -, -, rfl⟩
  simp

omit [BorelSpace τ] [CompactSpace τ] [MetricSpace U] [BorelSpace U] [CompactSpace U] in
theorem kernelDistance_comm (ρ σ : RelaxedControl τ U ν) :
    kernelDistance ρ σ = kernelDistance σ ρ := by
  unfold kernelDistance
  simp_rw [abs_sub_comm (ρ.measure.real _)]

omit [CompactSpace τ] [MetricSpace U] [BorelSpace U] [CompactSpace U] in
theorem kernelDistance_triangle (ρ σ κ : RelaxedControl τ U ν) :
    kernelDistance ρ κ ≤ kernelDistance ρ σ + kernelDistance σ κ := by
  refine csSup_le ⟨0, zero_mem_kernelDistance_set ρ κ⟩ ?_
  rintro r ⟨S, hS, hνS, A, hA, hAS, rfl⟩
  calc |ρ.measure.real A - κ.measure.real A| / ν.toMeasure.real S
      ≤ (|ρ.measure.real A - σ.measure.real A| + |σ.measure.real A - κ.measure.real A|) /
          ν.toMeasure.real S := by gcongr; exact abs_sub_le _ _ _
    _ = |ρ.measure.real A - σ.measure.real A| / ν.toMeasure.real S +
          |σ.measure.real A - κ.measure.real A| / ν.toMeasure.real S := add_div _ _ _
    _ ≤ kernelDistance ρ σ + kernelDistance σ κ := by
      gcongr
      · exact le_csSup (bddAbove_kernelDistance_set ρ σ) ⟨S, hS, hνS, A, hA, hAS, rfl⟩
      · exact le_csSup (bddAbove_kernelDistance_set σ κ) ⟨S, hS, hνS, A, hA, hAS, rfl⟩

omit [CompactSpace τ] [MetricSpace U] [BorelSpace U] [CompactSpace U] in
/-- The defining bound. -/
theorem abs_measureReal_sub_le_kernelDistance (ρ σ : RelaxedControl τ U ν) {S : Set τ}
    (hS : IsOpen S) (hνS : 0 < ν.toMeasure.real S) {A : Set (τ × U)} (hA : MeasurableSet A)
    (hAS : A ⊆ S ×ˢ univ) :
    |ρ.measure.real A - σ.measure.real A| ≤ kernelDistance ρ σ * ν.toMeasure.real S :=
  (div_le_iff₀ hνS).1 <|
    le_csSup (bddAbove_kernelDistance_set ρ σ) ⟨S, hS, hνS, A, hA, hAS, rfl⟩

omit [CompactSpace τ] [MetricSpace U] [BorelSpace U] [CompactSpace U] in
/-- `d_L` dominates the joint-measure total variation (take `S = univ`). -/
theorem abs_measureReal_sub_le_kernelDistance_univ (ρ σ : RelaxedControl τ U ν)
    {A : Set (τ × U)} (hA : MeasurableSet A) :
    |ρ.measure.real A - σ.measure.real A| ≤ kernelDistance ρ σ := by
  simpa using abs_measureReal_sub_le_kernelDistance ρ σ isOpen_univ (by simp) hA
    (subset_univ _ |>.trans (univ_prod_univ).symm.subset)

/-- **Weak lower semicontinuity of `d_L`.** -/
theorem lowerSemicontinuous_kernelDistance (σ : RelaxedControl τ U ν) :
    LowerSemicontinuous fun ρ : RelaxedControl τ U ν => kernelDistance ρ σ := by
  intro ρ₀ y hy
  change ∀ᶠ ρ in 𝓝 ρ₀, y < kernelDistance ρ σ
  rcases lt_or_ge y 0 with hy0 | hy0
  · exact Eventually.of_forall fun ρ => hy0.trans_le (kernelDistance_nonneg ρ σ)
  obtain ⟨r, ⟨S, hS, hνS, A, hA, hAS, rfl⟩, hyr⟩ :=
    (lt_csSup_iff (bddAbove_kernelDistance_set ρ₀ σ) ⟨0, zero_mem_kernelDistance_set ρ₀ σ⟩).1 hy
  rw [lt_div_iff₀ hνS] at hyr
  have hSm : MeasurableSet S := hS.measurableSet
  -- a one-sided gap on a measurable subset of `S × U`
  obtain ⟨B, hB, hBS, hyB⟩ : ∃ B : Set (τ × U), MeasurableSet B ∧ B ⊆ S ×ˢ univ ∧
      y * ν.toMeasure.real S < ρ₀.measure.real B - σ.measure.real B := by
    rcases le_total 0 (ρ₀.measure.real A - σ.measure.real A) with h | h
    · exact ⟨A, hA, hAS, by rwa [abs_of_nonneg h] at hyr⟩
    · refine ⟨(S ×ˢ univ) \ A, (hSm.prod MeasurableSet.univ).diff hA, sdiff_subset, ?_⟩
      have hprod : ∀ κ : RelaxedControl τ U ν,
          κ.measure.real (S ×ˢ univ) = ν.toMeasure.real S := fun κ => by
        rw [measureReal_def, measureReal_def, κ.measure_prod_univ hSm]
      rw [measureReal_sdiff hAS hA, measureReal_sdiff hAS hA, hprod, hprod]
      rw [abs_of_nonpos h] at hyr
      linarith
  set η : ℝ := ρ₀.measure.real B - σ.measure.real B - y * ν.toMeasure.real S with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  obtain ⟨O, hBO, hO, hσO⟩ := Set.exists_isOpen_lt_add (μ := σ.measure) B
    (measure_ne_top _ _) (ENNReal.ofReal_pos.2 hηpos).ne'
  have hσOreal : σ.measure.real O < σ.measure.real B + η := by
    have := (ENNReal.toReal_lt_toReal (measure_ne_top _ _)
      (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩)).2 hσO
    rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hηpos.le] at this
  set O' : Set (τ × U) := O ∩ S ×ˢ univ with hO'
  have hO'open : IsOpen O' := hO.inter (hS.prod isOpen_univ)
  have hBO' : B ⊆ O' := subset_inter hBO hBS
  have hσO' : σ.measure.real O' ≤ σ.measure.real O := measureReal_mono inter_subset_left
  have hρBO : ρ₀.measure.real B ≤ ρ₀.measure.real O' := measureReal_mono hBO'
  have hy' : y * ν.toMeasure.real S + σ.measure.real O' < (ρ₀.1 : Measure (τ × U)).real O' := by
    change _ < ρ₀.measure.real O'
    rw [hη] at hσOreal
    linarith
  have hev := ((continuous_subtype_val (p := fun μ : ProbabilityMeasure (τ × U) =>
    μ.map Prod.fst = ν)).tendsto ρ₀).eventually
    (lowerSemicontinuous_measureReal_isOpen hO'open ρ₀.1 _ hy')
  filter_upwards [hev] with ρ hρ
  change y * ν.toMeasure.real S + σ.measure.real O' < ρ.measure.real O' at hρ
  have hle := abs_measureReal_sub_le_kernelDistance ρ σ hS hνS hO'open.measurableSet
    inter_subset_right
  have hgap : y * ν.toMeasure.real S < kernelDistance ρ σ * ν.toMeasure.real S :=
    lt_of_lt_of_le (by linarith) ((le_abs_self _).trans hle)
  exact lt_of_mul_lt_mul_right hgap hνS.le

theorem isClosed_kernelDistance_le (σ : RelaxedControl τ U ν) (ε : ℝ) :
    IsClosed {ρ : RelaxedControl τ U ν | kernelDistance ρ σ ≤ ε} :=
  (lowerSemicontinuous_kernelDistance σ).isClosed_preimage ε

theorem isCompact_kernelDistance_le (σ : RelaxedControl τ U ν) (ε : ℝ) :
    IsCompact {ρ : RelaxedControl τ U ν | kernelDistance ρ σ ≤ ε} :=
  (isClosed_kernelDistance_le σ ε).isCompact

section Kernel

variable [StandardBorelSpace U] [Nonempty U]

omit [BorelSpace τ] [MetricSpace U] [BorelSpace U] [CompactSpace U] in
/-- Disintegration of the occupation mass of a measurable set along its time sections. -/
theorem measureReal_eq_integral_kernel (ρ : RelaxedControl τ U ν) {A : Set (τ × U)}
    (hA : MeasurableSet A) :
    ρ.measure.real A = ∫ t, (ρ.kernel t).real (Prod.mk t ⁻¹' A) ∂ν.toMeasure := by
  rw [measureReal_def, ← ρ.disintegrate, Measure.compProd_apply hA,
    ← integral_toReal (Kernel.measurable_kernel_prodMk_left hA).aemeasurable
      (Eventually.of_forall fun t => measure_lt_top _ _)]
  rfl

omit [MetricSpace τ] [BorelSpace τ] [CompactSpace τ]
  [MetricSpace U] [BorelSpace U] [CompactSpace U] in
theorem integrable_kernel_real (ρ : RelaxedControl τ U ν) {A : Set (τ × U)}
    (hA : MeasurableSet A) :
    Integrable (fun t => (ρ.kernel t).real (Prod.mk t ⁻¹' A)) ν.toMeasure :=
  Integrable.of_bound
    (Kernel.measurable_kernel_prodMk_left hA).ennreal_toReal.aestronglyMeasurable 1
    (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one)

omit [BorelSpace τ] [MetricSpace U] [BorelSpace U] [CompactSpace U] in
theorem measureReal_sub_eq_integral_kernel (ρ σ : RelaxedControl τ U ν) {A : Set (τ × U)}
    (hA : MeasurableSet A) :
    ρ.measure.real A - σ.measure.real A = ∫ t, ((ρ.kernel t).real (Prod.mk t ⁻¹' A) -
      (σ.kernel t).real (Prod.mk t ⁻¹' A)) ∂ν.toMeasure := by
  rw [integral_sub (integrable_kernel_real ρ hA) (integrable_kernel_real σ hA),
    measureReal_eq_integral_kernel ρ hA, measureReal_eq_integral_kernel σ hA]

omit [MetricSpace τ] [BorelSpace τ] [CompactSpace τ]
  [MetricSpace U] [BorelSpace U] [CompactSpace U] in
theorem integrable_kernel_real_set (ρ : RelaxedControl τ U ν) {B : Set U}
    (hB : MeasurableSet B) : Integrable (fun t => (ρ.kernel t).real B) ν.toMeasure :=
  Integrable.of_bound (ρ.kernel.measurable_coe hB).ennreal_toReal.aestronglyMeasurable 1
    (Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one)

omit [BorelSpace τ] [MetricSpace U] [BorelSpace U] [CompactSpace U] in
/-- Occupation mass of a rectangle as a time integral of kernel masses. -/
theorem measureReal_prod_eq_setIntegral_kernel (ρ : RelaxedControl τ U ν) {S : Set τ}
    (hS : MeasurableSet S) {B : Set U} (hB : MeasurableSet B) :
    ρ.measure.real (S ×ˢ B) = ∫ t in S, (ρ.kernel t).real B ∂ν.toMeasure := by
  rw [measureReal_eq_integral_kernel ρ (hS.prod hB), ← integral_indicator hS]
  congr 1
  ext t
  by_cases ht : t ∈ S
  · simp [indicator_of_mem ht, mk_preimage_prod_right ht]
  · simp [indicator_of_notMem ht, mk_preimage_prod_right_eq_empty ht]

omit [MetricSpace U] [BorelSpace U] [CompactSpace U] in
/-- One-sided kernel bound from `d_L ≤ ε`, for a fixed measurable set of controls. -/
theorem ae_kernel_sub_le_of_kernelDistance_le (ρ σ : RelaxedControl τ U ν) {ε : ℝ}
    (hε0 : 0 ≤ ε) (h : kernelDistance ρ σ ≤ ε) {B : Set U} (hB : MeasurableSet B) :
    ∀ᵐ t ∂ν.toMeasure, (ρ.kernel t).real B - (σ.kernel t).real B ≤ ε := by
  set g : τ → ℝ := fun t => (ρ.kernel t).real B - (σ.kernel t).real B with hg
  have hgm : Measurable g :=
    (ρ.kernel.measurable_coe hB).ennreal_toReal.sub (σ.kernel.measurable_coe hB).ennreal_toReal
  have hgb : ∀ t, -1 ≤ g t := fun t => by
    have h1 : (σ.kernel t).real B ≤ 1 := measureReal_le_one
    have h2 : 0 ≤ (ρ.kernel t).real B := measureReal_nonneg
    simp only [hg]
    linarith
  have hgi : Integrable g ν.toMeasure :=
    (integrable_kernel_real_set ρ hB).sub (integrable_kernel_real_set σ hB)
  have hkey : ∀ S : Set τ, IsOpen S → ∫ t in S, g t ∂ν.toMeasure ≤ ε * ν.toMeasure.real S := by
    intro S hS
    have hSm := hS.measurableSet
    have hint : ∫ t in S, g t ∂ν.toMeasure =
        ρ.measure.real (S ×ˢ B) - σ.measure.real (S ×ˢ B) := by
      rw [measureReal_prod_eq_setIntegral_kernel ρ hSm hB,
        measureReal_prod_eq_setIntegral_kernel σ hSm hB,
        integral_sub (integrable_kernel_real_set ρ hB).integrableOn
          (integrable_kernel_real_set σ hB).integrableOn]
    rw [hint]
    have hsub : S ×ˢ B ⊆ S ×ˢ univ := prod_mono le_rfl (subset_univ _)
    rcases (measureReal_nonneg (μ := ν.toMeasure) (s := S)).lt_or_eq with hpos | hzero
    · calc ρ.measure.real (S ×ˢ B) - σ.measure.real (S ×ˢ B)
          ≤ |ρ.measure.real (S ×ˢ B) - σ.measure.real (S ×ˢ B)| := le_abs_self _
        _ ≤ kernelDistance ρ σ * ν.toMeasure.real S :=
          abs_measureReal_sub_le_kernelDistance ρ σ hS hpos (hSm.prod hB) hsub
        _ ≤ ε * ν.toMeasure.real S := mul_le_mul_of_nonneg_right h hpos.le
    · have h1 := measureReal_le_of_subset_prod_univ ρ hSm hsub
      have h2 : 0 ≤ σ.measure.real (S ×ˢ B) := measureReal_nonneg
      rw [← hzero] at h1 ⊢
      linarith
  have hnull : ∀ η : ℝ, 0 < η → ν.toMeasure {t | ε + η ≤ g t} = 0 := by
    intro η hη
    set T : Set τ := {t | ε + η ≤ g t} with hTdef
    have hT : MeasurableSet T := measurableSet_le measurable_const hgm
    by_contra hne
    have hTpos : 0 < ν.toMeasure.real T := by
      rw [measureReal_def]
      exact ENNReal.toReal_pos hne (measure_ne_top _ _)
    set δ : ℝ := η * ν.toMeasure.real T / (2 * (1 + ε)) with hδdef
    have hδ : 0 < δ := by positivity
    obtain ⟨S, hTS, hS, -, hST⟩ := hT.exists_isOpen_sdiff_lt (μ := ν.toMeasure)
      (measure_ne_top _ _) (ENNReal.ofReal_pos.2 hδ).ne'
    have hSTr : ν.toMeasure.real (S \ T) < δ := ENNReal.toReal_lt_of_lt_ofReal hST
    have hsplit : ν.toMeasure.real S = ν.toMeasure.real T + ν.toMeasure.real (S \ T) := by
      rw [measureReal_sdiff hTS hT]
      ring
    have hintsplit : ∫ t in S, g t ∂ν.toMeasure =
        ∫ t in T, g t ∂ν.toMeasure + ∫ t in S \ T, g t ∂ν.toMeasure := by
      rw [← integral_inter_add_sdiff hT hgi.integrableOn, inter_eq_right.2 hTS]
    have h1 : (ε + η) * ν.toMeasure.real T ≤ ∫ t in T, g t ∂ν.toMeasure :=
      setIntegral_ge_of_const_le_real hT (measure_ne_top _ _) (fun t ht => ht) hgi.integrableOn
    have h2 : (-1) * ν.toMeasure.real (S \ T) ≤ ∫ t in S \ T, g t ∂ν.toMeasure :=
      setIntegral_ge_of_const_le_real (hS.measurableSet.diff hT) (measure_ne_top _ _)
        (fun t _ => hgb t) hgi.integrableOn
    have h3 := hkey S hS
    have h4 : η * ν.toMeasure.real T ≤ (1 + ε) * ν.toMeasure.real (S \ T) := by
      rw [hintsplit, hsplit] at h3
      linarith
    have h5 : (1 + ε) * ν.toMeasure.real (S \ T) < (1 + ε) * δ :=
      mul_lt_mul_of_pos_left hSTr (by linarith)
    have h6 : (1 + ε) * δ = η * ν.toMeasure.real T / 2 := by
      rw [hδdef]
      field_simp
    have h7 : 0 < η * ν.toMeasure.real T := mul_pos hη hTpos
    linarith
  rw [ae_iff]
  have hsub : {t | ¬ g t ≤ ε} ⊆ ⋃ n : ℕ, {t | ε + 1 / ((n : ℝ) + 1) ≤ g t} := by
    intro t ht
    simp only [mem_ofPred_eq, not_le] at ht
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 ht)
    exact mem_iUnion.2 ⟨n, by simp only [mem_ofPred_eq]; linarith⟩
  exact measure_mono_null hsub (measure_iUnion_null fun n => hnull _ Nat.one_div_pos_of_nat)

omit [MetricSpace U] [BorelSpace U] [CompactSpace U] in
/-- Two-sided kernel bound from `d_L ≤ ε`, for a fixed measurable set of controls. -/
theorem ae_abs_kernel_sub_le_of_kernelDistance_le (ρ σ : RelaxedControl τ U ν) {ε : ℝ}
    (hε0 : 0 ≤ ε) (h : kernelDistance ρ σ ≤ ε) {B : Set U} (hB : MeasurableSet B) :
    ∀ᵐ t ∂ν.toMeasure, |(ρ.kernel t).real B - (σ.kernel t).real B| ≤ ε := by
  filter_upwards [ae_kernel_sub_le_of_kernelDistance_le ρ σ hε0 h hB,
    ae_kernel_sub_le_of_kernelDistance_le σ ρ hε0 ((kernelDistance_comm σ ρ).trans_le h) hB]
    with t h1 h2
  rw [abs_le]
  constructor <;> linarith

omit [MetricSpace U] [BorelSpace U] [CompactSpace U] in
/-- **`d_L ≤ ε` is the book's `ess-sup_t |ν_t − ν₀t|(Ω) ≤ ε`**: the conditional laws differ by at
most `ε` in total variation (on every measurable set of controls) for `ν`-a.e. time. -/
theorem kernelDistance_le_iff_ae (ρ σ : RelaxedControl τ U ν) {ε : ℝ} (hε : 0 ≤ ε) :
    kernelDistance ρ σ ≤ ε ↔ ∀ᵐ t ∂ν.toMeasure, ∀ B : Set U, MeasurableSet B →
      |(ρ.kernel t).real B - (σ.kernel t).real B| ≤ ε := by
  constructor
  · intro h
    set C : Set (Set U) := generateSetAlgebra (MeasurableSpace.countableGeneratingSet U) with hCdef
    have hCc : C.Countable := countable_generateSetAlgebra
      MeasurableSpace.countable_countableGeneratingSet
    have hgen : ‹MeasurableSpace U› = MeasurableSpace.generateFrom C := by
      rw [hCdef, generateFrom_generateSetAlgebra_eq,
        MeasurableSpace.generateFrom_countableGeneratingSet]
    have hCm : ∀ A ∈ C, MeasurableSet A := fun A hA => by
      have := MeasurableSpace.measurableSet_generateFrom hA
      rwa [← hgen] at this
    have hall : ∀ᵐ t ∂ν.toMeasure, ∀ A ∈ C,
        |(ρ.kernel t).real A - (σ.kernel t).real A| ≤ ε :=
      (ae_ball_iff hCc).2 fun A hA => ae_abs_kernel_sub_le_of_kernelDistance_le ρ σ hε h
        (hCm A hA)
    filter_upwards [hall] with t ht B hB
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    obtain ⟨A, hAC, hAB⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing
      (μ := ρ.kernel t + σ.kernel t) isSetAlgebra_generateSetAlgebra.isSetRing
      ⟨{univ}, countable_singleton _,
        singleton_subset_iff.2 isSetAlgebra_generateSetAlgebra.univ_mem, by simp⟩
      hgen hB (ENNReal.ofReal_pos.2 hδ)
    have hsum : (ρ.kernel t).real (symmDiff A B) + (σ.kernel t).real (symmDiff A B) < δ := by
      have := ENNReal.toReal_lt_of_lt_ofReal hAB
      rwa [Measure.add_apply, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
        at this
    have h1 := abs_measureReal_sub_le_measureReal_symmDiff (ρ.kernel t) A B
    have h2 := abs_measureReal_sub_le_measureReal_symmDiff (σ.kernel t) A B
    have h3 := ht A hAC
    rw [abs_le] at h1 h2 h3
    rw [abs_lt]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  · intro h
    refine csSup_le ⟨0, zero_mem_kernelDistance_set ρ σ⟩ ?_
    rintro r ⟨S, hS, hνS, A, hA, hAS, rfl⟩
    rw [div_le_iff₀ hνS, measureReal_sub_eq_integral_kernel ρ σ hA, ← Real.norm_eq_abs]
    have hae : ∀ᵐ t ∂ν.toMeasure, ‖(ρ.kernel t).real (Prod.mk t ⁻¹' A) -
        (σ.kernel t).real (Prod.mk t ⁻¹' A)‖ ≤ S.indicator (fun _ => ε) t := by
      filter_upwards [h] with t ht
      by_cases htS : t ∈ S
      · rw [indicator_of_mem htS, Real.norm_eq_abs]
        exact ht _ (measurable_prodMk_left hA)
      · have hempty : Prod.mk t ⁻¹' A = ∅ :=
          eq_empty_of_forall_notMem fun u hu => htS (hAS hu).1
        simp [hempty, indicator_of_notMem htS]
    have hbound := norm_integral_le_of_norm_le
      ((integrable_const ε).indicator hS.measurableSet) hae
    rwa [integral_indicator_const _ hS.measurableSet, smul_eq_mul, mul_comm] at hbound

omit [MetricSpace U] [BorelSpace U] [CompactSpace U] in
/-- Consequence used downstream: kernel averages of a bounded measurable integrand differ by at
most `2 ε C` for a.e. time. -/
theorem abs_integral_kernel_sub_le (ρ σ : RelaxedControl τ U ν) {ε C : ℝ} (hε : 0 ≤ ε)
    (h : kernelDistance ρ σ ≤ ε) {f : U → ℝ} (hf : Measurable f) (hC : ∀ u, |f u| ≤ C) :
    ∀ᵐ t ∂ν.toMeasure, |∫ u, f u ∂ρ.kernel t - ∫ u, f u ∂σ.kernel t| ≤ 2 * ε * C := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC (Classical.arbitrary U))
  filter_upwards [(kernelDistance_le_iff_ae ρ σ hε).1 h] with t ht
  exact abs_integral_sub_le_of_forall_abs_measureReal_sub_le _ _ ht hf hC hC0

end Kernel

end Compact

end OptimalControl.RelaxedControl
