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
        Measure.withDensityᵥ_apply hv measurableSet_Ioc]
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
    _ = ∫⁻ t, ‖v t‖ₑ ∂μ := by simp [ν, Measure.withDensity_apply]

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
theorem withDensity_enorm_Ioc_eq_eVariationOn [NoAtoms μ]
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
      Measure.withDensityᵥ_apply hv measurableSet_Icc, integral_Icc_eq_integral_Ioc]
    exact hlaw s t hst
  calc
    _ = (μ.withDensityᵥ v).variation (Ioc a b) := by
      rw [Measure.variation_withDensityᵥ hv]
    _ = hBV.vectorMeasure.variation (Ioc a b) := by rw [heq]
    _ = eVariationOn x.rightLim (Ioc a b) := hBV.variation_vectorMeasure_Ioc
    _ = eVariationOn x (Ioc a b) := by rw [hr]

end DynamicalSystems.ClassicalEquiAC
