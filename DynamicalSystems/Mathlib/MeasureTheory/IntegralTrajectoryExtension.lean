/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.MeasureTheory.ClassicalEquiAbsoluteContinuityUniformIntegrable

/-!
# Constant trajectory and zero-density extensions

An integral trajectory on a moving interval is extended constantly outside its
own interval. Its velocity and running-cost densities are extended by zero.
The original integral laws and costs are preserved on a common compact time
interval. Classical equi-absolute continuity then gives uniform integrability
of these actual extended velocities.
-/

@[expose] public section

open Set MeasureTheory
open scoped Topology

namespace DynamicalSystems.ClassicalEquiAC

/-- Constant extension of a path from its own interval. -/
def constantExtension {E : Type*} (l r : ℝ) (x : ℝ → E) : ℝ → E :=
  fun t ↦ x (clampTime l r t)

/-- Zero extension of a density from its own interval. The excluded left
endpoint is immaterial for Lebesgue integrals and makes interval intersections
agree exactly with the clamping identity. -/
noncomputable def zeroExtension {E : Type*} [Zero E] (l r : ℝ) (v : ℝ → E) : ℝ → E :=
  (Ioc l r).indicator v

/-- Clamping time is continuous, including at both endpoints. -/
theorem continuous_clampTime (l r : ℝ) : Continuous (clampTime l r) :=
  continuous_const.max (continuous_const.min continuous_id)

/-- Constant extension requires only continuity on the original interval. -/
theorem continuous_constantExtension {E : Type*} [TopologicalSpace E]
    {l r : ℝ} (hlr : l ≤ r) {x : ℝ → E} (hx : ContinuousOn x (Icc l r)) :
    Continuous (constantExtension l r x) :=
  hx.comp_continuous (continuous_clampTime l r) (fun t ↦ clampTime_mem_Icc l r t hlr)

/-- The extension agrees with the original path throughout its own interval. -/
theorem constantExtension_eq {E : Type*} {l r t : ℝ} (x : ℝ → E)
    (ht : t ∈ Icc l r) : constantExtension l r x t = x t := by
  simp only [constantExtension, clampTime_eq_self ht]

/-- The extension is constant to the left of its own interval. -/
theorem constantExtension_left {E : Type*} {l r t : ℝ} (x : ℝ → E)
    (ht : t ≤ l) : constantExtension l r x t = x l := by
  simp only [constantExtension, clampTime_eq_left ht]

/-- The extension is constant to the right of its own interval. -/
theorem constantExtension_right {E : Type*} {l r t : ℝ} (x : ℝ → E)
    (hlr : l ≤ r) (ht : r ≤ t) : constantExtension l r x t = x r := by
  simp only [constantExtension, clampTime_eq_right hlr ht]

section Integrals

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- An integrable original density has an integrable zero extension on the
whole real line; ambient integrability is not a new source assumption. -/
theorem integrable_zeroExtension {l r : ℝ} {v : ℝ → E}
    (hv : IntegrableOn v (Icc l r)) : Integrable (zeroExtension l r v) :=
  (integrable_indicator_iff measurableSet_Ioc).mpr (hv.mono_set Ioc_subset_Icc_self)

/-- Zero extension preserves the complete source integral exactly. -/
theorem integral_zeroExtension_restrict {a b l r : ℝ} (hal : a ≤ l) (hrb : r ≤ b)
    (v : ℝ → E) :
    (∫ z, zeroExtension l r v z ∂volume.restrict (Icc a b)) = ∫ z in Icc l r, v z := by
  conv_rhs => rw [integral_Icc_eq_integral_Ioc]
  change (∫ z, (Ioc l r).indicator v z ∂volume.restrict (Icc a b)) = _
  rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (show Ioc l r ⊆ Icc a b from
      fun z hz ↦ ⟨hal.trans hz.1.le, hz.2.trans hrb⟩)]

/-- Intersecting a source interval with an ambient subinterval is exactly
clamping the latter's endpoints. This identity underlies the extended dynamics. -/
theorem setIntegral_zeroExtension_restrict {a b l r : ℝ}
    (hal : a ≤ l) (hrb : r ≤ b) (hlr : l ≤ r) (v : ℝ → E) (s t : ℝ) :
    (∫ z in Ioc s t, zeroExtension l r v z ∂volume.restrict (Icc a b)) =
      ∫ z in Ioc (clampTime l r s) (clampTime l r t), v z := by
  have hsets : (Ioc l r ∩ Ioc s t) ∩ Icc a b = Ioc s t ∩ Ioc l r := by
    ext z
    simp only [mem_inter_iff, mem_Ioc, mem_Icc]
    constructor
    · rintro ⟨⟨hzlr, hzst⟩, _⟩
      exact ⟨hzst, hzlr⟩
    · rintro ⟨hzst, hzlr⟩
      exact ⟨⟨hzlr, hzst⟩, ⟨hal.trans hzlr.1.le, hzlr.2.trans hrb⟩⟩
  change (∫ z in Ioc s t, (Ioc l r).indicator v z ∂volume.restrict (Icc a b)) = _
  rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    Measure.restrict_restrict (measurableSet_Ioc.inter measurableSet_Ioc),
    hsets, Ioc_clampTime _ _ _ _ hlr]

/-- The actual source integral dynamics imply the global integral difference
law for the constant path extension and the zero velocity extension. -/
theorem constantExtension_integral_law {a b l r : ℝ}
    (hal : a ≤ l) (hrb : r ≤ b) (hlr : l ≤ r) (x v : ℝ → E)
    (hlaw : ∀ s ∈ Icc l r, ∀ t ∈ Icc l r, s ≤ t →
      x t - x s = ∫ z in Ioc s t, v z) (s t : ℝ) (hst : s ≤ t) :
    constantExtension l r x t - constantExtension l r x s =
      ∫ z in Ioc s t, zeroExtension l r v z ∂volume.restrict (Icc a b) := by
  rw [setIntegral_zeroExtension_restrict hal hrb hlr]
  exact hlaw _ (clampTime_mem_Icc _ _ _ hlr) _ (clampTime_mem_Icc _ _ _ hlr)
    (clampTime_mono _ _ hst)

/-- Oriented-interval form of the extended integral law. -/
theorem constantExtension_intervalIntegral_law {a b l r : ℝ}
    (hal : a ≤ l) (hrb : r ≤ b) (hlr : l ≤ r) (x v : ℝ → E)
    (hlaw : ∀ s ∈ Icc l r, ∀ t ∈ Icc l r, s ≤ t →
      x t - x s = ∫ z in Ioc s t, v z) (s t : ℝ) :
    constantExtension l r x t - constantExtension l r x s =
      ∫ z in s..t, zeroExtension l r v z ∂volume.restrict (Icc a b) := by
  rcases le_total s t with hst | hts
  · rw [intervalIntegral.integral_of_le hst]
    exact constantExtension_integral_law hal hrb hlr x v hlaw s t hst
  · rw [intervalIntegral.integral_of_ge hts,
      ← constantExtension_integral_law hal hrb hlr x v hlaw t s hts]
    abel

end Integrals

/-- Classical equi-AC of original moving-interval trajectories produces
uniform integrability of their zero-extended velocities on a common interval.
The ambient integral laws, integrability and classical modulus are all derived
from source data in this theorem. -/
theorem unifIntegrable_zeroExtension_of_equiAC
    {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {a b : ℝ} (hab : a ≤ b) (l r : ι → ℝ) (x v : ι → ℝ → E)
    (htime : ∀ i, a ≤ l i ∧ l i ≤ r i ∧ r i ≤ b)
    (hcont : ∀ i, ContinuousOn (x i) (Icc (l i) (r i)))
    (hv : ∀ i, IntegrableOn (v i) (Icc (l i) (r i)))
    (hlaw : ∀ i s, s ∈ Icc (l i) (r i) → ∀ t, t ∈ Icc (l i) (r i) → s ≤ t →
      x i t - x i s = ∫ z in Ioc s t, v i z)
    (hx : EquiAbsolutelyContinuousOn x l r) :
    UnifIntegrable (fun i ↦ zeroExtension (l i) (r i) (v i)) 1
      (volume.restrict (Icc a b)) := by
  apply (hx.clamp (fun i ↦ (htime i).2.1) a b).unifIntegrable_Icc hab
  · intro i
    exact (integrable_zeroExtension (hv i)).restrict
  · intro i
    exact continuous_constantExtension (htime i).2.1 (hcont i)
  · intro i s t hst
    exact constantExtension_integral_law (htime i).1 (htime i).2.2 (htime i).2.1
      (x i) (v i) (hlaw i) s t hst

end DynamicalSystems.ClassicalEquiAC
