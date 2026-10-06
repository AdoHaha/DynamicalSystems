/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module
public import DynamicalSystems.OptimalControl.ContinuousTime.ControlHorizon
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Continuous integral paths from bounded measurable velocities

The path is constructed from its genuine integral, and its Lipschitz regularity
is derived using the exact Lebesgue time marginal.
-/
@[expose] public section
open Set MeasureTheory
open scoped NNReal
namespace OptimalControl

/-- The normalized Lebesgue horizon has no atoms, including its endpoints. -/
instance horizonProbability_nullSingleton (T : ℝ) (hT : 0 < T) :
    NullSingletonClass (horizonProbability T hT).toMeasure where
  measure_singleton t := by
    change ((ENNReal.ofReal T)⁻¹ • horizonVolume T) {t} = 0
    rw [Measure.smul_apply, horizonVolume, comap_subtype_coe_apply measurableSet_Icc]
    simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {T : ℝ} (hT : 0 < T) (x₀ : E) (u : ControlTime T → E)

/-- Integrate a velocity against the normalized horizon marginal. -/
noncomputable def integralControlPath (t : ControlTime T) : E :=
  x₀ + T • ∫ s in Ioc (timeZero T hT.le) t, u s ∂horizonProbability T hT

/-- The initial value follows from the empty initial integration interval. -/
theorem integralControlPath_initial :
    integralControlPath hT x₀ u (timeZero T hT.le) = x₀ := by
  simp [integralControlPath]

/-- On the compact time type, the actual path is also the strict-prefix integral.
Lebesgue endpoint nullity justifies this identity even for discontinuous controls. -/
theorem integralControlPath_prefix [CompleteSpace E]
    (hu : Integrable u (horizonProbability T hT).toMeasure) (t : ControlTime T) :
    integralControlPath hT x₀ u t = x₀ + T • ∫ s in Iio t, u s
      ∂horizonProbability T hT := by
  have hmin : Iic (timeZero T hT.le) = ({timeZero T hT.le} : Set (ControlTime T)) := by
    ext s
    simp only [mem_Iic, mem_singleton_iff]
    exact ⟨fun hs ↦ le_antisymm hs s.2.1, fun hs ↦ hs.le⟩
  have he := setIntegral_sdiff measurableSet_Ioc hu.integrableOn
    (Ioc_subset_Iic_self : Ioc (timeZero T hT.le) t ⊆ Iic t)
  have hle : timeZero T hT.le ≤ t := t.2.1
  rw [Iic_sdiff_Ioc_self_of_le hle, hmin, integral_singleton, measureReal_def,
    measure_singleton, ENNReal.toReal_zero, zero_smul] at he
  have hi : (∫ s in Ioc (timeZero T hT.le) t, u s ∂horizonProbability T hT) =
      ∫ s in Iic t, u s ∂horizonProbability T hT := by
    exact (sub_eq_zero.mp he.symm).symm
  rw [integralControlPath, hi, integral_Iic_eq_integral_Iio]

/-- The terminal prefix equals the full horizon integral. -/
theorem integralControlPath_terminal [CompleteSpace E]
    (hu : Integrable u (horizonProbability T hT).toMeasure) :
    integralControlPath hT x₀ u (timeEnd T hT.le) =
      x₀ + T • ∫ s, u s ∂horizonProbability T hT := by
  rw [integralControlPath_prefix hT x₀ u hu, ← integral_Iic_eq_integral_Iio]
  have hmax : Iic (timeEnd T hT.le) = (univ : Set (ControlTime T)) := by
    ext s
    simp only [mem_Iic, mem_univ, iff_true]
    exact s.2.2
  rw [hmax, setIntegral_univ]

/-- The full increment between any ordered times is the original velocity integral. -/
theorem integralControlPath_sub
    (hu : Integrable u (horizonProbability T hT).toMeasure)
    {r s : ControlTime T} (hrs : r ≤ s) :
    integralControlPath hT x₀ u s - integralControlPath hT x₀ u r =
      T • ∫ t in Ioc r s, u t ∂horizonProbability T hT := by
  let a := timeZero T hT.le
  have har : a ≤ r := r.2.1
  have hdiff : Ioc a s \ Ioc a r = Ioc r s := by
    ext t
    simp only [Set.mem_sdiff, mem_Ioc]
    constructor
    · rintro ⟨⟨hat, hts⟩, hn⟩
      exact ⟨lt_of_not_ge (fun htr ↦ hn ⟨hat, htr⟩), hts⟩
    · rintro ⟨hrt, hts⟩
      exact ⟨⟨har.trans_lt hrt, hts⟩, fun ht ↦ (not_le_of_gt hrt) ht.2⟩
  have heq := setIntegral_sdiff measurableSet_Ioc hu.integrableOn
    (Ioc_subset_Ioc_right hrs : Ioc a r ⊆ Ioc a s)
  rw [hdiff] at heq
  simp only [integralControlPath, add_sub_add_left_eq_sub, ← smul_sub]
  rw [← heq]

/-- Bounded velocities yield a Lipschitz path without assuming trajectory regularity. -/
theorem lipschitzWith_integralControlPath
    (hu : Integrable u (horizonProbability T hT).toMeasure)
    {M : ℝ≥0} (hM : ∀ t, ‖u t‖ ≤ M) :
    LipschitzWith M (integralControlPath hT x₀ u) := by
  have hb : ∀ r s : ControlTime T, r ≤ s →
      dist (integralControlPath hT x₀ u s) (integralControlPath hT x₀ u r) ≤
        M * dist s r := by
    intro r s hrs
    rw [dist_eq_norm, integralControlPath_sub hT x₀ u hu hrs,
      norm_smul, Real.norm_of_nonneg hT.le]
    have hn : ‖∫ t in Ioc r s, u t ∂horizonProbability T hT‖ ≤
        M * (horizonProbability T hT).toMeasure.real (Ioc r s) :=
      norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) (fun t _ ↦ hM t)
    calc
      _ ≤ T * (M * (horizonProbability T hT).toMeasure.real (Ioc r s)) :=
        mul_le_mul_of_nonneg_left hn hT.le
      _ = M * ((s : ℝ) - r) := by
        rw [mul_left_comm, scale_horizonProbability_real_Ioc T hT r s hrs]
      _ = M * dist s r := by
        rw [Subtype.dist_eq, Real.dist_eq,
          abs_of_nonneg (sub_nonneg.mpr (show (r : ℝ) ≤ s from hrs))]
  apply LipschitzWith.of_dist_le_mul
  intro r s
  rcases le_total r s with hrs | hsr
  · simpa only [dist_comm] using hb r s hrs
  · exact hb s r hsr

end OptimalControl
