/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.RelaxedControls
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Normalized Lebesgue time marginals on a positive finite horizon -/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace OptimalControl

/-- Compact time type for a finite horizon. -/
abbrev ControlTime (T : ℝ) := Icc (0 : ℝ) T

/-- Lebesgue measure on the time subtype, before normalization. -/
noncomputable def horizonVolume (T : ℝ) : Measure (ControlTime T) :=
  volume.comap ((↑) : ControlTime T → ℝ)

/-- Exact mass of the time horizon. -/
theorem horizonVolume_univ (T : ℝ) : horizonVolume T univ = ENNReal.ofReal T := by
  rw [horizonVolume, comap_subtype_coe_apply measurableSet_Icc]
  rw [image_univ, Subtype.range_coe]
  rw [Real.volume_Icc, sub_zero]

/-- The probability time marginal is normalized Lebesgue measure, not an
unspecified probability distribution on the horizon. -/
noncomputable def horizonProbability (T : ℝ) (hT : 0 < T) : ProbabilityMeasure (ControlTime T) :=
  ⟨(ENNReal.ofReal T)⁻¹ • horizonVolume T, by
    constructor
    rw [Measure.smul_apply, horizonVolume_univ, smul_eq_mul]
    exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hT)) ENNReal.ofReal_ne_top⟩

/-- The normalization is undone by multiplying by the horizon length. -/
theorem scale_horizonProbability (T : ℝ) (hT : 0 < T) :
    ENNReal.ofReal T • (horizonProbability T hT).toMeasure = horizonVolume T := by
  change ENNReal.ofReal T • ((ENNReal.ofReal T)⁻¹ • horizonVolume T) = _
  rw [smul_smul, ENNReal.mul_inv_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hT))
    ENNReal.ofReal_ne_top, one_smul]

/-- Under the subtype inclusion, unnormalized horizon volume is ordinary
Lebesgue measure restricted to `[0,T]`. -/
theorem map_horizonVolume (T : ℝ) :
    (horizonVolume T).map ((↑) : ControlTime T → ℝ) = volume.restrict (Icc 0 T) :=
  map_comap_subtype_coe measurableSet_Icc volume

/-- The mass of a time subinterval, after undoing normalization. -/
theorem horizonVolume_Ioc (T : ℝ) (r s : ControlTime T) :
    horizonVolume T (Ioc r s) = ENNReal.ofReal ((s : ℝ) - r) := by
  rw [horizonVolume, comap_subtype_coe_apply measurableSet_Icc]
  have he : ((↑) : ControlTime T → ℝ) '' Ioc r s = Ioc (r : ℝ) (s : ℝ) := by
    ext t
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro ht
      exact ⟨⟨t, ⟨le_trans r.2.1 ht.1.le, le_trans ht.2 s.2.2⟩⟩, ht, rfl⟩
  rw [he, Real.volume_Ioc]

/-- Initial time as an element of the compact horizon. -/
def timeZero (T : ℝ) (hT : 0 ≤ T) : ControlTime T := ⟨0, le_rfl, hT⟩

/-- Terminal time as an element of the compact horizon. -/
def timeEnd (T : ℝ) (hT : 0 ≤ T) : ControlTime T := ⟨T, hT, le_rfl⟩

/-- Exact real-valued interval mass after rescaling the probability marginal. -/
theorem scale_horizonProbability_real_Ioc (T : ℝ) (hT : 0 < T)
    (r s : ControlTime T) (hrs : r ≤ s) :
    T * (horizonProbability T hT).toMeasure.real (Ioc r s) = (s : ℝ) - r := by
  have h := congrArg (fun μ : Measure (ControlTime T) => μ.real (Ioc r s))
    (scale_horizonProbability T hT)
  simp only [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hT.le, horizonVolume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hrs)] at h
  exact h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Bochner integration with the normalized marginal is exactly integration
with Lebesgue horizon volume after multiplication by `T`. -/
theorem integral_horizonProbability (T : ℝ) (hT : 0 < T) (g : ControlTime T → E) :
    T • (∫ t, g t ∂horizonProbability T hT) = ∫ t, g t ∂horizonVolume T := by
  rw [← scale_horizonProbability T hT, integral_smul_measure]
  simp [ENNReal.toReal_ofReal hT.le]

end OptimalControl
