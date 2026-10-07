/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.RelaxedKernelDistance
public import Mathlib.Probability.Kernel.Disintegration.Unique

/-!
# Convex combinations of relaxed controls

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.35)–(11.3.37): the
variation `ν(θ) = ν^ε + θ(ν − ν^ε)` of the relaxed control used to derive the `ε`-level
Hamiltonian inequality.  Relaxed controls with a fixed time marginal form a convex set; occupation
integrals are affine in `θ`, the conditional kernels combine a.e. convexly, and the kernel-wise
distance is convex.

Book citations live in docstrings only.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace OptimalControl.RelaxedControl

variable {τ U : Type*} [MeasurableSpace τ] [MeasurableSpace U] {ν : ProbabilityMeasure τ}

theorem ofReal_one_sub_add_ofReal {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) :
    ENNReal.ofReal (1 - θ) + ENNReal.ofReal θ = 1 := by
  rw [← ENNReal.ofReal_add (by linarith [hθ.2]) hθ.1]
  simp

/-- The underlying measure `(1 − θ) ρ + θ σ` of a mixture. -/
noncomputable def mixMeasure (θ : ℝ) (ρ σ : RelaxedControl τ U ν) : Measure (τ × U) :=
  ENNReal.ofReal (1 - θ) • ρ.measure + ENNReal.ofReal θ • σ.measure

theorem isProbabilityMeasure_mixMeasure {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1)
    (ρ σ : RelaxedControl τ U ν) : IsProbabilityMeasure (mixMeasure θ ρ σ) :=
  ⟨by rw [mixMeasure, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
      measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one, ofReal_one_sub_add_ofReal hθ]⟩

theorem map_fst_mixMeasure {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (ρ σ : RelaxedControl τ U ν) :
    (mixMeasure θ ρ σ).map Prod.fst = ν.toMeasure := by
  have h1 : ρ.measure.map Prod.fst = ν.toMeasure := ρ.fst_measure
  have h2 : σ.measure.map Prod.fst = ν.toMeasure := σ.fst_measure
  rw [mixMeasure, Measure.map_add _ _ measurable_fst,
    Measure.map_smul _ measurable_fst.aemeasurable, Measure.map_smul _ measurable_fst.aemeasurable,
    h1, h2, ← add_smul, ofReal_one_sub_add_ofReal hθ, one_smul]

/-- The convex combination `(1 − θ) ρ + θ σ` of two relaxed controls, `θ ∈ [0,1]`. -/
noncomputable def mix (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (ρ σ : RelaxedControl τ U ν) :
    RelaxedControl τ U ν :=
  ⟨⟨mixMeasure θ ρ σ, isProbabilityMeasure_mixMeasure hθ ρ σ⟩, by
    apply Subtype.ext
    exact map_fst_mixMeasure hθ ρ σ⟩

theorem mix_measure (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (ρ σ : RelaxedControl τ U ν) :
    (mix θ hθ ρ σ).measure
      = ENNReal.ofReal (1 - θ) • ρ.measure + ENNReal.ofReal θ • σ.measure := rfl

theorem mix_zero (ρ σ : RelaxedControl τ U ν) : mix 0 ⟨le_rfl, zero_le_one⟩ ρ σ = ρ := by
  apply Subtype.ext
  apply Subtype.ext
  change mixMeasure 0 ρ σ = ρ.measure
  simp [mixMeasure]

theorem mix_one (ρ σ : RelaxedControl τ U ν) : mix 1 ⟨zero_le_one, le_rfl⟩ ρ σ = σ := by
  apply Subtype.ext
  apply Subtype.ext
  change mixMeasure 1 ρ σ = σ.measure
  simp [mixMeasure]

theorem mix_measureReal (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (ρ σ : RelaxedControl τ U ν)
    (A : Set (τ × U)) :
    (mix θ hθ ρ σ).measure.real A = (1 - θ) * ρ.measure.real A + θ * σ.measure.real A := by
  rw [measureReal_def, mix_measure, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    smul_eq_mul, smul_eq_mul,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith [hθ.2]),
    ENNReal.toReal_ofReal hθ.1]
  rfl

/-- Occupation integrals are affine in `θ`. -/
theorem integral_mix {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (θ : ℝ)
    (hθ : θ ∈ Icc (0 : ℝ) 1) (ρ σ : RelaxedControl τ U ν) {f : τ × U → E}
    (hρ : Integrable f ρ.measure) (hσ : Integrable f σ.measure) :
    ∫ z, f z ∂(mix θ hθ ρ σ).measure
      = (1 - θ) • ∫ z, f z ∂ρ.measure + θ • ∫ z, f z ∂σ.measure := by
  rw [mix_measure, integral_add_measure (hρ.smul_measure ENNReal.ofReal_ne_top)
    (hσ.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (by linarith [hθ.2]), ENNReal.toReal_ofReal hθ.1]

section Kernel

variable [StandardBorelSpace U] [Nonempty U]

/-- The pointwise convex combination of the conditional kernels, as a kernel. -/
noncomputable def mixKernel (θ : ℝ) (ρ σ : RelaxedControl τ U ν) : Kernel τ U where
  toFun t := ENNReal.ofReal (1 - θ) • ρ.kernel t + ENNReal.ofReal θ • σ.kernel t
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
    exact ((ρ.kernel.measurable_coe hs).const_mul _).add ((σ.kernel.measurable_coe hs).const_mul _)

theorem mixKernel_apply (θ : ℝ) (ρ σ : RelaxedControl τ U ν) (t : τ) :
    mixKernel θ ρ σ t = ENNReal.ofReal (1 - θ) • ρ.kernel t + ENNReal.ofReal θ • σ.kernel t :=
  rfl

theorem isMarkovKernel_mixKernel {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (ρ σ : RelaxedControl τ U ν) :
    IsMarkovKernel (mixKernel θ ρ σ) :=
  ⟨fun t => ⟨by rw [mixKernel_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      measure_univ, measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
      ofReal_one_sub_add_ofReal hθ]⟩⟩

theorem compProd_mixKernel {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (ρ σ : RelaxedControl τ U ν) :
    ν.toMeasure ⊗ₘ mixKernel θ ρ σ
      = ENNReal.ofReal (1 - θ) • ρ.measure + ENNReal.ofReal θ • σ.measure := by
  have := isMarkovKernel_mixKernel hθ ρ σ
  ext s hs
  rw [Measure.compProd_apply hs, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    ← ρ.disintegrate, ← σ.disintegrate, Measure.compProd_apply hs, Measure.compProd_apply hs,
    smul_eq_mul, smul_eq_mul, ← lintegral_const_mul _ (Kernel.measurable_kernel_prodMk_left hs),
    ← lintegral_const_mul _ (Kernel.measurable_kernel_prodMk_left hs),
    ← lintegral_add_left ((Kernel.measurable_kernel_prodMk_left hs).const_mul _)]
  rfl

/-- The conditional kernel of a mixture is the pointwise convex combination, `ν`-a.e. -/
theorem kernel_mix_ae (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (ρ σ : RelaxedControl τ U ν) :
    ∀ᵐ t ∂ν.toMeasure, (mix θ hθ ρ σ).kernel t
      = ENNReal.ofReal (1 - θ) • ρ.kernel t + ENNReal.ofReal θ • σ.kernel t := by
  have := isMarkovKernel_mixKernel hθ ρ σ
  have hκ : (mix θ hθ ρ σ).measure = (mix θ hθ ρ σ).measure.fst ⊗ₘ mixKernel θ ρ σ := by
    rw [fst_measure, compProd_mixKernel hθ, mix_measure]
  have h := eq_condKernel_of_measure_eq_compProd (mixKernel θ ρ σ) hκ
  rw [fst_measure] at h
  filter_upwards [h] with t ht
  exact ht.symm

/-- Averages against the kernel of a mixture, `ν`-a.e. (for integrable-in-`u` integrands). -/
theorem integral_kernel_mix_ae {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (θ : ℝ)
    (hθ : θ ∈ Icc (0 : ℝ) 1) (ρ σ : RelaxedControl τ U ν) {f : τ × U → E}
    (hρ : ∀ᵐ t ∂ν.toMeasure, Integrable (fun u => f (t, u)) (ρ.kernel t))
    (hσ : ∀ᵐ t ∂ν.toMeasure, Integrable (fun u => f (t, u)) (σ.kernel t)) :
    ∀ᵐ t ∂ν.toMeasure, ∫ u, f (t, u) ∂(mix θ hθ ρ σ).kernel t
      = (1 - θ) • ∫ u, f (t, u) ∂ρ.kernel t + θ • ∫ u, f (t, u) ∂σ.kernel t := by
  filter_upwards [kernel_mix_ae θ hθ ρ σ, hρ, hσ] with t ht h1 h2
  rw [ht, integral_add_measure (h1.smul_measure ENNReal.ofReal_ne_top)
    (h2.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (by linarith [hθ.2]), ENNReal.toReal_ofReal hθ.1]

end Kernel

section Distance

variable [MetricSpace τ] [BorelSpace τ] [CompactSpace τ]
  [MetricSpace U] [BorelSpace U] [CompactSpace U]

omit [CompactSpace τ] [MetricSpace U] [BorelSpace U] [CompactSpace U] in
/-- The kernel distance to a fixed control is convex along mixtures. -/
theorem kernelDistance_mix_le (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (ρ σ κ : RelaxedControl τ U ν) :
    kernelDistance (mix θ hθ ρ σ) κ ≤ (1 - θ) * kernelDistance ρ κ + θ * kernelDistance σ κ := by
  refine csSup_le ⟨0, zero_mem_kernelDistance_set _ _⟩ ?_
  rintro r ⟨S, hS, hνS, A, hA, hAS, rfl⟩
  have h0 : 0 ≤ 1 - θ := by linarith [hθ.2]
  have hθ0 : 0 ≤ θ := hθ.1
  have heq : (mix θ hθ ρ σ).measure.real A - κ.measure.real A
      = (1 - θ) * (ρ.measure.real A - κ.measure.real A)
        + θ * (σ.measure.real A - κ.measure.real A) := by
    rw [mix_measureReal]
    ring
  rw [div_le_iff₀ hνS, heq]
  calc |(1 - θ) * (ρ.measure.real A - κ.measure.real A)
          + θ * (σ.measure.real A - κ.measure.real A)|
      ≤ |(1 - θ) * (ρ.measure.real A - κ.measure.real A)|
          + |θ * (σ.measure.real A - κ.measure.real A)| := abs_add_le _ _
    _ = (1 - θ) * |ρ.measure.real A - κ.measure.real A|
          + θ * |σ.measure.real A - κ.measure.real A| := by
        rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg hθ0]
    _ ≤ (1 - θ) * (kernelDistance ρ κ * ν.toMeasure.real S)
          + θ * (kernelDistance σ κ * ν.toMeasure.real S) :=
        add_le_add
          (mul_le_mul_of_nonneg_left
            (abs_measureReal_sub_le_kernelDistance ρ κ hS hνS hA hAS) h0)
          (mul_le_mul_of_nonneg_left
            (abs_measureReal_sub_le_kernelDistance σ κ hS hνS hA hAS) hθ0)
    _ = ((1 - θ) * kernelDistance ρ κ + θ * kernelDistance σ κ) * ν.toMeasure.real S := by ring

omit [CompactSpace τ] [MetricSpace U] [BorelSpace U] [CompactSpace U] in
/-- Along the segment from `ρ` to `σ` the distance from `ρ` is at most `θ · d(σ,ρ)`
(so mixtures stay in the `ε`-ball of `ρ₀` whenever `ρ` and `σ` do). -/
theorem kernelDistance_mix_left_le (θ : ℝ) (hθ : θ ∈ Icc (0 : ℝ) 1) (ρ σ : RelaxedControl τ U ν) :
    kernelDistance (mix θ hθ ρ σ) ρ ≤ θ * kernelDistance σ ρ := by
  refine csSup_le ⟨0, zero_mem_kernelDistance_set _ _⟩ ?_
  rintro r ⟨S, hS, hνS, A, hA, hAS, rfl⟩
  have hθ0 : 0 ≤ θ := hθ.1
  have heq : (mix θ hθ ρ σ).measure.real A - ρ.measure.real A
      = θ * (σ.measure.real A - ρ.measure.real A) := by
    rw [mix_measureReal]
    ring
  rw [div_le_iff₀ hνS, heq, abs_mul, abs_of_nonneg hθ0, mul_assoc]
  exact mul_le_mul_of_nonneg_left (abs_measureReal_sub_le_kernelDistance σ ρ hS hνS hA hAS) hθ0

end Distance

end OptimalControl.RelaxedControl
