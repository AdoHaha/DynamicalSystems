/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integration by parts for primitives of integrable functions, and the du Bois-Reymond lemma in `L²`

Mathlib proves the fundamental theorem of calculus and integration by parts for scalar
absolutely continuous functions (`AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub`,
`AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul`), phrased with `deriv`.  It has
neither the *primitive form* needed to work with a path defined as `x₀ + ∫₀ᵗ v` (the velocity
carrier of `OptimalControl.BoundedState.VelocityTrajectory`) nor the du Bois-Reymond lemma for
`L²` (rather than continuous) functions.  This file supplies both.

## Main statements

* `ACIntegrationByParts.integral_mul_add_mul_eq_sub_of_primitive`: for two primitives
  `u = a₀ + ∫₀ᵗ g`, `c = c₀ + ∫₀ᵗ s` of interval integrable functions,
  `∫₀ᵀ (g c + u s) = u(T) c(T) - u(0) c(0)`.  Neither `u` nor `c` is differentiable
  everywhere; the identity is the a.e. product rule integrated.
* `ACIntegrationByParts.exists_ae_eq_const_of_integral_mul_eq_zero`: the du Bois-Reymond lemma in
  `L²(0,T)`: an `L²` function orthogonal to every mean-zero `L²` function is a.e. constant.  The
  test class is the *tangent space of absolutely continuous paths with `L²` velocity*, so no
  mollification or density argument is needed (the test function `f - mean f` is used directly).

The library file `Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`
is reused for the scalar absolutely continuous product rule.
-/

@[expose] public section

open MeasureTheory Set
open scoped Interval

namespace ACIntegrationByParts

/-- A primitive `t ↦ a₀ + ∫₀ᵗ g` of an interval integrable function is absolutely continuous. -/
theorem absolutelyContinuousOnInterval_primitive {g : ℝ → ℝ} {a₀ T : ℝ}
    (hg : IntervalIntegrable g volume 0 T) :
    AbsolutelyContinuousOnInterval (fun t => a₀ + ∫ r in (0 : ℝ)..t, g r) 0 T := by
  have h0 : (0 : ℝ) ∈ [[(0 : ℝ), T]] := by simp
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => a₀) 0 T :=
    (LipschitzWith.const a₀).lipschitzOnWith.absolutelyContinuousOnInterval
  exact hc.add (hg.absolutelyContinuousOnInterval_intervalIntegral h0)

/-- A primitive of an interval integrable function has derivative `g` almost everywhere (the
Lebesgue differentiation theorem in the form `deriv`). -/
theorem ae_deriv_primitive {g : ℝ → ℝ} {a₀ T : ℝ}
    (hg : IntervalIntegrable g volume 0 T) :
    ∀ᵐ t, t ∈ Ι (0 : ℝ) T → deriv (fun t => a₀ + ∫ r in (0 : ℝ)..t, g r) t = g t := by
  filter_upwards [hg.ae_hasDerivAt_integral] with t ht htm
  have := (ht (uIoc_subset_uIcc htm) 0 (by simp)).const_add a₀
  exact this.deriv

/-- **Integration by parts for primitives (a.e. product rule, integrated).**  For interval
integrable `g, s` and the primitives `u t = a₀ + ∫₀ᵗ g`, `c t = c₀ + ∫₀ᵗ s`,
`∫₀ᵀ (g c + u s) = u(T) c(T) - u(0) c(0)`.  Both `u` and `c` are merely absolutely continuous. -/
theorem integral_mul_add_mul_eq_sub_of_primitive {g s : ℝ → ℝ} {a₀ c₀ T : ℝ}
    (hg : IntervalIntegrable g volume 0 T) (hs : IntervalIntegrable s volume 0 T) :
    ∫ t in (0 : ℝ)..T, (g t * (c₀ + ∫ r in (0 : ℝ)..t, s r)
        + (a₀ + ∫ r in (0 : ℝ)..t, g r) * s t)
      = (a₀ + ∫ r in (0 : ℝ)..T, g r) * (c₀ + ∫ r in (0 : ℝ)..T, s r)
        - a₀ * c₀ := by
  have key := AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub
    (absolutelyContinuousOnInterval_primitive (a₀ := a₀) hg)
    (absolutelyContinuousOnInterval_primitive (a₀ := c₀) hs)
  simp only [intervalIntegral.integral_same, add_zero] at key ⊢
  rw [← key]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_deriv_primitive (a₀ := a₀) hg, ae_deriv_primitive (a₀ := c₀) hs]
    with t h1 h2 ht
  rw [h1 ht, h2 ht]

/-- **du Bois-Reymond lemma in `L²(0,T)`.**  If an `L²` function `f` satisfies
`∫₀ᵀ f s = 0` for every `L²` function `s` with `∫₀ᵀ s = 0`, then `f` is almost everywhere equal
to a constant.  The test function `s = f - mean f` is itself admissible, so no density or
mollification argument is required. -/
theorem exists_ae_eq_const_of_integral_mul_eq_zero {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (h : ∀ s : ℝ → ℝ, MemLp s 2 (volume.restrict (Ioc (0 : ℝ) T)) →
      ∫ t in (0 : ℝ)..T, s t = 0 → ∫ t in (0 : ℝ)..T, f t * s t = 0) :
    ∃ c : ℝ, ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) T)), f t = c := by
  set μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) T) with hμ
  have : IsFiniteMeasure μ := by
    rw [hμ]; infer_instance
  have hmass : μ.real univ = T := by
    rw [hμ, measureReal_def, Measure.restrict_apply_univ, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith)]
    ring
  have hf1 : Integrable f μ := hf.integrable one_le_two
  set c : ℝ := (∫ t, f t ∂μ) / T with hc
  have hcT : c * T = ∫ t, f t ∂μ := by
    rw [hc]; field_simp
  have hs : MemLp (fun t => f t - c) 2 μ := hf.sub (memLp_const c)
  have hint0 : ∫ t, (f t - c) ∂μ = 0 := by
    rw [integral_sub hf1 (integrable_const c), integral_const, hmass]
    simp only [smul_eq_mul]
    linarith
  have hint : ∫ t in (0 : ℝ)..T, (f t - c) = 0 := by
    rw [intervalIntegral.integral_of_le hT.le]
    exact hint0
  have h0 : ∫ t, f t * (f t - c) ∂μ = 0 := by
    have := h _ hs hint
    rwa [intervalIntegral.integral_of_le hT.le] at this
  have hsq : ∫ t, (f t - c) ^ 2 ∂μ = 0 := by
    have : ∀ t, (f t - c) ^ 2 = f t * (f t - c) - c * (f t - c) := fun t => by ring
    simp_rw [this]
    have h2 : Integrable (fun t => f t * (f t - c)) μ := hf.integrable_mul hs
    have h3 : Integrable (fun t => c * (f t - c)) μ :=
      (hf1.sub (integrable_const c)).const_mul c
    rw [integral_sub h2 h3, h0, integral_const_mul, hint0]
    simp
  refine ⟨c, ?_⟩
  have hnn : 0 ≤ᵐ[μ] fun t => (f t - c) ^ 2 := Filter.Eventually.of_forall fun t => sq_nonneg _
  have := (integral_eq_zero_iff_of_nonneg_ae hnn (hs.integrable_sq)).1 hsq
  filter_upwards [this] with t ht
  have : (f t - c) ^ 2 = 0 := ht
  linarith [pow_eq_zero_iff (two_ne_zero) |>.1 this]


section Pairing

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem intervalIntegrable_clm_comp (L : F →L[ℝ] ℝ) {f : ℝ → F} {T : ℝ}
    (hf : IntervalIntegrable f volume 0 T) : IntervalIntegrable (fun t => L (f t)) volume 0 T :=
  ⟨L.integrable_comp hf.1, L.integrable_comp hf.2⟩

theorem apply_eq_sum_coord (φ : E →L[ℝ] ℝ) (u : E) :
    φ u = ∑ i, φ (Module.finBasis ℝ E i) * (Module.finBasis ℝ E).coord i u := by
  calc φ u = φ (∑ i, (Module.finBasis ℝ E).repr u i • Module.finBasis ℝ E i) := by
        rw [(Module.finBasis ℝ E).sum_repr u]
    _ = _ := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, smul_eq_mul, mul_comm]
        rfl

/-- **Integration by parts for a covector primitive against a vector primitive.**  For a
`E →L[ℝ] ℝ`-valued primitive `p t = p₀ + ∫₀ᵗ g` and an `E`-valued primitive `η t = a + ∫₀ᵗ w` of
interval integrable `g, w` (`E` finite dimensional),
`∫₀ᵀ (⟨g, η⟩ + ⟨p, w⟩) = ⟨p T, η T⟩ - ⟨p 0, η 0⟩`.  The proof expands in a basis and applies the
scalar primitive rule coordinatewise. -/
theorem integral_apply_add_apply_eq_sub_of_primitive [CompleteSpace E]
    {g : ℝ → E →L[ℝ] ℝ} {w : ℝ → E} {p₀ : E →L[ℝ] ℝ} {a : E} {T : ℝ}
    (hT : 0 ≤ T) (hg : IntervalIntegrable g volume 0 T) (hw : IntervalIntegrable w volume 0 T) :
    ∫ t in (0 : ℝ)..T, ((g t) (a + ∫ r in (0 : ℝ)..t, w r)
        + (p₀ + ∫ r in (0 : ℝ)..t, g r) (w t))
      = (p₀ + ∫ r in (0 : ℝ)..T, g r) (a + ∫ r in (0 : ℝ)..T, w r) - p₀ a := by
  set b := Module.finBasis ℝ E with hb
  let ξ : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ := fun i => (b.coord i).toContinuousLinearMap
  have hξ : ∀ i u, ξ i u = b.coord i u := fun i u => rfl
  have hgi : ∀ i, IntervalIntegrable (fun t => g t (b i)) volume 0 T := fun i =>
    intervalIntegrable_clm_comp (ContinuousLinearMap.apply ℝ ℝ (b i)) hg
  have hsi : ∀ i, IntervalIntegrable (fun t => ξ i (w t)) volume 0 T := fun i =>
    intervalIntegrable_clm_comp (ξ i) hw
  have hcont : ∀ {F' : Type _} [NormedAddCommGroup F'] [NormedSpace ℝ F'] {f : ℝ → F'}
      (_ : IntervalIntegrable f volume 0 T) (c₀ : F'),
      ContinuousOn (fun t => c₀ + ∫ r in (0 : ℝ)..t, f r) (Icc (0 : ℝ) T) := by
    intro F' _ _ f hf c₀
    have hprim : ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, f s) [[(0 : ℝ), T]] :=
      intervalIntegral.continuousOn_primitive_interval' (a := (0 : ℝ)) hf (by simp [uIcc])
    rw [uIcc_of_le hT] at hprim
    exact continuousOn_const.add hprim
  -- coordinatewise integral of the covector primitive and the vector primitive
  have hPi : ∀ i, ∀ t, t ∈ Icc (0 : ℝ) T →
      (p₀ + ∫ r in (0 : ℝ)..t, g r) (b i) = p₀ (b i) + ∫ r in (0 : ℝ)..t, g r (b i) := by
    intro i t ht
    have := ContinuousLinearMap.intervalIntegral_comp_comm (ContinuousLinearMap.apply ℝ ℝ (b i))
      (hg.mono_set (by
        rw [uIcc_of_le ht.1, uIcc_of_le hT]; exact Icc_subset_Icc le_rfl ht.2))
    simp only [ContinuousLinearMap.apply_apply] at this
    rw [add_apply, ← this]
  have hηi : ∀ i, ∀ t, t ∈ Icc (0 : ℝ) T →
      ξ i (a + ∫ r in (0 : ℝ)..t, w r) = ξ i a + ∫ r in (0 : ℝ)..t, ξ i (w r) := by
    intro i t ht
    have := ContinuousLinearMap.intervalIntegral_comp_comm (ξ i)
      (hw.mono_set (by
        rw [uIcc_of_le ht.1, uIcc_of_le hT]; exact Icc_subset_Icc le_rfl ht.2))
    rw [map_add, this]
  have hterm : ∀ i, IntervalIntegrable (fun t => g t (b i) * (ξ i a + ∫ r in (0 : ℝ)..t, ξ i (w r))
      + (p₀ (b i) + ∫ r in (0 : ℝ)..t, g r (b i)) * ξ i (w t)) volume 0 T := by
    intro i
    have h1 : ContinuousOn (fun t => ξ i a + ∫ r in (0 : ℝ)..t, ξ i (w r)) (uIcc (0 : ℝ) T) := by
      rw [uIcc_of_le hT]; exact hcont (hsi i) _
    have h2 : ContinuousOn (fun t => p₀ (b i) + ∫ r in (0 : ℝ)..t, g r (b i)) (uIcc (0 : ℝ) T) := by
      rw [uIcc_of_le hT]; exact hcont (hgi i) _
    exact ((hgi i).mul_continuousOn h1).add ((hsi i).continuousOn_mul h2)
  have hscalar : ∀ i, ∫ t in (0 : ℝ)..T, (g t (b i) * (ξ i a + ∫ r in (0 : ℝ)..t, ξ i (w r))
      + (p₀ (b i) + ∫ r in (0 : ℝ)..t, g r (b i)) * ξ i (w t))
      = (p₀ (b i) + ∫ r in (0 : ℝ)..T, g r (b i)) * (ξ i a + ∫ r in (0 : ℝ)..T, ξ i (w r))
        - p₀ (b i) * ξ i a := fun i =>
    integral_mul_add_mul_eq_sub_of_primitive (a₀ := p₀ (b i)) (c₀ := ξ i a) (hgi i) (hsi i)
  have hpt : ∀ t ∈ Icc (0 : ℝ) T,
      (g t) (a + ∫ r in (0 : ℝ)..t, w r) + (p₀ + ∫ r in (0 : ℝ)..t, g r) (w t)
        = ∑ i, (g t (b i) * (ξ i a + ∫ r in (0 : ℝ)..t, ξ i (w r))
          + (p₀ (b i) + ∫ r in (0 : ℝ)..t, g r (b i)) * ξ i (w t)) := by
    intro t ht
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [apply_eq_sum_coord (g t) (a + ∫ r in (0 : ℝ)..t, w r)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hξ, hηi i t ht]
    · rw [apply_eq_sum_coord (p₀ + ∫ r in (0 : ℝ)..t, g r) (w t)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hξ, hPi i t ht]
  have hT' : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  rw [intervalIntegral.integral_congr (fun t ht => hpt t (by rwa [uIcc_of_le hT] at ht)),
    intervalIntegral.integral_finsetSum (fun i _ => hterm i)]
  simp only [hscalar]
  rw [Finset.sum_sub_distrib, apply_eq_sum_coord (p₀ + ∫ r in (0 : ℝ)..T, g r)
      (a + ∫ r in (0 : ℝ)..T, w r), apply_eq_sum_coord p₀ a]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hξ, hηi i T hT', hPi i T hT']

end Pairing

end ACIntegrationByParts
