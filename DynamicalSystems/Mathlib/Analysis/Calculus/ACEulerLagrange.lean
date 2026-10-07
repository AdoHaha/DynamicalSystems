/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.Calculus.ACIntegrationByParts
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Euler-Lagrange equation and endpoint transversality for absolutely continuous paths

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), §11.6, minimise the penalty
`F_K(φ) = ∫₀ᵀ L(t, φ, φ') dt + Φ₀(φ(0)) + Φ₁(φ(0), φ(T))` over absolutely continuous paths
`φ(t) = φ(0) + ∫₀ᵗ φ'` with `φ' ∈ L²` (the velocity carrier
`OptimalControl.BoundedState.VelocityTrajectory`).  Such a path is a.e. differentiable but
**not** `C¹`, so the `C¹` endpoint engine `EndpointTransversality.*` of
`OptimalControl/ContinuousTime/EndpointTransversalityConditions.lean` cannot be applied.  This file
supplies the missing analytic foundation, without assuming `C¹` anywhere:

1. *a.e. integration by parts* (`ACIntegrationByParts`, and
   `integral_firstVariationIntegrand_eq_boundary` below);
2. the *Gateaux derivative* of the action along `L²` test directions, by dominated convergence
   (`hasDerivAt_actionFunctional`);
3. the *weak Euler-Lagrange equation* `d/dt ∂ᵥL = ∂ₓL` a.e. in du Bois-Reymond form
   (`exists_ae_eq_momentumGradient_add_integral`) and
4. the *weak endpoint transversality* `p(0) = ∂Φ₀ + ∂₁Φ₁`, `p(T) = -∂₂Φ₁` for the absolutely
   continuous representative `p` of the momentum covector
   (`weakEulerLagrange_endpointTransversality`).

## The test-function class

Competitors are `x₀ + θ α e + ∫₀ᵗ (v + θ s e)` with `e ∈ E`, `α ∈ ℝ`, `s ∈ L²(0,T)`: the paths
whose velocity moves in the scalar-profile directions `s(t) e`.  Their displacement is
`η(t) = (α + ∫₀ᵗ s) e`, an *arbitrary* absolutely continuous scalar profile times a fixed
vector.  This class is exactly the tangent space of the velocity carrier in these directions; it
contains the book's localized test functions `ζ(t) e^{-Nt} e` of (11.6.14) and needs neither
smoothness of `s` nor a density argument: the du Bois-Reymond lemma
(`ACIntegrationByParts.exists_ae_eq_const_of_integral_mul_eq_zero`) is applied with the
admissible test function `f - mean f` itself.

## What is proved

For a Carathéodory `C¹` Lagrangian with `L²` gradient envelope (`IsCaratheodoryC1`: measurable in
`t`, `C¹` in `(x,v)`, `‖∇L(t,y,w)‖ ≤ a(t) + C‖w‖` locally uniformly in `y`) and `Φ₀`, `Φ₁`
differentiable at the endpoint data, local minimality of the action along scalar-profile
directions yields a covector `c` with `∂ᵥL = c + ∫₀ᵗ ∂ₓL` a.e. and the two transversality
relations for `p(t) = c + ∫₀ᵗ ∂ₓL` (`weakEulerLagrange_endpointTransversality`).

All declaration names are concept names; the book citation lives in docstrings only.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology Interval

namespace ACEulerLagrange

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Lebesgue measure on the horizon `(0,T]`. -/
abbrev timeMeasure (T : ℝ) : Measure ℝ := volume.restrict (Ioc (0 : ℝ) T)

/-- The absolutely continuous path `t ↦ x₀ + ∫₀ᵗ v` carried by its initial value and velocity.
This is the shape of `OptimalControl.BoundedState.VelocityTrajectory.value`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.1). -/
def primitive (x₀ : E) (v : ℝ → E) (t : ℝ) : E :=
  x₀ + ∫ r in (0 : ℝ)..t, v r

/-- The primitive starts at its initial value. -/
@[simp] theorem primitive_zero (x₀ : E) (v : ℝ → E) : primitive x₀ v 0 = x₀ := by
  simp [primitive]

omit [NormedSpace ℝ E] in
/-- An `L²` function on the horizon is interval integrable (finite measure). -/
theorem intervalIntegrable_of_memLp {T : ℝ} (hT : 0 ≤ T) {v : ℝ → E}
    (hv : MemLp v 2 (timeMeasure T)) : IntervalIntegrable v volume 0 T :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 (hv.integrable one_le_two)

omit [NormedSpace ℝ E] in
/-- Interval integrability on `[0,T]` restricts to `[0,t]` for `t ∈ [0,T]`. -/
theorem intervalIntegrable_of_mem_Icc {T : ℝ} {v : ℝ → E} (hv : IntervalIntegrable v volume 0 T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : IntervalIntegrable v volume 0 t :=
  hv.mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le (ht.1.trans ht.2)]
    exact Icc_subset_Icc le_rfl ht.2)

/-- The primitive of an interval integrable velocity is continuous on the horizon. -/
theorem continuousOn_primitive {T : ℝ} (hT : 0 ≤ T) {v : ℝ → E} (x₀ : E)
    (hv : IntervalIntegrable v volume 0 T) :
    ContinuousOn (primitive x₀ v) (Icc (0 : ℝ) T) := by
  have hprim : ContinuousOn (fun t : ℝ => ∫ s in (0 : ℝ)..t, v s) [[(0 : ℝ), T]] :=
    intervalIntegral.continuousOn_primitive_interval' (a := (0 : ℝ)) hv (by simp [uIcc])
  rw [uIcc_of_le hT] at hprim
  exact continuousOn_const.add hprim

/-- The primitive is bounded on the horizon. -/
theorem exists_norm_primitive_le {T : ℝ} (hT : 0 ≤ T) {v : ℝ → E} (x₀ : E)
    (hv : IntervalIntegrable v volume 0 T) :
    ∃ R : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ‖primitive x₀ v t‖ ≤ R := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuousOn_primitive hT x₀ hv)
  exact ⟨R, hR⟩

/-- The primitive is affine in the pair (initial value, velocity). -/
theorem primitive_add_smul {T : ℝ} {v w : ℝ → E} (x₀ a : E) (θ : ℝ)
    (hv : IntervalIntegrable v volume 0 T) (hw : IntervalIntegrable w volume 0 T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    primitive (x₀ + θ • a) (fun r => v r + θ • w r) t
      = primitive x₀ v t + θ • primitive a w t := by
  have h1 := intervalIntegrable_of_mem_Icc hv ht
  have h2 := intervalIntegrable_of_mem_Icc hw ht
  have e : ∫ r in (0 : ℝ)..t, (v r + θ • w r)
      = (∫ r in (0 : ℝ)..t, v r) + ∫ r in (0 : ℝ)..t, θ • w r :=
    intervalIntegral.integral_add h1 (h2.smul θ)
  unfold primitive
  change x₀ + θ • a + ∫ r in (0 : ℝ)..t, (v r + θ • w r) = _
  rw [e, intervalIntegral.integral_smul]
  simp only [smul_add]
  abel



section Gateaux

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- Carathéodory `C¹` regularity of a Lagrangian `L(t,x,v)` with explicit partial covectors `Lx`
and `Lv` and an `L²` envelope for the gradient. -/
structure IsCaratheodoryC1 (T : ℝ) (L : ℝ → E → E → ℝ) (Lx Lv : ℝ → E → E → E →L[ℝ] ℝ) :
    Prop where
  hasFDerivAt : ∀ t y w, HasFDerivAt (fun q : E × E => L t q.1 q.2)
    ((Lx t y w).comp (ContinuousLinearMap.fst ℝ E E) +
      (Lv t y w).comp (ContinuousLinearMap.snd ℝ E E)) (y, w)
  measurable_L : Measurable (fun p : ℝ × E × E => L p.1 p.2.1 p.2.2)
  measurable_Lx : Measurable (fun p : ℝ × E × E => Lx p.1 p.2.1 p.2.2)
  measurable_Lv : Measurable (fun p : ℝ × E × E => Lv p.1 p.2.1 p.2.2)
  growth : ∀ R : ℝ, ∃ (a : ℝ → ℝ) (C : ℝ), MemLp a 2 (timeMeasure T) ∧ 0 ≤ C ∧
    ∀ t y w, ‖y‖ ≤ R → ‖Lx t y w‖ ≤ a t + C * ‖w‖ ∧ ‖Lv t y w‖ ≤ a t + C * ‖w‖


variable {T : ℝ} {L : ℝ → E → E → ℝ} {Lx Lv : ℝ → E → E → E →L[ℝ] ℝ}

/-- The integrand `t ↦ L(t, x t + θ η t, v t + θ w t)` of the perturbed action is a.e.
strongly measurable. -/
theorem aestronglyMeasurable_perturbedIntegrand (hD : IsCaratheodoryC1 T L Lx Lv) (hT : 0 ≤ T)
    {v w : ℝ → E} (hv : MemLp v 2 (timeMeasure T)) (hw : MemLp w 2 (timeMeasure T))
    (x₀ a : E) (θ : ℝ) :
    AEStronglyMeasurable
      (fun t => L t (primitive x₀ v t + θ • primitive a w t) (v t + θ • w t))
      (timeMeasure T) := by
  have hx : AEMeasurable (primitive x₀ v) (timeMeasure T) :=
    ((continuousOn_primitive hT x₀ (intervalIntegrable_of_memLp hT hv)).mono
      Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc
  have hη : AEMeasurable (primitive a w) (timeMeasure T) :=
    ((continuousOn_primitive hT a (intervalIntegrable_of_memLp hT hw)).mono
      Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc
  have hvm := hv.aestronglyMeasurable.aemeasurable
  have hwm := hw.aestronglyMeasurable.aemeasurable
  exact (hD.measurable_L.comp_aemeasurable (aemeasurable_id.prodMk
    ((hx.add (hη.const_smul θ)).prodMk (hvm.add (hwm.const_smul θ))))).aestronglyMeasurable

/-- The first-variation integrand `t ↦ Lx(…)(η t) + Lv(…)(w t)` is a.e. strongly measurable. -/
theorem aestronglyMeasurable_firstVariationIntegrand (hD : IsCaratheodoryC1 T L Lx Lv)
    (hT : 0 ≤ T) {v w : ℝ → E} (hv : MemLp v 2 (timeMeasure T)) (hw : MemLp w 2 (timeMeasure T))
    (x₀ a : E) :
    AEStronglyMeasurable
      (fun t => Lx t (primitive x₀ v t) (v t) (primitive a w t)
        + Lv t (primitive x₀ v t) (v t) (w t)) (timeMeasure T) := by
  have hx : AEMeasurable (primitive x₀ v) (timeMeasure T) :=
    ((continuousOn_primitive hT x₀ (intervalIntegrable_of_memLp hT hv)).mono
      Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc
  have hη : AEMeasurable (primitive a w) (timeMeasure T) :=
    ((continuousOn_primitive hT a (intervalIntegrable_of_memLp hT hw)).mono
      Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc
  have hvm := hv.aestronglyMeasurable.aemeasurable
  have hwm := hw.aestronglyMeasurable.aemeasurable
  have hpt : AEMeasurable (fun t => (t, primitive x₀ v t, v t)) (timeMeasure T) :=
    aemeasurable_id.prodMk (hx.prodMk hvm)
  have hX : AEMeasurable (fun t => Lx t (primitive x₀ v t) (v t)) (timeMeasure T) :=
    hD.measurable_Lx.comp_aemeasurable hpt
  have hV : AEMeasurable (fun t => Lv t (primitive x₀ v t) (v t)) (timeMeasure T) :=
    hD.measurable_Lv.comp_aemeasurable hpt
  have hev : Measurable (fun p : (E →L[ℝ] ℝ) × E => p.1 p.2) :=
    (continuous_fst.clm_apply continuous_snd).measurable
  exact ((hev.comp_aemeasurable (hX.prodMk hη)).add
    (hev.comp_aemeasurable (hV.prodMk hwm))).aestronglyMeasurable


/-- **Gateaux derivative of the running action along an `L²` test direction.**  For a Carathéodory
`C¹` Lagrangian with `L²` gradient envelope, the path `x = x₀ + ∫₀ᵗ v` with `v ∈ L²`, and the test
direction `η = a + ∫₀ᵗ w`, `w ∈ L²`, the map
`θ ↦ ∫₀ᵀ L(t, x t + θ η t, v t + θ w t) dt` is differentiable at `0` with derivative
`∫₀ᵀ (∂ₓL · η + ∂ᵥL · w) dt`.  No `C¹` regularity of `x` is used; the proof is dominated
convergence. -/
theorem hasDerivAt_integral_perturbed (hD : IsCaratheodoryC1 T L Lx Lv) (hT : 0 ≤ T)
    {v w : ℝ → E} (hv : MemLp v 2 (timeMeasure T)) (hw : MemLp w 2 (timeMeasure T))
    (x₀ a : E)
    (hint : IntervalIntegrable (fun t => L t (primitive x₀ v t) (v t)) volume 0 T) :
    IntervalIntegrable (fun t => Lx t (primitive x₀ v t) (v t) (primitive a w t)
        + Lv t (primitive x₀ v t) (v t) (w t)) volume 0 T ∧
    HasDerivAt
      (fun θ : ℝ => ∫ t in (0 : ℝ)..T,
        L t (primitive x₀ v t + θ • primitive a w t) (v t + θ • w t))
      (∫ t in (0 : ℝ)..T, (Lx t (primitive x₀ v t) (v t) (primitive a w t)
        + Lv t (primitive x₀ v t) (v t) (w t))) 0 := by
  have hv1 := intervalIntegrable_of_memLp hT hv
  have hw1 := intervalIntegrable_of_memLp hT hw
  obtain ⟨Rx, hRx⟩ := exists_norm_primitive_le hT x₀ hv1
  obtain ⟨Rη, hRη⟩ := exists_norm_primitive_le hT a hw1
  have hRη0 : 0 ≤ Rη := (norm_nonneg _).trans (hRη 0 ⟨le_rfl, hT⟩)
  obtain ⟨A, C, hA, hC, hgrow⟩ := hD.growth (Rx + Rη)
  set bound : ℝ → ℝ := fun t => (A t + C * (‖v t‖ + ‖w t‖)) * (Rη + ‖w t‖) with hbound
  have hbound_int : IntervalIntegrable bound volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    have h1 : MemLp (fun t => A t + C * (‖v t‖ + ‖w t‖)) 2 (timeMeasure T) :=
      hA.add ((hv.norm.add hw.norm).const_mul C)
    have h2 : MemLp (fun t => Rη + ‖w t‖) 2 (timeMeasure T) :=
      (memLp_const Rη).add hw.norm
    exact h1.integrable_mul h2
  have hFd : ∀ t (θ : ℝ), HasDerivAt
      (fun θ : ℝ => L t (primitive x₀ v t + θ • primitive a w t) (v t + θ • w t))
      (Lx t (primitive x₀ v t + θ • primitive a w t) (v t + θ • w t) (primitive a w t)
        + Lv t (primitive x₀ v t + θ • primitive a w t) (v t + θ • w t) (w t)) θ := by
    intro t θ
    have hp1 : HasDerivAt (fun θ : ℝ => primitive x₀ v t + θ • primitive a w t)
        (primitive a w t) θ := by
      simpa using ((hasDerivAt_id θ).smul_const (primitive a w t)).const_add (primitive x₀ v t)
    have hp2 : HasDerivAt (fun θ : ℝ => v t + θ • w t) (w t) θ := by
      simpa using ((hasDerivAt_id θ).smul_const (w t)).const_add (v t)
    have hpath : HasDerivAt (fun θ : ℝ => (primitive x₀ v t + θ • primitive a w t,
        v t + θ • w t)) (primitive a w t, w t) θ := hp1.prodMk hp2
    have := (hD.hasFDerivAt t _ _).comp_hasDerivAt θ hpath
    simp only [add_apply, ContinuousLinearMap.coe_comp,
      Function.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] at this
    exact this
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := T) (x₀ := (0 : ℝ)) (s := ball (0 : ℝ) 1)
    (F := fun θ t => L t (primitive x₀ v t + θ • primitive a w t) (v t + θ • w t))
    (F' := fun θ t => Lx t (primitive x₀ v t + θ • primitive a w t) (v t + θ • w t)
        (primitive a w t) + Lv t (primitive x₀ v t + θ • primitive a w t) (v t + θ • w t) (w t))
    (bound := bound) (ball_mem_nhds _ one_pos) ?_ ?_ ?_ ?_ hbound_int ?_
  · simpa using key
  · refine Eventually.of_forall fun θ => ?_
    rw [uIoc_of_le hT]
    exact aestronglyMeasurable_perturbedIntegrand hD hT hv hw x₀ a θ
  · simpa using hint
  · rw [uIoc_of_le hT]
    simpa using aestronglyMeasurable_firstVariationIntegrand hD hT hv hw x₀ a
  · refine Eventually.of_forall fun t ht θ hθ => ?_
    rw [uIoc_of_le hT] at ht
    have htI : t ∈ Icc (0 : ℝ) T := Ioc_subset_Icc_self ht
    have hθ1 : |θ| < 1 := by simpa using hθ
    have hy : ‖primitive x₀ v t + θ • primitive a w t‖ ≤ Rx + Rη := by
      calc ‖primitive x₀ v t + θ • primitive a w t‖
          ≤ ‖primitive x₀ v t‖ + ‖θ • primitive a w t‖ := norm_add_le _ _
        _ ≤ Rx + Rη := by
            rw [norm_smul, Real.norm_eq_abs]
            have h1 := hRx t htI
            have h2 := hRη t htI
            nlinarith [abs_nonneg θ, norm_nonneg (primitive a w t)]
    obtain ⟨hgx, hgv⟩ := hgrow t _ (v t + θ • w t) hy
    have hvw : ‖v t + θ • w t‖ ≤ ‖v t‖ + ‖w t‖ := by
      calc ‖v t + θ • w t‖ ≤ ‖v t‖ + ‖θ • w t‖ := norm_add_le _ _
        _ ≤ ‖v t‖ + ‖w t‖ := by
            rw [norm_smul, Real.norm_eq_abs]
            nlinarith [abs_nonneg θ, norm_nonneg (w t)]
    set M : ℝ := A t + C * (‖v t‖ + ‖w t‖) with hM
    have hMx : ‖Lx t (primitive x₀ v t + θ • primitive a w t) (v t + θ • w t)‖ ≤ M := by
      refine hgx.trans ?_
      rw [hM]; nlinarith [mul_le_mul_of_nonneg_left hvw hC]
    have hMv : ‖Lv t (primitive x₀ v t + θ • primitive a w t) (v t + θ • w t)‖ ≤ M := by
      refine hgv.trans ?_
      rw [hM]; nlinarith [mul_le_mul_of_nonneg_left hvw hC]
    have hM0 : 0 ≤ M := (norm_nonneg _).trans hMx
    calc ‖Lx t (primitive x₀ v t + θ • primitive a w t) (v t + θ • w t) (primitive a w t)
          + Lv t (primitive x₀ v t + θ • primitive a w t) (v t + θ • w t) (w t)‖
        ≤ ‖Lx t (primitive x₀ v t + θ • primitive a w t) (v t + θ • w t) (primitive a w t)‖
          + ‖Lv t (primitive x₀ v t + θ • primitive a w t) (v t + θ • w t) (w t)‖ :=
          norm_add_le _ _
      _ ≤ M * Rη + M * ‖w t‖ := by
          gcongr
          · exact ((ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul hMx (hRη t htI) (norm_nonneg _) hM0))
          · exact ((ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul_of_nonneg_right hMv (norm_nonneg _)))
      _ = bound t := by rw [hbound]; ring
  · exact Eventually.of_forall fun t ht θ hθ => hFd t θ


/-- The endpoint-penalized action `∫₀ᵀ L(t, x t, v t) dt + Φ₀(x 0) + Φ₁(x 0, x T)` on the path
`x = primitive x₀ v`, evaluated on the pair `(x₀, v)` that carries the path.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.6) and §11.6. -/
def actionFunctional (L : ℝ → E → E → ℝ) (Φ₀ : E → ℝ) (Φ₁ : E × E → ℝ) (T : ℝ)
    (x₀ : E) (v : ℝ → E) : ℝ :=
  (∫ t in (0 : ℝ)..T, L t (primitive x₀ v t) (v t)) + Φ₀ x₀ + Φ₁ (x₀, primitive x₀ v T)

/-- The first variation of `actionFunctional` at `(x₀, v)` in the `L²` test direction
`(a, w)` (`η = primitive a w`): the running first variation plus the initial and endpoint
penalty boundary terms. -/
def actionFirstVariation (Lx Lv : ℝ → E → E → E →L[ℝ] ℝ) (Φ₀ : E → ℝ) (Φ₁ : E × E → ℝ)
    (T : ℝ) (x₀ : E) (v : ℝ → E) (a : E) (w : ℝ → E) : ℝ :=
  (∫ t in (0 : ℝ)..T, (Lx t (primitive x₀ v t) (v t) (primitive a w t)
      + Lv t (primitive x₀ v t) (v t) (w t)))
    + fderiv ℝ Φ₀ x₀ a + fderiv ℝ Φ₁ (x₀, primitive x₀ v T) (a, primitive a w T)

/-- **Gateaux derivative of the endpoint-penalized action on the absolutely continuous carrier.**
For `v, w ∈ L²(0,T;E)` and a Carathéodory `C¹` Lagrangian with `L²` gradient envelope,
`θ ↦ actionFunctional (x₀ + θ a) (v + θ w)` is differentiable at `0` with derivative
`actionFirstVariation`.  The base point is a genuinely absolutely continuous path (not `C¹`). -/
theorem hasDerivAt_actionFunctional (hD : IsCaratheodoryC1 T L Lx Lv) (hT : 0 ≤ T)
    {Φ₀ : E → ℝ} {Φ₁ : E × E → ℝ} {v w : ℝ → E}
    (hv : MemLp v 2 (timeMeasure T)) (hw : MemLp w 2 (timeMeasure T)) (x₀ a : E)
    (hint : IntervalIntegrable (fun t => L t (primitive x₀ v t) (v t)) volume 0 T)
    (hΦ₀ : DifferentiableAt ℝ Φ₀ x₀) (hΦ₁ : DifferentiableAt ℝ Φ₁ (x₀, primitive x₀ v T)) :
    HasDerivAt
      (fun θ : ℝ => actionFunctional L Φ₀ Φ₁ T (x₀ + θ • a) (fun t => v t + θ • w t))
      (actionFirstVariation Lx Lv Φ₀ Φ₁ T x₀ v a w) 0 := by
  have hv1 := intervalIntegrable_of_memLp hT hv
  have hw1 := intervalIntegrable_of_memLp hT hw
  have hrun := (hasDerivAt_integral_perturbed hD hT hv hw x₀ a hint).2
  have hpath0 : HasDerivAt (fun θ : ℝ => x₀ + θ • a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add x₀
  have hpathT : HasDerivAt (fun θ : ℝ => primitive x₀ v T + θ • primitive a w T)
      (primitive a w T) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (primitive a w T)).const_add
      (primitive x₀ v T)
  have hΦ₀d : HasDerivAt (fun θ : ℝ => Φ₀ (x₀ + θ • a)) (fderiv ℝ Φ₀ x₀ a) 0 := by
    have h : HasFDerivAt Φ₀ (fderiv ℝ Φ₀ x₀) (x₀ + (0 : ℝ) • a) := by
      simpa using hΦ₀.hasFDerivAt
    exact h.comp_hasDerivAt 0 hpath0
  have hΦ₁d : HasDerivAt
      (fun θ : ℝ => Φ₁ (x₀ + θ • a, primitive x₀ v T + θ • primitive a w T))
      (fderiv ℝ Φ₁ (x₀, primitive x₀ v T) (a, primitive a w T)) 0 := by
    have h : HasFDerivAt Φ₁ (fderiv ℝ Φ₁ (x₀, primitive x₀ v T))
        (x₀ + (0 : ℝ) • a, primitive x₀ v T + (0 : ℝ) • primitive a w T) := by
      simpa using hΦ₁.hasFDerivAt
    exact h.comp_hasDerivAt 0 (hpath0.prodMk hpathT)
  have hsum := (hrun.add hΦ₀d).add hΦ₁d
  have hfun : (fun θ : ℝ => actionFunctional L Φ₀ Φ₁ T (x₀ + θ • a) (fun t => v t + θ • w t))
      = fun θ : ℝ => (∫ t in (0 : ℝ)..T,
          L t (primitive x₀ v t + θ • primitive a w t) (v t + θ • w t))
          + Φ₀ (x₀ + θ • a)
          + Φ₁ (x₀ + θ • a, primitive x₀ v T + θ • primitive a w T) := by
    funext θ
    unfold actionFunctional
    have hI : ∫ t in (0 : ℝ)..T, L t (primitive (x₀ + θ • a) (fun r => v r + θ • w r) t)
          (v t + θ • w t)
        = ∫ t in (0 : ℝ)..T, L t (primitive x₀ v t + θ • primitive a w t) (v t + θ • w t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hT] at ht
      simp only [primitive_add_smul x₀ a θ hv1 hw1 ht]
    have hT' : primitive (x₀ + θ • a) (fun r => v r + θ • w r) T
        = primitive x₀ v T + θ • primitive a w T :=
      primitive_add_smul x₀ a θ hv1 hw1 ⟨hT, le_rfl⟩
    rw [hI, hT']
  rw [hfun]
  convert hsum using 1
  simp only [actionFirstVariation]


/-! ### Scalar-profile test directions -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- A scalar `L²` profile times a fixed vector is an `L²` test velocity. -/
theorem memLp_smul_const {T : ℝ} {s : ℝ → ℝ} (hs : MemLp s 2 (timeMeasure T)) (e : E) :
    MemLp (fun t => s t • e) 2 (timeMeasure T) := by
  refine MemLp.mono (hs.const_mul ‖e‖) (hs.aestronglyMeasurable.smul_const e) ?_
  refine Eventually.of_forall fun t => ?_
  simp only [norm_smul, Real.norm_eq_abs, norm_mul, abs_norm]
  rw [mul_comm]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The primitive of a scalar profile times a fixed vector. -/
theorem primitive_smul_const [CompleteSpace E] (s : ℝ → ℝ) (α : ℝ) (e : E) (t : ℝ) :
    primitive (α • e) (fun r => s r • e) t = (α + ∫ r in (0 : ℝ)..t, s r) • e := by
  unfold primitive
  rw [intervalIntegral.integral_smul_const, add_smul]


/-! ### The gradient curves along an absolutely continuous path -/

/-- The state covector `t ↦ ∂ₓL(t, x t, v t) ∈ E →L[ℝ] ℝ` along the path `x = primitive x₀ v`
(Berkovitz & Medhin, §11.6, `f₁⁰` of (11.6.9)). -/
def stateGradient (Lx : ℝ → E → E → E →L[ℝ] ℝ) (x₀ : E) (v : ℝ → E) (t : ℝ) : E →L[ℝ] ℝ :=
  Lx t (primitive x₀ v t) (v t)

/-- The momentum covector `t ↦ ∂ᵥL(t, x t, v t) ∈ E →L[ℝ] ℝ` along the path
`x = primitive x₀ v` (Berkovitz & Medhin, (11.6.8), the book's `ψ(ε;·)`). -/
def momentumGradient (Lv : ℝ → E → E → E →L[ℝ] ℝ) (x₀ : E) (v : ℝ → E) (t : ℝ) : E →L[ℝ] ℝ :=
  Lv t (primitive x₀ v t) (v t)

/-- The state covector curve is a.e. strongly measurable. -/
theorem aestronglyMeasurable_stateGradient (hD : IsCaratheodoryC1 T L Lx Lv) (hT : 0 ≤ T)
    {v : ℝ → E} (hv : MemLp v 2 (timeMeasure T)) (x₀ : E) :
    AEStronglyMeasurable (stateGradient Lx x₀ v) (timeMeasure T) := by
  have hx : AEMeasurable (primitive x₀ v) (timeMeasure T) :=
    ((continuousOn_primitive hT x₀ (intervalIntegrable_of_memLp hT hv)).mono
      Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc
  exact (hD.measurable_Lx.comp_aemeasurable (aemeasurable_id.prodMk
    (hx.prodMk hv.aestronglyMeasurable.aemeasurable))).aestronglyMeasurable

/-- The momentum covector curve is a.e. strongly measurable. -/
theorem aestronglyMeasurable_momentumGradient (hD : IsCaratheodoryC1 T L Lx Lv) (hT : 0 ≤ T)
    {v : ℝ → E} (hv : MemLp v 2 (timeMeasure T)) (x₀ : E) :
    AEStronglyMeasurable (momentumGradient Lv x₀ v) (timeMeasure T) := by
  have hx : AEMeasurable (primitive x₀ v) (timeMeasure T) :=
    ((continuousOn_primitive hT x₀ (intervalIntegrable_of_memLp hT hv)).mono
      Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc
  exact (hD.measurable_Lv.comp_aemeasurable (aemeasurable_id.prodMk
    (hx.prodMk hv.aestronglyMeasurable.aemeasurable))).aestronglyMeasurable

omit [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The gradient curves are dominated by one `L²` envelope. -/
theorem exists_gradient_envelope (hD : IsCaratheodoryC1 T L Lx Lv) (hT : 0 ≤ T)
    {v : ℝ → E} (hv : MemLp v 2 (timeMeasure T)) (x₀ : E) :
    ∃ B : ℝ → ℝ, MemLp B 2 (timeMeasure T) ∧ ∀ t ∈ Ioc (0 : ℝ) T,
      ‖stateGradient Lx x₀ v t‖ ≤ B t ∧ ‖momentumGradient Lv x₀ v t‖ ≤ B t := by
  obtain ⟨Rx, hRx⟩ := exists_norm_primitive_le hT x₀ (intervalIntegrable_of_memLp hT hv)
  obtain ⟨A, C, hA, hC, hgrow⟩ := hD.growth Rx
  refine ⟨fun t => A t + C * ‖v t‖, hA.add (hv.norm.const_mul C), fun t ht => ?_⟩
  exact hgrow t (primitive x₀ v t) (v t) (hRx t (Ioc_subset_Icc_self ht))

/-- The state covector curve `t ↦ ∂ₓL(t, x t, v t)` is in `L²(0,T)`. -/
theorem memLp_stateGradient (hD : IsCaratheodoryC1 T L Lx Lv) (hT : 0 ≤ T)
    {v : ℝ → E} (hv : MemLp v 2 (timeMeasure T)) (x₀ : E) :
    MemLp (stateGradient Lx x₀ v) 2 (timeMeasure T) := by
  obtain ⟨B, hB, hbd⟩ := exists_gradient_envelope hD hT hv x₀
  refine MemLp.mono hB (aestronglyMeasurable_stateGradient hD hT hv x₀) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Eventually.of_forall fun t ht => (hbd t ht).1.trans (le_abs_self _ |>.trans_eq
    (Real.norm_eq_abs _).symm)

/-- The momentum covector curve `t ↦ ∂ᵥL(t, x t, v t)` is in `L²(0,T)`. -/
theorem memLp_momentumGradient (hD : IsCaratheodoryC1 T L Lx Lv) (hT : 0 ≤ T)
    {v : ℝ → E} (hv : MemLp v 2 (timeMeasure T)) (x₀ : E) :
    MemLp (momentumGradient Lv x₀ v) 2 (timeMeasure T) := by
  obtain ⟨B, hB, hbd⟩ := exists_gradient_envelope hD hT hv x₀
  refine MemLp.mono hB (aestronglyMeasurable_momentumGradient hD hT hv x₀) ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Eventually.of_forall fun t ht => (hbd t ht).2.trans (le_abs_self _ |>.trans_eq
    (Real.norm_eq_abs _).symm)


/-! ### First variation along scalar-profile directions -/

/-- At a local minimum along the direction `(a, w)` the full first variation vanishes. -/
theorem actionFirstVariation_eq_zero_of_isLocalMin (hD : IsCaratheodoryC1 T L Lx Lv)
    (hT : 0 ≤ T) {Φ₀ : E → ℝ} {Φ₁ : E × E → ℝ} {v w : ℝ → E}
    (hv : MemLp v 2 (timeMeasure T)) (hw : MemLp w 2 (timeMeasure T)) (x₀ a : E)
    (hint : IntervalIntegrable (fun t => L t (primitive x₀ v t) (v t)) volume 0 T)
    (hΦ₀ : DifferentiableAt ℝ Φ₀ x₀) (hΦ₁ : DifferentiableAt ℝ Φ₁ (x₀, primitive x₀ v T))
    (hmin : IsLocalMin
      (fun θ : ℝ => actionFunctional L Φ₀ Φ₁ T (x₀ + θ • a) (fun t => v t + θ • w t)) 0) :
    actionFirstVariation Lx Lv Φ₀ Φ₁ T x₀ v a w = 0 :=
  IsLocalMin.hasDerivAt_eq_zero hmin
    (hasDerivAt_actionFunctional hD hT hv hw x₀ a hint hΦ₀ hΦ₁)

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The first variation along the scalar-profile direction `η t = (α + ∫₀ᵗ s) • e`. -/
theorem actionFirstVariation_scalarProfile [CompleteSpace E]
    (Φ₀ : E → ℝ) (Φ₁ : E × E → ℝ) (x₀ : E) (v : ℝ → E) (α : ℝ) (e : E) (s : ℝ → ℝ) :
    actionFirstVariation Lx Lv Φ₀ Φ₁ T x₀ v (α • e) (fun t => s t • e)
      = (∫ t in (0 : ℝ)..T, (stateGradient Lx x₀ v t e * (α + ∫ r in (0 : ℝ)..t, s r)
          + momentumGradient Lv x₀ v t e * s t))
        + α * fderiv ℝ Φ₀ x₀ e
        + α * fderiv ℝ Φ₁ (x₀, primitive x₀ v T) (e, 0)
        + (α + ∫ r in (0 : ℝ)..T, s r) * fderiv ℝ Φ₁ (x₀, primitive x₀ v T) (0, e) := by
  unfold actionFirstVariation
  have hI : ∫ t in (0 : ℝ)..T,
        (Lx t (primitive x₀ v t) (v t) (primitive (α • e) (fun r => s r • e) t)
          + Lv t (primitive x₀ v t) (v t) (s t • e))
      = ∫ t in (0 : ℝ)..T, (stateGradient Lx x₀ v t e * (α + ∫ r in (0 : ℝ)..t, s r)
          + momentumGradient Lv x₀ v t e * s t) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [primitive_smul_const, map_smul, smul_eq_mul, stateGradient, momentumGradient]
    ring
  rw [hI, primitive_smul_const]
  have hpair : ((α • e, (α + ∫ r in (0 : ℝ)..T, s r) • e) : E × E)
      = α • ((e, (0 : E)) : E × E) + (α + ∫ r in (0 : ℝ)..T, s r) • (((0 : E), e) : E × E) := by
    ext <;> simp
  rw [hpair, map_add, map_smul, map_smul, map_smul]
  simp only [smul_eq_mul]
  ring


/-! ### The du Bois-Reymond step -/

/-- **Local minimality along every scalar-profile test direction.**  The competitors are the
absolutely continuous paths `x₀ + θ α e + ∫₀ᵗ (v + θ s e)`, `e ∈ E`, `α ∈ ℝ`, `s ∈ L²(0,T)`:
the tangent space of the carrier in the directions `(α + ∫₀ᵗ s) e`.  Berkovitz & Medhin's
test functions `ζ(t) e^{-Nt} e` of (11.6.14) are of this form. -/
def IsLocalMinOnProfiles (L : ℝ → E → E → ℝ) (Φ₀ : E → ℝ) (Φ₁ : E × E → ℝ) (T : ℝ)
    (x₀ : E) (v : ℝ → E) : Prop :=
  ∀ (e : E) (α : ℝ) (s : ℝ → ℝ), MemLp s 2 (timeMeasure T) →
    IsLocalMin (fun θ : ℝ => actionFunctional L Φ₀ Φ₁ T (x₀ + θ • (α • e))
      (fun t => v t + θ • (s t • e))) 0

/-- For every direction `e`, `t ↦ ∂ᵥL(t,x,v) e - ∫₀ᵗ ∂ₓL(r,x,v) e dr` is a.e. constant. -/
theorem exists_ae_eq_const_momentumGradient_sub_integral_apply [CompleteSpace E]
    (hD : IsCaratheodoryC1 T L Lx Lv) (hT : 0 < T) {Φ₀ : E → ℝ} {Φ₁ : E × E → ℝ}
    {v : ℝ → E} (hv : MemLp v 2 (timeMeasure T)) (x₀ : E)
    (hint : IntervalIntegrable (fun t => L t (primitive x₀ v t) (v t)) volume 0 T)
    (hΦ₀ : DifferentiableAt ℝ Φ₀ x₀) (hΦ₁ : DifferentiableAt ℝ Φ₁ (x₀, primitive x₀ v T))
    (hmin : IsLocalMinOnProfiles L Φ₀ Φ₁ T x₀ v) (e : E) :
    ∃ c : ℝ, ∀ᵐ t ∂(timeMeasure T),
      momentumGradient Lv x₀ v t e - ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r e = c := by
  have hT0 : 0 ≤ T := hT.le
  have hgL := memLp_stateGradient hD hT0 hv x₀
  have hPL := memLp_momentumGradient hD hT0 hv x₀
  have hge : MemLp (fun t => stateGradient Lx x₀ v t e) 2 (timeMeasure T) :=
    (ContinuousLinearMap.apply ℝ ℝ e).comp_memLp' hgL
  have hPe : MemLp (fun t => momentumGradient Lv x₀ v t e) 2 (timeMeasure T) :=
    (ContinuousLinearMap.apply ℝ ℝ e).comp_memLp' hPL
  have hg1 : IntervalIntegrable (fun t => stateGradient Lx x₀ v t e) volume 0 T :=
    intervalIntegrable_of_memLp hT0 hge
  have hGcont : ContinuousOn (fun t => (0 : ℝ) + ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r e)
      (Icc (0 : ℝ) T) := continuousOn_primitive hT0 (0 : ℝ) hg1
  have hGL : MemLp (fun t => ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r e) 2
      (timeMeasure T) := by
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hGcont
    refine MemLp.of_bound ?_ B ?_
    · have := ContinuousOn.aestronglyMeasurable (μ := volume)
        (hGcont.mono (Ioc_subset_Icc_self (a := (0 : ℝ)) (b := T)))
        (measurableSet_Ioc (a := (0 : ℝ)) (b := T))
      simpa using this
    · rw [ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall fun t ht => by simpa using hB t (Ioc_subset_Icc_self ht)
  have hf : MemLp (fun t => momentumGradient Lv x₀ v t e
      - ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r e) 2 (timeMeasure T) := hPe.sub hGL
  refine ACIntegrationByParts.exists_ae_eq_const_of_integral_mul_eq_zero hT hf ?_
  intro s hs hsum
  have hs1 : IntervalIntegrable s volume 0 T := intervalIntegrable_of_memLp hT0 hs
  have hstat := actionFirstVariation_eq_zero_of_isLocalMin hD hT0 hv (memLp_smul_const hs e) x₀
    ((0 : ℝ) • e) hint hΦ₀ hΦ₁ (hmin e 0 s hs)
  rw [actionFirstVariation_scalarProfile] at hstat
  simp only [hsum, zero_mul, zero_add, add_zero] at hstat
  have hibp := ACIntegrationByParts.integral_mul_add_mul_eq_sub_of_primitive (a₀ := (0 : ℝ))
    (c₀ := (0 : ℝ)) hg1 hs1
  simp only [hsum, zero_add, mul_zero, sub_zero] at hibp
  have hC : ContinuousOn (fun t => ∫ r in (0 : ℝ)..t, s r) (uIcc (0 : ℝ) T) := by
    rw [uIcc_of_le hT0]
    exact continuousOn_primitive hT0 (0 : ℝ) hs1 |>.congr (fun t _ => by simp [primitive])
  have hG' : ContinuousOn (fun t => ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r e)
      (uIcc (0 : ℝ) T) := by
    rw [uIcc_of_le hT0]
    exact hGcont.congr (fun t _ => by simp)
  have h1 : IntervalIntegrable (fun t => stateGradient Lx x₀ v t e
      * ∫ r in (0 : ℝ)..t, s r) volume 0 T := hg1.mul_continuousOn hC
  have h2 : IntervalIntegrable (fun t => momentumGradient Lv x₀ v t e * s t) volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).2 (hPe.integrable_mul hs)
  have h3 : IntervalIntegrable (fun t => (∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r e) * s t)
      volume 0 T := hs1.continuousOn_mul hG'
  have e1 : ∫ t in (0 : ℝ)..T, (momentumGradient Lv x₀ v t e
        - ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r e) * s t
      = (∫ t in (0 : ℝ)..T, (stateGradient Lx x₀ v t e * (∫ r in (0 : ℝ)..t, s r)
          + momentumGradient Lv x₀ v t e * s t))
        - ∫ t in (0 : ℝ)..T, (stateGradient Lx x₀ v t e * (∫ r in (0 : ℝ)..t, s r)
          + (∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r e) * s t) := by
    refine (intervalIntegral.integral_congr ?_).trans
      (intervalIntegral.integral_sub (h1.add h2) (h1.add h3))
    intro t _
    simp only
    ring
  rw [e1, hstat, hibp]
  simp


/-- **Weak Euler-Lagrange equation (du Bois-Reymond form).**  Under local minimality along all
scalar-profile directions there is a covector `c ∈ E →L[ℝ] ℝ` with
`∂ᵥL(t, x t, v t) = c + ∫₀ᵗ ∂ₓL(r, x r, v r) dr` for almost every `t ∈ (0,T]`.  In particular the
a.e.-defined momentum covector has an absolutely continuous representative whose derivative is
`∂ₓL` a.e.: `d/dt ∂ᵥL = ∂ₓL` almost everywhere, without any `C¹` regularity of the path.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.6.9)-(11.6.10). -/
theorem exists_ae_eq_momentumGradient_add_integral [CompleteSpace E]
    (hD : IsCaratheodoryC1 T L Lx Lv) (hT : 0 < T) {Φ₀ : E → ℝ} {Φ₁ : E × E → ℝ}
    {v : ℝ → E} (hv : MemLp v 2 (timeMeasure T)) (x₀ : E)
    (hint : IntervalIntegrable (fun t => L t (primitive x₀ v t) (v t)) volume 0 T)
    (hΦ₀ : DifferentiableAt ℝ Φ₀ x₀) (hΦ₁ : DifferentiableAt ℝ Φ₁ (x₀, primitive x₀ v T))
    (hmin : IsLocalMinOnProfiles L Φ₀ Φ₁ T x₀ v) :
    ∃ c : E →L[ℝ] ℝ, ∀ᵐ t ∂(timeMeasure T),
      momentumGradient Lv x₀ v t
        = c + ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r := by
  have hT0 : 0 ≤ T := hT.le
  have hgL := memLp_stateGradient hD hT0 hv x₀
  have hPL := memLp_momentumGradient hD hT0 hv x₀
  have hg1 : IntervalIntegrable (stateGradient Lx x₀ v) volume 0 T :=
    intervalIntegrable_of_memLp hT0 hgL
  have hP1 : IntervalIntegrable (momentumGradient Lv x₀ v) volume 0 T :=
    intervalIntegrable_of_memLp hT0 hPL
  -- the dual-valued primitive of the state covector
  have hGc : ContinuousOn (fun t => ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r)
      (Icc (0 : ℝ) T) :=
    (continuousOn_primitive hT0 (0 : E →L[ℝ] ℝ) hg1).congr (fun t _ => by simp [primitive])
  have hG1 : IntervalIntegrable (fun t => ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r)
      volume 0 T := by
    refine ContinuousOn.intervalIntegrable ?_
    rwa [uIcc_of_le hT0]
  have hPG1 : IntervalIntegrable (fun t => momentumGradient Lv x₀ v t
      - ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r) volume 0 T := hP1.sub hG1
  -- evaluation commutes with the primitive
  have hevalG : ∀ (t : ℝ), t ∈ Icc (0 : ℝ) T → ∀ e : E,
      (∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r) e
        = ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r e := by
    intro t ht e
    exact (ContinuousLinearMap.intervalIntegral_comp_comm (ContinuousLinearMap.apply ℝ ℝ e)
      (intervalIntegrable_of_mem_Icc hg1 ht)).symm
  choose c hc using fun e : E => exists_ae_eq_const_momentumGradient_sub_integral_apply
    hD hT hv x₀ hint hΦ₀ hΦ₁ hmin e
  set C : E →L[ℝ] ℝ := (T⁻¹ : ℝ) • ∫ t in (0 : ℝ)..T, (momentumGradient Lv x₀ v t
      - ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r) with hC
  have hCe : ∀ e : E, C e = c e := by
    intro e
    have h1 : (∫ t in (0 : ℝ)..T, (momentumGradient Lv x₀ v t
        - ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r)) e
        = ∫ t in (0 : ℝ)..T, c e := by
      have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm
        (ContinuousLinearMap.apply ℝ ℝ e) hPG1
      simp only [ContinuousLinearMap.apply_apply] at hcomm
      rw [← hcomm]
      refine intervalIntegral.integral_congr_ae ?_
      have := (ae_restrict_iff' measurableSet_Ioc).1 (hc e)
      filter_upwards [this] with t ht htm
      rw [uIoc_of_le hT0] at htm
      have := ht htm
      simp only [sub_apply]
      rw [hevalG t (Ioc_subset_Icc_self htm) e]
      exact this
    rw [hC, smul_apply, h1]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    field_simp
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense E
  refine ⟨C, ?_⟩
  have hD' : ∀ e ∈ D, ∀ᵐ t ∂(timeMeasure T), momentumGradient Lv x₀ v t e
      - (∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r) e = C e := by
    intro e _
    have := (ae_restrict_iff' measurableSet_Ioc).1 (hc e)
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [this] with t ht htm
    rw [hevalG t (Ioc_subset_Icc_self htm) e, hCe e]
    exact ht htm
  have hD'' := (ae_ball_iff hDc).2 hD'
  filter_upwards [hD'', ae_restrict_mem measurableSet_Ioc] with t ht htm
  have heq : (momentumGradient Lv x₀ v t - ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r) = C := by
    refine ContinuousLinearMap.ext (fun e => ?_)
    have hfun := Continuous.ext_on hDd
      (f := fun e : E => (momentumGradient Lv x₀ v t
        - ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r) e) (g := fun e : E => C e)
      (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
      (fun e he => by simpa using ht e he)
    exact congrFun hfun e
  rw [← heq]
  abel


/-! ### Weak endpoint transversality -/

/-- The first variation along `(α + ∫₀ᵗ s) e`, after integrating by parts against the weak
Euler-Lagrange equation, collapses to boundary terms. -/
theorem boundaryIdentity_of_weakEulerLagrange [CompleteSpace E]
    (hD : IsCaratheodoryC1 T L Lx Lv) (hT : 0 < T) {Φ₀ : E → ℝ} {Φ₁ : E × E → ℝ}
    {v : ℝ → E} (hv : MemLp v 2 (timeMeasure T)) (x₀ : E)
    (hint : IntervalIntegrable (fun t => L t (primitive x₀ v t) (v t)) volume 0 T)
    (hΦ₀ : DifferentiableAt ℝ Φ₀ x₀) (hΦ₁ : DifferentiableAt ℝ Φ₁ (x₀, primitive x₀ v T))
    (hmin : IsLocalMinOnProfiles L Φ₀ Φ₁ T x₀ v) (c : E →L[ℝ] ℝ)
    (hEL : ∀ᵐ t ∂(timeMeasure T),
      momentumGradient Lv x₀ v t = c + ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r)
    (e : E) (α : ℝ) {s : ℝ → ℝ} (hs : MemLp s 2 (timeMeasure T)) :
    (c e + ∫ r in (0 : ℝ)..T, stateGradient Lx x₀ v r e) * (α + ∫ r in (0 : ℝ)..T, s r)
      - c e * α + α * fderiv ℝ Φ₀ x₀ e
      + α * fderiv ℝ Φ₁ (x₀, primitive x₀ v T) (e, 0)
      + (α + ∫ r in (0 : ℝ)..T, s r) * fderiv ℝ Φ₁ (x₀, primitive x₀ v T) (0, e) = 0 := by
  have hT0 : 0 ≤ T := hT.le
  have hgL := memLp_stateGradient hD hT0 hv x₀
  have hge : MemLp (fun t => stateGradient Lx x₀ v t e) 2 (timeMeasure T) :=
    (ContinuousLinearMap.apply ℝ ℝ e).comp_memLp' hgL
  have hg1 : IntervalIntegrable (fun t => stateGradient Lx x₀ v t e) volume 0 T :=
    intervalIntegrable_of_memLp hT0 hge
  have hs1 : IntervalIntegrable s volume 0 T := intervalIntegrable_of_memLp hT0 hs
  have hg1' : IntervalIntegrable (stateGradient Lx x₀ v) volume 0 T :=
    intervalIntegrable_of_memLp hT0 hgL
  have hstat := actionFirstVariation_eq_zero_of_isLocalMin hD hT0 hv (memLp_smul_const hs e) x₀
    (α • e) hint hΦ₀ hΦ₁ (hmin e α s hs)
  rw [actionFirstVariation_scalarProfile] at hstat
  have hibp := ACIntegrationByParts.integral_mul_add_mul_eq_sub_of_primitive
    (a₀ := c e) (c₀ := α) hg1 hs1
  have hcongr : ∫ t in (0 : ℝ)..T, (stateGradient Lx x₀ v t e * (α + ∫ r in (0 : ℝ)..t, s r)
        + momentumGradient Lv x₀ v t e * s t)
      = ∫ t in (0 : ℝ)..T, (stateGradient Lx x₀ v t e * (α + ∫ r in (0 : ℝ)..t, s r)
        + (c e + ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r e) * s t) := by
    refine intervalIntegral.integral_congr_ae ?_
    have := (ae_restrict_iff' measurableSet_Ioc).1 hEL
    filter_upwards [this] with t ht htm
    rw [uIoc_of_le hT0] at htm
    have h1 := congrArg (fun K : E →L[ℝ] ℝ => K e) (ht htm)
    simp only [add_apply] at h1
    have h2 : (∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r) e
        = ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r e :=
      (ContinuousLinearMap.intervalIntegral_comp_comm (ContinuousLinearMap.apply ℝ ℝ e)
        (intervalIntegrable_of_mem_Icc hg1' (Ioc_subset_Icc_self htm))).symm
    rw [h1, h2]
  rw [hcongr, hibp] at hstat
  linarith


/-- **Weak Euler-Lagrange equation and weak endpoint transversality for the absolutely
continuous carrier.**  Let `x = x₀ + ∫₀ᵗ v` with `v ∈ L²(0,T;E)`, a Carathéodory `C¹` Lagrangian
with `L²` gradient envelope, and `Φ₀, Φ₁` differentiable at the endpoint data.  If the penalized
action is locally minimal at `(x₀, v)` along every scalar-profile test direction
(`IsLocalMinOnProfiles`), then there is a covector `c ∈ E →L[ℝ] ℝ` such that

* `∂ᵥL(t, x t, v t) = c + ∫₀ᵗ ∂ₓL` for a.e. `t` (the weak Euler-Lagrange equation:
  `d/dt ∂ᵥL = ∂ₓL` a.e. for the absolutely continuous representative `p(t) = c + ∫₀ᵗ ∂ₓL`);
* `p(0) = c = ∂Φ₀(x₀) + ∂₁Φ₁(x₀, x T)`;
* `p(T) = c + ∫₀ᵀ ∂ₓL = -∂₂Φ₁(x₀, x T)`.

The endpoint values are those of the continuous representative `p`, not of the a.e.-defined
momentum `∂ᵥL(t, x t, v t)`; this is exactly the weak (du Bois-Reymond) content of
Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.6.15)-(11.6.16). -/
theorem weakEulerLagrange_endpointTransversality [CompleteSpace E]
    (hD : IsCaratheodoryC1 T L Lx Lv) (hT : 0 < T) {Φ₀ : E → ℝ} {Φ₁ : E × E → ℝ}
    {v : ℝ → E} (hv : MemLp v 2 (timeMeasure T)) (x₀ : E)
    (hint : IntervalIntegrable (fun t => L t (primitive x₀ v t) (v t)) volume 0 T)
    (hΦ₀ : DifferentiableAt ℝ Φ₀ x₀) (hΦ₁ : DifferentiableAt ℝ Φ₁ (x₀, primitive x₀ v T))
    (hmin : IsLocalMinOnProfiles L Φ₀ Φ₁ T x₀ v) :
    ∃ c : E →L[ℝ] ℝ,
      (∀ᵐ t ∂(timeMeasure T), momentumGradient Lv x₀ v t
        = c + ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r) ∧
      c = fderiv ℝ Φ₀ x₀
        + (fderiv ℝ Φ₁ (x₀, primitive x₀ v T)).comp (ContinuousLinearMap.inl ℝ E E) ∧
      c + ∫ r in (0 : ℝ)..T, stateGradient Lx x₀ v r
        = -((fderiv ℝ Φ₁ (x₀, primitive x₀ v T)).comp (ContinuousLinearMap.inr ℝ E E)) := by
  have hT0 : 0 ≤ T := hT.le
  obtain ⟨c, hEL⟩ := exists_ae_eq_momentumGradient_add_integral hD hT hv x₀ hint hΦ₀ hΦ₁ hmin
  refine ⟨c, hEL, ?_, ?_⟩
  · ext e
    have h := boundaryIdentity_of_weakEulerLagrange hD hT hv x₀ hint hΦ₀ hΦ₁ hmin c hEL e 1
      (s := fun _ => -T⁻¹) (memLp_const _)
    have hI : ∫ r in (0 : ℝ)..T, (-T⁻¹ : ℝ) = -1 := by
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      field_simp
    rw [hI] at h
    simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    linarith
  · ext e
    have h := boundaryIdentity_of_weakEulerLagrange hD hT hv x₀ hint hΦ₀ hΦ₁ hmin c hEL e 0
      (s := fun _ => T⁻¹) (memLp_const _)
    have hI : ∫ r in (0 : ℝ)..T, (T⁻¹ : ℝ) = 1 := by
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
      field_simp
    rw [hI] at h
    have hg1 : IntervalIntegrable (stateGradient Lx x₀ v) volume 0 T :=
      intervalIntegrable_of_memLp hT0 (memLp_stateGradient hD hT0 hv x₀)
    have h2 : (∫ r in (0 : ℝ)..T, stateGradient Lx x₀ v r) e
        = ∫ r in (0 : ℝ)..T, stateGradient Lx x₀ v r e :=
      (ContinuousLinearMap.intervalIntegral_comp_comm (ContinuousLinearMap.apply ℝ ℝ e)
        hg1).symm
    simp only [add_apply, neg_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply,
      h2]
    linarith


/-! ### Integration by parts for the first variation and the absolutely continuous representative -/

/-- **A.e. integration by parts for the first variation.**  If the weak Euler-Lagrange equation
`∂ᵥL = c + ∫₀ᵗ ∂ₓL` holds a.e., then the running first variation in *any* `L²` test direction
`η = a + ∫₀ᵗ w` collapses to its boundary term:
`∫₀ᵀ (∂ₓL · η + ∂ᵥL · w) = ⟨p(T), η(T)⟩ - ⟨c, a⟩` with `p(t) = c + ∫₀ᵗ ∂ₓL`.
This is the absolutely continuous replacement of the `C¹` integration by parts of
`EndpointTransversality.integral_firstVariationIntegrand_smul_const`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.6.9)-(11.6.10). -/
theorem integral_firstVariationIntegrand_eq_boundary [CompleteSpace E]
    (hD : IsCaratheodoryC1 T L Lx Lv) (hT : 0 ≤ T)
    {v w : ℝ → E} (hv : MemLp v 2 (timeMeasure T)) (hw : MemLp w 2 (timeMeasure T))
    (x₀ a : E) (c : E →L[ℝ] ℝ)
    (hEL : ∀ᵐ t ∂(timeMeasure T),
      momentumGradient Lv x₀ v t = c + ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r) :
    ∫ t in (0 : ℝ)..T, (Lx t (primitive x₀ v t) (v t) (primitive a w t)
        + Lv t (primitive x₀ v t) (v t) (w t))
      = (c + ∫ r in (0 : ℝ)..T, stateGradient Lx x₀ v r) (primitive a w T) - c a := by
  have hg1 : IntervalIntegrable (stateGradient Lx x₀ v) volume 0 T :=
    intervalIntegrable_of_memLp hT (memLp_stateGradient hD hT hv x₀)
  have hw1 := intervalIntegrable_of_memLp hT hw
  have hcongr : ∫ t in (0 : ℝ)..T, (Lx t (primitive x₀ v t) (v t) (primitive a w t)
        + Lv t (primitive x₀ v t) (v t) (w t))
      = ∫ t in (0 : ℝ)..T, (stateGradient Lx x₀ v t (a + ∫ r in (0 : ℝ)..t, w r)
        + (c + ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r) (w t)) := by
    refine intervalIntegral.integral_congr_ae ?_
    have := (ae_restrict_iff' measurableSet_Ioc).1 hEL
    filter_upwards [this] with t ht htm
    rw [uIoc_of_le hT] at htm
    have h1 := ht htm
    change stateGradient Lx x₀ v t (primitive a w t) + momentumGradient Lv x₀ v t (w t) = _
    rw [h1]
    rfl
  rw [hcongr, ACIntegrationByParts.integral_apply_add_apply_eq_sub_of_primitive hT hg1 hw1]
  simp [primitive]

/-- The absolutely continuous representative of the momentum covector: `p t = c + ∫₀ᵗ ∂ₓL`. -/
def momentumRepresentative (Lx : ℝ → E → E → E →L[ℝ] ℝ) (x₀ : E) (v : ℝ → E)
    (c : E →L[ℝ] ℝ) (t : ℝ) : E →L[ℝ] ℝ :=
  c + ∫ r in (0 : ℝ)..t, stateGradient Lx x₀ v r

/-- The representative is continuous on the horizon, has derivative `∂ₓL` almost everywhere, and
starts at `c`. -/
theorem momentumRepresentative_properties
    (hD : IsCaratheodoryC1 T L Lx Lv) (hT : 0 ≤ T)
    {v : ℝ → E} (hv : MemLp v 2 (timeMeasure T)) (x₀ : E) (c : E →L[ℝ] ℝ) :
    ContinuousOn (momentumRepresentative Lx x₀ v c) (Icc (0 : ℝ) T) ∧
    (∀ᵐ t ∂(timeMeasure T),
      HasDerivAt (momentumRepresentative Lx x₀ v c) (stateGradient Lx x₀ v t) t) ∧
    momentumRepresentative Lx x₀ v c 0 = c := by
  have hg1 : IntervalIntegrable (stateGradient Lx x₀ v) volume 0 T :=
    intervalIntegrable_of_memLp hT (memLp_stateGradient hD hT hv x₀)
  refine ⟨continuousOn_primitive hT c hg1, ?_, by simp [momentumRepresentative]⟩
  have h := hg1.ae_hasDerivAt_integral
  rw [uIcc_of_le hT] at h
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [h] with t ht htm
  exact (ht (Ioc_subset_Icc_self htm) 0 ⟨le_rfl, hT⟩).const_add c

/-! ### Identification of the explicit partial covectors with `fderiv` -/

omit [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The explicit velocity covector `Lv` is the Fréchet derivative of the velocity slice. -/
theorem IsCaratheodoryC1.hasFDerivAt_velocity (hD : IsCaratheodoryC1 T L Lx Lv) (t : ℝ)
    (y w : E) : HasFDerivAt (fun u : E => L t y u) (Lv t y w) w := by
  have hin : HasFDerivAt (fun u : E => (y, u)) ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E))
      w := (hasFDerivAt_const y w).prodMk (hasFDerivAt_id w)
  have h := (hD.hasFDerivAt t y w).comp w hin
  have hEq : ((Lx t y w).comp (ContinuousLinearMap.fst ℝ E E) +
      (Lv t y w).comp (ContinuousLinearMap.snd ℝ E E)).comp
        ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) = Lv t y w := by
    ext u
    simp
  rw [hEq] at h
  exact h

omit [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The explicit state covector `Lx` is the Fréchet derivative of the state slice. -/
theorem IsCaratheodoryC1.hasFDerivAt_state (hD : IsCaratheodoryC1 T L Lx Lv) (t : ℝ)
    (y w : E) : HasFDerivAt (fun u : E => L t u w) (Lx t y w) y := by
  have hin : HasFDerivAt (fun u : E => (u, w)) ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] E))
      y := (hasFDerivAt_id y).prodMk (hasFDerivAt_const w y)
  have h := (hD.hasFDerivAt t y w).comp y hin
  have hEq : ((Lx t y w).comp (ContinuousLinearMap.fst ℝ E E) +
      (Lv t y w).comp (ContinuousLinearMap.snd ℝ E E)).comp
        ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] E)) = Lx t y w := by
    ext u
    simp
  rw [hEq] at h
  exact h

omit [BorelSpace E] [FiniteDimensional ℝ E] in
/-- `Lv t y w = fderiv ℝ (fun u => L t y u) w`. -/
theorem IsCaratheodoryC1.fderiv_velocity_eq (hD : IsCaratheodoryC1 T L Lx Lv) (t : ℝ)
    (y w : E) : fderiv ℝ (fun u : E => L t y u) w = Lv t y w :=
  (hD.hasFDerivAt_velocity t y w).fderiv

omit [BorelSpace E] [FiniteDimensional ℝ E] in
/-- `Lx t y w = fderiv ℝ (fun u => L t u w) y`. -/
theorem IsCaratheodoryC1.fderiv_state_eq (hD : IsCaratheodoryC1 T L Lx Lv) (t : ℝ)
    (y w : E) : fderiv ℝ (fun u : E => L t u w) y = Lx t y w :=
  (hD.hasFDerivAt_state t y w).fderiv

end Gateaux

end ACEulerLagrange
