/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
/- Portions copyright (c) 2025 Yizheng Zhu; see the adaptation references below. -/
module

public import DynamicalSystems.Linear.Basic
public import DynamicalSystems.InputOutput.StateSpace
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Trajectories of finite-dimensional real linear time-invariant systems

This file develops the elementary solution theory of the finite-dimensional real
linear time-invariant system

```
x'(t) = A x(t) + B u(t),
y(t)  = C x(t) + D u(t),
```

following Trentelman, Stoorvogel and Hautus, *Control Theory for Linear Systems*,
Sections 2.6 and 3.1. The state, input and output maps are those of
`LinearSystem`; the algebraic system is converted to continuous linear maps using
finite-dimensionality, so that a single representation is retained.

The results established here are:

* `LinearSystem.expFlow`: the operator exponential `t ↦ exp (t • A)`, with
  `LinearSystem.hasDerivAt_expFlow` (`d/dt exp (t • A) = exp (t • A) ∘ A`),
  `LinearSystem.hasDerivAt_expFlow_apply_state`, and
  `LinearSystem.continuousA_commute_expFlow`.
* `LinearSystem.homogeneousSolution`: the homogeneous solution
  `x(t) = exp ((t - t₀) • A) x₀`, with `LinearSystem.homogeneousSolution_self`
  and `LinearSystem.hasDerivAt_homogeneousSolution`.
* `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_vector`: the
  vector-valued primitive of an interval integrable function is absolutely
  continuous; the corresponding Mathlib primitive theorem is real-valued only.
  The evaluation-against-operator analogue
  `AbsolutelyContinuousOnInterval.clm_apply` is proved without a `NormSMulClass`
  instance by using operator-norm inequalities.
* `LinearSystem.variationOfConstants`: the variation-of-constants formula
  `x(t) = exp ((t - t₀) • A) (x₀ + ∫_{t₀}^{t} exp (-(s - t₀) • A) (B (u s)) ds)`,
  isolating the forcing in the primitive `LinearSystem.forcing`; the initial
  condition is `LinearSystem.variationOfConstants_self`.
* `LinearSystem.locallyIntegrable_forcing`: the forcing integrand is locally
  integrable for every locally integrable input, proved by applying Mathlib's
  bounded-bilinear strong-measurability lemma
  (`ContinuousLinearMap.aestronglyMeasurable_comp₂`) to the flipped evaluation map
  and dominating by a compact bound on the continuous operator factor.
* `LinearSystem.variationOfConstants_ae_hasDerivAt`: the variation-of-constants
  curve solves `x' = A x + B u` almost everywhere for a locally integrable input,
  via `LocallyIntegrable.ae_hasDerivAt_integral`, the product rule
  `HasDerivAt.clm_apply`, and the semigroup/inverse laws
  `LinearSystem.expFlow_add`, `LinearSystem.expFlow_mul_neg`,
  `LinearSystem.expFlow_neg_mul`.
* `LinearSystem.variationOfConstants_integral`: the curve satisfies the integral
  form of the state equation, obtained from
  `AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero` applied to the
  primitive-subtracted curve; absolute continuity of the product of the smooth
  exponential flow with an absolutely continuous curve is supplied by the
  bounded-bilinear analogue `AbsolutelyContinuousOnInterval.clm_apply`.
* `LinearSystem.variationOfConstants_isCaratheodorySolutionOn`: the bridge to the
  existing Carathéodory integral-solution predicate.
* `LinearSystem.integralSolution_unique`: unconditional uniqueness of continuous
  integral solutions with a fixed locally integrable input, by rotating the
  difference with `exp (-(t - t₀) • A)` and applying
  `is_const_of_deriv_eq_zero`.
* `LinearSystem.ltiStateTrajectoryRel` and `LinearSystem.ltiInputOutputRel`:
  `stateTrajectoryRel`/`inputOutputRel` restricted to locally integrable inputs,
  together with `LinearSystem.ltiStateTrajectoryRel_subset`,
  `LinearSystem.ltiStateTrajectoryRel_existsUnique` and
  `LinearSystem.ltiInputOutputRel_existsUnique`, which are unconditional: the
  existence and uniqueness hypotheses present in the first draft are discharged
  by the analysis above. The readout retains the feedthrough `D`.

## Scope

Existence and uniqueness of continuous integral solutions for locally integrable
inputs are proved here; finite-time controllability and Gramian criteria are separate. The
`_of_existsUnique` variants record the conditional relational bridges for reuse
when an existence/uniqueness hypothesis is available from another source.

## References

The vector-valued primitive and operator-evaluation absolute-continuity proofs adapt Yizheng Zhu's
`Mathlib.MeasureTheory.Function.AbsolutelyContinuous` (Mathlib `v4.34.0-rc2`,
Apache-2.0), using the Bochner norm bound and operator-norm inequality respectively.

* H. L. Trentelman, A. A. Stoorvogel, M. Hautus, *Control Theory for Linear
  Systems*, Springer, 2001, Sections 2.6 and 3.1.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Interval

/-! ### Vector-valued primitives are absolutely continuous -/

/-- The primitive `x ↦ ∫ v in c..x, f v` of an interval integrable function into a
Banach space is absolutely continuous. This is the vector-valued form of
`IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`; the proof is
the same scalar proof with the absolute value replaced by the norm. -/
theorem IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_vector
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {a b c : ℝ} (h : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ ∫ v in c..x, f v) a b := by
  let s := fun E : ℕ × (ℕ → ℝ × ℝ) ↦ ⋃ i ∈ Finset.range E.1, uIoc (E.2 i).1 (E.2 i).2
  have : Tendsto (fun i ↦ ∫⁻ (x : ℝ) in s i, ‖f x‖ₑ ∂volume.restrict (uIoc a b))
      (AbsolutelyContinuousOnInterval.totalLengthFilter (X := ℝ) ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (𝓝 0) :=
    tendsto_setLIntegral_zero
    (ne_of_lt <| intervalIntegrable_iff.mp h |>.hasFiniteIntegral)
    (AbsolutelyContinuousOnInterval.tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero
      _ _)
  have := ENNReal.toReal_zero ▸ (ENNReal.continuousAt_toReal (by simp)).tendsto.comp this
  refine squeeze_zero' ?_ ?_ this
  · filter_upwards with (n, I)
    exact Finset.sum_nonneg (fun _ _ ↦ dist_nonneg)
  simp only [Function.comp_apply, s]
  have : ∀ᶠ (E : ℕ × (ℕ → ℝ × ℝ)) in
      AbsolutelyContinuousOnInterval.totalLengthFilter (X := ℝ) ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b),
      E ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [this] with (n, I) hnI
  obtain ⟨hnI1, hnI2⟩ := mem_ofPred_eq ▸ hnI
  simp only
  rw [← integral_norm_eq_lintegral_enorm (h.aestronglyMeasurable_restrict_uIoc.restrict),
      integral_biUnion_finset _ (by simp +contextual [uIoc]) hnI2]
  · refine Finset.sum_le_sum (fun i hi ↦ ?_)
    rw [dist_eq_norm,
        intervalIntegral.integral_interval_sub_left
          (by apply IntervalIntegrable.mono_set' h; grind [uIoc, uIcc])
          (by apply IntervalIntegrable.mono_set' h; grind [uIoc, uIcc]),
        Measure.restrict_restrict_of_subset
          (AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin hnI
            (Finset.mem_range.mp hi)),
        intervalIntegral.integral_symm, norm_neg,
        intervalIntegral.norm_intervalIntegral_eq]
    exact norm_integral_le_integral_norm _
  · intro i hi
    unfold IntegrableOn
    have h_subset : uIoc ((n, I).2 i).1 ((n, I).2 i).2 ⊆ uIoc a b :=
      AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin hnI (Finset.mem_range.mp hi)
    rw [Measure.restrict_restrict_of_subset h_subset]
    exact IntegrableOn.mono_set h.def'.norm h_subset |>.integrable

/-- Evaluation of an absolutely continuous operator curve against an absolutely continuous vector
curve is absolutely continuous. This is the bounded-bilinear analogue of
`AbsolutelyContinuousOnInterval.smul`, which is not applicable because operator evaluation is not a
`NormSMulClass` (its norm is only submultiplicative). The proof follows the `smul` template,
replacing the exact scalar norm identity by the operator norm inequality. -/
theorem AbsolutelyContinuousOnInterval.clm_apply
    {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T : ℝ → X →L[ℝ] Z} {f : ℝ → X} {a b : ℝ}
    (hT : AbsolutelyContinuousOnInterval T a b)
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ T t (f t)) a b := by
  obtain ⟨C, hC⟩ := hT.exists_bound
  obtain ⟨D, hD⟩ := hf.exists_bound
  have hC' : ∀ x ∈ uIcc a b, ‖T x‖ ≤ max C 0 :=
    fun x hx ↦ (hC x hx).trans (le_max_left _ _)
  have hD' : ∀ x ∈ uIcc a b, ‖f x‖ ≤ max D 0 :=
    fun x hx ↦ (hD x hx).trans (le_max_left _ _)
  have hC0 : (0 : ℝ) ≤ max C 0 := le_max_right _ _
  have hD0 : (0 : ℝ) ≤ max D 0 := le_max_right _ _
  unfold AbsolutelyContinuousOnInterval at hT hf ⊢
  have hdom : Tendsto (fun E : ℕ × (ℕ → ℝ × ℝ) ↦
      max C 0 * (∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2)) +
      max D 0 * (∑ i ∈ Finset.range E.1, dist (T (E.2 i).1) (T (E.2 i).2)))
      (AbsolutelyContinuousOnInterval.totalLengthFilter (X := ℝ) ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (𝓝 0) := by
    have h1 := hf.const_mul (max C 0)
    have h2 := hT.const_mul (max D 0)
    simpa using h1.add h2
  refine squeeze_zero' ?_ ?_ hdom
  · exact Filter.Eventually.of_forall fun _ ↦ Finset.sum_nonneg fun _ _ ↦ dist_nonneg
  · rw [eventually_inf_principal]
    filter_upwards with (n, I) hnI
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i hi ↦ ?_
    have hi' : (I i).1 ∈ uIcc a b ∧ (I i).2 ∈ uIcc a b := (mem_ofPred_eq ▸ hnI).left i hi
    calc dist (T (I i).1 (f (I i).1)) (T (I i).2 (f (I i).2))
        ≤ dist (T (I i).1 (f (I i).1)) (T (I i).1 (f (I i).2)) +
          dist (T (I i).1 (f (I i).2)) (T (I i).2 (f (I i).2)) := dist_triangle _ _ _
      _ ≤ max C 0 * dist (f (I i).1) (f (I i).2) +
          max D 0 * dist (T (I i).1) (T (I i).2) := by
          gcongr
          · rw [dist_eq_norm, dist_eq_norm, ← map_sub]
            calc ‖T (I i).1 (f (I i).1 - f (I i).2)‖
                ≤ ‖T (I i).1‖ * ‖f (I i).1 - f (I i).2‖ := (T (I i).1).le_opNorm _
              _ ≤ max C 0 * ‖f (I i).1 - f (I i).2‖ := by
                  gcongr
                  exact hC' _ hi'.1
          · rw [dist_eq_norm, dist_eq_norm, ← sub_apply]
            calc ‖(T (I i).1 - T (I i).2) (f (I i).2)‖
                ≤ ‖T (I i).1 - T (I i).2‖ * ‖f (I i).2‖ := (T (I i).1 - T (I i).2).le_opNorm _
              _ ≤ ‖T (I i).1 - T (I i).2‖ * max D 0 := by
                  gcongr
                  exact hD' _ hi'.2
              _ = max D 0 * ‖T (I i).1 - T (I i).2‖ := by ring

namespace LinearSystem

variable {X U Y : Type*}

/-! ### Operator-valued exponential curves -/

section Operator

variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The continuous state map associated with a real `LinearSystem` by
finite-dimensional continuity conversion. -/
noncomputable def continuousA (sys : LinearSystem ℝ X U Y) [FiniteDimensional ℝ X] :
    X →L[ℝ] X :=
  sys.A.toContinuousLinearMap

@[simp]
theorem continuousA_apply (sys : LinearSystem ℝ X U Y) [FiniteDimensional ℝ X] (x : X) :
    sys.continuousA x = sys.A x := rfl

/-- The continuous input map associated with a real `LinearSystem`. -/
noncomputable def continuousB (sys : LinearSystem ℝ X U Y) [FiniteDimensional ℝ U] :
    U →L[ℝ] X :=
  sys.B.toContinuousLinearMap

@[simp]
theorem continuousB_apply (sys : LinearSystem ℝ X U Y) [FiniteDimensional ℝ U] (u : U) :
    sys.continuousB u = sys.B u := rfl

/-- The continuous output map associated with a real `LinearSystem`. -/
noncomputable def continuousC (sys : LinearSystem ℝ X U Y) [FiniteDimensional ℝ X] :
    X →L[ℝ] Y :=
  sys.C.toContinuousLinearMap

@[simp]
theorem continuousC_apply (sys : LinearSystem ℝ X U Y) [FiniteDimensional ℝ X] (x : X) :
    sys.continuousC x = sys.C x := rfl

/-- The continuous feedthrough map associated with a real `LinearSystem`. -/
noncomputable def continuousD (sys : LinearSystem ℝ X U Y) [FiniteDimensional ℝ U] :
    U →L[ℝ] Y :=
  sys.D.toContinuousLinearMap

@[simp]
theorem continuousD_apply (sys : LinearSystem ℝ X U Y) [FiniteDimensional ℝ U] (u : U) :
    sys.continuousD u = sys.D u := rfl

end Operator

/-! ### The operator exponential and homogeneous solutions -/

section Exponential

variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The operator exponential `t ↦ exp (t • A)` of the state map of an LTI system.
Source: Trentelman–Stoorvogel–Hautus, equation (2.16). -/
noncomputable def expFlow (sys : LinearSystem ℝ X U Y) (t : ℝ) : X →L[ℝ] X :=
  NormedSpace.exp (t • sys.continuousA)

@[simp]
theorem expFlow_zero (sys : LinearSystem ℝ X U Y) : sys.expFlow 0 = 1 := by
  simp [expFlow]

/-- `d/dt exp (t • A) = exp (t • A) ∘ A`. -/
theorem hasDerivAt_expFlow (sys : LinearSystem ℝ X U Y) (t : ℝ) :
    HasDerivAt (fun s ↦ sys.expFlow s) (sys.expFlow t * sys.continuousA) t := by
  simpa [expFlow] using hasDerivAt_exp_smul_const sys.continuousA t

/-- The state map commutes with the exponential flow. -/
theorem continuousA_commute_expFlow (sys : LinearSystem ℝ X U Y) (t : ℝ) :
    Commute sys.continuousA (sys.expFlow t) := by
  simp only [expFlow]
  exact ((Commute.refl sys.continuousA).smul_right t).exp_right

/-- Pointwise form of `hasDerivAt_expFlow`. -/
theorem hasDerivAt_expFlow_apply (sys : LinearSystem ℝ X U Y) (t : ℝ) (x : X) :
    HasDerivAt (fun s ↦ sys.expFlow s x) (sys.expFlow t (sys.continuousA x)) t := by
  have h := (hasDerivAt_expFlow sys t).clm_apply
    (hasDerivAt_const (c := x) (x := t))
  simpa using h

/-- Pointwise form of `hasDerivAt_expFlow`, with the derivative written as `A` applied to
the evolved state. -/
theorem hasDerivAt_expFlow_apply_state (sys : LinearSystem ℝ X U Y) (t : ℝ) (x : X) :
    HasDerivAt (fun s ↦ sys.expFlow s x) (sys.A (sys.expFlow t x)) t := by
  have h := hasDerivAt_expFlow_apply sys t x
  have hcomm : sys.A (sys.expFlow t x) = sys.expFlow t (sys.A x) := by
    have h1 := (continuousA_commute_expFlow sys t).eq
    have h2 : sys.continuousA (sys.expFlow t x) = sys.expFlow t (sys.continuousA x) :=
      congrFun (congrArg (fun f : X →L[ℝ] X ↦ (f : X → X)) h1) x
    simpa [continuousA_apply] using h2
  rw [hcomm]
  simpa [continuousA_apply] using h

/-- The exponential flow is a one-parameter semigroup,
`exp ((s + t) • A) = exp (s • A) * exp (t • A)`. -/
theorem expFlow_add (sys : LinearSystem ℝ X U Y) (s t : ℝ) :
    sys.expFlow (s + t) = sys.expFlow s * sys.expFlow t := by
  have hcomm : Commute (s • sys.continuousA) (t • sys.continuousA) :=
    ((Commute.refl sys.continuousA).smul_right t).smul_left s
  have hmem : ∀ r : ℝ, r • sys.continuousA ∈
      Metric.eball (0 : X →L[ℝ] X) (NormedSpace.expSeries ℝ (X →L[ℝ] X)).radius :=
    fun r ↦ (NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _
  change NormedSpace.exp ((s + t) • sys.continuousA) =
    NormedSpace.exp (s • sys.continuousA) * NormedSpace.exp (t • sys.continuousA)
  rw [add_smul]
  exact NormedSpace.exp_add_of_commute_of_mem_ball hcomm (hmem s) (hmem t)

/-- `exp (t • A)` is a left inverse of `exp (-t • A)`. -/
theorem expFlow_mul_neg (sys : LinearSystem ℝ X U Y) (t : ℝ) :
    sys.expFlow t * sys.expFlow (-t) = 1 := by
  rw [← expFlow_add, add_neg_cancel, expFlow_zero]

/-- `exp (-t • A)` is a left inverse of `exp (t • A)`. -/
theorem expFlow_neg_mul (sys : LinearSystem ℝ X U Y) (t : ℝ) :
    sys.expFlow (-t) * sys.expFlow t = 1 := by
  rw [← expFlow_add, neg_add_cancel, expFlow_zero]

/-- Evaluation form of `continuousA_commute_expFlow`: the state map commutes with the
exponential flow on vectors. -/
theorem expFlow_apply_continuousA (sys : LinearSystem ℝ X U Y) (t : ℝ) (x : X) :
    sys.expFlow t (sys.continuousA x) = sys.continuousA (sys.expFlow t x) := by
  have h1 := (continuousA_commute_expFlow sys t).eq
  have h2 : sys.continuousA (sys.expFlow t x) = sys.expFlow t (sys.continuousA x) :=
    congrFun (congrArg (fun f : X →L[ℝ] X ↦ (f : X → X)) h1) x
  exact h2.symm

/-- The homogeneous solution `x(t) = exp ((t - t₀) • A) x₀` of `x' = A x`, `x(t₀) = x₀`.
Source: Trentelman–Stoorvogel–Hautus, equation (2.15). -/
noncomputable def homogeneousSolution (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) (x₀ : X)
    (t : ℝ) : X :=
  sys.expFlow (t - t₀) x₀

@[simp]
theorem homogeneousSolution_self (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) (x₀ : X) :
    sys.homogeneousSolution t₀ x₀ t₀ = x₀ := by
  simp [homogeneousSolution]

/-- The homogeneous solution has derivative `A x` at every time. -/
theorem hasDerivAt_homogeneousSolution (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) (x₀ : X)
    (t : ℝ) :
    HasDerivAt (fun s ↦ sys.homogeneousSolution t₀ x₀ s)
      (sys.A (sys.homogeneousSolution t₀ x₀ t)) t := by
  have h := hasDerivAt_expFlow_apply_state sys (t - t₀) x₀
  have hcomp : HasDerivAt (fun s : ℝ ↦ s - t₀) 1 t := (hasDerivAt_id t).sub_const t₀
  simpa [homogeneousSolution, Function.comp_def] using HasDerivAt.scomp (x := t) h hcomp

end Exponential

/-! ### Variation of constants

Trentelman–Stoorvogel–Hautus, equation (2.19), writing the forced solution as
`x(t) = exp ((t - t₀) • A) (x₀ + ∫_{t₀}^{t} exp (-(s - t₀) • A) (B (u s)) ds)`.
This form isolates the forcing into a primitive, which is absolutely continuous by
`IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_vector`, and it makes the
product rule `HasDerivAt.clm_apply` applicable without differentiating under the integral
sign. -/

section Variation

variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The forcing integrand of the variation-of-constants formula,
`s ↦ exp (-(s - t₀) • A) (B (u s))`. -/
noncomputable def forcing (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) (u : ℝ → U) : ℝ → X :=
  fun s ↦ sys.expFlow (-(s - t₀)) (sys.continuousB (u s))

/-- The variation-of-constants formula for an LTI system with input `u` and initial
state `x₀` at time `t₀`. -/
noncomputable def variationOfConstants (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) (x₀ : X)
    (u : ℝ → U) (t : ℝ) : X :=
  sys.expFlow (t - t₀) (x₀ + ∫ s in t₀..t, sys.forcing t₀ u s)

@[simp]
theorem variationOfConstants_self (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) (x₀ : X)
    (u : ℝ → U) : sys.variationOfConstants t₀ x₀ u t₀ = x₀ := by
  simp [variationOfConstants]

omit [FiniteDimensional ℝ U] in
/-- The operator factor of the forcing integrand is continuous in time; this is used to
identify the local integrability of `forcing`. -/
theorem continuous_forcing_operator (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) :
    Continuous (fun s : ℝ ↦ sys.expFlow (-(s - t₀))) := by
  have hdiff : Differentiable ℝ (fun s : ℝ ↦ sys.expFlow s) := by
    simpa [expFlow] using differentiable_exp_smul_const (𝕂 := ℝ) sys.continuousA
  exact hdiff.continuous.comp (by fun_prop)

omit [FiniteDimensional ℝ U] in
/-- The exponential flow along the shifted time `t ↦ exp ((t - t₀) • A)` is continuous. -/
theorem continuous_expFlow_sub (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) :
    Continuous (fun t : ℝ ↦ sys.expFlow (t - t₀)) := by
  have hdiff : Differentiable ℝ (fun s : ℝ ↦ sys.expFlow s) := by
    simpa [expFlow] using differentiable_exp_smul_const (𝕂 := ℝ) sys.continuousA
  exact hdiff.continuous.comp (by fun_prop)

omit [FiniteDimensional ℝ U] in
/-- Derivative of the shifted exponential flow:
`d/dt exp ((t - t₀) • A) = exp ((t - t₀) • A) ∘ A`. -/
theorem hasDerivAt_expFlow_sub (sys : LinearSystem ℝ X U Y) (t₀ t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ sys.expFlow (s - t₀))
      (sys.expFlow (t - t₀) * sys.continuousA) t := by
  have h := (hasDerivAt_expFlow sys (t - t₀)).scomp t (hasDerivAt_id t |>.sub_const t₀)
  simpa [Function.comp_def] using h

omit [FiniteDimensional ℝ U] in
/-- The shifted exponential flow is absolutely continuous, as the primitive
`1 + ∫ exp ((s - t₀) • A) ∘ A` of its continuous derivative. -/
theorem absolutelyContinuousOnInterval_expFlow_sub (sys : LinearSystem ℝ X U Y) (t₀ : ℝ)
    {a b : ℝ} (ht₀ : t₀ ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun t : ℝ ↦ sys.expFlow (t - t₀)) a b := by
  have hcont : Continuous (fun s : ℝ ↦ sys.expFlow (s - t₀) * sys.continuousA) :=
    (continuous_expFlow_sub sys t₀).mul continuous_const
  have hprim : AbsolutelyContinuousOnInterval
      (fun t : ℝ ↦ ∫ s in t₀..t, sys.expFlow (s - t₀) * sys.continuousA) a b :=
    IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_vector
      (hcont.intervalIntegrable a b) ht₀
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ (1 : X →L[ℝ] X)) a b :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ ↦ (1 : X →L[ℝ] X))).contDiffOn
      |>.absolutelyContinuousOnInterval
  have hfun : (fun t : ℝ ↦ sys.expFlow (t - t₀)) =
      (fun t : ℝ ↦ (1 : X →L[ℝ] X) +
        ∫ s in t₀..t, sys.expFlow (s - t₀) * sys.continuousA) := by
    funext t
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := t₀) (b := t)
      (f := fun r : ℝ ↦ sys.expFlow (r - t₀))
      (f' := fun s : ℝ ↦ sys.expFlow (s - t₀) * sys.continuousA)
      (fun s _ ↦ hasDerivAt_expFlow_sub sys t₀ s) (hcont.intervalIntegrable t₀ t)
    rw [h, sub_self, expFlow_zero]
    abel
  rw [hfun]
  exact hconst.add hprim

/-- The shifted flow cancels the forcing integrand: `exp ((t - t₀) • A) (forcing t) = B (u t)`. -/
theorem expFlow_forcing (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) (u : ℝ → U) (t : ℝ) :
    sys.expFlow (t - t₀) (sys.forcing t₀ u t) = sys.continuousB (u t) := by
  simp only [forcing]
  rw [← mul_apply_eq_comp, ← expFlow_add, add_neg_cancel, expFlow_zero]
  simp

/-- The forcing integrand of an LTI system is locally integrable whenever the input is. This
is proved by evaluating the fixed bounded bilinear map `ContinuousLinearMap.apply ℝ X` (flipped)
on the measurable operator and vector curves, then
dominate by the continuous operator bound times `‖u‖` on compact sets. -/
theorem locallyIntegrable_forcing (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) {u : ℝ → U}
    (hu : LocallyIntegrable u volume) :
    LocallyIntegrable (sys.forcing t₀ u) volume := by
  have hB_meas : AEStronglyMeasurable (fun s : ℝ ↦ sys.continuousB (u s)) volume :=
    sys.continuousB.continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable
  have hforcing_meas : AEStronglyMeasurable (sys.forcing t₀ u) volume := by
    have h := ContinuousLinearMap.aestronglyMeasurable_comp₂
      ((ContinuousLinearMap.apply ℝ X).flip)
      (continuous_forcing_operator sys t₀).aestronglyMeasurable hB_meas
    change AEStronglyMeasurable
      (fun s : ℝ ↦ sys.expFlow (-(s - t₀)) (sys.continuousB (u s))) volume
    simpa only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.apply_apply] using h
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (continuous_forcing_operator sys t₀).norm.continuousOn
  have hbound_int : Integrable (fun s : ℝ ↦ (max M 0 * ‖sys.continuousB‖) * ‖u s‖)
      (volume.restrict K) :=
    ((hu.integrableOn_isCompact hK).norm.const_mul (max M 0 * ‖sys.continuousB‖))
  refine Integrable.mono' hbound_int hforcing_meas.restrict ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with s hs
  calc ‖sys.forcing t₀ u s‖
      = ‖sys.expFlow (-(s - t₀)) (sys.continuousB (u s))‖ := rfl
    _ ≤ ‖sys.expFlow (-(s - t₀))‖ * ‖sys.continuousB (u s)‖ :=
        (sys.expFlow (-(s - t₀))).le_opNorm _
    _ ≤ max M 0 * (‖sys.continuousB‖ * ‖u s‖) := by
        gcongr
        · have := (hM s hs).trans (le_max_left M (0 : ℝ))
          simpa using this
        · exact sys.continuousB.le_opNorm (u s)
    _ = (max M 0 * ‖sys.continuousB‖) * ‖u s‖ := by ring

/-- The forcing is interval integrable on every interval. -/
theorem intervalIntegrable_forcing (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) {u : ℝ → U}
    (hu : LocallyIntegrable u volume) (a b : ℝ) :
    IntervalIntegrable (sys.forcing t₀ u) volume a b :=
  intervalIntegrable_iff.mpr <|
    ((locallyIntegrable_forcing sys t₀ hu).integrableOn_isCompact isCompact_uIcc).mono_set
      uIoc_subset_uIcc

/-- The dynamics `s ↦ A x(s) + B u(s)` along a continuous state curve and a locally integrable
input is locally integrable. -/
theorem locallyIntegrable_dynamics (sys : LinearSystem ℝ X U Y) (x : ℝ → X) (u : ℝ → U)
    (hx : Continuous x) (hu : LocallyIntegrable u volume) :
    LocallyIntegrable (fun s ↦ sys.dynamics (x s) (u s)) volume := by
  have hAx : LocallyIntegrable (fun s ↦ sys.continuousA (x s)) volume :=
    (sys.continuousA.continuous.comp hx).locallyIntegrable
  have hBu : LocallyIntegrable (fun s ↦ sys.continuousB (u s)) volume :=
    (hu.smul (‖sys.continuousB‖)).mono
      (sys.continuousB.continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable)
      (by
        filter_upwards with s
        simpa [norm_smul] using sys.continuousB.le_opNorm (u s))
  rw [locallyIntegrable_iff]
  intro K hK
  have hA_int := hAx.integrableOn_isCompact hK
  have hB_int := hBu.integrableOn_isCompact hK
  exact hA_int.add hB_int

/-- The variation-of-constants curve is continuous for a locally integrable input. -/
theorem continuous_variationOfConstants (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) (x₀ : X)
    (u : ℝ → U) (hu : LocallyIntegrable u volume) :
    Continuous (sys.variationOfConstants t₀ x₀ u) := by
  have hP : Continuous (fun t : ℝ ↦ ∫ s in t₀..t, sys.forcing t₀ u s) :=
    intervalIntegral.continuous_primitive (intervalIntegrable_forcing sys t₀ hu) t₀
  have hE : Continuous (fun t : ℝ ↦ sys.expFlow (t - t₀)) := continuous_expFlow_sub sys t₀
  have hQ : Continuous (fun t : ℝ ↦ x₀ + ∫ s in t₀..t, sys.forcing t₀ u s) :=
    continuous_const.add hP
  exact hE.clm_apply hQ

/-- The variation-of-constants curve is absolutely continuous on every interval containing `t₀`. -/
theorem variationOfConstants_absolutelyContinuousOnInterval_of_mem (sys : LinearSystem ℝ X U Y)
    (t₀ : ℝ) (x₀ : X) (u : ℝ → U) (hu : LocallyIntegrable u volume) {a b : ℝ}
    (ht₀ : t₀ ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (sys.variationOfConstants t₀ x₀ u) a b := by
  have hforcing_int : IntervalIntegrable (sys.forcing t₀ u) volume a b :=
    intervalIntegrable_forcing sys t₀ hu a b
  have hPrim : AbsolutelyContinuousOnInterval
      (fun t : ℝ ↦ ∫ s in t₀..t, sys.forcing t₀ u s) a b :=
    IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_vector hforcing_int ht₀
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ x₀) a b :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ ↦ x₀)).contDiffOn.absolutelyContinuousOnInterval
  have hQ : AbsolutelyContinuousOnInterval
      (fun t : ℝ ↦ x₀ + ∫ s in t₀..t, sys.forcing t₀ u s) a b := by
    exact hconst.add hPrim
  have hE : AbsolutelyContinuousOnInterval (fun t : ℝ ↦ sys.expFlow (t - t₀)) a b :=
    absolutelyContinuousOnInterval_expFlow_sub sys t₀ ht₀
  have hx := hE.clm_apply hQ
  exact hx

/-- The variation-of-constants curve is absolutely continuous on every compact time interval,
whether or not that interval contains the initial time. -/
theorem variationOfConstants_absolutelyContinuousOnInterval (sys : LinearSystem ℝ X U Y)
    (t₀ : ℝ) (x₀ : X) (u : ℝ → U) (hu : LocallyIntegrable u volume) (a b : ℝ) :
    AbsolutelyContinuousOnInterval (sys.variationOfConstants t₀ x₀ u) a b := by
  have hbase : t₀ ∈ uIcc (min a (min b t₀)) (max a (max b t₀)) := by
    grind [mem_uIcc]
  apply (variationOfConstants_absolutelyContinuousOnInterval_of_mem sys t₀ x₀ u hu hbase).mono
  apply uIcc_subset_uIcc <;> grind [mem_uIcc]

/-- Almost-everywhere derivative of the variation-of-constants curve: it solves
`x' = A x + B u` for a locally integrable input. -/
theorem variationOfConstants_ae_hasDerivAt (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) (x₀ : X)
    (u : ℝ → U) (hu : LocallyIntegrable u volume) :
    ∀ᵐ t, HasDerivAt (sys.variationOfConstants t₀ x₀ u)
      (sys.dynamics (sys.variationOfConstants t₀ x₀ u t) (u t)) t := by
  have hP : ∀ᵐ t : ℝ, HasDerivAt
      (fun s : ℝ ↦ ∫ r in t₀..s, sys.forcing t₀ u r) (sys.forcing t₀ u t) t :=
    (LocallyIntegrable.ae_hasDerivAt_integral (locallyIntegrable_forcing sys t₀ hu)).mono
      (fun t ht ↦ ht t₀)
  filter_upwards [hP] with t ht
  have hE : HasDerivAt (fun s : ℝ ↦ sys.expFlow (s - t₀))
      (sys.expFlow (t - t₀) * sys.continuousA) t := hasDerivAt_expFlow_sub sys t₀ t
  have hQ : HasDerivAt (fun s : ℝ ↦ x₀ + ∫ r in t₀..s, sys.forcing t₀ u r)
      (sys.forcing t₀ u t) t := by
    have h := (hasDerivAt_const (x := t) (c := x₀)).add ht
    change HasDerivAt (fun s : ℝ ↦ x₀ + ∫ r in t₀..s, sys.forcing t₀ u r)
      (0 + sys.forcing t₀ u t) t at h
    simpa only [zero_add] using h
  have hprod := hE.clm_apply hQ
  have hderiv : (sys.expFlow (t - t₀) * sys.continuousA)
        (x₀ + ∫ r in t₀..t, sys.forcing t₀ u r) +
        sys.expFlow (t - t₀) (sys.forcing t₀ u t) =
        sys.dynamics (sys.variationOfConstants t₀ x₀ u t) (u t) := by
    rw [mul_apply_eq_comp, expFlow_forcing, expFlow_apply_continuousA]
    simp [variationOfConstants, dynamics, continuousA_apply, continuousB_apply]
  rw [hderiv] at hprod
  change HasDerivAt
    (fun s : ℝ ↦ sys.expFlow (s - t₀) (x₀ + ∫ r in t₀..s, sys.forcing t₀ u r))
    (sys.dynamics (sys.variationOfConstants t₀ x₀ u t) (u t)) t
  exact hprod

/-- The variation-of-constants curve satisfies the integral form of the LTI state equation for a
locally integrable input. -/
theorem variationOfConstants_integral (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) (x₀ : X)
    (u : ℝ → U) (hu : LocallyIntegrable u volume) (t : ℝ) :
    sys.variationOfConstants t₀ x₀ u t =
      x₀ + ∫ s in t₀..t, sys.dynamics (sys.variationOfConstants t₀ x₀ u s) (u s) := by
  let x := sys.variationOfConstants t₀ x₀ u
  let F : ℝ → X := fun s ↦ sys.dynamics (x s) (u s)
  let g : ℝ → X := fun s ↦ x s - x₀ - ∫ r in t₀..s, F r
  have hx_cont : Continuous x := continuous_variationOfConstants sys t₀ x₀ u hu
  have hF_loc : LocallyIntegrable F volume := locallyIntegrable_dynamics sys x u hx_cont hu
  let R : ℝ := |t - t₀| + 1
  have hR : 0 < R := by positivity
  have hle : t₀ - R ≤ t₀ + R := by linarith
  have hF_int : IntervalIntegrable F volume (t₀ - R) (t₀ + R) :=
    intervalIntegrable_iff.mpr <|
      (hF_loc.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have ht₀ : t₀ ∈ uIcc (t₀ - R) (t₀ + R) := by
    rw [uIcc_of_le hle]
    exact ⟨by linarith, by linarith⟩
  have ht : t ∈ uIcc (t₀ - R) (t₀ + R) := by
    rw [uIcc_of_le hle]
    exact ⟨by linarith [neg_abs_le (t - t₀)], by linarith [le_abs_self (t - t₀)]⟩
  have hx_ac : AbsolutelyContinuousOnInterval x (t₀ - R) (t₀ + R) :=
    variationOfConstants_absolutelyContinuousOnInterval sys t₀ x₀ u hu _ _
  have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ x₀) (t₀ - R) (t₀ + R) :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ ↦ x₀)).contDiffOn.absolutelyContinuousOnInterval
  have hprim : AbsolutelyContinuousOnInterval (fun s : ℝ ↦ ∫ r in t₀..s, F r)
      (t₀ - R) (t₀ + R) :=
    IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral_vector hF_int ht₀
  have hg_ac : AbsolutelyContinuousOnInterval g (t₀ - R) (t₀ + R) := by
    have h := (hx_ac.sub hconst).sub hprim
    exact h
  have hx_deriv := variationOfConstants_ae_hasDerivAt sys t₀ x₀ u hu
  have hF_deriv : ∀ᵐ s : ℝ, HasDerivAt (fun r : ℝ ↦ ∫ q in t₀..r, F q) (F s) s :=
    (LocallyIntegrable.ae_hasDerivAt_integral hF_loc).mono (fun s hs ↦ hs t₀)
  have hg_ae : ∀ᵐ s, s ∈ uIcc (t₀ - R) (t₀ + R) → HasDerivAt g 0 s := by
    filter_upwards [hx_deriv, hF_deriv] with s hs hsF _
    have h1 : HasDerivAt (fun r : ℝ ↦ x r - x₀) (sys.dynamics (x s) (u s) - 0) s :=
      hs.sub (hasDerivAt_const (x := s) (c := x₀))
    have h2 : HasDerivAt g (sys.dynamics (x s) (u s) - 0 - F s) s :=
      h1.sub hsF
    have hzero : sys.dynamics (x s) (u s) - 0 - F s = 0 := by simp [F]
    rwa [hzero] at h2
  obtain ⟨C, hC⟩ := AbsolutelyContinuousOnInterval.const_of_ae_hasDerivAt_zero hg_ac hg_ae
  have hC0 : C = 0 := by
    rw [← hC t₀ ht₀]
    simp [g, x, variationOfConstants_self]
  have hgt : g t = 0 := by rw [hC t ht, hC0]
  have hsub : x t - x₀ = ∫ s in t₀..t, F s := sub_eq_zero.mp hgt
  rw [sub_eq_iff_eq_add, add_comm] at hsub
  simpa [x, F] using hsub

/-- The variation-of-constants curve is a Carathéodory integral solution of the LTI state
equation with a locally integrable input. -/
theorem variationOfConstants_isCaratheodorySolutionOn (sys : LinearSystem ℝ X U Y) (t₀ : ℝ)
    (x₀ : X) (u : ℝ → U) (hu : LocallyIntegrable u volume) :
    IsCaratheodorySolutionOn (sys.variationOfConstants t₀ x₀ u)
      (fun (t : ℝ) x ↦ sys.dynamics x (u t)) t₀ x₀ Set.univ :=
  fun t _ ↦ variationOfConstants_integral sys t₀ x₀ u hu t

/-- Uniqueness of continuous integral solutions of the LTI state equation with a fixed locally
integrable input: subtracting the two integral equations cancels the input and leaves the
homogeneous equation `w' = A w`, which the rotated curve `exp (-(t - t₀) • A) w(t)` has zero
derivative and initial value zero, hence vanishes identically. -/
theorem integralSolution_unique (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) (x₀ : X) (u : ℝ → U)
    (hu : LocallyIntegrable u volume) {x y : ℝ → X}
    (hx_cont : Continuous x) (hx₀ : x t₀ = x₀)
    (hx_int : ∀ t, x t = x₀ + ∫ s in t₀..t, sys.dynamics (x s) (u s))
    (hy_cont : Continuous y) (hy₀ : y t₀ = x₀)
    (hy_int : ∀ t, y t = x₀ + ∫ s in t₀..t, sys.dynamics (y s) (u s)) :
    x = y := by
  have hx_loc : LocallyIntegrable (fun s ↦ sys.dynamics (x s) (u s)) volume :=
    locallyIntegrable_dynamics sys x u hx_cont hu
  have hy_loc : LocallyIntegrable (fun s ↦ sys.dynamics (y s) (u s)) volume :=
    locallyIntegrable_dynamics sys y u hy_cont hu
  have hx_dyn_int (a b : ℝ) :
      IntervalIntegrable (fun s ↦ sys.dynamics (x s) (u s)) volume a b :=
    intervalIntegrable_iff.mpr <|
      (hx_loc.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have hy_dyn_int (a b : ℝ) :
      IntervalIntegrable (fun s ↦ sys.dynamics (y s) (u s)) volume a b :=
    intervalIntegrable_iff.mpr <|
      (hy_loc.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  let w : ℝ → X := x - y
  have hw_cont : Continuous w := hx_cont.sub hy_cont
  have hw_int : ∀ t, w t = ∫ s in t₀..t, sys.continuousA (w s) := by
    intro t
    calc w t = (x t - x₀) - (y t - x₀) := by simp [w]
      _ = (∫ s in t₀..t, sys.dynamics (x s) (u s)) -
            (∫ s in t₀..t, sys.dynamics (y s) (u s)) := by
              rw [hx_int t, hy_int t]; abel
      _ = ∫ s in t₀..t, (sys.dynamics (x s) (u s) - sys.dynamics (y s) (u s)) :=
            (intervalIntegral.integral_sub (hx_dyn_int t₀ t) (hy_dyn_int t₀ t)).symm
      _ = ∫ s in t₀..t, sys.continuousA (w s) := by
            refine intervalIntegral.integral_congr fun s _ ↦ ?_
            simp only [dynamics, continuousA_apply, w, Pi.sub_apply, map_sub]
            abel
  have hA_cont : Continuous (fun s ↦ sys.continuousA (w s)) :=
    sys.continuousA.continuous.comp hw_cont
  have hw_deriv : ∀ t, HasDerivAt w (sys.continuousA (w t)) t := by
    intro t
    have h := intervalIntegral.integral_hasDerivAt_right
      (hA_cont.intervalIntegrable t₀ t)
      hA_cont.aestronglyMeasurable.stronglyMeasurableAtFilter hA_cont.continuousAt
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s ↦ hw_int s)
  let g : ℝ → X := fun t ↦ sys.expFlow (t₀ - t) (w t)
  have hg_deriv : ∀ t, HasDerivAt g 0 t := by
    intro t
    have hE : HasDerivAt (fun s : ℝ ↦ sys.expFlow (t₀ - s))
        (-(sys.expFlow (t₀ - t) * sys.continuousA)) t := by
      have h := (hasDerivAt_expFlow sys (t₀ - t)).scomp t
        ((hasDerivAt_const (x := t) (c := t₀)).sub (hasDerivAt_id t))
      simpa [Function.comp_def] using h
    have hprod := hE.clm_apply (hw_deriv t)
    have hderiv : (-(sys.expFlow (t₀ - t) * sys.continuousA)) (w t) +
        sys.expFlow (t₀ - t) (sys.continuousA (w t)) = 0 := by
      rw [neg_apply, mul_apply_eq_comp, neg_add_cancel]
    rw [hderiv] at hprod
    simpa [g] using hprod
  have hg_diff : Differentiable ℝ g := fun t ↦ (hg_deriv t).differentiableAt
  have hg_const (a b : ℝ) : g a = g b :=
    is_const_of_deriv_eq_zero hg_diff (fun t ↦ (hg_deriv t).deriv) a b
  have hw_zero : ∀ t, w t = 0 := by
    intro t
    have hgt : sys.expFlow (t₀ - t) (w t) = 0 := by
      have h := hg_const t t₀
      change sys.expFlow (t₀ - t) (w t) = sys.expFlow (t₀ - t₀) (w t₀) at h
      simpa [w, hx₀, hy₀] using h
    calc w t = sys.expFlow (-(t₀ - t)) (sys.expFlow (t₀ - t) (w t)) := by
            rw [← mul_apply_eq_comp, expFlow_neg_mul]
            simp
      _ = sys.expFlow (-(t₀ - t)) 0 := by rw [hgt]
      _ = 0 := by simp
  funext t
  exact sub_eq_zero.mp (hw_zero t)

end Variation

/-! ### Admissible state-trajectory and input-output relations

`stateTrajectoryRel` and `inputOutputRel` keep pointwise input functions. We restrict
them to the admissible class of locally integrable inputs used in the analysis above;
the readout retains the feedthrough `D`. Nonzero `D` is exactly why pointwise outputs
cannot be identified for merely almost-everywhere-equal inputs. -/

section Bridges

variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The LTI state trajectory relation restricted to locally integrable inputs. -/
def ltiStateTrajectoryRel (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) (x₀ : X) :
    SetRel (ℝ → U) (ℝ → X) :=
  { p | LocallyIntegrable p.1 volume ∧ p.2 t₀ = x₀ ∧ Continuous p.2 ∧
    ∀ t, p.2 t = x₀ + ∫ s in t₀..t, sys.dynamics (p.2 s) (p.1 s) }

/-- The LTI input-output relation restricted to locally integrable inputs. The readout
`y = C x + D u` retains the feedthrough term `D`. -/
def ltiInputOutputRel (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) (x₀ : X) :
    SetRel (ℝ → U) (ℝ → Y) :=
  { p | ∃ x, (p.1, x) ∈ sys.ltiStateTrajectoryRel t₀ x₀ ∧
    ∀ t, p.2 t = sys.readout (x t) (p.1 t) }

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ U] in
/-- The restricted LTI state relation is contained in the corresponding instance of the
generic `stateTrajectoryRel` with the LTI vector field. -/
theorem ltiStateTrajectoryRel_subset (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) (x₀ : X) :
    sys.ltiStateTrajectoryRel t₀ x₀ ⊆
      stateTrajectoryRel (fun _ x u ↦ sys.dynamics x u) x₀ t₀ := by
  rintro p ⟨_, hx₀, hcont, hint⟩
  exact ⟨hx₀, hcont, hint⟩

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ U] in
/-- The restricted LTI output relation is contained in the existing generic input-output
relation with the same dynamics and readout, including feedthrough. -/
theorem ltiInputOutputRel_subset (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) (x₀ : X) :
    sys.ltiInputOutputRel t₀ x₀ ⊆
      inputOutputRel (fun _ x u ↦ sys.dynamics x u)
        (fun _ x u ↦ sys.readout x u) x₀ t₀ := by
  rintro p ⟨x, hx, hy⟩
  exact ⟨x, ltiStateTrajectoryRel_subset sys t₀ x₀ hx, hy⟩

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ U] in
/-- The LTI state relation is exactly the generic state relation restricted to locally
integrable inputs. -/
theorem mem_ltiStateTrajectoryRel_iff (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) (x₀ : X)
    (u : ℝ → U) (x : ℝ → X) :
    (u, x) ∈ sys.ltiStateTrajectoryRel t₀ x₀ ↔
      LocallyIntegrable u volume ∧
        (u, x) ∈ stateTrajectoryRel (fun _ x u ↦ sys.dynamics x u) x₀ t₀ := Iff.rfl

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ U] in
/-- The LTI input-output relation is exactly the generic relation restricted to locally
integrable inputs, with no regularity condition imposed on the pointwise readout. -/
theorem mem_ltiInputOutputRel_iff (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) (x₀ : X)
    (u : ℝ → U) (y : ℝ → Y) :
    (u, y) ∈ sys.ltiInputOutputRel t₀ x₀ ↔
      LocallyIntegrable u volume ∧
        (u, y) ∈ inputOutputRel (fun _ x u ↦ sys.dynamics x u)
          (fun _ x u ↦ sys.readout x u) x₀ t₀ := by
  constructor
  · rintro ⟨x, hx, hy⟩
    exact ⟨hx.1, x, hx.2, hy⟩
  · rintro ⟨hu, x, hx, hy⟩
    exact ⟨x, ⟨hu, hx⟩, hy⟩

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ U] in
/-- Under uniqueness of continuous integral solutions, every admissible input determines
a unique state trajectory. -/
theorem ltiStateTrajectoryRel_existsUnique_of_existsUnique (sys : LinearSystem ℝ X U Y)
    (t₀ : ℝ) (x₀ : X)
    (h_exist_unique : ∀ u : ℝ → U, LocallyIntegrable u volume →
      ∃! x : ℝ → X, Continuous x ∧ x t₀ = x₀ ∧
        ∀ t, x t = x₀ + ∫ s in t₀..t, sys.dynamics (x s) (u s)) :
    ∀ u : ℝ → U, LocallyIntegrable u volume →
      ∃! x : ℝ → X, (u, x) ∈ sys.ltiStateTrajectoryRel t₀ x₀ := by
  intro u hu
  obtain ⟨x, ⟨hx_cont, hx₀, hx_int⟩, hx_unique⟩ := h_exist_unique u hu
  refine ⟨x, ⟨hu, hx₀, hx_cont, hx_int⟩, ?_⟩
  rintro x' ⟨_, hx'₀, hx'_cont, hx'_int⟩
  exact hx_unique x' ⟨hx'_cont, hx'₀, hx'_int⟩

/-- Every admissible (locally integrable) input determines a unique state trajectory. This is
the unconditional LTI existence and uniqueness theorem: existence is the variation-of-constants
curve, and uniqueness is `LinearSystem.integralSolution_unique`. -/
theorem ltiStateTrajectoryRel_existsUnique (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) (x₀ : X) :
    ∀ u : ℝ → U, LocallyIntegrable u volume →
      ∃! x : ℝ → X, (u, x) ∈ sys.ltiStateTrajectoryRel t₀ x₀ := by
  intro u hu
  refine ⟨sys.variationOfConstants t₀ x₀ u,
    ⟨hu, variationOfConstants_self sys t₀ x₀ u,
      continuous_variationOfConstants sys t₀ x₀ u hu,
      fun t ↦ variationOfConstants_integral sys t₀ x₀ u hu t⟩, ?_⟩
  rintro x' ⟨_, hx'₀, hx'_cont, hx'_int⟩
  exact (integralSolution_unique sys t₀ x₀ u hu
    (continuous_variationOfConstants sys t₀ x₀ u hu)
    (variationOfConstants_self sys t₀ x₀ u)
    (fun t ↦ variationOfConstants_integral sys t₀ x₀ u hu t)
    hx'_cont hx'₀ hx'_int).symm

omit [FiniteDimensional ℝ X] [FiniteDimensional ℝ U] in
/-- Under unique state trajectories, every admissible input determines a unique output
trajectory, with the feedthrough `D` retained in the readout. -/
theorem ltiInputOutputRel_existsUnique_of_existsUnique (sys : LinearSystem ℝ X U Y)
    (t₀ : ℝ) (x₀ : X)
    (h_state : ∀ u : ℝ → U, LocallyIntegrable u volume →
      ∃! x : ℝ → X, (u, x) ∈ sys.ltiStateTrajectoryRel t₀ x₀) :
    ∀ u : ℝ → U, LocallyIntegrable u volume →
      ∃! y : ℝ → Y, (u, y) ∈ sys.ltiInputOutputRel t₀ x₀ := by
  intro u hu
  obtain ⟨x, hx_mem, hx_unique⟩ := h_state u hu
  refine ⟨fun t ↦ sys.readout (x t) (u t), ⟨x, hx_mem, fun _ ↦ rfl⟩, ?_⟩
  rintro y' ⟨x', hx'_mem, hy'⟩
  have hx_eq : x' = x := hx_unique x' hx'_mem
  subst hx_eq
  ext t
  exact hy' t

/-- Every admissible (locally integrable) input determines a unique output trajectory, with the
feedthrough `D` retained in the readout. -/
theorem ltiInputOutputRel_existsUnique (sys : LinearSystem ℝ X U Y) (t₀ : ℝ) (x₀ : X) :
    ∀ u : ℝ → U, LocallyIntegrable u volume →
      ∃! y : ℝ → Y, (u, y) ∈ sys.ltiInputOutputRel t₀ x₀ :=
  ltiInputOutputRel_existsUnique_of_existsUnique sys t₀ x₀
    (ltiStateTrajectoryRel_existsUnique sys t₀ x₀)

end Bridges

end LinearSystem
