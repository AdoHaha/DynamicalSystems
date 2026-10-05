/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.CalculusOfVariations
public import DynamicalSystems.OptimalControl.ContinuousTime.ConstrainedCoVMultipliers
public import DynamicalSystems.OptimalControl.ContinuousTime.LagrangianCovectorRegularity
public import DynamicalSystems.OptimalControl.ContinuousTime.FirstVariationDifferentiation
public import DynamicalSystems.OptimalControl.ContinuousTime.EulerLagrangeStationarity
public import DynamicalSystems.OptimalControl.ContinuousTime.WeakEulerLagrange
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Isoperimetric Euler–Lagrange equations

A single normal multiplier is extracted from genuine constrained optimality and
annihilates the cost/constraint combination for every endpoint-preserving `C¹`
direction.  The admissible two-parameter families are constructed inside an
explicit fixed-endpoint curve class; their strict derivatives come from the
actual integral differentiation theorem.

The final horizon theorem derives momentum differentiability and the exact
existing vanishing-first-variation predicate, including all differentiable test
directions.  Its endpoint derivatives are within the horizon.  A `C²` corollary
supplies the ordinary two-sided endpoint derivatives required by the existing
`eulerLagrange` predicate.

The multiplier interface `isoperimetricMultiplier_exists` applies the abstract
curve-family extraction to the two-parameter family; the conditional bridge
`eulerLagrange_of_augmentedVanishing` turns an assumed augmented vanishing
first variation into the augmented Euler–Lagrange equation.
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped Topology Interval


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **One common isoperimetric multiplier for the actual two-parameter family.**
Under a genuine constrained minimum of the actual `cvFunctional` integrals and the
derived strict differentiability of the parameterized pair, the multiplier
extracted from the `ξ` component is `-δJ[ξ] / δC[ξ]` and it annihilates the
combined first variation.  The scope is precisely the fixed pair `(η, ξ)`: the
identity holds for all `p ∈ ℝ × ℝ`, i.e. on `span{η,ξ}` only.  The value is
`η`-independent given `ξ`, but each invocation fixes one `η` and there is no single
invocation ranging over all test directions.  This is the multiplier interface
applied to a genuinely feasible family; the differentiability premise is the
derived `hasStrictFDerivAt_parameterFunctional`. -/
theorem _root_.IsoperimetricVariation.isoperimetricMultiplier_exists
    (L G : ℝ → E → E → ℝ) (K : E → ℝ) (T : ℝ)
    (S : Set (ℝ → E)) (x η ξ : ℝ → E)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (hG : ContDiff ℝ 1 (uncurryLagrangian G))
    (hK : ContDiff ℝ 1 K)
    (hx : ContDiff ℝ 1 x) (hη : ContDiff ℝ 1 η) (hξ : ContDiff ℝ 1 ξ) (hT : 0 ≤ T)
    (hΓ : ∀ p : ℝ × ℝ, perturbedCurve x η ξ p ∈ S)
    (hopt : IsMinOn (cvFunctional L K T)
      {y | y ∈ S ∧ cvFunctional G (fun _ ↦ 0) T y = cvFunctional G (fun _ ↦ 0) T x} x)
    (hξreg : firstVariation G (fun _ ↦ 0) T x ξ ≠ 0) :
    ∃ lam : ℝ, lam = -(firstVariation L K T x ξ) /
        (firstVariation G (fun _ ↦ 0) T x ξ) ∧
      ∀ p : ℝ × ℝ,
        (parameterDerivative (firstVariation L K T x η) (firstVariation L K T x ξ)) p
          + lam * (parameterDerivative (firstVariation G (fun _ ↦ 0) T x η)
            (firstVariation G (fun _ ↦ 0) T x ξ)) p = 0 := by
  have hJ := hasStrictFDerivAt_cvFunctional_perturbed L K T x η ξ hL hK hx hη hξ hT
  have hC := hasStrictFDerivAt_cvFunctional_perturbed G (fun _ ↦ 0) T x η ξ hG
    contDiff_const hx hη hξ hT
  have hC' : parameterDerivative (firstVariation G (fun _ ↦ 0) T x η)
      (firstVariation G (fun _ ↦ 0) T x ξ) ≠ 0 := by
    intro h
    apply hξreg
    have := congrArg (fun f : (ℝ × ℝ) →L[ℝ] ℝ ↦ f (0, 1)) h
    simpa using this
  obtain ⟨lam, hlam⟩ := IsoperimetricVariation.exists_normal_multiplier_of_curve_family
    L G K T S x (perturbedCurve x η ξ) (perturbedCurve_zero x η ξ) hΓ hopt _ _ hJ hC hC'
  have hJξval : (parameterDerivative (firstVariation L K T x η) (firstVariation L K T x ξ))
      (0, 1) = firstVariation L K T x ξ := by
    simp [parameterDerivative]
  have hCξval : (parameterDerivative (firstVariation G (fun _ ↦ 0) T x η)
      (firstVariation G (fun _ ↦ 0) T x ξ)) (0, 1) =
      firstVariation G (fun _ ↦ 0) T x ξ := by
    simp [parameterDerivative]
  have hlamξ := hlam (0, 1)
  rw [hJξval, hCξval] at hlamξ
  refine ⟨lam, ?_, hlam⟩
  field_simp
  linarith

/-- One explicit multiplier annihilates the cost/constraint combination for
every endpoint-preserving C1 direction. The nonzero constraint direction is
fixed before quantifying over the arbitrary test direction. -/
theorem _root_.IsoperimetricVariation.exists_common_isoperimetricMultiplier
    (L G : ℝ → E → E → ℝ) (K : E → ℝ) (T : ℝ) (x : ℝ → E)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L))
    (hG : ContDiff ℝ 1 (uncurryLagrangian G)) (hK : ContDiff ℝ 1 K)
    (hx : ContDiff ℝ 1 x) (hT : 0 ≤ T)
    (hopt : IsMinOn (cvFunctional L K T)
      {y | y ∈ fixedEndpointC1Curves T (x 0) (x T) ∧
        cvFunctional G (fun _ ↦ 0) T y = cvFunctional G (fun _ ↦ 0) T x} x)
    (hregular : ∃ ξ : ℝ → E, ContDiff ℝ 1 ξ ∧ ξ 0 = 0 ∧ ξ T = 0 ∧
      firstVariation G (fun _ ↦ 0) T x ξ ≠ 0) :
    ∃ lam : ℝ, ∀ η : ℝ → E, ContDiff ℝ 1 η → η 0 = 0 → η T = 0 →
      firstVariation L K T x η + lam * firstVariation G (fun _ ↦ 0) T x η = 0 := by
  obtain ⟨ξ, hξ, hξ₀, hξT, hξreg⟩ := hregular
  refine ⟨-(firstVariation L K T x ξ) / firstVariation G (fun _ ↦ 0) T x ξ, ?_⟩
  intro η hη hη₀ hηT
  obtain ⟨lam, hlam, hstationary⟩ := _root_.IsoperimetricVariation.isoperimetricMultiplier_exists L G K T
    (fixedEndpointC1Curves T (x 0) (x T)) x η ξ hL hG hK hx hη hξ hT
    (perturbedCurve_mem_fixedEndpointC1Curves T x η ξ hx hη hξ hη₀ hηT hξ₀ hξT)
    hopt hξreg
  simpa only [parameterDerivative_one_zero, hlam] using hstationary (1, 0)

/-- Actual constrained optimality produces a single multiplier and augmented
stationarity for every C1 endpoint-preserving direction. No first-variation
identity or multiplier is supplied as an input. -/
theorem _root_.IsoperimetricVariation.exists_augmented_stationarity_of_isoperimetric
    (L G : ℝ → E → E → ℝ) (K : E → ℝ) (T : ℝ) (x : ℝ → E)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L))
    (hG : ContDiff ℝ 1 (uncurryLagrangian G)) (hK : ContDiff ℝ 1 K)
    (hx : ContDiff ℝ 1 x) (hT : 0 ≤ T)
    (hopt : IsMinOn (cvFunctional L K T)
      {y | y ∈ fixedEndpointC1Curves T (x 0) (x T) ∧
        cvFunctional G (fun _ ↦ 0) T y = cvFunctional G (fun _ ↦ 0) T x} x)
    (hregular : ∃ ξ : ℝ → E, ContDiff ℝ 1 ξ ∧ ξ 0 = 0 ∧ ξ T = 0 ∧
      firstVariation G (fun _ ↦ 0) T x ξ ≠ 0) :
    ∃ lam : ℝ, ∀ η : ℝ → E, ContDiff ℝ 1 η → η 0 = 0 → η T = 0 →
      firstVariation (fun t y v ↦ L t y v + lam * G t y v) K T x η = 0 := by
  obtain ⟨lam, hlam⟩ := _root_.IsoperimetricVariation.exists_common_isoperimetricMultiplier L G K T x
    hL hG hK hx hT hopt hregular
  refine ⟨lam, fun η hη hη₀ hηT ↦ ?_⟩
  rw [_root_.firstVariation_add_smul L G K lam T x η hL hG hx hη]
  exact hlam η hη hη₀ hηT

/-- Full isoperimetric Euler–Lagrange necessity on the finite horizon under C1
data. One extracted multiplier works for every differentiable endpoint-zero
direction, and the actual momentum derivative is derived within the horizon.
No momentum derivative, multiplier, or vanishing variation is assumed. -/
theorem _root_.IsoperimetricVariation.augmentedEulerLagrangeWithin_of_isoperimetric
    (L G : ℝ → E → E → ℝ) (K : E → ℝ) (T : ℝ) (x : ℝ → E)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L))
    (hG : ContDiff ℝ 1 (uncurryLagrangian G)) (hK : ContDiff ℝ 1 K)
    (hx : ContDiff ℝ 1 x) (hT : 0 < T)
    (hopt : IsMinOn (cvFunctional L K T)
      {y | y ∈ fixedEndpointC1Curves T (x 0) (x T) ∧
        cvFunctional G (fun _ ↦ 0) T y = cvFunctional G (fun _ ↦ 0) T x} x)
    (hregular : ∃ ξ : ℝ → E, ContDiff ℝ 1 ξ ∧ ξ 0 = 0 ∧ ξ T = 0 ∧
      firstVariation G (fun _ ↦ 0) T x ξ ≠ 0) :
    ∃ lam : ℝ,
      HasVanishingFirstVariation (fun t y v ↦ L t y v + lam * G t y v) K T x ∧
      ∀ t ∈ Icc 0 T,
        HasDerivWithinAt
          (fun s ↦ fderiv ℝ (fun v : E ↦ L s (x s) v + lam * G s (x s) v)
            (deriv x s))
          (fderiv ℝ (fun y : E ↦ L t y (deriv x t) + lam * G t y (deriv x t)) (x t))
          (Icc 0 T) t := by
  obtain ⟨lam, hlam⟩ := _root_.IsoperimetricVariation.exists_augmented_stationarity_of_isoperimetric
    L G K T x hL hG hK hx hT.le hopt hregular
  have hwithin := WeakEulerLagrange.eulerLagrange_hasDerivWithinAt_of_firstVariation_zero hT
    (_root_.contDiff_lagrangian_add_smul L G lam hL hG) hx hlam
  exact ⟨lam,
    hasVanishingFirstVariation_of_eulerLagrange_within _ K T x hT.le hwithin,
    hwithin⟩

/-- Full isoperimetric necessity in the exact existing project predicates.
Primitive C2 Lagrangians and reference data provide the two-sided momentum
regularity required by `eulerLagrange` at both endpoints. The single normal
multiplier and all first-variation and Euler–Lagrange equations are outputs. -/
theorem _root_.IsoperimetricVariation.augmentedEulerLagrange_of_isoperimetric
    (L G : ℝ → E → E → ℝ) (K : E → ℝ) (T : ℝ) (x : ℝ → E)
    (hL : ContDiff ℝ 2 (uncurryLagrangian L))
    (hG : ContDiff ℝ 2 (uncurryLagrangian G)) (hK : ContDiff ℝ 1 K)
    (hx : ContDiff ℝ 2 x) (hT : 0 < T)
    (hopt : IsMinOn (cvFunctional L K T)
      {y | y ∈ fixedEndpointC1Curves T (x 0) (x T) ∧
        cvFunctional G (fun _ ↦ 0) T y = cvFunctional G (fun _ ↦ 0) T x} x)
    (hregular : ∃ ξ : ℝ → E, ContDiff ℝ 1 ξ ∧ ξ 0 = 0 ∧ ξ T = 0 ∧
      firstVariation G (fun _ ↦ 0) T x ξ ≠ 0) :
    ∃ lam : ℝ,
      HasVanishingFirstVariation (fun t y v ↦ L t y v + lam * G t y v) K T x ∧
      eulerLagrange (fun t y v ↦ L t y v + lam * G t y v) T x := by
  have hL₁ : ContDiff ℝ 1 (uncurryLagrangian L) := hL.of_le (by norm_num)
  have hG₁ : ContDiff ℝ 1 (uncurryLagrangian G) := hG.of_le (by norm_num)
  have hx₁ : ContDiff ℝ 1 x := hx.of_le (by norm_num)
  obtain ⟨lam, hvan, _⟩ := _root_.IsoperimetricVariation.augmentedEulerLagrangeWithin_of_isoperimetric
    L G K T x hL₁ hG₁ hK hx₁ hT hopt hregular
  have hA : ContDiff ℝ 2
      (uncurryLagrangian (fun t y v ↦ L t y v + lam * G t y v)) :=
    hL.add (contDiff_const.mul hG)
  have hP := contDiff_momentumCovector_of_contDiff_two _ x hA hx
  refine ⟨lam, hvan, ?_⟩
  exact eulerLagrange_of_firstVariation_zero _ K _ T x hT hvan
    (fun t _ ↦ (hP.differentiable one_ne_zero t).hasDerivAt)
    hP.continuous hP.continuous_deriv_one
    (continuous_stateCovector _ x (hA.of_le (by norm_num)) hx₁)

/-- **Augmented Euler–Lagrange from an assumed augmented vanishing variation.**
Given a multiplier `lam` together with the *assumed* hypothesis that the augmented
Lagrangian `L + lam • G` has vanishing first variation over all endpoint-vanishing
perturbations, the augmented Lagrangian `L + lam • G` satisfies the Euler–Lagrange
equation.  The conclusion is the pointwise ODE for `L + lam • G`; the proof applies
the existing integration-by-parts / fundamental-lemma interface
`eulerLagrange_of_firstVariation_zero` to the actual augmented spatial and velocity
derivatives, with the momentum regularity and continuity checked explicitly.  The
derivation of the augmented vanishing variation from the two-parameter
multiplier identity is not assumed: it is carried out by
`_root_.IsoperimetricVariation.exists_augmented_stationarity_of_isoperimetric`
above, whose endpoint corollaries
`augmentedEulerLagrangeWithin_of_isoperimetric` and
`augmentedEulerLagrange_of_isoperimetric` are the unconditional isoperimetric
Euler–Lagrange necessity theorems.  This theorem is the generic conditional bridge
used when the augmented vanishing variation is supplied directly. -/
theorem _root_.IsoperimetricVariation.eulerLagrange_of_augmentedVanishing
    (L G : ℝ → E → E → ℝ) (K : E → ℝ) (Q : ℝ → E →L[ℝ] ℝ) (T : ℝ) (x : ℝ → E)
    (lam : ℝ) (hT : 0 < T)
    (hvan : HasVanishingFirstVariation (fun t y v ↦ L t y v + lam * G t y v) K T x)
    (hPderiv : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt (fun s ↦ fderiv ℝ (fun v : E ↦ L s (x s) v + lam * G s (x s) v)
        (deriv x s)) (Q t) t)
    (hPcont : Continuous (fun s ↦ fderiv ℝ (fun v : E ↦ L s (x s) v + lam * G s (x s) v)
      (deriv x s)))
    (hQcont : Continuous Q)
    (hScont : Continuous (fun t ↦ fderiv ℝ
      (fun y : E ↦ L t y (deriv x t) + lam * G t y (deriv x t)) (x t))) :
    eulerLagrange (fun t y v ↦ L t y v + lam * G t y v) T x :=
  eulerLagrange_of_firstVariation_zero _ K Q T x hT hvan hPderiv hPcont hQcont hScont
