/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.K3IsoperimetricEulerLagrange
public import DynamicalSystems.OptimalControl.ContinuousTime.K3MomentumRegularity
public import DynamicalSystems.OptimalControl.ContinuousTime.K3DifferentiableExtension
public import DynamicalSystems.OptimalControl.ContinuousTime.WeakEulerLagrange

/-!
# Isoperimetric stationarity over all endpoint-preserving directions

The same normal multiplier is extracted from genuine constrained optimality for
every continuously differentiable test direction. The admissible two-parameter
families are constructed inside an explicit fixed-endpoint curve class; their
strict derivatives come from the actual integral differentiation theorem.

The final horizon theorem derives momentum differentiability and the exact
existing vanishing-first-variation predicate, including all differentiable test
directions. Its endpoint derivatives are within the horizon. A C2 corollary
supplies the ordinary two-sided endpoint derivatives required by the existing
`eulerLagrange` predicate, without assuming the Euler–Lagrange equations or an
unknown momentum derivative.
-/

@[expose] public section

open Set MeasureTheory
open scoped Interval

namespace KirkMedhin.K3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Globally continuously differentiable curves with the specified endpoint values. -/
def fixedEndpointC1Curves (T : ℝ) (a b : E) : Set (ℝ → E) :=
  {y | ContDiff ℝ 1 y ∧ y 0 = a ∧ y T = b}

/-- Affine perturbation preserves continuous differentiability. -/
theorem contDiff_perturbedCurve (x η ξ : ℝ → E)
    (hx : ContDiff ℝ 1 x) (hη : ContDiff ℝ 1 η) (hξ : ContDiff ℝ 1 ξ)
    (p : ℝ × ℝ) : ContDiff ℝ 1 (perturbedCurve x η ξ p) := by
  exact hx.add ((hη.const_smul p.1).add (hξ.const_smul p.2))

/-- Both coordinates of an endpoint-vanishing perturbation preserve the actual
fixed endpoints for every parameter, with no constraint value assumed. -/
theorem perturbedCurve_mem_fixedEndpointC1Curves (T : ℝ) (x η ξ : ℝ → E)
    (hx : ContDiff ℝ 1 x) (hη : ContDiff ℝ 1 η) (hξ : ContDiff ℝ 1 ξ)
    (hη₀ : η 0 = 0) (hηT : η T = 0) (hξ₀ : ξ 0 = 0) (hξT : ξ T = 0)
    (p : ℝ × ℝ) :
    perturbedCurve x η ξ p ∈ fixedEndpointC1Curves T (x 0) (x T) := by
  refine ⟨contDiff_perturbedCurve x η ξ hx hη hξ p, ?_, ?_⟩
  · simp only [perturbedCurve, hη₀, hξ₀, smul_zero, add_zero]
  · simp only [perturbedCurve, hηT, hξT, smul_zero, add_zero]

/-- One explicit multiplier annihilates the cost/constraint combination for
every endpoint-preserving C1 direction. The nonzero constraint direction is
fixed before quantifying over the arbitrary test direction. -/
theorem exists_common_isoperimetricMultiplier
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
  obtain ⟨lam, hlam, hstationary⟩ := isoperimetricMultiplier_exists L G K T
    (fixedEndpointC1Curves T (x 0) (x T)) x η ξ hL hG hK hx hη hξ hT
    (perturbedCurve_mem_fixedEndpointC1Curves T x η ξ hx hη hξ hη₀ hηT hξ₀ hξT)
    hopt hξreg
  simpa only [parameterDerivative_one_zero, hlam] using hstationary (1, 0)

/-- The joint C1 property is preserved by the actual augmented Lagrangian. -/
theorem contDiff_augmentedLagrangian (L G : ℝ → E → E → ℝ) (lam : ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L))
    (hG : ContDiff ℝ 1 (uncurryLagrangian G)) :
    ContDiff ℝ 1 (uncurryLagrangian (fun t y v ↦ L t y v + lam * G t y v)) :=
  hL.add (contDiff_const.mul hG)

/-- The actual augmented first-variation density is the linear combination of
the two original densities, by differentiating the actual Lagrangians. -/
theorem firstVariationIntegrand_augmented (L G : ℝ → E → E → ℝ) (lam : ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L))
    (hG : ContDiff ℝ 1 (uncurryLagrangian G)) (x η : ℝ → E) (t : ℝ) :
    firstVariationIntegrand (fun t y v ↦ L t y v + lam * G t y v) x η t =
      firstVariationIntegrand L x η t + lam * firstVariationIntegrand G x η t := by
  have hA := contDiff_augmentedLagrangian L G lam hL hG
  have hLd := differentiableAt_lagrangian_slice L hL t (x t) (deriv x t)
  have hGd := differentiableAt_lagrangian_slice G hG t (x t) (deriv x t)
  unfold firstVariationIntegrand
  rw [← fderiv_lagrangian_slice_apply _ hA, ← fderiv_lagrangian_slice_apply L hL,
    ← fderiv_lagrangian_slice_apply G hG]
  rw [fderiv_fun_add hLd (hGd.const_mul lam), fderiv_const_mul hGd lam]
  simp only [add_apply, smul_apply, smul_eq_mul]

/-- The actual first variation is linear in the running Lagrangian. Integrability
of both original densities is proved from primitive C1 hypotheses. -/
theorem firstVariation_augmented (L G : ℝ → E → E → ℝ) (K : E → ℝ)
    (lam T : ℝ) (x η : ℝ → E)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L))
    (hG : ContDiff ℝ 1 (uncurryLagrangian G))
    (hx : ContDiff ℝ 1 x) (hη : ContDiff ℝ 1 η) :
    firstVariation (fun t y v ↦ L t y v + lam * G t y v) K T x η =
      firstVariation L K T x η + lam * firstVariation G (fun _ ↦ 0) T x η := by
  have hLi : IntervalIntegrable (firstVariationIntegrand L x η) volume 0 T :=
    (continuous_firstVariationIntegrand L x η hL hx hη).intervalIntegrable 0 T
  have hGi : IntervalIntegrable (firstVariationIntegrand G x η) volume 0 T :=
    (continuous_firstVariationIntegrand G x η hG hx hη).intervalIntegrable 0 T
  simp only [firstVariation_eq_integrand,
    firstVariationIntegrand_augmented L G lam hL hG]
  rw [intervalIntegral.integral_add hLi (hGi.const_mul lam),
    intervalIntegral.integral_const_mul]
  rw [(hasFDerivAt_const (0 : ℝ) (x T)).fderiv]
  simp only [zero_apply, add_zero]
  ring

/-- Actual constrained optimality produces a single multiplier and augmented
stationarity for every C1 endpoint-preserving direction. No first-variation
identity or multiplier is supplied as an input. -/
theorem exists_augmented_stationarity_of_isoperimetric
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
  obtain ⟨lam, hlam⟩ := exists_common_isoperimetricMultiplier L G K T x
    hL hG hK hx hT hopt hregular
  refine ⟨lam, fun η hη hη₀ hηT ↦ ?_⟩
  rw [firstVariation_augmented L G K lam T x η hL hG hx hη]
  exact hlam η hη hη₀ hηT

/-- Full isoperimetric Euler–Lagrange necessity on the finite horizon under C1
data. One extracted multiplier works for every differentiable endpoint-zero
direction, and the actual momentum derivative is derived within the horizon.
No momentum derivative, multiplier, or vanishing variation is assumed. -/
theorem augmentedEulerLagrangeWithin_of_isoperimetric
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
  obtain ⟨lam, hlam⟩ := exists_augmented_stationarity_of_isoperimetric
    L G K T x hL hG hK hx hT.le hopt hregular
  have hwithin := WeakCoV.eulerLagrange_hasDerivWithinAt_of_firstVariation_zero hT
    (contDiff_augmentedLagrangian L G lam hL hG) hx hlam
  exact ⟨lam,
    hasVanishingFirstVariation_of_eulerLagrange_within _ K T x hT.le hwithin,
    hwithin⟩

/-- Full isoperimetric necessity in the exact existing project predicates.
Primitive C2 Lagrangians and reference data provide the two-sided momentum
regularity required by `eulerLagrange` at both endpoints. The single normal
multiplier and all first-variation and Euler–Lagrange equations are outputs. -/
theorem augmentedEulerLagrange_of_isoperimetric
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
  obtain ⟨lam, hvan, _⟩ := augmentedEulerLagrangeWithin_of_isoperimetric
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

end KirkMedhin.K3
