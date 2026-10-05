/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.ConstrainedCoVMultipliers
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# K3 (partial): two-parameter strict differentiability and multiplier

This module provides two pieces of the Kirk–Medhin K3 obligation; it does **not**
complete K3.

The existing interface
`IsoperimetricVariation.exists_normal_multiplier_of_curve_family` extracts a
normal multiplier from a constrained minimum, but it takes the strict Fréchet
differentiability of the parameterized integral functionals as an input.  For an
endpoint-preserving reference curve `x`, test directions `η`, `ξ`, and the
two-parameter family `Γ(a,b)(t) = x t + a • η t + b • ξ t`, this module *derives*
that input: it differentiates the actual `cvFunctional` integrals under the
interval-integral sign, and the resulting derivative at `(0,0)` has components
equal to the explicit `firstVariation` expressions.  The multiplier interface is
then applicable to this genuinely feasible family.  The module therefore supplies
(a) the strict two-parameter differentiability and (b) the common multiplier on
the two-parameter family.

**Historical note.**  An earlier revision of this module recorded the lifting from
the two-parameter stationarity to `HasVanishingFirstVariation (fun t y v ↦ L t y v +
λ * G t y v)` over *all* smooth endpoint-vanishing directions as *the open
residual*, with the chain minimum → multiplier → augmented Euler–Lagrange *not
closed in this module*.  That residual is now closed by
`KirkMedhin.K3.exists_common_isoperimetricMultiplier` in
`K3IsoperimetricLift.lean`, which fixes one multiplier and derives the identity for
all C1 endpoint-zero directions (feeding
`KirkMedhin.K3.augmentedEulerLagrangeWithin_of_isoperimetric` and
`KirkMedhin.K3.augmentedEulerLagrange_of_isoperimetric`).  The theorem
`eulerLagrange_of_augmentedVanishing` below is retained as a partial building
block that consumes an augmented vanishing variation as an assumed hypothesis;
it is not the final K3 endpoint.

## Main results

* `hasStrictFDerivAt_parameterFunctional`: strict Fréchet differentiability of
  the two-parameter `cvFunctional` pair, with derivative the `firstVariation`.

* `isoperimetricMultiplier_exists`: a common multiplier extracted from a genuine
  constrained minimum.  Its scope is the two-parameter family: for each fixed
  pair `(η, ξ)`, the identity holds for all `p ∈ ℝ × ℝ`, i.e. on `span{η,ξ}`
  only; the value is `η`-independent given `ξ`, and there is no single invocation
  ranging over all test directions.

* `eulerLagrange_of_augmentedVanishing`: the Euler–Lagrange equation for
  `L + λ • G`, proved from an *assumed* augmented vanishing first variation (not
  derived here from the two-parameter multiplier identity).
-/

@[expose] public section

open MeasureTheory Set Filter Metric
open scoped Topology Interval

namespace KirkMedhin.K3

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The uncurried Lagrangian `(t, y, v) ↦ L t y v`, used to state joint `C¹`
regularity in the state and velocity variables. -/
noncomputable def uncurryLagrangian (L : ℝ → E → E → ℝ) : ℝ × E × E → ℝ :=
  fun q ↦ L q.1 q.2.1 q.2.2

/-- The two-parameter perturbation family `Γ(a,b)(t) = x t + (a • η t + b • ξ t)`. -/
noncomputable def perturbedCurve (x η ξ : ℝ → E) (p : ℝ × ℝ) : ℝ → E :=
  fun t ↦ x t + (p.1 • η t + p.2 • ξ t)

/-- The affine state curve `t ↦ x t + (a • η t + b • ξ t)` attached to a parameter `p`. -/
noncomputable def perturbedState (x η ξ : ℝ → E) (p : ℝ × ℝ) (t : ℝ) : E :=
  x t + (p.1 • η t + p.2 • ξ t)

/-- The affine velocity curve `t ↦ v t + (a • w t + b • z t)` attached to a parameter `p`. -/
noncomputable def perturbedVelocity (v w z : ℝ → E) (p : ℝ × ℝ) (t : ℝ) : E :=
  v t + (p.1 • w t + p.2 • z t)

/-- The continuous linear functional `p ↦ A * p.1 + B * p.2` on `ℝ × ℝ`. -/
noncomputable def parameterDerivative (A B : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  A • ContinuousLinearMap.fst ℝ ℝ ℝ + B • ContinuousLinearMap.snd ℝ ℝ ℝ

@[simp] theorem parameterDerivative_apply (A B : ℝ) (p : ℝ × ℝ) :
    parameterDerivative A B p = A * p.1 + B * p.2 := by
  simp [parameterDerivative]

theorem parameterDerivative_one_zero (A B : ℝ) :
    parameterDerivative A B (1, 0) = A := by
  simp [parameterDerivative]

theorem parameterDerivative_zero_one (A B : ℝ) :
    parameterDerivative A B (0, 1) = B := by
  simp [parameterDerivative]

/-- A continuous linear functional on `ℝ × ℝ` is determined by its values on the
coordinate basis vectors. -/
theorem parameterDerivative_ext (f : (ℝ × ℝ) →L[ℝ] ℝ) :
    f = parameterDerivative (f (1, 0)) (f (0, 1)) := by
  apply ContinuousLinearMap.ext
  intro p
  have hp : p = p.1 • (1, 0) + p.2 • (0, 1) := by
    ext <;> simp
  conv_lhs => rw [hp]
  rw [map_add, map_smul, map_smul, parameterDerivative_apply]
  ring

/-- The running part of the first variation `δJ(x; η)`, without the terminal term. -/
noncomputable def firstVariationIntegrand (L : ℝ → E → E → ℝ) (x η : ℝ → E) (t : ℝ) : ℝ :=
  (fderiv ℝ (fun y : E ↦ L t y (deriv x t)) (x t)) (η t)
    + (fderiv ℝ (fun v : E ↦ L t (x t) v) (deriv x t)) (deriv η t)

/-- `firstVariation` is the integral of `firstVariationIntegrand` plus the terminal
term. -/
theorem firstVariation_eq_integrand (L : ℝ → E → E → ℝ) (K : E → ℝ) (T : ℝ)
    (x η : ℝ → E) :
    firstVariation L K T x η =
      (∫ t in 0..T, firstVariationIntegrand L x η t) + (fderiv ℝ K (x T)) (η T) :=
  rfl

/-- The affine parameter velocity `q ↦ (q.1 • η t + q.2 • ξ t, q.1 • w t + q.2 • z t)`. -/
noncomputable def affineDeriv (η ξ w z : ℝ → E) (t : ℝ) : (ℝ × ℝ) →L[ℝ] E × E :=
  (((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (η t) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ξ t)).prod
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (w t) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (z t)))

@[simp] theorem affineDeriv_apply (η ξ w z : ℝ → E) (t : ℝ) (q : ℝ × ℝ) :
    affineDeriv η ξ w z t q = (q.1 • η t + q.2 • ξ t, q.1 • w t + q.2 • z t) := by
  simp [affineDeriv]

/-- The parameterized Lagrangian integrand. -/
noncomputable def perturbedIntegrand (L : ℝ → E → E → ℝ) (x v η w ξ z : ℝ → E)
    (p : ℝ × ℝ) (t : ℝ) : ℝ :=
  L t (perturbedState x η ξ p t) (perturbedVelocity v w z p t)

/-- The partial derivative in the parameter of `perturbedIntegrand`, obtained by
composing the `fderiv` of the Lagrangian with the affine parameter velocity. -/
noncomputable def perturbedIntegrandDeriv (L : ℝ → E → E → ℝ) (x v η w ξ z : ℝ → E)
    (p : ℝ × ℝ) (t : ℝ) : (ℝ × ℝ) →L[ℝ] ℝ :=
  (fderiv ℝ (fun q : E × E ↦ L t q.1 q.2)
      (perturbedState x η ξ p t, perturbedVelocity v w z p t)).comp
    (affineDeriv η ξ w z t)

/-- Joint differentiability of the uncurried Lagrangian gives differentiability of
its curried slice `(a, b) ↦ L t a b` at any point. -/
theorem differentiableAt_lagrangian_slice (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (t : ℝ) (a b : E) :
    DifferentiableAt ℝ (fun q : E × E ↦ L t q.1 q.2) (a, b) := by
  have hdiff : DifferentiableAt ℝ (uncurryLagrangian L) (t, a, b) :=
    hL.differentiable one_ne_zero _
  have hι : HasFDerivAt (fun q : E × E ↦ (t, q.1, q.2))
      ((0 : E × E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (E × E))) (a, b) :=
    (hasFDerivAt_const (x := (a, b)) t).prodMk (hasFDerivAt_id (a, b))
  have hcomp := hdiff.hasFDerivAt.comp (a, b) hι
  exact hcomp.differentiableAt

/-- The `fderiv` of the curried Lagrangian slice splits into the two partial Fréchet
derivatives in the state and velocity variables. -/
theorem fderiv_lagrangian_slice_apply (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (t : ℝ) (a b u v : E) :
    fderiv ℝ (fun q : E × E ↦ L t q.1 q.2) (a, b) (u, v) =
      (fderiv ℝ (fun y : E ↦ L t y b) a) u +
        (fderiv ℝ (fun w : E ↦ L t a w) b) v := by
  have hΦ : HasFDerivAt (fun q : E × E ↦ L t q.1 q.2)
      (fderiv ℝ (fun q : E × E ↦ L t q.1 q.2) (a, b)) (a, b) :=
    (differentiableAt_lagrangian_slice L hL t a b).hasFDerivAt
  have hinl : HasFDerivAt (fun y : E ↦ (y, b)) (ContinuousLinearMap.inl ℝ E E) a :=
    (hasFDerivAt_id a).prodMk (hasFDerivAt_const b a)
  have hinr : HasFDerivAt (fun w : E ↦ (a, w)) (ContinuousLinearMap.inr ℝ E E) b :=
    (hasFDerivAt_const a b).prodMk (hasFDerivAt_id b)
  have h1' : HasFDerivAt ((fun q : E × E ↦ L t q.1 q.2) ∘ (fun y : E ↦ (y, b)))
      ((fderiv ℝ (fun q : E × E ↦ L t q.1 q.2) (a, b)).comp
        (ContinuousLinearMap.inl ℝ E E)) a :=
    hΦ.comp a hinl
  have h1 : fderiv ℝ (fun y : E ↦ L t y b) a
      = (fderiv ℝ (fun q : E × E ↦ L t q.1 q.2) (a, b)).comp
          (ContinuousLinearMap.inl ℝ E E) := by
    change fderiv ℝ ((fun q : E × E ↦ L t q.1 q.2) ∘ (fun y : E ↦ (y, b))) a = _
    exact h1'.fderiv
  have h2' : HasFDerivAt ((fun q : E × E ↦ L t q.1 q.2) ∘ (fun w : E ↦ (a, w)))
      ((fderiv ℝ (fun q : E × E ↦ L t q.1 q.2) (a, b)).comp
        (ContinuousLinearMap.inr ℝ E E)) b :=
    hΦ.comp b hinr
  have h2 : fderiv ℝ (fun w : E ↦ L t a w) b
      = (fderiv ℝ (fun q : E × E ↦ L t q.1 q.2) (a, b)).comp
          (ContinuousLinearMap.inr ℝ E E) := by
    change fderiv ℝ ((fun q : E × E ↦ L t q.1 q.2) ∘ (fun w : E ↦ (a, w))) b = _
    exact h2'.fderiv
  rw [h1, h2]
  rw [show (u, v) = (u, (0 : E)) + ((0 : E), v) by simp, map_add]
  rfl

/-- The `fderiv` of the curried slice, written through the joint `fderiv` of the
uncurried Lagrangian. -/
theorem fderiv_lagrangian_slice_eq (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (t : ℝ) (a b : E) :
    fderiv ℝ (fun q : E × E ↦ L t q.1 q.2) (a, b) =
      (fderiv ℝ (uncurryLagrangian L) (t, a, b)).comp
        ((0 : (E × E) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (E × E))) := by
  have hdiff : DifferentiableAt ℝ (uncurryLagrangian L) (t, a, b) :=
    hL.differentiable one_ne_zero _
  have hι : HasFDerivAt (fun q : E × E ↦ (t, q.1, q.2))
      ((0 : E × E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (E × E))) (a, b) :=
    (hasFDerivAt_const (x := (a, b)) t).prodMk (hasFDerivAt_id (a, b))
  have hcomp := hdiff.hasFDerivAt.comp (a, b) hι
  change fderiv ℝ (uncurryLagrangian L ∘ fun q : E × E ↦ (t, q.1, q.2)) (a, b) = _
  exact hcomp.fderiv

/-- `ContinuousLinearMap.smulRight` is continuous in its scalar argument. -/
theorem continuous_smulRight (f : (ℝ × ℝ) →L[ℝ] ℝ) (g : ℝ → E) (hg : Continuous g) :
    Continuous (fun t : ℝ ↦ f.smulRight (g t)) := by
  have hbil : Continuous (fun p : ((ℝ × ℝ) →L[ℝ] ℝ) × E ↦
      (ContinuousLinearMap.smulRight p.1 p.2)) :=
    isBoundedBilinearMap_smulRight.continuous
  exact hbil.comp (continuous_const.prodMk hg)

/-- The affine parameter velocity `t ↦ affineDeriv η ξ w z t` is continuous when its
four defining curves are. -/
theorem continuous_affineDeriv (η ξ w z : ℝ → E) (hη : Continuous η) (hξ : Continuous ξ)
    (hw : Continuous w) (hz : Continuous z) :
    Continuous (fun t : ℝ ↦ affineDeriv η ξ w z t) := by
  have h1 := continuous_smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) η hη
  have h2 := continuous_smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ) ξ hξ
  have h3 := continuous_smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) w hw
  have h4 := continuous_smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ) z hz
  have h := (ContinuousLinearMap.prodL ℝ).continuous.comp ((h1.add h2).prodMk (h3.add h4))
  refine h.congr ?_
  intro t
  simp only [Function.comp_apply, ContinuousLinearMap.prodL_apply, Pi.add_apply,
    affineDeriv]

/-- The parameter derivative integrand, rewritten through the joint `fderiv` of the
uncurried Lagrangian. -/
theorem perturbedIntegrandDeriv_eq (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (x v η w ξ z : ℝ → E)
    (p : ℝ × ℝ) (t : ℝ) :
    perturbedIntegrandDeriv L x v η w ξ z p t =
      (fderiv ℝ (uncurryLagrangian L)
        (t, perturbedState x η ξ p t, perturbedVelocity v w z p t)).comp
        (((0 : (E × E) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (E × E))).comp
          (affineDeriv η ξ w z t)) := by
  rw [perturbedIntegrandDeriv, fderiv_lagrangian_slice_eq L hL t]
  rfl

/-- Joint continuity of the parameter derivative integrand `(p, t) ↦ D_p F(p, t)`. -/
theorem continuous_perturbedIntegrandDeriv (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L))
    (x v η w ξ z : ℝ → E)
    (hx : Continuous x) (hv : Continuous v) (hη : Continuous η) (hw : Continuous w)
    (hξ : Continuous ξ) (hz : Continuous z) :
    Continuous (fun q : (ℝ × ℝ) × ℝ ↦ perturbedIntegrandDeriv L x v η w ξ z q.1 q.2) := by
  have hstate : Continuous (fun q : (ℝ × ℝ) × ℝ ↦ perturbedState x η ξ q.1 q.2) := by
    unfold perturbedState
    fun_prop
  have hvel : Continuous (fun q : (ℝ × ℝ) × ℝ ↦ perturbedVelocity v w z q.1 q.2) := by
    unfold perturbedVelocity
    fun_prop
  have hA : Continuous (fun q : (ℝ × ℝ) × ℝ ↦
      fderiv ℝ (uncurryLagrangian L) (q.2, perturbedState x η ξ q.1 q.2,
        perturbedVelocity v w z q.1 q.2)) :=
    (hL.continuous_fderiv one_ne_zero).comp (continuous_snd.prodMk (hstate.prodMk hvel))
  have hB : Continuous (fun q : (ℝ × ℝ) × ℝ ↦
      ((0 : (E × E) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (E × E))).comp
        (affineDeriv η ξ w z q.2)) :=
    continuous_const.clm_comp ((continuous_affineDeriv η ξ w z hη hξ hw hz).comp continuous_snd)
  have h := hA.clm_comp hB
  refine h.congr ?_
  intro q
  exact (perturbedIntegrandDeriv_eq L hL x v η w ξ z q.1 q.2).symm

/-- The affine state curve is differentiable in the parameter, with derivative the
state component of `affineDeriv`. -/
theorem hasFDerivAt_perturbedState (x η ξ : ℝ → E) (p : ℝ × ℝ) (t : ℝ) :
    HasFDerivAt (fun p' : ℝ × ℝ ↦ perturbedState x η ξ p' t)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (η t) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ξ t)) p := by
  have hlin : HasFDerivAt (fun p' : ℝ × ℝ ↦ p'.1 • η t + p'.2 • ξ t)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (η t) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ξ t)) p :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (η t) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ξ t)).hasFDerivAt
  simpa [perturbedState] using hlin

/-- The affine velocity curve is differentiable in the parameter, with derivative the
velocity component of `affineDeriv`. -/
theorem hasFDerivAt_perturbedVelocity (v w z : ℝ → E) (p : ℝ × ℝ) (t : ℝ) :
    HasFDerivAt (fun p' : ℝ × ℝ ↦ perturbedVelocity v w z p' t)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (w t) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (z t)) p := by
  have hlin : HasFDerivAt (fun p' : ℝ × ℝ ↦ p'.1 • w t + p'.2 • z t)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (w t) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (z t)) p :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (w t) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (z t)).hasFDerivAt
  simpa [perturbedVelocity] using hlin

/-- Pointwise strict-differentiability input: for every `t`, the parameterized
Lagrangian integrand is differentiable in the parameter, with derivative
`perturbedIntegrandDeriv`. -/
theorem hasFDerivAt_perturbedIntegrand (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L))
    (x v η w ξ z : ℝ → E) (p : ℝ × ℝ) (t : ℝ) :
    HasFDerivAt (fun p' : ℝ × ℝ ↦ perturbedIntegrand L x v η w ξ z p' t)
      (perturbedIntegrandDeriv L x v η w ξ z p t) p := by
  have hstate : HasFDerivAt (fun p' : ℝ × ℝ ↦ perturbedState x η ξ p' t)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (η t) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ξ t)) p :=
    hasFDerivAt_perturbedState x η ξ p t
  have hvel : HasFDerivAt (fun p' : ℝ × ℝ ↦ perturbedVelocity v w z p' t)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (w t) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (z t)) p :=
    hasFDerivAt_perturbedVelocity v w z p t
  have hpair : HasFDerivAt
      (fun p' : ℝ × ℝ ↦
        (perturbedState x η ξ p' t, perturbedVelocity v w z p' t))
      (affineDeriv η ξ w z t) p := by
    simpa only [affineDeriv] using hstate.prodMk hvel
  have hslice := (differentiableAt_lagrangian_slice L hL t
    (perturbedState x η ξ p t) (perturbedVelocity v w z p t)).hasFDerivAt
  have hcomp := hslice.comp p hpair
  have hcomp' : HasFDerivAt (fun p' : ℝ × ℝ ↦
      L t (perturbedState x η ξ p' t) (perturbedVelocity v w z p' t))
      (perturbedIntegrandDeriv L x v η w ξ z p t) p := hcomp
  exact hcomp'

/-- The perturbed curve `t ↦ x t + (a • η t + b • ξ t)` is differentiable in `t` with
explicit derivative. -/
theorem hasDerivAt_perturbedCurve (x η ξ : ℝ → E)
    (hx : ∀ t, HasDerivAt x (deriv x t) t) (hη : ∀ t, HasDerivAt η (deriv η t) t)
    (hξ : ∀ t, HasDerivAt ξ (deriv ξ t) t) (p : ℝ × ℝ) (t : ℝ) :
    HasDerivAt (perturbedCurve x η ξ p)
      (deriv x t + (p.1 • deriv η t + p.2 • deriv ξ t)) t := by
  unfold perturbedCurve
  exact (hx t).add (((hη t).const_smul p.1).add ((hξ t).const_smul p.2))

/-- The built-in derivative of the perturbed curve is the affine velocity. -/
theorem deriv_perturbedCurve (x η ξ : ℝ → E)
    (hx : ∀ t, HasDerivAt x (deriv x t) t) (hη : ∀ t, HasDerivAt η (deriv η t) t)
    (hξ : ∀ t, HasDerivAt ξ (deriv ξ t) t) (p : ℝ × ℝ) (t : ℝ) :
    deriv (perturbedCurve x η ξ p) t =
      perturbedVelocity (deriv x) (deriv η) (deriv ξ) p t :=
  (hasDerivAt_perturbedCurve x η ξ hx hη hξ p t).deriv

/-- The first coordinate of the parameter derivative integrand is the state-direction
partial derivative plus the velocity-direction partial derivative. -/
theorem perturbedIntegrandDeriv_fst (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (x v η w ξ z : ℝ → E)
    (p : ℝ × ℝ) (t : ℝ) :
    perturbedIntegrandDeriv L x v η w ξ z p t (1, 0) =
      (fderiv ℝ (fun y : E ↦ L t y (perturbedVelocity v w z p t))
        (perturbedState x η ξ p t)) (η t)
      + (fderiv ℝ (fun u : E ↦ L t (perturbedState x η ξ p t) u)
        (perturbedVelocity v w z p t)) (w t) := by
  rw [perturbedIntegrandDeriv, ContinuousLinearMap.comp_apply, affineDeriv_apply]
  simp only [one_smul, zero_smul, add_zero]
  exact fderiv_lagrangian_slice_apply L hL t _ _ _ _

/-- The second coordinate of the parameter derivative integrand. -/
theorem perturbedIntegrandDeriv_snd (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (x v η w ξ z : ℝ → E)
    (p : ℝ × ℝ) (t : ℝ) :
    perturbedIntegrandDeriv L x v η w ξ z p t (0, 1) =
      (fderiv ℝ (fun y : E ↦ L t y (perturbedVelocity v w z p t))
        (perturbedState x η ξ p t)) (ξ t)
      + (fderiv ℝ (fun u : E ↦ L t (perturbedState x η ξ p t) u)
        (perturbedVelocity v w z p t)) (z t) := by
  rw [perturbedIntegrandDeriv, ContinuousLinearMap.comp_apply, affineDeriv_apply]
  simp only [one_smul, zero_smul, zero_add]
  exact fderiv_lagrangian_slice_apply L hL t _ _ _ _

/-- At `p = 0`, the first coordinate of the parameter derivative integrand is the
running first-variation integrand in the direction `η`. -/
theorem perturbedIntegrandDeriv_zero_fst (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (x η ξ : ℝ → E) (t : ℝ) :
    perturbedIntegrandDeriv L x (deriv x) η (deriv η) ξ (deriv ξ) 0 t (1, 0) =
      firstVariationIntegrand L x η t := by
  rw [perturbedIntegrandDeriv_fst L hL]
  simp [perturbedState, perturbedVelocity, firstVariationIntegrand]

/-- At `p = 0`, the second coordinate of the parameter derivative integrand is the
running first-variation integrand in the direction `ξ`. -/
theorem perturbedIntegrandDeriv_zero_snd (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (x η ξ : ℝ → E) (t : ℝ) :
    perturbedIntegrandDeriv L x (deriv x) η (deriv η) ξ (deriv ξ) 0 t (0, 1) =
      firstVariationIntegrand L x ξ t := by
  rw [perturbedIntegrandDeriv_snd L hL]
  simp [perturbedState, perturbedVelocity, firstVariationIntegrand]

/-- Joint continuity of the parameterized Lagrangian integrand `(p, t) ↦ F(p, t)`. -/
theorem continuous_perturbedIntegrand (L : ℝ → E → E → ℝ)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L))
    (x v η w ξ z : ℝ → E)
    (hx : Continuous x) (hv : Continuous v) (hη : Continuous η) (hw : Continuous w)
    (hξ : Continuous ξ) (hz : Continuous z) :
    Continuous (fun q : (ℝ × ℝ) × ℝ ↦ perturbedIntegrand L x v η w ξ z q.1 q.2) := by
  have hstate : Continuous (fun q : (ℝ × ℝ) × ℝ ↦ perturbedState x η ξ q.1 q.2) := by
    unfold perturbedState
    fun_prop
  have hvel : Continuous (fun q : (ℝ × ℝ) × ℝ ↦ perturbedVelocity v w z q.1 q.2) := by
    unfold perturbedVelocity
    fun_prop
  have h := hL.continuous.comp (continuous_snd.prodMk (hstate.prodMk hvel))
  change Continuous (fun q : (ℝ × ℝ) × ℝ ↦
    L q.2 (perturbedState x η ξ q.1 q.2) (perturbedVelocity v w z q.1 q.2)) at h
  exact h

/-- The parameter integral is differentiable in the parameter at every point of
`ball 0 1`, with derivative the integral of the parameter derivative integrand.
The dominating bound comes from compactness. -/
theorem hasFDerivAt_perturbedIntegral_of_mem
    (L : ℝ → E → E → ℝ) (hL : ContDiff ℝ 1 (uncurryLagrangian L))
    (x v η w ξ z : ℝ → E)
    (hx : Continuous x) (hv : Continuous v) (hη : Continuous η) (hw : Continuous w)
    (hξ : Continuous ξ) (hz : Continuous z) (T : ℝ) (hT : 0 ≤ T)
    {B : ℝ} (hB : ∀ p ∈ closedBall (0 : ℝ × ℝ) 1, ∀ t ∈ Icc 0 T,
      ‖perturbedIntegrandDeriv L x v η w ξ z p t‖ ≤ B)
    {p : ℝ × ℝ} (hp : p ∈ ball (0 : ℝ × ℝ) 1) :
    HasFDerivAt (fun p' : ℝ × ℝ ↦ ∫ t in 0..T, perturbedIntegrand L x v η w ξ z p' t)
      (∫ t in 0..T, perturbedIntegrandDeriv L x v η w ξ z p t) p := by
  have hcontF := continuous_perturbedIntegrand L hL x v η w ξ z hx hv hη hw hξ hz
  have hcontF' := continuous_perturbedIntegrandDeriv L hL x v η w ξ z hx hv hη hw hξ hz
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume) (s := ball 0 1)
    (bound := fun _ : ℝ ↦ B) (Metric.isOpen_ball.mem_nhds hp) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards with p'
    exact (hcontF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hcontF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 T
  · exact (hcontF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [Set.uIoc_of_le hT] at ht
    intro p' hp'
    exact hB p' (ball_subset_closedBall hp') t (Set.Ioc_subset_Icc_self ht)
  · exact intervalIntegrable_const
  · filter_upwards with t
    intro p' _
    exact hasFDerivAt_perturbedIntegrand L hL x v η w ξ z p' t

/-- **Strict differentiability of the parameterized interval integral.**  The two
parameter integral `p ↦ ∫ t in 0..T, L t (x t + p.1 • η t + p.2 • ξ t)
(v t + p.1 • w t + p.2 • z t)` is strictly Fréchet differentiable at `0` with
derivative the integral of the explicit parameter derivative. -/
theorem hasStrictFDerivAt_perturbedIntegral
    (L : ℝ → E → E → ℝ) (hL : ContDiff ℝ 1 (uncurryLagrangian L))
    (x v η w ξ z : ℝ → E)
    (hx : Continuous x) (hv : Continuous v) (hη : Continuous η) (hw : Continuous w)
    (hξ : Continuous ξ) (hz : Continuous z) (T : ℝ) (hT : 0 ≤ T) :
    HasStrictFDerivAt (fun p : ℝ × ℝ ↦
        ∫ t in 0..T, perturbedIntegrand L x v η w ξ z p t)
      (∫ t in 0..T, perturbedIntegrandDeriv L x v η w ξ z 0 t) 0 := by
  have hcontF' := continuous_perturbedIntegrandDeriv L hL x v η w ξ z hx hv hη hw hξ hz
  obtain ⟨B, hB⟩ := (isCompact_closedBall (x := (0 : ℝ × ℝ)) (r := 1)).prod
      isCompact_Icc |>.exists_bound_of_continuousOn hcontF'.norm.continuousOn
  have hB' : ∀ p ∈ closedBall (0 : ℝ × ℝ) 1, ∀ t ∈ Icc 0 T,
      ‖perturbedIntegrandDeriv L x v η w ξ z p t‖ ≤ B := by
    intro p hp t ht
    simpa using hB (p, t) ⟨hp, ht⟩
  refine hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt (𝕜 := ℝ)
    (f := fun p : ℝ × ℝ ↦ ∫ t in 0..T, perturbedIntegrand L x v η w ξ z p t)
    (f' := fun p : ℝ × ℝ ↦ ∫ t in 0..T, perturbedIntegrandDeriv L x v η w ξ z p t)
    (x := 0) ?_ ?_
  · filter_upwards [Metric.ball_mem_nhds (0 : ℝ × ℝ) one_pos] with p hp
    exact hasFDerivAt_perturbedIntegral_of_mem L hL x v η w ξ z hx hv hη hw hξ hz T hT hB' hp
  · have hcont_set : ContinuousAt (fun p : ℝ × ℝ ↦
        ∫ t in Set.Ioc 0 T, perturbedIntegrandDeriv L x v η w ξ z p t) 0 := by
      refine continuousAt_of_dominated (μ := volume.restrict (Set.Ioc 0 T))
        (bound := fun _ : ℝ ↦ B) ?_ ?_ ?_ ?_
      · filter_upwards with p
        exact (hcontF'.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
      · filter_upwards [Metric.ball_mem_nhds (0 : ℝ × ℝ) one_pos] with p hp
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hB' p (ball_subset_closedBall hp) t (Set.Ioc_subset_Icc_self ht)
      · show Integrable (fun _ : ℝ ↦ B) (volume.restrict (Set.Ioc 0 T))
        exact integrable_const B
      · filter_upwards with t
        exact (hcontF'.comp (continuous_id.prodMk continuous_const)).continuousAt
    exact hcont_set.congr (Filter.Eventually.of_forall (fun _ ↦
      (intervalIntegral.integral_of_le hT).symm))

/-- **Strict differentiability of the perturbed `cvFunctional`.**  For a `C¹`
Lagrangian `L`, a `C¹` terminal cost `K`, and `C¹` reference and test curves, the
map `p ↦ cvFunctional L K T (Γ p)` is strictly Fréchet differentiable at `0`, with
derivative the continuous linear functional whose coordinate values are the
explicit first variations in `η` and `ξ`. -/
theorem hasStrictFDerivAt_cvFunctional_perturbed
    (L : ℝ → E → E → ℝ) (K : E → ℝ) (T : ℝ) (x η ξ : ℝ → E)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (hK : ContDiff ℝ 1 K)
    (hx : ContDiff ℝ 1 x) (hη : ContDiff ℝ 1 η) (hξ : ContDiff ℝ 1 ξ) (hT : 0 ≤ T) :
    HasStrictFDerivAt (fun p : ℝ × ℝ ↦ cvFunctional L K T (perturbedCurve x η ξ p))
      (parameterDerivative (firstVariation L K T x η) (firstVariation L K T x ξ)) 0 := by
  have hdx' : ∀ t, HasDerivAt x (deriv x t) t :=
    fun t ↦ (hx.differentiable one_ne_zero t).hasDerivAt
  have hdη' : ∀ t, HasDerivAt η (deriv η t) t :=
    fun t ↦ (hη.differentiable one_ne_zero t).hasDerivAt
  have hdξ' : ∀ t, HasDerivAt ξ (deriv ξ t) t :=
    fun t ↦ (hξ.differentiable one_ne_zero t).hasDerivAt
  have hdx : Continuous (deriv x) := hx.continuous_deriv_one
  have hdη : Continuous (deriv η) := hη.continuous_deriv_one
  have hdξ : Continuous (deriv ξ) := hξ.continuous_deriv_one
  have hcontDeriv := continuous_perturbedIntegrandDeriv L hL x (deriv x) η (deriv η)
    ξ (deriv ξ) hx.continuous hdx hη.continuous hdη hξ.continuous hdξ
  have hint : HasStrictFDerivAt
      (fun p : ℝ × ℝ ↦ ∫ t in 0..T,
        perturbedIntegrand L x (deriv x) η (deriv η) ξ (deriv ξ) p t)
      (∫ t in 0..T,
        perturbedIntegrandDeriv L x (deriv x) η (deriv η) ξ (deriv ξ) 0 t) 0 :=
    hasStrictFDerivAt_perturbedIntegral L hL x (deriv x) η (deriv η) ξ (deriv ξ)
      hx.continuous hdx hη.continuous hdη hξ.continuous hdξ T hT
  have hterm : HasStrictFDerivAt (fun p : ℝ × ℝ ↦ K (perturbedState x η ξ p T))
      ((fderiv ℝ K (x T)).comp
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (η T) +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ξ T))) 0 := by
    have hlin : HasStrictFDerivAt
        (fun p : ℝ × ℝ ↦ x T +
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (η T) +
            (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ξ T)) p)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (η T) +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ξ T)) 0 := by
      have h := (hasStrictFDerivAt_const (x T) 0).add
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (η T) +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ξ T)).hasStrictFDerivAt
      convert h using 1; simp
    have hKstrict := hK.hasStrictFDerivAt (x := x T) one_ne_zero
    have hK' : HasStrictFDerivAt K (fderiv ℝ K (x T))
        ((fun p : ℝ × ℝ ↦ x T +
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (η T) +
            (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ξ T)) p) 0) := by
      simpa using hKstrict
    have hcomp := hK'.comp 0 hlin
    simpa [Function.comp_apply, perturbedState,
      ContinuousLinearMap.smulRight_apply] using hcomp
  have hadd : HasStrictFDerivAt (fun p : ℝ × ℝ ↦
        (∫ t in 0..T,
          perturbedIntegrand L x (deriv x) η (deriv η) ξ (deriv ξ) p t)
          + K (perturbedState x η ξ p T))
      ((∫ t in 0..T,
        perturbedIntegrandDeriv L x (deriv x) η (deriv η) ξ (deriv ξ) 0 t) +
        (fderiv ℝ K (x T)).comp
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (η T) +
            (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ξ T))) 0 :=
    hint.add hterm
  have hfun : (fun p : ℝ × ℝ ↦
        (∫ t in 0..T,
          perturbedIntegrand L x (deriv x) η (deriv η) ξ (deriv ξ) p t)
          + K (perturbedState x η ξ p T))
      = fun p : ℝ × ℝ ↦ cvFunctional L K T (perturbedCurve x η ξ p) := by
    funext p
    simp only [cvFunctional, perturbedIntegrand]
    congr 1
    · apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [deriv_perturbedCurve x η ξ hdx' hdη' hdξ' p t]
      simp only [perturbedState, perturbedCurve]
  rw [hfun] at hadd
  have hJint_fst : (∫ t in 0..T,
        perturbedIntegrandDeriv L x (deriv x) η (deriv η) ξ (deriv ξ) 0 t) (1, 0)
      = ∫ t in 0..T, firstVariationIntegrand L x η t := by
    rw [ContinuousLinearMap.intervalIntegral_apply]
    · apply intervalIntegral.integral_congr
      intro t _
      exact perturbedIntegrandDeriv_zero_fst L hL x η ξ t
    · exact (hcontDeriv.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 T
  have hJint_snd : (∫ t in 0..T,
        perturbedIntegrandDeriv L x (deriv x) η (deriv η) ξ (deriv ξ) 0 t) (0, 1)
      = ∫ t in 0..T, firstVariationIntegrand L x ξ t := by
    rw [ContinuousLinearMap.intervalIntegral_apply]
    · apply intervalIntegral.integral_congr
      intro t _
      exact perturbedIntegrandDeriv_zero_snd L hL x η ξ t
    · exact (hcontDeriv.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 T
  have hKter_fst : ((fderiv ℝ K (x T)).comp
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (η T) +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ξ T))) (1, 0)
      = (fderiv ℝ K (x T)) (η T) := by
    simp [ContinuousLinearMap.smulRight_apply]
  have hKter_snd : ((fderiv ℝ K (x T)).comp
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (η T) +
          (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ξ T))) (0, 1)
      = (fderiv ℝ K (x T)) (ξ T) := by
    simp [ContinuousLinearMap.smulRight_apply]
  have hfst : ((∫ t in 0..T,
        perturbedIntegrandDeriv L x (deriv x) η (deriv η) ξ (deriv ξ) 0 t) +
        (fderiv ℝ K (x T)).comp
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (η T) +
            (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ξ T))) (1, 0)
      = firstVariation L K T x η := by
    rw [add_apply, hJint_fst, hKter_fst, firstVariation_eq_integrand]
  have hsnd : ((∫ t in 0..T,
        perturbedIntegrandDeriv L x (deriv x) η (deriv η) ξ (deriv ξ) 0 t) +
        (fderiv ℝ K (x T)).comp
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (η T) +
            (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ξ T))) (0, 1)
      = firstVariation L K T x ξ := by
    rw [add_apply, hJint_snd, hKter_snd, firstVariation_eq_integrand]
  have hderiv_eq : (∫ t in 0..T,
        perturbedIntegrandDeriv L x (deriv x) η (deriv η) ξ (deriv ξ) 0 t) +
        (fderiv ℝ K (x T)).comp
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (η T) +
            (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ξ T))
      = parameterDerivative (firstVariation L K T x η) (firstVariation L K T x ξ) := by
    rw [parameterDerivative_ext ((∫ t in 0..T,
        perturbedIntegrandDeriv L x (deriv x) η (deriv η) ξ (deriv ξ) 0 t) +
        (fderiv ℝ K (x T)).comp
          ((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (η T) +
            (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ξ T))),
      hfst, hsnd]
  rw [hderiv_eq] at hadd
  exact hadd

/-- **Strict Fréchet differentiability of the two-parameter `cvFunctional` pair.**
For actual `C¹` Lagrangians `L`, `G`, a `C¹` terminal cost `K`, and `C¹` reference and
test curves, the map `(a, b) ↦ (J(a,b), C(a,b))` with
`J(a,b) = cvFunctional L K T (Γ(a,b))`,
`C(a,b) = cvFunctional G (fun _ ↦ 0) T (Γ(a,b))`, and
`Γ(a,b)(t) = x t + (a • η t + b • ξ t)` is strictly Fréchet differentiable at
`(0,0)`.  Its derivative is the continuous linear map whose first component is the
first variation of `L` and whose second component is the first variation of `G`
(with zero terminal cost), evaluated in the directions `η` and `ξ`. -/
theorem hasStrictFDerivAt_parameterFunctional
    (L G : ℝ → E → E → ℝ) (K : E → ℝ) (T : ℝ) (x η ξ : ℝ → E)
    (hL : ContDiff ℝ 1 (uncurryLagrangian L)) (hG : ContDiff ℝ 1 (uncurryLagrangian G))
    (hK : ContDiff ℝ 1 K)
    (hx : ContDiff ℝ 1 x) (hη : ContDiff ℝ 1 η) (hξ : ContDiff ℝ 1 ξ) (hT : 0 ≤ T) :
    HasStrictFDerivAt
      (fun p : ℝ × ℝ ↦
        (cvFunctional L K T (perturbedCurve x η ξ p),
         cvFunctional G (fun _ ↦ 0) T (perturbedCurve x η ξ p)))
      ((parameterDerivative (firstVariation L K T x η) (firstVariation L K T x ξ)).prod
        (parameterDerivative (firstVariation G (fun _ ↦ 0) T x η)
          (firstVariation G (fun _ ↦ 0) T x ξ)))
      (0, 0) := by
  have hJ := hasStrictFDerivAt_cvFunctional_perturbed L K T x η ξ hL hK hx hη hξ hT
  have hC := hasStrictFDerivAt_cvFunctional_perturbed G (fun _ ↦ 0) T x η ξ hG
    contDiff_const hx hη hξ hT
  exact hJ.prodMk hC

/-- The two-parameter family at `(0,0)` is the reference curve. -/
theorem perturbedCurve_zero (x η ξ : ℝ → E) : perturbedCurve x η ξ 0 = x := by
  funext t
  simp [perturbedCurve]

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
theorem isoperimetricMultiplier_exists
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

/-- **Augmented Euler–Lagrange from an assumed augmented vanishing variation.**
Given a multiplier `lam` together with the *assumed* hypothesis that the augmented
Lagrangian `L + lam • G` has vanishing first variation over all endpoint-vanishing
perturbations, the augmented Lagrangian `L + lam • G` satisfies the Euler–Lagrange
equation.  The conclusion is the pointwise ODE for `L + lam • G`; the proof applies
the existing integration-by-parts / fundamental-lemma interface
`eulerLagrange_of_firstVariation_zero` to the actual augmented spatial and velocity
derivatives, with the momentum regularity and continuity checked explicitly.  This
does **not** derive the augmented vanishing variation from the two-parameter
multiplier identity of `isoperimetricMultiplier_exists`; that lifting is the open
residual. -/
theorem eulerLagrange_of_augmentedVanishing
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

end KirkMedhin.K3

#check @KirkMedhin.K3.hasStrictFDerivAt_parameterFunctional
#check @KirkMedhin.K3.isoperimetricMultiplier_exists
#check @KirkMedhin.K3.eulerLagrange_of_augmentedVanishing
