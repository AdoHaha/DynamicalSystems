/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# A spatial Fermat proof of the smooth HJB adjoint equation

At a fixed time, freeze the selected control. The HJB residual is nonnegative
at every nearby state and vanishes at the state of the selected trajectory.
Fermat's theorem therefore makes its spatial derivative zero. The product
rule and symmetry of the joint Hessian identify that derivative with the
covector adjoint equation.

The control is never differentiated. No smooth minimizing selector or
differentiation of an infimum is needed. The residual hypotheses contain the
HJB inequality and its attained value, not the adjoint conclusion.

The first theorem isolates a genuine second-order jet calculation. The second
specializes that calculation to a C² value function and the actual spatial
Fréchet derivative. Both are pointwise in time and use covectors; the existing
library's Riesz map converts the result to its vector costate predicate.

Classical background: Kirk, Optimal Control Theory, Dover 2004, §7.1;
Berkovitz and Medhin, Nonlinear Optimal Control Theory, CRC 2012, §6.2.
-/

@[expose] public section

open Filter
open scoped Topology

namespace HJBResidualBridge

variable {X : Type*} [NormedAddCommGroup X]

section Normed

variable [NormedSpace ℝ X]

/-- Inclusion of a spatial direction into joint time-state space. -/
def spatialInclusion : X →L[ℝ] (ℝ × X) :=
  (0 : X →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ X)

@[simp] theorem spatialInclusion_apply (h : X) :
    spatialInclusion h = (0, h) := rfl

omit [NormedSpace ℝ X] in
/-- A nonnegative HJB residual attaining zero has a spatial local minimum. -/
theorem isLocalMin_of_nonneg_of_eq_zero {R : X → ℝ} {z : X}
    (hnonneg : ∀ᶠ y in 𝓝 z, 0 ≤ R y) (hzero : R z = 0) :
    IsLocalMin R z := by
  change ∀ᶠ y in 𝓝 z, R z ≤ R y
  simpa only [hzero] using hnonneg

/-- **The HJB residual gives the covector adjoint equation.**

`J` is a differentiable field of covectors on joint time-state space, with
symmetric derivative `B`. For an actual value function it is `D W` and `B`
is its Hessian. The fixed-control dynamics `f` and running cost `L` have
derivatives `A` and `ell` in the state variable.

Only the scalar residual `L y + J (t,y) (1,f y)` is minimized. Its derivative
vanishes by Fermat; Hessian symmetry then converts it to the derivative of
`s ↦ J (s,x s)` restricted to spatial directions.
-/
theorem hjb_covector_adjoint_of_jet
    (J : (ℝ × X) → (ℝ × X) →L[ℝ] ℝ)
    (B : (ℝ × X) →L[ℝ] (ℝ × X) →L[ℝ] ℝ)
    (x : ℝ → X) (t : ℝ) (f : X → X) (L : X → ℝ)
    (A : X →L[ℝ] X) (ell : X →L[ℝ] ℝ)
    (hJ : HasFDerivAt J B (t, x t))
    (hB : ∀ a b : ℝ × X, B a b = B b a)
    (hx : HasDerivAt x (f (x t)) t)
    (hf : HasFDerivAt f A (x t))
    (hL : HasFDerivAt L ell (x t))
    (hnonneg : ∀ᶠ y in 𝓝 (x t), 0 ≤ L y + J (t, y) (1, f y))
    (hzero : L (x t) + J (t, x t) (1, f (x t)) = 0) :
    HasDerivAt (fun s ↦ (J (s, x s)).comp spatialInclusion)
      (-ell - ((J (t, x t)).comp spatialInclusion).comp A) t := by
  have hslice : HasFDerivAt (fun y : X ↦ (t, y)) spatialInclusion (x t) :=
    (hasFDerivAt_const t (x t)).prodMk (hasFDerivAt_id (x t))
  have hJspace : HasFDerivAt (fun y : X ↦ J (t, y))
      (B.comp spatialInclusion) (x t) := hJ.comp (x t) hslice
  have hvelocity : HasFDerivAt (fun y : X ↦ ((1 : ℝ), f y))
      ((0 : X →L[ℝ] ℝ).prod A) (x t) :=
    (hasFDerivAt_const (1 : ℝ) (x t)).prodMk hf
  have hresidual := hL.add (hJspace.clm_apply hvelocity)
  have hminimum := isLocalMin_of_nonneg_of_eq_zero hnonneg hzero
  have hstationary := hminimum.hasFDerivAt_eq_zero hresidual
  have hchain : HasDerivAt (fun s ↦ J (s, x s)) (B (1, f (x t))) t :=
    hJ.comp_hasDerivAt t ((hasDerivAt_id' t).prodMk hx)
  have hrestricted := hchain.clm_comp (hasDerivAt_const t spatialInclusion)
  have hderivative : (B (1, f (x t))).comp spatialInclusion =
      -ell - ((J (t, x t)).comp spatialInclusion).comp A := by
    ext h
    have heval := congrArg (fun q : X →L[ℝ] ℝ ↦ q h) hstationary
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.prod_apply,
      zero_apply, spatialInclusion_apply] at heval
    simp only [ContinuousLinearMap.comp_apply, sub_apply,
      neg_apply, spatialInclusion_apply]
    rw [hB (1, f (x t)) (0, h)]
    linarith
  simpa only [ContinuousLinearMap.comp_zero, add_zero, hderivative] using hrestricted

/-- The restriction of the joint derivative is the actual spatial derivative. -/
theorem jointDerivative_restrict_eq_spatial
    (W : (ℝ × X) → ℝ) (s : ℝ) (z : X)
    (hW : DifferentiableAt ℝ W (s, z)) :
    (fderiv ℝ W (s, z)).comp spatialInclusion =
      fderiv ℝ (fun y ↦ W (s, y)) z := by
  have hslice : HasFDerivAt (fun y : X ↦ (s, y)) spatialInclusion z :=
    (hasFDerivAt_const s z).prodMk (hasFDerivAt_id z)
  exact (hW.hasFDerivAt.comp z hslice).fderiv.symm

/-- **A C² HJB value function satisfies the adjoint equation.**

Freeze a selected control at time `t` in `f` and `L`. The hypotheses are the
ordinary joint smoothness of `W`, the state equation, state derivatives of
`f` and `L`, and an attained HJB residual. The conclusion derives the time
derivative of the actual spatial value-function covector.
-/
theorem hjb_value_covector_adjoint
    (W : (ℝ × X) → ℝ) (x : ℝ → X) (t : ℝ)
    (f : X → X) (L : X → ℝ)
    (A : X →L[ℝ] X) (ell : X →L[ℝ] ℝ)
    (hW : ContDiff ℝ 2 W)
    (hx : HasDerivAt x (f (x t)) t)
    (hf : HasFDerivAt f A (x t))
    (hL : HasFDerivAt L ell (x t))
    (hnonneg : ∀ᶠ y in 𝓝 (x t),
      0 ≤ L y + fderiv ℝ W (t, y) (1, f y))
    (hzero : L (x t) + fderiv ℝ W (t, x t) (1, f (x t)) = 0) :
    HasDerivAt (fun s ↦ fderiv ℝ (fun y ↦ W (s, y)) (x s))
      (-ell - (fderiv ℝ (fun y ↦ W (t, y)) (x t)).comp A) t := by
  have hJ : HasFDerivAt (fderiv ℝ W)
      (fderiv ℝ (fderiv ℝ W) (t, x t)) (t, x t) :=
    ((hW.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hB : ∀ a b : ℝ × X,
      fderiv ℝ (fderiv ℝ W) (t, x t) a b =
        fderiv ℝ (fderiv ℝ W) (t, x t) b a :=
    hW.contDiffAt.isSymmSndFDerivAt (by simp)
  have hbridge := hjb_covector_adjoint_of_jet (fderiv ℝ W)
    (fderiv ℝ (fderiv ℝ W) (t, x t)) x t f L A ell hJ hB hx hf hL
    hnonneg hzero
  have hrestrict : ∀ s : ℝ,
      (fderiv ℝ W (s, x s)).comp spatialInclusion =
        fderiv ℝ (fun y ↦ W (s, y)) (x s) := by
    intro s
    exact jointDerivative_restrict_eq_spatial W s (x s)
      (hW.differentiable (by norm_num) (s, x s))
  simpa only [hrestrict] using hbridge

end Normed

section InnerProduct

variable [InnerProductSpace ℝ X] [CompleteSpace X]

/-- **The same HJB derivation in the existing library's vector-costate form.**

This is the pointwise `costateEquation` statement: the costate is the value
gradient and the derivative is the negative spatial gradient of the
Hamiltonian with that costate frozen. Riesz duality is applied only after the
covector adjoint has been derived.
-/
theorem hjb_value_gradient_adjoint
    (W : (ℝ × X) → ℝ) (x : ℝ → X) (t : ℝ)
    (f : X → X) (L : X → ℝ)
    (A : X →L[ℝ] X) (ell : X →L[ℝ] ℝ)
    (hW : ContDiff ℝ 2 W)
    (hx : HasDerivAt x (f (x t)) t)
    (hf : HasFDerivAt f A (x t))
    (hL : HasFDerivAt L ell (x t))
    (hnonneg : ∀ᶠ y in 𝓝 (x t),
      0 ≤ L y + fderiv ℝ W (t, y) (1, f y))
    (hzero : L (x t) + fderiv ℝ W (t, x t) (1, f (x t)) = 0) :
    HasDerivAt (fun s ↦ gradient (fun y ↦ W (s, y)) (x s))
      (-gradient (fun y ↦ L y + inner ℝ
        (gradient (fun z ↦ W (t, z)) (x t)) (f y)) (x t)) t := by
  let q : X →L[ℝ] ℝ := fderiv ℝ (fun y ↦ W (t, y)) (x t)
  have hq := hjb_value_covector_adjoint W x t f L A ell hW hx hf hL hnonneg hzero
  have hduality : ∀ v : X,
      inner ℝ (gradient (fun z ↦ W (t, z)) (x t)) v = q v := by
    intro v
    change (InnerProductSpace.toDual ℝ X)
      (gradient (fun z ↦ W (t, z)) (x t)) v = q v
    rw [toDual_gradient]
  have hHamiltonian : HasFDerivAt (fun y ↦ L y + inner ℝ
      (gradient (fun z ↦ W (t, z)) (x t)) (f y)) (ell + q.comp A) (x t) := by
    simp only [hduality]
    exact hL.add (q.hasFDerivAt.comp (x t) hf)
  let riesz : (X →L[ℝ] ℝ) →L[ℝ] X :=
    (InnerProductSpace.toDual ℝ X).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hp := riesz.hasFDerivAt.comp_hasDerivAt t hq
  have hgrad := hHamiltonian.hasGradientAt.gradient
  change HasDerivAt (fun s ↦ gradient (fun y ↦ W (s, y)) (x s))
    ((InnerProductSpace.toDual ℝ X).symm (-ell - q.comp A)) t at hp
  rw [hgrad]
  convert hp using 1
  simp only [map_sub, map_neg, map_add]
  abel

end InnerProduct

end HJBResidualBridge
