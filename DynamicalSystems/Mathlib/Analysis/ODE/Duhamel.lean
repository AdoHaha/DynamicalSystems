/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistence
public import DynamicalSystems.Mathlib.Analysis.ODE.StateTransition
public import Mathlib.Analysis.Normed.Operator.Completeness

/-!
# Duhamel's formula constructs solutions

`IsStateTransition.variationOfConstants` expresses an existing solution as an
integral. This file proves the converse: the Duhamel integral is an actual
solution of the inhomogeneous equation.

The direct interface needs a state transition and continuous forcing. The
unbundled interface needs only continuous operator coefficients, a normalized
operator-valued fundamental solution, and its forward `HasDerivAt` equation.
Uniqueness supplies the cocycle, and differentiation of the inverse supplies
the backward equation. No propagator law, continuity of the two-time solution,
or differentiability of the integral is assumed in that interface.

All results hold in real Banach spaces, with no finite-dimensionality or
uniform-in-time bound on the coefficients. Intervals are oriented, so the
formulas hold both before and after the initial time.
-/

@[expose] public noncomputable section

open Filter Topology MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Continuous operator coefficients give a vector field uniformly locally
Lipschitz in the state, with a Lipschitz constant on each time neighborhood. -/
theorem Continuous.uniformlyLocallyLipschitz_clm {L : ℝ → E →L[ℝ] E}
    (hL : Continuous L) : UniformlyLocallyLipschitz (fun t x => L t x) := by
  intro t₀ x₀
  refine ⟨⟨‖L t₀‖ + 1, by positivity⟩, Set.univ, Filter.univ_mem, ?_⟩
  have hbound : ∀ᶠ t in 𝓝 t₀, ‖L t‖ < ‖L t₀‖ + 1 :=
    hL.norm.continuousAt.eventually_lt_const (by linarith)
  filter_upwards [hbound] with t ht
  exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le ht.le).lipschitzOnWith

namespace IsFundamentalSolution

variable {L : ℝ → E →L[ℝ] E} {X : ℝ → ℝ → E →L[ℝ] E}

/-- A normalized forward linear fundamental solution has the restart law by
uniqueness. The convention is `X s t`: propagate from `s` to `t`. -/
theorem linear_cocycle (hL : Continuous L)
    (hX₀ : ∀ s, X s s = ContinuousLinearMap.id ℝ E)
    (hX : ∀ s t, HasDerivAt (X s ·) ((L t).comp (X s t)) t)
    (s r t : ℝ) : (X r t).comp (X s r) = X s t := by
  have hΦ := linear_fundamental_solution L X hX₀ hX
  ext x
  have heq : (fun q => X r q (X s r x)) = fun q => X s q x :=
    (hΦ.isIntegralCurve r (X s r x)).eq_of_uniformlyLocallyLipschitz
      (t₀ := r) hL.uniformlyLocallyLipschitz_clm (hΦ.isIntegralCurve s x) (by simp [hX₀])
  exact congrFun heq t

variable [CompleteSpace E]

/-- The normalized forward operator equation determines a full state
transition, including its backward equation, in a Banach space. -/
theorem isStateTransition (hL : Continuous L)
    (hX₀ : ∀ s, X s s = ContinuousLinearMap.id ℝ E)
    (hX : ∀ s t, HasDerivAt (X s ·) ((L t).comp (X s t)) t) :
    IsStateTransition L (fun t s => X s t) := by
  have hcocycle := linear_cocycle hL hX₀ hX
  let U (s t : ℝ) : (E →L[ℝ] E)ˣ :=
    { val := X s t
      inv := X t s
      val_inv := by
        change (X s t).comp (X t s) = ContinuousLinearMap.id ℝ E
        rw [hcocycle, hX₀]
      inv_val := by
        change (X t s).comp (X s t) = ContinuousLinearMap.id ℝ E
        rw [hcocycle, hX₀] }
  have hinv (s t : ℝ) : Ring.inverse (X s t) = X t s :=
    Ring.inverse_unit (U s t)
  refine ⟨hX₀, hX, ?_, fun t r s => hcocycle s r t⟩
  intro t s
  have hderiv := (hasFDerivAt_ringInverse (𝕜 := ℝ) (U t s)).comp_hasDerivAt s (hX t s)
  have heq : (Ring.inverse ∘ X t) = fun r => X r t :=
    funext (hinv t)
  rw [heq] at hderiv
  convert hderiv using 1
  ext x
  change -(X s t (L s x)) = -(X s t (L s (X t s (X s t x))))
  have hcancel : X t s (X s t x) = x := by
    have h := congrArg (fun A : E →L[ℝ] E => A x) (hcocycle s t s)
    simpa [hX₀] using h
  rw [hcancel]

end IsFundamentalSolution

namespace IsStateTransition

variable [CompleteSpace E]
variable {L : ℝ → E →L[ℝ] E} {Phi : ℝ → ℝ → E →L[ℝ] E}
variable {g : ℝ → E}

/-- Factor the Duhamel integral through a fixed reference time. This reduces
its differentiation to the ordinary FTC for a one-variable integrand. -/
theorem duhamelOperator_eq (hPhi : IsStateTransition L Phi) (hg : Continuous g)
    (s : ℝ) (x₀ : E) (t : ℝ) :
    IsFundamentalSolution.duhamelOperator (fun r q => Phi q r) g s x₀ t =
      Phi t s (x₀ + ∫ r in s..t, Phi s r (g r)) := by
  have hP : Continuous (fun r => Phi s r) :=
    continuous_iff_continuousAt.mpr (fun r => (hPhi.backward s r).continuousAt)
  rw [IsFundamentalSolution.duhamelOperator, map_add,
    ← (Phi t s).intervalIntegral_comp_comm ((hP.clm_apply hg).intervalIntegrable s t)]
  congr 1
  apply intervalIntegral.integral_congr
  intro r _
  exact congrArg (fun A : E →L[ℝ] E => A (g r)) (hPhi.cocycle t s r).symm

/-- Duhamel's formula, in its constructive direction: the integral has the
derivative required by the inhomogeneous equation. -/
theorem hasDerivAt_duhamelOperator (hPhi : IsStateTransition L Phi) (hg : Continuous g)
    (s : ℝ) (x₀ : E) (t : ℝ) :
    HasDerivAt (IsFundamentalSolution.duhamelOperator (fun r q => Phi q r) g s x₀)
      (L t (IsFundamentalSolution.duhamelOperator (fun r q => Phi q r) g s x₀ t) + g t) t := by
  have hP : Continuous (fun r => Phi s r) :=
    continuous_iff_continuousAt.mpr (fun r => (hPhi.backward s r).continuousAt)
  have hFTC := ((hP.clm_apply hg).integral_hasStrictDerivAt s t).hasDerivAt
  have hd := (hPhi.forward s t).clm_apply ((hasDerivAt_const t x₀).add hFTC)
  have heq : IsFundamentalSolution.duhamelOperator (fun r q => Phi q r) g s x₀ =
      fun q => Phi q s (x₀ + ∫ r in s..q, Phi s r (g r)) :=
    funext (hPhi.duhamelOperator_eq hg s x₀)
  rw [heq]
  have hcancel : Phi t s (Phi s t (g t)) = g t := by
    have h := congrArg (fun A : E →L[ℝ] E => A (g t)) (hPhi.cocycle t s t)
    simpa [hPhi.diag] using h
  simpa only [ContinuousLinearMap.comp_apply, Pi.add_apply, zero_add, hcancel] using hd

/-- Duhamel's formula constructs a global integral curve. -/
theorem isIntegralCurve_duhamelOperator (hPhi : IsStateTransition L Phi) (hg : Continuous g)
    (s : ℝ) (x₀ : E) :
    IsIntegralCurve (IsFundamentalSolution.duhamelOperator (fun r q => Phi q r) g s x₀)
      (fun t x => L t x + g t) :=
  hPhi.hasDerivAt_duhamelOperator hg s x₀

/-- Duhamel's formula constructs the whole inhomogeneous fundamental solution,
with its initial condition supplied by the diagonal normalization. -/
theorem isFundamentalSolution_duhamelOperator
    (hPhi : IsStateTransition L Phi) (hg : Continuous g) :
    IsFundamentalSolution
      (IsFundamentalSolution.duhamelOperator (fun r q => Phi q r) g)
      (fun t x => L t x + g t) where
  isIntegralCurve := hPhi.isIntegralCurve_duhamelOperator hg
  initial := IsFundamentalSolution.duhamelOperator_initial _ hPhi.diag

end IsStateTransition

namespace IsFundamentalSolution

variable [CompleteSpace E]
variable {L : ℝ → E →L[ℝ] E} {X : ℝ → ℝ → E →L[ℝ] E} {g : ℝ → E}

/-- The unbundled Duhamel constructor from the normalized forward operator
equation and continuous coefficients and forcing. -/
theorem duhamelOperator_hasDerivAt (hL : Continuous L) (hg : Continuous g)
    (hX₀ : ∀ s, X s s = ContinuousLinearMap.id ℝ E)
    (hX : ∀ s t, HasDerivAt (X s ·) ((L t).comp (X s t)) t)
    (t₀ : ℝ) (x₀ : E) (t : ℝ) :
    HasDerivAt (duhamelOperator X g t₀ x₀)
      (L t (duhamelOperator X g t₀ x₀ t) + g t) t :=
  (isStateTransition hL hX₀ hX).hasDerivAt_duhamelOperator hg t₀ x₀ t

/-- The Duhamel operator is a genuine integral curve; its assumptions include
normalization and differentiability, not merely a value for total `deriv`. -/
theorem duhamelOperator_isIntegralCurve (hL : Continuous L) (hg : Continuous g)
    (hX₀ : ∀ s, X s s = ContinuousLinearMap.id ℝ E)
    (hX : ∀ s t, HasDerivAt (X s ·) ((L t).comp (X s t)) t)
    (t₀ : ℝ) (x₀ : E) :
    IsIntegralCurve (duhamelOperator X g t₀ x₀) (fun t x => L t x + g t) :=
  duhamelOperator_hasDerivAt hL hg hX₀ hX t₀ x₀

/-- The pointwise derivative form of Duhamel's formula. -/
theorem duhamelOperator_deriv (hL : Continuous L) (hg : Continuous g)
    (hX₀ : ∀ s, X s s = ContinuousLinearMap.id ℝ E)
    (hX : ∀ s t, HasDerivAt (X s ·) ((L t).comp (X s t)) t)
    (t₀ : ℝ) (x₀ : E) (t : ℝ) :
    deriv (duhamelOperator X g t₀ x₀) t = L t (duhamelOperator X g t₀ x₀ t) + g t :=
  (duhamelOperator_hasDerivAt hL hg hX₀ hX t₀ x₀ t).deriv

/-- Continuous forcing added to a normalized linear fundamental solution gives
a fundamental solution of the inhomogeneous equation by Duhamel's formula. -/
theorem duhamelOperator_isFundamentalSolution (hL : Continuous L) (hg : Continuous g)
    (hX₀ : ∀ s, X s s = ContinuousLinearMap.id ℝ E)
    (hX : ∀ s t, HasDerivAt (X s ·) ((L t).comp (X s t)) t) :
    IsFundamentalSolution (duhamelOperator X g) (fun t x => L t x + g t) :=
  (isStateTransition hL hX₀ hX).isFundamentalSolution_duhamelOperator hg

end IsFundamentalSolution
