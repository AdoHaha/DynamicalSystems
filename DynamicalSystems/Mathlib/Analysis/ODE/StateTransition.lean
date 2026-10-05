/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A full state transition from two fundamental linear initial-value problems

Solve `U' = A U`, `V' = -V A`, with `U(0) = V(0) = id`, in the space of
continuous linear endomorphisms. The product rule proves `V(t) U(t) = id`.
Finite dimensionality supplies the reverse identity. Consequently
`Phi(t,s) = U(t) V(s)` has the forward equation, backward equation, and cocycle
law. The Duhamel cancellation is then a theorem, obtained by the product rule.

The construction in this file is conditional only on the two explicitly stated
linear initial-value problems. It assumes neither a propagator law nor the
derivative of the Duhamel integrand. Existence of the two linear IVPs is an
independent ODE input; the companion existence adapter uses the repository's
`global_existence` theorem under continuous bounded coefficients.

References: Berkovitz and Medhin, Nonlinear Optimal Control Theory (2012),
Chapter 7; Sontag, Mathematical Control Theory (1998), Chapter 9.5.
-/

@[expose] public section

open MeasureTheory
open scoped Interval

namespace KirkMedhin

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The complete operator-valued state-transition specification. Time is ordered
as `Phi t s`: propagation from `s` to `t`. -/
structure IsStateTransition (A : ℝ → X →L[ℝ] X)
    (Phi : ℝ → ℝ → X →L[ℝ] X) : Prop where
  diag : ∀ s, Phi s s = ContinuousLinearMap.id ℝ X
  forward : ∀ s t, HasDerivAt (fun r => Phi r s) ((A t).comp (Phi t s)) t
  backward : ∀ t s, HasDerivAt (fun r => Phi t r) (-((Phi t s).comp (A s))) s
  cocycle : ∀ t r s, (Phi t r).comp (Phi r s) = Phi t s

/-- Independent linear IVP data. No identity involving a product of the two
solutions is assumed. -/
def HasFundamentalPair (A : ℝ → X →L[ℝ] X) : Prop :=
  ∃ U V : ℝ → X →L[ℝ] X,
    U 0 = ContinuousLinearMap.id ℝ X ∧
    V 0 = ContinuousLinearMap.id ℝ X ∧
    (∀ t, HasDerivAt U ((A t).comp (U t)) t) ∧
    (∀ t, HasDerivAt V (-((V t).comp (A t))) t)

/-- The two fundamental solutions multiply to the identity in this order,
without requiring finite dimensionality. -/
theorem fundamentalPair_left_inverse
    {A U V : ℝ → X →L[ℝ] X}
    (hU0 : U 0 = ContinuousLinearMap.id ℝ X)
    (hV0 : V 0 = ContinuousLinearMap.id ℝ X)
    (hU : ∀ t, HasDerivAt U ((A t).comp (U t)) t)
    (hV : ∀ t, HasDerivAt V (-((V t).comp (A t))) t)
    (t : ℝ) : (V t).comp (U t) = ContinuousLinearMap.id ℝ X := by
  have hz : ∀ r, HasDerivAt (fun q => (V q).comp (U q)) 0 r := by
    intro r
    convert (hV r).clm_comp (hU r) using 1
    ext x
    simp
  have hc := is_const_of_deriv_eq_zero
    (fun r => (hz r).differentiableAt) (fun r => (hz r).deriv) t 0
  simpa [hU0, hV0] using hc

/-- A one-sided inverse of an endomorphism is a two-sided inverse in finite
dimension. This is the sole use of finite dimensionality in the construction. -/
theorem clm_comp_eq_id_comm [FiniteDimensional ℝ X]
    {P Q : X →L[ℝ] X} (h : P.comp Q = ContinuousLinearMap.id ℝ X) :
    Q.comp P = ContinuousLinearMap.id ℝ X := by
  have hlin : P.toLinearMap.comp Q.toLinearMap = LinearMap.id :=
    congrArg (fun R : X →L[ℝ] X => R.toLinearMap) h
  have hrev : Q.toLinearMap.comp P.toLinearMap = LinearMap.id :=
    (LinearMap.comp_eq_id_comm ℝ X).mp hlin
  ext x
  exact congrArg (fun R : X →ₗ[ℝ] X => R x) hrev

/-- The fundamental-pair construction of the transition operator. -/
def transitionOfFundamentalPair (U V : ℝ → X →L[ℝ] X)
    (t s : ℝ) : X →L[ℝ] X := (U t).comp (V s)

/-- Actual solutions of the two linear IVPs produce the full propagator. -/
theorem isStateTransition_of_fundamentalPair [FiniteDimensional ℝ X]
    {A U V : ℝ → X →L[ℝ] X}
    (hU0 : U 0 = ContinuousLinearMap.id ℝ X)
    (hV0 : V 0 = ContinuousLinearMap.id ℝ X)
    (hU : ∀ t, HasDerivAt U ((A t).comp (U t)) t)
    (hV : ∀ t, HasDerivAt V (-((V t).comp (A t))) t) :
    IsStateTransition A (transitionOfFundamentalPair U V) := by
  have hVU : ∀ r, (V r).comp (U r) = ContinuousLinearMap.id ℝ X :=
    fundamentalPair_left_inverse hU0 hV0 hU hV
  have hUV : ∀ r, (U r).comp (V r) = ContinuousLinearMap.id ℝ X :=
    fun r => clm_comp_eq_id_comm (hVU r)
  refine ⟨hUV, ?_, ?_, ?_⟩
  · intro s t
    unfold transitionOfFundamentalPair
    convert (hU t).clm_comp (hasDerivAt_const t (V s)) using 1
    ext x
    simp
  · intro t s
    unfold transitionOfFundamentalPair
    convert (hasDerivAt_const s (U t)).clm_comp (hV s) using 1
    ext x
    simp
  · intro t r s
    ext x
    change U t (V r (U r (V s x))) = U t (V s x)
    have h := congrArg (fun R : X →L[ℝ] X => R (V s x)) (hVU r)
    change V r (U r (V s x)) = V s x at h
    rw [h]

/-- Existence of a full propagator from the independent pair of linear IVPs. -/
theorem exists_stateTransition_of_fundamentalPair [FiniteDimensional ℝ X]
    {A : ℝ → X →L[ℝ] X} (h : HasFundamentalPair A) :
    ∃ Phi : ℝ → ℝ → X →L[ℝ] X, IsStateTransition A Phi := by
  obtain ⟨U, V, hU0, hV0, hU, hV⟩ := h
  exact ⟨transitionOfFundamentalPair U V,
    isStateTransition_of_fundamentalPair hU0 hV0 hU hV⟩

/-- The cocycle factors the two-time family through a fixed time. Consequently
the two differential equations imply joint operator-norm continuity. -/
theorem IsStateTransition.continuous
    {A : ℝ → X →L[ℝ] X} {Phi : ℝ → ℝ → X →L[ℝ] X}
    (hPhi : IsStateTransition A Phi) :
    Continuous (fun z : ℝ × ℝ => Phi z.1 z.2) := by
  have hF : Continuous (fun t => Phi t 0) :=
    continuous_iff_continuousAt.mpr (fun t => (hPhi.forward 0 t).continuousAt)
  have hB : Continuous (fun s => Phi 0 s) :=
    continuous_iff_continuousAt.mpr (fun s => (hPhi.backward 0 s).continuousAt)
  have hcomp : Continuous (fun z : ℝ × ℝ => (Phi z.1 0).comp (Phi 0 z.2)) :=
    (hF.comp continuous_fst).clm_comp (hB.comp continuous_snd)
  have heq : (fun z : ℝ × ℝ => (Phi z.1 0).comp (Phi 0 z.2)) =
      (fun z : ℝ × ℝ => Phi z.1 z.2) := by
    funext z
    exact hPhi.cocycle z.1 0 z.2
  rwa [heq] at hcomp

/-- A single operator-norm bound works for all pairs of times in a compact
interval. This is useful when estimating the Duhamel remainder uniformly. -/
theorem IsStateTransition.exists_norm_bound_on_Icc
    {A : ℝ → X →L[ℝ] X} {Phi : ℝ → ℝ → X →L[ℝ] X}
    (hPhi : IsStateTransition A Phi) (a b : ℝ) :
    ∃ C ≥ (0 : ℝ), ∀ t ∈ Set.Icc a b, ∀ s ∈ Set.Icc a b, ‖Phi t s‖ ≤ C := by
  have hcompact : IsCompact (Set.Icc a b ×ˢ Set.Icc a b) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hPhi.continuous.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht s hs
  exact (hC (t, s) ⟨ht, hs⟩).trans (le_max_left _ _)

/-- The forward equation specialized to a constant initial vector. This matches
the forward clause of the earlier `stateTransition` predicate. -/
theorem IsStateTransition.forward_apply
    {A : ℝ → X →L[ℝ] X} {Phi : ℝ → ℝ → X →L[ℝ] X}
    (hPhi : IsStateTransition A Phi) (s t : ℝ) (x : X) :
    HasDerivAt (fun r => Phi r s x) (A t (Phi t s x)) t := by
  simpa using (hPhi.forward s t).clm_apply (hasDerivAt_const t x)

/-- Propagating a terminal covector backward gives the homogeneous adjoint
equation. In the cost-augmented state space this is the adjoint propagation
used after separating the endpoint-variation cone. -/
theorem IsStateTransition.terminal_covector_derivative
    {A : ℝ → X →L[ℝ] X} {Phi : ℝ → ℝ → X →L[ℝ] X}
    (hPhi : IsStateTransition A Phi) (lambda : X →L[ℝ] ℝ) (T t : ℝ) :
    HasDerivAt (fun s => lambda.comp (Phi T s))
      (-((lambda.comp (Phi T t)).comp (A t))) t := by
  convert (hasDerivAt_const t lambda).clm_comp (hPhi.backward T t) using 1
  ext x
  simp

/-- The backward-propagated covector has the prescribed terminal value. -/
theorem IsStateTransition.terminal_covector_value
    {A : ℝ → X →L[ℝ] X} {Phi : ℝ → ℝ → X →L[ℝ] X}
    (hPhi : IsStateTransition A Phi) (lambda : X →L[ℝ] ℝ) (T : ℝ) :
    lambda.comp (Phi T T) = lambda := by
  simp [hPhi.diag T]

/-- The derivative cancellation used by Duhamel's formula is derived from the
backward propagator equation and the actual inhomogeneous trajectory equation. -/
theorem IsStateTransition.duhamel_cancellation
    {A : ℝ → X →L[ℝ] X} {Phi : ℝ → ℝ → X →L[ℝ] X}
    (hPhi : IsStateTransition A Phi) {b x : ℝ → X} {t r : ℝ}
    (hx : HasDerivAt x (A r (x r) + b r) r) :
    HasDerivAt (fun q => Phi t q (x q)) (Phi t r (b r)) r := by
  simpa [map_add] using (hPhi.backward t r).clm_apply hx

/-- Variation of constants with no cancellation premise. -/
theorem IsStateTransition.variationOfConstants [CompleteSpace X]
    {A : ℝ → X →L[ℝ] X} {Phi : ℝ → ℝ → X →L[ℝ] X}
    {b x : ℝ → X} {s t : ℝ}
    (hPhi : IsStateTransition A Phi)
    (hx : ∀ r ∈ Set.uIcc s t, HasDerivAt x (A r (x r) + b r) r)
    (hint : IntervalIntegrable (fun r => Phi t r (b r)) volume s t) :
    x t = Phi t s (x s) + ∫ r in s..t, Phi t r (b r) := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := s) (b := t) (f := fun r => Phi t r (x r))
    (f' := fun r => Phi t r (b r))
    (fun r hr => hPhi.duhamel_cancellation (hx r hr)) hint
  simp only [hPhi.diag t, ContinuousLinearMap.id_apply] at hFTC
  rw [hFTC]
  abel

/-- For continuous forcing, the integrability premise in Duhamel's formula also
follows from the propagator equations. -/
theorem IsStateTransition.variationOfConstants_of_continuous [CompleteSpace X]
    {A : ℝ → X →L[ℝ] X} {Phi : ℝ → ℝ → X →L[ℝ] X}
    {b x : ℝ → X} {s t : ℝ}
    (hPhi : IsStateTransition A Phi)
    (hx : ∀ r ∈ Set.uIcc s t, HasDerivAt x (A r (x r) + b r) r)
    (hb : Continuous b) :
    x t = Phi t s (x s) + ∫ r in s..t, Phi t r (b r) := by
  apply hPhi.variationOfConstants hx
  have hP : Continuous (fun r => Phi t r) :=
    continuous_iff_continuousAt.mpr (fun r => (hPhi.backward t r).continuousAt)
  exact (hP.clm_apply hb).intervalIntegrable s t

end KirkMedhin

end
