/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.StateTransition
public import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistenceLinear
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.Order.ProjIcc

/-!
# Existence of the fundamental pair and full state transition

This adapter discharges the independent linear-IVP input of `StateTransition`
using the already proved `global_existence` theorem in DynamicalSystems.

For a continuous bounded coefficient `A`, solve the left and right operator
equations in the Banach space `X →L[ℝ] X`. For a coefficient continuous only on
a compact interval, clamp the time variable to that interval. No differentiable
dependence on initial time, no smoothness in time beyond continuity, and no
unproved bundled nonautonomous-flow theorem are used.
-/

@[expose] public section

open Set
open scoped NNReal

namespace KirkMedhin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A continuous bounded linear coefficient has a global solution through any
initial condition. This is an adapter to the existing nonlinear existence API. -/
theorem exists_global_linearIVP_of_bound
    {A : ℝ → E →L[ℝ] E} {K : ℝ≥0}
    (hA : Continuous A) (hbound : ∀ t, ‖A t‖ ≤ (K : ℝ))
    (s : ℝ) (y₀ : E) :
    ∃ y : ℝ → E, y s = y₀ ∧ ∀ t, HasDerivAt y (A t (y t)) t := by
  have hlip : ∀ t, LipschitzWith K (fun y : E => A t y) :=
    fun t => ContinuousLinearMap.lipschitzWith_of_opNorm_le (hbound t)
  have hcont : Continuous (fun z : ℝ × E => A z.1 z.2) :=
    (hA.comp continuous_fst).clm_apply continuous_snd
  obtain ⟨F, hF⟩ := global_existence (f := fun t y => A t y)
    (C' := 0) hlip (fun t => by simp) hcont
  exact ⟨F s y₀, (hF s y₀).2, (hF s y₀).1⟩

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Continuous bounded coefficients provide the two independent fundamental
IVPs used to construct the propagator. This theorem needs no finite dimension. -/
theorem hasFundamentalPair_of_continuous_bounded
    {A : ℝ → X →L[ℝ] X} {K : ℝ≥0}
    (hA : Continuous A) (hbound : ∀ t, ‖A t‖ ≤ (K : ℝ)) :
    HasFundamentalPair A := by
  let C := ContinuousLinearMap.compL ℝ X X X
  have hleft : Continuous (fun t => C (A t)) := C.continuous.comp hA
  have hright : Continuous (fun t => -(C.flip (A t))) :=
    (C.flip.continuous.comp hA).neg
  have hleft_bound : ∀ t, ‖C (A t)‖ ≤ (K : ℝ) := by
    intro t
    apply (C (A t)).opNorm_le_bound K.coe_nonneg
    intro M
    change ‖(A t).comp M‖ ≤ (K : ℝ) * ‖M‖
    exact ((A t).opNorm_comp_le M).trans
      (mul_le_mul_of_nonneg_right (hbound t) (norm_nonneg M))
  have hright_bound : ∀ t, ‖-(C.flip (A t))‖ ≤ (K : ℝ) := by
    intro t
    rw [norm_neg]
    apply (C.flip (A t)).opNorm_le_bound K.coe_nonneg
    intro M
    change ‖M.comp (A t)‖ ≤ (K : ℝ) * ‖M‖
    calc
      ‖M.comp (A t)‖ ≤ ‖M‖ * ‖A t‖ := M.opNorm_comp_le (A t)
      _ ≤ ‖M‖ * (K : ℝ) :=
        mul_le_mul_of_nonneg_left (hbound t) (norm_nonneg M)
      _ = (K : ℝ) * ‖M‖ := mul_comm _ _
  obtain ⟨U, hU0, hU⟩ := exists_global_linearIVP_of_bound
    hleft hleft_bound 0 (ContinuousLinearMap.id ℝ X)
  obtain ⟨V, hV0, hV⟩ := exists_global_linearIVP_of_bound
    hright hright_bound 0 (ContinuousLinearMap.id ℝ X)
  refine ⟨U, V, hU0, hV0, ?_, ?_⟩
  · intro t
    simpa [C] using hU t
  · intro t
    simpa [C] using hV t

/-- A full nonautonomous state transition exists under continuous bounded
coefficients. Forward, backward, and composition laws are conclusions. -/
theorem exists_stateTransition_of_continuous_bounded [FiniteDimensional ℝ X]
    {A : ℝ → X →L[ℝ] X} {K : ℝ≥0}
    (hA : Continuous A) (hbound : ∀ t, ‖A t‖ ≤ (K : ℝ)) :
    ∃ Phi : ℝ → ℝ → X →L[ℝ] X, IsStateTransition A Phi :=
  exists_stateTransition_of_fundamentalPair
    (hasFundamentalPair_of_continuous_bounded hA hbound)

/-- Compact-interval coefficient data suffice: extending by constant endpoint
values yields a continuous bounded coefficient and its full global propagator.
The extension agrees with the original coefficient throughout the interval. -/
theorem exists_clamped_stateTransition [FiniteDimensional ℝ X]
    {A : ℝ → X →L[ℝ] X} {a b : ℝ}
    (hab : a ≤ b) (hA : ContinuousOn A (Icc a b)) :
    ∃ Aext : ℝ → X →L[ℝ] X,
      EqOn Aext A (Icc a b) ∧
      ∃ Phi : ℝ → ℝ → X →L[ℝ] X, IsStateTransition Aext Phi := by
  let Aext : ℝ → X →L[ℝ] X := fun t => A (projIcc a b hab t)
  have hext : Continuous Aext := hA.domRestrict.comp continuous_projIcc
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  let K : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  have hbound : ∀ t, ‖Aext t‖ ≤ (K : ℝ) := by
    intro t
    exact (hM (projIcc a b hab t) (projIcc a b hab t).property).trans
      (le_max_left _ _)
  have heq : EqOn Aext A (Icc a b) := by
    intro t ht
    simp only [Aext, projIcc_of_mem hab ht]
  exact ⟨Aext, heq, exists_stateTransition_of_continuous_bounded hext hbound⟩

/-- Full propagator laws on a compact interval, stated directly with the
original coefficient. Diagonal and cocycle laws also hold outside that interval
for the constructed extension; each differential law needs its differentiated
time variable to lie inside the specified interval. -/
theorem exists_stateTransitionOn_Icc [FiniteDimensional ℝ X]
    {A : ℝ → X →L[ℝ] X} {a b : ℝ}
    (hab : a ≤ b) (hA : ContinuousOn A (Icc a b)) :
    ∃ Phi : ℝ → ℝ → X →L[ℝ] X,
      (∀ s, Phi s s = ContinuousLinearMap.id ℝ X) ∧
      (∀ s t, t ∈ Icc a b →
        HasDerivAt (fun r => Phi r s) ((A t).comp (Phi t s)) t) ∧
      (∀ t s, s ∈ Icc a b →
        HasDerivAt (fun r => Phi t r) (-((Phi t s).comp (A s))) s) ∧
      (∀ t r s, (Phi t r).comp (Phi r s) = Phi t s) := by
  obtain ⟨Aext, heq, Phi, hPhi⟩ := exists_clamped_stateTransition hab hA
  refine ⟨Phi, hPhi.diag, ?_, ?_, hPhi.cocycle⟩
  · intro s t ht
    simpa only [heq ht] using hPhi.forward s t
  · intro t s hs
    simpa only [heq hs] using hPhi.backward t s

end KirkMedhin

end
