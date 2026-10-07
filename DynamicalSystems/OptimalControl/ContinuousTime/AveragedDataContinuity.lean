/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.ControlAveragedRegularity

/-!
# Continuity in the state of the control-averaged data of a bounded-state problem

For each fixed time `t`, the control-averaged data

* `F t y = ∫ f(t,y,u) d(ρ.kernel t)(u)` (`Problem.averagedDynamics`),
* `∫ f⁰(t,y,u) d(ρ.kernel t)(u)` (`Problem.averagedRunningCost`),
* `Fx t y = ∫ fₓ(t,y,u) d(ρ.kernel t)(u)` (`Problem.averagedDynamicsDerivative`),
* `cx t y = T⁻¹ ∫ f⁰ₓ(t,y,u) d(ρ.kernel t)(u)` (`Problem.averagedRunningCovector`)

are continuous in the state `y`.  The clamped time `Set.projIcc 0 T t` is fixed, so the averages
are parameter integrals over the compact control set against a fixed probability measure, of
integrands jointly continuous in `(y,u)` (Assumption 11.6.1 via `Problem.DerivativeContinuity`).

As a consequence the state and velocity covectors of the pointwise-defect Lagrangian built from
these data are jointly continuous in `(x,v)` for each fixed time; this is what the `j → ∞` limit
of the penalised problems needs.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.5.1,
Assumption 11.6.1, (11.6.8)-(11.6.9).
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology Interval
open ProbabilityTheory

namespace OptimalControl.BoundedState

/-- **Continuity of a parameter integral over a compact control space.**  If `g : X → U → G` is
jointly continuous, `X` is locally compact and `U` is compact, then `x ↦ ∫ u, g x u dν(u)` is
continuous for every finite measure `ν`. -/
theorem continuous_kernel_average_param
    {U : Type*} [MeasurableSpace U] [TopologicalSpace U] [OpensMeasurableSpace U]
    [CompactSpace U] [SecondCountableTopology U] {ν : Measure U} [IsFiniteMeasure ν]
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X] [LocallyCompactSpace X]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : X → U → G} (hg : Continuous (Function.uncurry g)) :
    Continuous (fun x => ∫ u, g x u ∂ν) := by
  have h := continuous_parametric_integral_of_continuous (μ := ν) hg isCompact_univ
  simpa only [Measure.restrict_univ] using h

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]
  {P : Problem E V W}

namespace Problem

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Joint continuity in `(y,u)` of a slice `(y,u) ↦ g ((q,y),u)` of a jointly continuous field. -/
theorem continuous_slice_uncurry {G : Type*} [TopologicalSpace G] (P : Problem E V W)
    (q : P.Time) {g : (P.Time × E) × V → G} (hg : Continuous g) :
    Continuous (Function.uncurry fun (y : E) (u : P.Control) => g ((q, y), (u : V))) :=
  hg.comp ((continuous_const.prodMk continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd))

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- **Continuity of the averaged dynamics in the state.**  For each fixed time `t`,
`y ↦ ∫ f(t,y,u) d(ρ.kernel t)(u)` is continuous.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.6.1. -/
theorem continuous_averagedDynamics (P : Problem E V W) (ρ : P.Relaxed) (t : ℝ) :
    Continuous (P.averagedDynamics ρ t) := by
  unfold averagedDynamics
  exact continuous_kernel_average_param
    (P.continuous_slice_uncurry _ (g := fun z => P.dynamics z.1.1 z.1.2 z.2)
      P.dynamics_continuous)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- **Continuity of the averaged running cost in the state.**  For each fixed time `t`,
`y ↦ ∫ f⁰(t,y,u) d(ρ.kernel t)(u)` is continuous.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.6.1. -/
theorem continuous_averagedRunningCost (P : Problem E V W) (ρ : P.Relaxed) (t : ℝ) :
    Continuous (P.averagedRunningCost ρ t) := by
  unfold averagedRunningCost
  exact continuous_kernel_average_param
    (P.continuous_slice_uncurry _ (g := fun z => P.runningCost z.1.1 z.1.2 z.2)
      P.runningCost_continuous)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- **Continuity of the averaged dynamics derivative in the state.**  For each fixed time `t`,
`y ↦ ∫ fₓ(t,y,u) d(ρ.kernel t)(u)` is continuous.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.6.1. -/
theorem continuous_averagedDynamicsDerivative (P : Problem E V W) (D : P.SmoothData)
    (hD : P.DerivativeContinuity D) (ρ : P.Relaxed) (t : ℝ) :
    Continuous (P.averagedDynamicsDerivative D ρ t) := by
  unfold averagedDynamicsDerivative
  exact continuous_kernel_average_param
    (P.continuous_slice_uncurry _ (g := fun z => D.dynamicsDerivative z.1.1 z.1.2 z.2)
      hD.continuous_dynamicsDerivative)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- **Continuity of the averaged running-cost state covector in the state.**  For each fixed time
`t`, `y ↦ T⁻¹ ∫ f⁰ₓ(t,y,u) d(ρ.kernel t)(u)` is continuous.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.6.1. -/
theorem continuous_averagedRunningCovector (P : Problem E V W) (D : P.SmoothData)
    (hD : P.DerivativeContinuity D) (ρ : P.Relaxed) (t : ℝ) :
    Continuous (P.averagedRunningCovector D ρ t) := by
  unfold averagedRunningCovector
  refine Continuous.const_smul ?_ P.horizon⁻¹
  exact continuous_kernel_average_param
    (P.continuous_slice_uncurry _
      (g := fun z => (D.runningDerivative z.1.1 (z.1.2, z.2)).comp
        (ContinuousLinearMap.inl ℝ E V))
      (hD.continuous_runningDerivative.clm_comp_const (ContinuousLinearMap.inl ℝ E V)))

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- **Joint continuity of the pointwise-defect state covector built from the averaged data.**
For each fixed time `t`, `(x,v) ↦ cx t x - 2K ⟨v - F t x, Fx t x ·⟩` is continuous, with
`cx = T⁻¹ ∫ f⁰ₓ`, `F = ∫ f`, `Fx = ∫ fₓ`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.6.1, (11.6.9). -/
theorem continuous_pointwiseDefectStateCovector (P : Problem E V W) (D : P.SmoothData)
    (hD : P.DerivativeContinuity D) (ρ : P.Relaxed) (K : ℝ) (t : ℝ) :
    Continuous fun q : E × E =>
      pointwiseDefectStateCovector (P.averagedRunningCovector D ρ) (P.averagedDynamics ρ)
        (P.averagedDynamicsDerivative D ρ) K t q.1 q.2 := by
  unfold pointwiseDefectStateCovector
  have hfst : Continuous (Prod.fst : E × E → E) := continuous_fst
  have hcx := (P.continuous_averagedRunningCovector D hD ρ t).comp hfst
  have hF := (P.continuous_averagedDynamics ρ t).comp hfst
  have hFx := (P.continuous_averagedDynamicsDerivative D hD ρ t).comp hfst
  have hin : Continuous fun q : E × E => innerSL ℝ (q.2 - P.averagedDynamics ρ t q.1) :=
    (ContinuousLinearMap.continuous (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)).comp
      (continuous_snd.sub hF)
  exact hcx.sub ((hin.clm_comp hFx).const_smul (2 * K))

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- **Joint continuity of the pointwise-defect velocity covector built from the averaged
dynamics.**  For each fixed time `t`, `(x,v) ↦ 2⟨v - r t, ·⟩ + 2K⟨v - F t x, ·⟩` is continuous,
with `F = ∫ f`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.6.1, (11.6.8). -/
theorem continuous_pointwiseDefectVelocityCovector (P : Problem E V W) (ρ : P.Relaxed)
    (r : ℝ → E) (K : ℝ) (t : ℝ) :
    Continuous fun q : E × E =>
      pointwiseDefectVelocityCovector (P.averagedDynamics ρ) r K t q.1 q.2 := by
  unfold pointwiseDefectVelocityCovector
  have hfst : Continuous (Prod.fst : E × E → E) := continuous_fst
  have hF := (P.continuous_averagedDynamics ρ t).comp hfst
  have hL : Continuous (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.continuous (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)
  exact ((hL.comp (continuous_snd.sub continuous_const)).const_smul (2 : ℝ)).add
    ((hL.comp (continuous_snd.sub hF)).const_smul (2 * K))

end Problem

end OptimalControl.BoundedState
