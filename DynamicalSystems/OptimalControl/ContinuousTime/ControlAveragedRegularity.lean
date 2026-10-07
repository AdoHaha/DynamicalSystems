/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.VelocityPointwiseMinimizerEndpointConditions
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Regularity of the control-averaged data of a bounded-state problem

The endpoint/traversality chain of `VelocityPointwiseEndpointConditions.lean` and
`VelocityPointwiseMinimizerEndpointConditions.lean` takes as a hypothesis
`PointwiseDefectRegularity`, which asserts that the averaged data
`c t y = T⁻¹ ∫ f⁰(t,y,u) d(ρ.kernel t)(u)` and `F t y = ∫ f(t,y,u) d(ρ.kernel t)(u)`
are jointly measurable in `(t,y)`, are `C¹` in `y` with derivatives the averaged derivatives
`∫ f⁰ₓ` and `∫ fₓ`, and are locally bounded.

This file *derives* that hypothesis from the primitive assumptions of Berkovitz & Medhin's
Assumption 11.6.1 (via Assumption 11.5.1): joint continuity of `f`, `f⁰` and their spatial
derivatives in `(t,x,u)`, the compactness of the control set `Ω`, and measurability of the
conditional law `t ↦ ρ.kernel t`.  In particular it proves

* parametric measurability of a kernel average `(t,y) ↦ ∫ u, g (t,y,u) d(ρ.kernel t)(u)`
  (not only its `t`-measurability, which is `RelaxedControl.stronglyMeasurable_average`);
* differentiation under the kernel on the compact control set, from joint continuity of the
  derivative and `HasFDerivAt` of the slices;
* local boundedness of the averaged data and derivatives from continuity on the compact tubes.

The last section re-states the endpoint conditions with the primitive
`Problem.DerivativeContinuity` hypothesis in place of `PointwiseDefectRegularity`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.5.1,
Assumption 11.6.1, Theorem 11.6.3.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology Interval
open ProbabilityTheory

namespace OptimalControl.BoundedState

/-! ## Parametric measurability of a kernel average -/

/-- **Parametric measurability of a kernel average.**  If `g` is jointly strongly measurable in
`((t,y),u)`, then `(t,y) ↦ ∫ u, g ((t,y),u) d(ρ.kernel t)(u)` is strongly measurable.  This is
the `(t,y)`-parametric strengthening of `RelaxedControl.stronglyMeasurable_average`, obtained by
viewing the kernel as a kernel on the product time–state space via `Kernel.comap` along the
projection.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.6.1. -/
theorem RelaxedControl.stronglyMeasurable_kernel_average_param
    {τ U A : Type*} [MeasurableSpace τ] [MeasurableSpace U] [StandardBorelSpace U] [Nonempty U]
    {ν : ProbabilityMeasure τ} (ρ : RelaxedControl τ U ν) [MeasurableSpace A]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : (τ × A) × U → G} (hg : StronglyMeasurable g) :
    StronglyMeasurable (fun p : τ × A => ∫ u, g (p, u) ∂ρ.kernel p.1) := by
  have h := hg.integral_kernel_prod_right'
    (κ := Kernel.comap ρ.kernel Prod.fst measurable_fst)
  simpa only [Kernel.comap_apply] using h

/-! ## Differentiation under the kernel -/

/-- **Differentiation under a kernel integral on a compact control space.**  Let `F` be a family of
continuous functions of the control, `F'` a continuous family of candidate derivatives, and suppose
the slices `x ↦ F x u` are differentiable with derivative `F' x u` for every control `u`, with a
uniform bound `C` on `‖F' x u‖` for `x` in a neighbourhood `s` of `y₀`.  Then
`x ↦ ∫ u, F x u dν(u)` is differentiable at `y₀` with derivative `∫ u, F' y₀ u dν(u)`.

The proof is `hasFDerivAt_integral_of_dominated_of_fderiv_le` with the constant dominating
function `C`; compactness of the control space makes every continuous slice integrable.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.6.1. -/
theorem hasFDerivAt_kernel_average
    {U : Type*} [MeasurableSpace U] [TopologicalSpace U] [BorelSpace U] [CompactSpace U]
    [SecondCountableTopology U] {ν : Measure U} [IsProbabilityMeasure ν]
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {F : E → U → G} {F' : E → U → E →L[ℝ] G} {y₀ : E} {s : Set E} {C : ℝ}
    (hs : s ∈ 𝓝 y₀) (hF_cont : ∀ x, Continuous (F x)) (hF'_cont : ∀ x, Continuous (F' x))
    (h_bound : ∀ x ∈ s, ∀ u, ‖F' x u‖ ≤ C)
    (h_diff : ∀ u, ∀ x ∈ s, HasFDerivAt (F · u) (F' x u) x) :
    HasFDerivAt (fun x => ∫ u, F x u ∂ν) (∫ u, F' y₀ u ∂ν) y₀ := by
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) hs
    (Eventually.of_forall fun x => (hF_cont x).aestronglyMeasurable)
    ((hF_cont y₀).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    ((hF'_cont y₀).aestronglyMeasurable)
    (Eventually.of_forall fun u x hx => h_bound x hx u)
    (integrable_const C)
    (Eventually.of_forall fun u x hx => h_diff u x hx)

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]
  {P : Problem E V W}

namespace Problem

/-- **Primitive joint continuity of the derivative data** (Berkovitz & Medhin, Assumption 11.6.1
via Assumption 11.5.1): the spatial derivatives `fₓ` and `f⁰ₓ` of the problem data are jointly
continuous in `(t,x,u)`.  Together with compactness of `Ω` this is what replaces the absent
joint-continuity field of `Problem.SmoothData` (which only records `HasFDerivAt` of the slices). -/
structure DerivativeContinuity (P : Problem E V W) (D : P.SmoothData) : Prop where
  /-- Joint continuity of `fₓ(t,x,u)`. -/
  continuous_dynamicsDerivative :
    Continuous (fun z : (P.Time × E) × V => D.dynamicsDerivative z.1.1 z.1.2 z.2)
  /-- Joint continuity of the joint running-cost derivative `(f⁰ₓ, f⁰_u)`. -/
  continuous_runningDerivative :
    Continuous (fun z : (P.Time × E) × V => D.runningDerivative z.1.1 (z.1.2, z.2))

/-- The control-averaged state derivative `∫ fₓ(t,y,u) dν_t` of the averaged dynamics. -/
noncomputable def averagedDynamicsDerivative (P : Problem E V W) (D : P.SmoothData)
    (ρ : P.Relaxed) (t : ℝ) (y : E) : E →L[ℝ] E :=
  ∫ u, D.dynamicsDerivative (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le t) y (u : V)
    ∂ρ.kernel (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le t)

/-- The control-averaged running-cost state covector `T⁻¹ ∫ f⁰ₓ(t,y,u) dν_t`, the derivative of
`t, y ↦ T⁻¹ ∫ f⁰(t,y,u) dν_t`. -/
noncomputable def averagedRunningCovector (P : Problem E V W) (D : P.SmoothData)
    (ρ : P.Relaxed) (t : ℝ) (y : E) : E →L[ℝ] ℝ :=
  P.horizon⁻¹ • ∫ u,
    (D.runningDerivative (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le t) (y, (u : V))).comp
      (ContinuousLinearMap.inl ℝ E V)
    ∂ρ.kernel (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le t)

end Problem

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
/-- **Bounding a continuous field on a compact time–state–control tube.**  For a continuous
`f : (Time × E) × V → G`, on the tube `‖y‖ ≤ R` there is a nonnegative constant dominating
`‖f ((t,y),u)‖` uniformly in time and control. -/
theorem exists_bound_on_tube {G : Type*} [NormedAddCommGroup G]
    (f : (P.Time × E) × V → G) (hf : Continuous f) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : P.Time) (y : E) (u : P.Control),
      ‖y‖ ≤ R → ‖f ((t, y), (u : V))‖ ≤ C := by
  have hK : IsCompact (((univ : Set P.Time) ×ˢ Metric.closedBall (0 : E) R) ×ˢ P.controlSet) :=
    (isCompact_univ.prod (isCompact_closedBall (0 : E) R)).prod P.controlSet_compact
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t y u hy => ?_⟩
  have hmem : ((t, y), (u : V)) ∈
      ((univ : Set P.Time) ×ˢ Metric.closedBall (0 : E) R) ×ˢ P.controlSet :=
    ⟨⟨mem_univ _, Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hy)⟩, u.2⟩
  exact (hC _ hmem).trans (le_max_left _ _)

namespace Problem

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
/-- Bound on the dynamics derivative data on a state ball. -/
theorem exists_bound_dynamicsDerivative (P : Problem E V W) (D : P.SmoothData)
    (hD : P.DerivativeContinuity D) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : P.Time) (y : E) (u : P.Control),
      ‖y‖ ≤ R → ‖D.dynamicsDerivative t y (u : V)‖ ≤ C :=
  exists_bound_on_tube (fun z : (P.Time × E) × V => D.dynamicsDerivative z.1.1 z.1.2 z.2)
    hD.continuous_dynamicsDerivative R

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
/-- Bound on the running-cost derivative data on a state ball. -/
theorem exists_bound_runningDerivative (P : Problem E V W) (D : P.SmoothData)
    (hD : P.DerivativeContinuity D) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : P.Time) (y : E) (u : P.Control),
      ‖y‖ ≤ R → ‖D.runningDerivative t (y, (u : V))‖ ≤ C :=
  exists_bound_on_tube (fun z : (P.Time × E) × V => D.runningDerivative z.1.1 (z.1.2, z.2))
    hD.continuous_runningDerivative R

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
/-- Bound on the averaged dynamics integrand on a state ball. -/
theorem exists_bound_dynamics (P : Problem E V W) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : P.Time) (y : E) (u : P.Control),
      ‖y‖ ≤ R → ‖P.dynamics t y (u : V)‖ ≤ C :=
  exists_bound_on_tube (fun z : (P.Time × E) × V => P.dynamics z.1.1 z.1.2 z.2)
    P.dynamics_continuous R

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] in
/-- Bound on the averaged running-cost integrand on a state ball. -/
theorem exists_bound_runningCost (P : Problem E V W) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : P.Time) (y : E) (u : P.Control),
      ‖y‖ ≤ R → ‖P.runningCost t y (u : V)‖ ≤ C :=
  exists_bound_on_tube (fun z : (P.Time × E) × V => P.runningCost z.1.1 z.1.2 z.2)
    P.runningCost_continuous R

/-! ## Joint measurability of the averaged fields -/

omit [CompleteSpace E] in
/-- Parametric strong measurability of a control-averaged continuous field along the clamped time
projection: `(t,y) ↦ ∫ u, g (proj t, y, u) d(ρ.kernel (proj t))(u)`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.6.1. -/
theorem stronglyMeasurable_averaged_param {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (ρ : P.Relaxed) (g : (P.Time × E) × P.Control → G) (hg : Continuous g) :
    StronglyMeasurable (fun p : ℝ × E =>
      ∫ u, g ((Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le p.1, p.2), u)
        ∂ρ.kernel (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le p.1)) := by
  have h₁ : StronglyMeasurable (fun q : P.Time × E => ∫ u, g (q, u) ∂ρ.kernel q.1) :=
    RelaxedControl.stronglyMeasurable_kernel_average_param
      (ν := horizonProbability P.horizon P.horizon_pos) ρ hg.stronglyMeasurable
  have hφ : Measurable (fun p : ℝ × E =>
      (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le p.1, p.2)) := by fun_prop
  exact h₁.comp_measurable hφ

omit [CompleteSpace E] in
/-- Joint measurability of the averaged running cost. -/
theorem measurable_averagedRunningCost (P : Problem E V W) (ρ : P.Relaxed) :
    Measurable (fun p : ℝ × E => P.averagedRunningCost ρ p.1 p.2) := by
  have h := P.stronglyMeasurable_averaged_param ρ
    (fun z : (P.Time × E) × P.Control => P.runningCost z.1.1 z.1.2 (z.2 : V))
    (P.runningCost_continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  exact h.measurable

omit [CompleteSpace E] in
/-- Joint measurability of the averaged dynamics. -/
theorem measurable_averagedDynamics (P : Problem E V W) (ρ : P.Relaxed) :
    Measurable (fun p : ℝ × E => P.averagedDynamics ρ p.1 p.2) := by
  have h := P.stronglyMeasurable_averaged_param ρ
    (fun z : (P.Time × E) × P.Control => P.dynamics z.1.1 z.1.2 (z.2 : V))
    (P.dynamics_continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  exact h.measurable

omit [CompleteSpace E] in
/-- Joint measurability of the averaged dynamics derivative. -/
theorem measurable_averagedDynamicsDerivative (P : Problem E V W) (D : P.SmoothData)
    (hD : P.DerivativeContinuity D) (ρ : P.Relaxed) :
    Measurable (fun p : ℝ × E => P.averagedDynamicsDerivative D ρ p.1 p.2) := by
  have h := P.stronglyMeasurable_averaged_param ρ
    (fun z : (P.Time × E) × P.Control => D.dynamicsDerivative z.1.1 z.1.2 (z.2 : V))
    (hD.continuous_dynamicsDerivative.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
  exact h.measurable

omit [CompleteSpace E] in
/-- Joint measurability of the averaged running-cost state covector. -/
theorem measurable_averagedRunningCovector (P : Problem E V W) (D : P.SmoothData)
    (hD : P.DerivativeContinuity D) (ρ : P.Relaxed) :
    Measurable (fun p : ℝ × E => P.averagedRunningCovector D ρ p.1 p.2) := by
  have h := P.stronglyMeasurable_averaged_param ρ
    (fun z : (P.Time × E) × P.Control =>
      (D.runningDerivative z.1.1 (z.1.2, (z.2 : V))).comp (ContinuousLinearMap.inl ℝ E V))
    ((hD.continuous_runningDerivative.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).clm_comp_const
        (ContinuousLinearMap.inl ℝ E V))
  have h' : StronglyMeasurable (fun p : ℝ × E => P.horizon⁻¹ • ∫ u,
      (D.runningDerivative (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le p.1)
        (p.2, (u : V))).comp (ContinuousLinearMap.inl ℝ E V)
      ∂ρ.kernel (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le p.1)) :=
    h.const_smul P.horizon⁻¹
  exact h'.measurable

/-! ## Differentiation under the kernel for the problem data -/

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The norm of a Bochner integral against a conditional law is bounded by the uniform bound on
the integrand (the kernel is a probability kernel).

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.6.1. -/
theorem norm_integral_kernel_le (P : Problem E V W) (ρ : P.Relaxed) (q : P.Time)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : P.Control → G} {C : ℝ}
    (hg : ∀ u, ‖g u‖ ≤ C) :
    ‖∫ u, g u ∂ρ.kernel q‖ ≤ C := by
  calc ‖∫ u, g u ∂ρ.kernel q‖ ≤ C * (ρ.kernel q).real univ :=
        norm_integral_le_of_norm_le_const (Eventually.of_forall hg)
    _ = C := by rw [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one]

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- The averaged dynamics is differentiable in the state with derivative the averaged dynamics
derivative.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.6.1. -/
theorem hasFDerivAt_averagedDynamics (P : Problem E V W) (D : P.SmoothData)
    (hD : P.DerivativeContinuity D) (ρ : P.Relaxed) (t : ℝ) (y : E) :
    HasFDerivAt (P.averagedDynamics ρ t) (P.averagedDynamicsDerivative D ρ t y) y := by
  set q : P.Time := Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le t with hq
  obtain ⟨C, _hC0, hC⟩ := P.exists_bound_dynamicsDerivative D hD (‖y‖ + 1)
  have h := hasFDerivAt_kernel_average (ν := ρ.kernel q)
    (F := fun x (u : P.Control) => P.dynamics q x (u : V))
    (F' := fun x (u : P.Control) => D.dynamicsDerivative q x (u : V))
    (y₀ := y) (s := Metric.ball y 1) (C := C)
    (Metric.ball_mem_nhds y one_pos)
    (fun x => P.dynamics_continuous.comp
      ((continuous_const : Continuous (fun _ : P.Control => (q, x))).prodMk continuous_subtype_val))
    (fun x => hD.continuous_dynamicsDerivative.comp
      ((continuous_const : Continuous (fun _ : P.Control => (q, x))).prodMk continuous_subtype_val))
    (fun x hx u => hC q x u (by
      have hd := Metric.mem_ball.mp hx
      calc ‖x‖ = ‖y + (x - y)‖ := by rw [add_sub_cancel]
        _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
        _ = ‖y‖ + dist x y := by rw [dist_eq_norm]
        _ ≤ ‖y‖ + 1 := by linarith))
    (fun u x _ => D.dynamics_hasFDerivAt q (u : V) x)
  exact h

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- The averaged running cost `T⁻¹ ∫ f⁰` is differentiable in the state with derivative the
averaged running-cost state covector `T⁻¹ ∫ f⁰ₓ`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.6.1. -/
theorem hasFDerivAt_averagedRunningCost (P : Problem E V W) (D : P.SmoothData)
    (hD : P.DerivativeContinuity D) (ρ : P.Relaxed) (t : ℝ) (y : E) :
    HasFDerivAt (fun y => P.horizon⁻¹ * P.averagedRunningCost ρ t y)
      (P.averagedRunningCovector D ρ t y) y := by
  set q : P.Time := Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le t with hq
  obtain ⟨C, hC0, hC⟩ := P.exists_bound_runningDerivative D hD (‖y‖ + 1)
  have h := hasFDerivAt_kernel_average (ν := ρ.kernel q)
    (F := fun x (u : P.Control) => P.runningCost q x (u : V))
    (F' := fun x (u : P.Control) =>
      (D.runningDerivative q (x, (u : V))).comp (ContinuousLinearMap.inl ℝ E V))
    (y₀ := y) (s := Metric.ball y 1) (C := C)
    (Metric.ball_mem_nhds y one_pos)
    (fun x => P.runningCost_continuous.comp
      ((continuous_const : Continuous (fun _ : P.Control => (q, x))).prodMk continuous_subtype_val))
    (fun x => (hD.continuous_runningDerivative.comp
        ((continuous_const : Continuous
          (fun _ : P.Control => (q, x))).prodMk continuous_subtype_val)).clm_comp_const
        (ContinuousLinearMap.inl ℝ E V))
    (fun x hx u => by
      have hd := Metric.mem_ball.mp hx
      have hxy : ‖x‖ ≤ ‖y‖ + 1 := by
        calc ‖x‖ = ‖y + (x - y)‖ := by rw [add_sub_cancel]
          _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
          _ = ‖y‖ + dist x y := by rw [dist_eq_norm]
          _ ≤ ‖y‖ + 1 := by linarith
      calc ‖(D.runningDerivative q (x, (u : V))).comp
            (ContinuousLinearMap.inl ℝ E V)‖
          ≤ ‖D.runningDerivative q (x, (u : V))‖ * ‖ContinuousLinearMap.inl ℝ E V‖ :=
            ContinuousLinearMap.opNorm_comp_le _ (ContinuousLinearMap.inl ℝ E V)
        _ ≤ C * 1 := mul_le_mul (hC q x u hxy) (ContinuousLinearMap.norm_inl_le_one ℝ E V)
            (norm_nonneg _) hC0
        _ = C := mul_one C)
    (fun u x _ => HasFDerivAt.comp (f := fun e : E => (e, (u : V))) x
      (D.running_hasFDerivAt q (x, (u : V))) (hasFDerivAt_prodMk_left x (u : V)))
  exact h.const_mul P.horizon⁻¹

omit [CompleteSpace E] in
/-- **`PointwiseDefectRegularity` from primitive joint continuity (Assumption 11.6.1).**  If the
spatial derivatives `fₓ`, `f⁰ₓ` are jointly continuous in `(t,x,u)`, the control set `Ω` is
compact, and the reference velocity `r` is measurable and `L²`, then the control-averaged data of
the problem are jointly measurable, `C¹` in the state with averaged derivatives, and locally
bounded --- i.e. the hypotheses used by `VelocityPointwiseEndpointConditions.lean` /
`VelocityPointwiseMinimizerEndpointConditions.lean` hold with
`c = T⁻¹ ∫ f⁰`, `cx = T⁻¹ ∫ f⁰ₓ`, `F = ∫ f`, `Fx = ∫ fₓ`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.5.1,
Assumption 11.6.1. -/
theorem pointwiseDefectRegularity (P : Problem E V W) (D : P.SmoothData)
    (hD : P.DerivativeContinuity D) (ρ : P.Relaxed) (r : ℝ → E) (hr : Measurable r)
    (hrLp : MemLp r 2 (ACEulerLagrange.timeMeasure P.horizon)) (K : ℝ) (hK : 0 ≤ K) :
    PointwiseDefectRegularity P.horizon
      (fun t y => P.horizon⁻¹ * P.averagedRunningCost ρ t y)
      (P.averagedRunningCovector D ρ)
      (P.averagedDynamics ρ)
      (P.averagedDynamicsDerivative D ρ)
      r K where
  hasFDerivAt_c := fun t y => P.hasFDerivAt_averagedRunningCost D hD ρ t y
  hasFDerivAt_F := fun t y => P.hasFDerivAt_averagedDynamics D hD ρ t y
  measurable_c := (P.measurable_averagedRunningCost ρ).const_mul P.horizon⁻¹
  measurable_cx := P.measurable_averagedRunningCovector D hD ρ
  measurable_F := P.measurable_averagedDynamics ρ
  measurable_Fx := P.measurable_averagedDynamicsDerivative D hD ρ
  measurable_r := hr
  memLp_r := hrLp
  nonneg_K := hK
  bounded := by
    intro R
    obtain ⟨C₁, hC₁0, hC₁⟩ := P.exists_bound_runningDerivative D hD R
    obtain ⟨C₂, hC₂0, hC₂⟩ := P.exists_bound_dynamics R
    obtain ⟨C₃, hC₃0, hC₃⟩ := P.exists_bound_dynamicsDerivative D hD R
    have hTinv : 0 ≤ P.horizon⁻¹ := inv_nonneg.mpr P.horizon_pos.le
    refine ⟨max (P.horizon⁻¹ * C₁) (max C₂ C₃), ?_, fun t y hy => ?_⟩
    · exact le_max_of_le_left (mul_nonneg hTinv hC₁0)
    · refine ⟨?_, ?_, ?_⟩
      · have hb : ∀ u : P.Control,
            ‖(D.runningDerivative (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le t)
              (y, (u : V))).comp (ContinuousLinearMap.inl ℝ E V)‖ ≤ C₁ := by
          intro u
          calc ‖(D.runningDerivative (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le t)
                (y, (u : V))).comp (ContinuousLinearMap.inl ℝ E V)‖
              ≤ ‖D.runningDerivative (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le t)
                  (y, (u : V))‖ * ‖ContinuousLinearMap.inl ℝ E V‖ :=
                ContinuousLinearMap.opNorm_comp_le _ (ContinuousLinearMap.inl ℝ E V)
            _ ≤ C₁ * 1 := mul_le_mul (hC₁ _ y u hy) (ContinuousLinearMap.norm_inl_le_one ℝ E V)
                (norm_nonneg _) hC₁0
            _ = C₁ := mul_one C₁
        have hint := P.norm_integral_kernel_le ρ
          (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le t) hb
        rw [Problem.averagedRunningCovector, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg hTinv]
        exact (mul_le_mul_of_nonneg_left hint hTinv).trans (le_max_left _ _)
      · have hb : ∀ u : P.Control,
            ‖P.dynamics (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le t) y (u : V)‖ ≤ C₂ :=
          fun u => hC₂ _ y u hy
        have hint := P.norm_integral_kernel_le ρ
          (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le t) hb
        rw [Problem.averagedDynamics]
        exact hint.trans (le_trans (le_max_left C₂ C₃) (le_max_right _ _))
      · have hb : ∀ u : P.Control,
            ‖D.dynamicsDerivative (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le t) y
              (u : V)‖ ≤ C₃ := fun u => hC₃ _ y u hy
        have hint := P.norm_integral_kernel_le ρ
          (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le t) hb
        rw [Problem.averagedDynamicsDerivative]
        exact hint.trans (le_trans (le_max_right C₂ C₃) (le_max_right _ _))

end Problem

namespace VelocityTrajectory

/-! ## Endpoint conditions with the primitive regularity hypothesis -/

/-- **Endpoint conditions (11.6.15)-(11.6.16) for a strict-interior minimiser of the
pointwise-defect penalty, from primitive Assumption 11.6.1 data.**  This is
`VelocityTrajectory.pointwisePenaltyMinimizer_endpointConditions` with the
`PointwiseDefectRegularity` hypothesis replaced by the primitive joint continuity of the spatial
derivatives `fₓ`, `f⁰ₓ` (`Problem.DerivativeContinuity`), primitive measurability of the reference
velocity `φ₀'` and `0 ≤ K`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.5.1,
Assumption 11.6.1, Lemma 11.3.4, (11.6.8)-(11.6.16). -/
theorem pointwisePenaltyMinimizer_endpointConditions_of_derivativeContinuity
    (P : Problem E V W) (D : P.SmoothData) (hD : P.DerivativeContinuity D)
    (K ε : ℝ) (hK : 0 ≤ K) (γ₀ γ : VelocityTrajectory P) (ρ₀ ρ : P.Relaxed) (hε : 0 ≤ ε)
    (hr : Measurable γ₀.velocity)
    (hmin : ∀ (γ' : VelocityTrajectory P) (ρ' : P.Relaxed),
      InVelocityControlTube P γ₀ ρ₀ ε γ' ρ' →
        Problem.velocityPenalizedPointwise P K ε γ₀ ρ₀ γ ρ ≤
          Problem.velocityPenalizedPointwise P K ε γ₀ ρ₀ γ' ρ')
    (hmem : InVelocityControlTube P γ₀ ρ₀ ε γ ρ)
    (hv : (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2) < ε ^ 2)
    (hi : dist γ.initial γ₀.initial < ε)
    (hstate : ∀ t : P.Time, P.stateConstraint t (γ.value t) < 0)
    (D₁ D₂ : E →L[ℝ] W)
    (hT : HasFDerivAt (fun q : E × E => P.endpointConstraint q.1 q.2)
      (D₁.comp (ContinuousLinearMap.fst ℝ E E) + D₂.comp (ContinuousLinearMap.snd ℝ E E))
      (γ.value 0, γ.value P.horizon)) :
    ∃ p : ℝ → E →L[ℝ] ℝ,
      ContinuousOn p (Icc (0 : ℝ) P.horizon) ∧
      (∀ᵐ t ∂(ACEulerLagrange.timeMeasure P.horizon), p t =
        (2 : ℝ) • innerSL ℝ (γ.velocity t - γ₀.velocity t)
          + (2 * K) • innerSL ℝ (γ.velocity t - Problem.averagedDynamics P ρ t (γ.value t))) ∧
      (∀ᵐ t ∂(ACEulerLagrange.timeMeasure P.horizon), HasDerivAt p
        (P.averagedRunningCovector D ρ t (γ.value t) - (2 * K) •
          (innerSL ℝ (γ.velocity t - Problem.averagedDynamics P ρ t (γ.value t))).comp
            (P.averagedDynamicsDerivative D ρ t (γ.value t))) t) ∧
      p 0 = (2 : ℝ) • innerSL ℝ (γ.value 0 - γ₀.initial)
        + (2 * K) • (innerSL ℝ (P.endpointConstraint (γ.value 0) (γ.value P.horizon))).comp D₁ ∧
      p P.horizon = -((2 * K) •
        (innerSL ℝ (P.endpointConstraint (γ.value 0) (γ.value P.horizon))).comp D₂) :=
  pointwisePenaltyMinimizer_endpointConditions P K ε γ₀ γ ρ₀ ρ hε hmin hmem
    hv hi hstate (P.pointwiseDefectRegularity D hD ρ γ₀.velocity hr γ₀.memLp_velocity K hK)
    D₁ D₂ hT

/-- **Endpoint conditions for a strict-interior minimiser of the anchored pointwise-defect
penalty, from primitive Assumption 11.6.1 data.**  This is
`VelocityTrajectory.pointwisePenaltyMinimizer_endpointConditions_anchored` with the
`PointwiseDefectRegularity` hypothesis replaced by `Problem.DerivativeContinuity`, primitive
measurability of `φ₀'` and `0 ≤ K`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.5.1,
Assumption 11.6.1, Lemma 11.3.4, (11.6.8)-(11.6.16). -/
theorem pointwisePenaltyMinimizer_endpointConditions_anchored_of_derivativeContinuity
    (P : Problem E V W) (D : P.SmoothData) (hD : P.DerivativeContinuity D)
    (K ε : ℝ) (hK : 0 ≤ K) (γ₀ γ : VelocityTrajectory P) (ρ₀ ρ : P.Relaxed) (hε : 0 ≤ ε)
    (hr : Measurable γ₀.velocity)
    (hmin : ∀ (γ' : VelocityTrajectory P) (ρ' : P.Relaxed),
      InVelocityControlTube P γ₀ ρ₀ ε γ' ρ' →
        Problem.velocityPenalizedPointwise P K ε γ₀ ρ₀ γ ρ + K * dist γ.initial P.initial ^ 2 ≤
          Problem.velocityPenalizedPointwise P K ε γ₀ ρ₀ γ' ρ'
            + K * dist γ'.initial P.initial ^ 2)
    (hmem : InVelocityControlTube P γ₀ ρ₀ ε γ ρ)
    (hv : (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2) < ε ^ 2)
    (hi : dist γ.initial γ₀.initial < ε)
    (hstate : ∀ t : P.Time, P.stateConstraint t (γ.value t) < 0)
    (D₁ D₂ : E →L[ℝ] W)
    (hT : HasFDerivAt (fun q : E × E => P.endpointConstraint q.1 q.2)
      (D₁.comp (ContinuousLinearMap.fst ℝ E E) + D₂.comp (ContinuousLinearMap.snd ℝ E E))
      (γ.value 0, γ.value P.horizon)) :
    ∃ p : ℝ → E →L[ℝ] ℝ,
      ContinuousOn p (Icc (0 : ℝ) P.horizon) ∧
      (∀ᵐ t ∂(ACEulerLagrange.timeMeasure P.horizon), p t =
        (2 : ℝ) • innerSL ℝ (γ.velocity t - γ₀.velocity t)
          + (2 * K) • innerSL ℝ (γ.velocity t - Problem.averagedDynamics P ρ t (γ.value t))) ∧
      (∀ᵐ t ∂(ACEulerLagrange.timeMeasure P.horizon), HasDerivAt p
        (P.averagedRunningCovector D ρ t (γ.value t) - (2 * K) •
          (innerSL ℝ (γ.velocity t - Problem.averagedDynamics P ρ t (γ.value t))).comp
            (P.averagedDynamicsDerivative D ρ t (γ.value t))) t) ∧
      p 0 = (2 : ℝ) • innerSL ℝ (γ.value 0 - γ₀.initial)
        + (2 * K) • innerSL ℝ (γ.value 0 - P.initial)
        + (2 * K) • (innerSL ℝ (P.endpointConstraint (γ.value 0) (γ.value P.horizon))).comp D₁ ∧
      p P.horizon = -((2 * K) •
        (innerSL ℝ (P.endpointConstraint (γ.value 0) (γ.value P.horizon))).comp D₂) :=
  pointwisePenaltyMinimizer_endpointConditions_anchored P K ε γ₀ γ ρ₀ ρ hε hmin
    hmem hv hi hstate (P.pointwiseDefectRegularity D hD ρ γ₀.velocity hr γ₀.memLp_velocity K hK)
    D₁ D₂ hT

end VelocityTrajectory

end OptimalControl.BoundedState
