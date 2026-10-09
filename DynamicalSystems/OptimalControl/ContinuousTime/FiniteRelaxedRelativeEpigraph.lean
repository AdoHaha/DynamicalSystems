/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.MeasureTheory.MeasurableRelativeEpigraphLift
public import DynamicalSystems.OptimalControl.ContinuousTime.FiniteRelaxedEpigraph

/-!
# Relative-domain realization of finite relaxed controls

The dynamics need only be continuous on the original admissible graph. Both
ordinary and finite relaxed controls are realized using the original lower
semicontinuous cost, with a merely integrable lower bound. In particular, the
lower bound is not subtracted before applying the topological selector.
-/

@[expose] public section

open Set Filter MeasureTheory Topology DynamicalSystems.MeasurableLift
open scoped BigOperators

namespace OptimalControl

section RelativeContinuity

variable {T E U : Type*} [TopologicalSpace T] [TopologicalSpace E]
  [TopologicalSpace U] [AddCommMonoid E] [Module ℝ E]
  [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- Weighted dynamics are continuous on the finite relaxed graph when the
original dynamics are continuous only on their original admissible graph. -/
theorem continuousOn_finiteRelaxedVelocity (N : ℕ) (C : Set (T × E × U))
    (f : T × E × U → E) (hf : ContinuousOn f C) :
    ContinuousOn (finiteRelaxedVelocity N f) (finiteRelaxedControlGraph N C) := by
  unfold finiteRelaxedVelocity
  apply continuousOn_finsetSum
  intro i _
  exact (by fun_prop : Continuous
    (fun p : T × E × FiniteRelaxedControl N U ↦ p.2.2.1 i)).continuousOn.smul
      (hf.comp (by fun_prop : Continuous
        (fun p : T × E × FiniteRelaxedControl N U ↦
          (p.1, p.2.1, p.2.2.2 i))).continuousOn (fun p hp ↦ hp.2.2 i))

end RelativeContinuity

section Selection

variable {A T E U : Type*} [MeasurableSpace A] {μ : Measure A}
  [MetricSpace T] [MeasurableSpace T] [BorelSpace T]
  [SigmaCompactSpace T] [SecondCountableTopology T]
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SigmaCompactSpace E] [SecondCountableTopology E]
  [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [SigmaCompactSpace U]

/-- Relative dynamics continuity and epigraph domination recover an ordinary
measurable control with integrable velocity and cost. The lower bound is merely
integrable; the selector is applied to the original, unshifted cost. -/
theorem exists_integrable_control_of_constrained_epigraph_of_continuousOn
    (C : Set (T × E × U)) (f : T × E × U → E) (c : T × E × U → ℝ)
    (hC : IsClosed C) (hf : ContinuousOn f C) (hc : LowerSemicontinuousOn c C)
    (τ : A → T) (x v : A → E) (costLimit : A → ℝ)
    (hτ : Measurable τ) (hx : Measurable x)
    (hv : Integrable v μ) (hcost : Integrable costLimit μ)
    (β : A → ℝ) (hβ : Integrable β μ)
    (hlower : ∀ᵐ t ∂μ, ∀ u, (τ t, x t, u) ∈ C → β t ≤ c (τ t, x t, u))
    (hμ : μ ≠ 0)
    (hepi : ∀ᵐ t ∂μ, (v t, costLimit t) ∈
      constrainedVelocityCostSet C f c (τ t) (x t)) :
    ∃ u : A → U, Measurable u ∧
      (∀ᵐ t ∂μ, (τ t, x t, u t) ∈ C) ∧
      (∀ᵐ t ∂μ, f (τ t, x t, u t) = v t) ∧
      Integrable (fun t ↦ f (τ t, x t, u t)) μ ∧
      Integrable (fun t ↦ c (τ t, x t, u t)) μ ∧
      (∫ t, c (τ t, x t, u t) ∂μ) ≤ ∫ t, costLimit t ∂μ := by
  let vrep := hv.aestronglyMeasurable.mk v
  let crep := hcost.aestronglyMeasurable.mk costLimit
  have hvr : v =ᵐ[μ] vrep := hv.aestronglyMeasurable.ae_eq_mk
  have hcr : costLimit =ᵐ[μ] crep := hcost.aestronglyMeasurable.ae_eq_mk
  have hepirep : ∀ᵐ t ∂μ, (vrep t, crep t) ∈
      constrainedVelocityCostSet C f c (τ t) (x t) := by
    filter_upwards [hepi, hvr, hcr] with t ht hvt hct
    rwa [← hvt, ← hct]
  obtain ⟨u, hu, hreal⟩ :=
    exists_measurable_control_of_constrained_epigraph_of_continuousOn
      C f c hC hf hc τ x vrep crep hτ hx hv.aestronglyMeasurable.measurable_mk
      hcost.aestronglyMeasurable.measurable_mk hμ hepirep
  have hgraph : ∀ᵐ t ∂μ, (τ t, x t, u t) ∈ C := hreal.mono fun _ ht ↦ ht.1
  have hvel : (fun t ↦ f (τ t, x t, u t)) =ᵐ[μ] v := by
    filter_upwards [hreal, hvr] with t ht hvt
    exact ht.2.1.trans hvt.symm
  have hdom : ∀ᵐ t ∂μ, c (τ t, x t, u t) ≤ costLimit t := by
    filter_upwards [hreal, hcr] with t ht hct
    exact ht.2.2.trans_eq hct.symm
  have hrunmeas := aestronglyMeasurable_cost_of_ae_mem_closed_graph C hC c hc
    (fun t ↦ (τ t, x t, u t)) (hτ.prodMk (hx.prodMk hu)) hgraph
  have hbelow : ∀ᵐ t ∂μ, β t ≤ c (τ t, x t, u t) := by
    filter_upwards [hgraph, hlower] with t ht hlt
    exact hlt (u t) ht
  have hrunint : Integrable (fun t ↦ c (τ t, x t, u t)) μ := by
    apply (hcost.norm.add hβ.norm).mono' hrunmeas
    filter_upwards [hbelow, hdom] with t ht hdt
    change ‖c (τ t, x t, u t)‖ ≤ ‖costLimit t‖ + ‖β t‖
    simp only [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · have h := neg_abs_le (β t)
      have hcostzero := abs_nonneg (costLimit t)
      linarith
    · have h := le_abs_self (costLimit t)
      have hβzero := abs_nonneg (β t)
      linarith
  exact ⟨u, hu, hgraph, hvel, hv.congr hvel.symm, hrunint,
    integral_mono_ae hrunint hcost hdom⟩

variable [NormedSpace ℝ E]

/-- Actual measurable simplex weights and admissible atoms are selected under
relative continuity of the original dynamics. -/
theorem exists_measurable_finiteRelaxedControl_of_epigraph_of_continuousOn (N : ℕ)
    (C : Set (T × E × U)) (f : T × E × U → E) (c : T × E × U → ℝ)
    (hC : IsClosed C) (hf : ContinuousOn f C) (hc : LowerSemicontinuousOn c C)
    (τ : A → T) (x v : A → E) (costLimit : A → ℝ)
    (hτ : Measurable τ) (hx : Measurable x) (hv : Measurable v)
    (hcost : Measurable costLimit) (hμ : μ ≠ 0)
    (hepi : ∀ᵐ t ∂μ, (v t, costLimit t) ∈
      constrainedVelocityCostSet
        (finiteRelaxedControlGraph N C) (finiteRelaxedVelocity N f)
        (finiteRelaxedRunningCost N c) (τ t) (x t)) :
    ∃ (weights : A → Fin N → ℝ) (atoms : A → Fin N → U),
      Measurable weights ∧ Measurable atoms ∧ ∀ᵐ t ∂μ,
        (∀ i, 0 ≤ weights t i) ∧ (∑ i, weights t i) = 1 ∧
        (∀ i, (τ t, x t, atoms t i) ∈ C) ∧
        (∑ i, weights t i • f (τ t, x t, atoms t i)) = v t ∧
        (∑ i, weights t i * c (τ t, x t, atoms t i)) ≤ costLimit t := by
  obtain ⟨u, hu, hreal⟩ :=
    exists_measurable_control_of_constrained_epigraph_of_continuousOn
      (finiteRelaxedControlGraph N C) (finiteRelaxedVelocity N f)
      (finiteRelaxedRunningCost N c) (isClosed_finiteRelaxedControlGraph N C hC)
      (continuousOn_finiteRelaxedVelocity N C f hf)
      (lowerSemicontinuousOn_finiteRelaxedRunningCost N C c hc)
      τ x v costLimit hτ hx hv hcost hμ hepi
  exact ⟨fun t ↦ (u t).1, fun t ↦ (u t).2, measurable_fst.comp hu,
    measurable_snd.comp hu, hreal.mono fun t ht ↦
      ⟨ht.1.1, ht.1.2.1, ht.1.2.2, ht.2.1, ht.2.2⟩⟩

/-- The finite relaxed selector needs neither global dynamics continuity nor a
continuous lower bound for the running cost. Integrability is a conclusion. -/
theorem exists_integrable_finiteRelaxedControl_of_integrable_lowerBound_of_continuousOn
    (N : ℕ) (C : Set (T × E × U)) (f : T × E × U → E) (c : T × E × U → ℝ)
    (hC : IsClosed C) (hf : ContinuousOn f C) (hc : LowerSemicontinuousOn c C)
    (τ : A → T) (x v : A → E) (costLimit : A → ℝ)
    (hτ : Measurable τ) (hx : Measurable x)
    (hv : Integrable v μ) (hcost : Integrable costLimit μ)
    (β : A → ℝ) (hβ : Integrable β μ)
    (hlower : ∀ᵐ t ∂μ, ∀ u, (τ t, x t, u) ∈ C → β t ≤ c (τ t, x t, u))
    (hμ : μ ≠ 0)
    (hepi : ∀ᵐ t ∂μ, (v t, costLimit t) ∈
      constrainedVelocityCostSet
        (finiteRelaxedControlGraph N C) (finiteRelaxedVelocity N f)
        (finiteRelaxedRunningCost N c) (τ t) (x t)) :
    ∃ u : A → FiniteRelaxedControl N U, Measurable u ∧
      (∀ᵐ t ∂μ, (τ t, x t, u t) ∈ finiteRelaxedControlGraph N C) ∧
      (∀ᵐ t ∂μ, finiteRelaxedVelocity N f (τ t, x t, u t) = v t) ∧
      Integrable (fun t ↦ finiteRelaxedVelocity N f (τ t, x t, u t)) μ ∧
      Integrable (fun t ↦ finiteRelaxedRunningCost N c (τ t, x t, u t)) μ ∧
      (∫ t, finiteRelaxedRunningCost N c (τ t, x t, u t) ∂μ) ≤
        ∫ t, costLimit t ∂μ := by
  apply exists_integrable_control_of_constrained_epigraph_of_continuousOn
    (finiteRelaxedControlGraph N C) (finiteRelaxedVelocity N f)
    (finiteRelaxedRunningCost N c) (isClosed_finiteRelaxedControlGraph N C hC)
    (continuousOn_finiteRelaxedVelocity N C f hf)
    (lowerSemicontinuousOn_finiteRelaxedRunningCost N C c hc)
    τ x v costLimit hτ hx hv hcost β hβ ?_ hμ hepi
  filter_upwards [hlower] with t ht
  intro u hu
  exact finiteRelaxedRunningCost_ge_of_lowerBound N C c _ hu (β t) ht

end Selection

end OptimalControl
