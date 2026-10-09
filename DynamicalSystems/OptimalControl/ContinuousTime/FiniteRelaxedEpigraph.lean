/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.MeasureTheory.MeasurableEpigraphLift
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.Sequences
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Measurable finite-atomic relaxed epigraph realization

Finite relaxed controls consist of nonnegative weights summing to one and a
finite tuple of atoms in the original state-dependent control graph. Closedness
of this concrete graph, continuity of weighted dynamics, and lower semicontinuity
of weighted running costs are derived from the original data. The sigma-compact
measurable selector then produces actual measurable weights and atoms.

This implements the finite-control part of BM Theorem 5.4.4, Step 4. The number
of atoms is explicit; the book uses the state dimension plus two.
-/

@[expose] public section

open Set Filter MeasureTheory Topology
open scoped BigOperators

namespace OptimalControl

/-- A finite relaxed control is a tuple of real weights and a tuple of atoms.
The simplex and graph constraints are imposed by `finiteRelaxedControlGraph`. -/
abbrev FiniteRelaxedControl (N : ℕ) (U : Type*) := (Fin N → ℝ) × (Fin N → U)

/-- The original graph constraint at every atom, with the actual simplex conditions. -/
def finiteRelaxedControlGraph {T E U : Type*} (N : ℕ) (C : Set (T × E × U)) :
    Set (T × E × FiniteRelaxedControl N U) :=
  {p | (∀ i, 0 ≤ p.2.2.1 i) ∧ (∑ i, p.2.2.1 i) = 1 ∧
    ∀ i, (p.1, p.2.1, p.2.2.2 i) ∈ C}

/-- The actual finite weighted dynamics. -/
def finiteRelaxedVelocity {T E U : Type*} [AddCommMonoid E] [Module ℝ E]
    (N : ℕ) (f : T × E × U → E) (p : T × E × FiniteRelaxedControl N U) : E :=
  ∑ i, p.2.2.1 i • f (p.1, p.2.1, p.2.2.2 i)

/-- The actual finite weighted running cost. -/
def finiteRelaxedRunningCost {T E U : Type*} (N : ℕ) (c : T × E × U → ℝ)
    (p : T × E × FiniteRelaxedControl N U) : ℝ :=
  ∑ i, p.2.2.1 i * c (p.1, p.2.1, p.2.2.2 i)

/-- Multiplication by a continuous nonnegative weight preserves real-valued
lower semicontinuity on a set, including points where the weight is zero. -/
theorem lowerSemicontinuousOn_mul_continuous_nonneg
    {Z : Type*} [TopologicalSpace Z] (s : Set Z) (w c : Z → ℝ)
    (hw : ContinuousOn w s) (hnonneg : ∀ z ∈ s, 0 ≤ w z)
    (hc : LowerSemicontinuousOn c s) :
    LowerSemicontinuousOn (fun z ↦ w z * c z) s := by
  intro z hz y hy
  obtain ⟨u, v, hu, hwu, hv, hcv, huv⟩ : ∃ u v : Set ℝ,
      IsOpen u ∧ w z ∈ u ∧ IsOpen v ∧ c z ∈ v ∧
        u ×ˢ v ⊆ {p : ℝ × ℝ | y < p.1 * p.2} :=
    mem_nhds_prod_iff'.mp (continuous_mul.continuousAt (isOpen_Ioi.mem_nhds hy))
  obtain ⟨q, hq, hqv⟩ : ∃ q < c z, Ioc q (c z) ⊆ v :=
    exists_Ioc_subset_of_mem_nhds (hv.mem_nhds hcv) ⟨c z - 1, by linarith⟩
  filter_upwards [(hw z hz).eventually (hu.mem_nhds hwu), hc z hz q hq,
    self_mem_nhdsWithin] with a hwa hca has
  have hmin : min (c a) (c z) ∈ v := hqv ⟨lt_min hca hq, min_le_right _ _⟩
  have hprod : (w a, min (c a) (c z)) ∈ u ×ˢ v := ⟨hwa, hmin⟩
  exact (huv hprod).trans_le
    (mul_le_mul_of_nonneg_left (min_le_left _ _) (hnonneg a has))

/-- Upper hemicontinuity with closed values gives a closed original control
constraint graph. This derives the graph input used by finite relaxed selection. -/
theorem isClosed_controlGraph_of_upperHemicontinuous
    {T E U : Type*} [MetricSpace T] [MetricSpace E] [MetricSpace U]
    (Ω : T × E → Set U) (hΩ : UpperHemicontinuous Ω)
    (hclosed : ∀ p, IsClosed (Ω p)) :
    IsClosed {p : T × E × U | p.2.2 ∈ Ω (p.1, p.2.1)} := by
  apply isSeqClosed_iff_isClosed.mp
  intro seq p hmem hp
  exact UpperHemicontinuousAt.mem_of_tendsto (hΩ (p.1, p.2.1)) (hclosed _)
    (((continuous_fst.tendsto p).comp hp).prodMk_nhds
      ((continuous_snd.fst.tendsto p).comp hp))
    ((Eventually.of_forall hmem).frequently) ((continuous_snd.snd.tendsto p).comp hp)

section Topology

variable {T E U : Type*} [TopologicalSpace T] [TopologicalSpace E]
  [TopologicalSpace U]

/-- A closed original control graph gives a closed finite relaxed graph, without
compactness of the original controls. -/
theorem isClosed_finiteRelaxedControlGraph (N : ℕ) (C : Set (T × E × U))
    (hC : IsClosed C) : IsClosed (finiteRelaxedControlGraph N C) := by
  have hweights : IsClosed {p : T × E × FiniteRelaxedControl N U |
      ∀ i, 0 ≤ p.2.2.1 i} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i ↦ isClosed_le continuous_const (by fun_prop)
  have hsum : IsClosed {p : T × E × FiniteRelaxedControl N U |
      (∑ i, p.2.2.1 i) = 1} := isClosed_eq (by fun_prop) continuous_const
  have hatoms : IsClosed {p : T × E × FiniteRelaxedControl N U |
      ∀ i, (p.1, p.2.1, p.2.2.2 i) ∈ C} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i ↦ hC.preimage (by fun_prop)
  exact hweights.inter (hsum.inter hatoms)

variable [AddCommMonoid E] [Module ℝ E] [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- The finite weighted dynamics are continuous when the original dynamics are. -/
theorem continuous_finiteRelaxedVelocity (N : ℕ) (f : T × E × U → E)
    (hf : Continuous f) : Continuous (finiteRelaxedVelocity N f) := by
  unfold finiteRelaxedVelocity
  apply continuous_finsetSum
  intro i _
  exact (by fun_prop : Continuous (fun p : T × E × FiniteRelaxedControl N U ↦ p.2.2.1 i)).smul
    (hf.comp (by fun_prop))

omit [AddCommMonoid E] [Module ℝ E] [ContinuousAdd E] [ContinuousSMul ℝ E] in
/-- Lower semicontinuity of the original cost on its graph gives lower
semicontinuity of the weighted cost on the concrete finite relaxed graph. -/
theorem lowerSemicontinuousOn_finiteRelaxedRunningCost (N : ℕ)
    (C : Set (T × E × U)) (c : T × E × U → ℝ) (hc : LowerSemicontinuousOn c C) :
    LowerSemicontinuousOn (finiteRelaxedRunningCost N c) (finiteRelaxedControlGraph N C) := by
  unfold finiteRelaxedRunningCost
  apply lowerSemicontinuousOn_sum
  intro i _
  apply lowerSemicontinuousOn_mul_continuous_nonneg
  · exact (by fun_prop : Continuous
      (fun p : T × E × FiniteRelaxedControl N U ↦ p.2.2.1 i)).continuousOn
  · exact fun p hp ↦ hp.1 i
  · exact hc.comp (by fun_prop : Continuous
      (fun p : T × E × FiniteRelaxedControl N U ↦ (p.1, p.2.1, p.2.2.2 i))).continuousOn
      (fun p hp ↦ hp.2.2 i)

end Topology

/-- Nonnegative original graph costs give nonnegative finite relaxed graph costs. -/
theorem finiteRelaxedRunningCost_nonneg {T E U : Type*} (N : ℕ)
    (C : Set (T × E × U)) (c : T × E × U → ℝ) (hc : ∀ p ∈ C, 0 ≤ c p)
    (p : T × E × FiniteRelaxedControl N U) (hp : p ∈ finiteRelaxedControlGraph N C) :
    0 ≤ finiteRelaxedRunningCost N c p :=
  Finset.sum_nonneg fun i _ ↦ mul_nonneg (hp.1 i) (hc _ (hp.2.2 i))

/-- A common lower bound for original atom costs is a lower bound for the actual
weighted running cost, using the simplex normalization. -/
theorem finiteRelaxedRunningCost_ge_of_lowerBound {T E U : Type*} (N : ℕ)
    (C : Set (T × E × U)) (c : T × E × U → ℝ)
    (p : T × E × FiniteRelaxedControl N U) (hp : p ∈ finiteRelaxedControlGraph N C)
    (β : ℝ) (hlower : ∀ u, (p.1, p.2.1, u) ∈ C → β ≤ c (p.1, p.2.1, u)) :
    β ≤ finiteRelaxedRunningCost N c p := by
  calc
    β = ∑ i, p.2.2.1 i * β := by rw [← Finset.sum_mul, hp.2.1, one_mul]
    _ ≤ finiteRelaxedRunningCost N c p := Finset.sum_le_sum fun i _ ↦
      mul_le_mul_of_nonneg_left (hlower _ (hp.2.2 i)) (hp.1 i)

section Selection

variable {A T E U : Type*} [MeasurableSpace A] {μ : Measure A}
  [MetricSpace T] [MeasurableSpace T] [BorelSpace T]
  [SigmaCompactSpace T] [SecondCountableTopology T]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SigmaCompactSpace E] [SecondCountableTopology E]
  [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [SigmaCompactSpace U]

/-- The sigma-compact epigraph selector, instantiated with concrete weights and
atoms, constructs a measurable finite relaxed control. Its simplex constraints,
atom admissibility, and weighted dynamics/cost identities are conclusions.
This is the finite-atomic realization in BM Theorem 5.4.4, Step 4. -/
theorem exists_measurable_finiteRelaxedControl_of_epigraph (N : ℕ)
    (C : Set (T × E × U)) (f : T × E × U → E) (c : T × E × U → ℝ)
    (hC : IsClosed C) (hf : Continuous f) (hc : LowerSemicontinuousOn c C)
    (τ : A → T) (x v : A → E) (costLimit : A → ℝ)
    (hτ : Measurable τ) (hx : Measurable x) (hv : Measurable v) (hcost : Measurable costLimit)
    (hμ : μ ≠ 0)
    (hepi : ∀ᵐ t ∂μ, (v t, costLimit t) ∈
      DynamicalSystems.MeasurableLift.constrainedVelocityCostSet
        (finiteRelaxedControlGraph N C) (finiteRelaxedVelocity N f)
        (finiteRelaxedRunningCost N c) (τ t) (x t)) :
    ∃ (weights : A → Fin N → ℝ) (atoms : A → Fin N → U),
      Measurable weights ∧ Measurable atoms ∧ ∀ᵐ t ∂μ,
        (∀ i, 0 ≤ weights t i) ∧ (∑ i, weights t i) = 1 ∧
        (∀ i, (τ t, x t, atoms t i) ∈ C) ∧
        (∑ i, weights t i • f (τ t, x t, atoms t i)) = v t ∧
        (∑ i, weights t i * c (τ t, x t, atoms t i)) ≤ costLimit t := by
  obtain ⟨u, hu, hreal⟩ :=
    DynamicalSystems.MeasurableLift.exists_measurable_control_of_constrained_epigraph
      (finiteRelaxedControlGraph N C) (finiteRelaxedVelocity N f)
      (finiteRelaxedRunningCost N c) (isClosed_finiteRelaxedControlGraph N C hC)
      (continuous_finiteRelaxedVelocity N f hf)
      (lowerSemicontinuousOn_finiteRelaxedRunningCost N C c hc)
      τ x v costLimit hτ hx hv hcost hμ hepi
  exact ⟨fun t ↦ (u t).1, fun t ↦ (u t).2, measurable_fst.comp hu,
    measurable_snd.comp hu, hreal.mono fun t ht ↦
      ⟨ht.1.1, ht.1.2.1, ht.1.2.2, ht.2.1, ht.2.2⟩⟩

/-- A measurable map that lies almost everywhere in a closed cost graph has an
almost everywhere strongly measurable cost, even when lower semicontinuity is
assumed only on that graph. -/
theorem aestronglyMeasurable_cost_of_ae_mem_closed_graph
    {Z : Type*} [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    (C : Set Z) (hC : IsClosed C) (c : Z → ℝ) (hc : LowerSemicontinuousOn c C)
    (q : A → Z) (hq : Measurable q) (hmem : ∀ᵐ t ∂μ, q t ∈ C) :
    AEStronglyMeasurable (fun t ↦ c (q t)) μ := by
  classical
  have hcm : Measurable (fun z : C ↦ c z) :=
    (lowerSemicontinuous_restrict_iff.mpr hc).measurable
  let cext (z : Z) : ℝ := if hz : z ∈ C then c (⟨z, hz⟩ : C) else 0
  have hext : Measurable cext := hcm.dite measurable_const hC.measurableSet
  apply (hext.comp hq).aestronglyMeasurable.congr
  filter_upwards [hmem] with t ht
  change cext (q t) = c (q t)
  simp only [cext, dite_eq_left ht]

/-- A merely integrable lower bound and epigraph domination imply integrability
of the realized finite relaxed cost. The original cost is only lower
semicontinuous on its graph; no continuity of the lower bound is assumed. -/
theorem exists_integrable_finiteRelaxedControl_of_integrable_lowerBound (N : ℕ)
    (C : Set (T × E × U)) (f : T × E × U → E) (c : T × E × U → ℝ)
    (hC : IsClosed C) (hf : Continuous f) (hc : LowerSemicontinuousOn c C)
    (τ : A → T) (x v : A → E) (costLimit : A → ℝ)
    (hτ : Measurable τ) (hx : Measurable x)
    (hv : Integrable v μ) (hcost : Integrable costLimit μ)
    (β : A → ℝ) (hβ : Integrable β μ)
    (hlower : ∀ᵐ t ∂μ, ∀ u, (τ t, x t, u) ∈ C → β t ≤ c (τ t, x t, u))
    (hμ : μ ≠ 0)
    (hepi : ∀ᵐ t ∂μ, (v t, costLimit t) ∈
      DynamicalSystems.MeasurableLift.constrainedVelocityCostSet
        (finiteRelaxedControlGraph N C) (finiteRelaxedVelocity N f)
        (finiteRelaxedRunningCost N c) (τ t) (x t)) :
    ∃ u : A → FiniteRelaxedControl N U, Measurable u ∧
      (∀ᵐ t ∂μ, (τ t, x t, u t) ∈ finiteRelaxedControlGraph N C) ∧
      (∀ᵐ t ∂μ, finiteRelaxedVelocity N f (τ t, x t, u t) = v t) ∧
      Integrable (fun t ↦ finiteRelaxedVelocity N f (τ t, x t, u t)) μ ∧
      Integrable (fun t ↦ finiteRelaxedRunningCost N c (τ t, x t, u t)) μ ∧
      (∫ t, finiteRelaxedRunningCost N c (τ t, x t, u t) ∂μ) ≤ ∫ t, costLimit t ∂μ := by
  let vrep := hv.aestronglyMeasurable.mk v
  let crep := hcost.aestronglyMeasurable.mk costLimit
  have hvr : v =ᵐ[μ] vrep := hv.aestronglyMeasurable.ae_eq_mk
  have hcr : costLimit =ᵐ[μ] crep := hcost.aestronglyMeasurable.ae_eq_mk
  have hepirep : ∀ᵐ t ∂μ, (vrep t, crep t) ∈
      DynamicalSystems.MeasurableLift.constrainedVelocityCostSet
        (finiteRelaxedControlGraph N C) (finiteRelaxedVelocity N f)
        (finiteRelaxedRunningCost N c) (τ t) (x t) := by
    filter_upwards [hepi, hvr, hcr] with t ht hvt hct
    rwa [← hvt, ← hct]
  obtain ⟨weights, atoms, hw, ha, hreal⟩ :=
    exists_measurable_finiteRelaxedControl_of_epigraph N C f c hC hf hc
      τ x vrep crep hτ hx hv.aestronglyMeasurable.measurable_mk
      hcost.aestronglyMeasurable.measurable_mk hμ hepirep
  let u t := (weights t, atoms t)
  have hu : Measurable u := hw.prodMk ha
  have hgraph : ∀ᵐ t ∂μ, (τ t, x t, u t) ∈ finiteRelaxedControlGraph N C :=
    hreal.mono fun t ht ↦ ⟨ht.1, ht.2.1, ht.2.2.1⟩
  have hvel : ∀ᵐ t ∂μ, finiteRelaxedVelocity N f (τ t, x t, u t) = v t := by
    filter_upwards [hreal, hvr] with t ht hvt
    exact ht.2.2.2.1.trans hvt.symm
  have hdom : ∀ᵐ t ∂μ, finiteRelaxedRunningCost N c (τ t, x t, u t) ≤ costLimit t := by
    filter_upwards [hreal, hcr] with t ht hct
    exact ht.2.2.2.2.trans_eq hct.symm
  have hrunmeas := aestronglyMeasurable_cost_of_ae_mem_closed_graph
    (finiteRelaxedControlGraph N C) (isClosed_finiteRelaxedControlGraph N C hC)
    (finiteRelaxedRunningCost N c) (lowerSemicontinuousOn_finiteRelaxedRunningCost N C c hc)
    (fun t ↦ (τ t, x t, u t)) (hτ.prodMk (hx.prodMk hu)) hgraph
  have hbelow : ∀ᵐ t ∂μ, β t ≤ finiteRelaxedRunningCost N c (τ t, x t, u t) := by
    filter_upwards [hgraph, hlower] with t ht hlt
    exact finiteRelaxedRunningCost_ge_of_lowerBound N C c _ ht (β t) hlt
  have hrunint : Integrable (fun t ↦ finiteRelaxedRunningCost N c (τ t, x t, u t)) μ := by
    apply (hcost.norm.add hβ.norm).mono' hrunmeas
    filter_upwards [hbelow, hdom] with t ht hdt
    change ‖finiteRelaxedRunningCost N c (τ t, x t, u t)‖ ≤
      ‖costLimit t‖ + ‖β t‖
    simp only [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · have h := neg_abs_le (β t)
      have hcostzero := norm_nonneg (costLimit t)
      rw [Real.norm_eq_abs] at *
      linarith
    · have h := le_abs_self (costLimit t)
      have hβzero := norm_nonneg (β t)
      rw [Real.norm_eq_abs] at *
      linarith
  have hveleq : (fun t ↦ finiteRelaxedVelocity N f (τ t, x t, u t)) =ᵐ[μ] v := hvel
  exact ⟨u, hu, hgraph, hvel, hv.congr hveleq.symm, hrunint,
    integral_mono_ae hrunint hcost hdom⟩

/-- Finite relaxed epigraph realization also supplies integrability of the actual
weighted running cost and velocity and the running-cost bound. Integrability
of the cost is derived from nonnegative original costs and epigraph domination;
it is not an extra recovery assumption. -/
theorem exists_integrable_finiteRelaxedControl_of_epigraph (N : ℕ)
    (C : Set (T × E × U)) (f : T × E × U → E) (c : T × E × U → ℝ)
    (hC : IsClosed C) (hf : Continuous f) (hc : LowerSemicontinuousOn c C)
    (hnonneg : ∀ p ∈ C, 0 ≤ c p)
    (τ : A → T) (x v : A → E) (costLimit : A → ℝ)
    (hτ : Measurable τ) (hx : Measurable x)
    (hv : Integrable v μ) (hcost : Integrable costLimit μ) (hμ : μ ≠ 0)
    (hepi : ∀ᵐ t ∂μ, (v t, costLimit t) ∈
      DynamicalSystems.MeasurableLift.constrainedVelocityCostSet
        (finiteRelaxedControlGraph N C) (finiteRelaxedVelocity N f)
        (finiteRelaxedRunningCost N c) (τ t) (x t)) :
    ∃ u : A → FiniteRelaxedControl N U, Measurable u ∧
      (∀ᵐ t ∂μ, (τ t, x t, u t) ∈ finiteRelaxedControlGraph N C) ∧
      (∀ᵐ t ∂μ, finiteRelaxedVelocity N f (τ t, x t, u t) = v t) ∧
      Integrable (fun t ↦ finiteRelaxedVelocity N f (τ t, x t, u t)) μ ∧
      Integrable (fun t ↦ finiteRelaxedRunningCost N c (τ t, x t, u t)) μ ∧
      (∫ t, finiteRelaxedRunningCost N c (τ t, x t, u t) ∂μ) ≤ ∫ t, costLimit t ∂μ := by
  exact exists_integrable_finiteRelaxedControl_of_integrable_lowerBound
    N C f c hC hf hc τ x v costLimit hτ hx hv hcost (fun _ ↦ 0) (integrable_zero A ℝ μ)
    (Eventually.of_forall fun t u hu ↦ hnonneg _ hu) hμ hepi

end Selection

end OptimalControl
