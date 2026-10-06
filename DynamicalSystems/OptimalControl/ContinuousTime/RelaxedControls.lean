/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.Probability.Kernel.Disintegration.Integral
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Relaxed controls with a fixed time marginal

A relaxed control is a probability measure on time × control whose time
marginal is prescribed. Its compactness is proved, not assumed as compactness
of a feasible trajectory space. Every measurable ordinary control gives a
graph measure. Conversely, disintegration constructs an actual Markov kernel
and proves the integral identities needed by controlled dynamics and costs.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped Topology MeasureTheory

namespace OptimalControl

/-- Occupation-measure model with a fixed time marginal. The time measure can
be normalized Lebesgue measure on a finite horizon. -/
abbrev RelaxedControl (τ U : Type*) [MeasurableSpace τ] [MeasurableSpace U]
    (ν : ProbabilityMeasure τ) :=
  {ρ : ProbabilityMeasure (τ × U) // ρ.map Prod.fst = ν}

namespace RelaxedControl

variable {τ U : Type*} [MeasurableSpace τ] [MeasurableSpace U]
  {ν : ProbabilityMeasure τ}

/-- The underlying occupation measure. -/
noncomputable def measure (ρ : RelaxedControl τ U ν) : Measure (τ × U) := ρ.1.toMeasure

instance (ρ : RelaxedControl τ U ν) : IsProbabilityMeasure ρ.measure :=
  inferInstanceAs (IsProbabilityMeasure ρ.1.toMeasure)

/-- The defining marginal relation, as an equality of measures. -/
theorem fst_measure (ρ : RelaxedControl τ U ν) : ρ.measure.fst = ν.toMeasure := by
  exact congrArg ProbabilityMeasure.toMeasure ρ.2

/-- Every measurable ordinary control embeds by its actual graph measure. -/
noncomputable def ofControl (ν : ProbabilityMeasure τ) (u : τ → U) (hu : Measurable u) :
    RelaxedControl τ U ν := by
  refine ⟨ν.map (fun t => (t, u t)), ?_⟩
  apply Subtype.ext
  change Measure.map Prod.fst (Measure.map (fun t => (t, u t)) ν.toMeasure) = ν.toMeasure
  have hg : Measurable (fun t => (t, u t)) := measurable_id.prodMk hu
  rw [Measure.map_map measurable_fst hg]
  exact Measure.map_id

/-- Evaluation of an occupation integral on an ordinary control. -/
theorem integral_ofControl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν : ProbabilityMeasure τ) (u : τ → U) (hu : Measurable u)
    (f : τ × U → E) (hf : AEStronglyMeasurable f (ofControl ν u hu).measure) :
    (∫ z, f z ∂(ofControl ν u hu).measure) = ∫ t, f (t, u t) ∂ν := by
  exact integral_map (measurable_id.prodMk hu).aemeasurable hf

/-- A constant ordinary control witnesses nonemptiness whenever at least one
control value exists. No topological assumptions are needed for this fact. -/
instance [Nonempty U] : Nonempty (RelaxedControl τ U ν) :=
  ⟨ofControl ν (fun _ => Classical.choice (inferInstance : Nonempty U)) measurable_const⟩

section Compactness

variable [MetricSpace τ] [BorelSpace τ] [CompactSpace τ]
  [MetricSpace U] [BorelSpace U] [CompactSpace U]

omit [CompactSpace τ] in
/-- Fixed-marginal occupation measures form a closed subset of the weak
probability-measure space. -/
theorem isClosed_fixedMarginal (ν : ProbabilityMeasure τ) :
    IsClosed {ρ : ProbabilityMeasure (τ × U) | ρ.map Prod.fst = ν} :=
  isClosed_eq (ProbabilityMeasure.continuous_map continuous_fst) continuous_const

/-- Actual weak compactness of relaxed controls with compact time and control
spaces. This does not postulate compactness of a feasible trajectory set. -/
instance : CompactSpace (RelaxedControl τ U ν) :=
  isCompact_iff_compactSpace.mp (isClosed_fixedMarginal (U := U) ν).isCompact

end Compactness

section Disintegration

variable [StandardBorelSpace U] [Nonempty U]

/-- A disintegration constructed by Mathlib's standard-Borel conditional
kernel theorem; it is not additional input to the control problem. -/
noncomputable def kernel (ρ : RelaxedControl τ U ν) : Kernel τ U := ρ.measure.condKernel

instance (ρ : RelaxedControl τ U ν) : IsMarkovKernel ρ.kernel :=
  inferInstanceAs (IsMarkovKernel ρ.measure.condKernel)

/-- The constructed conditional kernel reconstructs the occupation measure
with the prescribed time marginal. -/
theorem disintegrate (ρ : RelaxedControl τ U ν) : ν.toMeasure ⊗ₘ ρ.kernel = ρ.measure := by
  rw [← ρ.fst_measure]
  exact Measure.disintegrate ρ.measure ρ.measure.condKernel

/-- Full-horizon disintegration of Bochner integrals, including vector-valued
dynamics as well as real running costs. -/
theorem integral_kernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : RelaxedControl τ U ν) {f : τ × U → E} (hf : Integrable f ρ.measure) :
    (∫ t, ∫ u, f (t, u) ∂ρ.kernel t ∂ν) = ∫ z, f z ∂ρ.measure := by
  rw [← ρ.fst_measure]
  exact Measure.integral_condKernel hf

/-- Restricted-time disintegration; used for actual integral dynamics rather
than only terminal or moment constraints. -/
theorem setIntegral_kernel {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : RelaxedControl τ U ν) {s : Set τ} (hs : MeasurableSet s)
    {f : τ × U → E} (hf : IntegrableOn f (s ×ˢ univ) ρ.measure) :
    (∫ t in s, ∫ u, f (t, u) ∂ρ.kernel t ∂ν) = ∫ z in s ×ˢ univ, f z ∂ρ.measure := by
  rw [← ρ.fst_measure]
  exact Measure.setIntegral_condKernel_univ_right hs hf

/-- The averaged field is strongly measurable whenever the original field is
jointly strongly measurable. -/
theorem stronglyMeasurable_average {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : RelaxedControl τ U ν) {f : τ × U → E} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun t => ∫ u, f (t, u) ∂ρ.kernel t) :=
  hf.integral_kernel_prod_right'

end Disintegration

end RelaxedControl
end OptimalControl
