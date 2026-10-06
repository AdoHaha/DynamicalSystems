/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.MeasureTheory.MeasurableArgmin
public import Mathlib.Probability.Kernel.Disintegration.Integral
public import Mathlib.Probability.Kernel.Disintegration.StandardBorel
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# Fiberwise replacement of a relaxed control and the common a.e. Hamiltonian minimum

Let `ν` be a finite measure on `T × U` (a *relaxed control*: `ν.fst` is its time marginal and
`U` a compact metric control set) and `h : T → U → ℝ` a Carathéodory integrand dominated by a
function `G` integrable for the time marginal (a Hamiltonian integrand).

* `DynamicalSystems.RelaxedHamiltonian.disintegration`,
  `DynamicalSystems.RelaxedHamiltonian.integral_eq_integral_condKernel`: the
  disintegration `ν = ν.fst ⊗ₘ k` along the time marginal with probability fibres `k t` and
  `∫ f dν = ∫ (∫ f(t,·) d(k t)) d(ν.fst)`.
* `DynamicalSystems.RelaxedHamiltonian.integral_compProd_le_of_fiber_le`: replacing the fibres `k t`
  by any Markov kernel `k'` that does not increase the fibre integrals a.e. does not increase the
  integral, and keeps the time marginal.
* `DynamicalSystems.RelaxedHamiltonian.exists_replacement_le`: replacing `ν` by the selector
  measure `(t, s t) ♯ ν.fst` (a deterministic control) with `s` a measurable argmin selector
  does not increase the integral; its value is `∫ min_u h(t, u) dt`.
* `DynamicalSystems.RelaxedHamiltonian.ae_integral_condKernel_eq_minValue`,
  `DynamicalSystems.RelaxedHamiltonian.ae_forall_integral_condKernel_le`: if `ν` minimises
  `∫ h dν` among measures with the same time marginal, then for `ν.fst`-a.e. `t` the fibre
  average satisfies `∫ h(t,·) d(k t) = min_u h(t,u)` and hence `≤ h(t, v)` for **every** `v`
  on one common a.e. set (Bressan–Piccoli §11.6, equation (11.6.13); §11.4 Hamiltonian minimum).
* `DynamicalSystems.RelaxedHamiltonian.ae_ae_le_of_optimal`: the fibre `k t` is supported on the
  argmin of `h t`, for a.e. `t`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory Set Filter Topology
open scoped ProbabilityTheory
open ProbabilityTheory (Kernel IsMarkovKernel)
open DynamicalSystems.MeasurableArgmin
open scoped ENNReal

namespace DynamicalSystems.RelaxedHamiltonian

variable {T U : Type*} [MeasurableSpace T] [MetricSpace U] [CompactSpace U] [Nonempty U]
  [MeasurableSpace U] [BorelSpace U]

/-! ### Disintegration of a relaxed control along its time marginal -/

section Disintegration

variable (ν : Measure (T × U)) [IsFiniteMeasure ν]

/-- **Disintegration of a relaxed control**: `ν = ν.fst ⊗ₘ k` with `k = ν.condKernel` a Markov
kernel (probability fibres `k t`). -/
theorem disintegration : ν.fst ⊗ₘ ν.condKernel = ν := ν.disintegrate ν.condKernel

/-- The fibres of the disintegration of a finite measure are probability measures. -/
instance (t : T) : IsProbabilityMeasure (ν.condKernel t) := inferInstance

/-- `∫ f dν = ∫ (∫ f(t, ·) d(k t)) d(ν.fst)`. -/
theorem integral_eq_integral_condKernel {f : T × U → ℝ} (hf : Integrable f ν) :
    ∫ x, f x ∂ν = ∫ t, ∫ u, f (t, u) ∂(ν.condKernel t) ∂ν.fst :=
  (Measure.integral_condKernel hf).symm

end Disintegration

/-! ### Carathéodory integrands and domination -/

section Integrand

variable {h : T → U → ℝ}

lemma measurable_uncurry (hm : ∀ u, Measurable fun t => h t u) (hc : ∀ t, Continuous (h t)) :
    Measurable (Function.uncurry h) := by
  have := measurable_uncurry_of_continuous_of_measurable (u := fun u t => h t u) hc hm
  exact this.comp measurable_swap

lemma integrable_uncurry {G : T → ℝ} (hm : ∀ u, Measurable fun t => h t u)
    (hc : ∀ t, Continuous (h t)) (hG : ∀ t u, |h t u| ≤ G t) {ν : Measure (T × U)}
    (hGi : Integrable G ν.fst) : Integrable (Function.uncurry h) ν := by
  have hGν : Integrable (fun x : T × U => G x.1) ν :=
    (integrable_map_measure hGi.aestronglyMeasurable measurable_fst.aemeasurable).1 hGi
  refine hGν.mono' (measurable_uncurry hm hc).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  simpa [Real.norm_eq_abs, Function.uncurry] using hG x.1 x.2

lemma abs_minValue_le {G : T → ℝ} (hG : ∀ t u, |h t u| ≤ G t) (t : T) :
    |minValue h t| ≤ G t := by
  obtain ⟨u₀⟩ := ‹Nonempty U›
  have hlo : ∀ u, -G t ≤ h t u := fun u => by linarith [(abs_le.mp (hG t u)).1]
  have hbdd : BddBelow (Set.range (h t)) := ⟨-G t, by rintro _ ⟨u, rfl⟩; exact hlo u⟩
  refine abs_le.mpr ⟨le_ciInf hlo, ?_⟩
  exact (ciInf_le hbdd u₀).trans (abs_le.mp (hG t u₀)).2

lemma integrable_minValue {G : T → ℝ} (hm : ∀ u, Measurable fun t => h t u)
    (hc : ∀ t, Continuous (h t)) (hG : ∀ t u, |h t u| ≤ G t) {μ : Measure T}
    (hGi : Integrable G μ) : Integrable (minValue h) μ :=
  hGi.mono' (measurable_minValue hm hc).aestronglyMeasurable
    (Eventually.of_forall fun t => by simpa [Real.norm_eq_abs] using abs_minValue_le hG t)

/-- For a probability fibre the fibre average dominates the minimum. -/
lemma minValue_le_integral (hc : ∀ t, Continuous (h t)) (t : T) (P : Measure U)
    [IsProbabilityMeasure P] : minValue h t ≤ ∫ u, h t u ∂P := by
  have hint : Integrable (h t) P :=
    (hc t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc minValue h t = ∫ _, minValue h t ∂P := by simp
    _ ≤ ∫ u, h t u ∂P := integral_mono (integrable_const _) hint fun u => minValue_le hc t u

/-- Fibre averages of a Carathéodory integrand are dominated by `G`. -/
lemma abs_integral_le {G : T → ℝ} (hG : ∀ t u, |h t u| ≤ G t) (t : T) (P : Measure U)
    [IsProbabilityMeasure P] : |∫ u, h t u ∂P| ≤ G t := by
  have := norm_integral_le_of_norm_le_const (μ := P) (f := h t) (C := G t)
    (Eventually.of_forall fun u => by simpa [Real.norm_eq_abs] using hG t u)
  simpa [Real.norm_eq_abs] using this

end Integrand

/-! ### Fiberwise replacement -/

section Replacement

variable {h : T → U → ℝ} {G : T → ℝ} {ν : Measure (T × U)} [IsFiniteMeasure ν]

/-- **Fiberwise replacement.** Replacing the fibres `ν.condKernel t` by a Markov kernel `κ'`
whose fibre integrals are a.e. no larger keeps the time marginal and does not increase
`∫ h`. -/
theorem integral_compProd_le_of_fiber_le (hm : ∀ u, Measurable fun t => h t u)
    (hc : ∀ t, Continuous (h t)) (hG : ∀ t u, |h t u| ≤ G t) (hGi : Integrable G ν.fst)
    (κ' : Kernel T U) [IsMarkovKernel κ']
    (hle : ∀ᵐ t ∂ν.fst, ∫ u, h t u ∂(κ' t) ≤ ∫ u, h t u ∂(ν.condKernel t)) :
    (ν.fst ⊗ₘ κ').fst = ν.fst ∧
      ∫ x, Function.uncurry h x ∂(ν.fst ⊗ₘ κ') ≤ ∫ x, Function.uncurry h x ∂ν := by
  have hfst : (ν.fst ⊗ₘ κ').fst = ν.fst := Measure.fst_compProd _ _
  refine ⟨hfst, ?_⟩
  have hint' : Integrable (Function.uncurry h) (ν.fst ⊗ₘ κ') :=
    integrable_uncurry hm hc hG (by rwa [hfst])
  have hint : Integrable (Function.uncurry h) ν := integrable_uncurry hm hc hG hGi
  rw [Measure.integral_compProd hint', integral_eq_integral_condKernel ν hint]
  have hmeas : StronglyMeasurable fun t => ∫ u, h t u ∂(κ' t) :=
    (measurable_uncurry hm hc).stronglyMeasurable.integral_kernel_prod_right'
  have hi1 : Integrable (fun t => ∫ u, h t u ∂(κ' t)) ν.fst :=
    hGi.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun t => by
      simpa [Real.norm_eq_abs] using abs_integral_le hG t (κ' t))
  have hi2 : Integrable (fun t => ∫ u, h t u ∂(ν.condKernel t)) ν.fst :=
    Integrable.integral_condKernel hint
  exact integral_mono_ae hi1 hi2 hle

/-- The deterministic relaxed control carried by a measurable selector `s`. -/
noncomputable def selectorMeasure (μ : Measure T) (s : T → U) : Measure (T × U) :=
  μ.map fun t => (t, s t)

lemma fst_selectorMeasure {μ : Measure T} {s : T → U} (hs : Measurable s) :
    (selectorMeasure μ s).fst = μ := by
  have hg : Measurable fun t => (t, s t) := measurable_id.prodMk hs
  unfold selectorMeasure Measure.fst
  rw [Measure.map_map measurable_fst hg]
  exact Measure.map_id

lemma integral_selectorMeasure {μ : Measure T} {s : T → U} (hs : Measurable s)
    (hm : ∀ u, Measurable fun t => h t u) (hc : ∀ t, Continuous (h t)) :
    ∫ x, Function.uncurry h x ∂(selectorMeasure μ s) = ∫ t, h t (s t) ∂μ := by
  have hg : Measurable fun t => (t, s t) := measurable_id.prodMk hs
  unfold selectorMeasure
  rw [integral_map hg.aemeasurable
    (measurable_uncurry hm hc).aestronglyMeasurable]
  rfl

/-- **Replacement by a measurable argmin selector.** There is a measurable `s` such that the
deterministic control `(t, s t) ♯ ν.fst` has the same time marginal, value
`∫ min_u h(t,u) d(ν.fst)`, and does not increase `∫ h`. -/
theorem exists_replacement_le (hm : ∀ u, Measurable fun t => h t u)
    (hc : ∀ t, Continuous (h t)) (hG : ∀ t u, |h t u| ≤ G t) (hGi : Integrable G ν.fst) :
    ∃ s : T → U, Measurable s ∧ (selectorMeasure ν.fst s).fst = ν.fst ∧
      ∫ x, Function.uncurry h x ∂(selectorMeasure ν.fst s) = ∫ t, minValue h t ∂ν.fst ∧
      ∫ x, Function.uncurry h x ∂(selectorMeasure ν.fst s) ≤ ∫ x, Function.uncurry h x ∂ν := by
  obtain ⟨s, hs, hsmin⟩ := exists_measurable_isMinOn hm hc
  have hsval : ∀ t, h t (s t) = minValue h t := fun t =>
    le_antisymm (le_ciInf (hsmin t)) (minValue_le hc t (s t))
  have hval : ∫ x, Function.uncurry h x ∂(selectorMeasure ν.fst s) = ∫ t, minValue h t ∂ν.fst := by
    rw [integral_selectorMeasure hs hm hc]
    exact integral_congr_ae (Eventually.of_forall hsval)
  refine ⟨s, hs, fst_selectorMeasure hs, hval, ?_⟩
  have hint : Integrable (Function.uncurry h) ν := integrable_uncurry hm hc hG hGi
  rw [hval, integral_eq_integral_condKernel ν hint]
  exact integral_mono_ae (integrable_minValue hm hc hG hGi) (Integrable.integral_condKernel hint)
    (Eventually.of_forall fun t => minValue_le_integral hc t (ν.condKernel t))

/-! ### The common a.e. Hamiltonian minimum -/

/-- **Common a.e. Hamiltonian minimum (11.6.13).** If `ν` minimises `∫ h` among measures with the
same time marginal, then for `ν.fst`-a.e. `t` the fibre average equals the minimum of `h t`. -/
theorem ae_integral_condKernel_eq_minValue (hm : ∀ u, Measurable fun t => h t u)
    (hc : ∀ t, Continuous (h t)) (hG : ∀ t u, |h t u| ≤ G t) (hGi : Integrable G ν.fst)
    (hopt : ∀ ν' : Measure (T × U), ν'.fst = ν.fst →
      ∫ x, Function.uncurry h x ∂ν ≤ ∫ x, Function.uncurry h x ∂ν') :
    ∀ᵐ t ∂ν.fst, ∫ u, h t u ∂(ν.condKernel t) = minValue h t := by
  obtain ⟨s, -, hfst, hval, -⟩ := exists_replacement_le (ν := ν) hm hc hG hGi
  have hint : Integrable (Function.uncurry h) ν := integrable_uncurry hm hc hG hGi
  have hgi := Integrable.integral_condKernel hint
  have hmi := integrable_minValue hm hc hG hGi
  have hge : ∀ t, 0 ≤ (fun t => ∫ u, h t u ∂(ν.condKernel t) - minValue h t) t :=
    fun t => sub_nonneg.mpr (minValue_le_integral hc t (ν.condKernel t))
  have hle := hopt _ hfst
  rw [hval, integral_eq_integral_condKernel ν hint] at hle
  simp only [Function.uncurry_apply_pair] at hle hgi
  have hzero : ∫ t, (∫ u, h t u ∂(ν.condKernel t) - minValue h t) ∂ν.fst = 0 := by
    refine le_antisymm ?_ (integral_nonneg hge)
    rw [integral_sub hgi hmi]
    linarith
  have := (integral_eq_zero_iff_of_nonneg hge (hgi.sub hmi)).mp hzero
  filter_upwards [this] with t ht
  simpa [sub_eq_zero] using ht

/-- Hamiltonian minimum against **every** control value on one common a.e. set. -/
theorem ae_forall_integral_condKernel_le (hm : ∀ u, Measurable fun t => h t u)
    (hc : ∀ t, Continuous (h t)) (hG : ∀ t u, |h t u| ≤ G t) (hGi : Integrable G ν.fst)
    (hopt : ∀ ν' : Measure (T × U), ν'.fst = ν.fst →
      ∫ x, Function.uncurry h x ∂ν ≤ ∫ x, Function.uncurry h x ∂ν') :
    ∀ᵐ t ∂ν.fst, ∀ v, ∫ u, h t u ∂(ν.condKernel t) ≤ h t v := by
  filter_upwards [ae_integral_condKernel_eq_minValue hm hc hG hGi hopt] with t ht v
  rw [ht]
  exact minValue_le hc t v

/-- For a.e. `t`, the fibre `ν.condKernel t` is concentrated on the argmin of `h t`. -/
theorem ae_ae_le_of_optimal (hm : ∀ u, Measurable fun t => h t u)
    (hc : ∀ t, Continuous (h t)) (hG : ∀ t u, |h t u| ≤ G t) (hGi : Integrable G ν.fst)
    (hopt : ∀ ν' : Measure (T × U), ν'.fst = ν.fst →
      ∫ x, Function.uncurry h x ∂ν ≤ ∫ x, Function.uncurry h x ∂ν') :
    ∀ᵐ t ∂ν.fst, ∀ᵐ u ∂(ν.condKernel t), ∀ v, h t u ≤ h t v := by
  filter_upwards [ae_integral_condKernel_eq_minValue hm hc hG hGi hopt] with t ht
  have hint : Integrable (h t) (ν.condKernel t) :=
    (hc t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnn : 0 ≤ fun u => h t u - minValue h t := fun u => sub_nonneg.mpr (minValue_le hc t u)
  have hz : ∫ u, (h t u - minValue h t) ∂(ν.condKernel t) = 0 := by
    rw [integral_sub hint (integrable_const _)]
    simp [ht]
  have := (integral_eq_zero_iff_of_nonneg hnn (hint.sub (integrable_const _))).mp hz
  filter_upwards [this] with u hu v
  have : h t u = minValue h t := by simpa [sub_eq_zero] using hu
  rw [this]
  exact minValue_le hc t v

end Replacement

end DynamicalSystems.RelaxedHamiltonian
