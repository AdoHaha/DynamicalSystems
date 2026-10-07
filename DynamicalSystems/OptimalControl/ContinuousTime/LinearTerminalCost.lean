/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.FiniteSwitching
public import DynamicalSystems.OptimalControl.ContinuousTime.MeasurableHamiltonian
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Finite switching from actual linear terminal-cost optimality

The endpoint is the variation-of-constants endpoint of the LTI system with measurable box
controls. Minimizing a nonzero linear terminal objective over actual control competitors
implies the common-AE Hamiltonian minimum and hence finite switching under the per-input
Krylov condition. This is a free-terminal, fixed-horizon theorem, not minimum-time necessity.
-/

@[expose] public section

open Set MeasureTheory TopologicalSpace
namespace OptimalControl

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype ι]

/-- Actual variation-of-constants terminal state for measurable LTI controls. -/
noncomputable def linearTerminalState (A : E →L[ℝ] E) (b : ι → E) (x₀ : E)
    (T : ℝ) (u : ℝ → EuclideanSpace ℝ ι) : E :=
  NormedSpace.exp (T • A) x₀ +
    ∫ t, NormedSpace.exp ((T - t) • A) (∑ i, u t i • b i) ∂volume.restrict (Icc 0 T)

/-- The actual endpoint response is integrable for measurable box controls. -/
theorem integrable_linear_terminal_response (A : E →L[ℝ] E) (b : ι → E) (T : ℝ)
    (u : ℝ → EuclideanSpace ℝ ι) (hu : Measurable u)
    (hbox : ∀ t ∈ Icc 0 T, u t ∈ unitBox ι) :
    Integrable (fun t ↦ NormedSpace.exp ((T - t) • A) (∑ i, u t i • b i))
      (volume.restrict (Icc 0 T)) := by
  have hi (i : ι) : Integrable
      (fun t ↦ u t i • NormedSpace.exp ((T - t) • A) (b i))
      (volume.restrict (Icc 0 T)) := by
    have hcexp : Continuous (fun t : ℝ ↦ NormedSpace.exp ((T - t) • A)) := by
      apply continuous_iff_continuousAt.mpr
      intro t
      exact ((hasDerivAt_exp_smul_const A (T - t)).comp_const_sub T t).continuousAt
    have hc : Continuous (fun t : ℝ ↦ NormedSpace.exp ((T - t) • A) (b i)) :=
      hcexp.clm_apply continuous_const
    have hm : AEStronglyMeasurable (fun t ↦ u t i) (volume.restrict (Icc 0 T)) :=
      ((EuclideanSpace.proj i).continuous.measurable.comp hu).aestronglyMeasurable
    have hbnd : ∀ᵐ t ∂volume.restrict (Icc 0 T), ‖u t i‖ ≤ 1 := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact (hbox t ht) i
    exact hc.integrableOn_Icc.bdd_smul 1 hm hbnd
  have hs := integrable_finsetSum Finset.univ (fun i _ ↦ hi i)
  simpa only [map_sum, map_smul] using hs

/-- Actual terminal-cost minimization yields a finite-switch representative. The terminal
covector is primitive problem data (the nonzero linear terminal objective), not a supplied
PMP certificate. No Hamiltonian minimization premise is required. -/
theorem hasAEFiniteSwitchesOn_of_linear_terminal_cost_minimizing
    (A : E →L[ℝ] E) (q : E →L[ℝ] ℝ) (b : ι → E) (x₀ : E) (T : ℝ)
    (hb : ∀ i, CyclicInput A (b i)) (hq : q ≠ 0)
    (u : ℝ → EuclideanSpace ℝ ι) (hu : Measurable u)
    (hbox : ∀ t, u t ∈ unitBox ι)
    (hopt : ∀ v : ℝ → EuclideanSpace ℝ ι, Measurable v → (∀ t, v t ∈ unitBox ι) →
      q (linearTerminalState A b x₀ T u) ≤ q (linearTerminalState A b x₀ T v)) :
    HasAEFiniteSwitchesOn u 0 T := by
  let μ := volume.restrict (Icc 0 T)
  let U := unitBox ι
  let H : ℝ → U → ℝ := fun t w ↦ terminalAdjointCovector A q T t (∑ i, w.val i • b i)
  let us : ℝ → U := fun t ↦ ⟨u t, hbox t⟩
  have hus : Measurable us := hu.subtype_mk
  have hHi (v : ℝ → U) (hv : Measurable v) : Integrable (fun t ↦ H t (v t)) μ := by
    exact q.integrable_comp (integrable_linear_terminal_response A b T
      (fun t ↦ (v t).val) (measurable_subtype_coe.comp hv) (fun t _ ↦ (v t).property))
  have hHformula (v : ℝ → U) (hv : Measurable v) :
      q (linearTerminalState A b x₀ T (fun t ↦ (v t).val)) =
        q (NormedSpace.exp (T • A) x₀) + ∫ t, H t (v t) ∂μ := by
    unfold linearTerminalState
    rw [map_add, ← q.integral_comp_comm (integrable_linear_terminal_response A b T
      (fun t ↦ (v t).val) (measurable_subtype_coe.comp hv) (fun t _ ↦ (v t).property))]
    rfl
  have hmin : ∀ v : ℝ → U, Measurable v →
      (∫ t, H t (us t) ∂μ) ≤ ∫ t, H t (v t) ∂μ := by
    intro v hv
    have hm := hopt (fun t ↦ (v t).val) (measurable_subtype_coe.comp hv)
      (fun t ↦ (v t).property)
    change q (linearTerminalState A b x₀ T (fun t ↦ (us t).val)) ≤ _ at hm
    rw [hHformula us hus, hHformula v hv] at hm
    linarith
  have hcont : ∀ᵐ t ∂μ, Continuous (H t) := by
    apply Filter.Eventually.of_forall
    intro t
    exact (terminalAdjointCovector A q T t).continuous.comp
      (continuous_finsetSum Finset.univ (fun i _ ↦
        ((EuclideanSpace.proj i).continuous.comp continuous_subtype_val).smul continuous_const))
  have ha := ae_hamiltonian_minimizing_of_integral_minimizing H us hus (hHi us hus)
    (fun w ↦ hHi (fun _ ↦ w) measurable_const) hcont hmin
  apply hasAEFiniteSwitchesOn_of_linear_box_minimizing A q b T hb hq u
    (Filter.Eventually.of_forall hbox)
  filter_upwards [ha] with t ht w hw
  exact ht ⟨w, hw⟩

end OptimalControl
