/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Bases

/-!
# Localization of measurable Hamiltonian integral minima

Measurable replacement on arbitrary measurable sets first gives a separate almost-everywhere
inequality for each control value. A countable dense subset and continuity in the control then
produce a single common full-measure set for all control values. The control type can be the
subtype of a compact control set; no trajectory feasibility is inferred from replacement.
-/

@[expose] public section

open Set MeasureTheory Filter TopologicalSpace
namespace OptimalControl
variable {Ω W : Type*} [MeasurableSpace Ω] [MeasurableSpace W] {μ : Measure Ω}

/-- An integral minimum over measurable controls implies the inequality for each fixed
control value almost everywhere. Only the original and constant Hamiltonians need integrability.
The comparison is justified by measurable replacement, not by state-constrained feasibility. -/
theorem ae_hamiltonian_le_of_integral_minimizing
    (H : Ω → W → ℝ) (u : Ω → W) (hu : Measurable u)
    (hi : Integrable (fun t ↦ H t (u t)) μ)
    (hc : ∀ w, Integrable (fun t ↦ H t w) μ)
    (hmin : ∀ v : Ω → W, Measurable v →
      (∫ t, H t (u t) ∂μ) ≤ ∫ t, H t (v t) ∂μ) (w : W) :
    ∀ᵐ t ∂μ, H t (u t) ≤ H t w := by
  classical
  apply ae_le_of_forall_setIntegral_le hi (hc w)
  intro s hs _
  have hm := hmin (s.piecewise (fun _ ↦ w) u) (measurable_const.piecewise hs hu)
  have heq : (fun t ↦ H t (s.piecewise (fun _ ↦ w) u t)) =
      s.piecewise (fun t ↦ H t w) (fun t ↦ H t (u t)) := by
    funext t
    by_cases ht : t ∈ s <;> simp [Set.piecewise, ht]
  rw [heq, integral_piecewise hs (hc w).integrableOn hi.integrableOn] at hm
  have horig := integral_add_compl hs hi
  linarith

variable [TopologicalSpace W] [SeparableSpace W]

/-- Integral Hamiltonian minimization over measurable controls gives Hamiltonian
minimization over all control values on one common full-measure set. Continuity is required
only in the control variable, and only almost everywhere in time. -/
theorem ae_hamiltonian_minimizing_of_integral_minimizing
    (H : Ω → W → ℝ) (u : Ω → W) (hu : Measurable u)
    (hi : Integrable (fun t ↦ H t (u t)) μ)
    (hc : ∀ w, Integrable (fun t ↦ H t w) μ)
    (hcont : ∀ᵐ t ∂μ, Continuous (H t))
    (hmin : ∀ v : Ω → W, Measurable v →
      (∫ t, H t (u t) ∂μ) ≤ ∫ t, H t (v t) ∂μ) :
    ∀ᵐ t ∂μ, ∀ w, H t (u t) ≤ H t w := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense W
  have hd : ∀ᵐ t ∂μ, ∀ w ∈ D, H t (u t) ≤ H t w :=
    (ae_ball_iff hDc).2 fun w _ ↦
      ae_hamiltonian_le_of_integral_minimizing H u hu hi hc hmin w
  filter_upwards [hd, hcont] with t ht hct
  exact hDd.induction ht (isClosed_le continuous_const hct)
end OptimalControl
