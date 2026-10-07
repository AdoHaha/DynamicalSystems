/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.HamiltonianMinimumLimit
public import DynamicalSystems.Mathlib.MeasureTheory.RelaxedHamiltonianMinimum

/-!
# The pointwise Hamiltonian minimum (Theorem 11.4.4 (v) / Theorem 11.6.3 (v))

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Theorem 11.4.4 (v),
Theorem 11.6.3 (v), (11.6.13).

If a relaxed control `ρ₀` minimises the Hamiltonian integral
`∫ (c f⁰(t,x₀(t),u) − Θ(t)·f(t,x₀(t),u)) dρ(t,u)` among all relaxed controls (all probability
measures with the same time marginal), then for a.e. `t` its conditional law minimises the
integrand over every control value: `∫ H(t,·) dρ₀,t ≤ H(t,v)` for all `v ∈ Ω`.  The integrated
inequality is the output of `hamiltonianIntegral_le_of_limit`.

Book citations live in docstrings only.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology Interval

namespace OptimalControl.BoundedState

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]

namespace Problem

omit [CompleteSpace E] in
/-- **Pointwise Hamiltonian minimum** from the integrated minimum over relaxed controls. -/
theorem ae_hamiltonian_le_of_hamiltonianIntegral_le (P : Problem E V W) (x₀ : P.Trajectory)
    (ρ₀ : P.Relaxed) {Θ : P.Time → E →L[ℝ] ℝ} {B : ℝ} (hΘ : Measurable Θ)
    (hΘb : ∀ t, ‖Θ t‖ ≤ B) (c : ℝ)
    (h : ∀ σ : P.Relaxed,
      hamiltonianIntegral P ρ₀ x₀ Θ c ≤ hamiltonianIntegral P σ x₀ Θ c) :
    ∀ᵐ t ∂(horizonProbability P.horizon P.horizon_pos).toMeasure, ∀ v : P.Control,
      ∫ u : P.Control, (c * P.runningCost t (x₀ t) (u : V)
          - Θ t (P.dynamics t (x₀ t) (u : V))) ∂ρ₀.kernel t
        ≤ c * P.runningCost t (x₀ t) (v : V) - Θ t (P.dynamics t (x₀ t) (v : V)) := by
  set H : P.Time → P.Control → ℝ := fun t u =>
    c * P.runningCost t (x₀ t) (u : V) - Θ t (P.dynamics t (x₀ t) (u : V)) with hH
  -- bounds
  obtain ⟨C₀, hC₀⟩ : ∃ C, ∀ (t : P.Time) (u : P.Control), |P.runningCost t (x₀ t) (u : V)| ≤ C := by
    have hK : IsCompact (((univ : Set P.Time) ×ˢ Set.range x₀) ×ˢ P.controlSet) :=
      (isCompact_univ.prod (isCompact_range x₀.continuous)).prod P.controlSet_compact
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn P.runningCost_continuous.continuousOn
    exact ⟨C, fun t u => by simpa using hC ((t, x₀ t), (u : V)) ⟨⟨mem_univ _, ⟨t, rfl⟩⟩, u.2⟩⟩
  obtain ⟨C₁, hC₁⟩ := exists_bound_dynamics_trajectory P x₀
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hΘb ⟨0, le_rfl, P.horizon_pos.le⟩)
  have hG : ∀ t u, |H t u| ≤ |c| * C₀ + B * C₁ := by
    intro t u
    simp only [hH]
    calc |c * P.runningCost t (x₀ t) (u : V) - Θ t (P.dynamics t (x₀ t) (u : V))|
        ≤ |c * P.runningCost t (x₀ t) (u : V)| + |Θ t (P.dynamics t (x₀ t) (u : V))| :=
          abs_sub _ _
      _ ≤ |c| * C₀ + B * C₁ := by
          gcongr
          · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC₀ t u) (abs_nonneg c)
          · rw [← Real.norm_eq_abs]
            calc ‖Θ t (P.dynamics t (x₀ t) (u : V))‖
                ≤ ‖Θ t‖ * ‖P.dynamics t (x₀ t) (u : V)‖ := (Θ t).le_opNorm _
              _ ≤ B * C₁ := mul_le_mul (hΘb t) (hC₁ t u) (norm_nonneg _) hB0
  -- continuity in u
  have hc : ∀ t, Continuous (H t) := by
    intro t
    have h1 : Continuous fun u : P.Control => P.runningCost t (x₀ t) (u : V) :=
      P.runningCost_continuous.comp
        ((continuous_const : Continuous fun _ : P.Control => (t, x₀ t)).prodMk
          continuous_subtype_val)
    have h2 : Continuous fun u : P.Control => P.dynamics t (x₀ t) (u : V) :=
      P.dynamics_continuous.comp
        ((continuous_const : Continuous fun _ : P.Control => (t, x₀ t)).prodMk
          continuous_subtype_val)
    exact (continuous_const.mul h1).sub ((Θ t).continuous.comp h2)
  -- measurability in t
  have hm : ∀ u, Measurable fun t => H t u := by
    intro u
    let _ : MeasurableSpace E := borel E
    have : BorelSpace E := ⟨rfl⟩
    have h1 : Continuous fun t : P.Time => P.runningCost t (x₀ t) (u : V) :=
      P.runningCost_continuous.comp
        ((continuous_id.prodMk x₀.continuous).prodMk continuous_const)
    have h2 : Continuous fun t : P.Time => P.dynamics t (x₀ t) (u : V) :=
      P.dynamics_continuous.comp
        ((continuous_id.prodMk x₀.continuous).prodMk continuous_const)
    have h3 : Measurable fun t : P.Time => Θ t (P.dynamics t (x₀ t) (u : V)) :=
      ContinuousLinearMap.measurable_apply₂.comp (hΘ.prodMk h2.measurable)
    exact (measurable_const.mul h1.measurable).sub h3
  have hGi : Integrable (fun _ : P.Time => |c| * C₀ + B * C₁) ρ₀.measure.fst := by
    rw [ρ₀.fst_measure]; exact integrable_const _
  have hopt : ∀ ν' : Measure (P.Time × P.Control), ν'.fst = ρ₀.measure.fst →
      ∫ x, Function.uncurry H x ∂ρ₀.measure ≤ ∫ x, Function.uncurry H x ∂ν' := by
    intro ν' hν'
    have hprob : IsProbabilityMeasure ν' := by
      constructor
      have := congrArg (fun μ : Measure P.Time => μ univ) hν'
      simp only [Measure.fst_univ] at this
      rw [this]; exact measure_univ
    let σ : P.Relaxed := ⟨⟨ν', hprob⟩, by
      apply Subtype.ext
      change ν'.map Prod.fst = _
      rw [← Measure.fst, hν', ρ₀.fst_measure]
      rfl⟩
    exact h σ
  have key := DynamicalSystems.RelaxedHamiltonian.ae_forall_integral_condKernel_le
    (ν := ρ₀.measure) hm hc hG hGi hopt
  rw [ρ₀.fst_measure] at key
  exact key

end Problem

end OptimalControl.BoundedState
