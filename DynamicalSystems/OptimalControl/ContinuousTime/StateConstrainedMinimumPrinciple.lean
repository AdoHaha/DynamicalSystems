/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.AffineControlPath
public import DynamicalSystems.OptimalControl.ContinuousTime.StateControlAdjointPairing
public import DynamicalSystems.OptimalControl.ContinuousTime.AffineStateMinimumPrinciple

/-!
# Necessary minimum principle from actual affine-convex state-constrained optimality

Primitive continuous affine dynamics and convex C¹ objective/constraint data yield finite
indexed measures and a constructed costate. Neither trajectories for replacements,
first-variation inequalities, transitions nor Hamiltonian minima are assumed.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology

namespace OptimalControl.ConvexStateControlProblem

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
  {n : ℕ} (P : OptimalControl.ConvexStateControlProblem E V n)

/-- Actual affine-convex constrained optimality constructs transition and measure data and
an adjoint satisfying the actual Hamiltonian minimum on one common full-measure set. -/
theorem exists_affine_state_minimum_principle (D : P.ContinuouslyDifferentiableData)
    (A : P.Time → E →L[ℝ] E) (hA : Continuous A)
    (B : P.Time → V →L[ℝ] E) (hB : Continuous B) (a : P.Time → E) (ha : Continuous a)
    (hf : ∀ t x u, P.dynamics t x u = A t x + B t u + a t)
    (z : P.Candidate) (hz : P.IsMinimum z) :
    ∃ (α : ℝ) (μ : Measure P.ConstraintIndex) (Aext : ℝ → E →L[ℝ] E)
      (Phi : ℝ → ℝ → E →L[ℝ] E), IsFiniteMeasure μ ∧ 0 ≤ α ∧
      (α ≠ 0 ∨ μ ≠ 0) ∧ (∫ q, P.residual z q ∂μ) = 0 ∧
      μ {q | P.residual z q ≠ 0} = 0 ∧ Continuous Aext ∧
      (∀ t : P.Time, Aext t = A t) ∧ IsStateTransition Aext Phi ∧
      ∀ᵐ t ∂(horizonProbability P.horizon P.horizon_pos).toMeasure, ∀ v ∈ P.controlSet,
        let p := P.affineMeasureCostate D z α μ (fun s ↦ Phi s 0) (fun s ↦ Phi 0 s) t
        α * P.runningCost t (z.1 t) (z.2 t) + p (P.dynamics t (z.1 t) (z.2 t)) ≤
          α * P.runningCost t (z.1 t) v + p (P.dynamics t (z.1 t) v) := by
  obtain ⟨α, μ, hfin, hα, hne, hcomp, hsupp, hvar⟩ :=
    P.exists_nonnegative_firstVariation_of_isMinimum D z hz
  let : IsFiniteMeasure μ := hfin
  obtain ⟨Aext, Phi, hAe, heA, hPhi, hcontrols, hresponse⟩ :=
    P.exists_affine_response_data A hA B hB a ha hf
  let K : P.Time → E →L[ℝ] E := fun s ↦ Phi s 0
  let J : P.Time → E →L[ℝ] E := fun s ↦ Phi 0 s
  have hK : Continuous K := hPhi.continuous.comp
    (continuous_subtype_val.prodMk continuous_const)
  have hJ : Continuous J := hPhi.continuous.comp
    (continuous_const.prodMk continuous_subtype_val)
  let Q : P.Time → V →L[ℝ] ℝ := fun t ↦
    (P.affineMeasureCostate D z α μ K J t).comp (B t)
  have hQ : Integrable Q (horizonProbability P.horizon P.horizon_pos).toMeasure :=
    P.integrable_affineMeasureCostate_control D z hz.1 α μ K J B hK hJ hB
  have hpair : ∀ u : P.Time → V, Measurable u → (∀ t, u t ∈ P.controlSet) →
      0 ≤ ∫ t, (α • P.runningControlCovector D z t + Q t) (u t - z.2 t)
        ∂horizonProbability P.horizon P.horizon_pos := by
    intro u hu hmem
    obtain ⟨y, hy, hyu⟩ := hcontrols u hu hmem
    have hn := hvar y hy
    have he := P.firstVariation_eq_control_pairing D α μ z y hz.1 hy K J B hK hJ hB
      (hresponse y z hy hz.1)
    rw [he] at hn
    simp only [hyu] at hn
    change 0 ≤ P.horizon * (∫ t,
      (α • P.runningControlCovector D z t + Q t) (u t - z.2 t)
        ∂horizonProbability P.horizon P.horizon_pos) at hn
    nlinarith [P.horizon_pos]
  have hae := P.ae_runningHamiltonian_minimizing_of_nonnegative_pairings
    D α hα z hz.1 Q hQ hpair
  refine ⟨α, μ, Aext, Phi, hfin, hα, hne, hcomp, hsupp, hAe, heA, hPhi, ?_⟩
  filter_upwards [hae] with t ht
  intro v hv
  have hm := ht v hv
  dsimp only
  simp only [hf, map_add]
  change α * P.runningCost t (z.1 t) (z.2 t) +
      ((P.affineMeasureCostate D z α μ K J t) (A t (z.1 t)) + Q t (z.2 t) +
        (P.affineMeasureCostate D z α μ K J t) (a t)) ≤
    α * P.runningCost t (z.1 t) v +
      ((P.affineMeasureCostate D z α μ K J t) (A t (z.1 t)) + Q t v +
        (P.affineMeasureCostate D z α μ K J t) (a t))
  linarith

/-- A complete affine-convex state-constrained necessity theorem. Actual optimality produces
finite measures and a constructed BV costate, exact measure-adjoint increments, jumps,
terminal traces and one common AE Hamiltonian minimum, including abnormal multipliers. -/
theorem exists_stateConstrainedPMP_of_affine_convex_minimum
    (D : P.ContinuouslyDifferentiableData)
    (A : P.Time → E →L[ℝ] E) (hA : Continuous A)
    (B : P.Time → V →L[ℝ] E) (hB : Continuous B) (a : P.Time → E) (ha : Continuous a)
    (hf : ∀ t x u, P.dynamics t x u = A t x + B t u + a t)
    (z : P.Candidate) (hz : P.IsMinimum z) :
    ∃ (α : ℝ) (μ : Measure P.ConstraintIndex) (Aext : ℝ → E →L[ℝ] E)
      (Phi : ℝ → ℝ → E →L[ℝ] E) (p : ℝ → E →L[ℝ] ℝ),
      IsFiniteMeasure μ ∧ 0 ≤ α ∧ (α ≠ 0 ∨ μ ≠ 0) ∧
      (∫ q, P.residual z q ∂μ) = 0 ∧ μ {q | P.residual z q ≠ 0} = 0 ∧
      Continuous Aext ∧ (∀ t : P.Time, Aext t = A t) ∧ IsStateTransition Aext Phi ∧
      p = P.affineCostateReal D z α μ Phi ∧ BoundedVariationOn p (Icc 0 P.horizon) ∧
      (∀ t : P.Time, ContinuousWithinAt p (Ici (t : ℝ)) t) ∧
      (∀ r s : ℝ, 0 ≤ r → r ≤ s → s ≤ P.horizon →
        p s - p r = -(∫ t in r..s, (p t).comp (Aext t)) -
          (P.horizon * α) • (∫ t in {t : P.Time | r < (t : ℝ) ∧ (t : ℝ) ≤ s},
            P.runningStateCovector D z t ∂horizonProbability P.horizon P.horizon_pos) -
          ∫ q in {q : P.ConstraintIndex | r < (q.1 : ℝ) ∧ (q.1 : ℝ) ≤ s},
            P.stateConstraintNormal D z q ∂μ) ∧
      (∀ t ∈ Ioc (0 : ℝ) P.horizon,
        p t - Function.leftLim p t =
          -∫ q in {q : P.ConstraintIndex | (q.1 : ℝ) = t}, P.stateConstraintNormal D z q ∂μ) ∧
      p P.horizon = α • D.terminalDerivative (z.1 (timeEnd P.horizon P.horizon_pos.le)) ∧
      Function.leftLim p P.horizon =
        α • D.terminalDerivative (z.1 (timeEnd P.horizon P.horizon_pos.le)) +
          ∫ q in {q : P.ConstraintIndex | (q.1 : ℝ) = P.horizon},
            P.stateConstraintNormal D z q ∂μ ∧
      ∀ᵐ t ∂(horizonProbability P.horizon P.horizon_pos).toMeasure, ∀ v ∈ P.controlSet,
        α * P.runningCost t (z.1 t) (z.2 t) + p t (P.dynamics t (z.1 t) (z.2 t)) ≤
          α * P.runningCost t (z.1 t) v + p t (P.dynamics t (z.1 t) v) := by
  obtain ⟨α, μ, Aext, Phi, hfin, hα, hne, hcomp, hsupp, hAe, heA, hPhi, hmin⟩ :=
    P.exists_affine_state_minimum_principle D A hA B hB a ha hf z hz
  let : IsFiniteMeasure μ := hfin
  refine ⟨α, μ, Aext, Phi, P.affineCostateReal D z α μ Phi, hfin, hα, hne, hcomp,
    hsupp, hAe, heA, hPhi, rfl,
    P.affineCostateReal_boundedVariation D z hz.1 α μ hPhi hAe 0 P.horizon,
    fun t ↦ P.affineCostateReal_right_continuous D z hz.1 α μ hPhi t,
    fun r s _ hrs _ ↦ P.affineCostateReal_increment D z hz.1 α μ hPhi hAe hrs,
    fun t _ ↦ P.affineCostateReal_jump D z hz.1 α μ hPhi t,
    P.affineCostateReal_terminal D z α μ hPhi,
    P.affineCostateReal_terminal_left_trace D z hz.1 α μ hPhi, ?_⟩
  filter_upwards [hmin] with t ht
  intro v hv
  simpa only [P.affineCostateReal_eq D z α μ Phi t] using ht v hv

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]
  [BorelSpace V] [SecondCountableTopology V] in
/-- Strict initial feasibility removes every initial-time constraint atom. -/
theorem stateMeasure_initial_fiber_eq_zero (z : P.Candidate) (hz : P.DynamicsAdmissible z)
    (μ : Measure P.ConstraintIndex) (hsupp : μ {q | P.residual z q ≠ 0} = 0)
    (hinit : ∀ i : Fin n, P.constraint (timeZero P.horizon P.horizon_pos.le, i) P.initial < 0) :
    μ {q : P.ConstraintIndex | (q.1 : ℝ) = 0} = 0 := by
  have hx0 : z.1 (timeZero P.horizon P.horizon_pos.le) = P.initial := by
    simpa using hz.2.2 (timeZero P.horizon P.horizon_pos.le)
  apply measure_mono_null _ hsupp
  intro q hq
  change (q.1 : ℝ) = 0 at hq
  have hqt : q.1 = timeZero P.horizon P.horizon_pos.le := Subtype.ext hq
  have hp : q = (timeZero P.horizon P.horizon_pos.le, q.2) := Prod.ext hqt rfl
  have hg : P.residual z q < 0 := by
    change P.constraint q (z.1 q.1) < 0
    rw [hp, hx0]
    exact hinit q.2
  exact ne_of_lt hg

end OptimalControl.ConvexStateControlProblem
