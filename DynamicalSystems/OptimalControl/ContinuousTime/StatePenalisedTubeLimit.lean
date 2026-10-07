/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.StatePenalisedTubeMinimizer
public import DynamicalSystems.OptimalControl.ContinuousTime.StatePenalisedConvergenceData
public import DynamicalSystems.OptimalControl.ContinuousTime.StateMultiplierMassBound
public import DynamicalSystems.OptimalControl.ContinuousTime.StateMultiplierStieltjes
public import DynamicalSystems.OptimalControl.ContinuousTime.VelocityPointwiseMinimizerEndpointConditions

/-!
# From the tube minimisers `(φ_j, y_j)` of (11.3.9) to the `j → ∞` multiplier limit

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.8)–(11.3.9),
Lemma 11.3.5, §11.6.

`StatePenalisedTubeMinimizer.lean` proves, at the level of the product domain
`E × WeakSpace(L²) × RelaxedControl`, that the state-penalised functionals `H^j` attain their
minima on the free tube `V(ε)` (frozen control `ν^ε`), that the minimisers are eventually strictly
interior, and that a subsequence converges strongly in `L²` / uniformly to an `F_K`-minimiser
satisfying the state constraint.

This file turns those minimisers into the input of the multiplier limit
`StateMultiplierLimit.lean`:

* `Problem.penalisedMinimiserSequence`: a `PenalisedMinimiserSequence` for the **pointwise-defect
  Lagrangian** `L = T⁻¹ c + ‖v − φ₀'‖² + K‖v − f‖²` (the §11.6 penalty `F_K` with the control
  averaged out against `ν^ε`) — functional identification via
  `velocityPenalizedPointwise_eq_action`, strict interiority giving the perturbation clause;
* `Problem.exists_stateMultiplierLimit_of_tubeMinimisers`: the `j → ∞` limit of Lemma 11.3.5:
  a limit path `γ^ε`, a subsequence, a nonincreasing multiplier `λ(ε;·)`, and the costate
  equation (11.6.11) with (11.6.6), (11.6.16) and the Stieltjes measure form.

Book citations live in docstrings only.
-/

@[expose] public section

open Set MeasureTheory Filter Metric ACEulerLagrange
open scoped Topology Interval ENNReal

namespace OptimalControl.BoundedState

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]

namespace Problem

variable {P : Problem E V W}

/-! ## The free tube on the velocity carrier -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- Membership of a carrier datum in the free tube `V(ε)` of (11.3.7) is the three tube
inequalities (velocity energy, initial distance, control distance). -/
theorem mem_lpFreeTube_iff_carrier {ε : ℝ} (γ₀ γ : VelocityTrajectory P) (ρ₀ ρ : P.Relaxed) :
    (γ.initial, toWeakSpace ℝ _ γ.toLp, ρ) ∈ lpFreeTube P ε γ₀ ρ₀ ↔
      (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2) ≤ ε ^ 2 ∧
        dist γ.initial γ₀.initial ≤ ε ∧ relaxedControlDistance P ρ ρ₀ ≤ ε := by
  have hsq : (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2) =
      ∫ a, ‖γ.toLp a - γ₀.toLp a‖ ^ 2 ∂(horizonMeasure P.horizon) := by
    rw [integral_sq_velocity_sub_eq γ₀ γ, integral_norm_sub_sq_eq_norm_sq,
      Lp_two_norm_sq_eq_integral_norm_sq]
  simp only [lpFreeTube, mem_prod, mem_closedBall, mem_ofPred_eq, hsq,
    (toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon))).injective.mem_set_image]
  tauto

omit [MeasurableSpace E] [BorelSpace E] in
/-- **Strict interior of the free tube: scalar-profile perturbations stay admissible.**  If the
velocity energy and the initial distance are strictly inside the tube, every scalar-profile
perturbation of the carrier stays in the free tube `V(ε)` of (11.3.7) for small parameter.  (No
state clause: this is the point of the state-constraint-free tube.)

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.7) and Lemma 11.3.5. -/
theorem eventually_perturbProfile_mem_lpFreeTube {ε : ℝ} (γ₀ γ : VelocityTrajectory P)
    (ρ₀ ρ : P.Relaxed)
    (hv : (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2) < ε ^ 2)
    (hi : dist γ.initial γ₀.initial < ε) (hc : relaxedControlDistance P ρ ρ₀ ≤ ε)
    (e : E) (α : ℝ) (s : ℝ → ℝ) (hs : MemLp s 2 (timeMeasure P.horizon)) :
    ∀ᶠ θ in 𝓝 (0 : ℝ),
      ((γ.perturbProfile e α s hs θ).initial,
        toWeakSpace ℝ _ (γ.perturbProfile e α s hs θ).toLp, ρ) ∈ lpFreeTube P ε γ₀ ρ₀ := by
  have hT := P.horizon_pos
  have h1 : ∀ᶠ θ : ℝ in 𝓝 0,
      (∫ t in (0 : ℝ)..P.horizon,
        ‖(γ.perturbProfile e α s hs θ).velocity t - γ₀.velocity t‖ ^ 2) ≤ ε ^ 2 := by
    have hu : MemLp (fun t => γ.velocity t - γ₀.velocity t) 2
        (timeMeasure P.horizon) := γ.memLp_velocity.sub γ₀.memLp_velocity
    have hw := memLp_smul_const (E := E) hs e
    have hcont := continuous_integral_norm_add_smul_sq hu hw
    have hrw : ∀ θ : ℝ, (∫ t in (0 : ℝ)..P.horizon,
        ‖(γ.perturbProfile e α s hs θ).velocity t - γ₀.velocity t‖ ^ 2)
        = ∫ t, ‖(γ.velocity t - γ₀.velocity t) + θ • (s t • e)‖ ^ 2
            ∂(timeMeasure P.horizon) := by
      intro θ
      rw [intervalIntegral.integral_of_le hT.le]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [VelocityTrajectory.perturbProfile, VelocityTrajectory.perturb]
      congr 2
      abel
    have h0 : (∫ t, ‖(γ.velocity t - γ₀.velocity t) + (0 : ℝ) • (s t • e)‖ ^ 2
        ∂(timeMeasure P.horizon)) < ε ^ 2 := by
      have := hv
      rw [intervalIntegral.integral_of_le hT.le] at this
      simpa using this
    have hev := (hcont.continuousAt (x := (0 : ℝ))).eventually (Iio_mem_nhds h0)
    filter_upwards [hev] with θ hθ
    rw [hrw θ]
    exact le_of_lt hθ
  have h2 : ∀ᶠ θ : ℝ in 𝓝 0, dist (γ.perturbProfile e α s hs θ).initial γ₀.initial ≤ ε := by
    have hcont : Continuous fun θ : ℝ => dist (γ.initial + θ • (α • e)) γ₀.initial := by
      fun_prop
    have h0 : dist (γ.initial + (0 : ℝ) • (α • e)) γ₀.initial < ε := by simpa using hi
    filter_upwards [(hcont.continuousAt (x := (0 : ℝ))).eventually (Iio_mem_nhds h0)] with θ hθ
    exact le_of_lt hθ
  filter_upwards [h1, h2] with θ hθ1 hθ2
  exact (mem_lpFreeTube_iff_carrier γ₀ _ ρ₀ ρ).2 ⟨hθ1, hθ2, hc⟩

/-! ## The state-penalised functional as an action functional -/

omit [MeasurableSpace E] [BorelSpace E] in
/-- The state violation of the carrier datum is the interval integral of `ω(G(t, γ(t)))`. -/
theorem lpStateViolation_carrier (G : ℝ → E → ℝ) (ω : ℝ → ℝ) (γ : VelocityTrajectory P)
    (ρ : P.Relaxed) :
    lpStateViolation P G ω (γ.initial, toWeakSpace ℝ _ γ.toLp, ρ)
      = ∫ r in (0 : ℝ)..P.horizon, ω (G r (γ.value r)) := by
  have hpath : lpPath P (γ.initial, toWeakSpace ℝ _ γ.toLp, ρ) = toBoundedPath γ := by
    simp only [lpPath, LinearEquiv.symm_apply_apply]
    exact γ.toBoundedPath_eq_primitiveBoundedPath.symm
  unfold lpStateViolation stateViolationIntegral
  rw [hpath]
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le P.horizon_pos.le] at hr
  simp only [toBoundedPath_apply]
  rw [Set.projIcc_of_mem _ hr]

/-- The initial penalty of the anchored pointwise penalty: `‖y − φ₀(0)‖² + K‖y − x₀‖²`. -/
noncomputable def tubeInitialPenalty (P : Problem E V W) (K : ℝ) (γ₀ : VelocityTrajectory P)
    (y : E) : ℝ :=
  ‖y - γ₀.initial‖ ^ 2 + K * ‖y - P.initial‖ ^ 2

/-- The endpoint penalty of the pointwise penalty: `K‖T(φ(0),φ(t₁))‖²`. -/
noncomputable def tubeEndpointPenalty (P : Problem E V W) (K : ℝ) (q : E × E) : ℝ :=
  K * ‖P.endpointConstraint q.1 q.2‖ ^ 2

/-- The pointwise-defect Lagrangian of the free-tube minimisation with frozen control `ρe`. -/
noncomputable def tubeLagrangian (P : Problem E V W) (K : ℝ) (γ₀ : VelocityTrajectory P)
    (ρe : P.Relaxed) : ℝ → E → E → ℝ :=
  pointwiseDefectLagrangian (fun t y => P.horizon⁻¹ * averagedRunningCost P ρe t y)
    (averagedDynamics P ρe) γ₀.velocity K

omit [MeasurableSpace E] [BorelSpace E] in
/-- **The state-penalised anchored functional `H^j` is a constant plus an action functional**
(Berkovitz & Medhin (11.3.8)): for a carrier `γ` and frozen control `ρ`,
`H^j(γ, ρ) = ε‖ρ − ν₀‖ + ∫₀ᵀ (L + jω(G)) dt + Φ₀(γ 0) + Φ₁(γ 0, γ T)` with `L` the
pointwise-defect Lagrangian. -/
theorem lpStatePenalisedAnchored_carrier {G : ℝ → E → ℝ} {ω : ℝ → ℝ}
    (hG : Continuous fun p : ℝ × E => G p.1 p.2) (hω : Continuous ω) (j K ε : ℝ)
    (γ₀ γ : VelocityTrajectory P) (ρ₀ ρ : P.Relaxed) :
    lpStatePenalisedAnchored P G ω j K ε γ₀ ρ₀ (γ.initial, toWeakSpace ℝ _ γ.toLp, ρ)
      = ε * relaxedControlDistance P ρ ρ₀ +
        actionFunctional (statePenalisedLagrangian (tubeLagrangian P K γ₀ ρ) G ω j)
          (tubeInitialPenalty P K γ₀) (tubeEndpointPenalty P K)
          P.horizon γ.initial γ.velocity := by
  have hint1 : IntervalIntegrable (fun t => tubeLagrangian P K γ₀ ρ t (γ.value t) (γ.velocity t))
      volume 0 P.horizon := intervalIntegrable_pointwiseDefectLagrangian_value P K γ₀ γ ρ
  have hint2 : IntervalIntegrable (fun r => ω (G r (γ.value r))) volume 0 P.horizon := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le P.horizon_pos.le]
    exact hω.comp_continuousOn ((hG.comp_continuousOn
      (continuousOn_id.prodMk γ.continuousOn_value)))
  have hsplit : ∫ t in (0 : ℝ)..P.horizon,
      statePenalisedLagrangian (tubeLagrangian P K γ₀ ρ) G ω j t (γ.value t) (γ.velocity t)
      = (∫ t in (0 : ℝ)..P.horizon, tubeLagrangian P K γ₀ ρ t (γ.value t) (γ.velocity t))
        + j * ∫ r in (0 : ℝ)..P.horizon, ω (G r (γ.value r)) := by
    unfold statePenalisedLagrangian
    rw [intervalIntegral.integral_add hint1 (hint2.const_mul j),
      intervalIntegral.integral_const_mul]
  have hcarrier := velocityPenalizedPointwiseAnchored_eq_lpPenaltyPointwiseAnchored P K ε γ₀ γ ρ₀ ρ
  have haction := velocityPenalizedPointwise_eq_action P K ε γ₀ ρ₀ γ ρ
  unfold lpStatePenalisedAnchored
  rw [lpStateViolation_carrier, ← hcarrier]
  unfold velocityPenalizedPointwiseAnchored
  rw [haction]
  unfold actionFunctional tubeInitialPenalty tubeEndpointPenalty
  have hval : ∀ t, primitive γ.initial γ.velocity t = γ.value t := fun t => rfl
  simp only [hval]
  rw [hsplit, dist_eq_norm]
  unfold tubeLagrangian
  ring

omit [MeasurableSpace E] [BorelSpace E] in
/-- The penalised pointwise-defect Lagrangian is interval integrable along every carrier. -/
theorem intervalIntegrable_statePenalisedTubeLagrangian {G : ℝ → E → ℝ} {ω : ℝ → ℝ}
    (hG : Continuous fun p : ℝ × E => G p.1 p.2) (hω : Continuous ω) (j K : ℝ)
    (γ₀ γ : VelocityTrajectory P) (ρ : P.Relaxed) :
    IntervalIntegrable (fun t => statePenalisedLagrangian (tubeLagrangian P K γ₀ ρ) G ω j t
      (γ.value t) (γ.velocity t)) volume 0 P.horizon := by
  have hint1 : IntervalIntegrable (fun t => tubeLagrangian P K γ₀ ρ t (γ.value t) (γ.velocity t))
      volume 0 P.horizon := intervalIntegrable_pointwiseDefectLagrangian_value P K γ₀ γ ρ
  have hint2 : IntervalIntegrable (fun r => ω (G r (γ.value r))) volume 0 P.horizon := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le P.horizon_pos.le]
    exact hω.comp_continuousOn ((hG.comp_continuousOn
      (continuousOn_id.prodMk γ.continuousOn_value)))
  exact hint1.add (hint2.const_mul j)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The initial penalty is smooth. -/
theorem contDiff_tubeInitialPenalty (K : ℝ) (γ₀ : VelocityTrajectory P) :
    ContDiff ℝ 1 (tubeInitialPenalty P K γ₀) := by
  unfold tubeInitialPenalty
  exact ((contDiff_id.sub contDiff_const).norm_sq ℝ).add
    (contDiff_const.mul ((contDiff_id.sub contDiff_const).norm_sq ℝ))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The endpoint penalty is `C¹` when the endpoint constraint is. -/
theorem contDiff_tubeEndpointPenalty (K : ℝ)
    (hT : ContDiff ℝ 1 (fun q : E × E => P.endpointConstraint q.1 q.2)) :
    ContDiff ℝ 1 (tubeEndpointPenalty P K) := by
  unfold tubeEndpointPenalty
  exact contDiff_const.mul (hT.norm_sq ℝ)

/-- **The sequence of minimisers `(φ_j, y_j)` of (11.3.9) as a `PenalisedMinimiserSequence`**
for the pointwise-defect Lagrangian.  The tube `V(ε)` provides the competitor set; strict
interiority of the velocity and initial clauses (Lemma 11.3.5) is the perturbation clause.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.8), (11.3.9),
Lemma 11.3.5. -/
noncomputable def tubeMinimiserSequence {G : ℝ → E → ℝ} {ω : ℝ → ℝ}
    (hG : Continuous fun p : ℝ × E => G p.1 p.2) (hω : Continuous ω) {K ε : ℝ}
    (hT : ContDiff ℝ 1 (fun q : E × E => P.endpointConstraint q.1 q.2))
    {γ₀ : VelocityTrajectory P} {ρ₀ ρe : P.Relaxed}
    {j : ℕ → ℝ} (hj0 : ∀ n, 0 ≤ j n)
    {d : ℕ → E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed}
    (hdmem : ∀ n, d n ∈ lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = ρe})
    (hdmin : ∀ n, IsMinOn (lpStatePenalisedAnchored P G ω (j n) K ε γ₀ ρ₀)
      (lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = ρe}) (d n))
    (hv : ∀ n, (∫ s in (0 : ℝ)..P.horizon,
        ‖(lpVelocityTrajectory P (d n)).velocity s - γ₀.velocity s‖ ^ 2) < ε ^ 2)
    (hi : ∀ n, dist (lpVelocityTrajectory P (d n)).initial γ₀.initial < ε) :
    PenalisedMinimiserSequence P (tubeLagrangian P K γ₀ ρe) G ω (tubeInitialPenalty P K γ₀)
      (tubeEndpointPenalty P K) where
  path n := lpVelocityTrajectory P (d n)
  penalty := j
  penalty_nonneg := hj0
  functional n γ := actionFunctional
    (statePenalisedLagrangian (tubeLagrangian P K γ₀ ρe) G ω (j n))
    (tubeInitialPenalty P K γ₀) (tubeEndpointPenalty P K) P.horizon γ.initial γ.velocity
  competitors n := {γ | (γ.initial, toWeakSpace ℝ _ γ.toLp, ρe) ∈ lpFreeTube P ε γ₀ ρ₀}
  functional_eq n γ' := rfl
  isMinOn n := by
    intro γ hγ
    have hγ' : (γ.initial, toWeakSpace ℝ _ γ.toLp, ρe) ∈
        lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = ρe} := ⟨hγ, rfl⟩
    have h1 := hdmin n hγ'
    have h2 : lpStatePenalisedAnchored P G ω (j n) K ε γ₀ ρ₀ (d n) =
        lpStatePenalisedAnchored P G ω (j n) K ε γ₀ ρ₀
          ((lpVelocityTrajectory P (d n)).initial,
            toWeakSpace ℝ _ (lpVelocityTrajectory P (d n)).toLp, ρe) := by
      have := lpVelocityTrajectory_data P (d n)
      rw [(hdmem n).2] at this
      rw [this]
    simp only [mem_ofPred_eq] at h1 ⊢
    rw [h2, lpStatePenalisedAnchored_carrier hG hω,
      lpStatePenalisedAnchored_carrier hG hω] at h1
    linarith
  interior n e α s hs := by
    have hmem := (hdmem n).1
    have hc : relaxedControlDistance P ρe ρ₀ ≤ ε := by
      have := hmem.2.2
      rw [← (hdmem n).2]
      exact this
    exact eventually_perturbProfile_mem_lpFreeTube γ₀ (lpVelocityTrajectory P (d n)) ρ₀ ρe
      (hv n) (hi n) hc e α s hs
  integrable n := intervalIntegrable_statePenalisedTubeLagrangian hG hω (j n) K γ₀ _ ρe
  differentiable₀ n := ((contDiff_tubeInitialPenalty K γ₀).differentiable one_ne_zero) _
  differentiable₁ n := ((contDiff_tubeEndpointPenalty K hT).differentiable one_ne_zero) _

omit [MeasurableSpace E] [BorelSpace E] in
/-- The `L²` energy of a carrier velocity is the squared norm of its class. -/
theorem integral_sq_velocity_eq_norm_sq_toLp (γ : VelocityTrajectory P) :
    (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s‖ ^ 2) = ‖γ.toLp‖ ^ 2 := by
  rw [Lp_two_norm_sq_eq_integral_norm_sq, intervalIntegral.integral_of_le P.horizon_pos.le]
  exact integral_congr_ae (by
    filter_upwards [γ.coeFn_toLp] with a ha
    rw [ha])

omit [MeasurableSpace E] [BorelSpace E] in
/-- A free-tube carrier has `L²` velocity energy at most `(‖φ₀'‖ + ε)²`. -/
theorem integral_sq_velocity_le_of_mem_lpFreeTube {ε : ℝ} (hε : 0 ≤ ε)
    (γ₀ γ : VelocityTrajectory P) (ρ₀ ρ : P.Relaxed)
    (hmem : (γ.initial, toWeakSpace ℝ _ γ.toLp, ρ) ∈ lpFreeTube P ε γ₀ ρ₀) :
    (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s‖ ^ 2) ≤ (‖γ₀.toLp‖ + ε) ^ 2 := by
  rw [integral_sq_velocity_eq_norm_sq_toLp]
  have h1 := ((mem_lpFreeTube_iff_carrier γ₀ γ ρ₀ ρ).1 hmem).1
  rw [integral_sq_velocity_sub_eq γ₀ γ, ← Lp_two_norm_sq_eq_integral_norm_sq] at h1
  have h2 : ‖γ.toLp - γ₀.toLp‖ ≤ ε := by
    have := abs_le_of_sq_le_sq' h1 hε
    exact this.2
  have h3 : ‖γ.toLp‖ ≤ ‖γ₀.toLp‖ + ε := by
    calc ‖γ.toLp‖ = ‖(γ.toLp - γ₀.toLp) + γ₀.toLp‖ := by rw [sub_add_cancel]
      _ ≤ ‖γ.toLp - γ₀.toLp‖ + ‖γ₀.toLp‖ := norm_add_le _ _
      _ ≤ ‖γ₀.toLp‖ + ε := by linarith
  exact pow_le_pow_left₀ (norm_nonneg _) h3 2

/-- The conclusion of the `j → ∞` limit at level `ε` (Lemma 11.3.5, (11.6.6), (11.6.11), (11.6.16)):
a limit path `γs`, which minimises the anchored pointwise penalty `F_K` over `B(ε)`, satisfies
`G ≤ 0` and all tube clauses strictly, together with a sequence of penalised minimisers for the
pointwise-defect Lagrangian whose multipliers converge to a nonincreasing `λ(ε;·)` with the costate
equation (`PenalisedMultiplierLimit`).

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.8), (11.3.9),
Lemma 11.3.5. -/
def TubeMultiplierLimit (P : Problem E V W) (K ε : ℝ) (γ₀ : VelocityTrajectory P)
    (ρ₀ ρe : P.Relaxed) (G : ℝ → E → ℝ) (Gx : ℝ → E → E →L[ℝ] ℝ)
    (Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)) (ω ω' : ℝ → ℝ)
    (cx : ℝ → E → E →L[ℝ] ℝ) (Fx : ℝ → E → E →L[ℝ] E) : Prop :=
  ∃ γs : VelocityTrajectory P,
    InVelocityControlTube P γ₀ ρ₀ ε γs ρe ∧
    (∀ γ' ρ', InVelocityControlTube P γ₀ ρ₀ ε γ' ρ' →
      velocityPenalizedPointwiseAnchored P K ε γ₀ ρ₀ γs ρe ≤
        velocityPenalizedPointwiseAnchored P K ε γ₀ ρ₀ γ' ρ') ∧
    (∀ t ∈ Icc (0 : ℝ) P.horizon, G t (γs.value t) ≤ 0) ∧
    (∫ s in (0 : ℝ)..P.horizon, ‖γs.velocity s - γ₀.velocity s‖ ^ 2) < ε ^ 2 ∧
    dist γs.initial γ₀.initial < ε ∧ relaxedControlDistance P ρe ρ₀ < ε ∧
    ∃ (seq : PenalisedMinimiserSequence P (tubeLagrangian P K γ₀ ρe) G ω
        (tubeInitialPenalty P K γ₀) (tubeEndpointPenalty P K)) (M : ℝ),
      PenalisedMultiplierLimit
        (pointwiseDefectStateCovector cx (averagedDynamics P ρe) Fx K)
        (pointwiseDefectVelocityCovector (averagedDynamics P ρe) γ₀.velocity K)
        ω' G Gx Gxd seq γs M

/-- **The `j → ∞` multiplier limit for the tube minimisers of (11.3.9)** (Berkovitz & Medhin,
Lemma 11.3.5, (11.6.6), (11.6.11), (11.6.16)).

Let `de = (φ_ε-datum, ν^ε)` minimise the anchored pointwise penalty `F_K` over `B(ε)` with
boundary positivity (`exists_anchored_tube_minimizer_of_boundary_positivity`), and let
`(φ_j, y_j)` minimise `H^j` over the free tube with frozen control `ν^ε` (item 1: they exist and are
eventually strictly interior).  Then there is a limit path `γ^ε` — an `F_K`-minimiser on `B(ε)`
satisfying the state constraint (item 2: strong `L²` and uniform convergence along a subsequence)
— and a subsequence of the minimisers (a `PenalisedMinimiserSequence` for the pointwise-defect
Lagrangian) whose multipliers converge to a nonincreasing `λ(ε;·)` with the costate equation
(11.6.11), (11.6.6), (11.6.16) (`PenalisedMultiplierLimit`).  The convergence data
`hLx`, `hGd`, `hLv` of `exists_stateMultiplier_limit_of_nondegenerate` are *derived*
(`PenalisedMinimiserSequence.convergenceData`), as is the multiplier mass bound (nondegeneracy,
Assumption 11.3.8, along the tube).

Remaining hypotheses (data regularity, not Lemma 11.3.5): the averaged data are regular
(`PointwiseDefectRegularity`) with the state/velocity covectors continuous in `(y,w)`; `G` is
regular with `∇²G(·)(1,·)` continuous; the endpoint constraint is `C¹`; `∇G ≠ 0` along tube paths.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.8), (11.3.9),
Lemma 11.3.5, Assumption 11.3.8. -/
theorem exists_stateMultiplierLimit_of_tubeMinimisers (P : Problem E V W)
    {G : ℝ → E → ℝ} {Gx : ℝ → E → E →L[ℝ] ℝ}
    {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)} {ω ω' : ℝ → ℝ}
    (hG : Continuous fun p : ℝ × E => G p.1 p.2)
    (hGP : ∀ (t : P.Time) (y : E), P.stateConstraint t y = G t y)
    (hGreg : StateConstraintRegularity G Gx) (hGx : StateGradientRegularity Gx Gxd)
    (hGdc : ∀ t, Continuous fun q : E × E => Gxd t q.1 (1, q.2))
    (hω₁ : IsStatePenaltyProfile ω) (hω₂ : StatePenaltyProfile ω ω')
    {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    (hT : ContDiff ℝ 1 (fun q : E × E => P.endpointConstraint q.1 q.2))
    {γ₀ : VelocityTrajectory P} {ρ₀ : P.Relaxed}
    {de : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed}
    (hde : de ∈ lpTube P ε γ₀ ρ₀)
    (hdemin : ∀ d ∈ lpTube P ε γ₀ ρ₀,
      lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ de ≤ lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ d)
    {J₀ : ℝ} (hdeJ : lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ de ≤ J₀)
    (hbdry : ∀ d, lpTubeBoundary P ε γ₀ ρ₀ d → J₀ < lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ d)
    {j : ℕ → ℝ} (hj : Tendsto j atTop atTop) (hj0 : ∀ n, 0 ≤ j n)
    {d : ℕ → E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed}
    (hdmem : ∀ n, d n ∈ lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = de.2.2})
    (hdmin : ∀ n, IsMinOn (lpStatePenalisedAnchored P G ω (j n) K ε γ₀ ρ₀)
      (lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = de.2.2}) (d n))
    {cx : ℝ → E → E →L[ℝ] ℝ} {Fx : ℝ → E → E →L[ℝ] E}
    (hreg : PointwiseDefectRegularity P.horizon
      (fun t y => P.horizon⁻¹ * averagedRunningCost P de.2.2 t y) cx
      (averagedDynamics P de.2.2) Fx γ₀.velocity K)
    (hLxc : ∀ t, Continuous fun q : E × E =>
      pointwiseDefectStateCovector cx (averagedDynamics P de.2.2) Fx K t q.1 q.2)
    (hLvc : ∀ t, Continuous fun q : E × E =>
      pointwiseDefectVelocityCovector (averagedDynamics P de.2.2) γ₀.velocity K t q.1 q.2)
    (hND : ∀ γ : VelocityTrajectory P, InVelocityControlTube P γ₀ ρ₀ ε γ de.2.2 →
      ∀ t ∈ Icc (0 : ℝ) P.horizon, Gx t (γ.value t) ≠ 0) :
    TubeMultiplierLimit P K ε γ₀ ρ₀ de.2.2 G Gx Gxd ω ω' cx Fx := by
  classical
  obtain ⟨γs, hγsmem, hγsmin, hγsG, hγsv, hγsi, hγsc, φ, hφ, hiT, hvT, hpT⟩ :=
    exists_subseq_tendsto_velocityStatePenalised_minimizer P hG hGP hω₁ hK hε hEnd hde hdemin
      hdeJ hbdry hj hj0 hdmem hdmin
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_strict_velocityStatePenalised_minimizer P hG
    hGP hω₁ hK hε hEnd hde hdemin hdeJ hbdry hj hj0 hdmem hdmin)
  have hφN : ∀ n, N ≤ φ (n + N) := fun n => (Nat.le_add_left N n).trans (hφ.id_le (n + N))
  set d' : ℕ → E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed :=
    fun n => d (φ (n + N)) with hd'
  set seq := tubeMinimiserSequence (P := P) (K := K) (ε := ε) (γ₀ := γ₀) (ρ₀ := ρ₀)
    (ρe := de.2.2) hG hω₁.continuous hT (j := fun n => j (φ (n + N))) (fun n => hj0 _)
    (d := d') (fun n => hdmem _) (fun n => hdmin _)
    (fun n => (hN _ (hφN n)).1) (fun n => (hN _ (hφN n)).2.1) with hseq
  -- convergence of the tail to the limit path
  have hpath : ∀ η > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) P.horizon,
      dist ((seq.path n).value t) (γs.value t) < η := fun η hη =>
    (tendsto_add_atTop_nat N).eventually (hpT η hη)
  have hvel : Tendsto (fun n => ∫ r in (0 : ℝ)..P.horizon,
      ‖(seq.path n).velocity r - γs.velocity r‖ ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => (lpVelocityTrajectory P (d' n)).toLp) atTop (𝓝 γs.toLp) :=
      hvT.comp (tendsto_add_atTop_nat N)
    have h2 : Tendsto (fun n => ‖(lpVelocityTrajectory P (d' n)).toLp - γs.toLp‖ ^ 2) atTop
        (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 h1).pow 2
      simpa using this
    refine h2.congr fun n => ?_
    rw [integral_sq_velocity_sub_eq γs, ← Lp_two_norm_sq_eq_integral_norm_sq]
    rfl
  have hD := hreg.isCaratheodoryC1
  obtain ⟨hLx, hGd, φ', hφ', hLv⟩ := PenalisedMinimiserSequence.convergenceData hD hLxc hLvc hGx
    hGdc seq γs hpath hvel
  set seq2 := seq.comp φ' with hseq2
  have hpath2 : ∀ η > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) P.horizon,
      dist ((seq2.path n).value t) (γs.value t) < η := fun η hη =>
    hφ'.tendsto_atTop.eventually (hpath η hη)
  have hΦ₀c : ContinuousAt (fderiv ℝ (tubeInitialPenalty P K γ₀)) (γs.value 0) :=
    ((contDiff_tubeInitialPenalty K γ₀).continuous_fderiv one_ne_zero).continuousAt
  have hΦ₁c : ContinuousAt (fderiv ℝ (tubeEndpointPenalty P K))
      (γs.value 0, γs.value P.horizon) :=
    ((contDiff_tubeEndpointPenalty K hT).continuous_fderiv one_ne_zero).continuousAt
  have hW : ∀ n, ∫ r in (0 : ℝ)..P.horizon, ‖(seq2.path n).velocity r‖ ^ 2
      ≤ (‖γ₀.toLp‖ + ε) ^ 2 := by
    intro n
    have hmem : (lpVelocityTrajectory P (d' (φ' n))).initial = (d' (φ' n)).1 := rfl
    have hdata := lpVelocityTrajectory_data P (d' (φ' n))
    have hfree : ((lpVelocityTrajectory P (d' (φ' n))).initial,
        toWeakSpace ℝ _ (lpVelocityTrajectory P (d' (φ' n))).toLp,
        (d' (φ' n)).2.2) ∈ lpFreeTube P ε γ₀ ρ₀ := by
      rw [hdata]; exact (hdmem _).1
    exact integral_sq_velocity_le_of_mem_lpFreeTube hε γ₀ _ ρ₀ _ hfree
  obtain ⟨M, hM⟩ := exists_stateMultiplier_limit_of_nondegenerate hD hω₂ hGreg hG hGx seq2 γs
    hpath2 (hLx.comp hφ'.tendsto_atTop) (hGd.comp hφ'.tendsto_atTop)
    (by
      simpa [hseq2, PenalisedMinimiserSequence.comp] using hLv)
    hΦ₀c hΦ₁c (hND γs hγsmem) hW
  exact ⟨γs, hγsmem, hγsmin, hγsG, hγsv, hγsi, hγsc, seq2, M, hM⟩

/-- **From the relaxed optimum to the `j → ∞` multiplier limit at level `ε`** (Berkovitz &
Medhin, Lemmas 11.3.3–11.3.5): given an optimal relaxed pair `(γ₀, ρ₀)`, there are a penalty scale
`K = K(ε)` and a control `ν^ε` (the `F_K`-minimiser on `B(ε)`) such that, for every regular
realisation of the averaged data, the minimisers of `H^j` over the free tube with frozen control
`ν^ε` exist (item 1) and yield the multiplier limit of `TubeMultiplierLimit` (item 2).

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemmas 11.3.3–11.3.5,
(11.3.8), (11.3.9). -/
theorem exists_tubeMultiplierLimit_of_relaxedMinimum (P : Problem E V W)
    {G : ℝ → E → ℝ} {Gx : ℝ → E → E →L[ℝ] ℝ}
    {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)} {ω ω' : ℝ → ℝ}
    (hG : Continuous fun p : ℝ × E => G p.1 p.2)
    (hGP : ∀ (t : P.Time) (y : E), P.stateConstraint t y = G t y)
    (hGreg : StateConstraintRegularity G Gx) (hGx : StateGradientRegularity Gx Gxd)
    (hGdc : ∀ t, Continuous fun q : E × E => Gxd t q.1 (1, q.2))
    (hω₁ : IsStatePenaltyProfile ω) (hω₂ : StatePenaltyProfile ω ω')
    {ε : ℝ} (hε : 0 < ε) (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    (hT : ContDiff ℝ 1 (fun q : E × E => P.endpointConstraint q.1 q.2))
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (hopt : P.IsRelaxedMinimum (toBoundedPath γ₀) ρ₀) :
    ∃ K : ℝ, 0 < K ∧ ∃ ρe : P.Relaxed,
      ∀ {cx : ℝ → E → E →L[ℝ] ℝ} {Fx : ℝ → E → E →L[ℝ] E},
        PointwiseDefectRegularity P.horizon
          (fun t y => P.horizon⁻¹ * averagedRunningCost P ρe t y) cx
          (averagedDynamics P ρe) Fx γ₀.velocity K →
        (∀ t, Continuous fun q : E × E =>
          pointwiseDefectStateCovector cx (averagedDynamics P ρe) Fx K t q.1 q.2) →
        (∀ t, Continuous fun q : E × E =>
          pointwiseDefectVelocityCovector (averagedDynamics P ρe) γ₀.velocity K t q.1 q.2) →
        (∀ γ : VelocityTrajectory P, InVelocityControlTube P γ₀ ρ₀ ε γ ρe →
          ∀ t ∈ Icc (0 : ℝ) P.horizon, Gx t (γ.value t) ≠ 0) →
        TubeMultiplierLimit P K ε γ₀ ρ₀ ρe G Gx Gxd ω ω' cx Fx := by
  classical
  obtain ⟨K, hK, de, hde, hdemin, hdeJ, hbdry⟩ :=
    exists_anchored_tube_minimizer_of_boundary_positivity P ε hε hEnd γ₀ ρ₀ hopt
  refine ⟨K, hK, de.2.2, fun {cx Fx} hreg hLxc hLvc hND => ?_⟩
  have hρe : relaxedControlDistance P de.2.2 ρ₀ ≤ ε := hde.1.2.2
  have hex : ∀ n : ℕ, ∃ d ∈ lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = de.2.2},
      IsMinOn (lpStatePenalisedAnchored P G ω (n : ℝ) K ε γ₀ ρ₀)
        (lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = de.2.2}) d := fun n =>
    exists_isMinOn_lpStatePenalisedAnchored P hG hω₁.continuous (n : ℝ) K ε hK.le hε.le hEnd γ₀
      ρ₀ de.2.2 hρe
  choose d hdmem hdmin using hex
  exact exists_stateMultiplierLimit_of_tubeMinimisers P hG hGP hGreg hGx hGdc hω₁ hω₂ hK.le hε.le
    hEnd hT hde hdemin hdeJ hbdry tendsto_natCast_atTop_atTop (fun n => Nat.cast_nonneg n) hdmem
    hdmin hreg hLxc hLvc hND

end Problem

end OptimalControl.BoundedState
