/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.Calculus.ACEulerLagrange
public import DynamicalSystems.OptimalControl.ContinuousTime.EndpointTransversalityConditions
public import DynamicalSystems.OptimalControl.ContinuousTime.VelocityTrajectories

/-!
# Endpoint transversality on the velocity carrier

`EndpointTransversalityConditions.lean` derives the endpoint relations (11.6.15)-(11.6.16) of
Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), §11.6, but assumes `x ∈ C¹`
and so cannot be applied to `γ.value`, the path `γ.initial + ∫₀ᵗ γ.velocity` of a
`VelocityTrajectory` (absolutely continuous, `γ.velocity ∈ L²`).  This file instantiates the
`C¹`-free weak Euler-Lagrange / transversality theorem of
`Mathlib/Analysis/Calculus/ACEulerLagrange.lean` on that carrier:

* `VelocityTrajectory.perturb`, `perturbProfile`: the perturbed carriers (affine perturbations of
  the initial value and velocity), which are again velocity trajectories;
* `penalizedFunctional_value_eq_actionFunctional`: the `deriv`-based penalized functional of the
  `C¹` engine agrees with the velocity-based action on the carrier;
* `VelocityTrajectory.endpointTransversality_of_isLocalMinOnProfiles` and
  `VelocityTrajectory.endpointTransversality_of_isMinOn`: the endpoint relations
  `p 0 = ∂Φ₀ + ∂₁Φ₁`, `p T = -∂₂Φ₁` for the absolutely continuous representative `p` of the
  momentum covector `momentumCovector L γ.value`, whose derivative is `stateCovector L γ.value`
  a.e. (the weak Euler-Lagrange equation).

The relations have exactly the shape of
`EndpointTransversality.momentumCovector_zero_eq_penalty_derivatives` and
`momentumCovector_horizon_eq_neg_penalty_derivative`; the only change is that the (a.e.-defined)
momentum covector at an endpoint is replaced by the value of its continuous representative.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology Interval

namespace OptimalControl.BoundedState

open ACEulerLagrange

variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]
  {P : Problem E V W}

namespace VelocityTrajectory

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The velocity of a carrier is an `L²(0,T)` function. -/
theorem memLp_velocity (γ : VelocityTrajectory P) :
    MemLp γ.velocity 2 (timeMeasure P.horizon) := by
  have hmeas : AEStronglyMeasurable γ.velocity (timeMeasure P.horizon) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le P.horizon_pos.le).1
      γ.velocity_intervalIntegrable).aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq_norm hmeas).2 γ.velocity_sq_integrable

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The carrier path is the primitive of its velocity. -/
theorem value_eq_primitive (γ : VelocityTrajectory P) :
    γ.value = primitive γ.initial γ.velocity := rfl

/-- The carrier `(γ.initial + θ a, γ.velocity + θ w)`: an affine perturbation of `γ` by an `L²`
test velocity `w` and an initial shift `a`.  It is again a velocity trajectory (absolutely
continuous with `L²` velocity), so it is an admissible competitor of the tube `B(ε)` whenever the
tube constraints are slack.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.1) and §11.6. -/
def perturb (γ : VelocityTrajectory P) (a : E) (w : ℝ → E)
    (hw : MemLp w 2 (timeMeasure P.horizon)) (θ : ℝ) : VelocityTrajectory P where
  initial := γ.initial + θ • a
  velocity := fun t => γ.velocity t + θ • w t
  velocity_intervalIntegrable :=
    γ.velocity_intervalIntegrable.add
      ((intervalIntegrable_of_memLp P.horizon_pos.le hw).smul θ)
  velocity_sq_integrable :=
    (memLp_two_iff_integrable_sq_norm
      ((γ.memLp_velocity.add (hw.const_smul θ)).aestronglyMeasurable)).1
      (γ.memLp_velocity.add (hw.const_smul θ))


omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The path of the perturbed carrier is the path plus `θ` times the primitive of the test
velocity. -/
theorem perturb_value (γ : VelocityTrajectory P) (a : E) (w : ℝ → E)
    (hw : MemLp w 2 (timeMeasure P.horizon)) (θ : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) P.horizon) :
    (γ.perturb a w hw θ).value t = γ.value t + θ • primitive a w t :=
  primitive_add_smul γ.initial a θ γ.velocity_intervalIntegrable
    (intervalIntegrable_of_memLp P.horizon_pos.le hw) ht

/-- The carrier perturbed in the scalar-profile direction `(α, s e)`: initial shift `α e`, velocity
shift `s(t) e`, so the displacement is `(α + ∫₀ᵗ s) e`. -/
def perturbProfile (γ : VelocityTrajectory P) (e : E) (α : ℝ)
    (s : ℝ → ℝ) (hs : MemLp s 2 (timeMeasure P.horizon)) (θ : ℝ) : VelocityTrajectory P :=
  γ.perturb (α • e) (fun t => s t • e) (memLp_smul_const hs e) θ

end VelocityTrajectory

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- A minimiser of `J` over `S`, all of whose scalar-profile perturbations lie in `S` for small
parameter, is a local minimiser along every scalar-profile direction. -/
theorem isLocalMinOnProfiles_of_isMinOn
    (γ : VelocityTrajectory P) (J : VelocityTrajectory P → ℝ) (S : Set (VelocityTrajectory P))
    (L : ℝ → E → E → ℝ) (Φ₀ : E → ℝ) (Φ₁ : E × E → ℝ)
    (hJ : ∀ γ' : VelocityTrajectory P,
      J γ' = actionFunctional L Φ₀ Φ₁ P.horizon γ'.initial γ'.velocity)
    (hmin : IsMinOn J S γ)
    (hinterior : ∀ (e : E) (α : ℝ) (s : ℝ → ℝ) (hs : MemLp s 2 (timeMeasure P.horizon)),
      ∀ᶠ θ in 𝓝 (0 : ℝ), γ.perturbProfile e α s hs θ ∈ S) :
    IsLocalMinOnProfiles L Φ₀ Φ₁ P.horizon γ.initial γ.velocity := by
  intro e α s hs
  filter_upwards [hinterior e α s hs] with θ hθ
  have h0 : actionFunctional L Φ₀ Φ₁ P.horizon (γ.initial + (0 : ℝ) • (α • e))
      (fun t => γ.velocity t + (0 : ℝ) • (s t • e))
        = actionFunctional L Φ₀ Φ₁ P.horizon γ.initial γ.velocity := by
    simp
  change actionFunctional L Φ₀ Φ₁ P.horizon (γ.initial + (0 : ℝ) • (α • e))
      (fun t => γ.velocity t + (0 : ℝ) • (s t • e)) ≤
    actionFunctional L Φ₀ Φ₁ P.horizon (γ.initial + θ • (α • e))
      (fun t => γ.velocity t + θ • (s t • e))
  rw [h0, ← hJ γ]
  exact (hJ (γ.perturbProfile e α s hs θ)) ▸ hmin hθ


omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The derivative of the carrier path is its velocity, almost everywhere on the horizon. -/
theorem VelocityTrajectory.ae_deriv_value (γ : VelocityTrajectory P) :
    ∀ᵐ t ∂(timeMeasure P.horizon), deriv γ.value t = γ.velocity t := by
  have h := (ae_restrict_iff' measurableSet_Icc).1 γ.ae_hasDerivAt_value
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [h] with t ht htm
  exact (ht (Ioc_subset_Icc_self htm)).deriv

/-- On the velocity carrier the `deriv`-based penalized functional of the `C¹` engine is the
velocity-based action functional. -/
theorem penalizedFunctional_value_eq_actionFunctional (γ : VelocityTrajectory P)
    (L : ℝ → E → E → ℝ) (Φ₀ : E → ℝ) (Φ₁ : E × E → ℝ) :
    EndpointTransversality.penalizedFunctional L Φ₀ Φ₁ P.horizon γ.value
      = actionFunctional L Φ₀ Φ₁ P.horizon γ.initial γ.velocity := by
  unfold EndpointTransversality.penalizedFunctional actionFunctional
  have hI : ∫ t in (0 : ℝ)..P.horizon, L t (γ.value t) (deriv γ.value t)
      = ∫ t in (0 : ℝ)..P.horizon, L t (primitive γ.initial γ.velocity t) (γ.velocity t) := by
    refine intervalIntegral.integral_congr_ae ?_
    have := (ae_restrict_iff' measurableSet_Ioc).1 γ.ae_deriv_value
    filter_upwards [this] with t ht htm
    rw [uIoc_of_le P.horizon_pos.le] at htm
    rw [ht htm]
    rfl
  rw [hI, VelocityTrajectory.value_zero]
  rfl

/-- **Endpoint transversality for the velocity carrier (weak form).**  Let `γ` be a velocity
trajectory (absolutely continuous, `γ' ∈ L²`, not `C¹`) and suppose the action
`∫₀ᵀ L(t, γ, γ') + Φ₀(γ 0) + Φ₁(γ 0, γ T)` is locally minimal at `γ` along every scalar-profile
test direction (`IsLocalMinOnProfiles`; in §11.6 this is the strict-interior minimality of the
pointwise-defect penalty, see `isLocalMinOnProfiles_of_isMinOn`).  Then the momentum covector
`∂ᵥL(t, γ t, γ' t)` has an absolutely continuous representative `p` with `p' = ∂ₓL` a.e. and

`p 0 = ∂Φ₀(γ 0) + ∂₁Φ₁(γ 0, γ T)`,  `p T = -∂₂Φ₁(γ 0, γ T)`.

These are the relations of `EndpointTransversality.momentumCovector_zero_eq_penalty_derivatives`
and `momentumCovector_horizon_eq_neg_penalty_derivative` with `momentumCovector L x 0` replaced by
the value of the representative `p` (the a.e.-defined momentum has no pointwise endpoint value).

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.6.15)-(11.6.16). -/
theorem VelocityTrajectory.endpointTransversality_of_isLocalMinOnProfiles
    [MeasurableSpace E] [BorelSpace E] (γ : VelocityTrajectory P)
    {L : ℝ → E → E → ℝ} {Lx Lv : ℝ → E → E → E →L[ℝ] ℝ}
    (hD : IsCaratheodoryC1 P.horizon L Lx Lv) {Φ₀ : E → ℝ} {Φ₁ : E × E → ℝ}
    (hint : IntervalIntegrable (fun t => L t (γ.value t) (γ.velocity t)) volume 0 P.horizon)
    (hΦ₀ : DifferentiableAt ℝ Φ₀ (γ.value 0))
    (hΦ₁ : DifferentiableAt ℝ Φ₁ (γ.value 0, γ.value P.horizon))
    (hmin : IsLocalMinOnProfiles L Φ₀ Φ₁ P.horizon γ.initial γ.velocity) :
    ∃ p : ℝ → E →L[ℝ] ℝ,
      ContinuousOn p (Icc (0 : ℝ) P.horizon) ∧
      (∀ᵐ t ∂(timeMeasure P.horizon),
        p t = EndpointTransversality.momentumCovector L γ.value t) ∧
      (∀ᵐ t ∂(timeMeasure P.horizon),
        HasDerivAt p (EndpointTransversality.stateCovector L γ.value t) t) ∧
      p 0 = fderiv ℝ Φ₀ (γ.value 0)
        + (fderiv ℝ Φ₁ (γ.value 0, γ.value P.horizon)).comp (ContinuousLinearMap.inl ℝ E E) ∧
      p P.horizon = -((fderiv ℝ Φ₁ (γ.value 0, γ.value P.horizon)).comp
        (ContinuousLinearMap.inr ℝ E E)) := by
  have hT0 : 0 ≤ P.horizon := P.horizon_pos.le
  have hv := γ.memLp_velocity
  have hv0 : γ.value 0 = γ.initial := γ.value_zero
  have hvT : γ.value P.horizon = primitive γ.initial γ.velocity P.horizon := rfl
  rw [hv0, hvT] at hΦ₁
  rw [hv0] at hΦ₀
  rw [hv0, hvT]
  have hΦ₀' : DifferentiableAt ℝ Φ₀ γ.initial := hΦ₀
  have hΦ₁' : DifferentiableAt ℝ Φ₁ (γ.initial, primitive γ.initial γ.velocity P.horizon) := hΦ₁
  obtain ⟨c, hEL, h0, hT⟩ := weakEulerLagrange_endpointTransversality hD P.horizon_pos hv
    γ.initial hint hΦ₀' hΦ₁' hmin
  obtain ⟨hcont, hderiv, hp0⟩ := momentumRepresentative_properties hD hT0 hv γ.initial c
  refine ⟨momentumRepresentative Lx γ.initial γ.velocity c, hcont, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hEL, γ.ae_deriv_value] with t ht hd
    unfold EndpointTransversality.momentumCovector
    rw [hd, hD.fderiv_velocity_eq]
    exact ht.symm
  · filter_upwards [hderiv, γ.ae_deriv_value] with t ht hd
    unfold EndpointTransversality.stateCovector
    rw [hd, hD.fderiv_state_eq]
    exact ht
  · rw [hp0, h0]
  · rw [← hT]
    rfl

/-- **Endpoint transversality from a minimiser on the velocity carrier.**  Let `J` be the penalty
functional on velocity trajectories, equal to the action `∫₀ᵀ L + Φ₀(γ 0) + Φ₁(γ 0, γ T)` of a
Carathéodory `C¹` Lagrangian, and let `γ` minimise `J` on a set `S` of competitors that contains
every scalar-profile perturbation of `γ` for small parameter (the *strict interior* of the
tube `B(ε)` of (11.3.2)).  Then the weak endpoint relations hold for the absolutely continuous
representative `p` of the momentum covector.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemma 11.3.4 and
(11.6.15)-(11.6.16). -/
theorem VelocityTrajectory.endpointTransversality_of_isMinOn
    [MeasurableSpace E] [BorelSpace E] (γ : VelocityTrajectory P)
    (J : VelocityTrajectory P → ℝ) (S : Set (VelocityTrajectory P))
    {L : ℝ → E → E → ℝ} {Lx Lv : ℝ → E → E → E →L[ℝ] ℝ}
    (hD : IsCaratheodoryC1 P.horizon L Lx Lv) {Φ₀ : E → ℝ} {Φ₁ : E × E → ℝ}
    (hJ : ∀ γ' : VelocityTrajectory P,
      J γ' = actionFunctional L Φ₀ Φ₁ P.horizon γ'.initial γ'.velocity)
    (hmin : IsMinOn J S γ)
    (hinterior : ∀ (e : E) (α : ℝ) (s : ℝ → ℝ) (hs : MemLp s 2 (timeMeasure P.horizon)),
      ∀ᶠ θ in 𝓝 (0 : ℝ), γ.perturbProfile e α s hs θ ∈ S)
    (hint : IntervalIntegrable (fun t => L t (γ.value t) (γ.velocity t)) volume 0 P.horizon)
    (hΦ₀ : DifferentiableAt ℝ Φ₀ (γ.value 0))
    (hΦ₁ : DifferentiableAt ℝ Φ₁ (γ.value 0, γ.value P.horizon)) :
    ∃ p : ℝ → E →L[ℝ] ℝ,
      ContinuousOn p (Icc (0 : ℝ) P.horizon) ∧
      (∀ᵐ t ∂(timeMeasure P.horizon),
        p t = EndpointTransversality.momentumCovector L γ.value t) ∧
      (∀ᵐ t ∂(timeMeasure P.horizon),
        HasDerivAt p (EndpointTransversality.stateCovector L γ.value t) t) ∧
      p 0 = fderiv ℝ Φ₀ (γ.value 0)
        + (fderiv ℝ Φ₁ (γ.value 0, γ.value P.horizon)).comp (ContinuousLinearMap.inl ℝ E E) ∧
      p P.horizon = -((fderiv ℝ Φ₁ (γ.value 0, γ.value P.horizon)).comp
        (ContinuousLinearMap.inr ℝ E E)) :=
  γ.endpointTransversality_of_isLocalMinOnProfiles hD hint hΦ₀ hΦ₁
    (isLocalMinOnProfiles_of_isMinOn γ J S L Φ₀ Φ₁ hJ hmin hinterior)

/-- **Consistency with the `C¹` engine.**  If the (a.e.-defined) momentum covector along the
carrier happens to be continuous on the horizon, then it equals its absolutely continuous
representative everywhere on `[0,T]`, and the weak endpoint relations become exactly
`EndpointTransversality.momentumCovector_zero_eq_penalty_derivatives` and
`momentumCovector_horizon_eq_neg_penalty_derivative`, with no `C¹` hypothesis on the path.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.6.15)-(11.6.16). -/
theorem VelocityTrajectory.momentumCovector_endpoints_of_continuousOn
    [MeasurableSpace E] [BorelSpace E] (γ : VelocityTrajectory P)
    {L : ℝ → E → E → ℝ} {Lx Lv : ℝ → E → E → E →L[ℝ] ℝ}
    (hD : IsCaratheodoryC1 P.horizon L Lx Lv) {Φ₀ : E → ℝ} {Φ₁ : E × E → ℝ}
    (hint : IntervalIntegrable (fun t => L t (γ.value t) (γ.velocity t)) volume 0 P.horizon)
    (hΦ₀ : DifferentiableAt ℝ Φ₀ (γ.value 0))
    (hΦ₁ : DifferentiableAt ℝ Φ₁ (γ.value 0, γ.value P.horizon))
    (hmin : IsLocalMinOnProfiles L Φ₀ Φ₁ P.horizon γ.initial γ.velocity)
    (hmom : ContinuousOn (EndpointTransversality.momentumCovector L γ.value)
      (Icc (0 : ℝ) P.horizon)) :
    EndpointTransversality.momentumCovector L γ.value 0 = fderiv ℝ Φ₀ (γ.value 0)
        + (fderiv ℝ Φ₁ (γ.value 0, γ.value P.horizon)).comp (ContinuousLinearMap.inl ℝ E E) ∧
      EndpointTransversality.momentumCovector L γ.value P.horizon
        = -((fderiv ℝ Φ₁ (γ.value 0, γ.value P.horizon)).comp
          (ContinuousLinearMap.inr ℝ E E)) := by
  obtain ⟨p, hpc, hae, -, h0, hT⟩ :=
    γ.endpointTransversality_of_isLocalMinOnProfiles hD hint hΦ₀ hΦ₁ hmin
  have hne : (0 : ℝ) ≠ P.horizon := P.horizon_pos.ne
  have hae' : p =ᵐ[volume.restrict (Icc (0 : ℝ) P.horizon)]
      EndpointTransversality.momentumCovector L γ.value := by
    have h := (ae_restrict_iff' measurableSet_Ioc).1 hae
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
    have hnull : ∀ᵐ t : ℝ, t ≠ 0 := by
      simp [ae_iff]
    filter_upwards [h, hnull] with t ht ht0 htI
    exact ht ⟨lt_of_le_of_ne htI.1 (Ne.symm ht0), htI.2⟩
  have heq := Measure.eqOn_Icc_of_ae_eq (μ := volume) hne hae' hpc hmom
  refine ⟨?_, ?_⟩
  · rw [← heq ⟨le_rfl, P.horizon_pos.le⟩]
    exact h0
  · rw [← heq ⟨P.horizon_pos.le, le_rfl⟩]
    exact hT

end OptimalControl.BoundedState
