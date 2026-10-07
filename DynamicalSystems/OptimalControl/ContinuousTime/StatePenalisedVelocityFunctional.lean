/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.VelocityPointwiseEndpointConditions

/-!
# The `ω`-penalised functional `H^j_{K(ε)}` on the velocity carrier

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), §11.3 and §11.6.  The state
inequality `G(t, φ(t)) ≤ 0` is handled in (11.3.8) by the penalised functional

`H^j(φ,ν) = j ∫₀^{t₁} ω(G(t, φ(t))) dt + F_K(φ,ν)`,

where `ω` is a `C¹` function vanishing on `(-∞, 0]` with `ω' ≥ 0`.  This file instantiates `H^j` on
the absolutely continuous / `L²`-velocity carrier `VelocityTrajectory`:

* `StatePenaltyProfile ω ω'` — the properties of `ω` used by the book (`C¹`, `ω' ≥ 0`,
  `ω = 0` on `(-∞,0]`), with `StatePenaltyProfile.deriv_eq_zero_of_nonpos`: `ω' = 0` on `(-∞,0]`;
* `StateConstraintRegularity G Gx` — Carathéodory regularity of the state constraint `G` and its
  state covector `Gx = ∇G` (measurable, `C¹` in the state, bounded on bounded sets);
* `statePenalisedLagrangian L G ω j = L + j ω(G)`, whose velocity covector is that of `L` and whose
  state covector is `Lx + j ω'(G) ∇G` (`statePenalisedStateCovector`);
* `IsCaratheodoryC1.statePenalised`: the penalised Lagrangian is again Carathéodory `C¹`;
* `VelocityTrajectory.statePenalised_weakEulerLagrange`: for a minimiser `γ` of `H^j` on a set `S`
  containing the scalar-profile perturbations, the *integrated* Euler–Lagrange equation
  `∂ᵥL = c + ∫₀ᵗ (∂ₓL + j ω'(G) ∇G)` a.e., with the endpoint relations (11.6.15)-(11.6.16) for the
  constant `c`;
* `VelocityTrajectory.pointwiseDefect_statePenalised_weakEulerLagrange`: the same for the §11.6
  pointwise-defect Lagrangian with its initial and endpoint penalties.

The multiplier `j ω'(G(t,γ(t)))` is the density of the book's state-multiplier measure at level `j`;
`StateMultiplierCostate.lean` turns it into the nonincreasing multiplier `λ` and the costate
equation (11.6.11).  Book citations live in docstrings only.
-/

@[expose] public section

open Set MeasureTheory Filter ACEulerLagrange
open scoped Topology Interval

namespace OptimalControl.BoundedState

/-- The properties of the penalty profile `ω` of (11.3.8) used in §11.6: `ω` is `C¹` with
derivative `ω'`, `ω' ≥ 0`, and `ω = 0` on `(-∞, 0]`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.8). -/
structure StatePenaltyProfile (ω ω' : ℝ → ℝ) : Prop where
  /-- `ω` has derivative `ω'`. -/
  hasDerivAt : ∀ s, HasDerivAt ω (ω' s) s
  /-- `ω'` is continuous. -/
  continuous_deriv : Continuous ω'
  /-- `ω' ≥ 0`. -/
  deriv_nonneg : ∀ s, 0 ≤ ω' s
  /-- `ω` vanishes on `(-∞, 0]`. -/
  eq_zero_of_nonpos : ∀ s, s ≤ 0 → ω s = 0

namespace StatePenaltyProfile

variable {ω ω' : ℝ → ℝ}

/-- The penalty profile is continuous. -/
theorem continuous (h : StatePenaltyProfile ω ω') : Continuous ω :=
  continuous_iff_continuousAt.2 fun s => (h.hasDerivAt s).continuousAt

/-- The derivative of the penalty profile vanishes on `(-∞, 0]`: the penalty exerts no force on
slack states and on the contact set. -/
theorem deriv_eq_zero_of_nonpos (h : StatePenaltyProfile ω ω') {s : ℝ} (hs : s ≤ 0) :
    ω' s = 0 := by
  have h1 : HasDerivWithinAt ω (ω' s) (Iic (0 : ℝ)) s := (h.hasDerivAt s).hasDerivWithinAt
  have h2 : HasDerivWithinAt ω (0 : ℝ) (Iic (0 : ℝ)) s :=
    (hasDerivWithinAt_const s (Iic (0 : ℝ)) (0 : ℝ)).congr
      (fun y hy => h.eq_zero_of_nonpos y hy) (h.eq_zero_of_nonpos s hs)
  exact (uniqueDiffOn_Iic (0 : ℝ) s hs).eq_deriv _ h1 h2

end StatePenaltyProfile

/-- **The library's smooth hinge is a penalty profile.**  `smoothHinge = expNegInvGlue` with
`ω' = deriv smoothHinge` satisfies `StatePenaltyProfile`: it is `C^∞`, nondecreasing (so
`ω' ≥ 0`) and vanishes on `(-∞, 0]`.  This is the concrete `ω` of (11.3.8).

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.8). -/
theorem statePenaltyProfile_smoothHinge : StatePenaltyProfile smoothHinge (deriv smoothHinge) where
  hasDerivAt s := (smoothHinge_contDiff.differentiable (by simp) s).hasDerivAt
  continuous_deriv := smoothHinge_contDiff.continuous_deriv (by simp)
  deriv_nonneg s :=
    ((smoothHinge_contDiff.differentiable (by simp) s).hasDerivAt).nonneg_of_monotone
      expNegInvGlue.monotone
  eq_zero_of_nonpos _ hs := smoothHinge_zero_of_nonpos hs

section StateConstraint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Carathéodory regularity of the state constraint `G(t,x)` with state covector `Gx = ∇G`:
differentiable in the state, jointly measurable, and bounded together with `∇G` on bounded sets.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.6.1 and
(11.6.2). -/
structure StateConstraintRegularity (G : ℝ → E → ℝ) (Gx : ℝ → E → E →L[ℝ] ℝ) : Prop where
  /-- `Gx` is the Fréchet derivative of `G` in the state. -/
  hasFDerivAt : ∀ t y, HasFDerivAt (G t) (Gx t y) y
  /-- `G` is jointly measurable. -/
  measurable_G : Measurable (fun p : ℝ × E => G p.1 p.2)
  /-- `Gx` is jointly measurable. -/
  measurable_Gx : Measurable (fun p : ℝ × E => Gx p.1 p.2)
  /-- `G` and `Gx` are bounded on bounded sets of states. -/
  bounded : ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t y, ‖y‖ ≤ R → |G t y| ≤ C ∧ ‖Gx t y‖ ≤ C

/-- The `ω`-penalised Lagrangian `L + j ω(G)` of the functional `H^j` of (11.3.8).

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.8). -/
noncomputable def statePenalisedLagrangian (L : ℝ → E → E → ℝ) (G : ℝ → E → ℝ) (ω : ℝ → ℝ)
    (j : ℝ) (t : ℝ) (x v : E) : ℝ :=
  L t x v + j * ω (G t x)

/-- The state covector `∂ₓL + j ω'(G) ∇G` of the `ω`-penalised Lagrangian: the book's
`f₁⁰ + j ω'(G) ∇G` of (11.6.9) at level `j`. -/
noncomputable def statePenalisedStateCovector (Lx : ℝ → E → E → E →L[ℝ] ℝ) (G : ℝ → E → ℝ)
    (ω' : ℝ → ℝ) (Gx : ℝ → E → E →L[ℝ] ℝ) (j : ℝ) (t : ℝ) (x v : E) : E →L[ℝ] ℝ :=
  Lx t x v + (j * ω' (G t x)) • Gx t x

variable {T : ℝ} {L : ℝ → E → E → ℝ} {Lx Lv : ℝ → E → E → E →L[ℝ] ℝ} {ω ω' : ℝ → ℝ}
  {G : ℝ → E → ℝ} {Gx : ℝ → E → E →L[ℝ] ℝ}

omit [BorelSpace E] in
/-- The `ω`-penalised Lagrangian is Carathéodory `C¹`, with velocity covector `Lv` unchanged and
state covector `statePenalisedStateCovector`. -/
theorem isCaratheodoryC1_statePenalised (hD : IsCaratheodoryC1 T L Lx Lv)
    (hω : StatePenaltyProfile ω ω') (hG : StateConstraintRegularity G Gx) (j : ℝ) :
    IsCaratheodoryC1 T (statePenalisedLagrangian L G ω j)
      (statePenalisedStateCovector Lx G ω' Gx j) Lv := by
  have hπ : Measurable (fun p : ℝ × E × E => ((p.1, p.2.1) : ℝ × E)) := by fun_prop
  have hG' : Measurable (fun p : ℝ × E × E => G p.1 p.2.1) := hG.measurable_G.comp hπ
  have hGx' : Measurable (fun p : ℝ × E × E => Gx p.1 p.2.1) := hG.measurable_Gx.comp hπ
  have hωm : Measurable ω := hω.continuous.measurable
  have hω'm : Measurable ω' := hω.continuous_deriv.measurable
  refine ⟨?_, ?_, ?_, hD.measurable_Lv, ?_⟩
  · intro t y w
    have h1 := hD.hasFDerivAt t y w
    have h2 : HasFDerivAt (fun u : E => ω (G t u)) (ω' (G t y) • Gx t y) y :=
      (hω.hasDerivAt (G t y)).comp_hasFDerivAt y (hG.hasFDerivAt t y)
    have h3 : HasFDerivAt (fun q : E × E => j * ω (G t q.1))
        ((j * ω' (G t y)) • (Gx t y).comp (ContinuousLinearMap.fst ℝ E E)) (y, w) := by
      have := (h2.comp (y, w)
        (hasFDerivAt_fst (𝕜 := ℝ) (E := E) (F := E) (p := (y, w)))).const_mul j
      refine this.congr_fderiv ?_
      ext q <;> simp [mul_smul]
    have h4 := h1.add h3
    unfold statePenalisedLagrangian
    refine h4.congr_fderiv ?_
    ext q <;> simp [statePenalisedStateCovector]
  · unfold statePenalisedLagrangian
    exact hD.measurable_L.add (((hωm.comp hG').const_mul j))
  · unfold statePenalisedStateCovector
    exact hD.measurable_Lx.add ((((hω'm.comp hG').const_mul j)).smul hGx')
  · intro R
    obtain ⟨a, C, ha, hC0, hb⟩ := hD.growth R
    obtain ⟨CG, hCG0, hGb⟩ := hG.bounded R
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := -CG) (b := CG)).exists_bound_of_continuousOn
      hω.continuous_deriv.continuousOn
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨by linarith, hCG0⟩)
    have ha' : MemLp (fun t => a t + |j| * M * CG) 2 (timeMeasure T) :=
      ha.add (memLp_const _)
    refine ⟨fun t => a t + |j| * M * CG, C, ha', hC0, fun t y w hy => ?_⟩
    obtain ⟨hGy, hGxy⟩ := hGb t y hy
    have hω'b : |ω' (G t y)| ≤ M := by
      have := hM (G t y) ⟨by linarith [(abs_le.1 hGy).1], (abs_le.1 hGy).2⟩
      simpa [Real.norm_eq_abs] using this
    have hpen : ‖(j * ω' (G t y)) • Gx t y‖ ≤ |j| * M * CG := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul]
      have h1 : |j| * |ω' (G t y)| ≤ |j| * M := by gcongr
      calc |j| * |ω' (G t y)| * ‖Gx t y‖ ≤ |j| * M * ‖Gx t y‖ := by gcongr
        _ ≤ |j| * M * CG := by gcongr
    obtain ⟨hb1, hb2⟩ := hb t y w hy
    have hnn : 0 ≤ |j| * M * CG := by positivity
    constructor
    · unfold statePenalisedStateCovector
      calc ‖Lx t y w + (j * ω' (G t y)) • Gx t y‖
          ≤ ‖Lx t y w‖ + ‖(j * ω' (G t y)) • Gx t y‖ := norm_add_le _ _
        _ ≤ (a t + C * ‖w‖) + |j| * M * CG := add_le_add hb1 hpen
        _ = _ := by ring
    · linarith

end StateConstraint

section Carrier

variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]
  {P : Problem E V W}

/-- **The integrated Euler-Lagrange equation of the `ω`-penalised functional `H^j` on the velocity
carrier, with the endpoint relations (11.6.15)-(11.6.16).**  Let `γ` minimise
`J = ∫₀ᵀ (L + j ω(G)) + Φ₀(γ 0) + Φ₁(γ 0, γ T)` over a set `S` containing every scalar-profile
perturbation of `γ` for small parameter (the strict interior of the tube `B(ε)` of (11.3.2): the
state inequality is *not* part of `S`, it is enforced by the penalty).  Then there is a covector
`c` with

* `∂ᵥL(t,γ,γ') = c + ∫₀ᵗ (∂ₓL + j ω'(G(r,γ r)) ∇G(r,γ r)) dr` a.e.  — (11.6.9)-(11.6.10) with the
  state-multiplier density `j ω'(G)` at level `j`;
* `c = ∂Φ₀(γ 0) + ∂₁Φ₁(γ 0, γ T)`  — (11.6.15), the initial condition;
* `c + ∫₀ᵀ (∂ₓL + j ω'(G) ∇G) = -∂₂Φ₁(γ 0, γ T)`  — (11.6.16).

No strict slackness of the state constraint is assumed, so this removes the restriction `G2` of the
earlier endpoint theorems: the active constraint enters only through the term `j ω'(G) ∇G`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.8) and
(11.6.8)-(11.6.16). -/
theorem VelocityTrajectory.statePenalised_weakEulerLagrange (γ : VelocityTrajectory P)
    (J : VelocityTrajectory P → ℝ) (S : Set (VelocityTrajectory P))
    {L : ℝ → E → E → ℝ} {Lx Lv : ℝ → E → E → E →L[ℝ] ℝ}
    (hD : IsCaratheodoryC1 P.horizon L Lx Lv) {ω ω' : ℝ → ℝ}
    (hω : StatePenaltyProfile ω ω') {G : ℝ → E → ℝ} {Gx : ℝ → E → E →L[ℝ] ℝ}
    (hG : StateConstraintRegularity G Gx) (j : ℝ) {Φ₀ : E → ℝ} {Φ₁ : E × E → ℝ}
    (hJ : ∀ γ' : VelocityTrajectory P,
      J γ' = actionFunctional (statePenalisedLagrangian L G ω j) Φ₀ Φ₁ P.horizon
        γ'.initial γ'.velocity)
    (hmin : IsMinOn J S γ)
    (hinterior : ∀ (e : E) (α : ℝ) (s : ℝ → ℝ) (hs : MemLp s 2 (timeMeasure P.horizon)),
      ∀ᶠ θ in 𝓝 (0 : ℝ), γ.perturbProfile e α s hs θ ∈ S)
    (hint : IntervalIntegrable
      (fun t => statePenalisedLagrangian L G ω j t (γ.value t) (γ.velocity t))
      volume 0 P.horizon)
    (hΦ₀ : DifferentiableAt ℝ Φ₀ (γ.value 0))
    (hΦ₁ : DifferentiableAt ℝ Φ₁ (γ.value 0, γ.value P.horizon)) :
    ∃ c : E →L[ℝ] ℝ,
      (∀ᵐ t ∂(timeMeasure P.horizon), Lv t (γ.value t) (γ.velocity t)
        = c + ∫ r in (0 : ℝ)..t, (Lx r (γ.value r) (γ.velocity r)
          + (j * ω' (G r (γ.value r))) • Gx r (γ.value r))) ∧
      c = fderiv ℝ Φ₀ (γ.value 0)
        + (fderiv ℝ Φ₁ (γ.value 0, γ.value P.horizon)).comp (ContinuousLinearMap.inl ℝ E E) ∧
      c + ∫ r in (0 : ℝ)..P.horizon, (Lx r (γ.value r) (γ.velocity r)
          + (j * ω' (G r (γ.value r))) • Gx r (γ.value r))
        = -((fderiv ℝ Φ₁ (γ.value 0, γ.value P.horizon)).comp (ContinuousLinearMap.inr ℝ E E)) := by
  have hDj := isCaratheodoryC1_statePenalised hD hω hG j
  have hloc := isLocalMinOnProfiles_of_isMinOn γ J S _ Φ₀ Φ₁ hJ hmin hinterior
  have hv := γ.memLp_velocity
  have hv0 : γ.value 0 = γ.initial := γ.value_zero
  have hvT : γ.value P.horizon = primitive γ.initial γ.velocity P.horizon := rfl
  rw [hv0, hvT] at hΦ₁
  rw [hv0] at hΦ₀
  rw [hv0, hvT]
  obtain ⟨c, hEL, h0, hT⟩ := weakEulerLagrange_endpointTransversality hDj P.horizon_pos hv
    γ.initial hint hΦ₀ hΦ₁ hloc
  exact ⟨c, hEL, h0, hT⟩

end Carrier

section PointwiseDefectCarrier

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]
  {P : Problem E V W}

/-- **The §11.6 pointwise-defect penalty with the `ω`-penalised state constraint:
endpoint relations (11.6.15)-(11.6.16) and the integrated Euler-Lagrange equation for an active
state constraint.**  Let `J` be the penalised functional
`∫₀ᵀ [c + ‖γ' - φ₀'‖² + K‖γ' - f‖² + j ω(G)] dt + ‖γ 0 - a‖² + κ‖γ 0 - b‖² + K‖T(γ 0, γ T)‖²`
(`H^j_{K}` of (11.3.8) with the control averaged out; `κ = 0` is the book's, `κ = K`, `b =
P.initial`
is the library's anchored penalty), and let `γ` minimise `J` on a set `S` containing the
scalar-profile perturbations of `γ`.  Then there is a covector `c₀` with

* `2⟨γ' - φ₀', ·⟩ + 2K⟨γ' - f, ·⟩ = c₀ + ∫₀ᵗ (c_x - 2K⟨γ' - f, f_x ·⟩ + j ω'(G) ∇G)` a.e.;
* `c₀ = 2⟨γ 0 - a, ·⟩ + 2κ⟨γ 0 - b, ·⟩ + 2K⟨T(γ 0, γ T), ∂₁T ·⟩`  — (11.6.15);
* `c₀ + ∫₀ᵀ (c_x - 2K⟨γ' - f, f_x ·⟩ + j ω'(G) ∇G) = -2K⟨T(γ 0, γ T), ∂₂T ·⟩`  — (11.6.16).

The state constraint need not be slack along `γ` (the gap `G2`): its force is the term
`j ω'(G) ∇G`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.6), (11.3.8) and
(11.6.8)-(11.6.16). -/
theorem VelocityTrajectory.pointwiseDefect_statePenalised_weakEulerLagrange (γ : VelocityTrajectory
    P)
    (J : VelocityTrajectory P → ℝ) (S : Set (VelocityTrajectory P))
    {c : ℝ → E → ℝ} {cx : ℝ → E → E →L[ℝ] ℝ} {F : ℝ → E → E} {Fx : ℝ → E → E →L[ℝ] E}
    {r : ℝ → E} {K : ℝ} (hreg : PointwiseDefectRegularity P.horizon c cx F Fx r K)
    {ω ω' : ℝ → ℝ} (hω : StatePenaltyProfile ω ω') {G : ℝ → E → ℝ}
    {Gx : ℝ → E → E →L[ℝ] ℝ} (hG : StateConstraintRegularity G Gx) (j : ℝ)
    (a b : E) (κ : ℝ) (Tend : E → E → W) (D₁ : E →L[ℝ] W) (D₂ : E →L[ℝ] W)
    (hT : HasFDerivAt (fun q : E × E => Tend q.1 q.2)
      (D₁.comp (ContinuousLinearMap.fst ℝ E E) + D₂.comp (ContinuousLinearMap.snd ℝ E E))
      (γ.value 0, γ.value P.horizon))
    (hJ : ∀ γ' : VelocityTrajectory P,
      J γ' = actionFunctional
        (statePenalisedLagrangian (pointwiseDefectLagrangian c F r K) G ω j)
        (fun y : E => ‖y - a‖ ^ 2 + κ * ‖y - b‖ ^ 2)
        (fun q : E × E => K * ‖Tend q.1 q.2‖ ^ 2) P.horizon γ'.initial γ'.velocity)
    (hmin : IsMinOn J S γ)
    (hinterior : ∀ (e : E) (α : ℝ) (s : ℝ → ℝ) (hs : MemLp s 2 (timeMeasure P.horizon)),
      ∀ᶠ θ in 𝓝 (0 : ℝ), γ.perturbProfile e α s hs θ ∈ S)
    (hint : IntervalIntegrable
      (fun t => statePenalisedLagrangian (pointwiseDefectLagrangian c F r K) G ω j t
        (γ.value t) (γ.velocity t)) volume 0 P.horizon) :
    ∃ c₀ : E →L[ℝ] ℝ,
      (∀ᵐ t ∂(timeMeasure P.horizon),
        pointwiseDefectVelocityCovector F r K t (γ.value t) (γ.velocity t)
          = c₀ + ∫ s in (0 : ℝ)..t,
            (pointwiseDefectStateCovector cx F Fx K s (γ.value s) (γ.velocity s)
              + (j * ω' (G s (γ.value s))) • Gx s (γ.value s))) ∧
      c₀ = (2 : ℝ) • innerSL ℝ (γ.value 0 - a) + (2 * κ) • innerSL ℝ (γ.value 0 - b)
        + (2 * K) • (innerSL ℝ (Tend (γ.value 0) (γ.value P.horizon))).comp D₁ ∧
      c₀ + ∫ s in (0 : ℝ)..P.horizon,
          (pointwiseDefectStateCovector cx F Fx K s (γ.value s) (γ.velocity s)
            + (j * ω' (G s (γ.value s))) • Gx s (γ.value s))
        = -((2 * K) • (innerSL ℝ (Tend (γ.value 0) (γ.value P.horizon))).comp D₂) := by
  have hD := hreg.isCaratheodoryC1
  have hΦ₀ : HasFDerivAt (fun y : E => ‖y - a‖ ^ 2 + κ * ‖y - b‖ ^ 2)
      ((2 : ℝ) • innerSL ℝ (γ.value 0 - a) + (2 * κ) • innerSL ℝ (γ.value 0 - b))
      (γ.value 0) := by
    have h := (hasFDerivAt_initialPenalty a (γ.value 0)).add
      ((hasFDerivAt_initialPenalty b (γ.value 0)).const_mul κ)
    refine h.congr_fderiv (ContinuousLinearMap.ext fun z => ?_)
    simp
    ring
  have hΦ₁ := hasFDerivAt_endpointPenalty (K := K) hT
  obtain ⟨c₀, hEL, h0, hT'⟩ := γ.statePenalised_weakEulerLagrange J S hD hω hG j hJ hmin
    hinterior hint hΦ₀.differentiableAt hΦ₁.differentiableAt
  refine ⟨c₀, hEL, ?_, ?_⟩
  · rw [h0, hΦ₀.fderiv, hΦ₁.fderiv]
    ext z
    simp
  · rw [hT', hΦ₁.fderiv]
    ext z
    simp

end PointwiseDefectCarrier

end OptimalControl.BoundedState
