/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.StatePenalisedTubeLimit
public import DynamicalSystems.OptimalControl.ContinuousTime.EpsilonLimitPassage

/-!
# From the `j → ∞` limit at level `ε` to the `ε`-level costate system

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.25), (11.3.33),
(11.3.34), (11.6.11), §11.4.

`StatePenalisedTubeLimit.lean` delivers, at a fixed level `ε`, the limit `λ(ε;·)` of the
penalised multipliers and the costate `Φ(ε;·)` of the pointwise-defect Lagrangian
(`PenalisedMultiplierLimit`).  This file rewrites that output in the linear form (11.3.25) used by
the `ε → 0` limiting operations of `EpsilonLimitPassage.lean`:

`Φ' = f⁰ₓ − (Φ − λ∇G − 2⟨φ_ε' − φ₀',·⟩)·fₓ + λ d(∇G)/dt`, `Φ(0) = ι + β·∂₁T + λ(0)∇G(0)`,
`Φ(T) = −β·∂₂T`,

with the endpoint multiplier `β_ε = (2K T(φ_ε(0),φ_ε(T)), 2K(φ_ε(0) − x₀))` (the second component is
the multiplier of the anchored initial condition).

* `tubeCostateSystem`: the explicit `EpsilonCostateSystem` of a tube limit.
* `exists_epsilonCostateSystem_of_penalisedMultiplierLimit`: it satisfies
  `IsEpsilonCostateSystem`.

Book citations live in docstrings only.
-/

@[expose] public section

open Set MeasureTheory Filter ACEulerLagrange
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

/-- The covector map `(b₁,b₂) ↦ b₁∘∂₁T + b₂` of the initial-time endpoint multipliers. -/
noncomputable def tubeDl (DT : E × E →L[ℝ] W) :
    ((W →L[ℝ] ℝ) × (E →L[ℝ] ℝ)) →L[ℝ] (E →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ E W ℝ).flip (DT.comp (ContinuousLinearMap.inl ℝ E E))).comp
      (ContinuousLinearMap.fst ℝ (W →L[ℝ] ℝ) (E →L[ℝ] ℝ))
    + ContinuousLinearMap.snd ℝ (W →L[ℝ] ℝ) (E →L[ℝ] ℝ)

/-- The covector map `(b₁,b₂) ↦ b₁∘∂₂T` of the terminal-time endpoint multipliers. -/
noncomputable def tubeDr (DT : E × E →L[ℝ] W) :
    ((W →L[ℝ] ℝ) × (E →L[ℝ] ℝ)) →L[ℝ] (E →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ E W ℝ).flip
    (DT.comp (ContinuousLinearMap.inr ℝ E E))).comp
      (ContinuousLinearMap.fst ℝ (W →L[ℝ] ℝ) (E →L[ℝ] ℝ))


omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- `∂T ↦ Dl` is continuous. -/
theorem continuous_tubeDl : Continuous (tubeDl : (E × E →L[ℝ] W) → _) := by
  unfold tubeDl
  exact ((((ContinuousLinearMap.compL ℝ E W ℝ).flip.continuous.comp
    (continuous_id.clm_comp continuous_const)).clm_comp continuous_const).add continuous_const)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- `∂T ↦ Dr` is continuous. -/
theorem continuous_tubeDr : Continuous (tubeDr : (E × E →L[ℝ] W) → _) := by
  unfold tubeDr
  exact (((ContinuousLinearMap.compL ℝ E W ℝ).flip.continuous.comp
    (continuous_id.clm_comp continuous_const)).clm_comp continuous_const)

/-- **The `ε`-level costate system of a tube limit.**  The cost covector `f⁰ₓ`, the covector action
of `fₓ`, `∇G`, `d(∇G)/dt`, the velocity-defect covector `2⟨φ_ε' − φ₀',·⟩` and the initial penalty
covector are read off the limit path `γ`; the endpoint multiplier is
`β = (2K⟨T(γ 0,γ T),·⟩, 2K⟨γ 0 − x₀,·⟩)` and the multiplier operators are
`Dl(b₁,b₂) = b₁∘∂₁T + b₂`, `Dr(b₁,b₂) = b₁∘∂₂T`, `DT = (∂₁T, ∂₂T)` the derivative of the endpoint
constraint at the limit endpoint data.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.25), (11.3.33),
(11.3.34). -/
noncomputable def tubeCostateSystem (P : Problem E V W) (K : ℝ) (γ₀ γ : VelocityTrajectory P)
    (cx : ℝ → E → E →L[ℝ] ℝ) (Fx : ℝ → E → E →L[ℝ] E) (Gx : ℝ → E → E →L[ℝ] ℝ)
    (Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)) (DT : E × E →L[ℝ] W)
    (Φ : ℝ → E →L[ℝ] ℝ) (lam : ℝ → ℝ) :
    EpsilonCostateSystem (E →L[ℝ] ℝ) ((W →L[ℝ] ℝ) × (E →L[ℝ] ℝ)) where
  Φ := Φ
  lam := lam
  β := ((2 * K) • innerSL ℝ (P.endpointConstraint (γ.value 0) (γ.value P.horizon)),
    (2 * K) • innerSL ℝ (γ.value 0 - P.initial))
  cx := fun r => cx r (γ.value r)
  A := fun r => (ContinuousLinearMap.compL ℝ E E ℝ).flip (Fx r (γ.value r))
  g := fun r => Gx r (γ.value r)
  gd := fun r => Gxd r (γ.value r) (1, γ.velocity r)
  defect := fun r => (2 : ℝ) • innerSL ℝ (γ.velocity r - γ₀.velocity r)
  ι := (2 : ℝ) • innerSL ℝ (γ.value 0 - γ₀.initial)
  Dl := tubeDl DT
  Dr := tubeDr DT

/-! ## Integrability along the limit path -/

/-- A bounded, almost everywhere strongly measurable function on `[0,T]` is interval integrable. -/
theorem intervalIntegrable_of_bounded_aestronglyMeasurable {Z : Type*} [NormedAddCommGroup Z]
    {T : ℝ} (hT : 0 ≤ T) {f : ℝ → Z}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioc (0 : ℝ) T))) {C : ℝ}
    (hC : ∀ t ∈ Icc (0 : ℝ) T, ‖f t‖ ≤ C) : IntervalIntegrable f volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  refine (integrable_const C).mono' hf ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact hC t ⟨ht.1.le, ht.2⟩

/-- The nonlinear Nemytskii composition `t ↦ f(t, γ(t))` of a jointly measurable function that is
bounded on bounded sets of states is interval integrable along a carrier path. -/
theorem intervalIntegrable_comp_value {Z : Type*} [NormedAddCommGroup Z] [MeasurableSpace Z]
    [BorelSpace Z] [SecondCountableTopology Z] (γ : VelocityTrajectory P) {f : ℝ → E → Z}
    (hm : Measurable fun p : ℝ × E => f p.1 p.2)
    (hb : ∀ R : ℝ, ∃ C : ℝ, ∀ t y, ‖y‖ ≤ R → ‖f t y‖ ≤ C) :
    IntervalIntegrable (fun r => f r (γ.value r)) volume 0 P.horizon := by
  obtain ⟨R, hR⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := P.horizon)).exists_bound_of_continuousOn
    γ.continuousOn_value
  obtain ⟨C, hC⟩ := hb R
  have hae : AEMeasurable (fun r => γ.value r) (volume.restrict (Ioc (0 : ℝ) P.horizon)) :=
    (γ.continuousOn_value.mono Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc
  exact intervalIntegrable_of_bounded_aestronglyMeasurable P.horizon_pos.le
    ((hm.comp_aemeasurable (aemeasurable_id.prodMk hae)).aestronglyMeasurable) fun t ht =>
      hC t _ (hR t ht)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The derivative of the initial penalty `‖y − φ₀(0)‖² + K‖y − x₀‖²`. -/
theorem fderiv_tubeInitialPenalty (K : ℝ) (γ₀ : VelocityTrajectory P) (y : E) :
    fderiv ℝ (tubeInitialPenalty P K γ₀) y
      = (2 : ℝ) • innerSL ℝ (y - γ₀.initial) + (2 * K) • innerSL ℝ (y - P.initial) := by
  have h1 := hasFDerivAt_initialPenalty γ₀.initial y
  have h2 := (hasFDerivAt_initialPenalty P.initial y).const_mul K
  have h := h1.add h2
  have : HasFDerivAt (tubeInitialPenalty P K γ₀)
      ((2 : ℝ) • innerSL ℝ (y - γ₀.initial) + (2 * K) • innerSL ℝ (y - P.initial)) y := by
    refine h.congr_fderiv ?_
    ext z
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  exact this.fderiv

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The derivative of the endpoint penalty `K‖T(q)‖²`. -/
theorem fderiv_tubeEndpointPenalty (K : ℝ) {DT : E × E →L[ℝ] W} {q : E × E}
    (hDT : HasFDerivAt (fun z : E × E => P.endpointConstraint z.1 z.2) DT q) :
    fderiv ℝ (tubeEndpointPenalty P K) q
      = (2 * K) • (innerSL ℝ (P.endpointConstraint q.1 q.2)).comp DT :=
  (hasFDerivAt_endpointPenalty hDT).fderiv

/-- **The tube limit is an `ε`-level costate system** (Berkovitz & Medhin (11.3.25),
(11.3.33)–(11.3.34), (11.6.11)).  The costate `Φ` of the pointwise-defect limit
(`PenalisedMultiplierLimit`) satisfies the *linear* integral equation
`Φ(t) = Φ(0) + ∫₀ᵗ (f⁰ₓ − (Φ − λ∇G − 2⟨φ_ε' − φ₀',·⟩)·fₓ + λ d(∇G)/dt)` — the penalty momentum
`2K⟨φ_ε' − f,·⟩ = ψ − 2⟨φ_ε' − φ₀',·⟩` is eliminated by the momentum identity
`ψ = Φ − λ∇G` — with `Φ(0) = ι + β·∂₁T + λ(0)∇G(0)` and `Φ(T) = −β·∂₂T`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.25), (11.3.33),
(11.3.34), (11.6.11), (11.6.8). -/
theorem exists_epsilonCostateSystem_of_penalisedMultiplierLimit
    {c : ℝ → E → ℝ} {F : ℝ → E → E} {cx : ℝ → E → E →L[ℝ] ℝ} {Fx : ℝ → E → E →L[ℝ] E}
    {K : ℝ} {γ₀ : VelocityTrajectory P}
    (hreg : PointwiseDefectRegularity P.horizon c cx F Fx γ₀.velocity K)
    {G : ℝ → E → ℝ} {Gx : ℝ → E → E →L[ℝ] ℝ}
    {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)} (hGx : StateGradientRegularity Gx Gxd)
    {ω ω' : ℝ → ℝ}
    (hT : ContDiff ℝ 1 (fun q : E × E => P.endpointConstraint q.1 q.2))
    (seq : PenalisedMinimiserSequence P (pointwiseDefectLagrangian c F γ₀.velocity K) G ω
      (tubeInitialPenalty P K γ₀) (tubeEndpointPenalty P K))
    {γ : VelocityTrajectory P} {M : ℝ}
    (hlim : PenalisedMultiplierLimit (pointwiseDefectStateCovector cx F Fx K)
      (pointwiseDefectVelocityCovector F γ₀.velocity K) ω' G Gx Gxd seq γ M) :
    ∃ (Φ : ℝ → E →L[ℝ] ℝ) (lam : ℝ → ℝ),
      IsEpsilonCostateSystem P.horizon (tubeCostateSystem P K γ₀ γ cx Fx Gx Gxd
        (fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2)
          (γ.value 0, γ.value P.horizon)) Φ lam) ∧
      (∀ t ∈ Icc (0 : ℝ) P.horizon, lam t ≤ M) ∧
      ((∃ δ : ℝ, 0 < δ ∧ δ < P.horizon ∧ ∀ t ∈ Icc (0 : ℝ) P.horizon,
          (t < δ ∨ P.horizon - δ < t) → G t (γ.value t) < 0) →
        ∃ δ : ℝ, 0 < δ ∧ (∀ t ∈ Icc (0 : ℝ) δ, lam t = lam 0) ∧
          ∀ t ∈ Icc (P.horizon - δ) P.horizon, lam t = 0) := by
  classical
  obtain ⟨φ, lam, hφ, htend, hanti, hbd, hlamT, hder, h0, hTT, hmom, hcompl, hend⟩ := hlim
  have hT0 : 0 ≤ P.horizon := P.horizon_pos.le
  have hD := hreg.isCaratheodoryC1
  obtain ⟨hgint, hgprim⟩ := γ.gradientAlongPath_eq_primitive hGx
  set q : E × E := (γ.value 0, γ.value P.horizon) with hq
  set DT := fderiv ℝ (fun q : E × E => P.endpointConstraint q.1 q.2) q with hDTdef
  have hDT : HasFDerivAt (fun z : E × E => P.endpointConstraint z.1 z.2) DT q :=
    ((hT.differentiable one_ne_zero) q).hasFDerivAt
  have hF0 := fderiv_tubeInitialPenalty (P := P) K γ₀ (γ.value 0)
  have hF1 := fderiv_tubeEndpointPenalty (P := P) K hDT
  set a : ℝ → E →L[ℝ] ℝ := fun r =>
    pointwiseDefectStateCovector cx F Fx K r (γ.value r) (γ.velocity r) with ha
  set gd : ℝ → E →L[ℝ] ℝ := fun r => Gxd r (γ.value r) (1, γ.velocity r) with hgd
  set c0 : E →L[ℝ] ℝ := fderiv ℝ (tubeInitialPenalty P K γ₀) (γ.value 0)
    + (fderiv ℝ (tubeEndpointPenalty P K) q).comp (ContinuousLinearMap.inl ℝ E E) with hc0
  set Φ : ℝ → E →L[ℝ] ℝ := limitStateCostate c0 lam (Gx 0 (γ.value 0)) a gd with hΦ
  have hΦdef : ∀ t, Φ t = (c0 + lam 0 • Gx 0 (γ.value 0)) + ∫ r in (0 : ℝ)..t,
      (a r + lam r • gd r) := fun t => rfl
  have hΦ0 : Φ 0 = c0 + lam 0 • Gx 0 (γ.value 0) := by simp [hΦdef]
  -- integrability and measurability facts
  have hlam0 : ∀ t ∈ Icc (0 : ℝ) P.horizon, 0 ≤ lam t := fun t ht => (hbd t ht).1
  have hgdI : IntervalIntegrable gd volume 0 P.horizon := hgint
  have hgc : ContinuousOn (fun t => Gx t (γ.value t)) (Icc (0 : ℝ) P.horizon) := by
    have hprim : ContinuousOn (fun t => ∫ r in (0 : ℝ)..t, Gxd r (γ.value r) (1, γ.velocity r))
        (Icc (0 : ℝ) P.horizon) := by
      have := intervalIntegral.continuousOn_primitive_interval' (a := (0 : ℝ)) hgint
        (by simp [uIcc, hT0] : (0 : ℝ) ∈ [[0, P.horizon]])
      rwa [uIcc_of_le hT0] at this
    exact (continuousOn_const.add hprim).congr hgprim
  have hgI : IntervalIntegrable (fun t => Gx t (γ.value t)) volume 0 P.horizon :=
    hgc.intervalIntegrable_of_Icc hT0
  have hlamgd : IntervalIntegrable (fun r => lam r • gd r) volume 0 P.horizon :=
    intervalIntegrable_lam_smul hT0 hanti hlam0 hlamT hgdI
  have hlamg : IntervalIntegrable (fun r => lam r • Gx r (γ.value r)) volume 0 P.horizon :=
    intervalIntegrable_lam_smul hT0 hanti hlam0 hlamT hgI
  have hΦc : ContinuousOn Φ (Icc (0 : ℝ) P.horizon) := by
    have hint : IntervalIntegrable (fun r => a r + lam r • gd r) volume 0 P.horizon := by
      have haI : IntervalIntegrable a volume 0 P.horizon :=
        intervalIntegrable_of_memLp hT0 (memLp_stateGradient hD hT0 γ.memLp_velocity γ.initial)
      exact haI.add hlamgd
    have := intervalIntegral.continuousOn_primitive_interval' (a := (0 : ℝ)) hint
      (by simp [uIcc, hT0] : (0 : ℝ) ∈ [[0, P.horizon]])
    rw [uIcc_of_le hT0] at this
    exact continuousOn_const.add this
  have hΦI : IntervalIntegrable Φ volume 0 P.horizon := hΦc.intervalIntegrable_of_Icc hT0
  have hFxI : AEStronglyMeasurable (fun r => Fx r (γ.value r))
      (volume.restrict (Ioc (0 : ℝ) P.horizon)) := by
    have hae : AEMeasurable (fun r => γ.value r) (volume.restrict (Ioc (0 : ℝ) P.horizon)) :=
      (γ.continuousOn_value.mono Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc
    exact (hreg.measurable_Fx.comp_aemeasurable (aemeasurable_id.prodMk hae)).aestronglyMeasurable
  obtain ⟨R, hR⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := P.horizon)).exists_bound_of_continuousOn
    γ.continuousOn_value
  obtain ⟨CF, hCF0, hCF⟩ := hreg.bounded R
  have hFxb : ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖Fx t (γ.value t)‖ ≤ CF := fun t ht =>
    (hCF t _ (hR t ht)).2.2
  -- the pointwise algebra: momentum identity gives the linear form of the integrand
  have hlin : ∀ r, pointwiseDefectVelocityCovector F γ₀.velocity K r (γ.value r) (γ.velocity r)
      = Φ r - lam r • Gx r (γ.value r) →
      a r + lam r • gd r = cx r (γ.value r)
        - (ContinuousLinearMap.compL ℝ E E ℝ).flip (Fx r (γ.value r))
            (Φ r - lam r • Gx r (γ.value r))
        + (ContinuousLinearMap.compL ℝ E E ℝ).flip (Fx r (γ.value r))
            ((2 : ℝ) • innerSL ℝ (γ.velocity r - γ₀.velocity r)) + lam r • gd r := by
    intro r hr
    simp only [ha, pointwiseDefectStateCovector]
    have hk : (2 * K) • innerSL ℝ (γ.velocity r - F r (γ.value r))
        = Φ r - lam r • Gx r (γ.value r) - (2 : ℝ) • innerSL ℝ (γ.velocity r - γ₀.velocity r) := by
      rw [← hr, pointwiseDefectVelocityCovector]
      abel
    have hk' : (2 * K) • (innerSL ℝ (γ.velocity r - F r (γ.value r))).comp (Fx r (γ.value r))
        = (Φ r - lam r • Gx r (γ.value r)).comp (Fx r (γ.value r))
          - ((2 : ℝ) • innerSL ℝ (γ.velocity r - γ₀.velocity r)).comp (Fx r (γ.value r)) := by
      rw [← ContinuousLinearMap.smul_comp, hk, ContinuousLinearMap.sub_comp]
    rw [hk']
    simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply]
    abel
  have hmom' : ∀ᵐ r ∂(volume.restrict (Ioc (0 : ℝ) P.horizon)),
      pointwiseDefectVelocityCovector F γ₀.velocity K r (γ.value r) (γ.velocity r)
        = Φ r - lam r • Gx r (γ.value r) := hmom
  -- the velocity-defect covector
  have hwI : MemLp (fun r => γ.velocity r - γ₀.velocity r) 2 (timeMeasure P.horizon) :=
    γ.memLp_velocity.sub γ₀.memLp_velocity
  have hwI1 : Integrable (fun r => γ.velocity r - γ₀.velocity r) (timeMeasure P.horizon) :=
    hwI.integrable one_le_two
  have hdefm : AEStronglyMeasurable (fun r => (2 : ℝ) • innerSL ℝ (γ.velocity r - γ₀.velocity r))
      (timeMeasure P.horizon) :=
    ((innerSL ℝ : E →L⋆[ℝ] E →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
      hwI.aestronglyMeasurable).const_smul (2 : ℝ)
  have hdefn : ∀ r, ‖(2 : ℝ) • innerSL ℝ (γ.velocity r - γ₀.velocity r)‖
      = 2 * ‖γ.velocity r - γ₀.velocity r‖ := fun r => by
    rw [norm_smul, innerSL_apply_norm, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hdefI : IntervalIntegrable (fun r => (2 : ℝ) • innerSL ℝ (γ.velocity r - γ₀.velocity r))
      volume 0 P.horizon := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT0]
    refine (hwI1.norm.const_mul 2).mono' hdefm (Eventually.of_forall fun r => ?_)
    rw [hdefn]
  have hΨI : IntervalIntegrable (fun r => Φ r - lam r • Gx r (γ.value r)) volume 0 P.horizon :=
    hΦI.sub hlamg
  have hΨm : AEStronglyMeasurable (fun r => Φ r - lam r • Gx r (γ.value r))
      (volume.restrict (Ioc (0 : ℝ) P.horizon)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).1 hΨI).aestronglyMeasurable
  refine ⟨Φ, lam, ?_, fun t ht => (hbd t ht).2, ?_⟩
  · refine
      { integrable_cx := intervalIntegrable_comp_value γ hreg.measurable_cx (fun R => ?_)
        integrable_gd := hgdI
        integrable_defect_vec := hdefI
        integrable_defect := ?_
        measurable_A := ?_
        measurable_g := ?_
        integrable_A := ?_
        integrable_lam_gd := hlamgd
        eq_integral := ?_
        initial := ?_
        terminal := ?_
        antitone := hanti
        nonneg := hlam0
        lam_horizon := hlamT }
    · obtain ⟨C, hC0, hC⟩ := hreg.bounded R
      exact ⟨C, fun t y hy => (hC t y hy).1⟩
    · change IntervalIntegrable (fun r => (ContinuousLinearMap.compL ℝ E E ℝ).flip
        (Fx r (γ.value r)) ((2 : ℝ) • innerSL ℝ (γ.velocity r - γ₀.velocity r)))
        volume 0 P.horizon
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT0]
      have hm : AEStronglyMeasurable (fun r => (ContinuousLinearMap.compL ℝ E E ℝ).flip
          (Fx r (γ.value r)) ((2 : ℝ) • innerSL ℝ (γ.velocity r - γ₀.velocity r)))
          (timeMeasure P.horizon) :=
        (ContinuousLinearMap.compL ℝ E E ℝ).aestronglyMeasurable_comp₂ hdefm hFxI
      refine (hwI1.norm.const_mul (2 * CF)).mono' hm ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      have hr' : r ∈ Icc (0 : ℝ) P.horizon := ⟨hr.1.le, hr.2⟩
      calc _ ≤ ‖(2 : ℝ) • innerSL ℝ (γ.velocity r - γ₀.velocity r)‖ * ‖Fx r (γ.value r)‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (2 * ‖γ.velocity r - γ₀.velocity r‖) * CF := by
            rw [hdefn]
            exact mul_le_mul_of_nonneg_left (hFxb r hr') (by positivity)
        _ = 2 * CF * ‖γ.velocity r - γ₀.velocity r‖ := by ring
    · change AEStronglyMeasurable (fun r => (ContinuousLinearMap.compL ℝ E E ℝ).flip
        (Fx r (γ.value r))) (volume.restrict (Ioc (0 : ℝ) P.horizon))
      exact (ContinuousLinearMap.compL ℝ E E ℝ).flip.continuous.comp_aestronglyMeasurable hFxI
    · change AEStronglyMeasurable (fun r => Gx r (γ.value r))
        (volume.restrict (Ioc (0 : ℝ) P.horizon))
      exact (hgc.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    · change IntervalIntegrable (fun r => (ContinuousLinearMap.compL ℝ E E ℝ).flip
        (Fx r (γ.value r)) (Φ r - lam r • Gx r (γ.value r))) volume 0 P.horizon
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT0]
      have hm : AEStronglyMeasurable (fun r => (ContinuousLinearMap.compL ℝ E E ℝ).flip
          (Fx r (γ.value r)) (Φ r - lam r • Gx r (γ.value r))) (timeMeasure P.horizon) :=
        (ContinuousLinearMap.compL ℝ E E ℝ).aestronglyMeasurable_comp₂ hΨm hFxI
      have hΨ1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT0).1 hΨI
      refine (hΨ1.norm.const_mul CF).mono' hm ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      have hr' : r ∈ Icc (0 : ℝ) P.horizon := ⟨hr.1.le, hr.2⟩
      calc _ ≤ ‖Φ r - lam r • Gx r (γ.value r)‖ * ‖Fx r (γ.value r)‖ :=
            ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖Φ r - lam r • Gx r (γ.value r)‖ * CF :=
            mul_le_mul_of_nonneg_left (hFxb r hr') (norm_nonneg _)
        _ = CF * ‖Φ r - lam r • Gx r (γ.value r)‖ := by ring
    · intro t ht
      have hI : ∫ r in (0 : ℝ)..t, (a r + lam r • gd r) = ∫ r in (0 : ℝ)..t,
          (cx r (γ.value r) - (ContinuousLinearMap.compL ℝ E E ℝ).flip (Fx r (γ.value r))
              (Φ r - lam r • Gx r (γ.value r))
            + (ContinuousLinearMap.compL ℝ E E ℝ).flip (Fx r (γ.value r))
              ((2 : ℝ) • innerSL ℝ (γ.velocity r - γ₀.velocity r)) + lam r • gd r) := by
        refine intervalIntegral.integral_congr_ae ?_
        have h1 := (ae_restrict_iff' measurableSet_Ioc).1 hmom'
        filter_upwards [h1] with r hr hrI
        rw [uIoc_of_le ht.1] at hrI
        exact hlin r (hr ⟨hrI.1, hrI.2.trans ht.2⟩)
      change Φ t = Φ 0 + ∫ r in (0 : ℝ)..t,
          (cx r (γ.value r) - (ContinuousLinearMap.compL ℝ E E ℝ).flip (Fx r (γ.value r))
              (Φ r - lam r • Gx r (γ.value r))
            + (ContinuousLinearMap.compL ℝ E E ℝ).flip (Fx r (γ.value r))
              ((2 : ℝ) • innerSL ℝ (γ.velocity r - γ₀.velocity r)) + lam r • gd r)
      rw [← hI, hΦdef t, hΦ0]
    · change Φ 0 = (2 : ℝ) • innerSL ℝ (γ.value 0 - γ₀.initial)
        + (tubeDl DT)
          ((2 * K) • innerSL ℝ (P.endpointConstraint (γ.value 0) (γ.value P.horizon)),
            (2 * K) • innerSL ℝ (γ.value 0 - P.initial))
        + lam 0 • Gx 0 (γ.value 0)
      rw [hΦ0, hc0, hF0, hF1]
      ext z
      simp only [tubeDl, add_apply, smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.coe_snd',
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply,
        smul_eq_mul]
      ring
    · change Φ P.horizon = -((tubeDr DT)
          ((2 * K) • innerSL ℝ (P.endpointConstraint (γ.value 0) (γ.value P.horizon)),
            (2 * K) • innerSL ℝ (γ.value 0 - P.initial)))
      rw [hTT, hF1]
      ext z
      simp only [tubeDr, neg_apply, smul_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
        ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, smul_eq_mul]
      rfl
  · intro hslack
    obtain ⟨δ, hδ, hconst0, hconstT⟩ := hend hslack
    exact ⟨δ / 2, by linarith, hconst0, hconstT⟩

end Problem

end OptimalControl.BoundedState
