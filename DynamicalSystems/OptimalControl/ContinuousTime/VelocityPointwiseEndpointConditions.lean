/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.VelocityEndpointTransversality
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Endpoint conditions (11.6.15)-(11.6.16) for the pointwise-defect penalty

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), §11.6, minimise

`F_K(φ,ν) = ∫₀ᵀ f⁰(φ,ν_t,t) dt + ‖φ' - φ₀'‖² + |φ(0) - φ₀(0)|² + ε‖ν - ν₀‖
           + K|T(φ(0),φ(T))|² + K ‖φ'(t) - f(φ(t),ν_t,t)‖²`.

For a fixed relaxed control the integrand is the *pointwise-defect Lagrangian*
`L(t,x,v) = c(t,x) + ‖v - r(t)‖² + K‖v - F(t,x)‖²`, `c = ∫ f⁰ dν_t`, `F = ∫ f dν_t`,
`r = φ₀'`.  This file

* shows `L` satisfies the Carathéodory `C¹` hypotheses (`IsCaratheodoryC1`) of
  `Mathlib/Analysis/Calculus/ACEulerLagrange.lean` whenever the averaged data are measurable,
  `C¹` in the state with locally uniformly bounded derivatives, and `r ∈ L²`
  (`PointwiseDefectRegularity.isCaratheodoryC1`);
* computes the momentum covector `∂ᵥL = 2⟨v - r, ·⟩ + 2K⟨v - F, ·⟩` (the book's `ψ(ε;·)` of
  (11.6.8)) and state covector `∂ₓL = c_x - 2K⟨v - F, F_x ·⟩`;
* proves the book-shaped endpoint conditions
  `VelocityTrajectory.pointwiseDefect_endpointConditions`:
  `p 0 = 2⟨γ 0 - φ₀(0), ·⟩ + 2K⟨T, ∂₁T ·⟩` and `p T = -2K⟨T, ∂₂T ·⟩`, with the factor `2` on the
  initial penalty and the factor `T(γ 0, γ T)` in the endpoint gradients that the printed
  (11.6.15)-(11.6.16) omit (see `R1_ENDCOND_REPORT.md` §6.3).
-/

@[expose] public section

open Set MeasureTheory Filter ACEulerLagrange
open scoped Topology Interval

namespace OptimalControl.BoundedState

section PointwiseDefect

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The pointwise-defect Lagrangian `L(t,x,v) = c(t,x) + ‖v - φ₀'(t)‖² + K ‖v - f(t,x)‖²` of
the §11.6 penalty `F_K`, with the control averaged out: `c(t,x) = ∫ f⁰(t,x,u) dν_t` and
`f(t,x) = ∫ f(t,x,u) dν_t`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.6) and §11.6. -/
noncomputable def pointwiseDefectLagrangian (c : ℝ → E → ℝ) (F : ℝ → E → E) (r : ℝ → E) (K : ℝ)
    (t : ℝ) (x v : E) : ℝ :=
  c t x + ‖v - r t‖ ^ 2 + K * ‖v - F t x‖ ^ 2

/-- The velocity covector `∂ᵥL = 2⟨v - φ₀', ·⟩ + 2K⟨v - f, ·⟩` of the pointwise-defect Lagrangian:
the book's `ψ(ε;·)` of (11.6.8).

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.6.8). -/
noncomputable def pointwiseDefectVelocityCovector (F : ℝ → E → E) (r : ℝ → E) (K : ℝ)
    (t : ℝ) (x v : E) : E →L[ℝ] ℝ :=
  (2 : ℝ) • innerSL ℝ (v - r t) + (2 * K) • innerSL ℝ (v - F t x)

/-- The state covector `∂ₓL = c_x - 2K⟨v - f, f_x ·⟩` of the pointwise-defect Lagrangian.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.6.9). -/
noncomputable def pointwiseDefectStateCovector (cx : ℝ → E → E →L[ℝ] ℝ) (F : ℝ → E → E)
    (Fx : ℝ → E → E →L[ℝ] E) (K : ℝ) (t : ℝ) (x v : E) : E →L[ℝ] ℝ :=
  cx t x - (2 * K) • (innerSL ℝ (v - F t x)).comp (Fx t x)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The pointwise-defect Lagrangian is jointly Fréchet differentiable in `(x,v)` with partial
covectors `pointwiseDefectStateCovector`, `pointwiseDefectVelocityCovector`. -/
theorem hasFDerivAt_pointwiseDefectLagrangian {c : ℝ → E → ℝ} {cx : ℝ → E → E →L[ℝ] ℝ}
    {F : ℝ → E → E} {Fx : ℝ → E → E →L[ℝ] E} (r : ℝ → E) (K : ℝ)
    (hc : ∀ t y, HasFDerivAt (c t) (cx t y) y) (hF : ∀ t y, HasFDerivAt (F t) (Fx t y) y)
    (t : ℝ) (y w : E) :
    HasFDerivAt (fun q : E × E => pointwiseDefectLagrangian c F r K t q.1 q.2)
      ((pointwiseDefectStateCovector cx F Fx K t y w).comp (ContinuousLinearMap.fst ℝ E E) +
        (pointwiseDefectVelocityCovector F r K t y w).comp (ContinuousLinearMap.snd ℝ E E))
      (y, w) := by
  have h1 : HasFDerivAt (fun q : E × E => c t q.1) ((cx t y).comp (ContinuousLinearMap.fst ℝ E E))
      (y, w) := (hc t y).comp (y, w) (hasFDerivAt_fst)
  have h2 : HasFDerivAt (fun q : E × E => q.2 - r t) (ContinuousLinearMap.snd ℝ E E) (y, w) :=
    hasFDerivAt_snd.sub_const (r t)
  have h2' := h2.norm_sq
  have h3 : HasFDerivAt (fun q : E × E => q.2 - F t q.1)
      (ContinuousLinearMap.snd ℝ E E - (Fx t y).comp (ContinuousLinearMap.fst ℝ E E)) (y, w) :=
    hasFDerivAt_snd.sub ((hF t y).comp (y, w) hasFDerivAt_fst)
  have h3' := h3.norm_sq.const_mul K
  have hsum := (h1.add h2').add h3'
  have hfun : (fun q : E × E => pointwiseDefectLagrangian c F r K t q.1 q.2)
      = ((fun q : E × E => c t q.1) + fun q : E × E => ‖q.2 - r t‖ ^ 2)
        + fun q : E × E => K * ‖q.2 - F t q.1‖ ^ 2 := rfl
  rw [hfun]
  refine hsum.congr_fderiv ?_
  ext q <;> simp [pointwiseDefectStateCovector, pointwiseDefectVelocityCovector] <;> ring


/-- The pointwise-defect Lagrangian is Carathéodory `C¹` with an `L²` gradient envelope whenever
the averaged data are measurable, `C¹` in the state, locally uniformly bounded, and `φ₀' ∈ L²`. -/
theorem isCaratheodoryC1_pointwiseDefectLagrangian {T : ℝ} {c : ℝ → E → ℝ}
    {cx : ℝ → E → E →L[ℝ] ℝ} {F : ℝ → E → E} {Fx : ℝ → E → E →L[ℝ] E} {r : ℝ → E} {K : ℝ}
    (hc : ∀ t y, HasFDerivAt (c t) (cx t y) y) (hF : ∀ t y, HasFDerivAt (F t) (Fx t y) y)
    (hcm : Measurable (fun p : ℝ × E => c p.1 p.2))
    (hcxm : Measurable (fun p : ℝ × E => cx p.1 p.2))
    (hFm : Measurable (fun p : ℝ × E => F p.1 p.2))
    (hFxm : Measurable (fun p : ℝ × E => Fx p.1 p.2))
    (hrm : Measurable r) (hr : MemLp r 2 (timeMeasure T)) (hK : 0 ≤ K)
    (hbd : ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t y, ‖y‖ ≤ R →
      ‖cx t y‖ ≤ C ∧ ‖F t y‖ ≤ C ∧ ‖Fx t y‖ ≤ C) :
    IsCaratheodoryC1 T (pointwiseDefectLagrangian c F r K)
      (pointwiseDefectStateCovector cx F Fx K) (pointwiseDefectVelocityCovector F r K) := by
  have hπ : Measurable (fun p : ℝ × E × E => ((p.1, p.2.1) : ℝ × E)) := by fun_prop
  have hc' : Measurable (fun p : ℝ × E × E => c p.1 p.2.1) := hcm.comp hπ
  have hcx' : Measurable (fun p : ℝ × E × E => cx p.1 p.2.1) := hcxm.comp hπ
  have hF' : Measurable (fun p : ℝ × E × E => F p.1 p.2.1) := hFm.comp hπ
  have hFx' : Measurable (fun p : ℝ × E × E => Fx p.1 p.2.1) := hFxm.comp hπ
  have hr' : Measurable (fun p : ℝ × E × E => r p.1) := hrm.comp measurable_fst
  have hw : Measurable (fun p : ℝ × E × E => p.2.2) := by fun_prop
  refine ⟨hasFDerivAt_pointwiseDefectLagrangian r K hc hF, ?_, ?_, ?_, ?_⟩
  · unfold pointwiseDefectLagrangian
    fun_prop
  · unfold pointwiseDefectStateCovector
    fun_prop
  · unfold pointwiseDefectVelocityCovector
    fun_prop
  · intro R
    obtain ⟨C, hC0, hCb⟩ := hbd R
    have ha : MemLp (fun t => (C + 2 * K * C * C + 2 * K * C) + 2 * ‖r t‖) 2 (timeMeasure T) := by
      have h1 : MemLp (fun _ : ℝ => C + 2 * K * C * C + 2 * K * C) 2 (timeMeasure T) :=
        memLp_const _
      have h2 : MemLp (fun t => 2 * ‖r t‖) 2 (timeMeasure T) := hr.norm.const_mul 2
      exact h1.add h2
    have hCw : 0 ≤ 2 * K * C + 2 + 2 * K := by positivity
    refine ⟨_, 2 * K * C + 2 + 2 * K, ha, hCw, fun t y w hy => ?_⟩
    obtain ⟨hcx, hFb, hFx⟩ := hCb t y hy
    have hKC : 0 ≤ K * C := mul_nonneg hK hC0
    have hwF : ‖w - F t y‖ ≤ ‖w‖ + C := (norm_sub_le _ _).trans (by linarith)
    have hwr : ‖w - r t‖ ≤ ‖w‖ + ‖r t‖ := norm_sub_le _ _
    constructor
    · unfold pointwiseDefectStateCovector
      calc ‖cx t y - (2 * K) • (innerSL ℝ (w - F t y)).comp (Fx t y)‖
          ≤ ‖cx t y‖ + ‖(2 * K) • (innerSL ℝ (w - F t y)).comp (Fx t y)‖ := norm_sub_le _ _
        _ ≤ C + (2 * K) * (‖w - F t y‖ * C) := by
            gcongr
            · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 2 * K)]
              gcongr
              refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
              gcongr
              exact (innerSL_apply_norm ℝ _).le
        _ ≤ _ := by nlinarith [norm_nonneg w, norm_nonneg (r t)]
    · unfold pointwiseDefectVelocityCovector
      calc ‖(2 : ℝ) • innerSL ℝ (w - r t) + (2 * K) • innerSL ℝ (w - F t y)‖
          ≤ ‖(2 : ℝ) • innerSL ℝ (w - r t)‖ + ‖(2 * K) • innerSL ℝ (w - F t y)‖ :=
            norm_add_le _ _
        _ ≤ 2 * ‖w - r t‖ + (2 * K) * ‖w - F t y‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (by positivity : 0 ≤ 2 * K), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
              (innerSL_apply_norm ℝ _), (innerSL_apply_norm ℝ _)]
        _ ≤ _ := by nlinarith [norm_nonneg w, norm_nonneg (r t)]


/-- Regularity of the averaged data `c, F` and the reference velocity `r = φ₀'` of the
pointwise-defect penalty: joint measurability, state differentiability, local uniform bounds on
`c_x, f, f_x` (Berkovitz & Medhin, Assumption 11.6.1) and `φ₀' ∈ L²`. -/
structure PointwiseDefectRegularity (T : ℝ) (c : ℝ → E → ℝ) (cx : ℝ → E → E →L[ℝ] ℝ)
    (F : ℝ → E → E) (Fx : ℝ → E → E →L[ℝ] E) (r : ℝ → E) (K : ℝ) : Prop where
  hasFDerivAt_c : ∀ t y, HasFDerivAt (c t) (cx t y) y
  hasFDerivAt_F : ∀ t y, HasFDerivAt (F t) (Fx t y) y
  measurable_c : Measurable (fun p : ℝ × E => c p.1 p.2)
  measurable_cx : Measurable (fun p : ℝ × E => cx p.1 p.2)
  measurable_F : Measurable (fun p : ℝ × E => F p.1 p.2)
  measurable_Fx : Measurable (fun p : ℝ × E => Fx p.1 p.2)
  measurable_r : Measurable r
  memLp_r : MemLp r 2 (timeMeasure T)
  nonneg_K : 0 ≤ K
  bounded : ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t y, ‖y‖ ≤ R →
    ‖cx t y‖ ≤ C ∧ ‖F t y‖ ≤ C ∧ ‖Fx t y‖ ≤ C

/-- Pointwise-defect regularity gives the Carathéodory `C¹` hypotheses of the weak Euler-Lagrange
theorem. -/
theorem PointwiseDefectRegularity.isCaratheodoryC1 {T : ℝ} {c : ℝ → E → ℝ}
    {cx : ℝ → E → E →L[ℝ] ℝ} {F : ℝ → E → E} {Fx : ℝ → E → E →L[ℝ] E} {r : ℝ → E} {K : ℝ}
    (h : PointwiseDefectRegularity T c cx F Fx r K) :
    IsCaratheodoryC1 T (pointwiseDefectLagrangian c F r K)
      (pointwiseDefectStateCovector cx F Fx K) (pointwiseDefectVelocityCovector F r K) :=
  isCaratheodoryC1_pointwiseDefectLagrangian h.hasFDerivAt_c h.hasFDerivAt_F h.measurable_c
    h.measurable_cx h.measurable_F h.measurable_Fx h.measurable_r h.memLp_r h.nonneg_K h.bounded

end PointwiseDefect

section Book

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]
  {P : Problem E V W}

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- The quadratic initial penalty `x ↦ ‖x - a‖²` has gradient `2 ⟨x - a, ·⟩`. -/
theorem hasFDerivAt_initialPenalty (a x : E) :
    HasFDerivAt (fun y : E => ‖y - a‖ ^ 2) ((2 : ℝ) • innerSL ℝ (x - a)) x := by
  have h : HasFDerivAt (fun y : E => ‖y - a‖ ^ 2)
      ((2 : ℕ) • (innerSL ℝ (x - a)).comp (ContinuousLinearMap.id ℝ E)) x :=
    ((hasFDerivAt_id x).sub_const a).norm_sq
  refine h.congr_fderiv (ContinuousLinearMap.ext fun z => ?_)
  simp [two_smul]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- The quadratic initial penalty `x ↦ ‖x - a‖²` has gradient `2 ⟨x - a, ·⟩`. -/
theorem fderiv_initialPenalty (a x : E) :
    fderiv ℝ (fun y : E => ‖y - a‖ ^ 2) x = (2 : ℝ) • innerSL ℝ (x - a) :=
  (hasFDerivAt_initialPenalty a x).fderiv

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- The quadratic endpoint penalty `q ↦ K ‖T(q)‖²` has gradient `2K ⟨T(q), ∂T ·⟩`. -/
theorem hasFDerivAt_endpointPenalty {K : ℝ} {Tend : E × E → W} {D : E × E →L[ℝ] W} {q : E × E}
    (h : HasFDerivAt Tend D q) :
    HasFDerivAt (fun z : E × E => K * ‖Tend z‖ ^ 2) ((2 * K) • (innerSL ℝ (Tend q)).comp D) q := by
  have := h.norm_sq.const_mul K
  refine this.congr_fderiv (ContinuousLinearMap.ext fun z => ?_)
  simp [two_smul]
  ring


/-- **Endpoint conditions (11.6.15)-(11.6.16) for the pointwise-defect penalty on the velocity
carrier, with an initial anchor.**  Let `J` be the penalty
`∫₀ᵀ [c(t,γ) + ‖γ' - φ₀'‖² + K ‖γ' - f(γ,ν_t,t)‖²] dt + ‖γ(0) - a‖² + κ ‖γ(0) - b‖²
  + K ‖T(γ 0, γ T)‖²`
(`F_K` of §11.6 with the control averaged out: `c = ∫ f⁰ dν_t`, `F = ∫ f dν_t`, `r = φ₀'`,
`a = φ₀(0)`; `κ = 0` is the book's `F_K`, `κ = K`, `b = P.initial` is the library's anchored
penalty), and let `γ` minimise `J` over a set `S` containing all scalar-profile perturbations of
`γ` for small parameter.  Then the momentum covector
`ψ(t) = 2⟨γ' - φ₀', ·⟩ + 2K⟨γ' - f, ·⟩` of (11.6.8) has an absolutely continuous representative
`p` with `p' = c_x - 2K⟨γ' - f, f_x ·⟩` a.e. ((11.6.9)-(11.6.10)) and

* `p 0 = 2⟨γ 0 - a, ·⟩ + 2κ⟨γ 0 - b, ·⟩ + 2K⟨T(γ 0, γ T), ∂₁T ·⟩`  (11.6.15),
* `p T = -2K⟨T(γ 0, γ T), ∂₂T ·⟩`  (11.6.16).

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.6), (11.6.8)-(11.6.16). -/
theorem VelocityTrajectory.pointwiseDefect_endpointConditions_anchored
    (γ : VelocityTrajectory P)
    (J : VelocityTrajectory P → ℝ) (S : Set (VelocityTrajectory P))
    {c : ℝ → E → ℝ} {cx : ℝ → E → E →L[ℝ] ℝ} {F : ℝ → E → E} {Fx : ℝ → E → E →L[ℝ] E}
    {r : ℝ → E} {K : ℝ} (hreg : PointwiseDefectRegularity P.horizon c cx F Fx r K)
    (a b : E) (κ : ℝ) (Tend : E → E → W) (D₁ : E →L[ℝ] W) (D₂ : E →L[ℝ] W)
    (hT : HasFDerivAt (fun q : E × E => Tend q.1 q.2)
      (D₁.comp (ContinuousLinearMap.fst ℝ E E) + D₂.comp (ContinuousLinearMap.snd ℝ E E))
      (γ.value 0, γ.value P.horizon))
    (hJ : ∀ γ' : VelocityTrajectory P,
      J γ' = ACEulerLagrange.actionFunctional (pointwiseDefectLagrangian c F r K)
        (fun y : E => ‖y - a‖ ^ 2 + κ * ‖y - b‖ ^ 2)
        (fun q : E × E => K * ‖Tend q.1 q.2‖ ^ 2)
        P.horizon γ'.initial γ'.velocity)
    (hmin : IsMinOn J S γ)
    (hinterior : ∀ (e : E) (α : ℝ) (s : ℝ → ℝ) (hs : MemLp s 2 (timeMeasure P.horizon)),
      ∀ᶠ θ in 𝓝 (0 : ℝ), γ.perturbProfile e α s hs θ ∈ S)
    (hint : IntervalIntegrable
      (fun t => pointwiseDefectLagrangian c F r K t (γ.value t) (γ.velocity t))
      volume 0 P.horizon) :
    ∃ p : ℝ → E →L[ℝ] ℝ,
      ContinuousOn p (Icc (0 : ℝ) P.horizon) ∧
      (∀ᵐ t ∂(timeMeasure P.horizon), p t =
        (2 : ℝ) • innerSL ℝ (γ.velocity t - r t)
          + (2 * K) • innerSL ℝ (γ.velocity t - F t (γ.value t))) ∧
      (∀ᵐ t ∂(timeMeasure P.horizon), HasDerivAt p
        (cx t (γ.value t) - (2 * K) • (innerSL ℝ (γ.velocity t - F t (γ.value t))).comp
          (Fx t (γ.value t))) t) ∧
      p 0 = (2 : ℝ) • innerSL ℝ (γ.value 0 - a) + (2 * κ) • innerSL ℝ (γ.value 0 - b)
        + (2 * K) • (innerSL ℝ (Tend (γ.value 0) (γ.value P.horizon))).comp D₁ ∧
      p P.horizon = -((2 * K) • (innerSL ℝ (Tend (γ.value 0) (γ.value P.horizon))).comp D₂) := by
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
  obtain ⟨p, hcont, hmom, hstate, h0, hT'⟩ := γ.endpointTransversality_of_isMinOn J S hD hJ hmin
    hinterior hint hΦ₀.differentiableAt hΦ₁.differentiableAt
  refine ⟨p, hcont, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hmom, γ.ae_deriv_value] with t ht hd
    rw [ht]
    unfold EndpointTransversality.momentumCovector
    rw [hd, hD.fderiv_velocity_eq]
    rfl
  · filter_upwards [hstate, γ.ae_deriv_value] with t ht hd
    unfold EndpointTransversality.stateCovector at ht
    rw [hd, hD.fderiv_state_eq] at ht
    exact ht
  · rw [h0, hΦ₀.fderiv, hΦ₁.fderiv]
    ext z
    simp
  · rw [hT', hΦ₁.fderiv]
    ext z
    simp

/-- **Endpoint conditions (11.6.15)-(11.6.16) for the pointwise-defect penalty on the velocity
carrier.**  Let `J` be the penalty
`∫₀ᵀ [c(t,γ) + ‖γ' - φ₀'‖² + K ‖γ' - f(γ,ν_t,t)‖²] dt + ‖γ(0) - a‖² + K ‖T(γ 0, γ T)‖²`
(`F_K` of §11.6 with the control averaged out: `c = ∫ f⁰ dν_t`, `F = ∫ f dν_t`, `r = φ₀'`,
`a = φ₀(0)`), and let `γ` minimise `J` over a set `S` containing all scalar-profile perturbations
of `γ` for small parameter.  Then the momentum covector
`ψ(t) = 2⟨γ' - φ₀', ·⟩ + 2K⟨γ' - f, ·⟩` of (11.6.8) has an absolutely continuous representative
`p` with `p' = c_x - 2K⟨γ' - f, f_x ·⟩` a.e. ((11.6.9)-(11.6.10)) and

* `p 0 = 2⟨γ 0 - a, ·⟩ + 2K⟨T(γ 0, γ T), ∂₁T ·⟩`  (11.6.15),
* `p T = -2K⟨T(γ 0, γ T), ∂₂T ·⟩`  (11.6.16).

The factor `2` on the initial penalty and the factor `T(γ 0, γ T)` in the endpoint gradients are
those of the book's own `F_K` (the printed (11.6.15)-(11.6.16) omit them).

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.6), (11.6.8)-(11.6.16). -/
theorem VelocityTrajectory.pointwiseDefect_endpointConditions (γ : VelocityTrajectory P)
    (J : VelocityTrajectory P → ℝ) (S : Set (VelocityTrajectory P))
    {c : ℝ → E → ℝ} {cx : ℝ → E → E →L[ℝ] ℝ} {F : ℝ → E → E} {Fx : ℝ → E → E →L[ℝ] E}
    {r : ℝ → E} {K : ℝ} (hreg : PointwiseDefectRegularity P.horizon c cx F Fx r K)
    (a : E) (Tend : E → E → W) (D₁ : E →L[ℝ] W) (D₂ : E →L[ℝ] W)
    (hT : HasFDerivAt (fun q : E × E => Tend q.1 q.2)
      (D₁.comp (ContinuousLinearMap.fst ℝ E E) + D₂.comp (ContinuousLinearMap.snd ℝ E E))
      (γ.value 0, γ.value P.horizon))
    (hJ : ∀ γ' : VelocityTrajectory P,
      J γ' = ACEulerLagrange.actionFunctional (pointwiseDefectLagrangian c F r K)
        (fun y : E => ‖y - a‖ ^ 2) (fun q : E × E => K * ‖Tend q.1 q.2‖ ^ 2)
        P.horizon γ'.initial γ'.velocity)
    (hmin : IsMinOn J S γ)
    (hinterior : ∀ (e : E) (α : ℝ) (s : ℝ → ℝ) (hs : MemLp s 2 (timeMeasure P.horizon)),
      ∀ᶠ θ in 𝓝 (0 : ℝ), γ.perturbProfile e α s hs θ ∈ S)
    (hint : IntervalIntegrable
      (fun t => pointwiseDefectLagrangian c F r K t (γ.value t) (γ.velocity t))
      volume 0 P.horizon) :
    ∃ p : ℝ → E →L[ℝ] ℝ,
      ContinuousOn p (Icc (0 : ℝ) P.horizon) ∧
      (∀ᵐ t ∂(timeMeasure P.horizon), p t =
        (2 : ℝ) • innerSL ℝ (γ.velocity t - r t)
          + (2 * K) • innerSL ℝ (γ.velocity t - F t (γ.value t))) ∧
      (∀ᵐ t ∂(timeMeasure P.horizon), HasDerivAt p
        (cx t (γ.value t) - (2 * K) • (innerSL ℝ (γ.velocity t - F t (γ.value t))).comp
          (Fx t (γ.value t))) t) ∧
      p 0 = (2 : ℝ) • innerSL ℝ (γ.value 0 - a)
        + (2 * K) • (innerSL ℝ (Tend (γ.value 0) (γ.value P.horizon))).comp D₁ ∧
      p P.horizon = -((2 * K) • (innerSL ℝ (Tend (γ.value 0) (γ.value P.horizon))).comp D₂) := by
  have hJ' : ∀ γ' : VelocityTrajectory P,
      J γ' = ACEulerLagrange.actionFunctional (pointwiseDefectLagrangian c F r K)
        (fun y : E => ‖y - a‖ ^ 2 + (0 : ℝ) * ‖y - a‖ ^ 2)
        (fun q : E × E => K * ‖Tend q.1 q.2‖ ^ 2)
        P.horizon γ'.initial γ'.velocity := by
    intro γ'
    rw [hJ γ']
    simp only [zero_mul, add_zero]
  obtain ⟨p, hcont, hmom, hstate, h0, hT'⟩ := γ.pointwiseDefect_endpointConditions_anchored J S
    hreg a a 0 Tend D₁ D₂ hT hJ' hmin hinterior hint
  refine ⟨p, hcont, hmom, hstate, ?_, hT'⟩
  rw [h0]
  simp

end Book

end OptimalControl.BoundedState
