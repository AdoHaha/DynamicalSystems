/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.RelaxedKernelDistance
public import DynamicalSystems.OptimalControl.ContinuousTime.VelocityPointwiseBoundaryPositivity

/-!
# The Hamiltonian inequality passes to the limit `ε → 0`

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.37), §11.4,
Theorem 11.4.4 (v), Theorem 11.6.3 (v).

At level `ε` the Hamiltonian inequality reads, for every relaxed control `σ`,
`∫ H_k dρ_k ≤ ∫ H_k dσ + ε_k` with `H_k(t,u) = c_k f⁰(t,x_k(t),u) − Θ_k(t)·f(t,x_k(t),u)`.
Here `c_k = 1/M_k` and `Θ_k = (Φ_k − λ_k∇G − defect_k)/M_k`.  If `x_k → x_∞` uniformly,
`ρ_k → ρ₀` in the control distance, `c_k → c_∞` and `Θ_k → Ψ` in `L¹(0,T)` with `Ψ` bounded, then
the inequality survives: `∫ H_∞ dρ₀ ≤ ∫ H_∞ dσ` for every relaxed `σ`.

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

/-- The Hamiltonian integral `∫ (c f⁰(t,x(t),u) − Θ(t)·f(t,x(t),u)) dρ(t,u)` of a relaxed
control. -/
noncomputable def hamiltonianIntegral (P : Problem E V W) (ρ : P.Relaxed) (x : P.Trajectory)
    (Θ : P.Time → E →L[ℝ] ℝ) (c : ℝ) : ℝ :=
  ∫ z, (c * P.runningCost z.1 (x z.1) (z.2 : V)
    - Θ z.1 (P.dynamics z.1 (x z.1) (z.2 : V))) ∂ρ.measure

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The time marginal of every relaxed control is the normalized Lebesgue measure. -/
theorem map_fst_measure (P : Problem E V W) (τ : P.Relaxed) :
    τ.measure.map Prod.fst = (horizonProbability P.horizon P.horizon_pos).toMeasure :=
  τ.fst_measure

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
theorem continuous_runningCost_along (P : Problem E V W) (y : P.Trajectory) :
    Continuous (fun z : P.Time × P.Control => P.runningCost z.1 (y z.1) (z.2 : V)) :=
  P.runningCost_continuous.comp
    ((continuous_fst.prodMk (y.continuous.comp continuous_fst)).prodMk
      (continuous_subtype_val.comp continuous_snd))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
theorem continuous_dynamics_along (P : Problem E V W) (y : P.Trajectory) :
    Continuous (fun z : P.Time × P.Control => P.dynamics z.1 (y z.1) (z.2 : V)) :=
  P.dynamics_continuous.comp
    ((continuous_fst.prodMk (y.continuous.comp continuous_fst)).prodMk
      (continuous_subtype_val.comp continuous_snd))

omit [CompleteSpace E] in
/-- The Hamiltonian integrand is a.e.-strongly measurable for every relaxed control, as soon as
the weight is a.e.-strongly measurable for the time marginal. -/
theorem aestronglyMeasurable_hamiltonianIntegrand (P : Problem E V W) (τ : P.Relaxed)
    (y : P.Trajectory) {Φ : P.Time → E →L[ℝ] ℝ}
    (hΦ : AEStronglyMeasurable Φ (horizonProbability P.horizon P.horizon_pos).toMeasure)
    (c : ℝ) :
    AEStronglyMeasurable (fun z : P.Time × P.Control => c * P.runningCost z.1 (y z.1) (z.2 : V)
      - Φ z.1 (P.dynamics z.1 (y z.1) (z.2 : V))) τ.measure := by
  have hΦ' : AEStronglyMeasurable (fun z : P.Time × P.Control => Φ z.1) τ.measure := by
    rw [← map_fst_measure P τ] at hΦ
    exact hΦ.comp_measurable measurable_fst
  have hf : AEStronglyMeasurable (fun z : P.Time × P.Control =>
      P.dynamics z.1 (y z.1) (z.2 : V)) τ.measure :=
    (continuous_dynamics_along P y).aestronglyMeasurable
  have happ : AEStronglyMeasurable (fun z : P.Time × P.Control =>
      Φ z.1 (P.dynamics z.1 (y z.1) (z.2 : V))) τ.measure :=
    (continuous_fst.clm_apply continuous_snd :
      Continuous fun p : (E →L[ℝ] ℝ) × E => p.1 p.2).comp_aestronglyMeasurable (hΦ'.prodMk hf)
  exact ((continuous_runningCost_along P y).aestronglyMeasurable.const_mul c).sub happ

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- Pointwise bound of the Hamiltonian integrand. -/
theorem norm_hamiltonianIntegrand_le {c a C₀ B Cf : ℝ} (L : E →L[ℝ] ℝ) (v : E)
    (ha : |a| ≤ C₀) (hL : ‖L‖ ≤ B) (hv : ‖v‖ ≤ Cf) :
    ‖c * a - L v‖ ≤ |c| * C₀ + B * Cf := by
  calc ‖c * a - L v‖ ≤ ‖c * a‖ + ‖L v‖ := norm_sub_le _ _
    _ ≤ |c| * C₀ + B * Cf := by
      refine add_le_add ?_ ?_
      · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left ha (abs_nonneg c)
      · exact (L.le_opNorm v).trans (mul_le_mul hL hv (norm_nonneg _) ((norm_nonneg _).trans hL))

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- Pointwise bound of the difference of two Hamiltonian integrands. -/
theorem norm_hamiltonianIntegrand_sub_le {c c₀ a a₀ α δ B Cf : ℝ} (Θ Ψ : E →L[ℝ] ℝ) (v v₀ : E)
    (hα : |c * a - c₀ * a₀| ≤ α) (hΨ : ‖Ψ‖ ≤ B) (hv : ‖v‖ ≤ Cf) (hδ : ‖v - v₀‖ ≤ δ) :
    ‖(c * a - Θ v) - (c₀ * a₀ - Ψ v₀)‖ ≤ α + B * δ + Cf * ‖Θ - Ψ‖ := by
  have e : (c * a - Θ v) - (c₀ * a₀ - Ψ v₀) = (c * a - c₀ * a₀) - ((Θ - Ψ) v + Ψ (v - v₀)) := by
    simp only [sub_apply, map_sub]
    ring
  rw [e]
  have h1 : ‖(Θ - Ψ) v‖ ≤ Cf * ‖Θ - Ψ‖ := ((Θ - Ψ).le_opNorm v).trans (by
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hv (norm_nonneg _))
  have h2 : ‖Ψ (v - v₀)‖ ≤ B * δ := (Ψ.le_opNorm _).trans
    (mul_le_mul hΨ hδ (norm_nonneg _) ((norm_nonneg _).trans hΨ))
  have h3 := norm_add_le ((Θ - Ψ) v) (Ψ (v - v₀))
  have h4 := norm_sub_le (c * a - c₀ * a₀) ((Θ - Ψ) v + Ψ (v - v₀))
  rw [Real.norm_eq_abs (c * a - c₀ * a₀)] at h4
  linarith

omit [CompleteSpace E] in
/-- **Stability of the Hamiltonian integral** under perturbation of the path, the weight and the
coefficient, for a fixed relaxed control: only `L¹(ν)` control of the weight is needed, since the
time marginal of every relaxed control is `ν`. -/
theorem abs_hamiltonianIntegral_sub_le (P : Problem E V W) (τ : P.Relaxed)
    (y x₀ : P.Trajectory) {Θ Ψ : P.Time → E →L[ℝ] ℝ} {c c₀ B C₀ Cf α δ : ℝ}
    (hΨb : ∀ t, ‖Ψ t‖ ≤ B)
    (hΨm : AEStronglyMeasurable Ψ (horizonProbability P.horizon P.horizon_pos).toMeasure)
    (hΘm : AEStronglyMeasurable Θ (horizonProbability P.horizon P.horizon_pos).toMeasure)
    (hΘi : Integrable (fun t => ‖Θ t - Ψ t‖)
      (horizonProbability P.horizon P.horizon_pos).toMeasure)
    (hC₀ : ∀ (t : P.Time) (u : P.Control), |P.runningCost t (x₀ t) u| ≤ C₀)
    (hCf : ∀ (t : P.Time) (u : P.Control), ‖P.dynamics t (x₀ t) u‖ ≤ Cf)
    (hCfy : ∀ (t : P.Time) (u : P.Control), ‖P.dynamics t (y t) u‖ ≤ Cf)
    (hα : ∀ (t : P.Time) (u : P.Control),
      |c * P.runningCost t (y t) u - c₀ * P.runningCost t (x₀ t) u| ≤ α)
    (hδ : ∀ (t : P.Time) (u : P.Control),
      ‖P.dynamics t (y t) u - P.dynamics t (x₀ t) u‖ ≤ δ) :
    |hamiltonianIntegral P τ y Θ c - hamiltonianIntegral P τ x₀ Ψ c₀|
      ≤ α + B * δ + Cf * ∫ t, ‖Θ t - Ψ t‖
        ∂(horizonProbability P.horizon P.horizon_pos).toMeasure := by
  have hmap := map_fst_measure P τ
  have hΘi' : Integrable (fun t => ‖Θ t - Ψ t‖) (τ.measure.map Prod.fst) := by
    rw [hmap]; exact hΘi
  have hw : Integrable (fun z : P.Time × P.Control => ‖Θ z.1 - Ψ z.1‖) τ.measure :=
    hΘi'.comp_measurable measurable_fst
  have hgi : Integrable (fun z : P.Time × P.Control =>
      α + B * δ + Cf * ‖Θ z.1 - Ψ z.1‖) τ.measure :=
    (integrable_const _).add (hw.const_mul Cf)
  have hh₀m := aestronglyMeasurable_hamiltonianIntegrand P τ x₀ hΨm c₀
  have hhm := aestronglyMeasurable_hamiltonianIntegrand P τ y hΘm c
  have hh₀i : Integrable (fun z : P.Time × P.Control => c₀ * P.runningCost z.1 (x₀ z.1) (z.2 : V)
      - Ψ z.1 (P.dynamics z.1 (x₀ z.1) (z.2 : V))) τ.measure :=
    Integrable.of_bound hh₀m (|c₀| * C₀ + B * Cf) (Eventually.of_forall fun z =>
      norm_hamiltonianIntegrand_le _ _ (hC₀ z.1 z.2) (hΨb z.1) (hCf z.1 z.2))
  have hbound : ∀ z : P.Time × P.Control,
      ‖(c * P.runningCost z.1 (y z.1) (z.2 : V) - Θ z.1 (P.dynamics z.1 (y z.1) (z.2 : V)))
        - (c₀ * P.runningCost z.1 (x₀ z.1) (z.2 : V)
          - Ψ z.1 (P.dynamics z.1 (x₀ z.1) (z.2 : V)))‖
        ≤ α + B * δ + Cf * ‖Θ z.1 - Ψ z.1‖ := fun z =>
    norm_hamiltonianIntegrand_sub_le _ _ _ _ (hα z.1 z.2) (hΨb z.1) (hCfy z.1 z.2) (hδ z.1 z.2)
  have hdi := hgi.mono' (hhm.sub hh₀m) (Eventually.of_forall hbound)
  have hhi : Integrable (fun z : P.Time × P.Control => c * P.runningCost z.1 (y z.1) (z.2 : V)
      - Θ z.1 (P.dynamics z.1 (y z.1) (z.2 : V))) τ.measure := by
    simpa using hdi.add hh₀i
  have hint : ∫ z, ‖Θ z.1 - Ψ z.1‖ ∂τ.measure
      = ∫ t, ‖Θ t - Ψ t‖ ∂(horizonProbability P.horizon P.horizon_pos).toMeasure := by
    rw [← hmap, integral_map measurable_fst.aemeasurable hΘi'.aestronglyMeasurable]
  have hgint : ∫ z, (α + B * δ + Cf * ‖Θ z.1 - Ψ z.1‖) ∂τ.measure
      = α + B * δ + Cf * ∫ t, ‖Θ t - Ψ t‖
        ∂(horizonProbability P.horizon P.horizon_pos).toMeasure := by
    rw [integral_add (integrable_const _) (hw.const_mul Cf), integral_const, integral_const_mul,
      hint]
    simp
  have e : hamiltonianIntegral P τ y Θ c - hamiltonianIntegral P τ x₀ Ψ c₀
      = ∫ z, ((c * P.runningCost z.1 (y z.1) (z.2 : V)
          - Θ z.1 (P.dynamics z.1 (y z.1) (z.2 : V)))
        - (c₀ * P.runningCost z.1 (x₀ z.1) (z.2 : V)
          - Ψ z.1 (P.dynamics z.1 (x₀ z.1) (z.2 : V)))) ∂τ.measure :=
    (integral_sub hhi hh₀i).symm
  rw [e, ← Real.norm_eq_abs, ← hgint]
  exact norm_integral_le_of_norm_le hgi (Eventually.of_forall hbound)

omit [CompleteSpace E] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- Uniform convergence of the paths gives uniform convergence of the integrands, and uniform
bounds, via uniform continuity of `f⁰, f` on the compact set `Time × closedBall × Ω`. -/
theorem exists_bounds_of_tendsto (P : Problem E V W) {x : ℕ → P.Trajectory}
    {x₀ : P.Trajectory} (hx : Tendsto x atTop (𝓝 x₀)) :
    ∃ C₀ Cf : ℝ, (∀ (t : P.Time) (u : P.Control), |P.runningCost t (x₀ t) u| ≤ C₀) ∧
      (∀ (t : P.Time) (u : P.Control), ‖P.dynamics t (x₀ t) u‖ ≤ Cf) ∧
      ∀ δ > 0, ∀ᶠ k in atTop, ∀ (t : P.Time) (u : P.Control),
        |P.runningCost t (x k t) u - P.runningCost t (x₀ t) u| ≤ δ ∧
        ‖P.dynamics t (x k t) u - P.dynamics t (x₀ t) u‖ ≤ δ ∧
        ‖P.dynamics t (x k t) u‖ ≤ Cf := by
  set R : ℝ := ‖x₀‖ + 1
  set K : Set ((P.Time × E) × V) := (univ ×ˢ Metric.closedBall (0 : E) R) ×ˢ P.controlSet
  have hK : IsCompact K :=
    (isCompact_univ.prod (isCompact_closedBall 0 R)).prod P.controlSet_compact
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn P.runningCost_continuous.continuousOn
  obtain ⟨Cf, hCf⟩ := hK.exists_bound_of_continuousOn P.dynamics_continuous.continuousOn
  have hmem : ∀ y : P.Trajectory, dist y x₀ ≤ 1 → ∀ (t : P.Time) (u : P.Control),
      ((t, y t), (u : V)) ∈ K := by
    intro y hy t u
    refine ⟨⟨mem_univ _, ?_⟩, u.2⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 := norm_sub_norm_le (y t) (x₀ t)
    rw [← dist_eq_norm] at h1
    have h2 := y.dist_coe_le_dist (g := x₀) t
    have h3 := x₀.norm_coe_le_norm t
    linarith
  have hdist : ∀ (t : P.Time) (a b : E) (u : V), dist ((t, a), u) ((t, b), u) = dist a b := by
    intro t a b u
    simp [Prod.dist_eq, dist_nonneg]
  have hx₀ : dist x₀ x₀ ≤ 1 := by simp
  refine ⟨C₀, Cf, fun t u => ?_, fun t u => hCf _ (hmem x₀ hx₀ t u), fun δ hδ => ?_⟩
  · have := hC₀ _ (hmem x₀ hx₀ t u)
    rwa [Real.norm_eq_abs] at this
  obtain ⟨η₁, hη₁, h₁⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous P.runningCost_continuous.continuousOn) δ hδ
  obtain ⟨η₂, hη₂, h₂⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous P.dynamics_continuous.continuousOn) δ hδ
  filter_upwards [Metric.tendsto_nhds.1 hx (min 1 (min η₁ η₂)) (by positivity)] with k hk
  intro t u
  have hk1 : dist (x k) x₀ ≤ 1 := hk.le.trans (min_le_left _ _)
  have hkt : dist (x k t) (x₀ t) < min η₁ η₂ :=
    ((x k).dist_coe_le_dist (g := x₀) t).trans_lt (hk.trans_le (min_le_right _ _))
  refine ⟨?_, ?_, hCf _ (hmem (x k) hk1 t u)⟩
  · have := h₁ _ (hmem (x k) hk1 t u) _ (hmem x₀ hx₀ t u)
      (by rw [hdist]; exact hkt.trans_le (min_le_left _ _))
    rw [Real.dist_eq] at this
    exact this.le
  · have := h₂ _ (hmem (x k) hk1 t u) _ (hmem x₀ hx₀ t u)
      (by rw [hdist]; exact hkt.trans_le (min_le_right _ _))
    rw [dist_eq_norm] at this
    exact this.le

omit [CompleteSpace E] in
/-- A measurable, everywhere bounded version of the limit integrand which agrees with it a.e. for
every relaxed control (the weight `Ψ` is only a.e.-strongly measurable). -/
theorem exists_measurable_bounded_integrand (P : Problem E V W) (x₀ : P.Trajectory)
    {Ψ : P.Time → E →L[ℝ] ℝ} {B : ℝ} (hΨb : ∀ t, ‖Ψ t‖ ≤ B)
    (hΨm : AEStronglyMeasurable Ψ (horizonProbability P.horizon P.horizon_pos).toMeasure)
    (c₀ : ℝ) {C₀ Cf : ℝ}
    (hC₀ : ∀ (t : P.Time) (u : P.Control), |P.runningCost t (x₀ t) u| ≤ C₀)
    (hCf : ∀ (t : P.Time) (u : P.Control), ‖P.dynamics t (x₀ t) u‖ ≤ Cf) :
    ∃ g : P.Time × P.Control → ℝ, Measurable g ∧ (∀ z, |g z| ≤ |c₀| * C₀ + B * Cf) ∧
      ∀ τ : P.Relaxed, g =ᵐ[τ.measure] fun z => c₀ * P.runningCost z.1 (x₀ z.1) (z.2 : V)
        - Ψ z.1 (P.dynamics z.1 (x₀ z.1) (z.2 : V)) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hΨb ⟨0, left_mem_Icc.2 P.horizon_pos.le⟩)
  set S : Set P.Time := {t | ‖hΨm.mk Ψ t‖ ≤ B} with hSdef
  have hS : MeasurableSet S :=
    measurableSet_le hΨm.stronglyMeasurable_mk.norm.measurable measurable_const
  set Ψ' : P.Time → E →L[ℝ] ℝ := S.indicator (hΨm.mk Ψ) with hΨ'def
  have hΨ'sm : StronglyMeasurable Ψ' := hΨm.stronglyMeasurable_mk.indicator hS
  have hΨ'b : ∀ t, ‖Ψ' t‖ ≤ B := fun t => by
    by_cases ht : t ∈ S
    · rw [hΨ'def, indicator_of_mem ht]; exact ht
    · rw [hΨ'def, indicator_of_notMem ht, norm_zero]; exact hB0
  have hΨ'ae : ∀ᵐ t ∂(horizonProbability P.horizon P.horizon_pos).toMeasure, Ψ' t = Ψ t := by
    filter_upwards [hΨm.ae_eq_mk] with t ht
    have htS : t ∈ S := by
      change ‖hΨm.mk Ψ t‖ ≤ B
      rw [← ht]; exact hΨb t
    rw [hΨ'def, indicator_of_mem htS, ht]
  refine ⟨fun z => c₀ * P.runningCost z.1 (x₀ z.1) (z.2 : V)
    - Ψ' z.1 (P.dynamics z.1 (x₀ z.1) (z.2 : V)), ?_, fun z => ?_, fun τ => ?_⟩
  · have happ : StronglyMeasurable (fun z : P.Time × P.Control =>
        Ψ' z.1 (P.dynamics z.1 (x₀ z.1) (z.2 : V))) :=
      (continuous_fst.clm_apply continuous_snd :
        Continuous fun p : (E →L[ℝ] ℝ) × E => p.1 p.2).comp_stronglyMeasurable
        ((hΨ'sm.comp_measurable measurable_fst).prodMk
          (continuous_dynamics_along P x₀).stronglyMeasurable)
    exact (((continuous_runningCost_along P x₀).stronglyMeasurable.const_mul c₀).sub
      happ).measurable
  · rw [← Real.norm_eq_abs]
    exact norm_hamiltonianIntegrand_le _ _ (hC₀ z.1 z.2) (hΨ'b z.1) (hCf z.1 z.2)
  · have hae : ∀ᵐ t ∂(τ.measure.map Prod.fst), Ψ' t = Ψ t := by
      rw [map_fst_measure P τ]; exact hΨ'ae
    filter_upwards [ae_of_ae_map measurable_fst.aemeasurable hae] with z hz
    simp only [hz]

/-- An `ε`–`δ` squeeze: if `|T k - L| ≤ g k + K δ` eventually for every `δ > 0` and `g → 0`,
then `T → L`. -/
theorem tendsto_of_forall_eventually_abs_sub_le {T g : ℕ → ℝ} {L K : ℝ}
    (hg : Tendsto g atTop (𝓝 0))
    (h : ∀ δ > 0, ∀ᶠ k in atTop, |T k - L| ≤ g k + K * δ) : Tendsto T atTop (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hK : 0 < |K| + 1 := by positivity
  have hδ : 0 < ε / (2 * (|K| + 1)) := by positivity
  filter_upwards [h _ hδ, Metric.tendsto_nhds.1 hg (ε / 2) (by positivity)] with k hk hgk
  rw [Real.dist_eq, sub_zero] at hgk
  rw [Real.dist_eq]
  have h1 : K * (ε / (2 * (|K| + 1))) ≤ ε / 2 := by
    calc K * (ε / (2 * (|K| + 1))) ≤ |K| * (ε / (2 * (|K| + 1))) :=
          mul_le_mul_of_nonneg_right (le_abs_self K) hδ.le
      _ ≤ (|K| + 1) * (ε / (2 * (|K| + 1))) :=
          mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = ε / 2 := by field_simp
  have := (abs_lt.1 hgk).2
  linarith

omit [CompleteSpace E] in
/-- **Passage to the limit in the Hamiltonian inequality.** -/
theorem hamiltonianIntegral_le_of_limit (P : Problem E V W)
    {x : ℕ → P.Trajectory} {x₀ : P.Trajectory} (hx : Tendsto x atTop (𝓝 x₀))
    {ρ : ℕ → P.Relaxed} {ρ₀ : P.Relaxed}
    (hρ : Tendsto (fun k => relaxedControlDistance P (ρ k) ρ₀) atTop (𝓝 0))
    {c : ℕ → ℝ} {c₀ : ℝ} (hc : Tendsto c atTop (𝓝 c₀))
    {Θ : ℕ → P.Time → E →L[ℝ] ℝ} {Ψ : P.Time → E →L[ℝ] ℝ} {B : ℝ}
    (hΨb : ∀ t, ‖Ψ t‖ ≤ B)
    (hΨm : AEStronglyMeasurable Ψ (horizonProbability P.horizon P.horizon_pos).toMeasure)
    (hΘm : ∀ k, AEStronglyMeasurable (Θ k) (horizonProbability P.horizon P.horizon_pos).toMeasure)
    (hΘi : ∀ k, Integrable (fun t => ‖Θ k t - Ψ t‖)
      (horizonProbability P.horizon P.horizon_pos).toMeasure)
    (hΘ : Tendsto (fun k => ∫ t, ‖Θ k t - Ψ t‖
      ∂(horizonProbability P.horizon P.horizon_pos).toMeasure) atTop (𝓝 0))
    {eps : ℕ → ℝ} (heps : Tendsto eps atTop (𝓝 0))
    (hH : ∀ (k : ℕ) (σ : P.Relaxed),
      hamiltonianIntegral P (ρ k) (x k) (Θ k) (c k)
        ≤ hamiltonianIntegral P σ (x k) (Θ k) (c k) + eps k)
    (σ : P.Relaxed) :
    hamiltonianIntegral P ρ₀ x₀ Ψ c₀ ≤ hamiltonianIntegral P σ x₀ Ψ c₀ := by
  obtain ⟨C₀, Cf, hC₀, hCf, hunif⟩ := exists_bounds_of_tendsto P hx
  have t₀ : P.Time := ⟨0, left_mem_Icc.2 P.horizon_pos.le⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hΨb t₀)
  have hC₀0 : 0 ≤ C₀ := (abs_nonneg _).trans (hC₀ t₀ (Classical.arbitrary _))
  have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hCf t₀ (Classical.arbitrary _))
  obtain ⟨g, hgm, hgb, hgae⟩ :=
    exists_measurable_bounded_integrand P x₀ hΨb hΨm c₀ hC₀ hCf
  have hM0 : 0 ≤ |c₀| * C₀ + B * Cf := by positivity
  -- uniform-in-`τ` stability estimate
  have hA : ∀ δ > 0, ∀ᶠ k in atTop, ∀ τ : P.Relaxed,
      |hamiltonianIntegral P τ (x k) (Θ k) (c k) - hamiltonianIntegral P τ x₀ Ψ c₀|
        ≤ |c k - c₀| * C₀ + Cf * ∫ t, ‖Θ k t - Ψ t‖
          ∂(horizonProbability P.horizon P.horizon_pos).toMeasure + (|c₀| + 1 + B) * δ := by
    intro δ hδ
    have hc1 : ∀ᶠ k in atTop, |c k| ≤ |c₀| + 1 := by
      filter_upwards [hc.abs.eventually (gt_mem_nhds (lt_add_one |c₀|))] with k hk using hk.le
    filter_upwards [hunif δ hδ, hc1] with k hk hck
    intro τ
    have hα : ∀ (t : P.Time) (u : P.Control),
        |c k * P.runningCost t (x k t) u - c₀ * P.runningCost t (x₀ t) u|
          ≤ |c k| * δ + |c k - c₀| * C₀ := by
      intro t u
      have e : c k * P.runningCost t (x k t) u - c₀ * P.runningCost t (x₀ t) u
          = c k * (P.runningCost t (x k t) u - P.runningCost t (x₀ t) u)
            + (c k - c₀) * P.runningCost t (x₀ t) u := by ring
      rw [e]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hk t u).1 (abs_nonneg _)
      · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hC₀ t u) (abs_nonneg _)
    have := abs_hamiltonianIntegral_sub_le P τ (x k) x₀ hΨb hΨm (hΘm k) (hΘi k) hC₀ hCf
      (fun t u => (hk t u).2.2) hα (fun t u => (hk t u).2.1)
    have h2 : |c k| * δ ≤ (|c₀| + 1) * δ := mul_le_mul_of_nonneg_right hck hδ.le
    nlinarith
  -- the measure-change estimate at the limit integrand
  have hB : ∀ k, |hamiltonianIntegral P (ρ k) x₀ Ψ c₀ - hamiltonianIntegral P ρ₀ x₀ Ψ c₀|
      ≤ 2 * relaxedControlDistance P (ρ k) ρ₀ * (|c₀| * C₀ + B * Cf) := by
    intro k
    have e : ∀ τ : P.Relaxed, hamiltonianIntegral P τ x₀ Ψ c₀ = ∫ z, g z ∂τ.measure :=
      fun τ => (integral_congr_ae (hgae τ)).symm
    rw [e, e]
    exact RelaxedControl.abs_integral_sub_le_of_forall_abs_measureReal_sub_le _ _
      (fun A hA => RelaxedControl.abs_measureReal_sub_le_kernelDistance_univ (ρ k) ρ₀ hA)
      hgm hgb hM0
  have hd0 : ∀ k, 0 ≤ relaxedControlDistance P (ρ k) ρ₀ := fun k =>
    RelaxedControl.kernelDistance_nonneg _ _
  set G : ℕ → ℝ := fun k => |c k - c₀| * C₀ + Cf * ∫ t, ‖Θ k t - Ψ t‖
    ∂(horizonProbability P.horizon P.horizon_pos).toMeasure
    + 2 * relaxedControlDistance P (ρ k) ρ₀ * (|c₀| * C₀ + B * Cf) with hG
  have hGt : Tendsto G atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => |c k - c₀|) atTop (𝓝 0) := by
      simpa using (hc.sub_const c₀).abs
    simpa [hG] using ((h1.mul_const C₀).add (hΘ.const_mul Cf)).add
      ((hρ.const_mul 2).mul_const (|c₀| * C₀ + B * Cf))
  have hT : Tendsto (fun k => hamiltonianIntegral P (ρ k) (x k) (Θ k) (c k)) atTop
      (𝓝 (hamiltonianIntegral P ρ₀ x₀ Ψ c₀)) := by
    refine tendsto_of_forall_eventually_abs_sub_le hGt (K := |c₀| + 1 + B) fun δ hδ => ?_
    filter_upwards [hA δ hδ] with k hk
    have h1 := hk (ρ k)
    have h2 := hB k
    have h3 := abs_sub_le (hamiltonianIntegral P (ρ k) (x k) (Θ k) (c k))
      (hamiltonianIntegral P (ρ k) x₀ Ψ c₀) (hamiltonianIntegral P ρ₀ x₀ Ψ c₀)
    simp only [hG]
    linarith
  have hS : Tendsto (fun k => hamiltonianIntegral P σ (x k) (Θ k) (c k)) atTop
      (𝓝 (hamiltonianIntegral P σ x₀ Ψ c₀)) := by
    refine tendsto_of_forall_eventually_abs_sub_le hGt (K := |c₀| + 1 + B) fun δ hδ => ?_
    filter_upwards [hA δ hδ] with k hk
    have h1 := hk σ
    have h2 : 0 ≤ 2 * relaxedControlDistance P (ρ k) ρ₀ * (|c₀| * C₀ + B * Cf) := by
      have := hd0 k
      positivity
    simp only [hG]
    linarith
  have := le_of_tendsto_of_tendsto hT (hS.add heps) (Eventually.of_forall fun k => hH k σ)
  simpa using this

end Problem

end OptimalControl.BoundedState
