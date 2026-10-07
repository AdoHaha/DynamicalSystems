/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.StateMultiplierLimit
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Geometry.Euclidean.Inversion.Calculus

/-!
# The boundary perturbation `h = ∇G/|∇G|²` and the uniform bound on the multiplier mass

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemma 11.3.5, Assumption 11.3.8
and (11.6.11).  The limit `j → ∞` of the penalised multipliers (`StateMultiplierLimit.lean`) needs a
uniform bound on the total multiplier masses `∫₀ᵀ j ω'(G(t, γ_j(t))) dt`.  The book obtains it by
perturbing the minimiser in the **outward direction** `h = ∇G/|∇G|²`, for which `⟨∇G, h⟩ = 1`.  This
file carries out that argument on the velocity carrier:

* `boundaryField φ = ∇G/|∇G|²` for a covector `φ = ∇G`, realised as the Kelvin inversion of the
Riesz
  vector of `φ` (`apply_boundaryField`: `φ (boundaryField φ) = 1`; `norm_boundaryField`;
  `dist_boundaryField_le`: it is Lipschitz away from `0`; `exists_hasDerivAt_boundaryField`);
* `VelocityTrajectory.exists_boundaryPerturbation`: under the nondegeneracy `‖∇G(t,γ t)‖ ≥ c₀ > 0`
  (Assumption 11.3.8, `ConstraintNondegenerate`), the field `h(t) = ∇G(t,γ t)/|∇G(t,γ t)|²` along a
  velocity trajectory is absolutely continuous with `h' ∈ L¹`, `⟨∇G, h⟩ = 1` and
  `‖h'‖ ≤ c₀⁻² C (1 + ‖γ'‖)`;
* `VelocityTrajectory.integral_statePenaltyDensity_le`: the multiplier mass is bounded in terms of
  the endpoint covectors, the `L²` norm of `γ'` and the growth constants of `L` and `G` only;
* `exists_uniform_nondegeneracy`, `exists_massBound_of_nondegenerate`: nondegeneracy
  `∇G(t, γL t) ≠ 0` along the *limit* path propagates to a uniform tube, so the masses along a
  uniformly convergent sequence of minimisers are bounded;
* `exists_stateMultiplier_limit_of_nondegenerate`: the `j → ∞` limit theorem of
  `StateMultiplierLimit.lean` with the mass bound discharged by nondegeneracy;
* `Problem.EndpointInterior.exists_slack_collar`, `Problem.EndpointInterior.slack_collar_of_close`,
  `Problem.ConstraintNondegenerate.ne_zero_clamped`: the library's Assumptions 11.4.1 and 11.3.8 in
  the `G : ℝ → E → ℝ` form used here (the first two pass the slack collar of the reference to the
  `ε`-minimisers).

Book citations live in docstrings only.
-/

@[expose] public section

open Set MeasureTheory Filter ACEulerLagrange
open scoped Topology Interval

namespace OptimalControl.BoundedState

section BoundaryField

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The Riesz isomorphism from covectors to vectors as a real-linear continuous map. -/
noncomputable def rieszCovector : (E →L[ℝ] ℝ) →L[ℝ] E :=
  { toFun := (InnerProductSpace.toDual ℝ E).symm
    map_add' := map_add _
    map_smul' := fun r x => by simp
    cont := (InnerProductSpace.toDual ℝ E).symm.continuous }

/-- The Riesz vector of `φ` represents `φ` by the inner product. -/
theorem inner_rieszCovector (φ : E →L[ℝ] ℝ) (x : E) : inner ℝ (rieszCovector φ) x = φ x := by
  simp [rieszCovector]

/-- The Riesz isomorphism preserves norms. -/
theorem norm_rieszCovector (φ : E →L[ℝ] ℝ) : ‖rieszCovector φ‖ = ‖φ‖ := by
  simp [rieszCovector]

/-- The **outward boundary field** `∇G/|∇G|²` of a covector `φ = ∇G`: the Kelvin inversion of the
Riesz vector of `φ`.  It is the direction `h = ∇G/|∇G|²` of the book's boundary perturbation, for
which `φ h = 1`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemma 11.3.5. -/
noncomputable def boundaryField (φ : E →L[ℝ] ℝ) : E :=
  EuclideanGeometry.inversion (0 : E) 1 (rieszCovector φ)

theorem boundaryField_eq (φ : E →L[ℝ] ℝ) :
    boundaryField φ = (1 / ‖φ‖) ^ 2 • rieszCovector φ := by
  simp [boundaryField, EuclideanGeometry.inversion, norm_rieszCovector]

/-- `⟨∇G, ∇G/|∇G|²⟩ = 1`. -/
theorem apply_boundaryField {φ : E →L[ℝ] ℝ} (hφ : φ ≠ 0) : φ (boundaryField φ) = 1 := by
  have hn : ‖φ‖ ≠ 0 := norm_ne_zero_iff.2 hφ
  rw [boundaryField_eq, ← inner_rieszCovector, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_rieszCovector]
  field_simp

/-- `‖∇G/|∇G|²‖ = 1/‖∇G‖`. -/
theorem norm_boundaryField (φ : E →L[ℝ] ℝ) : ‖boundaryField φ‖ = ‖φ‖⁻¹ := by
  by_cases hφ : φ = 0
  · simp [hφ, boundaryField]
  · have hn : 0 < ‖φ‖ := norm_pos_iff.2 hφ
    rw [boundaryField_eq, norm_smul, norm_rieszCovector, Real.norm_eq_abs, abs_of_nonneg (by
        positivity)]
    field_simp

/-- The boundary field is Lipschitz on covectors of norm at least `c₀`:
`‖h(φ) - h(ψ)‖ ≤ c₀⁻² ‖φ - ψ‖`. -/
theorem dist_boundaryField_le {φ ψ : E →L[ℝ] ℝ} {c₀ : ℝ} (hc₀ : 0 < c₀) (hφ : c₀ ≤ ‖φ‖)
    (hψ : c₀ ≤ ‖ψ‖) :
    dist (boundaryField φ) (boundaryField ψ) ≤ (c₀ ^ 2)⁻¹ * dist φ ψ := by
  have hu : rieszCovector φ ≠ 0 := by
    intro h
    have := norm_rieszCovector φ
    rw [h, norm_zero] at this
    linarith
  have hv : rieszCovector ψ ≠ 0 := by
    intro h
    have := norm_rieszCovector ψ
    rw [h, norm_zero] at this
    linarith
  unfold boundaryField
  rw [EuclideanGeometry.dist_inversion_inversion hu hv, dist_zero_right, dist_zero_right,
    norm_rieszCovector, norm_rieszCovector, dist_eq_norm, dist_eq_norm, ← map_sub,
    norm_rieszCovector]
  have hφ0 : 0 < ‖φ‖ := hc₀.trans_le hφ
  have hψ0 : 0 < ‖ψ‖ := hc₀.trans_le hψ
  have h1 : (c₀ ^ 2)⁻¹ ≥ 1 ^ 2 / (‖φ‖ * ‖ψ‖) := by
    rw [one_pow, ge_iff_le, div_le_iff₀ (by positivity)]
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul hφ hψ hc₀.le hφ0.le]
  exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

/-- **Differentiation of the boundary field along a differentiable covector path.**  If
`g` has derivative `g'` at `t` and `g t ≠ 0`, then `t ↦ ∇G/|∇G|² (g t)` has a derivative of norm
at most `‖g'‖/‖g t‖²`. -/
theorem exists_hasDerivAt_boundaryField {g : ℝ → E →L[ℝ] ℝ} {g' : E →L[ℝ] ℝ} {t : ℝ}
    (hg : HasDerivAt g g' t) (hne : g t ≠ 0) :
    ∃ d : E, HasDerivAt (fun s => boundaryField (g s)) d t ∧ ‖d‖ ≤ (‖g t‖ ^ 2)⁻¹ * ‖g'‖ := by
  have hu : rieszCovector (g t) ≠ 0 := by
    intro h
    have := norm_rieszCovector (g t)
    rw [h, norm_zero] at this
    exact hne (norm_eq_zero.1 this.symm)
  have hJ : HasDerivAt (fun s => rieszCovector (g s)) (rieszCovector g') t :=
    (rieszCovector (E := E)).hasFDerivAt.comp_hasDerivAt t hg
  have hinv := (EuclideanGeometry.hasFDerivAt_inversion (c := (0 : E)) (R := (1 : ℝ))
      hu).comp_hasDerivAt
    t hJ
  refine ⟨_, hinv, ?_⟩
  simp only [smul_apply, norm_smul, Real.norm_eq_abs]
  rw [dist_zero_right, norm_rieszCovector]
  simp [norm_rieszCovector]

end BoundaryField

section Perturbation

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]
  {P : Problem E V W}

/-- **The boundary perturbation `h = ∇G/|∇G|²` along a velocity trajectory.**  Let `γ` be a velocity
trajectory with `‖γ t‖ ≤ R`, `‖∇²G‖ ≤ C` on the `R`-ball, and the nondegeneracy
`‖∇G(t, γ t)‖ ≥ c₀ > 0` (Assumption 11.3.8).  Then `h(t) = ∇G(t,γ t)/|∇G(t,γ t)|²` is absolutely
continuous, `h = h(0) + ∫₀ᵗ h'` with `h'` interval integrable and `‖h'‖ ≤ c₀⁻² C (1 + ‖γ'‖)` a.e.,
`⟨∇G(t,γ t), h(t)⟩ = 1` and `‖h(t)‖ ≤ c₀⁻¹`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemma 11.3.5 and
Assumption 11.3.8. -/
theorem VelocityTrajectory.exists_boundaryPerturbation (γ : VelocityTrajectory P)
    {Gx : ℝ → E → E →L[ℝ] ℝ} {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)}
    (hG : StateGradientRegularity Gx Gxd) {R C c₀ : ℝ} (hC0 : 0 ≤ C)
    (hR : ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖γ.value t‖ ≤ R)
    (hC : ∀ t y, ‖y‖ ≤ R → ‖Gxd t y‖ ≤ C) (hc₀ : 0 < c₀)
    (hND : ∀ t ∈ Icc (0 : ℝ) P.horizon, c₀ ≤ ‖Gx t (γ.value t)‖) :
    ∃ h h' : ℝ → E, IntervalIntegrable h' volume 0 P.horizon ∧
      (∀ t ∈ Icc (0 : ℝ) P.horizon, h t = h 0 + ∫ r in (0 : ℝ)..t, h' r) ∧
      (∀ t ∈ Icc (0 : ℝ) P.horizon, Gx t (γ.value t) (h t) = 1) ∧
      (∀ t ∈ Icc (0 : ℝ) P.horizon, ‖h t‖ ≤ c₀⁻¹) ∧
      (∀ᵐ r ∂(timeMeasure P.horizon), ‖h' r‖ ≤ (c₀ ^ 2)⁻¹ * (C * (1 + ‖γ.velocity r‖))) := by
  have hT : 0 ≤ P.horizon := P.horizon_pos.le
  obtain ⟨-, hAC, hder, hdom, hbound⟩ := γ.gradientAlongPath_aux hG hC0 hR hC
  set g : ℝ → E →L[ℝ] ℝ := fun t => Gx t (γ.value t) with hg
  set h : ℝ → E := fun t => boundaryField (g t) with hh
  have hne : ∀ t ∈ Icc (0 : ℝ) P.horizon, g t ≠ 0 := by
    intro t ht h0
    have := hND t ht
    rw [show Gx t (γ.value t) = g t from rfl, h0, norm_zero] at this
    linarith
  -- absolute continuity of `h`
  have hACh : AbsolutelyContinuousOnInterval h 0 P.horizon := by
    refine absolutelyContinuousOnInterval_of_dist_le (K := (c₀ ^ 2)⁻¹ * C)
      γ.absolutelyContinuousOnInterval_arcParameter fun x hx y hy => ?_
    rw [uIcc_of_le hT] at hx hy
    calc dist (h x) (h y) ≤ (c₀ ^ 2)⁻¹ * dist (g x) (g y) :=
          dist_boundaryField_le hc₀ (hND x hx) (hND y hy)
      _ ≤ (c₀ ^ 2)⁻¹ * (C * dist (γ.arcParameter x) (γ.arcParameter y)) := by
          gcongr
          exact hdom x hx y hy
      _ = _ := by ring
  -- a.e. derivative of `h`, with its norm bound
  have hderh : ∀ᵐ t, t ∈ uIcc (0 : ℝ) P.horizon →
      HasDerivAt h (deriv h t) t ∧ ‖deriv h t‖ ≤ (c₀ ^ 2)⁻¹ *
        ‖Gxd t (γ.value t) (1, γ.velocity t)‖ := by
    filter_upwards [hder] with t ht htm
    rw [uIcc_of_le hT] at htm
    obtain ⟨d, hd, hdn⟩ := exists_hasDerivAt_boundaryField (ht (by rwa [uIcc_of_le hT])) (hne t htm)
    refine ⟨by rw [hd.deriv]; exact hd, ?_⟩
    rw [hd.deriv]
    refine hdn.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have : c₀ ^ 2 ≤ ‖g t‖ ^ 2 := by gcongr; exact hND t htm
    exact inv_anti₀ (by positivity) this
  have hbd : ∀ᵐ r ∂(timeMeasure P.horizon), ‖deriv h r‖ ≤
      (c₀ ^ 2)⁻¹ * (C * (1 + ‖γ.velocity r‖)) := by
    have hae := (ae_restrict_iff' measurableSet_Ioc).1 hbound
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hderh, hae] with t ht1 ht2 htm
    have h1 := (ht1 (by rw [uIcc_of_le hT]; exact ⟨htm.1.le, htm.2⟩)).2
    exact h1.trans (mul_le_mul_of_nonneg_left (ht2 htm) (by positivity))
  have hint : IntervalIntegrable (deriv h) volume 0 P.horizon := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    have hv : IntegrableOn γ.velocity (Ioc (0 : ℝ) P.horizon) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 γ.velocity_intervalIntegrable
    exact Integrable.mono' (g := fun r => (c₀ ^ 2)⁻¹ * (C * (1 + ‖γ.velocity r‖)))
      ((((integrable_const (1 : ℝ)).add hv.norm).const_mul C).const_mul _)
      (measurable_deriv h).aestronglyMeasurable hbd
  refine ⟨h, deriv h, hint, ?_, ?_, ?_, hbd⟩
  · exact eq_add_integral_of_absolutelyContinuousOnInterval hT hint hACh
      (hderh.mono fun t ht htm => (ht htm).1)
  · intro t ht
    exact apply_boundaryField (hne t ht)
  · intro t ht
    change ‖boundaryField (g t)‖ ≤ c₀⁻¹
    rw [norm_boundaryField]
    exact inv_anti₀ hc₀ (hND t ht)

/-- **Uniform bound on the multiplier mass (Lemma 11.3.5).**  Let `γ` satisfy the integrated
Euler-Lagrange relations of the penalised functional at level `j ≥ 0` (`hEL`, `hTT`, the output of
`VelocityTrajectory.statePenalised_weakEulerLagrange`) with initial and terminal covectors `c`,
`-q`,
and let `‖γ t‖ ≤ R`, `‖∇²G‖ ≤ C` on the `R`-ball, `‖∂ₓL‖, ‖∂ᵥL‖ ≤ env + C_L ‖γ'‖` there, and
`‖∇G(t,γ t)‖ ≥ c₀ > 0` (Assumption 11.3.8).  Then, with `K = c₀⁻² C`,

`∫₀ᵀ j ω'(G(t,γ t)) dt ≤ (‖q‖ + ‖c‖)/c₀ + ∫₀ᵀ ‖env‖² + (C_L² + K²) ∫₀ᵀ ‖γ'‖² + T (c₀⁻¹ + K)²`.

The right-hand side depends on the minimiser only through `‖q‖`, `‖c‖` and `‖γ'‖_{L²}`, all
uniformly
bounded in the `j → ∞` limit.  The proof pairs the integrated Euler-Lagrange equation with the
boundary perturbation `h = ∇G/|∇G|²` (`VelocityTrajectory.exists_boundaryPerturbation`) through
`integral_density_eq_boundary`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemma 11.3.5 and Assumption
11.3.8. -/
theorem VelocityTrajectory.integral_statePenaltyDensity_le (γ : VelocityTrajectory P)
    {L : ℝ → E → E → ℝ} {Lx Lv : ℝ → E → E → E →L[ℝ] ℝ}
    (hD : IsCaratheodoryC1 P.horizon L Lx Lv) {ω ω' : ℝ → ℝ}
    (hω : StatePenaltyProfile ω ω') {G : ℝ → E → ℝ} {Gx : ℝ → E → E →L[ℝ] ℝ}
    (hG : StateConstraintRegularity G Gx)
    {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)} (hGx : StateGradientRegularity Gx Gxd)
    {j : ℝ} {R C CL c₀ : ℝ} {env : ℝ → ℝ} (hC0 : 0 ≤ C) (hCL : 0 ≤ CL)
    (henv : MemLp env 2 (timeMeasure P.horizon))
    (hR : ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖γ.value t‖ ≤ R)
    (hC : ∀ t y, ‖y‖ ≤ R → ‖Gxd t y‖ ≤ C)
    (hgrow : ∀ t y w, ‖y‖ ≤ R →
      ‖Lx t y w‖ ≤ env t + CL * ‖w‖ ∧ ‖Lv t y w‖ ≤ env t + CL * ‖w‖)
    (hc₀ : 0 < c₀) (hND : ∀ t ∈ Icc (0 : ℝ) P.horizon, c₀ ≤ ‖Gx t (γ.value t)‖)
    (c q : E →L[ℝ] ℝ)
    (hEL : ∀ᵐ t ∂(timeMeasure P.horizon), Lv t (γ.value t) (γ.velocity t)
      = c + ∫ r in (0 : ℝ)..t, (Lx r (γ.value r) (γ.velocity r)
        + statePenaltyDensity ω' G j γ r • Gx r (γ.value r)))
    (hTT : c + ∫ r in (0 : ℝ)..P.horizon, (Lx r (γ.value r) (γ.velocity r)
        + statePenaltyDensity ω' G j γ r • Gx r (γ.value r)) = -q) :
    ∫ r in (0 : ℝ)..P.horizon, statePenaltyDensity ω' G j γ r
      ≤ (‖q‖ + ‖c‖) / c₀ + (∫ r in (0 : ℝ)..P.horizon, ‖env r‖ ^ 2)
        + (CL ^ 2 + ((c₀ ^ 2)⁻¹ * C) ^ 2) * (∫ r in (0 : ℝ)..P.horizon, ‖γ.velocity r‖ ^ 2)
        + P.horizon * (c₀⁻¹ + (c₀ ^ 2)⁻¹ * C) ^ 2 := by
  have hT : 0 ≤ P.horizon := P.horizon_pos.le
  have hT0 : P.horizon ∈ Icc (0 : ℝ) P.horizon := ⟨hT, le_rfl⟩
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) P.horizon := ⟨le_rfl, hT⟩
  obtain ⟨h, h', hh'int, hhprim, hgh, hhn, hh'b⟩ :=
    γ.exists_boundaryPerturbation hGx hC0 hR hC hc₀ hND
  obtain ⟨hgdint, hgprim⟩ := γ.gradientAlongPath_eq_primitive hGx
  have hgc : ContinuousOn (fun r => Gx r (γ.value r)) (Icc (0 : ℝ) P.horizon) :=
    continuousOn_of_primitive hT hgdint hgprim
  have hm := intervalIntegrable_statePenaltyDensity hω hG j γ
  have ha : IntervalIntegrable (fun r => Lx r (γ.value r) (γ.velocity r)) volume 0 P.horizon :=
    intervalIntegrable_of_memLp hT (memLp_stateGradient hD hT γ.memLp_velocity γ.initial)
  have hid := integral_density_eq_boundary hT hm c ha hgc hh'int hhprim
    (fun r hr => by simp [hgh r hr])
  have hTT' : c + ∫ r in (0 : ℝ)..P.horizon, (Lx r (γ.value r) (γ.velocity r)
      + statePenaltyDensity ω' G j γ r • Gx r (γ.value r)) = -q := hTT
  rw [hTT'] at hid
  set K' : ℝ := (c₀ ^ 2)⁻¹ * C with hK'
  have hK'0 : 0 ≤ K' := by positivity
  -- the pointwise bound of the remaining integrand
  have key : ∀ e w : ℝ, 0 ≤ e → 0 ≤ w →
      (e + CL * w) * c₀⁻¹ + (e + CL * w) * (K' * (1 + w))
        ≤ e ^ 2 + (CL ^ 2 + K' ^ 2) * w ^ 2 + (c₀⁻¹ + K') ^ 2 := by
    intro e w he hw
    nlinarith [sq_nonneg ((e + CL * w) - ((c₀⁻¹ + K') + K' * w)), sq_nonneg (e - CL * w),
      sq_nonneg ((c₀⁻¹ + K') - K' * w)]
  have hE2 : IntervalIntegrable (fun r => ‖env r‖ ^ 2) volume 0 P.horizon :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2
      (henv.integrable_sq.congr (Filter.Eventually.of_forall fun r => by simp))
  have hW2 : IntervalIntegrable (fun r => ‖γ.velocity r‖ ^ 2) volume 0 P.horizon :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).2 γ.velocity_sq_integrable
  have hSint : IntervalIntegrable (fun r => ‖env r‖ ^ 2 + (CL ^ 2 + K' ^ 2) * ‖γ.velocity r‖ ^ 2
      + (c₀⁻¹ + K') ^ 2) volume 0 P.horizon :=
    (hE2.add (hW2.const_mul _)).add intervalIntegrable_const
  have hSval : ∫ r in (0 : ℝ)..P.horizon, (‖env r‖ ^ 2 + (CL ^ 2 + K' ^ 2) * ‖γ.velocity r‖ ^ 2
      + (c₀⁻¹ + K') ^ 2)
      = (∫ r in (0 : ℝ)..P.horizon, ‖env r‖ ^ 2)
        + (CL ^ 2 + K' ^ 2) * (∫ r in (0 : ℝ)..P.horizon, ‖γ.velocity r‖ ^ 2)
        + P.horizon * (c₀⁻¹ + K') ^ 2 := by
    rw [intervalIntegral.integral_add (hE2.add (hW2.const_mul _)) intervalIntegrable_const,
      intervalIntegral.integral_add hE2 (hW2.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp
  have hIbound : ‖∫ r in (0 : ℝ)..P.horizon, (Lx r (γ.value r) (γ.velocity r) (h r)
      + (c + ∫ s in (0 : ℝ)..r, (Lx s (γ.value s) (γ.velocity s)
        + statePenaltyDensity ω' G j γ s • Gx s (γ.value s))) (h' r))‖
      ≤ ∫ r in (0 : ℝ)..P.horizon, (‖env r‖ ^ 2 + (CL ^ 2 + K' ^ 2) * ‖γ.velocity r‖ ^ 2
        + (c₀⁻¹ + K') ^ 2) := by
    refine intervalIntegral.norm_integral_le_of_norm_le hT ?_ hSint
    have hEL' := (ae_restrict_iff' measurableSet_Ioc).1 hEL
    have hh'b' := (ae_restrict_iff' measurableSet_Ioc).1 hh'b
    filter_upwards [hEL', hh'b'] with r h1 h2 hr
    have hrI : r ∈ Icc (0 : ℝ) P.horizon := ⟨hr.1.le, hr.2⟩
    obtain ⟨hLx, hLv⟩ := hgrow r (γ.value r) (γ.velocity r) (hR r hrI)
    have he : env r ≤ ‖env r‖ := le_abs_self _
    have hw0 := norm_nonneg (γ.velocity r)
    have hv1 : ‖Lx r (γ.value r) (γ.velocity r)‖ ≤ ‖env r‖ + CL * ‖γ.velocity r‖ := by linarith
    have hp : ‖c + ∫ s in (0 : ℝ)..r, (Lx s (γ.value s) (γ.velocity s)
        + statePenaltyDensity ω' G j γ s • Gx s (γ.value s))‖
        ≤ ‖env r‖ + CL * ‖γ.velocity r‖ := by
      rw [← h1 hr]; linarith
    have hhb : ‖h' r‖ ≤ K' * (1 + ‖γ.velocity r‖) := by
      rw [hK', mul_assoc]; exact h2 hr
    have hu : 0 ≤ ‖env r‖ + CL * ‖γ.velocity r‖ := by positivity
    calc ‖Lx r (γ.value r) (γ.velocity r) (h r) + (c + ∫ s in (0 : ℝ)..r,
            (Lx s (γ.value s) (γ.velocity s)
              + statePenaltyDensity ω' G j γ s • Gx s (γ.value s))) (h' r)‖
        ≤ ‖Lx r (γ.value r) (γ.velocity r) (h r)‖ + ‖(c + ∫ s in (0 : ℝ)..r,
            (Lx s (γ.value s) (γ.velocity s)
              + statePenaltyDensity ω' G j γ s • Gx s (γ.value s))) (h' r)‖ :=
          norm_add_le _ _
      _ ≤ (‖env r‖ + CL * ‖γ.velocity r‖) * c₀⁻¹
          + (‖env r‖ + CL * ‖γ.velocity r‖) * (K' * (1 + ‖γ.velocity r‖)) := by
          refine add_le_add ?_ ?_
          · exact ((Lx r (γ.value r) (γ.velocity r)).le_opNorm (h r)).trans
              (mul_le_mul hv1 (hhn r hrI) (norm_nonneg _) hu)
          · exact (ContinuousLinearMap.le_opNorm _ _).trans
              (mul_le_mul hp hhb (norm_nonneg _) hu)
      _ ≤ _ := key _ _ (norm_nonneg _) hw0
  -- assemble
  have hqh : ‖(-q) (h P.horizon)‖ ≤ ‖q‖ * c₀⁻¹ := by
    calc ‖(-q) (h P.horizon)‖ ≤ ‖-q‖ * ‖h P.horizon‖ := (-q).le_opNorm _
      _ ≤ ‖q‖ * c₀⁻¹ := by
        rw [norm_neg]
        exact mul_le_mul_of_nonneg_left (hhn _ hT0) (norm_nonneg _)
  have hch : ‖c (h 0)‖ ≤ ‖c‖ * c₀⁻¹ :=
    (c.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hhn _ h00) (norm_nonneg _))
  have h1 : |(-q) (h P.horizon)| ≤ ‖q‖ * c₀⁻¹ := by rwa [← Real.norm_eq_abs]
  have h2 : |c (h 0)| ≤ ‖c‖ * c₀⁻¹ := by rwa [← Real.norm_eq_abs]
  have h3 := (abs_le.1 (Real.norm_eq_abs _ ▸ hIbound)).1
  rw [hSval] at h3
  have h4 := (abs_le.1 h1).2
  have h5 := (abs_le.1 h2).1
  have h6 : (‖q‖ + ‖c‖) / c₀ = ‖q‖ * c₀⁻¹ + ‖c‖ * c₀⁻¹ := by
    rw [add_div, div_eq_mul_inv, div_eq_mul_inv]
  rw [h6]
  linarith

end Perturbation

section Final

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]
  {P : Problem E V W}

/-- **The multiplier masses of a sequence of penalised minimisers are uniformly bounded.**  Let
`seq` be a sequence of minimisers of the `ω`-penalised functionals converging (uniformly on `[0,T]`)
to `γL`, with `C¹` endpoint penalties at the limit endpoint data, with `‖γ_n‖ ≤ R`, `‖γ_n'‖_{L²}`
bounded, and the constraint nondegenerate along the sequence (`‖∇G(t,γ_n t)‖ ≥ c₀ > 0`,
Assumption 11.3.8).  Then `n ↦ ∫₀ᵀ j_n ω'(G(t,γ_n t)) dt` is bounded.  This is the estimate that
the book obtains from the boundary perturbation `h = ∇G/|∇G|²` (Lemma 11.3.5); here it is
`VelocityTrajectory.integral_statePenaltyDensity_le`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemma 11.3.5 and
Assumption 11.3.8. -/
theorem exists_massBound_of_uniformNondegenerate
    {L : ℝ → E → E → ℝ} {Lx Lv : ℝ → E → E → E →L[ℝ] ℝ}
    (hD : IsCaratheodoryC1 P.horizon L Lx Lv) {ω ω' : ℝ → ℝ}
    (hω : StatePenaltyProfile ω ω') {G : ℝ → E → ℝ} {Gx : ℝ → E → E →L[ℝ] ℝ}
    (hG : StateConstraintRegularity G Gx)
    {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)} (hGx : StateGradientRegularity Gx Gxd)
    {Φ₀ : E → ℝ} {Φ₁ : E × E → ℝ} (seq : PenalisedMinimiserSequence P L G ω Φ₀ Φ₁)
    (γL : VelocityTrajectory P)
    (hpath : ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) P.horizon,
      dist ((seq.path n).value t) (γL.value t) < ε)
    (hΦ₀c : ContinuousAt (fderiv ℝ Φ₀) (γL.value 0))
    (hΦ₁c : ContinuousAt (fderiv ℝ Φ₁) (γL.value 0, γL.value P.horizon))
    {R c₀ W₂ : ℝ} (hR : ∀ n, ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖(seq.path n).value t‖ ≤ R)
    (hc₀ : 0 < c₀)
    (hND : ∀ n, ∀ t ∈ Icc (0 : ℝ) P.horizon, c₀ ≤ ‖Gx t ((seq.path n).value t)‖)
    (hW₂ : ∀ n, ∫ r in (0 : ℝ)..P.horizon, ‖(seq.path n).velocity r‖ ^ 2 ≤ W₂) :
    ∃ M : ℝ, ∀ n, ∫ r in (0 : ℝ)..P.horizon,
      statePenaltyDensity ω' G (seq.penalty n) (seq.path n) r ≤ M := by
  have hT : 0 ≤ P.horizon := P.horizon_pos.le
  have hT0 : P.horizon ∈ Icc (0 : ℝ) P.horizon := ⟨hT, le_rfl⟩
  have h00 : (0 : ℝ) ∈ Icc (0 : ℝ) P.horizon := ⟨le_rfl, hT⟩
  choose c hEL h0 hTT using fun n => (seq.path n).statePenalised_weakEulerLagrange
    (seq.functional n) (seq.competitors n) hD hω hG (seq.penalty n) (seq.functional_eq n)
    (seq.isMinOn n) (seq.interior n) (seq.integrable n) (seq.differentiable₀ n)
    (seq.differentiable₁ n)
  -- convergence, hence boundedness, of the endpoint covectors
  have hpt : ∀ t ∈ Icc (0 : ℝ) P.horizon,
      Tendsto (fun n => (seq.path n).value t) atTop (𝓝 (γL.value t)) := fun t ht =>
    Metric.tendsto_nhds.2 fun ε hε => (hpath ε hε).mono fun n hn => hn t ht
  have hend : Tendsto (fun n => ((seq.path n).value 0, (seq.path n).value P.horizon)) atTop
      (𝓝 (γL.value 0, γL.value P.horizon)) := (hpt 0 h00).prodMk_nhds (hpt _ hT0)
  have hF1 : Tendsto (fun n => fderiv ℝ Φ₁ ((seq.path n).value 0, (seq.path n).value P.horizon))
      atTop (𝓝 (fderiv ℝ Φ₁ (γL.value 0, γL.value P.horizon))) := hΦ₁c.tendsto.comp hend
  have hF0 : Tendsto (fun n => fderiv ℝ Φ₀ ((seq.path n).value 0)) atTop
      (𝓝 (fderiv ℝ Φ₀ (γL.value 0))) := hΦ₀c.tendsto.comp (hpt 0 h00)
  have hF1l : Tendsto (fun n => (fderiv ℝ Φ₁ ((seq.path n).value 0,
      (seq.path n).value P.horizon)).comp (ContinuousLinearMap.inl ℝ E E)) atTop
      (𝓝 ((fderiv ℝ Φ₁ (γL.value 0, γL.value P.horizon)).comp
        (ContinuousLinearMap.inl ℝ E E))) :=
    ((continuous_id.clm_comp_const (ContinuousLinearMap.inl ℝ E E)).tendsto _).comp hF1
  have hcn : Tendsto c atTop (𝓝 (fderiv ℝ Φ₀ (γL.value 0)
      + (fderiv ℝ Φ₁ (γL.value 0, γL.value P.horizon)).comp (ContinuousLinearMap.inl ℝ E E))) :=
    (hF0.add hF1l).congr fun n => (h0 n).symm
  have hqn : Tendsto (fun n => (fderiv ℝ Φ₁ ((seq.path n).value 0,
      (seq.path n).value P.horizon)).comp (ContinuousLinearMap.inr ℝ E E)) atTop
      (𝓝 ((fderiv ℝ Φ₁ (γL.value 0, γL.value P.horizon)).comp
        (ContinuousLinearMap.inr ℝ E E))) :=
    ((continuous_id.clm_comp_const (ContinuousLinearMap.inr ℝ E E)).tendsto _).comp hF1
  obtain ⟨Bc, hBc⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto c hcn)
  obtain ⟨Bq, hBq⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ hqn)
  obtain ⟨env, CL, henv, hCL, hgrow⟩ := hD.growth R
  obtain ⟨C, hC0, hC⟩ := hGx.bounded R
  refine ⟨(Bq + Bc) / c₀ + (∫ r in (0 : ℝ)..P.horizon, ‖env r‖ ^ 2)
      + (CL ^ 2 + ((c₀ ^ 2)⁻¹ * C) ^ 2) * W₂
      + P.horizon * (c₀⁻¹ + (c₀ ^ 2)⁻¹ * C) ^ 2, fun n => ?_⟩
  have hn := (seq.path n).integral_statePenaltyDensity_le hD hω hG hGx hC0 hCL henv (hR n) hC
    hgrow hc₀ (hND n) (c n) ((fderiv ℝ Φ₁ ((seq.path n).value 0,
      (seq.path n).value P.horizon)).comp (ContinuousLinearMap.inr ℝ E E)) (hEL n) (hTT n)
  have hq : ‖(fderiv ℝ Φ₁ ((seq.path n).value 0, (seq.path n).value P.horizon)).comp
      (ContinuousLinearMap.inr ℝ E E)‖ ≤ Bq := hBq _ ⟨n, rfl⟩
  have hc : ‖c n‖ ≤ Bc := hBc _ ⟨n, rfl⟩
  have hcoef : 0 ≤ CL ^ 2 + ((c₀ ^ 2)⁻¹ * C) ^ 2 := by positivity
  have h1 : (‖(fderiv ℝ Φ₁ ((seq.path n).value 0, (seq.path n).value P.horizon)).comp
      (ContinuousLinearMap.inr ℝ E E)‖ + ‖c n‖) / c₀ ≤ (Bq + Bc) / c₀ :=
    div_le_div_of_nonneg_right (by linarith) hc₀.le
  have h2 := mul_le_mul_of_nonneg_left (hW₂ n) hcoef
  linarith

/-- Shifting a sequence of penalised minimisers by `N` (dropping the first `N` terms). -/
def PenalisedMinimiserSequence.shift {L : ℝ → E → E → ℝ} {G : ℝ → E → ℝ} {ω : ℝ → ℝ}
    {Φ₀ : E → ℝ} {Φ₁ : E × E → ℝ} (seq : PenalisedMinimiserSequence P L G ω Φ₀ Φ₁) (N : ℕ) :
    PenalisedMinimiserSequence P L G ω Φ₀ Φ₁ where
  path n := seq.path (n + N)
  penalty n := seq.penalty (n + N)
  penalty_nonneg n := seq.penalty_nonneg (n + N)
  functional n := seq.functional (n + N)
  competitors n := seq.competitors (n + N)
  functional_eq n := seq.functional_eq (n + N)
  isMinOn n := seq.isMinOn (n + N)
  interior n := seq.interior (n + N)
  integrable n := seq.integrable (n + N)
  differentiable₀ n := seq.differentiable₀ (n + N)
  differentiable₁ n := seq.differentiable₁ (n + N)

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] in
/-- **Nondegeneracy along the limit path propagates to a tube** (Assumption 11.3.8).  If the
state covector `∇G` is jointly continuous and does not vanish along a continuous path `y` on
`[0,T]`, then `‖∇G(t,z)‖ ≥ c₀ > 0` whenever `‖z - y t‖ ≤ ρ`, for some `c₀, ρ > 0`. -/
theorem exists_uniform_nondegeneracy {Gx : ℝ → E → E →L[ℝ] ℝ}
    (hGxc : Continuous (fun p : ℝ × E => Gx p.1 p.2)) {T : ℝ} (hT : 0 ≤ T) {y : ℝ → E}
    (hy : ContinuousOn y (Icc (0 : ℝ) T)) (hne : ∀ t ∈ Icc (0 : ℝ) T, Gx t (y t) ≠ 0) :
    ∃ c₀ ρ : ℝ, 0 < c₀ ∧ 0 < ρ ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ z : E, dist z (y t) ≤ ρ →
      c₀ ≤ ‖Gx t z‖ := by
  have hne0 : (Icc (0 : ℝ) T).Nonempty := ⟨0, le_rfl, hT⟩
  have hφ : ContinuousOn (fun t => ‖Gx t (y t)‖) (Icc (0 : ℝ) T) :=
    (hGxc.comp_continuousOn (continuousOn_id.prodMk hy)).norm
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn hne0 hφ
  set m : ℝ := ‖Gx t₀ (y t₀)‖ with hm
  have hmpos : 0 < m := norm_pos_iff.2 (hne t₀ ht₀)
  have hK : IsCompact ((fun q : ℝ × E => (q.1, y q.1 + q.2)) ''
      (Icc (0 : ℝ) T ×ˢ Metric.closedBall (0 : E) 1)) := by
    refine (isCompact_Icc.prod (isCompact_closedBall 0 1)).image_of_continuousOn ?_
    exact (continuousOn_fst.prodMk ((hy.comp continuousOn_fst (fun q hq => hq.1)).add
      continuousOn_snd))
  have hunif := hK.uniformContinuousOn_of_continuous hGxc.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hunif
  obtain ⟨η, hη, hηG⟩ := hunif (m / 2) (by positivity)
  refine ⟨m / 2, min η 1 / 2, by positivity, by positivity, fun t ht z hz => ?_⟩
  have hρ1 : min η 1 / 2 < η := by
    have := min_le_left η 1
    linarith [lt_min hη one_pos]
  have hρ2 : min η 1 / 2 ≤ 1 := by
    have := min_le_right η 1
    linarith [lt_min hη one_pos]
  have hmem1 : (t, y t) ∈ (fun q : ℝ × E => (q.1, y q.1 + q.2)) ''
      (Icc (0 : ℝ) T ×ˢ Metric.closedBall (0 : E) 1) := ⟨(t, 0), ⟨ht, by simp⟩, by simp⟩
  have hmem2 : (t, z) ∈ (fun q : ℝ × E => (q.1, y q.1 + q.2)) ''
      (Icc (0 : ℝ) T ×ˢ Metric.closedBall (0 : E) 1) :=
    ⟨(t, z - y t), ⟨ht, by simpa [dist_eq_norm] using hz.trans hρ2⟩, by simp⟩
  have hclose := hηG (t, z) hmem2 (t, y t) hmem1 (by
    rw [Prod.dist_eq]
    simpa using hz.trans_lt hρ1)
  rw [dist_eq_norm] at hclose
  have h1 : ‖Gx t (y t)‖ ≤ ‖Gx t z‖ + ‖Gx t z - Gx t (y t)‖ := by
    calc ‖Gx t (y t)‖ = ‖Gx t z - (Gx t z - Gx t (y t))‖ := by rw [sub_sub_cancel]
      _ ≤ ‖Gx t z‖ + ‖Gx t z - Gx t (y t)‖ := by
        simpa using norm_sub_le (Gx t z) (Gx t z - Gx t (y t))
  have h2 : m ≤ ‖Gx t (y t)‖ := hmin ht
  linarith

/-- **The multiplier masses of a sequence of penalised minimisers are uniformly bounded, under
nondegeneracy at the limit path only.**  As `exists_massBound_of_uniformNondegenerate`, but the
uniform bounds `‖γ_n‖ ≤ R` and `‖∇G(t,γ_n t)‖ ≥ c₀` are derived (for large `n`) from the uniform
convergence `γ_n → γL` and the nondegeneracy `∇G(t, γL t) ≠ 0` of the limit path (Assumption 11.3.8,
`ConstraintNondegenerate`); the finitely many remaining terms are bounded individually.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemma 11.3.5 and
Assumption 11.3.8. -/
theorem exists_massBound_of_nondegenerate
    {L : ℝ → E → E → ℝ} {Lx Lv : ℝ → E → E → E →L[ℝ] ℝ}
    (hD : IsCaratheodoryC1 P.horizon L Lx Lv) {ω ω' : ℝ → ℝ}
    (hω : StatePenaltyProfile ω ω') {G : ℝ → E → ℝ} {Gx : ℝ → E → E →L[ℝ] ℝ}
    (hG : StateConstraintRegularity G Gx)
    {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)} (hGx : StateGradientRegularity Gx Gxd)
    {Φ₀ : E → ℝ} {Φ₁ : E × E → ℝ} (seq : PenalisedMinimiserSequence P L G ω Φ₀ Φ₁)
    (γL : VelocityTrajectory P)
    (hpath : ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) P.horizon,
      dist ((seq.path n).value t) (γL.value t) < ε)
    (hΦ₀c : ContinuousAt (fderiv ℝ Φ₀) (γL.value 0))
    (hΦ₁c : ContinuousAt (fderiv ℝ Φ₁) (γL.value 0, γL.value P.horizon))
    (hND : ∀ t ∈ Icc (0 : ℝ) P.horizon, Gx t (γL.value t) ≠ 0) {W₂ : ℝ}
    (hW₂ : ∀ n, ∫ r in (0 : ℝ)..P.horizon, ‖(seq.path n).velocity r‖ ^ 2 ≤ W₂) :
    ∃ M : ℝ, ∀ n, ∫ r in (0 : ℝ)..P.horizon,
      statePenaltyDensity ω' G (seq.penalty n) (seq.path n) r ≤ M := by
  have hT : 0 ≤ P.horizon := P.horizon_pos.le
  have hGxc : Continuous (fun p : ℝ × E => Gx p.1 p.2) :=
    continuous_iff_continuousAt.2 fun p => (hGx.hasFDerivAt p.1 p.2).continuousAt
  obtain ⟨c₀, ρ, hc₀, hρ, hND'⟩ := exists_uniform_nondegeneracy hGxc hT
    γL.continuousOn_value hND
  obtain ⟨R₀, hR₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := P.horizon)).exists_bound_of_continuousOn
    γL.continuousOn_value
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hpath (min ρ 1) (lt_min hρ one_pos))
  have hshift : ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) P.horizon,
      dist (((seq.shift N).path n).value t) (γL.value t) < ε := fun ε hε =>
    (tendsto_add_atTop_nat N).eventually (hpath ε hε)
  obtain ⟨M', hM'⟩ := exists_massBound_of_uniformNondegenerate hD hω hG hGx (seq.shift N) γL
    hshift hΦ₀c hΦ₁c (R := |R₀| + 1) (c₀ := c₀) (W₂ := W₂)
    (fun n t ht => by
      have h1 := hN (n + N) (Nat.le_add_left N n) t ht
      have h2 := (hR₀ t ht).trans (le_abs_self R₀)
      have h3 : ‖((seq.shift N).path n).value t‖ ≤ ‖γL.value t‖ + dist (((seq.shift N).path
          n).value t)
          (γL.value t) := by
        rw [dist_eq_norm]
        simpa using norm_le_norm_add_norm_sub' ((seq.shift N).path n |>.value t) (γL.value t)
      have h4 : dist (((seq.shift N).path n).value t) (γL.value t) < 1 := h1.trans_le (min_le_right
          _ _)
      linarith)
    hc₀ (fun n t ht => hND' t ht _ (by
      have h1 := hN (n + N) (Nat.le_add_left N n) t ht
      exact (h1.trans_le (min_le_left _ _)).le.trans (by
        have := min_le_left ρ 1
        linarith [lt_min hρ one_pos])))
    (fun n => hW₂ (n + N))
  refine ⟨max M' (∑ k ∈ Finset.range N, |∫ r in (0 : ℝ)..P.horizon,
      statePenaltyDensity ω' G (seq.penalty k) (seq.path k) r|), fun n => ?_⟩
  by_cases hn : n < N
  · refine le_max_of_le_right ?_
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun k => |∫ r in (0 : ℝ)..P.horizon,
      statePenaltyDensity ω' G (seq.penalty k) (seq.path k) r|) (fun k _ => abs_nonneg _)
      (Finset.mem_range.2 hn))
  · refine le_max_of_le_left ?_
    have := hM' (n - N)
    simpa [PenalisedMinimiserSequence.shift, Nat.sub_add_cancel (not_lt.1 hn)] using this

/-- **The `j → ∞` limit for an active state constraint, with the nondegeneracy hypothesis in place
of a multiplier-mass bound.**  This is `exists_stateMultiplier_limit_of_penalisedMinimisers` with
the uniform bound on the multiplier masses discharged by the boundary perturbation
`h = ∇G/|∇G|²` (`exists_massBound_of_nondegenerate`): the only new hypotheses are
`‖γ_n'‖_{L²}² ≤ W₂` (the tube `B(ε)`) and `∇G(t, γL t) ≠ 0` along the limit path (Assumption 11.3.8,
`ConstraintNondegenerate`).  Assumption 11.4.1 (`EndpointInterior`) enters the conclusion
`PenalisedMultiplierLimit`: the limit multiplier is constant near both endpoints.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemma 11.3.5,
Assumptions 11.3.8 and 11.4.1, (11.6.6), (11.6.11), (11.6.15)-(11.6.16). -/
theorem exists_stateMultiplier_limit_of_nondegenerate
    {L : ℝ → E → E → ℝ} {Lx Lv : ℝ → E → E → E →L[ℝ] ℝ}
    (hD : IsCaratheodoryC1 P.horizon L Lx Lv) {ω ω' : ℝ → ℝ}
    (hω : StatePenaltyProfile ω ω') {G : ℝ → E → ℝ} {Gx : ℝ → E → E →L[ℝ] ℝ}
    (hG : StateConstraintRegularity G Gx) (hGc : Continuous (fun p : ℝ × E => G p.1 p.2))
    {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)} (hGx : StateGradientRegularity Gx Gxd)
    {Φ₀ : E → ℝ} {Φ₁ : E × E → ℝ} (seq : PenalisedMinimiserSequence P L G ω Φ₀ Φ₁)
    (γL : VelocityTrajectory P)
    (hpath : ∀ ε > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) P.horizon,
      dist ((seq.path n).value t) (γL.value t) < ε)
    (hLx : Tendsto (fun n => ∫ r in (0 : ℝ)..P.horizon,
      ‖Lx r ((seq.path n).value r) ((seq.path n).velocity r)
        - Lx r (γL.value r) (γL.velocity r)‖) atTop (𝓝 0))
    (hGd : Tendsto (fun n => ∫ r in (0 : ℝ)..P.horizon,
      ‖Gxd r ((seq.path n).value r) (1, (seq.path n).velocity r)
        - Gxd r (γL.value r) (1, γL.velocity r)‖) atTop (𝓝 0))
    (hLv : ∀ᵐ t ∂(timeMeasure P.horizon), Tendsto
      (fun n => Lv t ((seq.path n).value t) ((seq.path n).velocity t)) atTop
      (𝓝 (Lv t (γL.value t) (γL.velocity t))))
    (hΦ₀c : ContinuousAt (fderiv ℝ Φ₀) (γL.value 0))
    (hΦ₁c : ContinuousAt (fderiv ℝ Φ₁) (γL.value 0, γL.value P.horizon))
    (hND : ∀ t ∈ Icc (0 : ℝ) P.horizon, Gx t (γL.value t) ≠ 0) {W₂ : ℝ}
    (hW₂ : ∀ n, ∫ r in (0 : ℝ)..P.horizon, ‖(seq.path n).velocity r‖ ^ 2 ≤ W₂) :
    ∃ M : ℝ, PenalisedMultiplierLimit Lx Lv ω' G Gx Gxd seq γL M := by
  obtain ⟨M, hM⟩ := exists_massBound_of_nondegenerate hD hω hG hGx seq γL hpath hΦ₀c hΦ₁c hND hW₂
  exact ⟨M, exists_stateMultiplier_limit_of_penalisedMinimisers hD hω hG hGc hGx seq γL hpath hLx
    hGd hLv hΦ₀c hΦ₁c hM⟩

end Final

section ProblemBridge

variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] {P : Problem E V W}

/-- The state constraint `G(t,y)` of a problem extended to all `t ∈ ℝ` by clamping time to the
horizon: the form `G : ℝ → E → ℝ` used by the velocity-carrier theorems. -/
noncomputable def Problem.clampedStateConstraint (P : Problem E V W) (t : ℝ) (y : E) : ℝ :=
  P.stateConstraint (Set.projIcc 0 P.horizon P.horizon_pos.le t) y

/-- The state covector `∇G(t,y)` of a problem with smooth data, extended to all `t ∈ ℝ` by clamping
time to the horizon. -/
noncomputable def Problem.clampedStateConstraintDerivative (P : Problem E V W) (D : P.SmoothData)
    (t : ℝ) (y : E) : E →L[ℝ] ℝ :=
  D.stateConstraintDerivative (Set.projIcc 0 P.horizon P.horizon_pos.le t) y

omit [FiniteDimensional ℝ E] in
/-- The clamped state covector is the state derivative of the clamped state constraint. -/
theorem Problem.hasFDerivAt_clampedStateConstraint (P : Problem E V W) (D : P.SmoothData)
    (t : ℝ) (y : E) :
    HasFDerivAt (P.clampedStateConstraint t) (P.clampedStateConstraintDerivative D t y) y :=
  D.stateConstraint_hasFDerivAt _ y

omit [FiniteDimensional ℝ E] in
/-- **Assumption 11.4.1 in the form used by the velocity-carrier limit theorem.**  If the problem
satisfies `EndpointInterior` along a trajectory `x` that is the path of the velocity trajectory
`γL`, then the (clamped) state constraint is strictly slack along `γL` on `[0,δ) ∪ (T-δ,T]`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.4.1. -/
theorem Problem.EndpointInterior.exists_slack_collar {x : P.Trajectory}
    (γL : VelocityTrajectory P) (hx : ∀ t : P.Time, x t = γL.value t)
    (h : P.EndpointInterior x) :
    ∃ δ : ℝ, 0 < δ ∧ δ < P.horizon ∧ ∀ t ∈ Icc (0 : ℝ) P.horizon,
      (t < δ ∨ P.horizon - δ < t) → P.clampedStateConstraint t (γL.value t) < 0 := by
  obtain ⟨δ, hδ, hδT, hslack⟩ := h
  refine ⟨δ, hδ, hδT, fun t ht hcollar => ?_⟩
  have := hslack ⟨t, ht⟩ hcollar
  rw [hx] at this
  simpa [Problem.clampedStateConstraint, Set.projIcc_of_mem _ ht] using this

omit [FiniteDimensional ℝ E] in
/-- The clamped state constraint is jointly continuous. -/
theorem Problem.continuous_clampedStateConstraint (P : Problem E V W) :
    Continuous (fun p : ℝ × E => P.clampedStateConstraint p.1 p.2) := by
  have hproj : Continuous (fun t : ℝ => Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le t) :=
    continuous_projIcc
  exact P.stateConstraint_continuous.comp ((hproj.comp continuous_fst).prodMk continuous_snd)

/-- **Assumption 11.4.1 is stable under uniform perturbation of the path.**  If the reference
trajectory `x₀` satisfies `EndpointInterior`, there are `δ, η > 0` such that every velocity
trajectory `η`-uniformly close to `x₀` has a strictly slack state constraint on the collar
`[0,δ) ∪ (T-δ,T]`: this is the passage from the reference `φ₀` to the `ε`-minimisers `φ̃_ε` for
small `ε` in the book ("if `ε` is sufficiently small, `G(t, φ̃_ε(t)) < 0` on `(0,δ) ∪ (t₁-δ,t₁)`").

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.4.1 and §11.6. -/
theorem Problem.EndpointInterior.slack_collar_of_close {x₀ : P.Trajectory}
    (h : P.EndpointInterior x₀) :
    ∃ δ η : ℝ, 0 < δ ∧ δ < P.horizon ∧ 0 < η ∧ ∀ γ : VelocityTrajectory P,
      (∀ t : P.Time, dist (γ.value t) (x₀ t) < η) → ∀ t ∈ Icc (0 : ℝ) P.horizon,
        (t < δ ∨ P.horizon - δ < t) → P.clampedStateConstraint t (γ.value t) < 0 := by
  obtain ⟨δ₀, hδ₀, hδ₀T, hslack⟩ := h
  set y : ℝ → E := fun t => x₀ (Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le t) with hy
  have hyc : Continuous y := x₀.continuous.comp continuous_projIcc
  have hA : IsCompact (Icc (0 : ℝ) (δ₀ / 2) ∪ Icc (P.horizon - δ₀ / 2) P.horizon) :=
    isCompact_Icc.union isCompact_Icc
  have hAsub : ∀ r ∈ Icc (0 : ℝ) (δ₀ / 2) ∪ Icc (P.horizon - δ₀ / 2) P.horizon,
      r ∈ Icc (0 : ℝ) P.horizon ∧ (r < δ₀ ∨ P.horizon - δ₀ < r) := by
    intro r hr
    rcases hr with hr | hr
    · exact ⟨⟨hr.1, by linarith [hr.2]⟩, Or.inl (by linarith [hr.2])⟩
    · exact ⟨⟨by linarith [hr.1], hr.2⟩, Or.inr (by linarith [hr.1])⟩
  obtain ⟨η, hη, hηG⟩ := exists_slack_radius P.continuous_clampedStateConstraint hA hyc.continuousOn
    (fun r hr => by
      obtain ⟨hrI, hrc⟩ := hAsub r hr
      have := hslack ⟨r, hrI⟩ hrc
      simpa [Problem.clampedStateConstraint, hy, Set.projIcc_of_mem _ hrI] using this)
  refine ⟨δ₀ / 2, η, by positivity, by linarith, hη, fun γ hγ t ht hcollar => ?_⟩
  have htA : t ∈ Icc (0 : ℝ) (δ₀ / 2) ∪ Icc (P.horizon - δ₀ / 2) P.horizon := by
    rcases hcollar with h1 | h1
    · exact Or.inl ⟨ht.1, h1.le⟩
    · exact Or.inr ⟨h1.le, ht.2⟩
  refine hηG t htA (γ.value t) ?_
  have := hγ ⟨t, ht⟩
  simpa [hy, Set.projIcc_of_mem _ ht] using this

omit [FiniteDimensional ℝ E] in
/-- **Assumption 11.3.8 in the form used by the velocity-carrier limit theorem.**  If the problem
satisfies `ConstraintNondegenerate` along a trajectory `x` that is the path of the velocity
trajectory `γL`, then the (clamped) state covector `∇G(t, γL t)` does not vanish on `[0,T]`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.3.8. -/
theorem Problem.ConstraintNondegenerate.ne_zero_clamped {D : P.SmoothData} {x : P.Time → E}
    (γL : VelocityTrajectory P) (hx : ∀ t : P.Time, x t = γL.value t)
    (h : P.ConstraintNondegenerate D x) :
    ∀ t ∈ Icc (0 : ℝ) P.horizon, P.clampedStateConstraintDerivative D t (γL.value t) ≠ 0 := by
  obtain ⟨ε₂, hε₂, hne⟩ := h
  intro t ht
  have := hne ⟨t, ht⟩ (x ⟨t, ht⟩) (by simpa using hε₂)
  rw [stateConstraintNormal, hx] at this
  simpa [Problem.clampedStateConstraintDerivative, Set.projIcc_of_mem _ ht] using this

end ProblemBridge

end OptimalControl.BoundedState
