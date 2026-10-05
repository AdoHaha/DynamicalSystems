/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Abel

/-!
# Short-interval trajectory displacement for needle variations

This file proves the analytic estimate which distinguishes the actual needle
trajectory from the frozen-reference impulse. It assumes integral equations,
uniform local Lipschitz bounds, and continuity of the trajectories. It does not
assume differentiability with respect to a needle parameter, a trajectory
sensitivity estimate, a Hamiltonian inequality, a costate, or optimality.

On an interval of length `h`, the maximum displacement `D` satisfies
`D ≤ h * (M + L * D)`. When `L * h ≤ 1/2`, elementary absorption gives
`D ≤ 2 * M * h`. The error relative to the frozen impulse is consequently at
most `2 * L * M * h^2`. No general ODE parameter-dependence theorem or
Gronwall inequality is needed on this shrinking interval.

Existence of the integral solutions is a separate ODE obligation. Genuine
step needles are generally not admissible under an everywhere-classical
`HasDerivAt` definition: their trajectories have corners at the switching
times. Integral or piecewise-classical admissibility is needed by the PMP
caller. These estimates themselves do not change an admissibility predicate.

The final asymptotic theorem takes the frozen-impulse limit already proved by
`needleImpulseFirstOrder` in `NeedleVariation.lean` and upgrades it to the
actual trajectory displacement limit.

The argument is the standard short-time needle estimate in Berkovitz and
Medhin, *Nonlinear Optimal Control Theory*, CRC Press, 2012, Chapter 7.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Interval Topology NNReal

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Absorption on a short interval for a continuous solution of a perturbed
integral equation. The forcing is bounded by `M`; the residual is bounded by
`L` times the displacement itself. -/
theorem norm_le_two_mul_of_integral_equation
    {e g r : ℝ → X} {a b L M : ℝ}
    (hab : a ≤ b) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hsmall : L * (b - a) ≤ 1 / 2)
    (he : ContinuousOn e (Icc a b))
    (heq : ∀ t ∈ Icc a b, e t = ∫ s in a..t, g s + r s)
    (hg : ∀ t ∈ Icc a b, ‖g t‖ ≤ M)
    (hr : ∀ t ∈ Icc a b, ‖r t‖ ≤ L * ‖e t‖) :
    ∀ t ∈ Icc a b, ‖e t‖ ≤ 2 * M * (b - a) := by
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hab) he.norm
  have hbound : ∀ s ∈ Ι a c, ‖g s + r s‖ ≤ M + L * ‖e c‖ := by
    intro s hs
    rw [uIoc_of_le hc.1] at hs
    have hsab : s ∈ Icc a b := ⟨hs.1.le, hs.2.trans hc.2⟩
    exact (norm_add_le _ _).trans (add_le_add (hg s hsab)
      ((hr s hsab).trans (mul_le_mul_of_nonneg_left (hmax hsab) hL)))
  have hmax_bound : ‖e c‖ ≤ (M + L * ‖e c‖) * (b - a) := by
    calc
      ‖e c‖ = ‖∫ s in a..c, g s + r s‖ := congrArg norm (heq c hc)
      _ ≤ (M + L * ‖e c‖) * |c - a| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
      _ = (M + L * ‖e c‖) * (c - a) := by
        rw [abs_of_nonneg (sub_nonneg.mpr hc.1)]
      _ ≤ (M + L * ‖e c‖) * (b - a) := by
        exact mul_le_mul_of_nonneg_left (sub_le_sub_right hc.2 a) (by positivity)
  have habsorb : L * (b - a) * ‖e c‖ ≤ (1 / 2) * ‖e c‖ :=
    mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
  have hmax_final : ‖e c‖ ≤ 2 * M * (b - a) := by
    nlinarith
  exact fun t ht => (hmax ht).trans hmax_final

/-- The actual displacement differs from its frozen forcing integral by a
quadratic remainder. Integrability is recorded explicitly before splitting
the integral. -/
theorem norm_sub_integral_le_quadratic_of_integral_equation
    {e g r : ℝ → X} {a b L M : ℝ}
    (hab : a ≤ b) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hsmall : L * (b - a) ≤ 1 / 2)
    (he : ContinuousOn e (Icc a b))
    (heq : ∀ t ∈ Icc a b, e t = ∫ s in a..t, g s + r s)
    (hg : ∀ t ∈ Icc a b, ‖g t‖ ≤ M)
    (hr : ∀ t ∈ Icc a b, ‖r t‖ ≤ L * ‖e t‖)
    (hgi : IntervalIntegrable g volume a b)
    (hri : IntervalIntegrable r volume a b) :
    ‖e b - ∫ s in a..b, g s‖ ≤ 2 * L * M * (b - a) ^ 2 := by
  have he_bound := norm_le_two_mul_of_integral_equation
    hab hL hM hsmall he heq hg hr
  have hr_bound : ∀ s ∈ Ι a b, ‖r s‖ ≤ 2 * L * M * (b - a) := by
    intro s hs
    rw [uIoc_of_le hab] at hs
    have hsab : s ∈ Icc a b := Ioc_subset_Icc_self hs
    calc
      ‖r s‖ ≤ L * ‖e s‖ := hr s hsab
      _ ≤ L * (2 * M * (b - a)) :=
        mul_le_mul_of_nonneg_left (he_bound s hsab) hL
      _ = 2 * L * M * (b - a) := by ring
  have hrem : e b - (∫ s in a..b, g s) = ∫ s in a..b, r s := by
    rw [heq b (right_mem_Icc.mpr hab), intervalIntegral.integral_add hgi hri]
    abel
  rw [hrem]
  calc
    ‖∫ s in a..b, r s‖ ≤ (2 * L * M * (b - a)) * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hr_bound
    _ = 2 * L * M * (b - a) ^ 2 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      ring

/-- Trajectory form of the short-interval estimate. `F` is the test-control
vector field and `f₀` is the reference velocity. The two trajectories have
the same state at the start of the needle. All analytic premises are primitive
integral-solution, continuity, integrability, forcing, and Lipschitz conditions.

The Lipschitz hypothesis is needed only on the two actual trajectories; a
uniform Lipschitz-on-a-tube assumption gives this pointwise bound immediately.
-/
theorem needle_displacement_bound_of_integral_eq
    {x y : ℝ → X} {F : ℝ → X → X} {f₀ : ℝ → X} {a b L M : ℝ}
    (hab : a ≤ b) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hsmall : L * (b - a) ≤ 1 / 2)
    (hxcont : ContinuousOn x (Icc a b)) (hycont : ContinuousOn y (Icc a b))
    (hstart : x a = y a)
    (hx : ∀ t ∈ Icc a b, x t = x a + ∫ s in a..t, F s (x s))
    (hy : ∀ t ∈ Icc a b, y t = y a + ∫ s in a..t, f₀ s)
    (hxi : IntervalIntegrable (fun s => F s (x s)) volume a b)
    (hyi : IntervalIntegrable (fun s => F s (y s)) volume a b)
    (hf₀i : IntervalIntegrable f₀ volume a b)
    (hforcing : ∀ t ∈ Icc a b, ‖F t (y t) - f₀ t‖ ≤ M)
    (hlip : ∀ t ∈ Icc a b, ‖F t (x t) - F t (y t)‖ ≤ L * ‖x t - y t‖) :
    (∀ t ∈ Icc a b, ‖x t - y t‖ ≤ 2 * M * (b - a)) ∧
      ‖x b - y b - ∫ s in a..b, (F s (y s) - f₀ s)‖ ≤
        2 * L * M * (b - a) ^ 2 := by
  let e : ℝ → X := fun t => x t - y t
  let g : ℝ → X := fun t => F t (y t) - f₀ t
  let r : ℝ → X := fun t => F t (x t) - F t (y t)
  have he : ContinuousOn e (Icc a b) := hxcont.sub hycont
  have heq : ∀ t ∈ Icc a b, e t = ∫ s in a..t, g s + r s := by
    intro t ht
    have hsub : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl ht.2
    have hxi' := hxi.mono_set hsub
    have hf₀i' := hf₀i.mono_set hsub
    calc
      e t = (x a + ∫ s in a..t, F s (x s)) -
          (y a + ∫ s in a..t, f₀ s) := by
        change x t - y t = _
        rw [hx t ht, hy t ht]
      _ = (∫ s in a..t, F s (x s)) - ∫ s in a..t, f₀ s := by
        rw [hstart]
        abel
      _ = ∫ s in a..t, (F s (x s) - f₀ s) :=
        (intervalIntegral.integral_sub hxi' hf₀i').symm
      _ = ∫ s in a..t, g s + r s := by
        congr 1
        funext s
        dsimp [g, r]
        abel
  exact ⟨norm_le_two_mul_of_integral_equation hab hL hM hsmall he heq hforcing hlip,
    norm_sub_integral_le_quadratic_of_integral_equation hab hL hM hsmall he heq
      hforcing hlip (hyi.sub hf₀i) (hxi.sub hyi)⟩

/-- A quadratic difference preserves a one-sided first-order expansion.
This is an analytic transfer lemma, with no optimal-control hypotheses. -/
theorem tendsto_scaled_sub_of_quadratic_remainder
    {d I : ℝ → X} {v : X} {C : ℝ}
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖d ε - I ε‖ ≤ C * ε ^ 2)
    (himpulse : Tendsto (fun ε : ℝ => ε⁻¹ • (I ε - ε • v))
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ε⁻¹ • (d ε - ε • v)) (𝓝[>] 0) (𝓝 0) := by
  have hnorm_bound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖ε⁻¹ • (d ε - I ε)‖ ≤ C * ε := by
    filter_upwards [hbound, self_mem_nhdsWithin] with ε hε hpos
    have hεpos : 0 < ε := hpos
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hεpos]
    calc
      ε⁻¹ * ‖d ε - I ε‖ ≤ ε⁻¹ * (C * ε ^ 2) :=
        mul_le_mul_of_nonneg_left hε (inv_nonneg.mpr hεpos.le)
      _ = C * ε := by field_simp [ne_of_gt hεpos]
  have hlinear : Tendsto (fun ε : ℝ => C * ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
  have hnorm : Tendsto (fun ε : ℝ => ‖ε⁻¹ • (d ε - I ε)‖)
      (𝓝[>] 0) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hnorm_bound hlinear
  have herror : Tendsto (fun ε : ℝ => ε⁻¹ • (d ε - I ε))
      (𝓝[>] 0) (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  simpa only [← smul_add, sub_add_sub_cancel, add_zero] using herror.add himpulse

/-- Upgrade the frozen needle impulse to the actual displacement. The
quadratic error bound is supplied by `needle_displacement_bound_of_integral_eq`
with `a = τ - ε` and `b = τ`; `himpulse` is the conclusion of the existing
`needleImpulseFirstOrder` theorem. -/
theorem needle_displacement_firstOrder_of_impulse_firstOrder
    (d : ℝ → X) (g : ℝ → X) (τ : ℝ) (C : ℝ)
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ‖d ε - ∫ t in (τ - ε)..τ, g t‖ ≤ C * ε ^ 2)
    (himpulse : Tendsto (fun ε : ℝ =>
        ε⁻¹ • ((∫ t in (τ - ε)..τ, g t) - ε • g τ)) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ε⁻¹ • (d ε - ε • g τ)) (𝓝[>] 0) (𝓝 0) :=
  tendsto_scaled_sub_of_quadratic_remainder hbound himpulse

/-- Primitive data for one needle interval. This records integral solutions
and local regularity, without assuming any displacement bound or sensitivity
with respect to the interval width. -/
structure NeedleIntervalData (x y : ℝ → X) (F : ℝ → X → X) (f₀ : ℝ → X)
    (a b L M : ℝ) : Prop where
  perturbed_continuous : ContinuousOn x (Icc a b)
  reference_continuous : ContinuousOn y (Icc a b)
  initial_eq : x a = y a
  perturbed_integral_eq : ∀ t ∈ Icc a b, x t = x a + ∫ s in a..t, F s (x s)
  reference_integral_eq : ∀ t ∈ Icc a b, y t = y a + ∫ s in a..t, f₀ s
  perturbed_integrable : IntervalIntegrable (fun s => F s (x s)) volume a b
  frozen_integrable : IntervalIntegrable (fun s => F s (y s)) volume a b
  reference_integrable : IntervalIntegrable f₀ volume a b
  forcing_bound : ∀ t ∈ Icc a b, ‖F t (y t) - f₀ t‖ ≤ M
  lipschitz_bound : ∀ t ∈ Icc a b,
    ‖F t (x t) - F t (y t)‖ ≤ L * ‖x t - y t‖

/-- The true needle displacement has the same first-order jump as the
frozen-reference impulse. In a control problem use
`F t z = f t z v` and `f₀ t = f t (y t) (u₀ t)`.

The family hypothesis is only the existence of integral trajectories with
uniform primitive local bounds. The frozen-impulse limit follows from
`needleImpulseFirstOrder`; no displacement asymptotic is assumed. -/
theorem needle_displacement_firstOrder_of_integral_solutions
    {x : ℝ → ℝ → X} {y : ℝ → X} {F : ℝ → X → X} {f₀ : ℝ → X}
    {τ L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hfamily : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      NeedleIntervalData (x ε) y F f₀ (τ - ε) τ L M)
    (himpulse : Tendsto (fun ε : ℝ => ε⁻¹ •
        ((∫ t in (τ - ε)..τ, (F t (y t) - f₀ t)) - ε • (F τ (y τ) - f₀ τ)))
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ =>
        ε⁻¹ • (x ε τ - y τ - ε • (F τ (y τ) - f₀ τ)))
      (𝓝[>] 0) (𝓝 0) := by
  have hlinear : Tendsto (fun ε : ℝ => L * ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), L * ε < 1 / 2 :=
    hlinear.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  apply tendsto_scaled_sub_of_quadratic_remainder (C := 2 * L * M) _ himpulse
  filter_upwards [hfamily, hsmall, self_mem_nhdsWithin] with ε hε hεsmall hpos
  have hεpos : 0 < ε := hpos
  have hab : τ - ε ≤ τ := by linarith
  have hlength : τ - (τ - ε) = ε := by ring
  have hsmall' : L * (τ - (τ - ε)) ≤ 1 / 2 := by
    rw [hlength]
    exact hεsmall.le
  have h := (needle_displacement_bound_of_integral_eq hab hL hM hsmall'
    hε.perturbed_continuous hε.reference_continuous hε.initial_eq
    hε.perturbed_integral_eq hε.reference_integral_eq hε.perturbed_integrable
    hε.frozen_integrable hε.reference_integrable hε.forcing_bound hε.lipschitz_bound).2
  simpa only [hlength] using h

/-- Once the needle has ended, both trajectories solve the reference ODE.
The short-interval `O(ε)` displacement therefore remains uniformly `O(ε)`
up to the final time. This is a direct application of Mathlib's Gronwall
estimate on a time-dependent tube; only right derivatives are required.

In combination with the shrinking-interval bound, this suffices for the
direct adjoint-pairing proof of the cost expansion. No spatial derivative of
the flow, uniform trajectory sensitivity, or propagator is assumed. -/
theorem needle_displacement_bound_after_spike
    {x y : ℝ → X} {V : ℝ → X → X} {tube : ℝ → Set X}
    {τ T C ε : ℝ} {K : ℝ≥0}
    (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hV : ∀ t ∈ Ico τ T, LipschitzOnWith K (V t) (tube t))
    (hx : ContinuousOn x (Icc τ T))
    (hx' : ∀ t ∈ Ico τ T, HasDerivWithinAt x (V t (x t)) (Ici t) t)
    (hxtube : ∀ t ∈ Ico τ T, x t ∈ tube t)
    (hy : ContinuousOn y (Icc τ T))
    (hy' : ∀ t ∈ Ico τ T, HasDerivWithinAt y (V t (y t)) (Ici t) t)
    (hytube : ∀ t ∈ Ico τ T, y t ∈ tube t)
    (hstart : ‖x τ - y τ‖ ≤ C * ε) :
    ∀ t ∈ Icc τ T, ‖x t - y t‖ ≤ (C * Real.exp (K * (T - τ))) * ε := by
  have hstart' : dist (x τ) (y τ) ≤ C * ε := by
    simpa only [dist_eq_norm] using hstart
  have hgronwall := dist_le_of_trajectories_ODE_of_mem
    hV hx hx' hxtube hy hy' hytube hstart'
  intro t ht
  have hexp : Real.exp (K * (t - τ)) ≤ Real.exp (K * (T - τ)) := by
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 τ) K.coe_nonneg)
  calc
    ‖x t - y t‖ = dist (x t) (y t) := (dist_eq_norm _ _).symm
    _ ≤ (C * ε) * Real.exp (K * (t - τ)) := hgronwall t ht
    _ ≤ (C * ε) * Real.exp (K * (T - τ)) :=
      mul_le_mul_of_nonneg_left hexp (mul_nonneg hC hε)
    _ = (C * Real.exp (K * (T - τ))) * ε := by ring

end
