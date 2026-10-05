/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.K3MomentumRegularity
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.ProjIcc

/-!
# Weak Euler–Lagrange regularity from actual stationarity

Vanishing first variation implies differentiability of the momentum; its
regularity is a conclusion rather than a supplied derivative hypothesis.
At the endpoints the correct consequence is a within-interval derivative.
Two-sided derivatives are obtained at all interior times.
-/

@[expose] public section

namespace WeakEulerLagrange

open Set Filter MeasureTheory
open scoped Interval Topology

/-- A continuous scalar function orthogonal to the derivatives of every C1
endpoint-zero test curve is constant on the full closed interval. The test is
the primitive of the function minus its average; its variance must vanish. -/
theorem eq_const_of_integral_mul_deriv_eq_zero
    {r : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hr : Continuous r)
    (hzero : ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → φ a = 0 → φ b = 0 →
      ∫ t in a..b, r t * deriv φ t = 0) :
    ∀ t ∈ Icc a b, r t = r a := by
  let m : ℝ := (b - a)⁻¹ * ∫ t in a..b, r t
  let ψ : ℝ → ℝ := fun t => r t - m
  let φ : ℝ → ℝ := fun t => ∫ s in a..t, ψ s
  have hψ : Continuous ψ := hr.sub continuous_const
  have hφd : ∀ t, HasDerivAt φ (ψ t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right (hψ.intervalIntegrable a t)
      hψ.aestronglyMeasurable.stronglyMeasurableAtFilter hψ.continuousAt
  have hφderiv : deriv φ = ψ := funext (fun t => (hφd t).deriv)
  have hφ : ContDiff ℝ 1 φ := contDiff_one_iff_deriv.mpr
    ⟨fun t => (hφd t).differentiableAt, hφderiv ▸ hψ⟩
  have hφa : φ a = 0 := by simp [φ]
  have hφb : φ b = 0 := by
    change (∫ t in a..b, r t - m) = 0
    rw [intervalIntegral.integral_sub (hr.intervalIntegrable a b) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    dsimp [m]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  have hψint : (∫ t in a..b, ψ t) = 0 := hφb
  have horth : (∫ t in a..b, r t * ψ t) = 0 := by
    simpa only [hφderiv] using hzero φ hφ hφa hφb
  have hvariance : (∫ t in a..b, (ψ t) ^ 2) = 0 := by
    calc
      (∫ t in a..b, (ψ t) ^ 2) =
          ∫ t in a..b, (r t * ψ t - m * ψ t) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp [ψ]
        ring
      _ = (∫ t in a..b, r t * ψ t) - m * ∫ t in a..b, ψ t := by
        have hi₁ : IntervalIntegrable (fun t => r t * ψ t) volume a b :=
          (hr.mul hψ).intervalIntegrable a b
        have hi₂ : IntervalIntegrable (fun t => m * ψ t) volume a b :=
          (continuous_const.mul hψ).intervalIntegrable a b
        rw [intervalIntegral.integral_sub hi₁ hi₂, intervalIntegral.integral_const_mul]
      _ = 0 := by rw [horth, hψint]; ring
  have hpoint : ∀ t ∈ Icc a b, ψ t = 0 := by
    intro t ht
    by_contra hne
    have hpos := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      hab (f := fun _ : ℝ => (0 : ℝ)) (g := fun t => (ψ t) ^ 2)
      continuousOn_const (hψ.pow 2).continuousOn
      (fun s _ => sq_nonneg (ψ s)) ⟨t, ht, sq_pos_of_ne_zero hne⟩
    simp only [intervalIntegral.integral_zero, hvariance, lt_self_iff_false] at hpos
  intro t ht
  have ht' : r t = m := sub_eq_zero.mp (hpoint t ht)
  have ha' : r a = m := sub_eq_zero.mp (hpoint a (left_mem_Icc.mpr hab.le))
  exact ht'.trans ha'.symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The weak momentum equation implies an actual integral representation in
the continuous dual. Scalar test directions suffice; no finite-dimensional or
inner-product structure is needed. -/
theorem momentum_eq_add_integral_of_stationary
    {p q : ℝ → E →L[ℝ] ℝ} {a b : ℝ} (hab : a < b)
    (hp : Continuous p) (hq : Continuous q)
    (hstationary : ∀ η : ℝ → E, ContDiff ℝ 1 η → η a = 0 → η b = 0 →
      ∫ t in a..b, q t (η t) + p t (deriv η t) = 0) :
    ∀ t ∈ Icc a b, p t = p a + ∫ s in a..t, q s := by
  let Q : ℝ → E →L[ℝ] ℝ := fun t => ∫ s in a..t, q s
  have hQd : ∀ t, HasDerivAt Q (q t) t := by
    intro t
    exact intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable a t)
      hq.aestronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt
  have hQc : Continuous Q := continuous_iff_continuousAt.mpr
    (fun t => (hQd t).continuousAt)
  have hQa : Q a = 0 := by simp [Q]
  have hresidual : ∀ e : E, ∀ t ∈ Icc a b,
      p t e - Q t e = p a e - Q a e := by
    intro e
    apply eq_const_of_integral_mul_deriv_eq_zero hab
      ((hp.clm_apply continuous_const).sub (hQc.clm_apply continuous_const))
    intro φ hφ hφa hφb
    have hφdiff : Differentiable ℝ φ := hφ.differentiable (by norm_num)
    have hη := hstationary (fun t => φ t • e) (hφ.smul_const e)
      (by rw [hφa, zero_smul]) (by rw [hφb, zero_smul])
    have hpφ : IntervalIntegrable (fun t => p t e * deriv φ t) volume a b := by
      have hc : Continuous (fun t => p t e * deriv φ t) :=
        (hp.clm_apply continuous_const).mul (hφ.continuous_deriv (by norm_num))
      exact hc.intervalIntegrable a b
    have hqφ : IntervalIntegrable (fun t => q t e * φ t) volume a b :=
      ((hq.clm_apply continuous_const).mul hφ.continuous).intervalIntegrable a b
    have hQφ : IntervalIntegrable (fun t => Q t e * deriv φ t) volume a b := by
      have hc : Continuous (fun t => Q t e * deriv φ t) :=
        (hQc.clm_apply continuous_const).mul (hφ.continuous_deriv (by norm_num))
      exact hc.intervalIntegrable a b
    have hstation : (∫ t in a..b, q t e * φ t) +
        (∫ t in a..b, p t e * deriv φ t) = 0 := by
      rw [← intervalIntegral.integral_add hqφ hpφ]
      convert hη using 1
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only
      rw [deriv_smul_const hφdiff.differentiableAt e, map_smul, map_smul]
      simp only [smul_eq_mul]
      ring
    have hQe : ∀ t, HasDerivAt (fun s => Q s e) (q t e) t := by
      intro t
      simpa using (hQd t).clm_apply (hasDerivAt_const t e)
    have hibp := integral_deriv_mul_eq_neg_integral_mul_deriv
      (fun t (_ : t ∈ uIcc a b) => hφdiff.differentiableAt.hasDerivAt)
      (fun t (_ : t ∈ uIcc a b) => hQe t)
      ((hφ.continuous_deriv (by norm_num)).intervalIntegrable a b)
      ((hq.clm_apply continuous_const).intervalIntegrable a b) hφa hφb
    have hibp' : (∫ t in a..b, Q t e * deriv φ t) =
        -(∫ t in a..b, q t e * φ t) := by
      simpa only [mul_comm] using hibp
    calc
      (∫ t in a..b, (p t e - Q t e) * deriv φ t) =
          (∫ t in a..b, p t e * deriv φ t) -
            (∫ t in a..b, Q t e * deriv φ t) := by
        rw [← intervalIntegral.integral_sub hpφ hQφ]
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = 0 := by rw [hibp']; linarith
  intro t ht
  ext e
  have h := hresidual e t ht
  rw [hQa, zero_apply] at h
  change p t e = p a e + Q t e
  linarith

/-- Actual momentum differentiability on the closed horizon, with the correct
within-interval semantics at its endpoints. -/
theorem momentum_hasDerivWithinAt_of_stationary
    {p q : ℝ → E →L[ℝ] ℝ} {a b : ℝ} (hab : a < b)
    (hp : Continuous p) (hq : Continuous q)
    (hstationary : ∀ η : ℝ → E, ContDiff ℝ 1 η → η a = 0 → η b = 0 →
      ∫ t in a..b, q t (η t) + p t (deriv η t) = 0) :
    ∀ t ∈ Icc a b, HasDerivWithinAt p (q t) (Icc a b) t := by
  have heq := momentum_eq_add_integral_of_stationary hab hp hq hstationary
  intro t ht
  have hd := intervalIntegral.integral_hasDerivAt_right (hq.intervalIntegrable a t)
    hq.aestronglyMeasurable.stronglyMeasurableAtFilter hq.continuousAt
  exact (hd.const_add (p a)).hasDerivWithinAt.congr_of_mem
    (fun s hs => heq s hs) ht

/-- Two-sided momentum differentiability follows at every interior time. -/
theorem momentum_hasDerivAt_of_stationary
    {p q : ℝ → E →L[ℝ] ℝ} {a b : ℝ} (hab : a < b)
    (hp : Continuous p) (hq : Continuous q)
    (hstationary : ∀ η : ℝ → E, ContDiff ℝ 1 η → η a = 0 → η b = 0 →
      ∫ t in a..b, q t (η t) + p t (deriv η t) = 0) :
    ∀ t ∈ Ioo a b, HasDerivAt p (q t) t := by
  intro t ht
  exact (momentum_hasDerivWithinAt_of_stationary hab hp hq hstationary
    t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- The weak theorem needs continuity only on the actual horizon. Continuous
clamped extensions are used to build globally C1 admissible test curves. -/
theorem momentum_hasDerivWithinAt_of_stationary_continuousOn
    {p q : ℝ → E →L[ℝ] ℝ} {a b : ℝ} (hab : a < b)
    (hp : ContinuousOn p (Icc a b)) (hq : ContinuousOn q (Icc a b))
    (hstationary : ∀ η : ℝ → E, ContDiff ℝ 1 η → η a = 0 → η b = 0 →
      ∫ t in a..b, q t (η t) + p t (deriv η t) = 0) :
    ∀ t ∈ Icc a b, HasDerivWithinAt p (q t) (Icc a b) t := by
  let P : ℝ → E →L[ℝ] ℝ := fun t => p (projIcc a b hab.le t)
  let Q : ℝ → E →L[ℝ] ℝ := fun t => q (projIcc a b hab.le t)
  have hPc : Continuous P := hp.domRestrict.comp continuous_projIcc
  have hQc : Continuous Q := hq.domRestrict.comp continuous_projIcc
  have hPeq : EqOn P p (Icc a b) := by
    intro t ht
    simp only [P, projIcc_of_mem hab.le ht]
  have hQeq : EqOn Q q (Icc a b) := by
    intro t ht
    simp only [Q, projIcc_of_mem hab.le ht]
  have hzero : ∀ η : ℝ → E, ContDiff ℝ 1 η → η a = 0 → η b = 0 →
      ∫ t in a..b, Q t (η t) + P t (deriv η t) = 0 := by
    intro η hη hηa hηb
    rw [← hstationary η hη hηa hηb]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab.le] at ht
    change Q t (η t) + P t (deriv η t) = q t (η t) + p t (deriv η t)
    rw [hPeq ht, hQeq ht]
  intro t ht
  have hd := momentum_hasDerivWithinAt_of_stationary hab hPc hQc hzero t ht
  rw [hQeq ht] at hd
  exact hd.congr_of_mem (fun s hs => (hPeq hs).symm) ht

/-- Interior two-sided differentiability from horizon-only continuity and
stationarity, including the version needed on a single piecewise C1 arc. -/
theorem momentum_hasDerivAt_of_stationary_continuousOn
    {p q : ℝ → E →L[ℝ] ℝ} {a b : ℝ} (hab : a < b)
    (hp : ContinuousOn p (Icc a b)) (hq : ContinuousOn q (Icc a b))
    (hstationary : ∀ η : ℝ → E, ContDiff ℝ 1 η → η a = 0 → η b = 0 →
      ∫ t in a..b, q t (η t) + p t (deriv η t) = 0) :
    ∀ t ∈ Ioo a b, HasDerivAt p (q t) t := by
  intro t ht
  exact (momentum_hasDerivWithinAt_of_stationary_continuousOn hab hp hq hstationary
    t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-- The actual first variation and primitive C1 data imply weak Euler–Lagrange
regularity. Momentum differentiability is derived, not assumed. -/
theorem eulerLagrange_hasDerivWithinAt_of_firstVariation_zero
    {L : ℝ → E → E → ℝ} {K : E → ℝ} {T : ℝ} {x : ℝ → E}
    (hT : 0 < T) (hL : ContDiff ℝ 1 (uncurryLagrangian L))
    (hx : ContDiff ℝ 1 x)
    (hstationary : ∀ η : ℝ → E, ContDiff ℝ 1 η → η 0 = 0 → η T = 0 →
      firstVariation L K T x η = 0) :
    ∀ t ∈ Icc 0 T,
      HasDerivWithinAt
        (fun s : ℝ => fderiv ℝ (fun v : E => L s (x s) v) (deriv x s))
        (fderiv ℝ (fun y : E => L t y (deriv x t)) (x t)) (Icc 0 T) t := by
  apply momentum_hasDerivWithinAt_of_stationary hT
    (continuous_momentumCovector L x hL hx)
    (continuous_stateCovector L x hL hx)
  intro η hη hη₀ hηT
  simpa only [firstVariation, hηT, map_zero, add_zero] using
    hstationary η hη hη₀ hηT

/-- The actual Euler–Lagrange differential equation at every interior time,
derived from first variation under only C1 Lagrangian and reference data. -/
theorem eulerLagrange_hasDerivAt_of_firstVariation_zero
    {L : ℝ → E → E → ℝ} {K : E → ℝ} {T : ℝ} {x : ℝ → E}
    (hT : 0 < T) (hL : ContDiff ℝ 1 (uncurryLagrangian L))
    (hx : ContDiff ℝ 1 x)
    (hstationary : ∀ η : ℝ → E, ContDiff ℝ 1 η → η 0 = 0 → η T = 0 →
      firstVariation L K T x η = 0) :
    ∀ t ∈ Ioo 0 T,
      HasDerivAt
        (fun s : ℝ => fderiv ℝ (fun v : E => L s (x s) v) (deriv x s))
        (fderiv ℝ (fun y : E => L t y (deriv x t)) (x t)) t := by
  intro t ht
  exact (eulerLagrange_hasDerivWithinAt_of_firstVariation_zero hT hL hx hstationary
    t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end WeakEulerLagrange

end
