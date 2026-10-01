/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Estimation.DeadZone
public import DynamicalSystems.AdaptiveControl.BoundedGrowth
public import DynamicalSystems.AdaptiveControl.Direct
public import DynamicalSystems.ParameterAdaptation.Convergence

/-! # Robust direct adaptive control with bounded disturbances

This file formalizes the analytical core of *robust direct adaptive control* with
a bounded disturbance of I. D. Landau, R. Lozano, M'Saad and A. Karimi, *Adaptive
Control: Algorithms, Analysis and Applications*, 2nd ed., Springer 2011,
Section 11.5.2 (Theorem 11.5, printed pp. 390-393, eqs. 11.170-11.194).

The plant is driven by a bounded disturbance `w (t + 1)` with known bound
`|w (t + 1)| ≤ Δ` (eq. 11.175). The a priori filtered tracking error satisfies
`ε⁰(t + 1) = θ̃_C(t)ᵀ φ_C(t) + w(t + 1)` (eq. 11.177), and the robust PAA uses the
dead-zone function `f[ε⁰] = deadZone Δ ε⁰` of eq. 11.180. The key scalar fact
behind the Lyapunov analysis is the residual inequality (eq. 11.181)

`(ε⁰ − w) · f[ε⁰] ≥ f[ε⁰]²`,

which makes the dead-zone update dissipate the parameter-error Lyapunov function.

The growth bound (11.186) relates the weighted regressor norm `x` to the running
maximum of the performance error `e`. Replacing `e` by its dead-zoned version
`deadZone Δ e` shifts the bound by `C₂ · Δ`, because the dead zone differs from the
identity by at most the dead-zone level: `|e| ≤ Δ + |deadZone Δ e|`.

## Main results

* `deadzone_residual_le_sq`: the residual inequality (11.181) of the dead-zone PAA.
* `robust_direct_growth_bound`: the shifted growth bound replacing `e` by
  `deadZone Δ e` (the `Δ`-shifted form of (11.186)).
* `robust_direct_adaptive_stability`: Theorem 11.5 at statement level — the
  regressor is bounded (11.185), the dead-zoned error tends to `0`, and
  `limsup |ε⁰| ≤ Δ` (11.182).
* `robust_direct_lyapunov_bounded`: a non-increasing Lyapunov sequence is bounded
  by its initial value.
* `robust_direct_param_step_tendsto_zero`: the parameter increments of the
  dead-zone PAA tend to `0` (the scalar content of (11.184)).
* `robust_direct_pe_parameter_convergence`: with persistent excitation, a bounded
  regressor, a vanishing dead-zoned prediction error and the PAA step bound, the
  parameter-error norm `θ̃(t)` tends to `0`.
-/

@[expose] public section

open scoped Topology

/-- **Equation (11.181), the residual inequality of the dead-zone PAA.** If the
disturbance is bounded by the dead-zone level, `|w| ≤ Δ`, then the dead-zoned
adaptation error `f[ε⁰] = deadZone Δ e` satisfies

`(deadZone Δ e)² ≤ (e − w) · deadZone Δ e`.

Inside the dead zone the error is zero, so both sides vanish. Outside the dead zone
`deadZone Δ e = e − Δ · sign e` has the sign of `e` and magnitude `|e| − Δ`; since
`|w| ≤ Δ < |e|`, the factor `e − w` has the same sign as `e` and magnitude at least
`|e| − Δ`, so the product `(e − w) · deadZone Δ e` dominates its square. -/
theorem deadzone_residual_le_sq {Delta e w : ℝ} (hDelta : 0 ≤ Delta)
    (hw : |w| ≤ Delta) : (deadZone Delta e) ^ 2 ≤ (e - w) * deadZone Delta e := by
  rw [deadZone]
  split_ifs with h
  · simp
  · rw [not_le] at h
    have hw_le : w ≤ Delta := (abs_le.mp hw).2
    have hw_ge : -Delta ≤ w := (abs_le.mp hw).1
    rcases lt_trichotomy e 0 with hneg | hzero | hpos
    · rw [Real.sign_of_neg hneg, mul_neg_one, sub_neg_eq_add]
      have he : e + Delta < 0 := by
        rw [abs_of_neg hneg] at h
        linarith
      nlinarith
    · rw [hzero, abs_zero] at h
      exact absurd h (not_lt.mpr hDelta)
    · rw [Real.sign_of_pos hpos, mul_one]
      have he : 0 < e - Delta := by
        rw [abs_of_pos hpos] at h
        linarith
      nlinarith

/-- **The dead zone differs from the identity by at most its level.** For `Δ ≥ 0`
the absolute error is bounded by the dead-zone level plus the absolute dead-zoned
error: `|e| ≤ Δ + |deadZone Δ e|`.

Inside the dead zone `deadZone Δ e = 0` and `|e| ≤ Δ`; outside,
`|deadZone Δ e| = |e| − Δ`, giving equality. This is the scalar step that shifts
the growth bound (11.186) by `Δ` when the performance error is replaced by its
dead-zoned version. -/
theorem abs_le_add_abs_deadZone {Delta e : ℝ} (hDelta : 0 ≤ Delta) :
    |e| ≤ Delta + |deadZone Delta e| := by
  rw [deadZone]
  split_ifs with h
  · simpa using h
  · rw [not_le] at h
    rcases lt_trichotomy e 0 with hneg | hzero | hpos
    · rw [Real.sign_of_neg hneg, mul_neg_one, sub_neg_eq_add]
      rw [abs_of_neg hneg] at h ⊢
      have he : e + Delta < 0 := by linarith
      rw [abs_of_neg he]
      linarith
    · rw [hzero, abs_zero] at h
      exact absurd h (not_lt.mpr hDelta)
    · rw [Real.sign_of_pos hpos, mul_one]
      rw [abs_of_pos hpos] at h ⊢
      have he : 0 < e - Delta := by linarith
      rw [abs_of_pos he]
      linarith

/-- **Shifted growth bound (the `Δ`-shifted form of (11.186)).** Assume the growth
bound (11.24) `x t ≤ C₁ + C₂ · max_{k ≤ t+D+1} e k` relating the weighted regressor
norm `x` to the performance error `e`. Replacing `e` by its dead-zoned version
`deadZone Δ e` shifts the constant by `C₂ · Δ`, because `|e k| ≤ Δ + |deadZone Δ (e k)|`:

`x t ≤ (C₁ + C₂ · Δ) + C₂ · max_{k ≤ t+D+1} |deadZone Δ (e k)|`.

The running maximum of `e` is bounded via `Finset.sup'_le` by `Δ` plus the running
maximum of `|deadZone Δ e|`. -/
theorem robust_direct_growth_bound {x e : ℕ → ℝ} {Delta C1 C2 : ℝ} (D : ℕ)
    (hDelta : 0 ≤ Delta) (hC2 : 0 ≤ C2)
    (hbound : ∀ t, x t ≤ C1 + C2 * (Finset.range (t + D + 2)).sup' (by simp) e) :
    ∀ t, x t ≤ (C1 + C2 * Delta) +
      C2 * (Finset.range (t + D + 2)).sup' (by simp) (fun k ↦ |deadZone Delta (e k)|) := by
  intro t
  have hsup : (Finset.range (t + D + 2)).sup' (by simp) e ≤
      Delta + (Finset.range (t + D + 2)).sup' (by simp)
        (fun k ↦ |deadZone Delta (e k)|) := by
    apply Finset.sup'_le
    intro k hk
    have h1 : e k ≤ |e k| := le_abs_self _
    have h2 : |e k| ≤ Delta + |deadZone Delta (e k)| := abs_le_add_abs_deadZone hDelta
    have h3 : |deadZone Delta (e k)| ≤
        (Finset.range (t + D + 2)).sup' (by simp) (fun k ↦ |deadZone Delta (e k)|) :=
      Finset.le_sup' (fun k ↦ |deadZone Delta (e k)|) hk
    linarith
  calc x t ≤ C1 + C2 * (Finset.range (t + D + 2)).sup' (by simp) e := hbound t
    _ ≤ C1 + C2 * (Delta + (Finset.range (t + D + 2)).sup' (by simp)
          (fun k ↦ |deadZone Delta (e k)|)) := by
          have hh := mul_le_mul_of_nonneg_left hsup hC2
          linarith
    _ = (C1 + C2 * Delta) + C2 * (Finset.range (t + D + 2)).sup' (by simp)
          (fun k ↦ |deadZone Delta (e k)|) := by ring

/-- **Theorem 11.5 (robust direct adaptive control), statement level.** Assume the
growth bound (11.186) `x t ≤ C₁ + C₂ · max_{k ≤ t+D+1} e k` for the weighted
regressor norm, and the dead-zone PAA dissipation

`V (t + 1) ≤ V t − (deadZone Δ (e (t+D+1)))² / (1 + (x t)²)`

of eq. (11.191), where `V` is a non-negative Lyapunov sequence for the controller
parameter error. Then the weighted regressor is bounded (11.185), the dead-zoned
error tends to `0`, and `limsup |ε⁰| ≤ Δ` (11.182).

The shifted growth bound `robust_direct_growth_bound` and the dissipation are fed
into `direct_adaptive_stability_of_dissipation` with the non-negative error
`|deadZone Δ (e ·)|`, which yields boundedness and `|deadZone Δ (e (t+D+1))| → 0`;
the latter transfers to `deadZone Δ (e (t+D+1)) → 0`, and
`|ε⁰| ≤ Δ + |deadZone Δ ε⁰|` gives the eventual `Δ`-bound. -/
theorem robust_direct_adaptive_stability {V x e : ℕ → ℝ} {Delta C1 C2 : ℝ} (D : ℕ)
    (hDelta : 0 ≤ Delta) (hV : ∀ t, 0 ≤ V t) (hx : ∀ t, 0 ≤ x t)
    (hC1 : 0 < C1) (hC2 : 0 < C2)
    (hbound : ∀ t, x t ≤ C1 + C2 * (Finset.range (t + D + 2)).sup' (by simp) e)
    (hdiss : ∀ t, V (t + 1) ≤ V t - (deadZone Delta (e (t + D + 1))) ^ 2 /
      (1 + (x t) ^ 2)) :
    (∃ M, ∀ t, x t ≤ M) ∧
      Filter.Tendsto (fun t ↦ deadZone Delta (e (t + D + 1))) Filter.atTop (𝓝 0) ∧
      (∀ eps > 0, ∀ᶠ t in Filter.atTop, |e (t + D + 1)| ≤ Delta + eps) := by
  have hC1' : 0 < C1 + C2 * Delta := by
    have : 0 ≤ C2 * Delta := mul_nonneg hC2.le hDelta
    linarith
  have hbound' : ∀ t, x t ≤ (C1 + C2 * Delta) +
      C2 * (Finset.range (t + D + 2)).sup' (by simp)
        (fun k ↦ |deadZone Delta (e k)|) :=
    robust_direct_growth_bound D hDelta hC2.le hbound
  have hstep' : ∀ t, V (t + 1) ≤ V t -
      |deadZone Delta (e (t + D + 1))| ^ 2 / (1 + (x t) ^ 2) := by
    intro t
    simpa only [sq_abs] using hdiss t
  obtain ⟨hM, htend_abs⟩ :=
    direct_adaptive_stability_of_dissipation hV hx (fun t ↦ abs_nonneg _) hC1' hC2 D
      hbound' hstep'
  have htend_dz : Filter.Tendsto (fun t ↦ deadZone Delta (e (t + D + 1)))
      Filter.atTop (𝓝 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).mpr htend_abs
  refine ⟨hM, htend_dz, ?_⟩
  intro eps heps
  have hev : ∀ᶠ t in Filter.atTop, |deadZone Delta (e (t + D + 1))| < eps :=
    (tendsto_order.1 htend_abs).2 eps heps
  filter_upwards [hev] with t ht
  have hle := abs_le_add_abs_deadZone (e := e (t + D + 1)) hDelta
  linarith

/-- **Boundedness of a non-increasing Lyapunov sequence.** If `V` does not increase
at any step, `V (t + 1) ≤ V t`, then by induction it stays below its initial value,
`V t ≤ V 0` for every `t`. This is the monotonicity half of the Lyapunov argument
of Theorem 11.5: the positive sequence `‖θ̃_C(t)‖²_{F⁻¹}` is non-increasing, hence
bounded (11.183). -/
theorem robust_direct_lyapunov_bounded {V : ℕ → ℝ} (hdiss : ∀ t, V (t + 1) ≤ V t) :
    ∀ t, V t ≤ V 0 := by
  intro t
  induction t with
  | zero => exact le_refl _
  | succ n ih => exact le_trans (hdiss n) ih

/-- **The parameter increments of the dead-zone PAA tend to `0`.** Assume the step
bound
`∑ k, (θ̂(t+1) k − θ̂(t) k)² ≤ K · (deadZone Δ (e (t+1)))²`
of the dead-zone PAA, and that the dead-zoned error itself tends to `0`. Then the
squared parameter increment tends to `0`. The lower bound `0` and the upper bound
`K · (deadZone Δ (e (t+1)))² → 0` squeeze the non-negative increment sum. This is
the scalar content of the parameter-update convergence (11.184). -/
theorem robust_direct_param_step_tendsto_zero {n : ℕ} (thetaHat : ℕ → Fin n → ℝ)
    (e : ℕ → ℝ) (Delta K : ℝ)
    (hstep_le : ∀ t, ∑ k, (thetaHat (t + 1) k - thetaHat t k) ^ 2 ≤
      K * (deadZone Delta (e (t + 1))) ^ 2)
    (herr : Filter.Tendsto (fun t ↦ deadZone Delta (e (t + 1))) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun t ↦ ∑ k, (thetaHat (t + 1) k - thetaHat t k) ^ 2)
      Filter.atTop (𝓝 0) := by
  have hg : Filter.Tendsto (fun t ↦ K * (deadZone Delta (e (t + 1))) ^ 2)
      Filter.atTop (𝓝 0) :=
    by simpa using (herr.pow 2).const_mul K
  exact squeeze_zero (fun t ↦ Finset.sum_nonneg (fun k _ ↦ sq_nonneg _)) hstep_le hg

/-- **Robust parametric convergence under persistent excitation.** Assume the
dead-zone PAA step bound
`∑ k, (θ̂(t+1) k − θ̂(t) k)² ≤ K · (deadZone Δ (φ(t)ᵀθ̃(t)))²`,
that the dead-zoned prediction error `deadZone Δ (φ(t)ᵀθ̃(t))` tends to `0` along
with the prediction error `φ(t)ᵀθ̃(t)`, that the regressor is bounded,
`‖φ(t)‖² ≤ Mphi`, and that `φ` is persistently exciting with level `alpha > 0`.
Then the parameter-error norm tends to `0`, `‖θ(t) − θ̂(t)‖² → 0`.

The step bound and the dead-zoned-error limit give, through
`robust_direct_param_step_tendsto_zero` (applied to the shifted error sequence
`e`), the vanishing increments `‖θ̃(t+1) − θ̃(t)‖² → 0` required by Landau
Theorem 3.5. Persistent excitation, the bounded regressor and the vanishing
prediction error then feed `pe_parameter_convergence_dynamic` with
`θ̃(t) = θ − θ̂(t)`, yielding the conclusion. -/
theorem robust_direct_pe_parameter_convergence {n N : ℕ} (phi : ℕ → Fin n → ℝ)
    (theta : Fin n → ℝ) (thetaHat : ℕ → Fin n → ℝ) {alpha Delta K : ℝ}
    (halpha : 0 < alpha)
    (hPE : ∀ t, ∀ v : Fin n → ℝ,
      alpha * ∑ k, v k ^ 2 ≤ ∑ j : Fin N, (∑ k, phi (t + j.val) k * v k) ^ 2)
    (hphi : ∃ Mphi, ∀ t, ∑ k, (phi t k) ^ 2 ≤ Mphi)
    (herr : Filter.Tendsto (fun t ↦ ∑ k, phi t k * (theta k - thetaHat t k))
      Filter.atTop (𝓝 0))
    (hstep_le : ∀ t, ∑ k, (thetaHat (t + 1) k - thetaHat t k) ^ 2 ≤
      K * (deadZone Delta (∑ k, phi t k * (theta k - thetaHat t k))) ^ 2)
    (hdz_err : Filter.Tendsto
      (fun t ↦ deadZone Delta (∑ k, phi t k * (theta k - thetaHat t k)))
      Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun t ↦ ∑ k, (theta k - thetaHat t k) ^ 2) Filter.atTop (𝓝 0) := by
  let e : ℕ → ℝ := fun t ↦ ∑ k, phi (t - 1) k * (theta k - thetaHat (t - 1) k)
  have he : ∀ t, e (t + 1) = ∑ k, phi t k * (theta k - thetaHat t k) := by
    intro t
    simp only [e, Nat.add_sub_cancel]
  have hstep_le' : ∀ t, ∑ k, (thetaHat (t + 1) k - thetaHat t k) ^ 2 ≤
      K * (deadZone Delta (e (t + 1))) ^ 2 := by
    intro t
    rw [he t]
    exact hstep_le t
  have hdz : Filter.Tendsto (fun t ↦ deadZone Delta (e (t + 1))) Filter.atTop (𝓝 0) :=
    Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun t ↦ by
      change deadZone Delta (∑ k, phi t k * (theta k - thetaHat t k)) =
        deadZone Delta (e (t + 1))
      rw [he t])) hdz_err
  have hstep := robust_direct_param_step_tendsto_zero thetaHat e Delta K hstep_le' hdz
  let thetaTilde : ℕ → Fin n → ℝ := fun t k ↦ theta k - thetaHat t k
  have hstepTilde : Filter.Tendsto
      (fun t ↦ ∑ k, (thetaTilde (t + 1) k - thetaTilde t k) ^ 2) Filter.atTop (𝓝 0) :=
    Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun t ↦ by
      apply Finset.sum_congr rfl
      intro k _
      simp only [thetaTilde]
      ring)) hstep
  have hherr' : Filter.Tendsto (fun t ↦ ∑ k, phi t k * thetaTilde t k) Filter.atTop (𝓝 0) :=
    Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun t ↦ by
      apply Finset.sum_congr rfl
      intro k _
      simp only [thetaTilde])) herr
  have hconv := pe_parameter_convergence_dynamic phi thetaTilde halpha hPE hherr' hstepTilde hphi
  simpa only [thetaTilde] using hconv
