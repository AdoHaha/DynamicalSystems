/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.SlidingMode.Basic
public import DynamicalSystems.Control.SlidingMode.Relay
public import DynamicalSystems.DiscreteTime.Lyapunov
public import DynamicalSystems.DiscreteTime.UltimateBoundedness
public import Mathlib.Basic.Real.Sign
public import Mathlib.Tactic

/-! # Discrete-time sliding mode and integral SMC

This file formalizes the scalar discrete-time sliding-mode reaching law and the
discrete-time integral sliding-mode control (ISMC) of G. Bartolini, L. Fridman,
A. Pisano and E. Usai (eds.), *Modern Sliding Mode Control Theory: New
Perspectives and Applications*, LNCIS 375, Springer 2008:

* **Chapter 6** (Zbigniew Galias and Xinghuo Yu, *On Euler's Discretization of
  Sliding Mode Control Systems with Relative Degree Restriction*, printed
  pp. 119–136): the Euler discretization of equivalent-control-based SMC yields
  the scalar switching recurrence `g(x(k+1)) = g(x(k)) - α h sign(g(x(k)))`
  (eq. (11)). Its trajectories enter the quasi-sliding mode band
  `{|s| ≤ α h}` and then alternate between the two half-bands (Lemma 1).
* **Chapter 12** (Xu Jian-Xin and Khalid Abidi, *Output Tracking with
  Discrete-Time Integral Sliding Mode Control*, printed pp. 247–268): the
  discrete integral sliding variable `σ(k) = e(k) - e(0) + ζ(k)`,
  `ζ(k + 1) = ζ(k) + E e(k)`, `ζ(0) = 0`, eliminates the reaching phase
  (eq. (5)), and the tracking error obeys the discrete comparison
  `|e(k+1)| ≤ a |e(k)| + δ_max` whose steady state is bounded by
  `δ_max / (1 - a)` (eq. (15)–(21)).

## Discrete reaching law

Gao's reaching law `s(k+1) = (1 - q) s(k) - ε sign(s(k))` with `0 ≤ q < 1`
unifies the exponential reaching law (`q > 0`) with the Euler-discretized
ECB-SMC recurrence of Chapter 6 (`q = 0`, `ε = α h`). The scalar map is
`gaoReachingMap q ε` and its `q = 0` specialization is `eulerECBReachingMap ε`.

For `|s| > ε` the excess `max (|s| - ε) 0` contracts by at least `ε` whenever it
stays above `ε`; the Archimedean property therefore forces the orbit into the
quasi-sliding band in finitely many steps, and the band is forward invariant.
Because `ε > 0` and the map is discontinuous only at `s = 0`, the discrete
sliding mode does not reach `s = 0` exactly but is confined to the band, where
consecutive values alternate in sign (Chapter 6, Lemma 1).

## Integral SMC

The accumulator `discreteIntegralState E e` is the finite sum `ζ(k)` and the
integral sliding variable is `discreteIntegralSlidingVariable E e`. The
algebraic identity `reaching_phase_elimination` states `σ(0) = 0`, so the
closed-loop motion starts on the sliding manifold. The tracking-error bounds
`ismc_tracking_error_bound`, `ismc_tracking_error_max_bound` and
`ismc_tracking_error_eventually_bound` are the discrete comparison estimates,
reusing `DynamicalSystems.DiscreteTime.Comparison` and
`DynamicalSystems.DiscreteTime.UltimateBoundedness`; the parametric bound
`ismc_tracking_error_O_T_squared` is the exact algebraic content of the
`O(T²)` accuracy claim of Chapter 12 eq. (21).

## Scope

Only the *scalar* switching dynamics is treated. The matrix Euler analysis of
Chapter 6 §2.3 (convergence to a period-2 orbit and its coordinates), the
higher relative-degree theory of §3, and the continuous sampled-data
disturbance integrals `∫_0^T e^{Aτ} B f(…) dτ` of Chapter 12 are deliberately
outside the scope of this file.
-/

@[expose] public section

open Filter
open scoped Topology

/-! ## Part A: discrete reaching law and quasi-sliding mode band -/

/-- The quasi-sliding mode band of width `Δ`: the interval `{s | |s| ≤ Δ}`
(Chapter 6, printed p. 122). -/
def quasiSlidingBand (Δ : ℝ) : Set ℝ := {s | |s| ≤ Δ}

/-- Membership in the quasi-sliding mode band (a `simp` lemma). -/
@[simp] theorem mem_quasiSlidingBand_iff (Δ s : ℝ) :
    s ∈ quasiSlidingBand Δ ↔ |s| ≤ Δ := Iff.rfl

/-- Gao's discrete reaching map `s ↦ (1 - q) s - ε sign s`. With `q = 0` it is
the Euler-discretized reaching law of Chapter 6, eq. (10)–(11). -/
noncomputable def gaoReachingMap (q ε : ℝ) (s : ℝ) : ℝ := (1 - q) * s - ε * Real.sign s

/-- The pointwise unfolding of `gaoReachingMap` (a `simp` lemma). -/
@[simp] theorem gaoReachingMap_apply (q ε s : ℝ) :
    gaoReachingMap q ε s = (1 - q) * s - ε * Real.sign s := rfl

/-- Bridge to the relay feedback of `DynamicalSystems.Control.SlidingMode.Relay`:
Gao's reaching map is `(1 - q) s` minus the relay `relay ε s`. -/
theorem gaoReachingMap_eq_relay (q ε s : ℝ) :
    gaoReachingMap q ε s = (1 - q) * s - relay ε s := by
  simp only [gaoReachingMap_apply, relay_apply]

/-- The Euler-discretized equivalent-control-based SMC reaching map of Chapter 6,
eq. (10)–(11): `s ↦ s - ε sign s`, the `q = 0` case of `gaoReachingMap`. -/
noncomputable def eulerECBReachingMap (ε : ℝ) : ℝ → ℝ := gaoReachingMap 0 ε

/-- The pointwise unfolding of `eulerECBReachingMap` (a `simp` lemma). -/
@[simp] theorem eulerECBReachingMap_apply (ε s : ℝ) :
    eulerECBReachingMap ε s = s - ε * Real.sign s := by
  simp only [eulerECBReachingMap, gaoReachingMap_apply]
  ring

/-- `gaoReachingMap` is odd in `s`, since `Real.sign` is odd. This is what lets
the analysis below treat the two half-lines symmetrically. -/
theorem gaoReachingMap_neg (q ε s : ℝ) :
    gaoReachingMap q ε (-s) = -gaoReachingMap q ε s := by
  simp only [gaoReachingMap_apply, Real.sign_neg]
  ring

/-- **Band forward invariance.** For `0 ≤ q < 1` and `ε ≥ 0` the quasi-sliding
band `{|s| ≤ ε}` is forward invariant under Gao's reaching map. -/
theorem mapsTo_gaoReachingMap_quasiSlidingBand {q ε : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hε : 0 ≤ ε) :
    Set.MapsTo (gaoReachingMap q ε) (quasiSlidingBand ε) (quasiSlidingBand ε) := by
  intro s hs
  rw [mem_quasiSlidingBand_iff] at hs ⊢
  rw [gaoReachingMap_apply]
  rcases lt_trichotomy s 0 with hsneg | rfl | hspos
  · rw [abs_le] at hs
    rw [Real.sign_of_neg hsneg, abs_le]
    have h1q0 : 0 ≤ 1 - q := by linarith
    have hle : (1 - q) * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h1q0 (le_of_lt hsneg)
    have hge : s ≤ (1 - q) * s := by
      have h2 : s - (1 - q) * s = q * s := by ring
      have h3 : q * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hq0 (le_of_lt hsneg)
      linarith
    exact ⟨by linarith, by linarith⟩
  · simp [hε]
  · rw [abs_le] at hs
    rw [Real.sign_of_pos hspos, abs_le]
    have h1q0 : 0 ≤ 1 - q := by linarith
    have hge : 0 ≤ (1 - q) * s := mul_nonneg h1q0 (le_of_lt hspos)
    have hle : (1 - q) * s ≤ s := by
      have h1 : (1 - q) * s ≤ 1 * s := mul_le_mul_of_nonneg_right (by linarith : 1 - q ≤ 1)
        (le_of_lt hspos)
      linarith
    exact ⟨by linarith, by linarith [hs.2]⟩

/-- Forward invariance of the quasi-sliding band under the Euler-discretized
reaching law (the `q = 0` case of `mapsTo_gaoReachingMap_quasiSlidingBand`). -/
theorem mapsTo_eulerECBReachingMap_quasiSlidingBand {ε : ℝ} (hε : 0 ≤ ε) :
    Set.MapsTo (eulerECBReachingMap ε) (quasiSlidingBand ε) (quasiSlidingBand ε) :=
  mapsTo_gaoReachingMap_quasiSlidingBand le_rfl (by norm_num) hε

/-- **Period-2 alternation, positive half** (Chapter 6, Lemma 1): inside the band,
a positive value is mapped to a non-positive value. -/
theorem gaoReachingMap_nonpos_of_mem_band {q ε s : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hε : 0 < ε) (hs : s ∈ quasiSlidingBand ε) (hspos : 0 < s) :
    gaoReachingMap q ε s ≤ 0 := by
  rw [mem_quasiSlidingBand_iff] at hs
  rw [gaoReachingMap_apply, Real.sign_of_pos hspos]
  have h1q : 0 ≤ 1 - q := by linarith
  have := mul_le_mul_of_nonneg_left (abs_le.mp hs).2 h1q
  nlinarith

/-- **Period-2 alternation, negative half** (Chapter 6, Lemma 1): inside the band,
a negative value is mapped to a non-negative value. -/
theorem gaoReachingMap_nonneg_of_mem_band {q ε s : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hε : 0 < ε) (hs : s ∈ quasiSlidingBand ε) (hsneg : s < 0) :
    0 ≤ gaoReachingMap q ε s := by
  rw [mem_quasiSlidingBand_iff] at hs
  rw [gaoReachingMap_apply, Real.sign_of_neg hsneg]
  have h1q : 0 ≤ 1 - q := by linarith
  have := mul_le_mul_of_nonneg_left (abs_le.mp hs).1 h1q
  nlinarith

/-- Step contraction above the band: for `ε < s` the reaching map decreases the
state by at least `ε`. -/
theorem gaoReachingMap_le_sub_of_gt {q ε s : ℝ} (hq0 : 0 ≤ q) (hε : 0 < ε) (hs : ε < s) :
    gaoReachingMap q ε s ≤ s - ε := by
  have hspos : 0 < s := by linarith
  rw [gaoReachingMap_apply, Real.sign_of_pos hspos]
  nlinarith [mul_nonneg hq0 (le_of_lt hspos)]

/-- No overshoot below `-ε` when coming from above the band: for `ε < s` the
reaching map lands strictly above `-ε`. The hypothesis `0 ≤ q` belongs to the
standard reaching-law signature but is not needed for this one-sided bound. -/
theorem gaoReachingMap_gt_neg_of_gt {q ε s : ℝ} (_hq0 : 0 ≤ q) (hq1 : q < 1) (hε : 0 < ε)
    (hs : ε < s) : -ε < gaoReachingMap q ε s := by
  have hspos : 0 < s := by linarith
  rw [gaoReachingMap_apply, Real.sign_of_pos hspos]
  have h1q : 0 < 1 - q := by linarith
  have := mul_lt_mul_of_pos_left hs h1q
  nlinarith

/-- Step contraction below the band: for `s < -ε` the reaching map increases the
state by at least `ε`. -/
theorem gaoReachingMap_ge_add_of_lt {q ε s : ℝ} (hq0 : 0 ≤ q) (hε : 0 < ε) (hs : s < -ε) :
    s + ε ≤ gaoReachingMap q ε s := by
  have hsneg : s < 0 := by linarith
  rw [gaoReachingMap_apply, Real.sign_of_neg hsneg]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hq0 (le_of_lt hsneg)]

/-- No overshoot above `ε` when coming from below the band: for `s < -ε` the
reaching map lands strictly below `ε`. The hypothesis `0 ≤ q` belongs to the
standard reaching-law signature but is not needed for this one-sided bound. -/
theorem gaoReachingMap_lt_pos_of_lt {q ε s : ℝ} (_hq0 : 0 ≤ q) (hq1 : q < 1) (hε : 0 < ε)
    (hs : s < -ε) : gaoReachingMap q ε s < ε := by
  have hsneg : s < 0 := by linarith
  rw [gaoReachingMap_apply, Real.sign_of_neg hsneg]
  have h1q : 0 < 1 - q := by linarith
  have := mul_lt_mul_of_pos_left hs h1q
  nlinarith

/-! ### The excess and its contraction -/

/-- Elementary bound: if `-ε < x ≤ m`, then the excess `max (|x| - ε) 0` is at
most `max (m - ε) 0`. -/
private lemma max_abs_sub_le {ε x m : ℝ} (hlo : -ε < x) (hhi : x ≤ m) :
    max (|x| - ε) 0 ≤ max (m - ε) 0 := by
  rw [max_le_iff]
  refine ⟨?_, le_max_of_le_right le_rfl⟩
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact le_max_of_le_left (by linarith)
  · rw [abs_of_neg hx]
    exact le_max_of_le_right (by linarith)

/-- The excess `max (|s| - ε) 0` above the quasi-sliding band contracts by one
step of the reaching map, at least by `ε` while it exceeds `ε`. -/
private lemma gaoReachingMap_excess_step {q ε : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hε : 0 < ε) (s : ℝ) :
    max (|gaoReachingMap q ε s| - ε) 0 ≤ max (max (|s| - ε) 0 - ε) 0 := by
  rcases le_or_gt |s| ε with hs | hs
  · have hband : s ∈ quasiSlidingBand ε := by rwa [mem_quasiSlidingBand_iff]
    have hf := mapsTo_gaoReachingMap_quasiSlidingBand hq0 hq1 hε.le hband
    rw [mem_quasiSlidingBand_iff] at hf
    have h1 : |s| - ε ≤ 0 := by linarith
    have h2 : |gaoReachingMap q ε s| - ε ≤ 0 := by linarith
    rw [max_eq_right h1, max_eq_right h2, max_eq_right (by linarith : (0 : ℝ) - ε ≤ 0)]
  · rw [lt_abs] at hs
    rcases hs with hspos | hsneg
    · have hsa : |s| = s := abs_of_pos (by linarith)
      rw [hsa, max_eq_left (by linarith : (0 : ℝ) ≤ s - ε)]
      have h := max_abs_sub_le (gaoReachingMap_gt_neg_of_gt hq0 hq1 hε hspos)
        (gaoReachingMap_le_sub_of_gt hq0 hε hspos)
      have heq : (s - ε) - ε = s - 2 * ε := by ring
      simpa only [heq] using h
    · have hsn : s < 0 := by linarith
      have hsa : |s| = -s := abs_of_neg hsn
      rw [hsa, max_eq_left (by linarith : (0 : ℝ) ≤ -s - ε)]
      have hspos : ε < -s := by linarith
      have h := max_abs_sub_le (gaoReachingMap_gt_neg_of_gt hq0 hq1 hε hspos)
        (gaoReachingMap_le_sub_of_gt hq0 hε hspos)
      rw [gaoReachingMap_neg, abs_neg] at h
      have heq : ((-s) - ε) - ε = -s - 2 * ε := by ring
      simpa only [heq] using h

/-- Auxiliary identity: for `ε ≥ 0` the outer `max` may be pushed inside,
`max (max a 0 - ε) 0 = max (a - ε) 0`. -/
private lemma max_max_sub {a ε : ℝ} (hε : 0 ≤ ε) :
    max (max a 0 - ε) 0 = max (a - ε) 0 := by
  rcases le_total a 0 with ha | ha
  · rw [max_eq_right ha, max_eq_right (by linarith : (0 : ℝ) - ε ≤ 0),
      max_eq_right (by linarith : a - ε ≤ 0)]
  · rw [max_eq_left ha]

/-- Auxiliary identity: the one-step excess drop is the excess truncated at `ε`,
`max 0 (a - ε) = max 0 a - max 0 (min ε a)` for `ε > 0`. -/
private lemma max_sub_max_min {a ε : ℝ} (hε : 0 < ε) :
    max 0 (a - ε) = max 0 a - max 0 (min ε a) := by
  rcases le_total a 0 with ha | ha
  · rw [max_eq_left (by linarith : a - ε ≤ 0), min_eq_right (by linarith : a ≤ ε),
      max_eq_left ha]
    ring
  · rcases le_total a ε with haε | hεa
    · rw [max_eq_left (by linarith : a - ε ≤ 0), min_eq_right haε, max_eq_right ha]
      ring
    · rw [max_eq_right (by linarith : 0 ≤ a - ε), min_eq_left hεa, max_eq_right ha,
        max_eq_right hε.le]

/-- **Finite-step reach into the quasi-sliding band.** From any initial value
`s₀`, Gao's reaching law reaches `{|s| ≤ ε}` in finitely many steps and then
stays there, because the band is forward invariant. -/
theorem gaoReachingMap_reaches_quasiSlidingBand (q ε : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hε : 0 < ε) (s₀ : ℝ) :
    ∃ N : ℕ, ∀ k ≥ N, (gaoReachingMap q ε)^[k] s₀ ∈ quasiSlidingBand ε := by
  have hstep : ∀ s : ℝ, max (|gaoReachingMap q ε s| - ε) 0
      ≤ max (max (|s| - ε) 0 - ε) 0 := gaoReachingMap_excess_step hq0 hq1 hε
  have hind : ∀ k : ℕ, max (|(gaoReachingMap q ε)^[k] s₀| - ε) 0
      ≤ max (max (|s₀| - ε) 0 - ↑k * ε) 0 := by
    intro k
    induction k with
    | zero =>
        simp only [Function.iterate_zero, id_eq, Nat.cast_zero, zero_mul, sub_zero]
        rw [max_eq_left (le_max_right (|s₀| - ε) 0)]
    | succ k ih =>
        rw [Function.iterate_succ_apply']
        calc max (|gaoReachingMap q ε ((gaoReachingMap q ε)^[k] s₀)| - ε) 0
            ≤ max (max (|(gaoReachingMap q ε)^[k] s₀| - ε) 0 - ε) 0 := hstep _
          _ ≤ max (max (max (|s₀| - ε) 0 - ↑k * ε) 0 - ε) 0 :=
                max_le_max (sub_le_sub_right ih ε) le_rfl
          _ = max (max (|s₀| - ε) 0 - ↑k * ε - ε) 0 := max_max_sub hε.le
          _ = max (max (|s₀| - ε) 0 - ↑(k + 1) * ε) 0 := by push_cast; ring_nf
  obtain ⟨N, hN⟩ := exists_nat_gt (max (|s₀| - ε) 0 / ε)
  refine ⟨N, fun k hk => ?_⟩
  rw [mem_quasiSlidingBand_iff]
  have hN' : max (|s₀| - ε) 0 < (N : ℝ) * ε := by
    rwa [div_lt_iff₀ hε] at hN
  have hzero : max (max (|s₀| - ε) 0 - ↑k * ε) 0 = 0 := by
    rw [max_eq_right]
    have hNk : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith [mul_le_mul_of_nonneg_right hNk hε.le]
  have hbound := hind k
  rw [hzero] at hbound
  have := (max_le_iff.mp hbound).1
  linarith

/-- Finite-step reach for the Euler-discretized ECB-SMC reaching law (Chapter 6,
eq. (10)–(11)), a direct specialization of
`gaoReachingMap_reaches_quasiSlidingBand` at `q = 0`. -/
theorem eulerECBReachingMap_reaches_quasiSlidingBand (ε : ℝ) (hε : 0 < ε) (s₀ : ℝ) :
    ∃ N : ℕ, ∀ k ≥ N, (eulerECBReachingMap ε)^[k] s₀ ∈ quasiSlidingBand ε :=
  gaoReachingMap_reaches_quasiSlidingBand 0 ε le_rfl (by norm_num) hε s₀

/-- The excess `max (|s k| - ε) 0` along an orbit of Gao's reaching law is
bounded by the affine comparison sequence `max (E₀ - k ε) 0`. -/
private lemma gao_excess_bound {q ε : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hε : 0 < ε)
    {s : ℕ → ℝ} (h_rec : ∀ k, s (k + 1) = gaoReachingMap q ε (s k)) (n : ℕ) :
    max (|s n| - ε) 0 ≤ max (max (|s 0| - ε) 0 - ↑n * ε) 0 := by
  have hstep : ∀ x : ℝ, max (|gaoReachingMap q ε x| - ε) 0
      ≤ max (max (|x| - ε) 0 - ε) 0 := gaoReachingMap_excess_step hq0 hq1 hε
  induction n with
  | zero =>
      simp only [Nat.cast_zero, zero_mul, sub_zero]
      rw [max_eq_left (le_max_right (|s 0| - ε) 0)]
  | succ n ih =>
      rw [h_rec n]
      calc max (|gaoReachingMap q ε (s n)| - ε) 0
          ≤ max (max (|s n| - ε) 0 - ε) 0 := hstep _
        _ ≤ max (max (max (|s 0| - ε) 0 - ↑n * ε) 0 - ε) 0 :=
              max_le_max (sub_le_sub_right ih ε) le_rfl
        _ = max (max (|s 0| - ε) 0 - ↑n * ε - ε) 0 := max_max_sub hε.le
        _ = max (max (|s 0| - ε) 0 - ↑(n + 1) * ε) 0 := by push_cast; ring_nf

/-- **Telescoping dissipation bound for the reaching law.** The excess
`w k = max 0 (min ε (|s k| - ε))` removed from the trajectory at step `k` is
summable along an orbit, and its partial sums are bounded by the initial excess
`max 0 (|s 0| - ε)`. This is the discrete dissipation (telescoping) estimate
behind `gao_steps_outside_band_bound`, obtained through Landau's telescoping
bridge `DynamicalSystems.DiscreteTime.Lyapunov.sum_le_of_succ_le_sub`. -/
theorem gao_excess_dissipation_bound {q ε : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hε : 0 < ε)
    (s : ℕ → ℝ) (h_rec : ∀ k, s (k + 1) = gaoReachingMap q ε (s k)) (n : ℕ) :
    (Finset.range n).sum (fun k ↦ max 0 (min ε (|s k| - ε)))
      ≤ max 0 (|s 0| - ε) := by
  apply sum_le_of_succ_le_sub (v := fun k ↦ max 0 (|s k| - ε))
  · intro k
    exact le_max_left _ _
  · intro k
    rw [h_rec k]
    have hstep := gaoReachingMap_excess_step hq0 hq1 hε (s k)
    rw [max_comm (|gaoReachingMap q ε (s k)| - ε) 0] at hstep
    refine hstep.trans ?_
    rw [max_max_sub hε.le, max_comm (|s k| - ε - ε) 0]
    exact le_of_eq (max_sub_max_min hε)

/-- **Dissipation bound on the number of steps outside the band** (general
recurrence form). If a sequence following Gao's reaching law satisfies
`ε < |s k|` for all `k < N` (it stays strictly outside the quasi-sliding band
for `N` steps), then `N ε ≤ |s 0|`. Equivalently the orbit can spend at most
`|s 0| / ε` steps outside the band, the discrete dissipation (telescoping) bound. -/
theorem gao_steps_outside_band_bound_of_recurrence (q ε : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hε : 0 < ε) (s : ℕ → ℝ) (h_rec : ∀ k, s (k + 1) = gaoReachingMap q ε (s k))
    (N : ℕ) (h_outside : ∀ k < N, ε < |s k|) :
    (N : ℝ) * ε ≤ |s 0| := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    simp
  · have h0 : ε < |s 0| := h_outside 0 hN
    have hE0 : max (|s 0| - ε) 0 = |s 0| - ε := max_eq_left (by linarith)
    have hpred : N - 1 < N := Nat.sub_one_lt (Nat.pos_iff_ne_zero.mp hN)
    have hout : ε < |s (N - 1)| := h_outside (N - 1) hpred
    have hEN : 0 < max (|s (N - 1)| - ε) 0 := by
      rw [max_eq_left (by linarith : (0 : ℝ) ≤ |s (N - 1)| - ε)]
      linarith
    have hb := gao_excess_bound hq0 hq1 hε h_rec (N - 1)
    rw [hE0] at hb
    have hpos : 0 < |s 0| - ε - ↑(N - 1) * ε := by
      have hmax : 0 < max (|s 0| - ε - ↑(N - 1) * ε) 0 := lt_of_lt_of_le hEN hb
      by_contra hle
      rw [not_lt] at hle
      rw [max_eq_right hle] at hmax
      exact lt_irrefl 0 hmax
    have hcast : (N : ℝ) * ε = ↑(N - 1) * ε + ε := by
      have h1 : (1 : ℕ) ≤ N := Nat.succ_le_of_lt hN
      have hc : (↑(N - 1) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub h1, Nat.cast_one]
      rw [hc]
      ring
    rw [hcast]
    linarith

/-- **Dissipation bound on the number of steps outside the band.** If the orbit of
Gao's reaching law started at `s₀` stays strictly outside the quasi-sliding band
for `N` steps, then `N ε ≤ |s₀|`; at most `|s₀| / ε` steps can be spent outside
the band. -/
theorem gao_steps_outside_band_bound (q ε : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hε : 0 < ε)
    (s₀ : ℝ) :
    ∀ N : ℕ, (∀ k < N, ε < |(gaoReachingMap q ε)^[k] s₀|) → (N : ℝ) * ε ≤ |s₀| := by
  intro N h_outside
  exact gao_steps_outside_band_bound_of_recurrence q ε hq0 hq1 hε
    (fun k ↦ (gaoReachingMap q ε)^[k] s₀)
    (fun k ↦ Function.iterate_succ_apply' _ _ _) N h_outside

/-! ## Part B: discrete integral sliding mode control -/

/-- The discrete integral accumulator of Chapter 12 eq. (5): `ζ 0 = 0` and
`ζ (k + 1) = ζ k + E e k`. -/
def discreteIntegralState (E : ℝ) (e : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => discreteIntegralState E e k + E * e k

/-- The accumulator starts at zero (a `simp` lemma). -/
@[simp] theorem discreteIntegralState_zero (E : ℝ) (e : ℕ → ℝ) :
    discreteIntegralState E e 0 = 0 := rfl

/-- The accumulator recursion (a `simp` lemma). -/
@[simp] theorem discreteIntegralState_succ (E : ℝ) (e : ℕ → ℝ) (k : ℕ) :
    discreteIntegralState E e (k + 1) = discreteIntegralState E e k + E * e k := rfl

/-- The discrete integral sliding variable `σ k = e k - e 0 + ζ k`
(Chapter 12 eq. (5)). -/
def discreteIntegralSlidingVariable (E : ℝ) (e : ℕ → ℝ) (k : ℕ) : ℝ :=
  e k - e 0 + discreteIntegralState E e k

/-- **Reaching-phase elimination** (Chapter 12 eq. (5)): the discrete integral
sliding variable vanishes at step `0`, `σ 0 = 0`, so the closed loop starts on
the sliding manifold with no reaching phase. -/
@[simp] theorem reaching_phase_elimination (E : ℝ) (e : ℕ → ℝ) :
    discreteIntegralSlidingVariable E e 0 = 0 := by
  simp only [discreteIntegralSlidingVariable, discreteIntegralState_zero, sub_self, zero_add]

/-- **Discrete tracking-error comparison bound** (Chapter 12 eq. (15)–(18)). If
the tracking error obeys `|e (k+1)| ≤ a |e k| + |δ k|` with `|δ k| ≤ δ_max` and
`0 ≤ a < 1`, then `|e k| ≤ a^k |e 0| + δ_max (1 - a^k) / (1 - a)`. -/
theorem ismc_tracking_error_bound {e δ : ℕ → ℝ} {a δ_max : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hδ : ∀ k, |δ k| ≤ δ_max)
    (h_rec : ∀ k, |e (k + 1)| ≤ a * |e k| + |δ k|) (k : ℕ) :
    |e k| ≤ a ^ k * |e 0| + δ_max * (1 - a ^ k) / (1 - a) := by
  have h_step : ∀ k, |e (k + 1)| ≤ a * |e k| + δ_max := fun k ↦
    (h_rec k).trans (add_le_add_right (hδ k) (a * |e k|))
  exact le_of_succ_le_mul_add ha0 ha1 (fun k ↦ abs_nonneg (e k)) h_step k

/-- **Uniform tracking-error bound** (Chapter 12): under the same hypotheses the
error is bounded by `max (|e 0|) (δ_max / (1 - a))`. -/
theorem ismc_tracking_error_max_bound {e δ : ℕ → ℝ} {a δ_max : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hδ : ∀ k, |δ k| ≤ δ_max)
    (h_rec : ∀ k, |e (k + 1)| ≤ a * |e k| + |δ k|) (k : ℕ) :
    |e k| ≤ max (|e 0|) (δ_max / (1 - a)) := by
  have h_step : ∀ k, |e (k + 1)| ≤ a * |e k| + δ_max := fun k ↦
    (h_rec k).trans (add_le_add_right (hδ k) (a * |e k|))
  exact le_max_of_succ_le_mul_add ha0 ha1 (fun k ↦ abs_nonneg (e k)) h_step k

/-- **Ultimate tracking-error bound** (Chapter 12 eq. (21)): the tracking error is
eventually within `δ_max / (1 - a) + ε` of zero for every `ε > 0`. -/
theorem ismc_tracking_error_eventually_bound {e δ : ℕ → ℝ} {a δ_max ε : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a < 1) (hε : 0 < ε) (hδ : ∀ k, |δ k| ≤ δ_max)
    (h_rec : ∀ k, |e (k + 1)| ≤ a * |e k| + |δ k|) :
    ∀ᶠ k in atTop, |e k| ≤ δ_max / (1 - a) + ε := by
  have h_step : ∀ k, |e (k + 1)| ≤ a * |e k| + δ_max := fun k ↦
    (h_rec k).trans (add_le_add_right (hδ k) (a * |e k|))
  exact eventually_le_add_of_succ_le_mul_add ha0 ha1 (fun k ↦ abs_nonneg (e k)) h_step hε

/-- **Parametric `O(T²)` tracking bound** (Chapter 12 eq. (21)). If the disturbance
second difference obeys `δ_max ≤ M T³` and the contraction gap obeys
`κ T ≤ 1 - a` with `κ > 0`, then the steady-state tracking bound satisfies
`δ_max / (1 - a) ≤ (M / κ) T²`. This is the exact algebraic content of the
`O(T²)` accuracy statement, with no continuous-sampling asymptotics. The
hypothesis `0 ≤ a` belongs to the reviewed signature but is not needed for this
algebraic bound. -/
theorem ismc_tracking_error_O_T_squared {M κ T δ_max a : ℝ} (hM : 0 ≤ M) (hκ : 0 < κ)
    (hT : 0 < T) (hδ : δ_max ≤ M * T ^ 3) (_ha0 : 0 ≤ a) (ha1 : a < 1)
    (hgap : κ * T ≤ 1 - a) :
    δ_max / (1 - a) ≤ (M / κ) * T ^ 2 := by
  have hpos : 0 < 1 - a := by linarith
  have hκT : 0 < κ * T := mul_pos hκ hT
  have hMT : 0 ≤ M * T ^ 3 := mul_nonneg hM (by positivity)
  calc δ_max / (1 - a) ≤ (M * T ^ 3) / (1 - a) := div_le_div_of_nonneg_right hδ hpos.le
    _ ≤ (M * T ^ 3) / (κ * T) := div_le_div_of_nonneg_left hMT hκT hgap
    _ = (M / κ) * T ^ 2 := by
        field_simp
