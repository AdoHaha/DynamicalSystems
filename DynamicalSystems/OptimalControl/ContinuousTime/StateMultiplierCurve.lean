/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.PenaltyBoundaryPositivity
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Integral.PeakFunction

/-!
# The state-multiplier curve of Berkovitz & Medhin §11.3

This file formalizes the analytic core of the state-multiplier construction of
Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), §11.3.

The book's Lemma 11.3.7 is the du Bois–Reymond lemma for **nonnegative,
endpoint-vanishing** test functions: if `p, q ∈ L¹(0,1)` and

  `∫_0^1 (p w + q w') dt ≥ 0`

for every nonnegative `w` with `w(0) = w(1) = 0` (piecewise `C¹`, or, as used in
the book's own first variation (11.3.20), absolutely continuous with square
integrable derivative), then `T(t) = q(t) − ∫_0^t p` is nonincreasing outside a
null set.  The formal statement below uses the equivalent primitive rendering of
the test class (the primitive of `ψ` plays the rôle of `w`), which is exactly the
class supplied by the first variation.

Lemma 11.3.9 is the companion observation: the nonincreasing function
`λ(ε;·) = Ψ(ε;·)·ξ(ε;·) − ∫_0^t Ψ(ε;·)·ξ'(ε;·)` is constant on every interval
on which the source field `Ψ(ε;·)` is constant, hence on the components of the
slack set `{G < 0}`.

Book citations live only in docstrings; all declaration names are concept names.
-/

@[expose] public section

open Set MeasureTheory Filter intervalIntegral
open scoped Topology

namespace DuBoisReymond

noncomputable section

/-- A fixed smooth bump supported inside `(0,1)`, used to build the nonnegative
endpoint-vanishing test functions of the du Bois–Reymond lemma. -/
def testBump : ContDiffBump (1 / 2 : ℝ) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

theorem testBump_rOut : testBump.rOut = 1 / 2 := rfl

/-- The density `ω` of the test bump, normalized to have total mass one. -/
def testDensity (x : ℝ) : ℝ := ContDiffBump.normed testBump volume x

theorem testDensity_nonneg (x : ℝ) : 0 ≤ testDensity x :=
  ContDiffBump.nonneg_normed testBump x

theorem testDensity_integral : ∫ x, testDensity x = 1 :=
  ContDiffBump.integral_normed testBump

theorem testDensity_contDiff : ContDiff ℝ (⊤ : ℕ∞) testDensity :=
  ContDiffBump.contDiff_normed testBump

theorem testDensity_continuous : Continuous testDensity :=
  testDensity_contDiff.continuous

theorem testDensity_support_subset : Function.support testDensity ⊆ Ioo 0 1 := by
  have hsupp : Function.support testDensity = Metric.ball (1 / 2 : ℝ) (1 / 2) := by
    unfold testDensity
    rw [ContDiffBump.support_normed_eq]
    rfl
  intro x hx
  rw [hsupp, Metric.mem_ball, Real.dist_eq] at hx
  rw [mem_Ioo]
  constructor <;> linarith [abs_lt.mp hx |>.1, abs_lt.mp hx |>.2]

theorem testDensity_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : testDensity x = 0 := by
  by_contra h
  have hmem : x ∈ Function.support testDensity := Function.mem_support.mpr h
  exact absurd (testDensity_support_subset hmem).1 (not_lt.mpr hx)

theorem testDensity_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) : testDensity x = 0 := by
  by_contra h
  have hmem : x ∈ Function.support testDensity := Function.mem_support.mpr h
  exact absurd (testDensity_support_subset hmem).2 (not_lt.mpr hx)

/-- The cumulative distribution function of the test bump,
`R u = ∫_0^u ω`. -/
def testCumulative (u : ℝ) : ℝ := ∫ s in (0 : ℝ)..u, testDensity s

theorem testCumulative_zero_of_nonpos {u : ℝ} (hu : u ≤ 0) : testCumulative u = 0 := by
  rw [testCumulative]
  have hcongr : (∫ s in (0 : ℝ)..u, testDensity s) =
      ∫ s in (0 : ℝ)..u, (fun _ => (0 : ℝ)) s :=
    intervalIntegral.integral_congr fun s hs =>
      testDensity_eq_zero_of_nonpos (le_trans hs.2 (max_le_iff.mpr ⟨le_rfl, hu⟩))
  rw [hcongr]; simp

theorem testCumulative_one_of_one_le {u : ℝ} (hu : 1 ≤ u) : testCumulative u = 1 := by
  have hsplit : (∫ s in (0 : ℝ)..u, testDensity s) =
      (∫ s in (0 : ℝ)..1, testDensity s) + ∫ s in (1 : ℝ)..u, testDensity s :=
    (intervalIntegral.integral_add_adjacent_intervals
      (testDensity_continuous.intervalIntegrable 0 1)
      (testDensity_continuous.intervalIntegrable 1 u)).symm
  have h01 : (∫ s in (0 : ℝ)..1, testDensity s) = 1 := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) (f := testDensity)
      (a := (0 : ℝ)) (b := 1) ?_, testDensity_integral]
    intro x hx
    exact ⟨(testDensity_support_subset hx).1, (testDensity_support_subset hx).2.le⟩
  have hzero : (∫ s in (1 : ℝ)..u, testDensity s) = 0 := by
    have hcongr : (∫ s in (1 : ℝ)..u, testDensity s) =
        ∫ s in (1 : ℝ)..u, (fun _ => (0 : ℝ)) s :=
      intervalIntegral.integral_congr fun s hs =>
        testDensity_eq_zero_of_one_le ((min_eq_left hu).ge.trans hs.1)
    rw [hcongr]; simp
  rw [testCumulative, hsplit, h01, hzero, add_zero]

theorem testCumulative_monotone : Monotone testCumulative := by
  intro u v huv
  have hsplit : (∫ s in (0 : ℝ)..u, testDensity s) + ∫ s in u..v, testDensity s =
      ∫ s in (0 : ℝ)..v, testDensity s :=
    intervalIntegral.integral_add_adjacent_intervals
      (testDensity_continuous.intervalIntegrable 0 u)
      (testDensity_continuous.intervalIntegrable u v)
  have hnonneg : 0 ≤ ∫ s in u..v, testDensity s :=
    intervalIntegral.integral_nonneg huv (fun s _ => testDensity_nonneg s)
  rw [testCumulative, testCumulative]
  linarith

theorem testCumulative_continuous : Continuous testCumulative :=
  intervalIntegral.continuous_primitive
    (fun _ _ => testDensity_continuous.intervalIntegrable _ _) 0

theorem testCumulative_hasDerivAt (u : ℝ) :
    HasDerivAt testCumulative (testDensity u) u :=
  intervalIntegral.integral_hasDerivAt_right
    (testDensity_continuous.intervalIntegrable 0 u)
    (testDensity_continuous.stronglyMeasurableAtFilter volume (𝓝 u))
    testDensity_continuous.continuousAt

end

end DuBoisReymond

namespace DuBoisReymond

noncomputable section

/-- The smooth trapezoidal primitive `R((t-a)/ε) - R((t-b)/ε)` used as a
nonnegative, endpoint-vanishing test function. -/
def testTrapezoid (a b ε : ℝ) (t : ℝ) : ℝ :=
  testCumulative ((t - a) / ε) - testCumulative ((t - b) / ε)

/-- The density (derivative) of the trapezoidal test function. -/
def testTrapezoidDensity (a b ε : ℝ) (t : ℝ) : ℝ :=
  ε⁻¹ * (testDensity ((t - a) / ε) - testDensity ((t - b) / ε))

theorem testTrapezoid_zero {a b ε : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 < ε) :
    testTrapezoid a b ε 0 = 0 := by
  have ha' : (0 - a) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  have hb' : (0 - b) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  rw [testTrapezoid, testCumulative_zero_of_nonpos ha', testCumulative_zero_of_nonpos hb',
    sub_self]

theorem testTrapezoidDensity_continuous {a b ε : ℝ} (_hε : ε ≠ 0) :
    Continuous (testTrapezoidDensity a b ε) := by
  unfold testTrapezoidDensity
  have hinner : Continuous (fun t : ℝ => (t - a) / ε) := by fun_prop
  have hinner' : Continuous (fun t : ℝ => (t - b) / ε) := by fun_prop
  exact continuous_const.mul
    ((testDensity_continuous.comp hinner).sub (testDensity_continuous.comp hinner'))

theorem testTrapezoid_hasDerivAt {a b ε : ℝ} (_hε : ε ≠ 0) (t : ℝ) :
    HasDerivAt (testTrapezoid a b ε) (testTrapezoidDensity a b ε t) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s - a) / ε) (1 / ε) t := by
    simpa using ((hasDerivAt_id t).sub_const a).div_const ε
  have h2 : HasDerivAt (fun s : ℝ => (s - b) / ε) (1 / ε) t := by
    simpa using ((hasDerivAt_id t).sub_const b).div_const ε
  have hA := (testCumulative_hasDerivAt ((t - a) / ε)).comp t h1
  have hB := (testCumulative_hasDerivAt ((t - b) / ε)).comp t h2
  have hsub := hA.sub hB
  change HasDerivAt
    (fun s : ℝ => testCumulative ((s - a) / ε) - testCumulative ((s - b) / ε))
    (testDensity ((t - a) / ε) * (1 / ε) - testDensity ((t - b) / ε) * (1 / ε)) t at hsub
  have hfun : (fun s : ℝ => testCumulative ((s - a) / ε) - testCumulative ((s - b) / ε))
      = testTrapezoid a b ε := by
    funext s; rfl
  rw [hfun] at hsub
  have hval : testDensity ((t - a) / ε) * (1 / ε) - testDensity ((t - b) / ε) * (1 / ε)
      = testTrapezoidDensity a b ε t := by
    unfold testTrapezoidDensity
    ring
  rwa [hval] at hsub

theorem integral_testTrapezoidDensity {a b ε t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hε' : 0 < ε) :
    ∫ s in (0 : ℝ)..t, testTrapezoidDensity a b ε s = testTrapezoid a b ε t := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) t,
      HasDerivAt (testTrapezoid a b ε) (testTrapezoidDensity a b ε x) x :=
    fun x _ => testTrapezoid_hasDerivAt hε'.ne' x
  have hint : IntervalIntegrable (testTrapezoidDensity a b ε) volume 0 t :=
    (testTrapezoidDensity_continuous hε'.ne').intervalIntegrable 0 t
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint,
    testTrapezoid_zero (a := a) (b := b) ha hb hε', sub_zero]

end

end DuBoisReymond

namespace DuBoisReymond

noncomputable section

/-- **Lemma 11.3.9 (abstract core).**  If the nonincreasing multiplier curve is
built from a source field `Ψ` by the Stieltjes formula
`λ(t) = Ψ(t)ξ(t) − ∫_0^t Ψ(s)ξ'(s) ds`, and if `Ψ` is constant on an interval
`[α,β]`, then `λ` is constant on `[α,β]`.

This is the step that turns the smooth interior variation (Remark 11.3.6),
giving constancy of `Ψ` on a component of the slack set `{G < 0}`, into
constancy of the state multiplier there.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012),
(11.3.21) and Lemma 11.3.9. -/
theorem multiplierCurve_eq_of_source_constant
    {Psi xi xi' : ℝ → ℝ} {lam : ℝ → ℝ}
    (hlam : lam = fun t => Psi t * xi t - ∫ s in (0 : ℝ)..t, Psi s * xi' s)
    (hxi : ∀ t, HasDerivAt xi (xi' t) t)
    (hxi'int : ∀ a b, IntervalIntegrable xi' volume a b)
    (hPsi'int : ∀ a b, IntervalIntegrable (fun s => Psi s * xi' s) volume a b)
    {α β : ℝ} (hαβ : α ≤ β)
    (hconst : ∀ t ∈ Icc α β, Psi t = Psi α) :
    ∀ t ∈ Icc α β, lam t = lam α := by
  intro t ht
  have hαt : α ≤ t := ht.1
  have hsplit : (∫ s in (0 : ℝ)..t, Psi s * xi' s) =
      (∫ s in (0 : ℝ)..α, Psi s * xi' s) + ∫ s in α..t, Psi s * xi' s :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hPsi'int 0 α) (hPsi'int α t)).symm
  have hconst' : ∀ s ∈ uIcc α t, Psi s * xi' s = Psi α * xi' s := by
    intro s hs
    rw [mem_uIcc] at hs
    rcases hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
    · rw [hconst s ⟨hs1, hs2.trans ht.2⟩]
    · rw [hconst s ⟨ht.1.trans hs1, hs2.trans hαβ⟩]
  have hint_eq : (∫ s in α..t, Psi s * xi' s) = Psi α * ∫ s in α..t, xi' s := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr hconst'
  have hFTC : (∫ s in α..t, xi' s) = xi t - xi α :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hxi x) (hxi'int α t)
  rw [hlam]
  simp only
  rw [hsplit, hint_eq, hFTC, hconst t ht]
  ring

end

end DuBoisReymond

namespace DuBoisReymond

open MeasureTheory

noncomputable section

theorem testDensity_hasCompactSupport : HasCompactSupport testDensity :=
  testBump.hasCompactSupport_normed

theorem testCumulative_nonneg (u : ℝ) : 0 ≤ testCumulative u := by
  rcases le_or_gt 0 u with h | h
  · have h0 : testCumulative 0 = 0 := testCumulative_zero_of_nonpos le_rfl
    rw [← h0]
    exact testCumulative_monotone h
  · rw [testCumulative_zero_of_nonpos h.le]

theorem testCumulative_le_one (u : ℝ) : testCumulative u ≤ 1 := by
  rcases le_or_gt u 1 with h | h
  · rw [← testCumulative_one_of_one_le le_rfl]
    exact testCumulative_monotone h
  · rw [testCumulative_one_of_one_le h.le]

theorem testTrapezoid_nonneg {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε) (x : ℝ) :
    0 ≤ testTrapezoid a b ε x := by
  rw [testTrapezoid]
  have hle : (x - b) / ε ≤ (x - a) / ε := by gcongr
  linarith [testCumulative_monotone hle]

theorem testTrapezoid_le_one (x a b ε : ℝ) : testTrapezoid a b ε x ≤ 1 := by
  rw [testTrapezoid]
  have h1 := testCumulative_le_one ((x - a) / ε)
  have h2 := testCumulative_nonneg ((x - b) / ε)
  linarith

theorem tendsto_testCumulative_div (a x : ℝ) :
    Tendsto (fun ε : ℝ => testCumulative ((x - a) / ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (if a < x then (1 : ℝ) else 0)) := by
  rcases lt_trichotomy a x with h | h | h
  · simp only [h, ite_true]
    have hlim : Tendsto (fun ε : ℝ => (x - a) / ε) (𝓝[>] (0 : ℝ)) atTop := by
      simpa only [div_eq_mul_inv] using
        (tendsto_const_mul_atTop_of_pos (sub_pos.mpr h)).mpr
          (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), testCumulative ((x - a) / ε) = 1 :=
      (hlim.eventually (eventually_ge_atTop 1)).mono
        (fun ε hε => testCumulative_one_of_one_le hε)
    exact tendsto_const_nhds.congr' (hev.mono (fun ε hε => hε.symm))
  · subst h
    simp only [lt_irrefl, ite_false]
    have hz : (fun ε : ℝ => testCumulative ((a - a) / ε)) = fun _ => (0 : ℝ) := by
      funext ε; rw [sub_self, zero_div, testCumulative_zero_of_nonpos le_rfl]
    rw [hz]
    exact tendsto_const_nhds
  · simp only [not_lt.mpr h.le, ite_false]
    have hlim : Tendsto (fun ε : ℝ => (x - a) / ε) (𝓝[>] (0 : ℝ)) atBot := by
      simpa only [div_eq_mul_inv] using
        (tendsto_const_mul_atBot_of_neg (sub_neg.mpr h)).mpr
          (tendsto_inv_nhdsGT_zero (𝕜 := ℝ))
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), testCumulative ((x - a) / ε) = 0 :=
      (hlim.eventually (eventually_le_atBot 0)).mono
        (fun ε hε => testCumulative_zero_of_nonpos hε)
    exact tendsto_const_nhds.congr' (hev.mono (fun ε hε => hε.symm))

theorem tendsto_testTrapezoid (a b x : ℝ) (hab : a ≤ b) :
    Tendsto (fun ε : ℝ => testTrapezoid a b ε x) (𝓝[>] (0 : ℝ))
      (𝓝 (if a < x ∧ x ≤ b then (1 : ℝ) else 0)) := by
  have h1 := tendsto_testCumulative_div a x
  have h2 := tendsto_testCumulative_div b x
  have hsub := h1.sub h2
  have hlim_eq : (if a < x then (1 : ℝ) else 0) - (if b < x then (1 : ℝ) else 0)
      = if a < x ∧ x ≤ b then (1 : ℝ) else 0 := by
    by_cases ha : a < x
    · by_cases hb : b < x
      · simp [ha, hb]
      · simp [ha, hb]
    · by_cases hb : b < x
      · exfalso; linarith
      · simp [ha, hb]
  rw [hlim_eq] at hsub
  simpa only [Pi.sub_apply, testTrapezoid] using hsub

end

end DuBoisReymond

namespace DuBoisReymond

noncomputable section

theorem testTrapezoid_continuous (a b ε : ℝ) : Continuous (testTrapezoid a b ε) := by
  unfold testTrapezoid
  have h1 : Continuous (fun t : ℝ => (t - a) / ε) := by fun_prop
  have h2 : Continuous (fun t : ℝ => (t - b) / ε) := by fun_prop
  exact (testCumulative_continuous.comp h1).sub (testCumulative_continuous.comp h2)

theorem abs_testTrapezoid_le_one (x a b ε : ℝ) : |testTrapezoid a b ε x| ≤ 1 := by
  have h1 : 0 ≤ testCumulative ((x - a) / ε) := testCumulative_nonneg _
  have h2 : testCumulative ((x - a) / ε) ≤ 1 := testCumulative_le_one _
  have h3 : 0 ≤ testCumulative ((x - b) / ε) := testCumulative_nonneg _
  have h4 : testCumulative ((x - b) / ε) ≤ 1 := testCumulative_le_one _
  rw [testTrapezoid, abs_le]
  constructor <;> linarith

theorem indicator_Ioc_testTrapezoid_eq (a b x : ℝ) :
    (if a < x ∧ x ≤ b then (1 : ℝ) else 0) = (Ioc a b).indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ Ioc a b
  · rw [Set.indicator_of_mem hx]
    exact ite_eq_left (Set.mem_Ioc.mp hx)
  · rw [Set.indicator_of_notMem hx, ite_eq_right]
    intro h
    exact hx (Set.mem_Ioc.mpr h)

/-- **The `p`-limit of the trapezoidal test.**  For `p ∈ L¹(0,1)` and `0 ≤ a ≤ b ≤ 1`,
`∫_0^1 p·testTrapezoid a b ε → ∫_a^b p` as `ε → 0⁺`.  This is the dominated-convergence
step (P) of the book's Lemma 11.3.7 proof. -/
theorem tendsto_integral_testTrapezoid (p : ℝ → ℝ)
    (hp : IntegrableOn p (Ioc (0 : ℝ) 1) volume) {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a)
    (hb : b ≤ 1) :
    Tendsto (fun ε : ℝ => ∫ x in (0 : ℝ)..1, p x * testTrapezoid a b ε x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ x in a..b, p x)) := by
  rw [show (fun ε : ℝ => ∫ x in (0 : ℝ)..1, p x * testTrapezoid a b ε x)
      = fun ε => ∫ x in Ioc (0 : ℝ) 1, p x * testTrapezoid a b ε x from by
        funext ε; exact intervalIntegral.integral_of_le zero_le_one]
  have hlim : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      Tendsto (fun ε : ℝ => p x * testTrapezoid a b ε x) (𝓝[>] (0 : ℝ))
        (𝓝 (p x * (Ioc a b).indicator (fun _ => (1 : ℝ)) x)) := by
    filter_upwards with x
    simpa only [indicator_Ioc_testTrapezoid_eq] using
      (tendsto_testTrapezoid a b x hab).const_mul (p x)
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ‖p x * testTrapezoid a b ε x‖ ≤ ‖p x‖ := by
    filter_upwards with ε
    filter_upwards with x
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (by
      rw [Real.norm_eq_abs]; exact abs_testTrapezoid_le_one x a b ε)
  have hmeas : ∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun x => p x * testTrapezoid a b ε x) (volume.restrict (Ioc (0 : ℝ) 1)) :=
    Filter.Eventually.of_forall fun ε =>
      hp.aestronglyMeasurable.mul (testTrapezoid_continuous a b ε).aestronglyMeasurable
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioc (0 : ℝ) 1)) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε x => p x * testTrapezoid a b ε x)
    (f := fun x => p x * (Ioc a b).indicator (fun _ => (1 : ℝ)) x)
    (bound := fun x => ‖p x‖) hmeas hbound hp.norm hlim
  have hconversion : (∫ x in Ioc (0 : ℝ) 1,
      p x * (Ioc a b).indicator (fun _ => (1 : ℝ)) x) = ∫ x in a..b, p x := by
    rw [show (fun x => p x * (Ioc a b).indicator (fun _ => (1 : ℝ)) x)
        = (Ioc a b).indicator (fun x => p x) from by
          funext x
          by_cases hx : x ∈ Ioc a b <;>
            simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc]
    rw [show Ioc (0 : ℝ) 1 ∩ Ioc a b = Ioc a b from by
      ext x
      exact ⟨fun h => h.2, fun h => ⟨⟨lt_of_le_of_lt ha h.1, le_trans h.2 hb⟩, h⟩⟩]
    exact (intervalIntegral.integral_of_le hab).symm
  rwa [hconversion] at hDCT

end

end DuBoisReymond

namespace DuBoisReymond

noncomputable section

/-- The scaled bump as an integral: `ε⁻¹ ∫_0^1 q ω((·-c)/ε) = ∫ q(c+εu) ω(u) du`. -/
theorem integral_scaled_testDensity_mul (q : ℝ → ℝ) (c ε : ℝ) (hε : ε ≠ 0) :
    ε⁻¹ * (∫ x in (0 : ℝ)..1, q x * testDensity ((x - c) / ε)) =
      ∫ u in (-c / ε)..((1 - c) / ε), q (c + ε * u) * testDensity u := by
  have h := intervalIntegral.integral_comp_mul_add
    (f := fun x : ℝ => q x * testDensity ((x - c) / ε)) (hc := hε)
    (a := -c / ε) (b := (1 - c) / ε) (d := c)
  rw [smul_eq_mul] at h
  have h0 : ε * (-c / ε) + c = 0 := by field_simp [hε]; ring
  have h1 : ε * ((1 - c) / ε) + c = 1 := by field_simp [hε]; ring
  rw [h0, h1] at h
  have hfun : ∀ u : ℝ, (fun x : ℝ => q x * testDensity ((x - c) / ε)) (ε * u + c)
      = q (c + ε * u) * testDensity u := by
    intro u
    simp only
    rw [show ε * u + c = c + ε * u by ring,
      show c + ε * u - c = ε * u by ring, mul_div_cancel_left₀ u hε]
  simp_rw [hfun] at h
  exact h.symm

/-- **The `q`-limit of the trapezoidal density.**  For `q` continuous and
`0 ≤ c < 1`, the scaled bump `ε⁻¹ ω((·-c)/ε)` is a one-sided approximate identity on
`[0,1]`, so `∫_0^1 q x · ε⁻¹ ω((x-c)/ε) → q c`.  This is the weighted-average step (Q)
of the book's Lemma 11.3.7 proof. -/
theorem tendsto_integral_scaled_testDensity (q : ℝ → ℝ) (hq : Continuous q) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) :
    Tendsto (fun ε : ℝ => ∫ x in (0 : ℝ)..1, q x * (ε⁻¹ * testDensity ((x - c) / ε)))
      (𝓝[>] (0 : ℝ)) (𝓝 (q c)) := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hq.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (q c)) (hM c ⟨hc0, by linarith⟩)
  have hint : Integrable (fun u : ℝ => M * testDensity u) volume :=
    (testDensity_continuous.integrable_of_hasCompactSupport
      testDensity_hasCompactSupport).const_mul M
  have hmeas : ∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable
      (fun u : ℝ => testDensity u * q (c + ε * u)) volume :=
    Filter.Eventually.of_forall fun ε =>
      (testDensity_continuous.mul (hq.comp (by fun_prop))).aestronglyMeasurable
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ u ∂volume,
      ‖testDensity u * q (c + ε * u)‖ ≤ M * testDensity u := by
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 2 - c by linarith)] with ε hε
    filter_upwards with u
    by_cases hu : testDensity u = 0
    · simp [hu]
    · have hu01 := testDensity_support_subset (Function.mem_support.mpr hu)
      have hcu : c + ε * u ∈ Icc (0 : ℝ) 2 := by
        constructor
        · nlinarith [hc0, hε.1.le, hu01.1.le]
        · nlinarith [hε.1.le, hε.2, hu01.1.le, hu01.2.le, hc1.le]
      have hqM := hM _ hcu
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (testDensity_nonneg u),
        mul_comm M (testDensity u)]
      exact mul_le_mul_of_nonneg_left hqM (testDensity_nonneg u)
  have hlim : ∀ᵐ u ∂volume, Tendsto (fun ε : ℝ => testDensity u * q (c + ε * u))
      (𝓝[>] (0 : ℝ)) (𝓝 (testDensity u * q c)) := by
    filter_upwards with u
    have h1 : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have harg : Tendsto (fun ε : ℝ => c + ε * u) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
      simpa using tendsto_const_nhds.add (h1.mul_const u)
    exact tendsto_const_nhds.mul (hq.continuousAt.tendsto.comp harg)
  have hDCT := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := 𝓝[>] (0 : ℝ))
    (F := fun ε u => testDensity u * q (c + ε * u))
    (f := fun u => testDensity u * q c)
    (bound := fun u => M * testDensity u) hmeas hbound hint hlim
  have hval : (∫ u, testDensity u * q c) = q c := by
    rw [MeasureTheory.integral_mul_const, testDensity_integral, one_mul]
  rw [hval] at hDCT
  refine hDCT.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 - c by linarith)] with ε hε
  rw [show (∫ x in (0 : ℝ)..1, q x * (ε⁻¹ * testDensity ((x - c) / ε)))
      = ε⁻¹ * ∫ x in (0 : ℝ)..1, q x * testDensity ((x - c) / ε) from by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro x _
        ring]
  rw [integral_scaled_testDensity_mul q c ε hε.1.ne',
    intervalIntegral.integral_eq_integral_of_support_subset (μ := volume) ?_]
  · apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    ring
  · intro u hu
    rw [Function.mem_support] at hu
    have hu' : testDensity u ≠ 0 := fun h => hu (by rw [h, mul_zero])
    have hu01 := testDensity_support_subset (Function.mem_support.mpr hu')
    rw [mem_Ioc]
    constructor
    · have hle : -c / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.1.le
      linarith [hu01.1]
    · have h1c : 1 ≤ (1 - c) / ε := by
        rw [le_div_iff₀ hε.1]
        linarith [hε.2]
      linarith [hu01.2]

end

end DuBoisReymond

namespace DuBoisReymond

noncomputable section

/-- **The `q`-limit of the trapezoidal density.** -/
theorem tendsto_integral_testTrapezoidDensity (q : ℝ → ℝ) (hq : Continuous q) {a b : ℝ}
    (hab : a ≤ b) (ha : 0 ≤ a) (hb : b < 1) :
    Tendsto (fun ε : ℝ => ∫ x in (0 : ℝ)..1, q x * testTrapezoidDensity a b ε x)
      (𝓝[>] (0 : ℝ)) (𝓝 (q a - q b)) := by
  have h1 := tendsto_integral_scaled_testDensity q hq ha (lt_of_le_of_lt hab hb)
  have h2 := tendsto_integral_scaled_testDensity q hq (le_trans ha hab) hb
  have hfun : (fun ε : ℝ => ∫ x in (0 : ℝ)..1, q x * testTrapezoidDensity a b ε x)
      = (fun ε : ℝ => ∫ x in (0 : ℝ)..1, q x * (ε⁻¹ * testDensity ((x - a) / ε)))
        - (fun ε : ℝ => ∫ x in (0 : ℝ)..1, q x * (ε⁻¹ * testDensity ((x - b) / ε))) := by
    funext ε
    rw [Pi.sub_apply,
      show (∫ x in (0 : ℝ)..1, q x * testTrapezoidDensity a b ε x)
        = ∫ x in (0 : ℝ)..1, (q x * (ε⁻¹ * testDensity ((x - a) / ε))
            - q x * (ε⁻¹ * testDensity ((x - b) / ε))) from by
          apply intervalIntegral.integral_congr
          intro x _
          unfold testTrapezoidDensity
          ring,
      intervalIntegral.integral_sub]
    · exact (hq.mul (continuous_const.mul
        (testDensity_continuous.comp (by fun_prop)))).intervalIntegrable 0 1
    · exact (hq.mul (continuous_const.mul
        (testDensity_continuous.comp (by fun_prop)))).intervalIntegrable 0 1
  rw [hfun]
  exact h1.sub h2

/-- **Lemma 11.3.7 (nonnegative endpoint-vanishing test functions).**  Let
`p ∈ L¹(0,1)` and `q` continuous.  If

  `∫_0^1 (p w + q w') ≥ 0`

for every nonnegative test function `w` with `w(0) = w(1) = 0` — rendered here, as in the
book's own first variation (11.3.20), through the absolutely continuous primitive
`w(t) = ∫_0^t ψ` — then `T(t) = q(t) − ∫_0^t p` is nonincreasing on `[0,1]`.

The test class is the primitive class of (11.3.20); the book states it for piecewise `C¹`
test functions, which is contained in this class, so the formal hypothesis is the one
actually supplied by the first variation.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012),
Lemma 11.3.7. -/
theorem antitone_of_nonnegative_endpointVanishing_test
    {p q : ℝ → ℝ}
    (hp : IntervalIntegrable p volume 0 1)
    (hq : Continuous q)
    (htest : ∀ ψ : ℝ → ℝ, IntervalIntegrable ψ volume 0 1 →
      (∫ t in (0 : ℝ)..1, ψ t) = 0 →
      (∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ ∫ s in (0 : ℝ)..t, ψ s) →
      0 ≤ ∫ t in (0 : ℝ)..1, (p t * (∫ s in (0 : ℝ)..t, ψ s) + q t * ψ t)) :
    AntitoneOn (fun t => q t - ∫ s in (0 : ℝ)..t, p s) (Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  rcases eq_or_lt_of_le hab with rfl | hlt
  · rfl
  have hpIoc : IntegrableOn p (Ioc (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp hp
  have hp_sub : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ 1 → IntervalIntegrable p volume x y := by
    intro x y hx hxy hy
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hxy).mpr
      (hpIoc.mono_set fun z hz => ⟨lt_of_le_of_lt hx hz.1, le_trans hz.2 hy⟩)
  have hf_cont : ContinuousOn (fun t => q t - ∫ s in (0 : ℝ)..t, p s) (Icc (0 : ℝ) 1) := by
    have h := hq.continuousOn.sub (intervalIntegral.continuousOn_primitive_interval' hp
      (a := (0 : ℝ)) left_mem_uIcc)
    rw [uIcc_of_le zero_le_one] at h
    exact h
  have hinner : ∀ b' ∈ Ioo a 1,
      q b' - ∫ s in (0 : ℝ)..b', p s ≤ q a - ∫ s in (0 : ℝ)..a, p s := by
    intro b' hb'mem
    have ha_lt_b' : a < b' := hb'mem.1
    have hb'_lt_1 : b' < 1 := hb'mem.2
    have hεbound : 0 < 1 - b' := by linarith
    have hb'0 : 0 ≤ b' := le_trans ha.1 ha_lt_b'.le
    have hineq : ∀ ε ∈ Ioc (0 : ℝ) (1 - b'),
        0 ≤ ∫ x in (0 : ℝ)..1,
          (p x * testTrapezoid a b' ε x + q x * testTrapezoidDensity a b' ε x) := by
      intro ε hε
      have hεpos : 0 < ε := hε.1
      have hεle : ε ≤ 1 - b' := hε.2
      have hzero : (∫ t in (0 : ℝ)..1, testTrapezoidDensity a b' ε t) = 0 := by
        rw [integral_testTrapezoidDensity ha.1 hb'0 hεpos, testTrapezoid,
          testCumulative_one_of_one_le (show 1 ≤ (1 - a) / ε by
            rw [le_div_iff₀ hεpos]; linarith),
          testCumulative_one_of_one_le (show 1 ≤ (1 - b') / ε by
            rw [le_div_iff₀ hεpos]; linarith)]
        ring
      have hnonneg : ∀ t ∈ Icc (0 : ℝ) 1,
          0 ≤ ∫ s in (0 : ℝ)..t, testTrapezoidDensity a b' ε s := by
        intro t _
        rw [integral_testTrapezoidDensity ha.1 hb'0 hεpos]
        exact testTrapezoid_nonneg (le_of_lt ha_lt_b') hεpos t
      have hres := htest (testTrapezoidDensity a b' ε)
        ((testTrapezoidDensity_continuous hεpos.ne').intervalIntegrable 0 1) hzero hnonneg
      simpa only [integral_testTrapezoidDensity ha.1 hb'0 hεpos] using hres
    have hlim := (tendsto_integral_testTrapezoid p hpIoc (le_of_lt ha_lt_b') ha.1
        hb'_lt_1.le).add
      (tendsto_integral_testTrapezoidDensity q hq (le_of_lt ha_lt_b') ha.1 hb'_lt_1)
    have hnonneg : 0 ≤ (∫ x in a..b', p x) + (q a - q b') := by
      refine ge_of_tendsto hlim ?_
      filter_upwards [Ioc_mem_nhdsGT hεbound] with ε hε
      have h0 := hineq ε hε
      have h1 : IntervalIntegrable (fun x => p x * testTrapezoid a b' ε x) volume 0 1 :=
        hp.mul_continuousOn (testTrapezoid_continuous a b' ε).continuousOn
      have h2 : IntervalIntegrable (fun x => q x * testTrapezoidDensity a b' ε x) volume 0 1 :=
        (hq.mul (testTrapezoidDensity_continuous hε.1.ne')).intervalIntegrable 0 1
      rw [intervalIntegral.integral_add h1 h2] at h0
      exact h0
    have hsplit : (∫ x in (0 : ℝ)..b', p x) =
        (∫ x in (0 : ℝ)..a, p x) + ∫ x in a..b', p x :=
      (intervalIntegral.integral_add_adjacent_intervals (hp_sub 0 a le_rfl ha.1 ha.2)
        (hp_sub a b' ha.1 (le_of_lt ha_lt_b') hb'_lt_1.le)).symm
    linarith
  rcases lt_or_eq_of_le hb.2 with hb1 | hb1
  · exact hinner b ⟨hlt, hb1⟩
  · subst hb1
    have hsub : Ioo a 1 ⊆ Icc (0 : ℝ) 1 := fun s hs => ⟨le_trans ha.1 hs.1.le, hs.2.le⟩
    have htend : Tendsto (fun t => q t - ∫ s in (0 : ℝ)..t, p s) (𝓝[Ioo a 1] (1 : ℝ))
        (𝓝 (q 1 - ∫ s in (0 : ℝ)..1, p s)) :=
      (hf_cont 1 ⟨zero_le_one, le_rfl⟩).mono_left (nhdsWithin_mono _ hsub)
    refine le_of_tendsto (x := 𝓝[Ioo a 1] (1 : ℝ)) (hx := right_nhdsWithin_Ioo_neBot hlt)
      htend ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hinner s hs

end

end DuBoisReymond
