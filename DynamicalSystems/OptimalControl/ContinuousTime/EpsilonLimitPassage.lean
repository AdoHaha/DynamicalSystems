/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.BoundedVariation.HellySelection
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The `ε → 0` limiting operations of §11.4: Helly, normalisation, passage to the limit

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), §11.4 (Remarks 11.4.2–11.4.3,
(11.4.1)–(11.4.5), (11.4.14)–(11.4.16)) and Theorem 11.4.4 / 11.6.3.

For each `ε` the `j → ∞` limit (`StatePenalisedTubeLimit.lean`) delivers a nonincreasing multiplier
`λ(ε;·) ≥ 0` with `λ(ε;t₁) = 0` and a costate `Φ(ε;·)` solving the *linear* integral equation
(11.6.11)/(11.3.25)

`Φ' = f⁰ₓ − (Φ − λ∇G − 2(φ_ε' − φ₀'))·fₓ + λ d(∇G)/dt`

with the boundary relations (11.3.33)–(11.3.34).  This file runs the §11.4 limiting operations on
such a family: normalise by `M(ε) = 1 + |Φ(ε;t₁)| + λ(ε;0⁺) + |β_ε|` (11.4.3), bound `Φ/M` and its
variation uniformly by a Gronwall estimate (11.4.1)–(11.4.2), extract a pointwise-convergent
subsequence by Helly's selection theorem (11.4.4)–(11.4.5) and pass to the limit in the integral
equation (11.4.14)–(11.4.16), obtaining the conclusions (i)–(iv) of Theorem 11.4.4 in the
absolutely continuous (measure-free) form of the adjoint law.

* `EpsilonCostateSystem`: the data of one `ε`;  `IsEpsilonCostateSystem`: its equations.
* `exists_limit_of_epsilonCostateSystems`: the limiting operations.

Book citations live in docstrings only.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology Interval ENNReal

namespace OptimalControl.BoundedState

/-- The data of the `ε`-level costate system on `[0,T]`: the costate `Φ(ε;·)` and multiplier
`λ(ε;·)`; the endpoint multiplier `β_ε`; the cost covector `f⁰ₓ` along the `ε`-path (`cx`), the
covector action `A t = (·)∘fₓ(t)` of the dynamics derivative, `∇G` along the path (`g`) and its
total derivative `d(∇G)/dt` (`gd`), the velocity-defect covector `2⟨φ_ε' − φ₀',·⟩` (`defect`), the
covector `ι` of the initial penalty and the endpoint-multiplier operators `Dl, Dr` (`∂₁T, ∂₂T`).

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.25), (11.3.33),
(11.3.34). -/
structure EpsilonCostateSystem (X Y : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] where
  /-- The costate `Φ(ε;·)`. -/
  Φ : ℝ → X
  /-- The multiplier `λ(ε;·)`. -/
  lam : ℝ → ℝ
  /-- The endpoint multiplier `β_ε`. -/
  β : Y
  /-- The cost covector `f⁰ₓ` along the `ε`-path. -/
  cx : ℝ → X
  /-- The covector action `Φ ↦ Φ·fₓ` of the dynamics derivative along the `ε`-path. -/
  A : ℝ → X →L[ℝ] X
  /-- `∇G` along the `ε`-path. -/
  g : ℝ → X
  /-- `d(∇G)/dt` along the `ε`-path. -/
  gd : ℝ → X
  /-- The velocity-defect covector `2⟨φ_ε' − φ₀', ·⟩`. -/
  defect : ℝ → X
  /-- The covector of the initial penalty `2⟨φ_ε(0) − φ₀(0), ·⟩`. -/
  ι : X
  /-- The covector map of the initial constraint (`β ↦ β·∂₁T`). -/
  Dl : Y →L[ℝ] X
  /-- The covector map of the terminal constraint (`β ↦ β·∂₂T`). -/
  Dr : Y →L[ℝ] X

namespace EpsilonCostateSystem

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The normalising constant `M(ε) = 1 + |Φ(ε;T)| + λ(ε;0) + |β_ε|` of (11.4.3). -/
noncomputable def norm' (s : EpsilonCostateSystem X Y) (T : ℝ) : ℝ :=
  1 + ‖s.Φ T‖ + s.lam 0 + ‖s.β‖

end EpsilonCostateSystem

/-- The equations of the `ε`-level costate system (11.3.25), (11.3.33), (11.3.34), (11.6.11):

* `Φ' = cx − A(Φ − λ g − defect) + λ gd` in integrated form on `[0,T]`;
* `Φ(0) = ι + β·∂₁T + λ(0) ∇G(0)`, `Φ(T) = −β·∂₂T`;
* `λ` nonincreasing, nonnegative, `λ(T) = 0`;
* integrability / measurability of the data (needed because Bochner integrals of non-integrable
  functions are `0` by convention, which would make the `L¹` convergence hypotheses vacuous).

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.25), (11.3.33),
(11.3.34). -/
structure IsEpsilonCostateSystem {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (T : ℝ) (s : EpsilonCostateSystem X Y) : Prop where
  integrable_cx : IntervalIntegrable s.cx volume 0 T
  integrable_gd : IntervalIntegrable s.gd volume 0 T
  integrable_defect_vec : IntervalIntegrable s.defect volume 0 T
  integrable_defect : IntervalIntegrable (fun r => s.A r (s.defect r)) volume 0 T
  measurable_A : AEStronglyMeasurable s.A (volume.restrict (Ioc (0 : ℝ) T))
  measurable_g : AEStronglyMeasurable s.g (volume.restrict (Ioc (0 : ℝ) T))
  integrable_A : IntervalIntegrable (fun r => s.A r (s.Φ r - s.lam r • s.g r)) volume 0 T
  integrable_lam_gd : IntervalIntegrable (fun r => s.lam r • s.gd r) volume 0 T
  eq_integral : ∀ t ∈ Icc (0 : ℝ) T, s.Φ t = s.Φ 0 + ∫ r in (0 : ℝ)..t,
    (s.cx r - s.A r (s.Φ r - s.lam r • s.g r) + s.A r (s.defect r) + s.lam r • s.gd r)
  initial : s.Φ 0 = s.ι + s.Dl s.β + s.lam 0 • s.g 0
  terminal : s.Φ T = -(s.Dr s.β)
  antitone : AntitoneOn s.lam (Icc (0 : ℝ) T)
  nonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ s.lam t
  lam_horizon : s.lam T = 0

section Auxiliary

/-! ### Auxiliary lemmas: variation of primitives, a backward Grönwall inequality, `L¹` limits -/

/-- Comparison of variations: if `f` moves (in `edist`) at most as much as `g` between any two
points of `s`, then the variation of `f` on `s` is at most that of `g`. -/
theorem eVariationOn_le_of_edist_le {α E F : Type*} [LinearOrder α] [PseudoEMetricSpace E]
    [PseudoEMetricSpace F] {f : α → E} {g : α → F} {s : Set α}
    (h : ∀ x ∈ s, ∀ y ∈ s, edist (f x) (f y) ≤ edist (g x) (g y)) :
    eVariationOn f s ≤ eVariationOn g s :=
  iSup_mono fun p => Finset.sum_le_sum fun _ _ => h _ (p.2.2.2 _) _ (p.2.2.2 _)

/-- The variation of a primitive is at most the `L¹` norm of the integrand. -/
theorem eVariationOn_le_integral_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f F : ℝ → E} {T : ℝ} (hT : 0 ≤ T) (hF : IntervalIntegrable F volume 0 T)
    (hf : ∀ t ∈ Icc (0 : ℝ) T, f t = f 0 + ∫ r in (0 : ℝ)..t, F r) :
    eVariationOn f (Icc 0 T) ≤ ENNReal.ofReal (∫ r in (0 : ℝ)..T, ‖F r‖) := by
  set G : ℝ → ℝ := fun x => ∫ r in (0 : ℝ)..x, ‖F r‖ with hG
  have hGi : ∀ x ∈ Icc (0 : ℝ) T, ∀ y ∈ Icc (0 : ℝ) T, IntervalIntegrable F volume x y :=
    fun x hx y hy => hF.mono_set (uIcc_subset_uIcc (by rwa [uIcc_of_le hT])
      (by rwa [uIcc_of_le hT]))
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hdiff : ∀ x ∈ Icc (0 : ℝ) T, ∀ y ∈ Icc (0 : ℝ) T,
      G y - G x = ∫ r in x..y, ‖F r‖ := fun x hx y hy =>
    intervalIntegral.integral_interval_sub_left (hGi 0 h0 y hy).norm (hGi 0 h0 x hx).norm
  have hmono : MonotoneOn G (Icc 0 T) := by
    intro x hx y hy hxy
    have := hdiff x hx y hy
    have : 0 ≤ ∫ r in x..y, ‖F r‖ :=
      intervalIntegral.integral_nonneg hxy fun _ _ => norm_nonneg _
    linarith
  have hle : ∀ x ∈ Icc (0 : ℝ) T, ∀ y ∈ Icc (0 : ℝ) T, x ≤ y →
      dist (f x) (f y) ≤ dist (G x) (G y) := by
    intro x hx y hy hxy
    have hfxy : f y - f x = ∫ r in x..y, F r := by
      rw [hf y hy, hf x hx, add_sub_add_left_eq_sub]
      exact intervalIntegral.integral_interval_sub_left (hGi 0 h0 y hy) (hGi 0 h0 x hx)
    rw [dist_comm, dist_eq_norm, hfxy, Real.dist_eq, abs_sub_comm, hdiff x hx y hy]
    exact (intervalIntegral.norm_integral_le_integral_norm hxy).trans (le_abs_self _)
  calc eVariationOn f (Icc 0 T) ≤ eVariationOn G (Icc 0 T) := by
        refine eVariationOn_le_of_edist_le fun x hx y hy => ?_
        rw [edist_dist, edist_dist]
        refine ENNReal.ofReal_le_ofReal ?_
        rcases le_total x y with hxy | hxy
        · exact hle x hx y hy hxy
        · rw [dist_comm, dist_comm (G x)]; exact hle y hy x hx hxy
    _ = ENNReal.ofReal (G T - G 0) := by
        rw [← hmono.eVariationOn_eq h0 ⟨hT, le_rfl⟩, inter_self]
    _ = ENNReal.ofReal (∫ r in (0 : ℝ)..T, ‖F r‖) := by
        simp [hG]

/-- A backward integral Grönwall inequality: if `u` is continuous on `[0,T]` and
`u t ≤ K + C ∫ₜᵀ u`, then `u t ≤ K e^{CT}` on `[0,T]`. -/
theorem le_of_integral_gronwall_backward {u : ℝ → ℝ} {K C T : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (hK : 0 ≤ K) (hu : ContinuousOn u (Icc 0 T))
    (h : ∀ t ∈ Icc (0 : ℝ) T, u t ≤ K + C * ∫ r in t..T, u r) :
    ∀ t ∈ Icc (0 : ℝ) T, u t ≤ K * Real.exp (C * T) := by
  set v : ℝ → ℝ := fun x => u (max 0 (min x T)) with hvdef
  have hcl : ∀ x, max 0 (min x T) ∈ Icc (0 : ℝ) T := fun x =>
    ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hv : Continuous v :=
    hu.comp_continuous (continuous_const.max (continuous_id.min continuous_const)) hcl
  have hvu : ∀ x ∈ Icc (0 : ℝ) T, v x = u x := fun x hx => by
    simp only [hvdef, min_eq_left hx.2, max_eq_right hx.1]
  have hint : ∀ t ∈ Icc (0 : ℝ) T, ∫ r in t..T, u r = ∫ r in t..T, v r := fun t ht =>
    intervalIntegral.integral_congr fun r hr => by
      rw [uIcc_of_le ht.2] at hr
      exact (hvu r ⟨ht.1.trans hr.1, hr.2⟩).symm
  set f : ℝ → ℝ := fun x => K + C * ∫ r in (T - x)..T, v r with hfdef
  have hf : ∀ x, HasDerivAt f (C * v (T - x)) x := by
    intro x
    have h1 : HasDerivAt (fun x => ∫ r in T..(T - x), v r) (v (T - x) * (-1)) x :=
      ((hv.integral_hasStrictDerivAt T (T - x)).hasDerivAt).comp x
        ((hasDerivAt_id x).const_sub T)
    have h2 : f = fun x => K + C * -(∫ r in T..(T - x), v r) := by
      funext x
      change K + C * ∫ r in (T - x)..T, v r = _
      rw [intervalIntegral.integral_symm T (T - x)]
    rw [h2]
    convert (h1.neg.const_mul C).const_add K using 1
    ring
  have key := le_gronwallBound_of_liminf_deriv_right_le (f := f)
    (f' := fun x => C * v (T - x)) (δ := K) (K := C) (ε := 0) (a := 0) (b := T)
    (fun x _ => (hf x).continuousAt.continuousWithinAt)
    (fun x _ r hr => by
      simpa [slope_def_field, div_eq_inv_mul] using
        ((hf x).hasDerivWithinAt.liminf_right_slope_le hr))
    (by simp [hfdef])
    (fun x hx => by
      have hx' : T - x ∈ Icc (0 : ℝ) T := ⟨by linarith [hx.2], by linarith [hx.1]⟩
      have h3 := h (T - x) hx'
      rw [hint _ hx'] at h3
      simp only [hvu _ hx', add_zero, hfdef]
      exact mul_le_mul_of_nonneg_left h3 hC)
  intro t ht
  have ht' : T - t ∈ Icc (0 : ℝ) T := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h2 := key (T - t) ht'
  rw [gronwallBound_ε0, sub_zero] at h2
  calc u t ≤ f (T - t) := by
        simp only [hfdef, sub_sub_cancel]; rw [← hint t ht]; exact h t ht
    _ ≤ K * Real.exp (C * (T - t)) := h2
    _ ≤ K * Real.exp (C * T) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith [ht.1]) hC)) hK

/-- Interval integrability on `[0,T]` from an a.e.-strongly measurable function dominated by an
interval integrable one. -/
theorem intervalIntegrable_of_norm_le {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    {g : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hg : IntervalIntegrable g volume 0 T)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioc 0 T)))
    (hle : ∀ r ∈ Ioc (0 : ℝ) T, ‖f r‖ ≤ g r) : IntervalIntegrable f volume 0 T :=
  hg.mono_fun' (by rwa [uIoc_of_le hT])
    (by rw [uIoc_of_le hT]; exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ hle))

/-- `L¹` convergence on `[0,T]` (controlled by majorants with vanishing integrals) gives
convergence of all the integrals `∫₀ᵗ`, `t ∈ [0,T]`. -/
theorem tendsto_intervalIntegral_of_norm_sub_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {T : ℝ} (hT : 0 ≤ T) {f : ℕ → ℝ → E} {f₀ : ℝ → E}
    (hf : ∀ k, IntervalIntegrable (f k) volume 0 T) (hf₀ : IntervalIntegrable f₀ volume 0 T)
    {b : ℕ → ℝ → ℝ} (hb : ∀ k, IntervalIntegrable (b k) volume 0 T)
    (hle : ∀ k, ∀ r ∈ Ioc (0 : ℝ) T, ‖f k r - f₀ r‖ ≤ b k r)
    (hlim : Tendsto (fun k => ∫ r in (0 : ℝ)..T, b k r) atTop (𝓝 0)) :
    ∀ t ∈ Icc (0 : ℝ) T,
      Tendsto (fun k => ∫ r in (0 : ℝ)..t, f k r) atTop (𝓝 (∫ r in (0 : ℝ)..t, f₀ r)) := by
  intro t ht
  have hsub : uIcc 0 t ⊆ uIcc 0 T :=
    uIcc_subset_uIcc left_mem_uIcc (by rw [uIcc_of_le hT]; exact ht)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hlim
  rw [← intervalIntegral.integral_sub ((hf k).mono_set hsub) (hf₀.mono_set hsub)]
  calc _ ≤ ∫ r in (0 : ℝ)..t, b k r :=
        intervalIntegral.norm_integral_le_of_norm_le ht.1
          (ae_of_all _ fun r hr => hle k r ⟨hr.1, hr.2.trans ht.2⟩) ((hb k).mono_set hsub)
    _ ≤ ∫ r in (0 : ℝ)..T, b k r :=
        intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
          ((ae_restrict_iff' measurableSet_Ioc).2
            (ae_of_all _ fun r hr => (norm_nonneg _).trans (hle k r hr))) (hb k)

/-- Dominated convergence to `0` on `[0,T]` for real functions. -/
theorem tendsto_intervalIntegral_zero_of_dominated {T : ℝ} (hT : 0 ≤ T) {h : ℕ → ℝ → ℝ}
    {M : ℝ → ℝ} (hm : ∀ k, AEStronglyMeasurable (h k) (volume.restrict (Ioc 0 T)))
    (hbd : ∀ k, ∀ r ∈ Ioc (0 : ℝ) T, ‖h k r‖ ≤ M r) (hM : IntervalIntegrable M volume 0 T)
    (hlim : ∀ r ∈ Ioc (0 : ℝ) T, Tendsto (fun k => h k r) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ r in (0 : ℝ)..T, h k r) atTop (𝓝 0) := by
  have := intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (a := 0) (b := T) (l := atTop) (f := fun _ => (0 : ℝ)) M
    (Eventually.of_forall fun k => by rw [uIoc_of_le hT]; exact hm k)
    (Eventually.of_forall fun k => ae_of_all _ fun r hr => by
      rw [uIoc_of_le hT] at hr; exact hbd k r hr) hM
    (ae_of_all _ fun r hr => by rw [uIoc_of_le hT] at hr; exact hlim r hr)
  simpa using this

end Auxiliary

namespace EpsilonCostateSystem

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The integrand `cx − A(Φ − λ g − defect) + λ gd` of the `ε`-level adjoint equation. -/
noncomputable def adj (s : EpsilonCostateSystem X Y) (r : ℝ) : X :=
  s.cx r - s.A r (s.Φ r - s.lam r • s.g r) + s.A r (s.defect r) + s.lam r • s.gd r

end EpsilonCostateSystem

namespace IsEpsilonCostateSystem

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] {T : ℝ} {s : EpsilonCostateSystem X Y}

theorem one_le_norm' (hs : IsEpsilonCostateSystem T s) (hT : 0 ≤ T) : 1 ≤ s.norm' T := by
  have := hs.nonneg 0 ⟨le_rfl, hT⟩
  unfold EpsilonCostateSystem.norm'
  linarith [norm_nonneg (s.Φ T), norm_nonneg s.β]

theorem inv_norm'_pos (hs : IsEpsilonCostateSystem T s) (hT : 0 ≤ T) :
    0 < 1 / s.norm' T :=
  one_div_pos.2 (by linarith [hs.one_le_norm' hT])

theorem inv_norm'_le_one (hs : IsEpsilonCostateSystem T s) (hT : 0 ≤ T) :
    1 / s.norm' T ≤ 1 :=
  (div_le_one (by linarith [hs.one_le_norm' hT])).2 (hs.one_le_norm' hT)

theorem normalised_lam_mem (hs : IsEpsilonCostateSystem T s) (hT : 0 ≤ T) :
    ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ 1 / s.norm' T * s.lam t ∧ 1 / s.norm' T * s.lam t ≤ 1 := by
  intro t ht
  have hpos := hs.one_le_norm' hT
  have h0 : s.lam t ≤ s.lam 0 := hs.antitone ⟨le_rfl, hT⟩ ht ht.1
  have hl0 : s.lam 0 ≤ s.norm' T := by
    unfold EpsilonCostateSystem.norm'
    linarith [norm_nonneg (s.Φ T), norm_nonneg s.β]
  refine ⟨mul_nonneg (hs.inv_norm'_pos hT).le (hs.nonneg t ht), ?_⟩
  rw [one_div, inv_mul_le_iff₀ (by linarith)]
  linarith

theorem normalised_sum (hs : IsEpsilonCostateSystem T s) (hT : 0 ≤ T) :
    1 / s.norm' T + ‖(1 / s.norm' T) • s.Φ T‖ + 1 / s.norm' T * s.lam 0 +
      ‖(1 / s.norm' T) • s.β‖ = 1 := by
  have hpos : 0 < s.norm' T := by linarith [hs.one_le_norm' hT]
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (hs.inv_norm'_pos hT).le]
  have key : 1 / s.norm' T * s.norm' T = 1 := one_div_mul_cancel hpos.ne'
  have hdef : s.norm' T = 1 + ‖s.Φ T‖ + s.lam 0 + ‖s.β‖ := rfl
  linear_combination key - (1 / s.norm' T) * hdef

theorem integrable_adj (hs : IsEpsilonCostateSystem T s) :
    IntervalIntegrable s.adj volume 0 T :=
  ((hs.integrable_cx.sub hs.integrable_A).add hs.integrable_defect).add hs.integrable_lam_gd

theorem eq_integral_adj (hs : IsEpsilonCostateSystem T s) :
    ∀ t ∈ Icc (0 : ℝ) T, s.Φ t = s.Φ 0 + ∫ r in (0 : ℝ)..t, s.adj r :=
  hs.eq_integral

theorem normalised_eq_integral (hs : IsEpsilonCostateSystem T s) :
    ∀ t ∈ Icc (0 : ℝ) T, (1 / s.norm' T) • s.Φ t =
      (1 / s.norm' T) • s.Φ 0 + ∫ r in (0 : ℝ)..t, (1 / s.norm' T) • s.adj r := by
  intro t ht
  rw [intervalIntegral.integral_smul, ← smul_add, ← hs.eq_integral_adj t ht]

theorem continuousOn_Φ (hs : IsEpsilonCostateSystem T s) (hT : 0 ≤ T) :
    ContinuousOn s.Φ (Icc 0 T) := by
  have h := intervalIntegral.continuousOn_primitive_interval' hs.integrable_adj left_mem_uIcc
  rw [uIcc_of_le hT] at h
  exact (continuousOn_const.add h).congr fun t ht => hs.eq_integral_adj t ht

/-- The pointwise bound on the normalised integrand used in the Grönwall estimate (11.4.1). -/
theorem norm_smul_adj_le (hs : IsEpsilonCostateSystem T s) (hT : 0 ≤ T) {C : ℝ} (hC : 0 ≤ C)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) T) (hcx : ‖s.cx r‖ ≤ C) (hA : ‖s.A r‖ ≤ C)
    (hg : ‖s.g r‖ ≤ C) :
    ‖(1 / s.norm' T) • s.adj r‖ ≤
      (C + C * C + C * ‖s.defect r‖ + ‖s.gd r‖) + C * ‖(1 / s.norm' T) • s.Φ r‖ := by
  set m := 1 / s.norm' T with hm
  have hm0 : 0 < m := hs.inv_norm'_pos hT
  have hm1 : m ≤ 1 := hs.inv_norm'_le_one hT
  obtain ⟨hl0, hl1⟩ := hs.normalised_lam_mem hT r hr
  have heq : m • s.adj r = m • s.cx r - s.A r (m • s.Φ r - (m * s.lam r) • s.g r) +
      m • s.A r (s.defect r) + (m * s.lam r) • s.gd r := by
    simp only [EpsilonCostateSystem.adj, smul_add, smul_sub, map_sub, map_smul, smul_smul]
  rw [heq]
  have h1 : ‖m • s.cx r‖ ≤ C := by
    rw [norm_smul, Real.norm_of_nonneg hm0.le]; nlinarith [norm_nonneg (s.cx r)]
  have h2 : ‖s.A r (m • s.Φ r - (m * s.lam r) • s.g r)‖ ≤ C * ‖m • s.Φ r‖ + C * C := by
    calc _ ≤ ‖s.A r‖ * ‖m • s.Φ r - (m * s.lam r) • s.g r‖ := (s.A r).le_opNorm _
      _ ≤ C * (‖m • s.Φ r‖ + C) := by
        refine mul_le_mul hA ?_ (norm_nonneg _) hC
        refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
        rw [norm_smul, Real.norm_of_nonneg hl0]; nlinarith [norm_nonneg (s.g r)]
      _ = _ := by ring
  have h3 : ‖m • s.A r (s.defect r)‖ ≤ C * ‖s.defect r‖ := by
    rw [norm_smul, Real.norm_of_nonneg hm0.le]
    calc m * ‖s.A r (s.defect r)‖ ≤ 1 * (‖s.A r‖ * ‖s.defect r‖) :=
          mul_le_mul hm1 ((s.A r).le_opNorm _) (norm_nonneg _) zero_le_one
      _ ≤ C * ‖s.defect r‖ := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_right hA (norm_nonneg _)
  have h4 : ‖(m * s.lam r) • s.gd r‖ ≤ ‖s.gd r‖ := by
    rw [norm_smul, Real.norm_of_nonneg hl0]; nlinarith [norm_nonneg (s.gd r)]
  have e1 := norm_add_le (m • s.cx r - s.A r (m • s.Φ r - (m * s.lam r) • s.g r) +
      m • s.A r (s.defect r)) ((m * s.lam r) • s.gd r)
  have e2 := norm_add_le (m • s.cx r - s.A r (m • s.Φ r - (m * s.lam r) • s.g r))
      (m • s.A r (s.defect r))
  have e3 := norm_sub_le (m • s.cx r) (s.A r (m • s.Φ r - (m * s.lam r) • s.g r))
  linarith

/-- **Uniform bounds (11.4.1)–(11.4.2)** for one normalised system: a Grönwall bound on
`‖Φ/M‖` and the induced bound on its variation. -/
theorem normalised_bounds (hs : IsEpsilonCostateSystem T s) (hT : 0 ≤ T) {C : ℝ} (hC : 0 ≤ C)
    (hcx : ∀ t ∈ Icc (0 : ℝ) T, ‖s.cx t‖ ≤ C) (hA : ∀ t ∈ Icc (0 : ℝ) T, ‖s.A t‖ ≤ C)
    (hg : ∀ t ∈ Icc (0 : ℝ) T, ‖s.g t‖ ≤ C) {K : ℝ}
    (hK : (C + C * C) * T + C * (∫ r in (0 : ℝ)..T, ‖s.defect r‖) +
      ∫ r in (0 : ℝ)..T, ‖s.gd r‖ ≤ K) :
    (∀ t ∈ Icc (0 : ℝ) T, ‖(1 / s.norm' T) • s.Φ t‖ ≤ (1 + K) * Real.exp (C * T)) ∧
      eVariationOn (fun t => (1 / s.norm' T) • s.Φ t) (Icc 0 T) ≤
        ENNReal.ofReal (K + C * (T * ((1 + K) * Real.exp (C * T)))) := by
  set m := 1 / s.norm' T with hm
  set φ : ℝ → X := fun t => m • s.Φ t with hφ
  set F : ℝ → X := fun r => m • s.adj r with hF
  set bf : ℝ → ℝ := fun r => (C + C * C) + C * ‖s.defect r‖ + ‖s.gd r‖ with hbf
  have hFi : IntervalIntegrable F volume 0 T := hs.integrable_adj.smul m
  have hbfi : IntervalIntegrable bf volume 0 T :=
    (intervalIntegrable_const.add (hs.integrable_defect_vec.norm.const_mul C)).add
      hs.integrable_gd.norm
  have hφeq : ∀ t ∈ Icc (0 : ℝ) T, φ t = φ 0 + ∫ r in (0 : ℝ)..t, F r :=
    hs.normalised_eq_integral
  have hφc : ContinuousOn φ (Icc 0 T) := (hs.continuousOn_Φ hT).const_smul m
  have hbd : ∀ r ∈ Icc (0 : ℝ) T, ‖F r‖ ≤ bf r + C * ‖φ r‖ := fun r hr => by
    have := hs.norm_smul_adj_le hT hC hr (hcx r hr) (hA r hr) (hg r hr)
    simp only [hF, hbf, hφ]; linarith
  have hbf0 : ∀ r, 0 ≤ bf r := fun r => by
    simp only [hbf]; positivity
  have hbfint : ∫ r in (0 : ℝ)..T, bf r ≤ K := by
    have e : ∫ r in (0 : ℝ)..T, bf r = (C + C * C) * T + C * (∫ r in (0 : ℝ)..T, ‖s.defect r‖) +
        ∫ r in (0 : ℝ)..T, ‖s.gd r‖ := by
      simp only [hbf]
      rw [intervalIntegral.integral_add (intervalIntegrable_const.add
          (hs.integrable_defect_vec.norm.const_mul C)) hs.integrable_gd.norm,
        intervalIntegral.integral_add intervalIntegrable_const
          (hs.integrable_defect_vec.norm.const_mul C),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
      ring
    linarith
  have hK0 : 0 ≤ K := (intervalIntegral.integral_nonneg hT fun r _ => hbf0 r).trans hbfint
  have hφT : ‖φ T‖ ≤ 1 := by
    have := hs.normalised_sum hT
    have h1 := (hs.inv_norm'_pos hT).le
    have h2 := (hs.normalised_lam_mem hT 0 ⟨le_rfl, hT⟩).1
    have h3 := norm_nonneg ((1 / s.norm' T) • s.β)
    simp only [hφ, hm]; linarith
  have hsub : ∀ t ∈ Icc (0 : ℝ) T, uIcc t T ⊆ Icc 0 T := fun t ht => by
    rw [uIcc_of_le ht.2]; exact Icc_subset_Icc ht.1 le_rfl
  have hnφi : ∀ t ∈ Icc (0 : ℝ) T, IntervalIntegrable (fun r => ‖φ r‖) volume t T :=
    fun t ht => ((continuous_norm.comp_continuousOn hφc).mono (hsub t ht)).intervalIntegrable
  have hbfi' : ∀ t ∈ Icc (0 : ℝ) T, IntervalIntegrable bf volume t T := fun t ht =>
    hbfi.mono_set (by rw [uIcc_of_le hT]; exact hsub t ht)
  have hB : ∀ t ∈ Icc (0 : ℝ) T, ‖φ t‖ ≤ (1 + K) * Real.exp (C * T) := by
    refine le_of_integral_gronwall_backward (u := fun t => ‖φ t‖) hT hC (by linarith)
      (continuous_norm.comp_continuousOn hφc) fun t ht => ?_
    have hT' : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
    have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
    have hFi' : ∀ x ∈ Icc (0 : ℝ) T, IntervalIntegrable F volume 0 x := fun x hx =>
      hFi.mono_set (uIcc_subset_uIcc left_mem_uIcc (by rw [uIcc_of_le hT]; exact hx))
    have hrep : φ t = φ T - ∫ r in t..T, F r := by
      rw [← intervalIntegral.integral_interval_sub_left (hFi' T hT') (hFi' t ht), hφeq T hT',
        hφeq t ht]
      abel
    have hint : ‖∫ r in t..T, F r‖ ≤ ∫ r in t..T, (bf r + C * ‖φ r‖) :=
      intervalIntegral.norm_integral_le_of_norm_le ht.2
        (ae_of_all _ fun r hr => hbd r ⟨ht.1.trans hr.1.le, hr.2⟩)
        ((hbfi' t ht).add ((hnφi t ht).const_mul C))
    rw [intervalIntegral.integral_add (hbfi' t ht) ((hnφi t ht).const_mul C),
      intervalIntegral.integral_const_mul] at hint
    have hbt : ∫ r in t..T, bf r ≤ ∫ r in (0 : ℝ)..T, bf r :=
      intervalIntegral.integral_mono_interval ht.1 ht.2 le_rfl (ae_of_all _ fun r => hbf0 r)
        hbfi
    have := norm_sub_le (φ T) (∫ r in t..T, F r)
    rw [← hrep] at this
    change ‖φ t‖ ≤ 1 + K + C * ∫ r in t..T, ‖φ r‖
    linarith
  refine ⟨hB, ?_⟩
  refine (eVariationOn_le_integral_norm hT hFi hφeq).trans (ENNReal.ofReal_le_ofReal ?_)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  calc ∫ r in (0 : ℝ)..T, ‖F r‖ ≤ ∫ r in (0 : ℝ)..T, (bf r + C * ‖φ r‖) :=
        intervalIntegral.integral_mono_on hT hFi.norm (hbfi.add ((hnφi 0 h0).const_mul C))
          fun r hr => hbd r hr
    _ = (∫ r in (0 : ℝ)..T, bf r) + C * ∫ r in (0 : ℝ)..T, ‖φ r‖ := by
        rw [intervalIntegral.integral_add hbfi ((hnφi 0 h0).const_mul C),
          intervalIntegral.integral_const_mul]
    _ ≤ K + C * (T * ((1 + K) * Real.exp (C * T))) := by
        have : ∫ r in (0 : ℝ)..T, ‖φ r‖ ≤ T * ((1 + K) * Real.exp (C * T)) := by
          calc ∫ r in (0 : ℝ)..T, ‖φ r‖ ≤ ∫ _ in (0 : ℝ)..T, (1 + K) * Real.exp (C * T) :=
                intervalIntegral.integral_mono_on hT (hnφi 0 h0) intervalIntegrable_const
                  fun r hr => hB r hr
            _ = _ := by simp; ring
        nlinarith

end IsEpsilonCostateSystem

section PassageIntegral

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- **Passage to the limit in the integrated adjoint equation (11.4.14)–(11.4.16).** If the
normalised costates and multipliers of a family of `ε`-level systems converge at every point of
`[0,T]` (and `1/M_k → λ⁰`), with a uniform bound `B` on the normalised costates, then the limits
satisfy the limiting adjoint law in integrated form; the limits are a.e.-strongly measurable and
the limiting integrand is interval integrable. -/
theorem integral_identity_of_tendsto {T : ℝ} (hT : 0 < T)
    (s : ℕ → EpsilonCostateSystem X Y) (hs : ∀ k, IsEpsilonCostateSystem T (s k))
    {C : ℝ} (hA : ∀ k, ∀ t ∈ Icc (0 : ℝ) T, ‖(s k).A t‖ ≤ C)
    (hg : ∀ k, ∀ t ∈ Icc (0 : ℝ) T, ‖(s k).g t‖ ≤ C)
    {cx₀ : ℝ → X} {A₀ : ℝ → X →L[ℝ] X} {g₀ gd₀ : ℝ → X}
    (hcx₀ : IntervalIntegrable cx₀ volume 0 T) (hgd₀ : IntervalIntegrable gd₀ volume 0 T)
    (hA₀m : AEStronglyMeasurable A₀ (volume.restrict (Ioc (0 : ℝ) T)))
    (hg₀m : AEStronglyMeasurable g₀ (volume.restrict (Ioc (0 : ℝ) T)))
    (hA₀ : ∀ t ∈ Icc (0 : ℝ) T, ‖A₀ t‖ ≤ C) (hg₀ : ∀ t ∈ Icc (0 : ℝ) T, ‖g₀ t‖ ≤ C)
    (hcxlim : Tendsto (fun k => ∫ r in (0 : ℝ)..T, ‖(s k).cx r - cx₀ r‖) atTop (𝓝 0))
    (hAlim : Tendsto (fun k => ∫ r in (0 : ℝ)..T, ‖(s k).A r - A₀ r‖) atTop (𝓝 0))
    (hgdlim : Tendsto (fun k => ∫ r in (0 : ℝ)..T, ‖(s k).gd r - gd₀ r‖) atTop (𝓝 0))
    (hdeflim : Tendsto (fun k => ∫ r in (0 : ℝ)..T, ‖(s k).defect r‖) atTop (𝓝 0))
    (hglim : ∀ t ∈ Icc (0 : ℝ) T, Tendsto (fun k => (s k).g t) atTop (𝓝 (g₀ t)))
    {B : ℝ} (hB : ∀ k, ∀ t ∈ Icc (0 : ℝ) T, ‖(1 / (s k).norm' T) • (s k).Φ t‖ ≤ B)
    {Φ : ℝ → X} {lam : ℝ → ℝ} {lam0 : ℝ}
    (hΦ : ∀ t ∈ Icc (0 : ℝ) T,
      Tendsto (fun k => (1 / (s k).norm' T) • (s k).Φ t) atTop (𝓝 (Φ t)))
    (hlam : ∀ t ∈ Icc (0 : ℝ) T,
      Tendsto (fun k => (1 / (s k).norm' T) * (s k).lam t) atTop (𝓝 (lam t)))
    (hm : Tendsto (fun k => 1 / (s k).norm' T) atTop (𝓝 lam0)) :
    AEStronglyMeasurable Φ (volume.restrict (Ioc (0 : ℝ) T)) ∧
      AEStronglyMeasurable lam (volume.restrict (Ioc (0 : ℝ) T)) ∧
      IntervalIntegrable (fun r => lam0 • cx₀ r - A₀ r (Φ r - lam r • g₀ r) + lam r • gd₀ r)
        volume 0 T ∧
      ∀ t ∈ Icc (0 : ℝ) T, Φ t = Φ 0 + ∫ r in (0 : ℝ)..t,
        (lam0 • cx₀ r - A₀ r (Φ r - lam r • g₀ r) + lam r • gd₀ r) := by
  have hT0 : 0 ≤ T := hT.le
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT0⟩
  have hC : 0 ≤ C := (norm_nonneg _).trans (hA 0 0 h0)
  set m : ℕ → ℝ := fun k => 1 / (s k).norm' T with hmdef
  set φ : ℕ → ℝ → X := fun k t => m k • (s k).Φ t with hφdef
  set l : ℕ → ℝ → ℝ := fun k t => m k * (s k).lam t with hldef
  have hm0 : ∀ k, 0 < m k := fun k => (hs k).inv_norm'_pos hT0
  have hm1 : ∀ k, m k ≤ 1 := fun k => (hs k).inv_norm'_le_one hT0
  have hl : ∀ k, ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ l k t ∧ l k t ≤ 1 := fun k =>
    (hs k).normalised_lam_mem hT0
  have hΦB : ∀ t ∈ Icc (0 : ℝ) T, ‖Φ t‖ ≤ B := fun t ht =>
    le_of_tendsto' (hΦ t ht).norm fun k => hB k t ht
  have hlam01 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ lam t ∧ lam t ≤ 1 := fun t ht =>
    ⟨ge_of_tendsto' (hlam t ht) fun k => (hl k t ht).1,
      le_of_tendsto' (hlam t ht) fun k => (hl k t ht).2⟩
  -- measurability
  have hIoc : Ioc (0 : ℝ) T ⊆ Icc 0 T := Ioc_subset_Icc_self
  have hφm : ∀ k, AEStronglyMeasurable (φ k) (volume.restrict (Ioc (0 : ℝ) T)) := fun k =>
    ((((hs k).continuousOn_Φ hT0).const_smul (m k)).mono hIoc).aestronglyMeasurable
      measurableSet_Ioc
  have hlm : ∀ k, AEStronglyMeasurable (l k) (volume.restrict (Ioc (0 : ℝ) T)) := fun k =>
    ((aemeasurable_restrict_of_antitoneOn measurableSet_Ioc
      ((hs k).antitone.mono hIoc)).const_mul (m k)).aestronglyMeasurable
  have hΦm : AEStronglyMeasurable Φ (volume.restrict (Ioc (0 : ℝ) T)) :=
    aestronglyMeasurable_of_tendsto_ae atTop hφm
      ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun r hr => hΦ r (hIoc hr)))
  have hlamm : AEStronglyMeasurable lam (volume.restrict (Ioc (0 : ℝ) T)) :=
    aestronglyMeasurable_of_tendsto_ae atTop hlm
      ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun r hr => hlam r (hIoc hr)))
  -- the arguments of the `A`-terms
  set v : ℕ → ℝ → X := fun k r => φ k r - l k r • (s k).g r with hvdef
  set v₀ : ℝ → X := fun r => Φ r - lam r • g₀ r with hv₀def
  have hvm : ∀ k, AEStronglyMeasurable (v k) (volume.restrict (Ioc (0 : ℝ) T)) := fun k =>
    (hφm k).sub ((hlm k).smul (hs k).measurable_g)
  have hv₀m : AEStronglyMeasurable v₀ (volume.restrict (Ioc (0 : ℝ) T)) :=
    hΦm.sub (hlamm.smul hg₀m)
  have hvB : ∀ k, ∀ r ∈ Icc (0 : ℝ) T, ‖v k r‖ ≤ B + C := by
    intro k r hr
    refine (norm_sub_le _ _).trans (add_le_add (hB k r hr) ?_)
    rw [norm_smul, Real.norm_of_nonneg (hl k r hr).1]
    nlinarith [(hl k r hr).1, (hl k r hr).2, hg k r hr, norm_nonneg ((s k).g r)]
  have hv₀B : ∀ r ∈ Icc (0 : ℝ) T, ‖v₀ r‖ ≤ B + C := by
    intro r hr
    refine (norm_sub_le _ _).trans (add_le_add (hΦB r hr) ?_)
    rw [norm_smul, Real.norm_of_nonneg (hlam01 r hr).1]
    nlinarith [(hlam01 r hr).1, (hlam01 r hr).2, hg₀ r hr, norm_nonneg (g₀ r)]
  -- the limit integrand
  set F : ℝ → X := fun r => lam0 • cx₀ r - A₀ r (Φ r - lam r • g₀ r) + lam r • gd₀ r with hFdef
  have hFi : IntervalIntegrable F volume 0 T := by
    have h1 : IntervalIntegrable (fun r => lam0 • cx₀ r) volume 0 T := hcx₀.smul lam0
    have h2 : IntervalIntegrable (fun r => A₀ r (v₀ r)) volume 0 T :=
      intervalIntegrable_of_norm_le hT0 (intervalIntegrable_const (c := C * (B + C)))
        ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := X) (F := X)).continuous
          |>.comp_aestronglyMeasurable (hA₀m.prodMk hv₀m))
        fun r hr => ((A₀ r).le_opNorm _).trans
          (mul_le_mul (hA₀ r (hIoc hr)) (hv₀B r (hIoc hr)) (norm_nonneg _) hC)
    have h3 : IntervalIntegrable (fun r => lam r • gd₀ r) volume 0 T :=
      intervalIntegrable_of_norm_le hT0 hgd₀.norm (hlamm.smul hgd₀.aestronglyMeasurable)
        fun r hr => by
          rw [norm_smul, Real.norm_of_nonneg (hlam01 r (hIoc hr)).1]
          nlinarith [(hlam01 r (hIoc hr)).2, norm_nonneg (gd₀ r)]
    exact (h1.sub h2).add h3
  -- the majorants
  set b1 : ℕ → ℝ → ℝ := fun k r => ‖(s k).cx r - cx₀ r‖ + ‖m k - lam0‖ * ‖cx₀ r‖ with hb1
  set w : ℕ → ℝ → ℝ := fun k r => ‖v k r - v₀ r‖ with hw
  set b2 : ℕ → ℝ → ℝ := fun k r => (B + C) * ‖(s k).A r - A₀ r‖ + C * w k r with hb2
  set b3 : ℕ → ℝ → ℝ := fun k r => C * ‖(s k).defect r‖ with hb3
  set q : ℕ → ℝ → ℝ := fun k r => ‖l k r - lam r‖ * ‖gd₀ r‖ with hq
  set b4 : ℕ → ℝ → ℝ := fun k r => ‖(s k).gd r - gd₀ r‖ + q k r with hb4
  have hwm : ∀ k, AEStronglyMeasurable (w k) (volume.restrict (Ioc (0 : ℝ) T)) := fun k =>
    ((hvm k).sub hv₀m).norm
  have hwB : ∀ k, ∀ r ∈ Ioc (0 : ℝ) T, ‖w k r‖ ≤ (B + C) + (B + C) := fun k r hr => by
    simp only [hw, norm_norm]
    exact (norm_sub_le _ _).trans (add_le_add (hvB k r (hIoc hr)) (hv₀B r (hIoc hr)))
  have hqm : ∀ k, AEStronglyMeasurable (q k) (volume.restrict (Ioc (0 : ℝ) T)) := fun k =>
    ((hlm k).sub hlamm).norm.mul hgd₀.aestronglyMeasurable.norm
  have hqB : ∀ k, ∀ r ∈ Ioc (0 : ℝ) T, ‖q k r‖ ≤ ‖gd₀ r‖ := fun k r hr => by
    have h1 := hl k r (hIoc hr)
    have h2 := hlam01 r (hIoc hr)
    have : ‖l k r - lam r‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith
    simp only [hq, norm_mul, norm_norm]
    nlinarith [norm_nonneg (gd₀ r), norm_nonneg (l k r - lam r)]
  have hwi : ∀ k, IntervalIntegrable (w k) volume 0 T := fun k =>
    intervalIntegrable_of_norm_le hT0 intervalIntegrable_const (hwm k) (hwB k)
  have hqi : ∀ k, IntervalIntegrable (q k) volume 0 T := fun k =>
    intervalIntegrable_of_norm_le hT0 hgd₀.norm (hqm k) (hqB k)
  have hAAi : ∀ k, IntervalIntegrable (fun r => (s k).A r - A₀ r) volume 0 T := fun k =>
    intervalIntegrable_of_norm_le hT0 (intervalIntegrable_const (c := C + C))
      ((hs k).measurable_A.sub hA₀m)
      fun r hr => (norm_sub_le _ _).trans (add_le_add (hA k r (hIoc hr)) (hA₀ r (hIoc hr)))
  have hb1i : ∀ k, IntervalIntegrable (b1 k) volume 0 T := fun k =>
    ((hs k).integrable_cx.sub hcx₀).norm.add (hcx₀.norm.const_mul _)
  have hb2i : ∀ k, IntervalIntegrable (b2 k) volume 0 T := fun k =>
    ((hAAi k).norm.const_mul _).add ((hwi k).const_mul _)
  have hb3i : ∀ k, IntervalIntegrable (b3 k) volume 0 T := fun k =>
    (hs k).integrable_defect_vec.norm.const_mul _
  have hb4i : ∀ k, IntervalIntegrable (b4 k) volume 0 T := fun k =>
    ((hs k).integrable_gd.sub hgd₀).norm.add (hqi k)
  -- the pointwise estimate
  have hle : ∀ k, ∀ r ∈ Ioc (0 : ℝ) T,
      ‖m k • (s k).adj r - F r‖ ≤ b1 k r + b2 k r + b3 k r + b4 k r := by
    intro k r hr'
    have hr := hIoc hr'
    have hsplit : m k • (s k).adj r - F r =
        (m k • (s k).cx r - lam0 • cx₀ r) - ((s k).A r (v k r) - A₀ r (v₀ r)) +
          m k • (s k).A r ((s k).defect r) + (l k r • (s k).gd r - lam r • gd₀ r) := by
      simp only [EpsilonCostateSystem.adj, hFdef, hvdef, hv₀def, hφdef, hldef, smul_add,
        smul_sub, map_sub, map_smul, smul_smul]
      abel
    have e1 : ‖m k • (s k).cx r - lam0 • cx₀ r‖ ≤ b1 k r := by
      have : m k • (s k).cx r - lam0 • cx₀ r =
          m k • ((s k).cx r - cx₀ r) + (m k - lam0) • cx₀ r := by
        rw [smul_sub, sub_smul]; abel
      rw [this]
      refine (norm_add_le _ _).trans (add_le_add ?_ (norm_smul _ _).le)
      rw [norm_smul, Real.norm_of_nonneg (hm0 k).le]
      nlinarith [hm1 k, norm_nonneg ((s k).cx r - cx₀ r)]
    have e2 : ‖(s k).A r (v k r) - A₀ r (v₀ r)‖ ≤ b2 k r := by
      have : (s k).A r (v k r) - A₀ r (v₀ r) =
          ((s k).A r - A₀ r) (v k r) + A₀ r (v k r - v₀ r) := by
        rw [show ((s k).A r - A₀ r) (v k r) = (s k).A r (v k r) - A₀ r (v k r) from rfl,
          map_sub (A₀ r) (v k r) (v₀ r)]
        abel
      rw [this]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · calc _ ≤ ‖(s k).A r - A₀ r‖ * ‖v k r‖ := ContinuousLinearMap.le_opNorm _ _
          _ ≤ ‖(s k).A r - A₀ r‖ * (B + C) :=
            mul_le_mul_of_nonneg_left (hvB k r hr) (norm_nonneg _)
          _ = _ := by ring
      · exact ((A₀ r).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hA₀ r hr) (norm_nonneg _))
    have e3 : ‖m k • (s k).A r ((s k).defect r)‖ ≤ b3 k r := by
      rw [norm_smul, Real.norm_of_nonneg (hm0 k).le]
      calc m k * ‖(s k).A r ((s k).defect r)‖ ≤ 1 * (‖(s k).A r‖ * ‖(s k).defect r‖) :=
            mul_le_mul (hm1 k) (((s k).A r).le_opNorm _) (norm_nonneg _) zero_le_one
        _ ≤ C * ‖(s k).defect r‖ := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_right (hA k r hr) (norm_nonneg _)
    have e4 : ‖l k r • (s k).gd r - lam r • gd₀ r‖ ≤ b4 k r := by
      have : l k r • (s k).gd r - lam r • gd₀ r =
          l k r • ((s k).gd r - gd₀ r) + (l k r - lam r) • gd₀ r := by
        rw [smul_sub, sub_smul]; abel
      rw [this]
      refine (norm_add_le _ _).trans (add_le_add ?_ (norm_smul _ _).le)
      rw [norm_smul, Real.norm_of_nonneg (hl k r hr).1]
      nlinarith [(hl k r hr).2, norm_nonneg ((s k).gd r - gd₀ r)]
    rw [hsplit]
    have f1 := norm_add_le ((m k • (s k).cx r - lam0 • cx₀ r) -
      ((s k).A r (v k r) - A₀ r (v₀ r)) + m k • (s k).A r ((s k).defect r))
      (l k r • (s k).gd r - lam r • gd₀ r)
    have f2 := norm_add_le ((m k • (s k).cx r - lam0 • cx₀ r) -
      ((s k).A r (v k r) - A₀ r (v₀ r))) (m k • (s k).A r ((s k).defect r))
    have f3 := norm_sub_le (m k • (s k).cx r - lam0 • cx₀ r)
      ((s k).A r (v k r) - A₀ r (v₀ r))
    linarith
  -- the majorants have vanishing integrals
  have hmn : Tendsto (fun k => ‖m k - lam0‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 hm
  have t1 : Tendsto (fun k => ∫ r in (0 : ℝ)..T, b1 k r) atTop (𝓝 0) := by
    have e : ∀ k, ∫ r in (0 : ℝ)..T, b1 k r = (∫ r in (0 : ℝ)..T, ‖(s k).cx r - cx₀ r‖) +
        ‖m k - lam0‖ * ∫ r in (0 : ℝ)..T, ‖cx₀ r‖ := fun k => by
      simp only [hb1]
      rw [intervalIntegral.integral_add ((hs k).integrable_cx.sub hcx₀).norm
        (hcx₀.norm.const_mul _), intervalIntegral.integral_const_mul]
    simp only [e]
    simpa using hcxlim.add (hmn.mul_const (∫ r in (0 : ℝ)..T, ‖cx₀ r‖))
  have t2 : Tendsto (fun k => ∫ r in (0 : ℝ)..T, b2 k r) atTop (𝓝 0) := by
    have e : ∀ k, ∫ r in (0 : ℝ)..T, b2 k r =
        (B + C) * (∫ r in (0 : ℝ)..T, ‖(s k).A r - A₀ r‖) +
          C * ∫ r in (0 : ℝ)..T, w k r := fun k => by
      simp only [hb2]
      rw [intervalIntegral.integral_add ((hAAi k).norm.const_mul _) ((hwi k).const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hw0 : Tendsto (fun k => ∫ r in (0 : ℝ)..T, w k r) atTop (𝓝 0) :=
      tendsto_intervalIntegral_zero_of_dominated hT0 hwm hwB intervalIntegrable_const
        fun r hr => by
          have hr' := hIoc hr
          have := ((hΦ r hr').sub ((hlam r hr').smul (hglim r hr')))
          exact tendsto_iff_norm_sub_tendsto_zero.1 this
    simp only [e]
    simpa using (hAlim.const_mul (B + C)).add (hw0.const_mul C)
  have t3 : Tendsto (fun k => ∫ r in (0 : ℝ)..T, b3 k r) atTop (𝓝 0) := by
    simp only [hb3, intervalIntegral.integral_const_mul]
    simpa using hdeflim.const_mul C
  have t4 : Tendsto (fun k => ∫ r in (0 : ℝ)..T, b4 k r) atTop (𝓝 0) := by
    have e : ∀ k, ∫ r in (0 : ℝ)..T, b4 k r =
        (∫ r in (0 : ℝ)..T, ‖(s k).gd r - gd₀ r‖) + ∫ r in (0 : ℝ)..T, q k r := fun k => by
      simp only [hb4]
      rw [intervalIntegral.integral_add ((hs k).integrable_gd.sub hgd₀).norm (hqi k)]
    have hq0 : Tendsto (fun k => ∫ r in (0 : ℝ)..T, q k r) atTop (𝓝 0) :=
      tendsto_intervalIntegral_zero_of_dominated hT0 hqm hqB hgd₀.norm fun r hr => by
        have := (tendsto_iff_norm_sub_tendsto_zero.1 (hlam r (hIoc hr))).mul_const ‖gd₀ r‖
        simpa only [hq, zero_mul] using this
    simp only [e]
    simpa using hgdlim.add hq0
  have hbi : ∀ k, IntervalIntegrable (fun r => b1 k r + b2 k r + b3 k r + b4 k r) volume 0 T :=
    fun k => (((hb1i k).add (hb2i k)).add (hb3i k)).add (hb4i k)
  have tsum : Tendsto (fun k => ∫ r in (0 : ℝ)..T, (b1 k r + b2 k r + b3 k r + b4 k r))
      atTop (𝓝 0) := by
    have e : ∀ k, ∫ r in (0 : ℝ)..T, (b1 k r + b2 k r + b3 k r + b4 k r) =
        (∫ r in (0 : ℝ)..T, b1 k r) + (∫ r in (0 : ℝ)..T, b2 k r) +
          (∫ r in (0 : ℝ)..T, b3 k r) + ∫ r in (0 : ℝ)..T, b4 k r := fun k => by
      rw [intervalIntegral.integral_add (((hb1i k).add (hb2i k)).add (hb3i k)) (hb4i k),
        intervalIntegral.integral_add ((hb1i k).add (hb2i k)) (hb3i k),
        intervalIntegral.integral_add (hb1i k) (hb2i k)]
    simp only [e]
    simpa using ((t1.add t2).add t3).add t4
  have hconv := tendsto_intervalIntegral_of_norm_sub_le hT0
    (f := fun k r => m k • (s k).adj r) (fun k => (hs k).integrable_adj.smul (m k)) hFi hbi
    hle tsum
  refine ⟨hΦm, hlamm, hFi, fun t ht => ?_⟩
  have h1 : Tendsto (fun k => φ k t - φ k 0) atTop (𝓝 (Φ t - Φ 0)) := (hΦ t ht).sub (hΦ 0 h0)
  have h2 : Tendsto (fun k => φ k t - φ k 0) atTop (𝓝 (∫ r in (0 : ℝ)..t, F r)) := by
    refine (hconv t ht).congr fun k => ?_
    simp only [hφdef]
    rw [(hs k).normalised_eq_integral t ht]
    abel
  have := tendsto_nhds_unique h1 h2
  rw [← this]
  abel

end PassageIntegral

section Passage

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- **The `ε → 0` limiting operations of §11.4 (Theorem 11.4.4 (i)–(iv), measure-free form).**

Let `s k` be `ε_k`-level costate systems (`ε_k → 0`) on `[0,T]` with the data bounds and
convergences below: uniform bounds on `f⁰ₓ, ∇G, ‖fₓ‖` and on `∫‖d(∇G)/dt‖`; convergence in `L¹` of
`f⁰ₓ, fₓ, d(∇G)/dt` to the data `cx₀, A₀, gd₀` of the optimal pair, `L¹`-convergence of the velocity
defects to `0`, pointwise convergence `∇G(φ_ε) → g₀`, and convergence of the initial/terminal
covector data (`‖ι_k‖ → 0`, `Dl_k → Dl₀`, `Dr_k → Dr₀`).  Then, along a subsequence, the normalised
costates `Φ_k/M_k` and multipliers `λ_k/M_k` converge **at every point** (Helly) to a function of
bounded variation `Φ` and a nonincreasing `λ ≥ 0` with `λ(T) = 0`, `β_k/M_k → β`,
`1/M_k → λ⁰`, and

* (i)   `|Φ(T)| + λ(0) + |β| + λ⁰ = 1`;
* (ii)  `Φ(t) = Φ(0) + ∫₀ᵗ (λ⁰ f⁰ₓ − (Φ − λ∇G)·fₓ + λ d(∇G)/dt)`  (adjoint law in integrated form);
* (iii) `Φ(0) = λ(0) ∇G(0) + β·∂₁T`;
* (iv)  `Φ(T) = −β·∂₂T`.

Here `λ(0) = λ(0⁺)` when the multipliers are constant near `0` (Assumption 11.4.1, see
`lam_const_near_zero`).

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Remarks 11.4.2–11.4.3,
(11.4.1)–(11.4.5), (11.4.14)–(11.4.16), Theorem 11.4.4. -/
theorem exists_limit_of_epsilonCostateSystems {T : ℝ} (hT : 0 < T)
    (s : ℕ → EpsilonCostateSystem X Y) (hs : ∀ k, IsEpsilonCostateSystem T (s k))
    {C : ℝ} (hcx : ∀ k, ∀ t ∈ Icc (0 : ℝ) T, ‖(s k).cx t‖ ≤ C)
    (hA : ∀ k, ∀ t ∈ Icc (0 : ℝ) T, ‖(s k).A t‖ ≤ C)
    (hg : ∀ k, ∀ t ∈ Icc (0 : ℝ) T, ‖(s k).g t‖ ≤ C)
    (hgd : ∀ k, ∫ r in (0 : ℝ)..T, ‖(s k).gd r‖ ≤ C)
    {cx₀ : ℝ → X} {A₀ : ℝ → X →L[ℝ] X} {g₀ gd₀ : ℝ → X} {Dl₀ Dr₀ : Y →L[ℝ] X}
    (hcx₀ : IntervalIntegrable cx₀ volume 0 T) (hgd₀ : IntervalIntegrable gd₀ volume 0 T)
    (hA₀m : AEStronglyMeasurable A₀ (volume.restrict (Ioc (0 : ℝ) T)))
    (hg₀m : AEStronglyMeasurable g₀ (volume.restrict (Ioc (0 : ℝ) T)))
    (hA₀ : ∀ t ∈ Icc (0 : ℝ) T, ‖A₀ t‖ ≤ C) (hg₀ : ∀ t ∈ Icc (0 : ℝ) T, ‖g₀ t‖ ≤ C)
    (hcxlim : Tendsto (fun k => ∫ r in (0 : ℝ)..T, ‖(s k).cx r - cx₀ r‖) atTop (𝓝 0))
    (hAlim : Tendsto (fun k => ∫ r in (0 : ℝ)..T, ‖(s k).A r - A₀ r‖) atTop (𝓝 0))
    (hgdlim : Tendsto (fun k => ∫ r in (0 : ℝ)..T, ‖(s k).gd r - gd₀ r‖) atTop (𝓝 0))
    (hdeflim : Tendsto (fun k => ∫ r in (0 : ℝ)..T, ‖(s k).defect r‖) atTop (𝓝 0))
    (hglim : ∀ t ∈ Icc (0 : ℝ) T, Tendsto (fun k => (s k).g t) atTop (𝓝 (g₀ t)))
    (hιlim : Tendsto (fun k => ‖(s k).ι‖) atTop (𝓝 0))
    (hDl : Tendsto (fun k => (s k).Dl) atTop (𝓝 Dl₀))
    (hDr : Tendsto (fun k => (s k).Dr) atTop (𝓝 Dr₀)) :
    ∃ (ψ : ℕ → ℕ) (Φ : ℝ → X) (lam : ℝ → ℝ) (β : Y) (lam0 : ℝ),
      StrictMono ψ ∧
      (∀ t ∈ Icc (0 : ℝ) T, Tendsto (fun k => (1 / (s (ψ k)).norm' T) • (s (ψ k)).Φ t) atTop
        (𝓝 (Φ t))) ∧
      (∀ t ∈ Icc (0 : ℝ) T, Tendsto (fun k => (1 / (s (ψ k)).norm' T) * (s (ψ k)).lam t) atTop
        (𝓝 (lam t))) ∧
      Tendsto (fun k => (1 / (s (ψ k)).norm' T) • (s (ψ k)).β) atTop (𝓝 β) ∧
      Tendsto (fun k => 1 / (s (ψ k)).norm' T) atTop (𝓝 lam0) ∧
      eVariationOn Φ (Icc (0 : ℝ) T) ≠ ⊤ ∧
      AntitoneOn lam (Icc (0 : ℝ) T) ∧ (∀ t ∈ Icc (0 : ℝ) T, 0 ≤ lam t) ∧ lam T = 0 ∧
      0 ≤ lam0 ∧ lam0 ≤ 1 ∧
      ‖Φ T‖ + lam 0 + ‖β‖ + lam0 = 1 ∧
      (∀ t ∈ Icc (0 : ℝ) T, Φ t = Φ 0 + ∫ r in (0 : ℝ)..t,
        (lam0 • cx₀ r - A₀ r (Φ r - lam r • g₀ r) + lam r • gd₀ r)) ∧
      Φ 0 = lam 0 • g₀ 0 + Dl₀ β ∧ Φ T = -(Dr₀ β) ∧
      AEStronglyMeasurable Φ (volume.restrict (Ioc (0 : ℝ) T)) ∧
      AEStronglyMeasurable lam (volume.restrict (Ioc (0 : ℝ) T)) ∧
      IntervalIntegrable (fun r => lam0 • cx₀ r - A₀ r (Φ r - lam r • g₀ r) + lam r • gd₀ r)
        volume 0 T ∧
      ∃ B : ℝ, ∀ k, ∀ t ∈ Icc (0 : ℝ) T, ‖(1 / (s (ψ k)).norm' T) • (s (ψ k)).Φ t‖ ≤ B := by
  have hT0 : 0 ≤ T := hT.le
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT0⟩
  have hTm : T ∈ Icc (0 : ℝ) T := ⟨hT0, le_rfl⟩
  have hC : 0 ≤ C := (norm_nonneg _).trans (hA 0 0 h0)
  -- Step 1–2: uniform Grönwall and variation bounds (11.4.1)–(11.4.2)
  obtain ⟨D, hD⟩ : ∃ D, ∀ k, ∫ r in (0 : ℝ)..T, ‖(s k).defect r‖ ≤ D := by
    obtain ⟨D, hD⟩ := hdeflim.bddAbove_range
    exact ⟨D, fun k => hD ⟨k, rfl⟩⟩
  set K : ℝ := (C + C * C) * T + C * D + C with hK
  have hbounds := fun k => (hs k).normalised_bounds hT0 hC (hcx k) (hA k) (hg k) (K := K) (by
    have h1 := mul_le_mul_of_nonneg_left (hD k) hC
    have h2 := hgd k
    simp only [hK]; linarith)
  set B : ℝ := (1 + K) * Real.exp (C * T) with hBdef
  have hB : ∀ k, ∀ t ∈ Icc (0 : ℝ) T, ‖(1 / (s k).norm' T) • (s k).Φ t‖ ≤ B :=
    fun k => (hbounds k).1
  have hφT : ∀ k, ‖(1 / (s k).norm' T) • (s k).Φ T‖ ≤ 1 := fun k => by
    have := (hs k).normalised_sum hT0
    have h1 := ((hs k).inv_norm'_pos hT0).le
    have h2 := ((hs k).normalised_lam_mem hT0 0 h0).1
    have h3 := norm_nonneg ((1 / (s k).norm' T) • (s k).β)
    linarith
  have hlvar : ∀ k, eVariationOn (fun t => (1 / (s k).norm' T) * (s k).lam t) (Icc 0 T) ≤
      ENNReal.ofReal 1 := fun k => by
    have hmono : MonotoneOn (fun t => -((1 / (s k).norm' T) * (s k).lam t)) (Icc 0 T) :=
      fun x hx y hy hxy => neg_le_neg
        (mul_le_mul_of_nonneg_left ((hs k).antitone hx hy hxy) ((hs k).inv_norm'_pos hT0).le)
    have hv := hmono.eVariationOn_eq h0 hTm
    rw [inter_self] at hv
    refine (eVariationOn_le_of_edist_le
      (g := fun t => -((1 / (s k).norm' T) * (s k).lam t)) fun x _ y _ => by
        rw [edist_neg_neg]).trans ?_
    rw [hv]
    refine ENNReal.ofReal_le_ofReal ?_
    have := ((hs k).normalised_lam_mem hT0 0 h0).2
    simp only [(hs k).lam_horizon, mul_zero, neg_zero, zero_sub, neg_neg]
    exact this
  -- Step 3: Helly selection and compactness (11.4.4)–(11.4.5)
  obtain ⟨ψ₁, Φ, hψ₁, hΦvar, hΦlim⟩ := DynamicalSystems.Helly.helly_selection
    (fun k t => (1 / (s k).norm' T) • (s k).Φ t) hT0 hTm (B := 1) hφT ENNReal.ofReal_ne_top
    fun k => (hbounds k).2
  obtain ⟨ψ₂, lam, hψ₂, -, -, hlamlim⟩ := DynamicalSystems.Helly.helly_selection_real
    (fun k t => (1 / (s (ψ₁ k)).norm' T) * (s (ψ₁ k)).lam t) hT0 hTm (B := 0)
    (fun k => by simp [(hs (ψ₁ k)).lam_horizon]) ENNReal.ofReal_ne_top fun k => hlvar (ψ₁ k)
  obtain ⟨p, hp, ψ₃, hψ₃, hlim3⟩ :=
    ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod (isCompact_closedBall (0 : Y) 1)).tendsto_subseq
      (x := fun k => (1 / (s (ψ₁ (ψ₂ k))).norm' T,
        (1 / (s (ψ₁ (ψ₂ k))).norm' T) • (s (ψ₁ (ψ₂ k))).β))
      fun k => by
        refine ⟨⟨((hs _).inv_norm'_pos hT0).le, (hs _).inv_norm'_le_one hT0⟩, ?_⟩
        rw [mem_closedBall_zero_iff]
        have := (hs (ψ₁ (ψ₂ k))).normalised_sum hT0
        have h1 := ((hs (ψ₁ (ψ₂ k))).inv_norm'_pos hT0).le
        have h2 := ((hs (ψ₁ (ψ₂ k))).normalised_lam_mem hT0 0 h0).1
        have h3 := norm_nonneg ((1 / (s (ψ₁ (ψ₂ k))).norm' T) • (s (ψ₁ (ψ₂ k))).Φ T)
        linarith
  set ψ : ℕ → ℕ := fun k => ψ₁ (ψ₂ (ψ₃ k)) with hψdef
  have hψ : StrictMono ψ := hψ₁.comp (hψ₂.comp hψ₃)
  have hψt : Tendsto ψ atTop atTop := hψ.tendsto_atTop
  have hΦψ : ∀ t ∈ Icc (0 : ℝ) T,
      Tendsto (fun k => (1 / (s (ψ k)).norm' T) • (s (ψ k)).Φ t) atTop (𝓝 (Φ t)) :=
    fun t ht => (hΦlim t ht).comp (hψ₂.comp hψ₃).tendsto_atTop
  have hlamψ : ∀ t ∈ Icc (0 : ℝ) T,
      Tendsto (fun k => (1 / (s (ψ k)).norm' T) * (s (ψ k)).lam t) atTop (𝓝 (lam t)) :=
    fun t ht => (hlamlim t ht).comp hψ₃.tendsto_atTop
  have hmψ : Tendsto (fun k => 1 / (s (ψ k)).norm' T) atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hlim3
  have hβψ : Tendsto (fun k => (1 / (s (ψ k)).norm' T) • (s (ψ k)).β) atTop (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hlim3
  have hpass := integral_identity_of_tendsto hT (fun k => s (ψ k)) (fun k => hs _)
    (fun k => hA _) (fun k => hg _) hcx₀ hgd₀ hA₀m hg₀m hA₀ hg₀ (hcxlim.comp hψt)
    (hAlim.comp hψt) (hgdlim.comp hψt) (hdeflim.comp hψt) (fun t ht => (hglim t ht).comp hψt)
    (fun k => hB _) hΦψ hlamψ hmψ
  refine ⟨ψ, Φ, lam, p.2, p.1, hψ, hΦψ, hlamψ, hβψ, hmψ,
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hΦvar, ?_, ?_, ?_, hp.1.1, hp.1.2, ?_, hpass.2.2.2,
    ?_, ?_, hpass.1, hpass.2.1, hpass.2.2.1, ⟨B, fun k => hB _⟩⟩
  · -- `λ` is nonincreasing
    exact fun x hx y hy hxy => le_of_tendsto_of_tendsto' (hlamψ y hy) (hlamψ x hx) fun k =>
      mul_le_mul_of_nonneg_left ((hs _).antitone hx hy hxy) ((hs _).inv_norm'_pos hT0).le
  · -- `λ ≥ 0`
    exact fun t ht => ge_of_tendsto' (hlamψ t ht) fun k => ((hs _).normalised_lam_mem hT0 t ht).1
  · -- `λ(T) = 0`
    refine tendsto_nhds_unique (hlamψ T hTm) (tendsto_const_nhds.congr fun k => ?_)
    rw [(hs _).lam_horizon, mul_zero]
  · -- (i) the normalisation
    have h1 := (((hmψ.add (hΦψ T hTm).norm).add (hlamψ 0 h0)).add hβψ.norm)
    have h2 := tendsto_nhds_unique h1
      (tendsto_const_nhds.congr fun k => ((hs (ψ k)).normalised_sum hT0).symm)
    linarith
  · -- (iii) the initial condition
    have happ := (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Y) (F := X)).continuous
    have hι : Tendsto (fun k => (1 / (s (ψ k)).norm' T) • (s (ψ k)).ι) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun k => ?_) (hιlim.comp hψt)
      rw [norm_smul, Real.norm_of_nonneg ((hs _).inv_norm'_pos hT0).le]
      have := (hs (ψ k)).inv_norm'_le_one hT0
      have := norm_nonneg (s (ψ k)).ι
      exact mul_le_of_le_one_left (norm_nonneg _) (by assumption)
    have hDlβ : Tendsto (fun k => (s (ψ k)).Dl ((1 / (s (ψ k)).norm' T) • (s (ψ k)).β)) atTop
        (𝓝 (Dl₀ p.2)) :=
      (happ.tendsto (Dl₀, p.2)).comp ((hDl.comp hψt).prodMk_nhds hβψ)
    have hgg := (hlamψ 0 h0).smul ((hglim 0 h0).comp hψt)
    have hsum := (hι.add hDlβ).add hgg
    have h2 := tendsto_nhds_unique (hΦψ 0 h0) (hsum.congr fun k => ?_)
    · rw [h2, zero_add, add_comm]
    · simp only [Function.comp, (hs (ψ k)).initial, smul_add, map_smul, smul_smul]
  · -- (iv) the terminal condition
    have happ := (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Y) (F := X)).continuous
    have hDrβ : Tendsto (fun k => (s (ψ k)).Dr ((1 / (s (ψ k)).norm' T) • (s (ψ k)).β)) atTop
        (𝓝 (Dr₀ p.2)) :=
      (happ.tendsto (Dr₀, p.2)).comp ((hDr.comp hψt).prodMk_nhds hβψ)
    refine tendsto_nhds_unique (hΦψ T hTm) (hDrβ.neg.congr fun k => ?_)
    simp only [(hs (ψ k)).terminal, smul_neg, map_smul]

end Passage

end OptimalControl.BoundedState
