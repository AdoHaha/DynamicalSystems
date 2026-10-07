/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.StatePenalisedVelocityFunctional
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The nonincreasing state multiplier and the costate equation (11.6.11)

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), §11.6.  For the `ω`-penalised
functional `H^j` of `StatePenalisedVelocityFunctional.lean` the state-multiplier measure at level
`j` has the density `m(t) = j ω'(G(t, γ(t))) ≥ 0`.  This file builds, from such a density,

* the **nonincreasing state multiplier** `λ(t) = ∫_t^T m` (`stateMultiplier`): `λ ≥ 0`,
  `λ(T) = 0`, `λ` is antitone and continuous, and it is **constant on every interval on which
  `m` vanishes** — in particular on every interval on which the state constraint is slack or
  active-but-`ω' = 0` (`stateMultiplier_eq_of_density_eq_zero`, the complementarity condition,
  cf. Lemma 11.3.9);
* the **costate** `Φ = p + λ ∇G(t,γ(t))`, which is absolutely continuous and satisfies the
  measure-free equation `Φ' = ∂ₓL + λ d(∇G(t,γ(t)))/dt` (`stateCostate_eq_primitive`; the
  integrated form of (11.6.11)) with `Φ(0) = p(0) + λ(0) ∇G(0,γ(0))` (11.6.6) and `Φ(T) = p(T)`
  (11.6.16) because `λ(T) = 0`;
* `gradientAlongPath_eq_primitive`: `t ↦ ∇G(t, γ(t))` is an absolutely continuous covector path
  with derivative `∇²G (1, γ')` along an `L²`-velocity carrier, so the costate equation makes
  sense;
* the **boundary-perturbation mass identity** `integral_density_eq_boundary` for the test field
  `h = ∇G/|∇G|²`: the total multiplier mass is read off from the endpoint data.

Book citations live in docstrings only.
-/

@[expose] public section

open Set MeasureTheory Filter ACEulerLagrange
open scoped Topology Interval

namespace OptimalControl.BoundedState

section Integrability

variable {F : Type*} [NormedAddCommGroup F] {T : ℝ}

/-- Interval integrability on `[0,T]` restricts to any subinterval with endpoints in `[0,T]`. -/
theorem intervalIntegrable_of_mem_Icc_Icc {f : ℝ → F} (hf : IntervalIntegrable f volume 0 T)
    (hT : 0 ≤ T) {a b : ℝ} (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable f volume a b :=
  hf.mono_set (by
    rw [uIcc_of_le hT]
    exact uIcc_subset_Icc ha hb)

end Integrability

section MultiplierCurve

variable {T : ℝ} {m : ℝ → ℝ}

/-- The nonincreasing state multiplier `λ(t) = ∫_t^T m` built from a nonnegative multiplier density
`m` on `[0,T]`: the book's `λ(ε;·)` of (11.6.11), normalised by `λ(T) = 0`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.21) and (11.6.11). -/
noncomputable def stateMultiplier (T : ℝ) (m : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ r in t..T, m r

/-- The multiplier vanishes at the horizon. -/
@[simp] theorem stateMultiplier_horizon : stateMultiplier T m T = 0 := by
  simp [stateMultiplier]

/-- The multiplier is the initial mass minus the running mass: `λ(t) = λ(0) + ∫₀ᵗ (-m)`. -/
theorem stateMultiplier_eq_sub (hT : 0 ≤ T) (hm : IntervalIntegrable m volume 0 T) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    stateMultiplier T m t = stateMultiplier T m 0 + ∫ r in (0 : ℝ)..t, -m r := by
  have h0t : IntervalIntegrable m volume 0 t :=
    intervalIntegrable_of_mem_Icc_Icc hm hT ⟨le_rfl, hT⟩ ht
  have h := intervalIntegral.integral_interval_sub_left hm h0t
  rw [intervalIntegral.integral_neg]
  unfold stateMultiplier
  linarith

/-- The multiplier is nonnegative for a nonnegative density. -/
theorem stateMultiplier_nonneg (hm0 : ∀ r ∈ Icc (0 : ℝ) T, 0 ≤ m r) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ stateMultiplier T m t :=
  intervalIntegral.integral_nonneg ht.2 fun r hr => hm0 r ⟨ht.1.trans hr.1, hr.2⟩

/-- The multiplier is nonincreasing on `[0,T]`: its increments are `-∫ m ≤ 0`. -/
theorem stateMultiplier_antitoneOn (hT : 0 ≤ T) (hm : IntervalIntegrable m volume 0 T)
    (hm0 : ∀ r ∈ Icc (0 : ℝ) T, 0 ≤ m r) :
    AntitoneOn (stateMultiplier T m) (Icc (0 : ℝ) T) := by
  intro s hs t ht hst
  have hst' : IntervalIntegrable m volume s t := intervalIntegrable_of_mem_Icc_Icc hm hT hs ht
  have htT : IntervalIntegrable m volume t T :=
    intervalIntegrable_of_mem_Icc_Icc hm hT ht ⟨hT, le_rfl⟩
  have hsum := intervalIntegral.integral_add_adjacent_intervals hst' htT
  have hnn : 0 ≤ ∫ r in s..t, m r :=
    intervalIntegral.integral_nonneg hst fun r hr => hm0 r ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩
  unfold stateMultiplier
  linarith

/-- The multiplier is continuous on `[0,T]`. -/
theorem stateMultiplier_continuousOn (hT : 0 ≤ T) (hm : IntervalIntegrable m volume 0 T) :
    ContinuousOn (stateMultiplier T m) (Icc (0 : ℝ) T) := by
  have hprim : ContinuousOn (fun t : ℝ => ∫ r in (0 : ℝ)..t, -m r) [[(0 : ℝ), T]] :=
    intervalIntegral.continuousOn_primitive_interval' (a := (0 : ℝ)) hm.neg (by simp [uIcc])
  rw [uIcc_of_le hT] at hprim
  refine ((continuousOn_const (c := stateMultiplier T m 0)).add hprim).congr fun t ht => ?_
  exact stateMultiplier_eq_sub hT hm ht

/-- **Complementarity.**  The multiplier is constant on every interval `[α,β] ⊆ [0,T]` on which the
multiplier density vanishes.  For the density `j ω'(G(t,γ t))` this holds on every interval on which
`G(t, γ t) ≤ 0`: the state-multiplier measure charges only the contact set.  (This is the penalty
form of Lemma 11.3.9: the multiplier of the book is constant off the contact set.)

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemma 11.3.9 and (11.6.11). -/
theorem stateMultiplier_eq_of_density_eq_zero (hT : 0 ≤ T) (hm : IntervalIntegrable m volume 0 T)
    {α β : ℝ} (hα : α ∈ Icc (0 : ℝ) T) (hβ : β ∈ Icc (0 : ℝ) T)
    (hzero : ∀ r ∈ Icc α β, m r = 0) :
    ∀ t ∈ Icc α β, stateMultiplier T m t = stateMultiplier T m α := by
  intro t ht
  have htI : t ∈ Icc (0 : ℝ) T := ⟨hα.1.trans ht.1, ht.2.trans hβ.2⟩
  have hαt : IntervalIntegrable m volume α t := intervalIntegrable_of_mem_Icc_Icc hm hT hα htI
  have htT : IntervalIntegrable m volume t T :=
    intervalIntegrable_of_mem_Icc_Icc hm hT htI ⟨hT, le_rfl⟩
  have hsum := intervalIntegral.integral_add_adjacent_intervals hαt htT
  have h0 : ∫ r in α..t, m r = 0 := by
    have : ∫ r in α..t, m r = ∫ r in α..t, (0 : ℝ) :=
      intervalIntegral.integral_congr fun r hr => by
        rw [uIcc_of_le ht.1] at hr
        exact hzero r ⟨hr.1, hr.2.trans ht.2⟩
    rw [this]
    simp
  unfold stateMultiplier
  linarith

end MultiplierCurve

section Costate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ} {m : ℝ → ℝ}

/-- Evaluating a covector-valued interval integral on a vector commutes with the integral. -/
theorem apply_intervalIntegral {f : ℝ → E →L[ℝ] ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (e : E) :
    (∫ r in a..b, f r) e = ∫ r in a..b, f r e :=
  (ContinuousLinearMap.intervalIntegral_comp_comm (ContinuousLinearMap.apply ℝ ℝ e) hf).symm

/-- A path that is the primitive of an interval integrable derivative is continuous on `[0,T]`. -/
theorem continuousOn_of_primitive {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hT : 0 ≤ T) {g g' : ℝ → F} (hg' : IntervalIntegrable g' volume 0 T)
    (hg : ∀ t ∈ Icc (0 : ℝ) T, g t = g 0 + ∫ r in (0 : ℝ)..t, g' r) :
    ContinuousOn g (Icc (0 : ℝ) T) := by
  have hprim : ContinuousOn (fun t : ℝ => ∫ r in (0 : ℝ)..t, g' r) [[(0 : ℝ), T]] :=
    intervalIntegral.continuousOn_primitive_interval' (a := (0 : ℝ)) hg' (by simp [uIcc])
  rw [uIcc_of_le hT] at hprim
  exact ((continuousOn_const (c := g 0)).add hprim).congr hg

/-- **Product rule for the multiplier against an absolutely continuous covector path.**  If
`g(t) = g(0) + ∫₀ᵗ g'` on `[0,T]` and `λ(t) = ∫_t^T m`, then
`λ(t) g(t) = λ(0) g(0) + ∫₀ᵗ (λ g' - m g)`.  This is the integrated Leibniz rule that removes the
state-multiplier *measure* `m dt` from the covector equation. -/
theorem stateMultiplier_smul_eq_primitive (hT : 0 ≤ T) (hm : IntervalIntegrable m volume 0 T)
    {g g' : ℝ → E →L[ℝ] ℝ} (hg' : IntervalIntegrable g' volume 0 T)
    (hg : ∀ t ∈ Icc (0 : ℝ) T, g t = g 0 + ∫ r in (0 : ℝ)..t, g' r) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    stateMultiplier T m t • g t = stateMultiplier T m 0 • g 0
      + ∫ r in (0 : ℝ)..t, (stateMultiplier T m r • g' r - m r • g r) := by
  have hgc := continuousOn_of_primitive hT hg' hg
  have h0t : ∀ r ∈ Icc (0 : ℝ) t, r ∈ Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hmt : IntervalIntegrable m volume 0 t :=
    intervalIntegrable_of_mem_Icc_Icc hm hT ⟨le_rfl, hT⟩ ht
  have hg't : IntervalIntegrable g' volume 0 t :=
    intervalIntegrable_of_mem_Icc_Icc hg' hT ⟨le_rfl, hT⟩ ht
  have hlam : ContinuousOn (stateMultiplier T m) (uIcc (0 : ℝ) t) := by
    rw [uIcc_of_le ht.1]
    exact (stateMultiplier_continuousOn hT hm).mono fun r hr => h0t r hr
  have hgt : ContinuousOn g (uIcc (0 : ℝ) t) := by
    rw [uIcc_of_le ht.1]
    exact hgc.mono fun r hr => h0t r hr
  have hI1 : IntervalIntegrable (fun r => stateMultiplier T m r • g' r) volume 0 t :=
    hg't.continuousOn_smul hlam
  have hI2 : IntervalIntegrable (fun r => m r • g r) volume 0 t := hmt.smul_continuousOn hgt
  ext e
  have hsc : IntervalIntegrable (fun r => g' r e) volume 0 t :=
    ACIntegrationByParts.intervalIntegrable_clm_comp (ContinuousLinearMap.apply ℝ ℝ e) hg't
  have key := ACIntegrationByParts.integral_mul_add_mul_eq_sub_of_primitive
    (g := fun r => -m r) (s := fun r => g' r e) (a₀ := stateMultiplier T m 0)
    (c₀ := g 0 e) hmt.neg hsc
  have hgr : ∀ r ∈ Icc (0 : ℝ) t, g 0 e + ∫ x in (0 : ℝ)..r, g' x e = g r e := by
    intro r hr
    have hr' : IntervalIntegrable g' volume 0 r :=
      intervalIntegrable_of_mem_Icc_Icc hg' hT ⟨le_rfl, hT⟩ (h0t r hr)
    rw [hg r (h0t r hr), add_apply, apply_intervalIntegral hr' e]
  have hlr : ∀ r ∈ Icc (0 : ℝ) t,
      stateMultiplier T m 0 + ∫ x in (0 : ℝ)..r, -m x = stateMultiplier T m r := fun r hr =>
    (stateMultiplier_eq_sub hT hm (h0t r hr)).symm
  have hcongr : ∫ r in (0 : ℝ)..t, (-m r * (g 0 e + ∫ x in (0 : ℝ)..r, g' x e)
      + (stateMultiplier T m 0 + ∫ x in (0 : ℝ)..r, -m x) * g' r e)
      = ∫ r in (0 : ℝ)..t, (-(m r * g r e) + stateMultiplier T m r * g' r e) :=
    intervalIntegral.integral_congr fun r hr => by
      rw [uIcc_of_le ht.1] at hr
      rw [hgr r hr, hlr r hr]
      ring
  rw [hcongr] at key
  have hint : (∫ r in (0 : ℝ)..t, (stateMultiplier T m r • g' r - m r • g r)) e
      = ∫ r in (0 : ℝ)..t, (-(m r * g r e) + stateMultiplier T m r * g' r e) := by
    rw [apply_intervalIntegral (hI1.sub hI2) e]
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp only [sub_apply, smul_apply, smul_eq_mul]
    ring
  rw [add_apply, hint, key, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
  have h1 := hgr t ⟨ht.1, le_rfl⟩
  have h2 := hlr t ⟨ht.1, le_rfl⟩
  rw [← h1, ← h2]
  ring

/-- **The costate `Φ = p + λ ∇G` has a measure-free equation.**  Let `p(t) = c + ∫₀ᵗ (a + m g)` be
the integrated covector with state-multiplier density `m` and gradient path `g` (an absolutely
continuous covector path with derivative `g'`), and `λ(t) = ∫_t^T m`.  Then
`Φ(t) = p(t) + λ(t) g(t)` satisfies, on `[0,T]`,

`Φ(t) = Φ(0) + ∫₀ᵗ (a + λ g')`,  `Φ(0) = c + λ(0) g(0)`.

This is the integrated form of (11.6.11), `Φ' = ∂ₓL + λ d(∇G)/dt`, with the initial condition
(11.6.6); the multiplier measure `m dt` no longer appears.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.6.6) and (11.6.11). -/
theorem stateCostate_eq_primitive (hT : 0 ≤ T) (hm : IntervalIntegrable m volume 0 T)
    {a g g' : ℝ → E →L[ℝ] ℝ} (c : E →L[ℝ] ℝ) (ha : IntervalIntegrable a volume 0 T)
    (hg' : IntervalIntegrable g' volume 0 T)
    (hg : ∀ t ∈ Icc (0 : ℝ) T, g t = g 0 + ∫ r in (0 : ℝ)..t, g' r) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    (c + ∫ r in (0 : ℝ)..t, (a r + m r • g r)) + stateMultiplier T m t • g t
      = (c + stateMultiplier T m 0 • g 0)
        + ∫ r in (0 : ℝ)..t, (a r + stateMultiplier T m r • g' r) := by
  have hgc := continuousOn_of_primitive hT hg' hg
  have h0t : ∀ r ∈ Icc (0 : ℝ) t, r ∈ Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hmt : IntervalIntegrable m volume 0 t :=
    intervalIntegrable_of_mem_Icc_Icc hm hT ⟨le_rfl, hT⟩ ht
  have hat : IntervalIntegrable a volume 0 t :=
    intervalIntegrable_of_mem_Icc_Icc ha hT ⟨le_rfl, hT⟩ ht
  have hg't : IntervalIntegrable g' volume 0 t :=
    intervalIntegrable_of_mem_Icc_Icc hg' hT ⟨le_rfl, hT⟩ ht
  have hlam : ContinuousOn (stateMultiplier T m) (uIcc (0 : ℝ) t) := by
    rw [uIcc_of_le ht.1]
    exact (stateMultiplier_continuousOn hT hm).mono fun r hr => h0t r hr
  have hgt : ContinuousOn g (uIcc (0 : ℝ) t) := by
    rw [uIcc_of_le ht.1]
    exact hgc.mono fun r hr => h0t r hr
  have hI1 : IntervalIntegrable (fun r => stateMultiplier T m r • g' r) volume 0 t :=
    hg't.continuousOn_smul hlam
  have hI2 : IntervalIntegrable (fun r => m r • g r) volume 0 t := hmt.smul_continuousOn hgt
  have hB := stateMultiplier_smul_eq_primitive hT hm hg' hg ht
  rw [intervalIntegral.integral_sub hI1 hI2] at hB
  rw [intervalIntegral.integral_add hat hI2, intervalIntegral.integral_add hat hI1, hB]
  abel

/-- Pairing an interval integrable covector path with a continuous vector path is interval
integrable. -/
theorem intervalIntegrable_clm_apply_of_continuousOn {f : ℝ → E →L[ℝ] ℝ} {k : ℝ → E}
    (hT : 0 ≤ T) (hf : IntervalIntegrable f volume 0 T) (hk : ContinuousOn k (Icc (0 : ℝ) T)) :
    IntervalIntegrable (fun r => f r (k r)) volume 0 T := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hk
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioc (0 : ℝ) T)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hf).aestronglyMeasurable
  have hkm : AEStronglyMeasurable k (volume.restrict (Ioc (0 : ℝ) T)) :=
    (hk.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  refine IntervalIntegrable.mono_fun' (g := fun r => ‖f r‖ * M) (hf.norm.mul_const M) ?_ ?_
  · rw [uIoc_of_le hT]
    exact ContinuousLinearMap.aestronglyMeasurable_comp₂
      (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)) hfm hkm
  · rw [uIoc_of_le hT, Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun r hr => ?_
    calc ‖f r (k r)‖ ≤ ‖f r‖ * ‖k r‖ := (f r).le_opNorm (k r)
      _ ≤ ‖f r‖ * M := mul_le_mul_of_nonneg_left (hM r ⟨hr.1.le, hr.2⟩) (norm_nonneg _)

/-- Pairing a continuous covector path with an interval integrable vector path is interval
integrable. -/
theorem intervalIntegrable_clm_apply_of_continuousOn' {f : ℝ → E →L[ℝ] ℝ} {k : ℝ → E}
    (hT : 0 ≤ T) (hf : ContinuousOn f (Icc (0 : ℝ) T)) (hk : IntervalIntegrable k volume 0 T) :
    IntervalIntegrable (fun r => f r (k r)) volume 0 T := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hkm : AEStronglyMeasurable k (volume.restrict (Ioc (0 : ℝ) T)) :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hk).aestronglyMeasurable
  have hfm : AEStronglyMeasurable f (volume.restrict (Ioc (0 : ℝ) T)) :=
    (hf.mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  refine IntervalIntegrable.mono_fun' (g := fun r => M * ‖k r‖) (hk.norm.const_mul M) ?_ ?_
  · rw [uIoc_of_le hT]
    exact ContinuousLinearMap.aestronglyMeasurable_comp₂
      (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)) hfm hkm
  · rw [uIoc_of_le hT, Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun r hr => ?_
    calc ‖f r (k r)‖ ≤ ‖f r‖ * ‖k r‖ := (f r).le_opNorm (k r)
      _ ≤ M * ‖k r‖ := mul_le_mul_of_nonneg_right (hM r ⟨hr.1.le, hr.2⟩) (norm_nonneg _)

/-- **Boundary-perturbation identity for the total multiplier mass.**  Let
`p(t) = c + ∫₀ᵗ (a + m g)` be the integrated covector with multiplier density `m ≥ 0`, and let
`h = h(0) + ∫₀ᵗ h'` be an absolutely continuous test field with `⟨∇G, h⟩ = 1` on the support of
`m` (the book's outward direction `h = ∇G/|∇G|²`).  Then

`∫₀ᵀ m = ⟨p(T), h(T)⟩ - ⟨c, h(0)⟩ - ∫₀ᵀ (⟨a, h⟩ + ⟨p, h'⟩)`:

the total mass of the state-multiplier measure is read off from the endpoint covectors, the
`∂ₓL` along the path and the momentum, so it is bounded uniformly whenever these are.  This is the
estimate that makes the multipliers `λ_j(0) = ∫₀ᵀ m_j` bounded, so Helly's selection applies.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemma 11.3.5 and (11.6.11). -/
theorem integral_density_eq_boundary [FiniteDimensional ℝ E] [CompleteSpace E] (hT : 0 ≤ T)
    (hm : IntervalIntegrable m volume 0 T)
    {a g : ℝ → E →L[ℝ] ℝ} (c : E →L[ℝ] ℝ) (ha : IntervalIntegrable a volume 0 T)
    (hgc : ContinuousOn g (Icc (0 : ℝ) T)) {h h' : ℝ → E}
    (hh' : IntervalIntegrable h' volume 0 T)
    (hh : ∀ t ∈ Icc (0 : ℝ) T, h t = h 0 + ∫ r in (0 : ℝ)..t, h' r)
    (hnorm : ∀ r ∈ Icc (0 : ℝ) T, m r * g r (h r) = m r) :
    ∫ r in (0 : ℝ)..T, m r
      = (c + ∫ r in (0 : ℝ)..T, (a r + m r • g r)) (h T) - c (h 0)
        - ∫ r in (0 : ℝ)..T, (a r (h r)
          + (c + ∫ s in (0 : ℝ)..r, (a s + m s • g s)) (h' r)) := by
  have hgm : IntervalIntegrable (fun r => m r • g r) volume 0 T :=
    hm.smul_continuousOn (by rwa [uIcc_of_le hT])
  have hA : IntervalIntegrable (fun r => a r + m r • g r) volume 0 T := ha.add hgm
  have hhc := continuousOn_of_primitive hT hh' hh
  have hpc : ContinuousOn (fun r => c + ∫ s in (0 : ℝ)..r, (a s + m s • g s)) (Icc (0 : ℝ) T) := by
    have hprim : ContinuousOn (fun t : ℝ => ∫ r in (0 : ℝ)..t, (a r + m r • g r))
        [[(0 : ℝ), T]] :=
      intervalIntegral.continuousOn_primitive_interval' (a := (0 : ℝ)) hA (by simp [uIcc])
    rw [uIcc_of_le hT] at hprim
    exact (continuousOn_const (c := c)).add hprim
  have key := ACIntegrationByParts.integral_apply_add_apply_eq_sub_of_primitive
    (g := fun r => a r + m r • g r) (w := h') (p₀ := c) (a := h 0) hT hA hh'
  have hcongr : ∫ t in (0 : ℝ)..T, ((a t + m t • g t) (h 0 + ∫ r in (0 : ℝ)..t, h' r)
        + (c + ∫ r in (0 : ℝ)..t, (a r + m r • g r)) (h' t))
      = ∫ t in (0 : ℝ)..T, ((a t (h t) + (c + ∫ r in (0 : ℝ)..t, (a r + m r • g r)) (h' t))
          + m t) :=
    intervalIntegral.integral_congr fun t ht => by
      rw [uIcc_of_le hT] at ht
      simp only [← hh t ht, add_apply, smul_apply, smul_eq_mul, hnorm t ht]
      ring
  have h1 : IntervalIntegrable (fun r => a r (h r)) volume 0 T :=
    intervalIntegrable_clm_apply_of_continuousOn hT ha hhc
  have h2 : IntervalIntegrable
      (fun r => (c + ∫ s in (0 : ℝ)..r, (a s + m s • g s)) (h' r)) volume 0 T :=
    intervalIntegrable_clm_apply_of_continuousOn' hT hpc hh'
  rw [hcongr, intervalIntegral.integral_add (h1.add h2) hm, intervalIntegral.integral_add h1 h2,
    ← hh T ⟨hT, le_rfl⟩] at key
  rw [intervalIntegral.integral_add h1 h2]
  linarith

end Costate

section AbsolutelyContinuous

/-- A function whose increments are dominated by those of an absolutely continuous scalar function
is absolutely continuous.  (Domination version of
`LipschitzOnWith.comp_absolutelyContinuousOnInterval`.) -/
theorem absolutelyContinuousOnInterval_of_dist_le {X : Type*} [PseudoMetricSpace X] {f : ℝ → X}
    {Λ : ℝ → ℝ} {K : ℝ} {a b : ℝ} (hΛ : AbsolutelyContinuousOnInterval Λ a b)
    (h : ∀ x ∈ uIcc a b, ∀ y ∈ uIcc a b, dist (f x) (f y) ≤ K * dist (Λ x) (Λ y)) :
    AbsolutelyContinuousOnInterval f a b := by
  apply squeeze_zero' ?_ ?_ (by simpa using Tendsto.const_mul K hΛ)
  · exact .of_forall fun _ => Finset.sum_nonneg fun _ _ => dist_nonneg
  rw [eventually_inf_principal]
  filter_upwards with (n, I) hnI
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi => h _ (hnI.left i hi).left _ (hnI.left i hi).right

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The primitive of an interval integrable vector-valued function is absolutely continuous. -/
theorem absolutelyContinuousOnInterval_integral {d : ℝ → F} {T : ℝ} (hd : IntervalIntegrable d
    volume 0 T)
    : AbsolutelyContinuousOnInterval (fun t => ∫ r in (0 : ℝ)..t, d r) 0 T := by
  have hΛ : AbsolutelyContinuousOnInterval (fun t => ∫ r in (0 : ℝ)..t, ‖d r‖) 0 T :=
    hd.norm.absolutelyContinuousOnInterval_intervalIntegral (by simp [uIcc])
  refine absolutelyContinuousOnInterval_of_dist_le (K := 1) hΛ fun x hx y hy => ?_
  have h0x : IntervalIntegrable d volume 0 x := hd.mono_set (uIcc_subset_uIcc_left hx)
  have h0y : IntervalIntegrable d volume 0 y := hd.mono_set (uIcc_subset_uIcc_left hy)
  have e1 : (∫ r in (0 : ℝ)..x, d r) - ∫ r in (0 : ℝ)..y, d r = ∫ r in y..x, d r :=
    intervalIntegral.integral_interval_sub_left h0x h0y
  have e2 : (∫ r in (0 : ℝ)..x, ‖d r‖) - ∫ r in (0 : ℝ)..y, ‖d r‖ = ∫ r in y..x, ‖d r‖ :=
    intervalIntegral.integral_interval_sub_left h0x.norm h0y.norm
  rw [dist_eq_norm, Real.dist_eq, e1, e2, one_mul]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

variable [CompleteSpace F]

/-- **Fundamental theorem of calculus for absolutely continuous vector-valued functions.**  If `f`
is
absolutely continuous on `[0,T]` and has derivative `d ∈ L¹` almost everywhere, then
`f(t) = f(0) + ∫₀ᵗ d` on `[0,T]`. -/
theorem eq_add_integral_of_absolutelyContinuousOnInterval {f d : ℝ → F} {T : ℝ} (hT : 0 ≤ T)
    (hd : IntervalIntegrable d volume 0 T) (hf : AbsolutelyContinuousOnInterval f 0 T)
    (hder : ∀ᵐ t, t ∈ uIcc (0 : ℝ) T → HasDerivAt f (d t) t) :
    ∀ t ∈ Icc (0 : ℝ) T, f t = f 0 + ∫ r in (0 : ℝ)..t, d r := by
  have hP := absolutelyContinuousOnInterval_integral hd
  have hu : AbsolutelyContinuousOnInterval (fun t => f t - ∫ r in (0 : ℝ)..t, d r) 0 T :=
    hf.sub hP
  have hleb := hd.ae_hasDerivAt_integral
  have hzero : ∀ᵐ t, t ∈ uIcc (0 : ℝ) T →
      HasDerivAt (fun t => f t - ∫ r in (0 : ℝ)..t, d r) 0 t := by
    filter_upwards [hder, hleb] with t h1 h2 ht
    have := (h1 ht).sub (h2 ht 0 (by simp [uIcc]))
    rw [sub_self] at this
    exact this
  obtain ⟨C, hC⟩ := hu.const_of_ae_hasDerivAt_zero hzero
  intro t ht
  have h1 := hC t (by rw [uIcc_of_le hT]; exact ht)
  have h2 := hC 0 (by simp [uIcc])
  simp only [intervalIntegral.integral_same, sub_zero] at h2
  have : f t - ∫ r in (0 : ℝ)..t, d r = f 0 := h1.trans h2.symm
  rw [← this]
  abel

/-- A function equal to a primitive of an interval integrable function on `[0,T]` has that function
as derivative almost everywhere on the horizon. -/
theorem ae_hasDerivAt_of_eq_primitive {Φ f : ℝ → F} {T : ℝ} (hT : 0 ≤ T)
    (hf : IntervalIntegrable f volume 0 T)
    (hΦ : ∀ t ∈ Icc (0 : ℝ) T, Φ t = Φ 0 + ∫ r in (0 : ℝ)..t, f r) :
    ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) T)), HasDerivAt Φ (f t) t := by
  have h := hf.ae_hasDerivAt_integral
  rw [uIcc_of_le hT] at h
  have hnull : ∀ᵐ t : ℝ, t ≠ T := by simp [ae_iff]
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [h, hnull] with t ht htT htm
  have hd := (ht (Ioc_subset_Icc_self htm) 0 ⟨le_rfl, hT⟩).const_add (Φ 0)
  refine hd.congr_of_eventuallyEq ?_
  exact Filter.eventuallyEq_of_mem (Ioo_mem_nhds htm.1 (lt_of_le_of_ne htm.2 htT))
    fun u hu => hΦ u (Ioo_subset_Icc_self hu)

end AbsolutelyContinuous

section Carrier

variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]
  {P : Problem E V W}

/-- Second-order regularity of the state constraint: the state covector `Gx = ∇G` is jointly
differentiable in `(t,y)` with derivative `Gxd`, which is measurable and bounded on bounded sets of
states.  The derivative of `t ↦ ∇G(t,γ(t))` along a path is `Gxd (1, γ')`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Assumption 11.6.1 and (11.6.11).
-/
structure StateGradientRegularity (Gx : ℝ → E → E →L[ℝ] ℝ)
    (Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)) : Prop where
  /-- `Gxd` is the joint Fréchet derivative of `Gx` in `(t,y)`. -/
  hasFDerivAt : ∀ t y, HasFDerivAt (fun q : ℝ × E => Gx q.1 q.2) (Gxd t y) (t, y)
  /-- `Gxd` is jointly measurable. -/
  measurable : Measurable (fun p : ℝ × E => Gxd p.1 p.2)
  /-- `Gxd` is bounded on bounded sets of states. -/
  bounded : ∀ R : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t y, ‖y‖ ≤ R → ‖Gxd t y‖ ≤ C

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The path of a velocity trajectory is absolutely continuous on the horizon. -/
theorem VelocityTrajectory.absolutelyContinuousOnInterval_value (γ : VelocityTrajectory P) :
    AbsolutelyContinuousOnInterval γ.value 0 P.horizon := by
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => γ.initial) 0 P.horizon :=
    (LipschitzWith.const γ.initial).lipschitzOnWith.absolutelyContinuousOnInterval
  exact hc.add (absolutelyContinuousOnInterval_integral γ.velocity_intervalIntegrable)

/-- The arc-length parameter `t ↦ t + ∫₀ᵗ ‖γ'‖` of a velocity trajectory: an absolutely continuous
nondecreasing function whose increments dominate those of the path and of every Lipschitz function
of `(t, γ(t))`. -/
noncomputable def VelocityTrajectory.arcParameter (γ : VelocityTrajectory P) (t : ℝ) : ℝ :=
  t + ∫ r in (0 : ℝ)..t, ‖γ.velocity r‖

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The arc-length parameter is absolutely continuous on the horizon. -/
theorem VelocityTrajectory.absolutelyContinuousOnInterval_arcParameter (γ : VelocityTrajectory P) :
    AbsolutelyContinuousOnInterval γ.arcParameter 0 P.horizon :=
  (LipschitzWith.id.lipschitzOnWith (s := uIcc (0 : ℝ) P.horizon)
    ).absolutelyContinuousOnInterval.add
    (γ.velocity_intervalIntegrable.norm.absolutelyContinuousOnInterval_intervalIntegral
      (by simp [uIcc]))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The increments of the arc-length parameter dominate those of the path:
`‖γ x - γ y‖ ≤ |x - y| + |∫_y^x ‖γ'‖| = dist (Λ x) (Λ y)` for the `Λ = arcParameter`, and the
distance of the arc-length parameter is `|x - y| + |∫_y^x ‖γ'‖|`. -/
theorem VelocityTrajectory.dist_arcParameter (γ : VelocityTrajectory P) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) P.horizon) (hy : y ∈ Icc (0 : ℝ) P.horizon) :
    dist (γ.arcParameter x) (γ.arcParameter y)
      = |x - y| + |∫ r in y..x, ‖γ.velocity r‖| := by
  have hT : 0 ≤ P.horizon := P.horizon_pos.le
  have hnorm : IntervalIntegrable (fun r => ‖γ.velocity r‖) volume 0 P.horizon :=
    γ.velocity_intervalIntegrable.norm
  have h0x : IntervalIntegrable (fun r => ‖γ.velocity r‖) volume 0 x :=
    intervalIntegrable_of_mem_Icc_Icc hnorm hT ⟨le_rfl, hT⟩ hx
  have h0y : IntervalIntegrable (fun r => ‖γ.velocity r‖) volume 0 y :=
    intervalIntegrable_of_mem_Icc_Icc hnorm hT ⟨le_rfl, hT⟩ hy
  have e2 : (∫ r in (0 : ℝ)..x, ‖γ.velocity r‖) - ∫ r in (0 : ℝ)..y, ‖γ.velocity r‖
      = ∫ r in y..x, ‖γ.velocity r‖ := intervalIntegral.integral_interval_sub_left h0x h0y
  unfold VelocityTrajectory.arcParameter
  rw [Real.dist_eq]
  have e3 : x + (∫ r in (0 : ℝ)..x, ‖γ.velocity r‖)
      - (y + ∫ r in (0 : ℝ)..y, ‖γ.velocity r‖) = (x - y) + ∫ r in y..x, ‖γ.velocity r‖ := by
    rw [← e2]; ring
  rw [e3]
  rcases le_total y x with h | h
  · have hI : 0 ≤ ∫ r in y..x, ‖γ.velocity r‖ :=
      intervalIntegral.integral_nonneg h fun _ _ => norm_nonneg _
    rw [abs_of_nonneg (sub_nonneg.2 h), abs_of_nonneg hI, abs_of_nonneg (by linarith)]
  · have hI : 0 ≤ ∫ r in x..y, ‖γ.velocity r‖ :=
      intervalIntegral.integral_nonneg h fun _ _ => norm_nonneg _
    have hsym : ∫ r in y..x, ‖γ.velocity r‖ = -∫ r in x..y, ‖γ.velocity r‖ :=
      intervalIntegral.integral_symm x y
    rw [hsym, abs_neg, abs_of_nonneg hI, abs_of_nonpos (sub_nonpos.2 h),
      abs_of_nonpos (by linarith)]
    ring

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ V]
  [BorelSpace V] in
/-- The increment of the path is dominated by that of the arc-length parameter. -/
theorem VelocityTrajectory.norm_value_sub_le (γ : VelocityTrajectory P) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) P.horizon) (hy : y ∈ Icc (0 : ℝ) P.horizon) :
    ‖γ.value x - γ.value y‖ ≤ |∫ r in y..x, ‖γ.velocity r‖| := by
  rw [γ.value_sub_value hy hx]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

/-- **The gradient along an `L²`-velocity path: absolute continuity, derivative, and bounds.**
Let `γ` be a velocity trajectory with `‖γ t‖ ≤ R` on `[0,T]` and let `‖∇²G‖ ≤ C` on the ball of
radius
`R`.  Then `t ↦ ∇G(t, γ(t))` is absolutely continuous with a.e. derivative
`∇²G(t,γ(t)) (1, γ'(t))`, an interval integrable function bounded by `C (1 + ‖γ'‖)`, and its
increments are dominated by `C` times those of the arc-length parameter.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.6.11). -/
theorem VelocityTrajectory.gradientAlongPath_aux (γ : VelocityTrajectory P)
    {Gx : ℝ → E → E →L[ℝ] ℝ} {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)}
    (hG : StateGradientRegularity Gx Gxd) {R C : ℝ} (hC0 : 0 ≤ C)
    (hR : ∀ t ∈ Icc (0 : ℝ) P.horizon, ‖γ.value t‖ ≤ R)
    (hC : ∀ t y, ‖y‖ ≤ R → ‖Gxd t y‖ ≤ C) :
    IntervalIntegrable (fun r => Gxd r (γ.value r) (1, γ.velocity r)) volume 0 P.horizon ∧
      AbsolutelyContinuousOnInterval (fun t => Gx t (γ.value t)) 0 P.horizon ∧
      (∀ᵐ t, t ∈ uIcc (0 : ℝ) P.horizon → HasDerivAt (fun t => Gx t (γ.value t))
        (Gxd t (γ.value t) (1, γ.velocity t)) t) ∧
      (∀ x ∈ Icc (0 : ℝ) P.horizon, ∀ y ∈ Icc (0 : ℝ) P.horizon,
        dist (Gx x (γ.value x)) (Gx y (γ.value y)) ≤ C * dist (γ.arcParameter x) (γ.arcParameter
            y)) ∧
      (∀ᵐ r ∂(timeMeasure P.horizon), ‖Gxd r (γ.value r) (1, γ.velocity r)‖
        ≤ C * (1 + ‖γ.velocity r‖)) := by
  have hT : 0 ≤ P.horizon := P.horizon_pos.le
  have hvint := γ.velocity_intervalIntegrable
  -- Lipschitz estimate along the path
  have hlip : ∀ x ∈ Icc (0 : ℝ) P.horizon, ∀ y ∈ Icc (0 : ℝ) P.horizon,
      ‖Gx x (γ.value x) - Gx y (γ.value y)‖ ≤ C * (|x - y| + ‖γ.value x - γ.value y‖) := by
    intro x hx y hy
    have hconv : Convex ℝ ((univ : Set ℝ) ×ˢ Metric.closedBall (0 : E) R) :=
      convex_univ.prod (convex_closedBall 0 R)
    have hmem : ∀ z ∈ Icc (0 : ℝ) P.horizon, (z, γ.value z) ∈
        (univ : Set ℝ) ×ˢ Metric.closedBall (0 : E) R := fun z hz =>
      ⟨mem_univ _, by simpa using hR z hz⟩
    have hmv := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun q : ℝ × E => Gx q.1 q.2) (f' := fun q => Gxd q.1 q.2) (C := C)
      (fun q _ => (hG.hasFDerivAt q.1 q.2).hasFDerivWithinAt)
      (fun q hq => hC q.1 q.2 (by simpa using hq.2)) (hmem y hy) (hmem x hx)
    refine hmv.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    rw [Prod.mk_sub_mk, Prod.norm_def]
    exact max_le (by simp [Real.norm_eq_abs])
      (le_add_of_nonneg_left (abs_nonneg _))
  -- domination by the increments of the arc-length parameter
  have hdom : ∀ x ∈ Icc (0 : ℝ) P.horizon, ∀ y ∈ Icc (0 : ℝ) P.horizon,
      dist (Gx x (γ.value x)) (Gx y (γ.value y)) ≤ C * dist (γ.arcParameter x) (γ.arcParameter y)
          := by
    intro x hx y hy
    rw [dist_eq_norm, γ.dist_arcParameter hx hy]
    exact (hlip x hx y hy).trans
      (mul_le_mul_of_nonneg_left (by linarith [γ.norm_value_sub_le hx hy]) hC0)
  have hAC : AbsolutelyContinuousOnInterval (fun t => Gx t (γ.value t)) 0 P.horizon :=
    absolutelyContinuousOnInterval_of_dist_le (K := C) γ.absolutelyContinuousOnInterval_arcParameter
      fun x hx y hy => by
        rw [uIcc_of_le hT] at hx hy
        exact hdom x hx y hy
  -- the a.e. derivative is `Gxd (1, γ')`
  have hder : ∀ᵐ t, t ∈ uIcc (0 : ℝ) P.horizon → HasDerivAt (fun t => Gx t (γ.value t))
      (Gxd t (γ.value t) (1, γ.velocity t)) t := by
    have h := γ.ae_hasDerivAt_value
    rw [ae_restrict_iff' measurableSet_Icc] at h
    filter_upwards [h] with t ht htm
    rw [uIcc_of_le hT] at htm
    have hp : HasDerivAt (fun t => ((t, γ.value t) : ℝ × E)) (1, γ.velocity t) t :=
      (hasDerivAt_id t).prodMk (ht htm)
    exact (hG.hasFDerivAt t (γ.value t)).comp_hasDerivAt t hp
  -- the pointwise bound
  have hbound : ∀ r ∈ Ioc (0 : ℝ) P.horizon, ‖Gxd r (γ.value r) (1, γ.velocity r)‖
      ≤ C * (1 + ‖γ.velocity r‖) := by
    intro r hr
    have h1 := (Gxd r (γ.value r)).le_opNorm (1, γ.velocity r)
    have h2 := hC r (γ.value r) (hR r ⟨hr.1.le, hr.2⟩)
    have h3 : ‖((1 : ℝ), γ.velocity r)‖ ≤ 1 + ‖γ.velocity r‖ := by
      rw [Prod.norm_def]
      exact max_le (by simp) (by linarith [norm_nonneg (γ.velocity r)])
    calc ‖Gxd r (γ.value r) (1, γ.velocity r)‖
        ≤ ‖Gxd r (γ.value r)‖ * ‖((1 : ℝ), γ.velocity r)‖ := h1
      _ ≤ C * (1 + ‖γ.velocity r‖) :=
        mul_le_mul h2 h3 (norm_nonneg _) hC0
  -- integrability of the derivative
  have hint : IntervalIntegrable (fun r => Gxd r (γ.value r) (1, γ.velocity r)) volume
      0 P.horizon := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
    have hv : IntegrableOn γ.velocity (Ioc (0 : ℝ) P.horizon) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hvint
    have hmeasγ : AEMeasurable γ.value (volume.restrict (Ioc (0 : ℝ) P.horizon)) :=
      (γ.continuousOn_value.mono Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc
    have hA : AEStronglyMeasurable (fun r => Gxd r (γ.value r))
        (volume.restrict (Ioc (0 : ℝ) P.horizon)) :=
      (hG.measurable.comp_aemeasurable (aemeasurable_id.prodMk hmeasγ)).aestronglyMeasurable
    have hw : AEStronglyMeasurable (fun r => ((1 : ℝ), γ.velocity r))
        (volume.restrict (Ioc (0 : ℝ) P.horizon)) :=
      aestronglyMeasurable_const.prodMk hv.aestronglyMeasurable
    have hd := ContinuousLinearMap.aestronglyMeasurable_comp₂
      (ContinuousLinearMap.id ℝ ((ℝ × E) →L[ℝ] (E →L[ℝ] ℝ))) hA hw
    refine Integrable.mono' (g := fun r => C * (1 + ‖γ.velocity r‖))
      (((integrable_const (1 : ℝ)).add hv.norm).const_mul C) hd ?_
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall hbound
  refine ⟨hint, hAC, hder, hdom, ?_⟩
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Filter.Eventually.of_forall hbound

/-- **The gradient along an `L²`-velocity path is absolutely continuous.**  For a velocity
trajectory `γ` and a state covector `Gx = ∇G` with second-order regularity, the covector path
`t ↦ ∇G(t, γ(t))` is the primitive of `t ↦ ∇²G(t, γ(t)) (1, γ'(t))` (an `L¹` function), i.e.
`d(∇G)/dt = ∇²G (1, γ')` and `∇G(t,γ(t)) = ∇G(0,γ(0)) + ∫₀ᵗ d(∇G)/dt`.  This is the term
`λ d(∇G)/dt` of the costate equation (11.6.11).

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.6.11). -/
theorem VelocityTrajectory.gradientAlongPath_eq_primitive (γ : VelocityTrajectory P)
    {Gx : ℝ → E → E →L[ℝ] ℝ} {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)}
    (hG : StateGradientRegularity Gx Gxd) :
    IntervalIntegrable (fun r => Gxd r (γ.value r) (1, γ.velocity r)) volume 0 P.horizon ∧
      ∀ t ∈ Icc (0 : ℝ) P.horizon, Gx t (γ.value t)
        = Gx 0 (γ.value 0) + ∫ r in (0 : ℝ)..t, Gxd r (γ.value r) (1, γ.velocity r) := by
  have hT : 0 ≤ P.horizon := P.horizon_pos.le
  obtain ⟨R, hR⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := P.horizon)).exists_bound_of_continuousOn
    γ.continuousOn_value
  obtain ⟨C, hC0, hC⟩ := hG.bounded R
  obtain ⟨hint, hAC, hder, -, -⟩ := γ.gradientAlongPath_aux hG hC0 hR hC
  exact ⟨hint, eq_add_integral_of_absolutelyContinuousOnInterval hT hint hAC hder⟩

/-- The multiplier density `j ω'(G(t, γ(t)))` of the state-multiplier measure at level `j`: the
density of the book's measure `dμ_j` of (11.6.9)-(11.6.10) along the carrier `γ`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.6.9)-(11.6.10). -/
noncomputable def statePenaltyDensity (ω' : ℝ → ℝ) (G : ℝ → E → ℝ) (j : ℝ)
    (γ : VelocityTrajectory P) (r : ℝ) : ℝ :=
  j * ω' (G r (γ.value r))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The multiplier density is nonnegative for `j ≥ 0`. -/
theorem statePenaltyDensity_nonneg {ω ω' : ℝ → ℝ} (hω : StatePenaltyProfile ω ω')
    (G : ℝ → E → ℝ) {j : ℝ} (hj : 0 ≤ j) (γ : VelocityTrajectory P) (r : ℝ) :
    0 ≤ statePenaltyDensity ω' G j γ r :=
  mul_nonneg hj (hω.deriv_nonneg _)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
/-- The multiplier density vanishes wherever the state constraint holds: the penalty exerts no force
on slack states or on the contact set.  This is the complementarity condition at level `j`. -/
theorem statePenaltyDensity_eq_zero_of_nonpos {ω ω' : ℝ → ℝ} (hω : StatePenaltyProfile ω ω')
    (G : ℝ → E → ℝ) (j : ℝ) (γ : VelocityTrajectory P) {r : ℝ} (hr : G r (γ.value r) ≤ 0) :
    statePenaltyDensity ω' G j γ r = 0 := by
  unfold statePenaltyDensity
  rw [hω.deriv_eq_zero_of_nonpos hr, mul_zero]

/-- The multiplier density is interval integrable on the horizon. -/
theorem intervalIntegrable_statePenaltyDensity {ω ω' : ℝ → ℝ} (hω : StatePenaltyProfile ω ω')
    {G : ℝ → E → ℝ} {Gx : ℝ → E → E →L[ℝ] ℝ} (hG : StateConstraintRegularity G Gx) (j : ℝ)
    (γ : VelocityTrajectory P) :
    IntervalIntegrable (statePenaltyDensity ω' G j γ) volume 0 P.horizon := by
  have hT : 0 ≤ P.horizon := P.horizon_pos.le
  obtain ⟨R, hR⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := P.horizon)).exists_bound_of_continuousOn
    γ.continuousOn_value
  obtain ⟨CG, hCG0, hGb⟩ := hG.bounded R
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -CG) (b := CG)).exists_bound_of_continuousOn
    hω.continuous_deriv.continuousOn
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hT]
  have hmeasγ : AEMeasurable γ.value (volume.restrict (Ioc (0 : ℝ) P.horizon)) :=
    (γ.continuousOn_value.mono Ioc_subset_Icc_self).aemeasurable measurableSet_Ioc
  have hmeas : AEStronglyMeasurable (statePenaltyDensity ω' G j γ)
      (volume.restrict (Ioc (0 : ℝ) P.horizon)) := by
    have h1 : AEMeasurable (fun r => G r (γ.value r)) (volume.restrict (Ioc (0 : ℝ) P.horizon)) :=
      hG.measurable_G.comp_aemeasurable (aemeasurable_id.prodMk hmeasγ)
    exact ((hω.continuous_deriv.measurable.comp_aemeasurable h1).const_mul j).aestronglyMeasurable
  refine Integrable.mono' (g := fun _ => |j| * M) (integrable_const _) hmeas ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Filter.Eventually.of_forall fun r hr => ?_
  have hGr := (hGb r (γ.value r) (hR r ⟨hr.1.le, hr.2⟩)).1
  have h1 := hM (G r (γ.value r)) ⟨by linarith [(abs_le.1 hGr).1], (abs_le.1 hGr).2⟩
  unfold statePenaltyDensity
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using h1) (abs_nonneg _)

/-- The costate `Φ = p + λ ∇G` of the penalised functional at level `j`:
`Φ(t) = c + ∫₀ᵗ (a + m g) + λ(t) g(t)` with `a = ∂ₓL` along the path, `m` the multiplier density,
`g = ∇G(t,γ(t))` and `λ = ∫_t^T m`.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.6.6) and (11.6.11). -/
noncomputable def stateCostate (T : ℝ) (m : ℝ → ℝ) (c : E →L[ℝ] ℝ) (a g : ℝ → E →L[ℝ] ℝ)
    (t : ℝ) : E →L[ℝ] ℝ :=
  (c + ∫ r in (0 : ℝ)..t, (a r + m r • g r)) + stateMultiplier T m t • g t

/-- **The state-multiplier curve of the `ω`-penalised functional.**  For `j ≥ 0` the multiplier
`λ_j(t) = j ∫_t^T ω'(G(r, γ r)) dr` is nonnegative, nonincreasing, continuous, vanishes at `T`, and
is
constant on every interval `[α,β]` on which `G(r, γ r) ≤ 0` (the constraint measure is carried by
the
set where the state actually touches the constraint).

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.6.11) and Lemma 11.3.9. -/
theorem VelocityTrajectory.statePenaltyMultiplier_properties (γ : VelocityTrajectory P)
    {ω ω' : ℝ → ℝ} (hω : StatePenaltyProfile ω ω') {G : ℝ → E → ℝ} {Gx : ℝ → E → E →L[ℝ] ℝ}
    (hG : StateConstraintRegularity G Gx) {j : ℝ} (hj : 0 ≤ j) :
    (∀ t ∈ Icc (0 : ℝ) P.horizon,
      0 ≤ stateMultiplier P.horizon (statePenaltyDensity ω' G j γ) t) ∧
    AntitoneOn (stateMultiplier P.horizon (statePenaltyDensity ω' G j γ))
      (Icc (0 : ℝ) P.horizon) ∧
    stateMultiplier P.horizon (statePenaltyDensity ω' G j γ) P.horizon = 0 ∧
    ContinuousOn (stateMultiplier P.horizon (statePenaltyDensity ω' G j γ))
      (Icc (0 : ℝ) P.horizon) ∧
    ∀ α β : ℝ, α ∈ Icc (0 : ℝ) P.horizon → β ∈ Icc (0 : ℝ) P.horizon →
      (∀ r ∈ Icc α β, G r (γ.value r) ≤ 0) →
        ∀ t ∈ Icc α β, stateMultiplier P.horizon (statePenaltyDensity ω' G j γ) t
          = stateMultiplier P.horizon (statePenaltyDensity ω' G j γ) α := by
  have hT : 0 ≤ P.horizon := P.horizon_pos.le
  have hm := intervalIntegrable_statePenaltyDensity hω hG j γ
  have hm0 : ∀ r ∈ Icc (0 : ℝ) P.horizon, 0 ≤ statePenaltyDensity ω' G j γ r :=
    fun r _ => statePenaltyDensity_nonneg hω G hj γ r
  refine ⟨fun t ht => stateMultiplier_nonneg hm0 ht, stateMultiplier_antitoneOn hT hm hm0,
    stateMultiplier_horizon, stateMultiplier_continuousOn hT hm, ?_⟩
  intro α β hα hβ hslack
  exact stateMultiplier_eq_of_density_eq_zero hT hm hα hβ fun r hr =>
    statePenaltyDensity_eq_zero_of_nonpos hω G j γ (hslack r hr)

/-- **The costate equation (11.6.11) with initial condition (11.6.6) and terminal condition
(11.6.16), at level `j`, for an active state constraint.**  Let `γ` minimise the `ω`-penalised
functional `H^j` on a set `S` containing the scalar-profile perturbations of `γ`, with `G` and
`∇G = Gx` regular (`StateConstraintRegularity`, `StateGradientRegularity`) and `j ≥ 0`.  Then
with the nonincreasing multiplier `λ = ∫_t^T j ω'(G(r, γ r)) dr` there is a costate `Φ`
(`stateCostate`) such that

* the momentum covector is `∂ᵥL(t,γ,γ') = Φ(t) - λ(t) ∇G(t,γ(t))` a.e.;
* `Φ(t) = Φ(0) + ∫₀ᵗ (∂ₓL + λ d(∇G)/dt)` on `[0,T]`, i.e. `Φ' = ∂ₓL + λ d(∇G)/dt` a.e. with
  `d(∇G)/dt = ∇²G (1, γ')` — no measure appears;
* `Φ(0) = ∂Φ₀(γ 0) + ∂₁Φ₁(γ 0, γ T) + λ(0) ∇G(0, γ 0)`  — (11.6.6);
* `Φ(T) = -∂₂Φ₁(γ 0, γ T)`  — (11.6.16).

No slackness of the state constraint is assumed (this removes the gap `G2` of the earlier
endpoint theorems).  `Assumption 11.4.1` enters in the limit `j → ∞`
(`StateMultiplierLimit.lean`), where it forces `λ` to be constant near both endpoints.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.6.6), (11.6.11),
(11.6.15)-(11.6.16). -/
theorem VelocityTrajectory.statePenalised_costateEquation (γ : VelocityTrajectory P)
    (J : VelocityTrajectory P → ℝ) (S : Set (VelocityTrajectory P))
    {L : ℝ → E → E → ℝ} {Lx Lv : ℝ → E → E → E →L[ℝ] ℝ}
    (hD : IsCaratheodoryC1 P.horizon L Lx Lv) {ω ω' : ℝ → ℝ}
    (hω : StatePenaltyProfile ω ω') {G : ℝ → E → ℝ} {Gx : ℝ → E → E →L[ℝ] ℝ}
    (hG : StateConstraintRegularity G Gx)
    {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)} (hGx : StateGradientRegularity Gx Gxd)
    {j : ℝ} {Φ₀ : E → ℝ} {Φ₁ : E × E → ℝ}
    (hJ : ∀ γ' : VelocityTrajectory P,
      J γ' = actionFunctional (statePenalisedLagrangian L G ω j) Φ₀ Φ₁ P.horizon
        γ'.initial γ'.velocity)
    (hmin : IsMinOn J S γ)
    (hinterior : ∀ (e : E) (α : ℝ) (s : ℝ → ℝ) (hs : MemLp s 2 (timeMeasure P.horizon)),
      ∀ᶠ θ in 𝓝 (0 : ℝ), γ.perturbProfile e α s hs θ ∈ S)
    (hint : IntervalIntegrable
      (fun t => statePenalisedLagrangian L G ω j t (γ.value t) (γ.velocity t))
      volume 0 P.horizon)
    (hΦ₀ : DifferentiableAt ℝ Φ₀ (γ.value 0))
    (hΦ₁ : DifferentiableAt ℝ Φ₁ (γ.value 0, γ.value P.horizon)) :
    ∃ c : E →L[ℝ] ℝ,
      let Φ := stateCostate P.horizon (statePenaltyDensity ω' G j γ) c
        (fun r => Lx r (γ.value r) (γ.velocity r)) (fun r => Gx r (γ.value r))
      let lam := stateMultiplier P.horizon (statePenaltyDensity ω' G j γ)
      (∀ᵐ t ∂(timeMeasure P.horizon), Lv t (γ.value t) (γ.velocity t)
        = Φ t - lam t • Gx t (γ.value t)) ∧
      (∀ t ∈ Icc (0 : ℝ) P.horizon, Φ t = Φ 0 + ∫ r in (0 : ℝ)..t,
        (Lx r (γ.value r) (γ.velocity r)
          + lam r • Gxd r (γ.value r) (1, γ.velocity r))) ∧
      (∀ᵐ t ∂(timeMeasure P.horizon), HasDerivAt Φ
        (Lx t (γ.value t) (γ.velocity t) + lam t • Gxd t (γ.value t) (1, γ.velocity t)) t) ∧
      Φ 0 = fderiv ℝ Φ₀ (γ.value 0)
          + (fderiv ℝ Φ₁ (γ.value 0, γ.value P.horizon)).comp (ContinuousLinearMap.inl ℝ E E)
          + lam 0 • Gx 0 (γ.value 0) ∧
      Φ P.horizon
        = -((fderiv ℝ Φ₁ (γ.value 0, γ.value P.horizon)).comp (ContinuousLinearMap.inr ℝ E E)) := by
  have hT : 0 ≤ P.horizon := P.horizon_pos.le
  obtain ⟨c, hEL, h0, hTT⟩ := γ.statePenalised_weakEulerLagrange J S hD hω hG j hJ hmin hinterior
    hint hΦ₀ hΦ₁
  obtain ⟨hgint, hgprim⟩ := γ.gradientAlongPath_eq_primitive hGx
  have hm := intervalIntegrable_statePenaltyDensity hω hG j γ
  have ha : IntervalIntegrable (fun r => Lx r (γ.value r) (γ.velocity r)) volume 0 P.horizon :=
    intervalIntegrable_of_memLp hT
      (memLp_stateGradient hD hT γ.memLp_velocity γ.initial)
  have hlam := stateMultiplier_continuousOn hT hm
  have hlg' : IntervalIntegrable (fun r => stateMultiplier P.horizon
      (statePenaltyDensity ω' G j γ) r • Gxd r (γ.value r) (1, γ.velocity r)) volume
      0 P.horizon := hgint.continuousOn_smul (by rwa [uIcc_of_le hT])
  have hcost : ∀ t ∈ Icc (0 : ℝ) P.horizon,
      (c + ∫ r in (0 : ℝ)..t, (Lx r (γ.value r) (γ.velocity r)
        + statePenaltyDensity ω' G j γ r • Gx r (γ.value r)))
        + stateMultiplier P.horizon (statePenaltyDensity ω' G j γ) t • Gx t (γ.value t)
      = (c + stateMultiplier P.horizon (statePenaltyDensity ω' G j γ) 0 • Gx 0 (γ.value 0))
        + ∫ r in (0 : ℝ)..t, (Lx r (γ.value r) (γ.velocity r)
          + stateMultiplier P.horizon (statePenaltyDensity ω' G j γ) r
            • Gxd r (γ.value r) (1, γ.velocity r)) := fun t ht =>
    stateCostate_eq_primitive hT hm c ha hgint hgprim ht
  refine ⟨c, ?_⟩
  intro Φ lam
  have hΦ0 : Φ 0 = c + lam 0 • Gx 0 (γ.value 0) := by
    simp [Φ, lam, stateCostate]
  have hΦprim : ∀ t ∈ Icc (0 : ℝ) P.horizon, Φ t = Φ 0 + ∫ r in (0 : ℝ)..t,
      (Lx r (γ.value r) (γ.velocity r) + lam r • Gxd r (γ.value r) (1, γ.velocity r)) := by
    intro t ht
    rw [hΦ0]
    exact hcost t ht
  refine ⟨?_, hΦprim, ?_, ?_, ?_⟩
  · filter_upwards [hEL] with t ht
    rw [ht]
    simp [Φ, lam, stateCostate, statePenaltyDensity]
  · exact ae_hasDerivAt_of_eq_primitive hT (ha.add hlg') hΦprim
  · rw [hΦ0, h0]
  · have : Φ P.horizon = c + ∫ r in (0 : ℝ)..P.horizon,
        (Lx r (γ.value r) (γ.velocity r) + statePenaltyDensity ω' G j γ r • Gx r (γ.value r)) := by
      simp [Φ, stateCostate]
    rw [this]
    exact hTT

end Carrier

section PointwiseDefectCostate

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]
  {P : Problem E V W}

/-- **The costate equation (11.6.11) for the §11.6 pointwise-defect penalty with an active state
constraint.**  Let `γ` minimise
`∫₀ᵀ [c + ‖γ' - φ₀'‖² + K‖γ' - f‖² + j ω(G)] dt + ‖γ 0 - a‖² + κ‖γ 0 - b‖² + K‖T(γ 0, γ T)‖²`
(`H^j_K` of (11.3.8)) on a set containing its scalar-profile perturbations, with `j ≥ 0`.  With the
nonincreasing multiplier `λ = ∫_t^T j ω'(G(r, γ r)) dr` there is a costate `Φ`
(`stateCostate`, `Φ = ψ + λ ∇G` for the momentum `ψ = 2⟨γ' - φ₀', ·⟩ + 2K⟨γ' - f, ·⟩`) such that

* `Φ' = c_x - 2K⟨γ' - f, f_x ·⟩ + λ d(∇G)/dt` (integrated form), `d(∇G)/dt = ∇²G (1, γ')`;
* `Φ(0) = 2⟨γ 0 - a, ·⟩ + 2κ⟨γ 0 - b, ·⟩ + 2K⟨T(γ 0, γ T), ∂₁T ·⟩ + λ(0) ∇G(0, γ 0)`  — (11.6.6),
  (11.6.15);
* `Φ(T) = -2K⟨T(γ 0, γ T), ∂₂T ·⟩`  — (11.6.16);
* the momentum is `ψ = Φ - λ ∇G` a.e.

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.6), (11.3.8),
(11.6.6), (11.6.8)-(11.6.16). -/
theorem VelocityTrajectory.pointwiseDefect_statePenalised_costateEquation (γ : VelocityTrajectory P)
    (J : VelocityTrajectory P → ℝ) (S : Set (VelocityTrajectory P))
    {c : ℝ → E → ℝ} {cx : ℝ → E → E →L[ℝ] ℝ} {F : ℝ → E → E} {Fx : ℝ → E → E →L[ℝ] E}
    {r : ℝ → E} {K : ℝ} (hreg : PointwiseDefectRegularity P.horizon c cx F Fx r K)
    {ω ω' : ℝ → ℝ} (hω : StatePenaltyProfile ω ω') {G : ℝ → E → ℝ}
    {Gx : ℝ → E → E →L[ℝ] ℝ} (hG : StateConstraintRegularity G Gx)
    {Gxd : ℝ → E → (ℝ × E) →L[ℝ] (E →L[ℝ] ℝ)} (hGx : StateGradientRegularity Gx Gxd)
    {j : ℝ} (a b : E) (κ : ℝ) (Tend : E → E → W) (D₁ : E →L[ℝ] W) (D₂ : E →L[ℝ] W)
    (hT : HasFDerivAt (fun q : E × E => Tend q.1 q.2)
      (D₁.comp (ContinuousLinearMap.fst ℝ E E) + D₂.comp (ContinuousLinearMap.snd ℝ E E))
      (γ.value 0, γ.value P.horizon))
    (hJ : ∀ γ' : VelocityTrajectory P,
      J γ' = actionFunctional
        (statePenalisedLagrangian (pointwiseDefectLagrangian c F r K) G ω j)
        (fun y : E => ‖y - a‖ ^ 2 + κ * ‖y - b‖ ^ 2)
        (fun q : E × E => K * ‖Tend q.1 q.2‖ ^ 2) P.horizon γ'.initial γ'.velocity)
    (hmin : IsMinOn J S γ)
    (hinterior : ∀ (e : E) (α : ℝ) (s : ℝ → ℝ) (hs : MemLp s 2 (timeMeasure P.horizon)),
      ∀ᶠ θ in 𝓝 (0 : ℝ), γ.perturbProfile e α s hs θ ∈ S)
    (hint : IntervalIntegrable
      (fun t => statePenalisedLagrangian (pointwiseDefectLagrangian c F r K) G ω j t
        (γ.value t) (γ.velocity t)) volume 0 P.horizon) :
    ∃ c₀ : E →L[ℝ] ℝ,
      (∀ᵐ t ∂(timeMeasure P.horizon),
        pointwiseDefectVelocityCovector F r K t (γ.value t) (γ.velocity t)
          = stateCostate P.horizon (statePenaltyDensity ω' G j γ) c₀
              (fun s => pointwiseDefectStateCovector cx F Fx K s (γ.value s) (γ.velocity s))
              (fun s => Gx s (γ.value s)) t
            - stateMultiplier P.horizon (statePenaltyDensity ω' G j γ) t • Gx t (γ.value t)) ∧
      (∀ t ∈ Icc (0 : ℝ) P.horizon,
        stateCostate P.horizon (statePenaltyDensity ω' G j γ) c₀
          (fun s => pointwiseDefectStateCovector cx F Fx K s (γ.value s) (γ.velocity s))
          (fun s => Gx s (γ.value s)) t
        = stateCostate P.horizon (statePenaltyDensity ω' G j γ) c₀
            (fun s => pointwiseDefectStateCovector cx F Fx K s (γ.value s) (γ.velocity s))
            (fun s => Gx s (γ.value s)) 0
          + ∫ s in (0 : ℝ)..t,
            (pointwiseDefectStateCovector cx F Fx K s (γ.value s) (γ.velocity s)
              + stateMultiplier P.horizon (statePenaltyDensity ω' G j γ) s
                • Gxd s (γ.value s) (1, γ.velocity s))) ∧
      stateCostate P.horizon (statePenaltyDensity ω' G j γ) c₀
          (fun s => pointwiseDefectStateCovector cx F Fx K s (γ.value s) (γ.velocity s))
          (fun s => Gx s (γ.value s)) 0
        = (2 : ℝ) • innerSL ℝ (γ.value 0 - a) + (2 * κ) • innerSL ℝ (γ.value 0 - b)
          + (2 * K) • (innerSL ℝ (Tend (γ.value 0) (γ.value P.horizon))).comp D₁
          + stateMultiplier P.horizon (statePenaltyDensity ω' G j γ) 0 • Gx 0 (γ.value 0) ∧
      stateCostate P.horizon (statePenaltyDensity ω' G j γ) c₀
          (fun s => pointwiseDefectStateCovector cx F Fx K s (γ.value s) (γ.velocity s))
          (fun s => Gx s (γ.value s)) P.horizon
        = -((2 * K) • (innerSL ℝ (Tend (γ.value 0) (γ.value P.horizon))).comp D₂) := by
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
  obtain ⟨c₀, hmom, hprim, -, h0, hT'⟩ := γ.statePenalised_costateEquation J S hD hω hG hGx
    hJ hmin hinterior hint hΦ₀.differentiableAt hΦ₁.differentiableAt
  refine ⟨c₀, hmom, hprim, ?_, ?_⟩
  · rw [h0, hΦ₀.fderiv, hΦ₁.fderiv]
    ext z
    simp
  · rw [hT', hΦ₁.fderiv]
    ext z
    simp

end PointwiseDefectCostate

end OptimalControl.BoundedState
