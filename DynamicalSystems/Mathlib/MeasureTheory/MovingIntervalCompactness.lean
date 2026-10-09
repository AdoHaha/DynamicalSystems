/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.MeasureTheory.EquiIntegrableTrajectories

/-!
# Compactness with moving trajectory endpoints

The fixed-interval weak L1 extraction is combined with compact extraction of
endpoint times. Joint continuity of evaluation preserves the closed boundary
condition. Constant extensions stay constant outside the limiting interval.
These are the moving-endpoint conclusions in BM Theorem 5.4.4, Step 1.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ENNReal BoundedContinuousFunction

namespace DynamicalSystems.EquiIntegrableTrajectories

/-- An interior time of the limiting interval eventually lies in every moving
interval. This supplies eventual epigraph feasibility in BM Theorem 5.4.4, Step 3. -/
theorem eventually_mem_Ioo_of_endpoint_tendsto
    {l r : ℕ → ℝ} {a b t : ℝ}
    (hl : Tendsto l atTop (𝓝 a)) (hr : Tendsto r atTop (𝓝 b)) (ht : t ∈ Ioo a b) :
    ∀ᶠ n in atTop, t ∈ Ioo (l n) (r n) :=
  (hl.eventually (gt_mem_nhds ht.1)).and (hr.eventually (lt_mem_nhds ht.2))

section OuterConstancy

variable {E : Type*} [MetricSpace E] {a b : ℝ}

/-- Uniform path convergence and convergent moving endpoints preserve constancy
of the extensions outside the limiting interval. -/
theorem const_on_outer_intervals_of_uniform_tendsto_endpoints
    (x : ℕ → Icc a b →ᵇ E) (xlim : Icc a b →ᵇ E)
    (l r : ℕ → Icc a b) (l₀ r₀ : Icc a b)
    (hx : Tendsto x atTop (𝓝 xlim))
    (hl : Tendsto l atTop (𝓝 l₀)) (hr : Tendsto r atTop (𝓝 r₀))
    (hleft : ∀ n (t : Icc a b), (t : ℝ) ≤ l n → x n t = x n (l n))
    (hright : ∀ n (t : Icc a b), (r n : ℝ) ≤ t → x n t = x n (r n)) :
    (∀ t : Icc a b, (t : ℝ) ≤ l₀ → xlim t = xlim l₀) ∧
      ∀ t : Icc a b, (r₀ : ℝ) ≤ t → xlim t = xlim r₀ := by
  have hlreal := continuous_subtype_val.tendsto l₀ |>.comp hl
  have hrreal := continuous_subtype_val.tendsto r₀ |>.comp hr
  constructor
  · intro t ht
    rcases ht.lt_or_eq with ht | ht
    · have heq : (fun n ↦ x n t) =ᶠ[atTop] fun n ↦ x n (l n) := by
        filter_upwards [hlreal.eventually (lt_mem_nhds ht)] with n hn
        exact hleft n t hn.le
      exact tendsto_nhds_unique (hx.eval_const t) ((hx.eval hl).congr' heq.symm)
    · have hteq : t = l₀ := Subtype.ext ht
      rw [hteq]
  · intro t ht
    rcases ht.lt_or_eq with ht | ht
    · have heq : (fun n ↦ x n t) =ᶠ[atTop] fun n ↦ x n (r n) := by
        filter_upwards [hrreal.eventually (gt_mem_nhds ht)] with n hn
        exact hright n t hn.le
      exact tendsto_nhds_unique (hx.eval_const t) ((hx.eval hr).congr' heq.symm)
    · have hteq : r₀ = t := Subtype.ext ht
      rw [hteq]

end OuterConstancy

section Extraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {a b : ℝ}

omit [CompleteSpace E] in
/-- The primitive law on the ambient interval restricts to actual integral
dynamics on a limiting subinterval. No new derivative or trajectory is supplied. -/
theorem integral_difference_law_on_subinterval
    (hab : a ≤ b) (x : Icc a b → E) (v : Lp E 1 (volume.restrict (Icc a b)))
    (hlaw : ∀ t : Icc a b, x t - x ⟨a, le_rfl, hab⟩ =
      ∫ z in Ioc a (t : ℝ), v z ∂volume.restrict (Icc a b))
    (l r : Icc a b) (t : Icc (l : ℝ) (r : ℝ)) :
    x ⟨t, l.property.1.trans t.property.1, t.property.2.trans r.property.2⟩ - x l =
      ∫ z in Ioc (l : ℝ) (t : ℝ), v z ∂volume.restrict (Icc (l : ℝ) (r : ℝ)) := by
  let ts : Icc a b := ⟨t, l.property.1.trans t.property.1,
    t.property.2.trans r.property.2⟩
  have ht := hlaw ts
  have hl := hlaw l
  rw [← intervalIntegral.integral_of_le ts.property.1] at ht
  rw [← intervalIntegral.integral_of_le l.property.1] at hl
  have hi : ∀ c d : ℝ, IntervalIntegrable v (volume.restrict (Icc a b)) c d :=
    fun c d ↦ (memLp_one_iff_integrable.mp (Lp.memLp v)).intervalIntegrable
  have hdiff : x ts - x l = ∫ z in (l : ℝ)..(t : ℝ), v z
      ∂volume.restrict (Icc a b) := by
    rw [← intervalIntegral.integral_interval_sub_left (hi a t) (hi a l), ← ht, ← hl]
    abel
  rw [hdiff, intervalIntegral.integral_of_le t.property.1]
  have hsambient : Ioc (l : ℝ) (t : ℝ) ⊆ Icc a b := fun z hz ↦
    ⟨l.property.1.trans hz.1.le, hz.2.trans (t.property.2.trans r.property.2)⟩
  have hslimit : Ioc (l : ℝ) (t : ℝ) ⊆ Icc (l : ℝ) (r : ℝ) := fun z hz ↦
    ⟨hz.1.le, hz.2.trans t.property.2⟩
  rw [Measure.restrict_restrict measurableSet_Ioc,
    Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr hsambient, inter_eq_left.mpr hslimit]

/-- Joint extraction of uniform trajectories, weak L1 velocities, and endpoint
times from actual integral trajectories with constant extensions. The limiting
law and closed boundary condition are derived. Strict endpoint separation comes
from the primitive boundary set, not a supplied positive limiting duration.
This is the extended-trajectory form of BM Theorem 5.4.4, Step 1. -/
theorem exists_uniform_limit_endpoints_weak_L1_integral_law
    (hab : a ≤ b) (x : ℕ → Icc a b →ᵇ E)
    (u : ℕ → Lp E 1 (volume.restrict (Icc a b))) (l r : ℕ → Icc a b)
    (K : Set E) (hK : IsCompact K) (hvalues : ∀ n t, x n t ∈ K)
    (hUI : UnifIntegrable (fun n t ↦ u n t) 1 (volume.restrict (Icc a b)))
    (hlaw : ∀ n (s t : Icc a b), x n t - x n s =
      ∫ z in (s : ℝ)..(t : ℝ), u n z ∂volume.restrict (Icc a b))
    (hleft : ∀ n (t : Icc a b), (t : ℝ) ≤ l n → x n t = x n (l n))
    (hright : ∀ n (t : Icc a b), (r n : ℝ) ≤ t → x n t = x n (r n))
    (B : Set (ℝ × E × ℝ × E)) (hB : IsClosed B)
    (hBtime : ∀ p ∈ B, p.1 < p.2.2.1)
    (hboundary : ∀ n, ((l n : ℝ), x n (l n), (r n : ℝ), x n (r n)) ∈ B) :
    ∃ (xlim : Icc a b →ᵇ E) (v : Lp E 1 (volume.restrict (Icc a b)))
      (l₀ r₀ : Icc a b) (k : ℕ → ℕ), StrictMono k ∧
      Tendsto (x ∘ k) atTop (𝓝 xlim) ∧ (∀ t, xlim t ∈ K) ∧
      Tendsto (l ∘ k) atTop (𝓝 l₀) ∧ Tendsto (r ∘ k) atTop (𝓝 r₀) ∧
      (l₀ : ℝ) < r₀ ∧ ((l₀ : ℝ), xlim l₀, (r₀ : ℝ), xlim r₀) ∈ B ∧
      Tendsto (fun n ↦ toWeakSpace ℝ (Lp E 1 (volume.restrict (Icc a b))) (u (k n)))
        atTop (𝓝 (toWeakSpace ℝ (Lp E 1 (volume.restrict (Icc a b))) v)) ∧
      (∀ t : Icc a b, xlim t - xlim ⟨a, le_rfl, hab⟩ =
        ∫ z in Ioc a (t : ℝ), v z ∂volume.restrict (Icc a b)) ∧
      (∀ t : Icc a b, (t : ℝ) ≤ l₀ → xlim t = xlim l₀) ∧
      ∀ t : Icc a b, (r₀ : ℝ) ≤ t → xlim t = xlim r₀ := by
  obtain ⟨xlim, v, k, hk, hx, hvalueslim, hu, hlawlim⟩ :=
    exists_uniform_limit_weak_L1_tendsto_integral_law hab x u K hK hvalues hUI hlaw
  have hcompact : IsCompact (univ : Set (Icc a b × Icc a b)) := isCompact_univ
  obtain ⟨p, _, j, hj, hp⟩ := hcompact.tendsto_subseq
    (fun n ↦ mem_univ (l (k n), r (k n)))
  have hx' := hx.comp hj.tendsto_atTop
  have hl := (continuous_fst.tendsto p).comp hp
  have hr := (continuous_snd.tendsto p).comp hp
  have hboundlim : ((p.1 : ℝ), xlim p.1, (p.2 : ℝ), xlim p.2) ∈ B := by
    apply hB.mem_of_tendsto
      (((continuous_subtype_val.tendsto p.1).comp hl).prodMk_nhds
        ((hx'.eval hl).prodMk_nhds
          (((continuous_subtype_val.tendsto p.2).comp hr).prodMk_nhds (hx'.eval hr))))
    exact Eventually.of_forall fun n ↦ hboundary (k (j n))
  have hconst := const_on_outer_intervals_of_uniform_tendsto_endpoints
    (fun n ↦ x (k (j n))) xlim (fun n ↦ l (k (j n))) (fun n ↦ r (k (j n)))
    p.1 p.2 hx' hl hr (fun n ↦ hleft (k (j n))) (fun n ↦ hright (k (j n)))
  exact ⟨xlim, v, p.1, p.2, k ∘ j, hk.comp hj, hx', hvalueslim, hl, hr,
    hBtime _ hboundlim, hboundlim, hu.comp hj.tendsto_atTop, hlawlim, hconst⟩

end Extraction

end DynamicalSystems.EquiIntegrableTrajectories
