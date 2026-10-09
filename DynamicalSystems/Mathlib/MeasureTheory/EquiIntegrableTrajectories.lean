/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.MeasureTheory.WeakL1Compactness
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Compactness of trajectories with uniformly integrable velocities

Equi-absolute continuity of derivative integrals gives equicontinuity of actual
integral trajectories. Compact ranges then give uniform subsequential convergence.
Weak L1 cluster points retain the integral law. These are the analytic trajectory
extraction steps in BM Theorem 5.4.4, Step 1, without an L2 velocity hypothesis.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal BoundedContinuousFunction

namespace DynamicalSystems.EquiIntegrableTrajectories

section Equicontinuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ}

omit [NormedSpace ℝ E] in
/-- Uniformly absolutely continuous L1 integrals on a compact real interval are
uniformly bounded in L1. A finite cover by short intervals constructs the bound;
no separate norm-bound certificate is supplied. This is BM equation (5.3.1). -/
theorem uniformIntegrable_of_unifIntegrable_on_interval
    (u : ℕ → Lp E 1 (volume.restrict (Icc a b)))
    (hUI : UnifIntegrable (fun n t ↦ u n t) 1 (volume.restrict (Icc a b))) :
    UniformIntegrable (fun n t ↦ u n t) 1 (volume.restrict (Icc a b)) := by
  classical
  obtain ⟨δ, hδ, hsmall⟩ := unifIntegrable_iff.mp hUI 1 zero_lt_one
  obtain ⟨d, hd, hdδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hδ
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  let U (t : ℝ) := Ioo (t - d / 4) (t + d / 4)
  have hcover : Icc a b ⊆ ⋃ t, U t := fun t _ ↦
    mem_iUnion.mpr ⟨t, by dsimp [U]; constructor <;> linarith⟩
  obtain ⟨s, hs⟩ := isCompact_Icc.elim_finite_subcover U (fun _ ↦ isOpen_Ioo) hcover
  have hmeasure : ∀ t, (volume.restrict (Icc a b)) (U t) ≤ δ := by
    intro t
    refine (Measure.restrict_le_self _).trans ?_
    rw [Real.volume_Ioo, show (t + d / 4) - (t - d / 4) = d / 2 by ring]
    exact (ENNReal.ofReal_le_ofReal (show (d : ℝ) / 2 ≤ d by linarith)).trans
      (by simpa using hdδ.le)
  refine ⟨hUI, (s.card : ℝ≥0), fun n ↦ ?_⟩
  have hrestrict : (volume.restrict (Icc a b)).restrict (⋃ t : s, U t) =
      volume.restrict (Icc a b) := by
    apply Measure.restrict_eq_self_of_ae_mem
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [iUnion_subtype, Finset.mem_coe] using hs ht
  calc
    eLpNorm (fun t ↦ u n t) 1 (volume.restrict (Icc a b)) =
        ∫⁻ t, ‖u n t‖ₑ ∂volume.restrict (Icc a b) :=
      eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable (u n))
    _ = ∫⁻ t in ⋃ j : s, U j, ‖u n t‖ₑ ∂volume.restrict (Icc a b) := by rw [hrestrict]
    _ ≤ ∑' j : s, ∫⁻ t in U j, ‖u n t‖ₑ ∂volume.restrict (Icc a b) :=
      lintegral_iUnion_le _ _
    _ ≤ ∑' _j : s, (1 : ℝ≥0∞) := ENNReal.tsum_le_tsum fun j ↦ by
      rw [← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable (u n)).restrict]
      exact hsmall n _ (hmeasure j)
    _ = (s.card : ℝ≥0) := by simp

/-- Uniformly absolutely continuous velocity integrals give equicontinuity of
trajectories satisfying the actual integral difference law. -/
theorem equicontinuous_of_unifIntegrable_integral_law
    (x : ℕ → Icc a b → E) (u : ℕ → Lp E 1 (volume.restrict (Icc a b)))
    (hUI : UnifIntegrable (fun n t ↦ u n t) 1 (volume.restrict (Icc a b)))
    (hlaw : ∀ n (s t : Icc a b), x n t - x n s =
      ∫ r in (s : ℝ)..(t : ℝ), u n r ∂volume.restrict (Icc a b)) :
    Equicontinuous x := by
  intro t
  apply Metric.equicontinuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := unifIntegrable_iff.mp hUI
    (ENNReal.ofReal (ε / 2)) (ENNReal.ofReal_pos.mpr (half_pos hε))
  obtain ⟨d, hd, hdδ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hδ
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast hd
  refine ⟨d, hdpos, fun s hs n ↦ ?_⟩
  have hmeasure : (volume.restrict (Icc a b)) (uIoc (t : ℝ) (s : ℝ)) ≤ δ := by
    refine (Measure.restrict_le_self _).trans ?_
    rw [Real.volume_uIoc]
    exact (ENNReal.ofReal_le_ofReal
      (by simpa [Subtype.dist_eq, Real.dist_eq] using hs.le)).trans (by simpa using hdδ.le)
  have hbound := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hsmall n _ hmeasure)
  rw [ENNReal.toReal_ofReal (half_pos hε).le] at hbound
  have hnorm : (∫ r in uIoc (t : ℝ) (s : ℝ), ‖u n r‖
      ∂volume.restrict (Icc a b)) ≤ ε / 2 := by
    rwa [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable (u n)).restrict,
      ← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable (u n)).restrict]
  rw [dist_comm, dist_eq_norm, hlaw]
  calc
    ‖∫ r in (t : ℝ)..(s : ℝ), u n r ∂volume.restrict (Icc a b)‖ ≤
        ∫ r in uIoc (t : ℝ) (s : ℝ), ‖u n r‖ ∂volume.restrict (Icc a b) :=
      intervalIntegral.norm_integral_le_integral_norm_uIoc
    _ < ε := hnorm.trans_lt (half_lt_self hε)

/-- Compact range and equi-integrable velocities yield a uniformly convergent
subsequence of actual integral trajectories, by Arzelà–Ascoli. -/
theorem exists_uniform_tendsto_subseq_of_unifIntegrable_integral_law
    (x : ℕ → Icc a b →ᵇ E) (u : ℕ → Lp E 1 (volume.restrict (Icc a b)))
    (K : Set E) (hK : IsCompact K) (hvalues : ∀ n t, x n t ∈ K)
    (hUI : UnifIntegrable (fun n t ↦ u n t) 1 (volume.restrict (Icc a b)))
    (hlaw : ∀ n (s t : Icc a b), x n t - x n s =
      ∫ r in (s : ℝ)..(t : ℝ), u n r ∂volume.restrict (Icc a b)) :
    ∃ (xlim : Icc a b →ᵇ E) (k : ℕ → ℕ), StrictMono k ∧
      Tendsto (x ∘ k) atTop (𝓝 xlim) ∧ ∀ t, xlim t ∈ K := by
  have heq := equicontinuous_of_unifIntegrable_integral_law (fun n t ↦ x n t) u hUI hlaw
  have hRange : Equicontinuous (fun f : range x ↦ (f.val : Icc a b → E)) := by
    have h := heq.comp fun f : range x ↦ Classical.choose f.property
    convert h using 1
    funext f t
    exact (congrArg (fun p : Icc a b →ᵇ E ↦ p t) (Classical.choose_spec f.property)).symm
  have hcompact : IsCompact (closure (range x)) :=
    BoundedContinuousFunction.arzela_ascoli K hK (range x)
      (fun f t hf ↦ by obtain ⟨n, rfl⟩ := hf; exact hvalues n t)
      hRange
  obtain ⟨xlim, hxlim, k, hk, hlim⟩ := hcompact.tendsto_subseq
    (fun n ↦ subset_closure (mem_range_self n))
  refine ⟨xlim, k, hk, hlim, fun t ↦ ?_⟩
  exact hK.isClosed.mem_of_tendsto (hlim.eval_const t)
    (.of_forall fun n ↦ hvalues (k n) t)

end Equicontinuity

section IntegralLaw

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Set integration is a continuous linear operation on L1. -/
noncomputable def setIntegralCLM (s : Set α) : Lp E 1 μ →L[ℝ] E :=
  L1.integralCLM.comp (LpToLpRestrictCLM α E ℝ μ 1 s)

/-- The bundled L1 set integral agrees with the Bochner set integral. -/
theorem setIntegralCLM_apply (s : Set α) (u : Lp E 1 μ) :
    setIntegralCLM s u = ∫ t in s, u t ∂μ := by
  rw [setIntegralCLM, ContinuousLinearMap.comp_apply, ← L1.integral_eq,
    L1.integral_eq_integral]
  exact integral_congr_ae (LpToLpRestrictCLM_coeFn ℝ s u)

/-- A weak L1 cluster point retains an integral law whose trajectory values
converge pointwise. The law is proved, not assumed for the limiting velocity. -/
theorem setIntegral_eq_of_weak_clusterPoint_of_tendsto
    (u : ℕ → Lp E 1 μ) (v : Lp E 1 μ)
    (hv : ClusterPt (toWeakSpace ℝ (Lp E 1 μ) v)
      (map (fun n ↦ toWeakSpace ℝ (Lp E 1 μ) (u n)) atTop))
    (s : Set α) (y : ℕ → E) (ylim : E)
    (hlaw : ∀ n, ∫ t in s, u n t ∂μ = y n)
    (hy : Tendsto y atTop (𝓝 ylim)) : ∫ t in s, v t ∂μ = ylim := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro φ
  have hobs : Tendsto (fun n ↦ (φ.comp (setIntegralCLM s)) (u n)) atTop (𝓝 (φ ylim)) := by
    simpa only [ContinuousLinearMap.comp_apply, setIntegralCLM_apply, hlaw,
      Function.comp_def] using
      (φ.continuous.tendsto ylim).comp hy
  simpa only [ContinuousLinearMap.comp_apply, setIntegralCLM_apply] using
    WeakL1.dual_apply_eq_of_weak_clusterPoint_of_tendsto u v hv
      (φ.comp (setIntegralCLM s)) (φ ylim) hobs

end IntegralLaw

section IntervalUniqueness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b : ℝ}

/-- An L1 velocity on a real interval is determined by all its indefinite
integrals. Lebesgue differentiation proves equality of the actual L1 elements. -/
theorem eq_of_setIntegral_Ioc_eq (hab : a ≤ b)
    (u v : Lp E 1 (volume.restrict (Icc a b)))
    (heq : ∀ t ∈ Icc a b, (∫ r in Ioc a t, u r ∂volume.restrict (Icc a b)) =
      ∫ r in Ioc a t, v r ∂volume.restrict (Icc a b)) : u = v := by
  let f := (Icc a b).indicator u
  let g := (Icc a b).indicator v
  have hf : Integrable f volume := (integrable_indicator_iff measurableSet_Icc).mpr
    (memLp_one_iff_integrable.mp (Lp.memLp u))
  have hg : Integrable g volume := (integrable_indicator_iff measurableSet_Icc).mpr
    (memLp_one_iff_integrable.mp (Lp.memLp v))
  have hprimitive : ∀ t ∈ Icc a b, (∫ r in a..t, f r) = ∫ r in a..t, g r := by
    intro t ht
    have hident : ∀ w : Lp E 1 (volume.restrict (Icc a b)),
        (∫ r in a..t, (Icc a b).indicator w r) =
          ∫ r in Ioc a t, w r ∂volume.restrict (Icc a b) := by
      intro w
      rw [intervalIntegral.integral_of_le ht.1, setIntegral_indicator measurableSet_Icc,
        Measure.restrict_restrict measurableSet_Ioc]
    exact (hident u).trans ((heq t ht).trans (hident v).symm)
  apply Lp.ext
  let ufun : ℝ → E := u
  let vfun : ℝ → E := v
  change ufun =ᵐ[volume.restrict (Icc a b)] vfun
  rw [← restrict_Ioo_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo,
    (hf.intervalIntegrable.ae_hasDerivAt_integral (a := a) (b := b)).filter_mono ae_restrict_le,
    (hg.intervalIntegrable.ae_hasDerivAt_integral (a := a) (b := b)).filter_mono ae_restrict_le]
    with t ht hft hgt
  have htcc : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
  have htI : t ∈ uIcc a b := by simpa [uIcc_of_le hab] using htcc
  have haI : a ∈ uIcc a b := by simp [hab]
  have hneigh : ∀ᶠ s in 𝓝 t, s ∈ Ioo a b := Ioo_mem_nhds ht.1 ht.2
  have hev : (fun t ↦ ∫ r in a..t, g r) =ᶠ[𝓝 t] fun t ↦ ∫ r in a..t, f r :=
    hneigh.mono fun s hs ↦ (hprimitive s ⟨hs.1.le, hs.2.le⟩).symm
  have h := ((hft htI a haI).congr_of_eventuallyEq hev).unique (hgt htI a haI)
  simpa only [f, g, indicator_of_mem htcc] using h

end IntervalUniqueness

section WeakConvergence

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {a b : ℝ}

/-- Equi-integrable velocities converge weakly in L1 when their actual
indefinite integral trajectories converge pointwise to the primitive of an L1
velocity. Weak cluster compactness and uniqueness of primitives prove convergence
against every continuous linear functional, the sufficiency direction of BM 5.3.5. -/
theorem weak_L1_tendsto_of_unifIntegrable_of_integral_law_limit
    (hab : a ≤ b) (u : ℕ → Lp E 1 (volume.restrict (Icc a b)))
    (v : Lp E 1 (volume.restrict (Icc a b)))
    (x : ℕ → Icc a b → E) (xlim : Icc a b → E)
    (hUI : UnifIntegrable (fun n t ↦ u n t) 1 (volume.restrict (Icc a b)))
    (hx : ∀ t, Tendsto (fun n ↦ x n t) atTop (𝓝 (xlim t)))
    (hlaw : ∀ n (t : Icc a b), x n t - x n ⟨a, le_rfl, hab⟩ =
      ∫ r in Ioc a (t : ℝ), u n r ∂volume.restrict (Icc a b))
    (hv : ∀ t : Icc a b, xlim t - xlim ⟨a, le_rfl, hab⟩ =
      ∫ r in Ioc a (t : ℝ), v r ∂volume.restrict (Icc a b)) :
    Tendsto (fun n ↦ toWeakSpace ℝ (Lp E 1 (volume.restrict (Icc a b))) (u n))
      atTop (𝓝 (toWeakSpace ℝ (Lp E 1 (volume.restrict (Icc a b))) v)) := by
  have hfull := uniformIntegrable_of_unifIntegrable_on_interval u hUI
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto
    (topDualPairing ℝ (Lp E 1 (volume.restrict (Icc a b)))).flip
    (separatingDual_iff_injective.mp inferInstance)).mpr
  intro φ
  change Tendsto (fun n ↦ φ (u n)) atTop (𝓝 (φ v))
  apply tendsto_of_subseq_tendsto
  intro ns hns
  have hUIns : UniformIntegrable (fun n t ↦ u (ns n) t) 1
      (volume.restrict (Icc a b)) := by
    obtain ⟨C, hC⟩ := hfull.2
    exact ⟨hUI.comp ns, C, fun n ↦ hC (ns n)⟩
  obtain ⟨v', hcluster⟩ := WeakL1.exists_weak_L1_clusterPoint_of_uniformIntegrable
    (fun n ↦ u (ns n)) hUIns
  have heq : v' = v := by
    apply eq_of_setIntegral_Ioc_eq hab
    intro t ht
    have hlimlaw := setIntegral_eq_of_weak_clusterPoint_of_tendsto
      (fun n ↦ u (ns n)) v' hcluster (Ioc a t)
      (fun n ↦ x (ns n) ⟨t, ht⟩ - x (ns n) ⟨a, le_rfl, hab⟩)
      (xlim ⟨t, ht⟩ - xlim ⟨a, le_rfl, hab⟩)
      (fun n ↦ (hlaw (ns n) ⟨t, ht⟩).symm)
      (((hx ⟨t, ht⟩).comp hns).sub ((hx ⟨a, le_rfl, hab⟩).comp hns))
    exact hlimlaw.trans (hv ⟨t, ht⟩)
  have hscalar : MapClusterPt (φ v) atTop (fun n ↦ φ (u (ns n))) := by
    rw [heq] at hcluster
    exact MapClusterPt.continuousAt_comp
      (X := WeakSpace ℝ (Lp E 1 (volume.restrict (Icc a b))))
      (WeakBilin.eval_continuous
        (topDualPairing ℝ (Lp E 1 (volume.restrict (Icc a b)))).flip φ).continuousAt hcluster
  obtain ⟨k, _, hlim⟩ := hscalar.tendsto_subseq
  exact ⟨k, hlim⟩

end WeakConvergence

section CompactIntegralLaw

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {a b : ℝ}

/-- Joint trajectory extraction and weak L1 limiting dynamics from compact range
and uniformly integrable velocities. Uniform convergence and the limiting
integral law are conclusions; the original sequence need not be bounded in L2.
This proves the cluster-point form of BM Theorem 5.4.4, Step 1. -/
theorem exists_uniform_limit_weak_L1_clusterPoint_integral_law
    (hab : a ≤ b) (x : ℕ → Icc a b →ᵇ E)
    (u : ℕ → Lp E 1 (volume.restrict (Icc a b)))
    (K : Set E) (hK : IsCompact K) (hvalues : ∀ n t, x n t ∈ K)
    (hUI : UnifIntegrable (fun n t ↦ u n t) 1 (volume.restrict (Icc a b)))
    (hlaw : ∀ n (s t : Icc a b), x n t - x n s =
      ∫ r in (s : ℝ)..(t : ℝ), u n r ∂volume.restrict (Icc a b)) :
    ∃ (xlim : Icc a b →ᵇ E) (v : Lp E 1 (volume.restrict (Icc a b))) (k : ℕ → ℕ),
      StrictMono k ∧ Tendsto (x ∘ k) atTop (𝓝 xlim) ∧ (∀ t, xlim t ∈ K) ∧
      ClusterPt (toWeakSpace ℝ (Lp E 1 (volume.restrict (Icc a b))) v)
        (map (fun n ↦ toWeakSpace ℝ (Lp E 1 (volume.restrict (Icc a b))) (u (k n))) atTop) ∧
      ∀ t : Icc a b, xlim t - xlim ⟨a, le_rfl, hab⟩ =
        ∫ r in Ioc a (t : ℝ), v r ∂volume.restrict (Icc a b) := by
  obtain ⟨xlim, k, hk, hlim, hvalueslim⟩ :=
    exists_uniform_tendsto_subseq_of_unifIntegrable_integral_law x u K hK hvalues hUI hlaw
  have hfull := uniformIntegrable_of_unifIntegrable_on_interval u hUI
  have hUIk : UniformIntegrable (fun n t ↦ u (k n) t) 1
      (volume.restrict (Icc a b)) := by
    obtain ⟨C, hC⟩ := hfull.2
    exact ⟨hUI.comp k, C, fun n ↦ hC (k n)⟩
  obtain ⟨v, hv⟩ := WeakL1.exists_weak_L1_clusterPoint_of_uniformIntegrable
    (fun n ↦ u (k n)) hUIk
  refine ⟨xlim, v, k, hk, hlim, hvalueslim, hv, fun t ↦ ?_⟩
  apply Eq.symm
  apply setIntegral_eq_of_weak_clusterPoint_of_tendsto (fun n ↦ u (k n)) v hv
    (Ioc a (t : ℝ)) (fun n ↦ x (k n) t - x (k n) ⟨a, le_rfl, hab⟩)
  · intro n
    have h := hlaw (k n) ⟨a, le_rfl, hab⟩ t
    rw [intervalIntegral.integral_of_le t.property.1] at h
    exact h.symm
  · exact (hlim.eval_const t).sub (hlim.eval_const ⟨a, le_rfl, hab⟩)

/-- Uniform trajectory convergence and weak L1 velocity convergence are extracted
jointly from compact range and uniformly absolutely continuous velocity integrals.
The limiting integral law is also derived. This is the fixed-interval compactness
crux of BM Theorem 5.4.4, Step 1, without any L2 or weak-limit certificate. -/
theorem exists_uniform_limit_weak_L1_tendsto_integral_law
    (hab : a ≤ b) (x : ℕ → Icc a b →ᵇ E)
    (u : ℕ → Lp E 1 (volume.restrict (Icc a b)))
    (K : Set E) (hK : IsCompact K) (hvalues : ∀ n t, x n t ∈ K)
    (hUI : UnifIntegrable (fun n t ↦ u n t) 1 (volume.restrict (Icc a b)))
    (hlaw : ∀ n (s t : Icc a b), x n t - x n s =
      ∫ r in (s : ℝ)..(t : ℝ), u n r ∂volume.restrict (Icc a b)) :
    ∃ (xlim : Icc a b →ᵇ E) (v : Lp E 1 (volume.restrict (Icc a b))) (k : ℕ → ℕ),
      StrictMono k ∧ Tendsto (x ∘ k) atTop (𝓝 xlim) ∧ (∀ t, xlim t ∈ K) ∧
      Tendsto (fun n ↦ toWeakSpace ℝ (Lp E 1 (volume.restrict (Icc a b))) (u (k n)))
        atTop (𝓝 (toWeakSpace ℝ (Lp E 1 (volume.restrict (Icc a b))) v)) ∧
      ∀ t : Icc a b, xlim t - xlim ⟨a, le_rfl, hab⟩ =
        ∫ r in Ioc a (t : ℝ), v r ∂volume.restrict (Icc a b) := by
  obtain ⟨xlim, v, k, hk, hlim, hvalueslim, _, hlawlim⟩ :=
    exists_uniform_limit_weak_L1_clusterPoint_integral_law hab x u K hK hvalues hUI hlaw
  have hweak := weak_L1_tendsto_of_unifIntegrable_of_integral_law_limit hab
    (fun n ↦ u (k n)) v (fun n t ↦ x (k n) t) xlim (hUI.comp k)
    (fun t ↦ hlim.eval_const t) (fun n t ↦ ?_) hlawlim
  · exact ⟨xlim, v, k, hk, hlim, hvalueslim, hweak, hlawlim⟩
  · have h := hlaw (k n) ⟨a, le_rfl, hab⟩ t
    rwa [intervalIntegral.integral_of_le t.property.1] at h

end CompactIntegralLaw

end DynamicalSystems.EquiIntegrableTrajectories
