/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistenceLinear
public import DynamicalSystems.Mathlib.Analysis.ODE.UniformlyLocallyLipschitzUniqueness
public import Mathlib.Analysis.Calculus.FDeriv.Extend
public import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Global existence from local Lipschitz continuity and linear growth

The growth hypotheses in this module use constants uniform on each compact time
interval. A separate bound for each time is insufficient, even for a smooth
scalar vector field.

The continuation argument uses completeness of the state space and a bound on the
speed of a solution. It does not require closed balls in the state space to be compact.
-/

@[expose] public noncomputable section

open Set Filter Topology Metric
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E → E}

/-- Linear growth on each compact time interval, with constants allowed to depend on
the interval but not on the state or on the time inside that interval. -/
def LocallyUniformLinearGrowth (f : ℝ → E → E) : Prop :=
  ∀ a b : ℝ, ∃ C C' : ℝ≥0, ∀ t ∈ Icc a b, ∀ x : E,
    ‖f t x‖ ≤ (C : ℝ) * ‖x‖ + C'

omit [NormedSpace ℝ E] in
/-- A uniform linear-growth estimate in particular provides locally uniform linear growth. -/
theorem locallyUniformLinearGrowth_of_bound {C C' : ℝ≥0}
    (h : ∀ t x, ‖f t x‖ ≤ (C : ℝ) * ‖x‖ + C') :
    LocallyUniformLinearGrowth f :=
  fun _ _ => ⟨C, C', fun t _ x => h t x⟩

omit [NormedSpace ℝ E] in
/-- Continuous time-dependent growth coefficients provide the compact-time
bounds required for global existence. They need not be bounded on all of `ℝ`. -/
theorem locallyUniformLinearGrowth_of_continuous_bound {c c' : ℝ → ℝ}
    (hc : Continuous c) (hc' : Continuous c')
    (hbound : ∀ t x, ‖f t x‖ ≤ c t * ‖x‖ + c' t) :
    LocallyUniformLinearGrowth f := by
  intro a b
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨C', hC'⟩ := isCompact_Icc.exists_bound_of_continuousOn hc'.continuousOn
  refine ⟨Real.toNNReal C, Real.toNNReal C', fun t ht x => ?_⟩
  have hct : c t ≤ (Real.toNNReal C : ℝ) :=
    (Real.le_norm_self _).trans ((hC t ht).trans (Real.le_coe_toNNReal _))
  have hct' : c' t ≤ (Real.toNNReal C' : ℝ) :=
    (Real.le_norm_self _).trans ((hC' t ht).trans (Real.le_coe_toNNReal _))
  exact (hbound t x).trans (add_le_add (mul_le_mul_of_nonneg_right hct (norm_nonneg _)) hct')

namespace ODE

/-- Grönwall bounds a solution throughout a bounded open interval, using growth
constants valid on the corresponding closed time interval. -/
theorem norm_le_gronwallBound_of_linear_growth_Ioo
    {α : ℝ → E} {t₀ R : ℝ} {C C' : ℝ≥0}
    (hα : ∀ t ∈ Ioo (t₀ - R) (t₀ + R), HasDerivAt α (f t (α t)) t)
    (hbound : ∀ t ∈ Icc (t₀ - R) (t₀ + R), ∀ x,
      ‖f t x‖ ≤ (C : ℝ) * ‖x‖ + C') :
    ∀ t ∈ Ioo (t₀ - R) (t₀ + R),
      ‖α t‖ ≤ gronwallBound ‖α t₀‖ C C' R := by
  classical
  let g : ℝ → E → E := fun t x => if t ∈ Icc (t₀ - R) (t₀ + R) then f t x else 0
  have hg : ∀ t x, ‖g t x‖ ≤ (C : ℝ) * ‖x‖ + C' := by
    intro t x
    dsimp [g]
    split_ifs with ht
    · exact hbound t ht x
    · simp only [norm_zero]
      positivity
  intro t ht
  let T : ℝ := |t - t₀|
  have hT : 0 ≤ T := abs_nonneg _
  have hTR : T < R := by
    dsimp [T]
    rw [abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hwithin : ∀ s ∈ Icc (t₀ - T) (t₀ + T),
      HasDerivWithinAt α (g s (α s)) (Icc (t₀ - T) (t₀ + T)) s := by
    intro s hs
    have hsR : s ∈ Ioo (t₀ - R) (t₀ + R) :=
      ⟨by linarith [hs.1], by linarith [hs.2]⟩
    simpa only [g, ite_eq_left (Ioo_subset_Icc_self hsR)] using (hα s hsR).hasDerivWithinAt
  have htT : t ∈ Icc (t₀ - T) (t₀ + T) := by
    have h := abs_le.mp (le_refl |t - t₀|)
    exact ⟨by dsimp [T]; linarith [h.1], by dsimp [T]; linarith [h.2]⟩
  exact (norm_le_gronwallBound_of_linear_growth
    C.coe_nonneg C'.coe_nonneg hg hT hwithin t htT).trans
    (gronwallBound_mono (norm_nonneg _) C'.coe_nonneg C.coe_nonneg hTR.le)

/-- Linear growth bounds the speed and makes every solution on a bounded open
interval uniformly Lipschitz. Completeness is not needed for this a priori estimate. -/
theorem lipschitzOnWith_of_linear_growth_Ioo
    {α : ℝ → E} {t₀ R : ℝ} {C C' : ℝ≥0} (_hR : 0 < R)
    (hα : ∀ t ∈ Ioo (t₀ - R) (t₀ + R), HasDerivAt α (f t (α t)) t)
    (hbound : ∀ t ∈ Icc (t₀ - R) (t₀ + R), ∀ x,
      ‖f t x‖ ≤ (C : ℝ) * ‖x‖ + C') :
    ∃ K : ℝ≥0, LipschitzOnWith K α (Ioo (t₀ - R) (t₀ + R)) := by
  let B : ℝ := gronwallBound ‖α t₀‖ C C' R
  have hnorm := norm_le_gronwallBound_of_linear_growth_Ioo hα hbound
  refine ⟨Real.toNNReal ((C : ℝ) * B + C'), ?_⟩
  apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
    (fun t ht => (hα t ht).differentiableAt) _ (convex_Ioo _ _)
  intro t ht
  have hspeed : ‖deriv α t‖ ≤ (C : ℝ) * B + C' := by
    rw [(hα t ht).deriv]
    calc
      ‖f t (α t)‖ ≤ (C : ℝ) * ‖α t‖ + C' := hbound t (Ioo_subset_Icc_self ht) (α t)
      _ ≤ (C : ℝ) * B + C' := by gcongr; exact hnorm t ht
  exact_mod_cast hspeed.trans (Real.le_coe_toNNReal _)

omit [NormedSpace ℝ E] in
/-- A solution on a bounded open time interval whose speed is uniformly bounded has
a finite state limit at its right endpoint. This is the role of completeness in continuation. -/
theorem exists_tendsto_right_of_lipschitzOn [CompleteSpace E]
    {α : ℝ → E} {a b : ℝ} {K : ℝ≥0} (hab : a < b)
    (hα : LipschitzOnWith K α (Ioo a b)) :
    ∃ x : E, Tendsto α (𝓝[<] b) (𝓝 x) := by
  have hI : Ioo a b ∈ 𝓝[<] b := Ioo_mem_nhdsLT hab
  have hc : Cauchy (𝓝[<] b) := cauchy_nhds.mono nhdsWithin_le_nhds
  exact CompleteSpace.complete (hc.map_of_le hα.uniformContinuousOn (le_principal_iff.mpr hI))

/-- A uniformly Lipschitz solution on a bounded open interval extends beyond its
right endpoint. Only local Lipschitz continuity of the vector field is used. -/
theorem exists_extension_Ioo_right [CompleteSpace E]
    (hf : UniformlyLocallyLipschitz f) (hcont : Continuous f.uncurry)
    {α : ℝ → E} {a b : ℝ} {K : ℝ≥0} (hab : a < b)
    (hα : ∀ t ∈ Ioo a b, HasDerivAt α (f t (α t)) t)
    (hαlip : LipschitzOnWith K α (Ioo a b)) :
    ∃ ε > 0, ∃ β : ℝ → E, EqOn β α (Ioo a b) ∧
      ∀ t ∈ Ioo a (b + ε), HasDerivAt β (f t (β t)) t := by
  classical
  obtain ⟨x, hx⟩ := exists_tendsto_right_of_lipschitzOn hab hαlip
  let u : ℝ → E := Function.update α b x
  have hu_eq : EqOn u α (Ioo a b) := by
    intro t ht
    simp [u, Function.update_of_ne (ne_of_lt ht.2)]
  have hu_at : ∀ t ∈ Ioo a b, HasDerivAt u (f t (u t)) t := by
    intro t ht
    rw [hu_eq ht]
    apply (hα t ht).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs using hu_eq hs
  have hu_lim : Tendsto u (𝓝[<] b) (𝓝 (u b)) := by
    simp only [u, Function.update_self]
    apply hx.congr'
    filter_upwards [self_mem_nhdsWithin] with t (ht : t < b)
    simp [Function.update_of_ne (ne_of_lt ht)]
  have hu_left : HasDerivWithinAt u (f b (u b)) (Iic b) b := by
    apply hasDerivWithinAt_Iic_of_tendsto_deriv
      (fun t ht => (hu_at t ht).differentiableAt.differentiableWithinAt)
      (hu_lim.mono_left (nhdsWithin_mono b Ioo_subset_Iio_self)) (Ioo_mem_nhdsLT hab)
    have hf_lim : Tendsto (fun t => f t (u t)) (𝓝[<] b) (𝓝 (f b (u b))) :=
      (hcont.tendsto (b, u b)).comp
        ((show Tendsto (fun t : ℝ => t) (𝓝[<] b) (𝓝 b) from nhdsWithin_le_nhds).prodMk_nhds hu_lim)
    apply hf_lim.congr'
    filter_upwards [Ioo_mem_nhdsLT hab] with t ht
    exact (hu_at t ht).deriv.symm
  have hf_pi : Continuous f := continuous_pi fun x =>
    hcont.comp (continuous_id.prodMk continuous_const)
  obtain ⟨ε, hε, r, hr, ψ, hψ⟩ :=
    hf.exists_forall_mem_closedBall_eq_isIntegralCurveOn hf_pi b (u b)
  let γ : ℝ → E := ψ (u b)
  obtain ⟨hγ0, hγ⟩ := hψ (u b) (mem_closedBall_self hr.le)
  have hγ_at : ∀ t ∈ Ioo (b - ε) (b + ε), HasDerivAt γ (f t (γ t)) t := by
    intro t ht
    exact (hγ t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hγb : γ b = u b := hγ0
  obtain ⟨L, U, hU, hfL⟩ := hf b (u b)
  have hγU : ∀ᶠ t in 𝓝[≤] b, γ t ∈ U := by
    have hU' : U ∈ 𝓝 (γ b) := hγb.symm ▸ hU
    exact ((hγ_at b ⟨by linarith, by linarith⟩).continuousAt.eventually_mem hU').filter_mono
      nhdsWithin_le_nhds
  have huU : ∀ᶠ t in 𝓝[≤] b, u t ∈ U := hu_left.continuousWithinAt.eventually_mem hU
  have hnear : ∀ᶠ t in 𝓝[≤] b,
      a < t ∧ b - ε < t ∧ LipschitzOnWith L (f t) U ∧ u t ∈ U ∧ γ t ∈ U := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hab),
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (show b - ε < b by linarith)),
      hfL.filter_mono nhdsWithin_le_nhds, huU, hγU] with t hat hεt hLt hut hγt
    exact ⟨hat, hεt, hLt, hut, hγt⟩
  obtain ⟨l, hlb, hl⟩ := mem_nhdsLE_iff_exists_Icc_subset.mp hnear
  have hal : a < l := (hl ⟨le_rfl, hlb.le⟩).1
  have hel : b - ε < l := (hl ⟨le_rfl, hlb.le⟩).2.1
  have hγ_small : ∀ t ∈ Icc l b, HasDerivAt γ (f t (γ t)) t := by
    intro t ht
    exact hγ_at t ⟨hel.trans_le ht.1, by linarith [ht.2]⟩
  have hu_small : ∀ t ∈ Icc l b,
      HasDerivWithinAt u (f t (u t)) (Iic b) t := by
    intro t ht
    rcases eq_or_lt_of_le ht.2 with rfl | htb
    · exact hu_left
    · exact (hu_at t ⟨hal.trans_le ht.1, htb⟩).hasDerivWithinAt
  have hagree : EqOn u γ (Icc l b) := by
    apply IsIntegralCurveOn.eqOn_Icc_left (s := fun _ => U)
      (fun t ht => (hl (Ioc_subset_Icc_self ht)).2.2.1)
      (fun t ht => (hu_small t ht).continuousWithinAt.mono Icc_subset_Iic_self)
      (fun t ht => (hu_small t (Ioc_subset_Icc_self ht)).mono Ioc_subset_Iic_self)
      (fun t ht => (hl (Ioc_subset_Icc_self ht)).2.2.2.1)
      (fun t ht => (hγ_small t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hγ_small t (Ioc_subset_Icc_self ht)).hasDerivWithinAt)
      (fun t ht => (hl (Ioc_subset_Icc_self ht)).2.2.2.2)
      hγb.symm
  let c : ℝ := (l + b) / 2
  have hlc : l < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  let β : ℝ → E := fun t => if t ≤ c then α t else γ t
  have hβα : EqOn β α (Ioo a b) := by
    intro t ht
    dsimp [β]
    split_ifs with htc
    · rfl
    · have hlt : l ≤ t := by linarith [lt_of_not_ge htc]
      exact (hagree ⟨hlt, ht.2.le⟩).symm.trans (hu_eq ht)
  refine ⟨ε, hε, β, hβα, fun t ht => ?_⟩
  rcases lt_or_ge t b with htb | hbt
  · rw [hβα ⟨ht.1, htb⟩]
    apply (hα t ⟨ht.1, htb⟩).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ⟨ht.1, htb⟩] with s hs using hβα hs
  · have hct : c < t := hcb.trans_le hbt
    have hβγ : β =ᶠ[𝓝 t] γ := by
      filter_upwards [Ioi_mem_nhds hct] with s hs
      simp [β, not_le.mpr hs]
    rw [hβγ.eq_of_nhds]
    exact (hγ_at t ⟨hel.trans hlc |>.trans hct, ht.2⟩).congr_of_eventuallyEq hβγ

/-- A bounded-speed solution extends beyond both endpoints of a bounded open
interval. Time reversal reduces left continuation to right continuation. -/
theorem exists_extension_Ioo [CompleteSpace E]
    (hf : UniformlyLocallyLipschitz f) (hcont : Continuous f.uncurry)
    {α : ℝ → E} {a b : ℝ} {K : ℝ≥0} (hab : a < b)
    (hα : ∀ t ∈ Ioo a b, HasDerivAt α (f t (α t)) t)
    (hαlip : LipschitzOnWith K α (Ioo a b)) :
    ∃ ε > 0, ∃ β : ℝ → E, EqOn β α (Ioo a b) ∧
      ∀ t ∈ Ioo (a - ε) (b + ε), HasDerivAt β (f t (β t)) t := by
  classical
  obtain ⟨εr, hεr, βr, hβr_eq, hβr⟩ := exists_extension_Ioo_right hf hcont hab hα hαlip
  let v : ℝ → E → E := fun t x => -(f (-t) x)
  have hv : UniformlyLocallyLipschitz v := by
    intro t₀ x₀
    obtain ⟨L, U, hU, hL⟩ := hf (-t₀) x₀
    refine ⟨L, U, hU, ?_⟩
    filter_upwards [(continuous_neg.tendsto t₀).eventually hL] with t ht
    exact ht.neg
  have hvcont : Continuous v.uncurry := by
    exact (hcont.comp (continuous_fst.neg.prodMk continuous_snd)).neg
  have hαrev : ∀ t ∈ Ioo (-b) (-a),
      HasDerivAt (fun s => α (-s)) (v t (α (-t))) t := by
    intro t ht
    have h := (hα (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩).scomp t (hasDerivAt_neg t)
    simpa [v, Function.comp_def] using h
  have hαrev_lip : LipschitzOnWith K (fun t => α (-t)) (Ioo (-b) (-a)) := by
    refine LipschitzOnWith.of_dist_le_mul fun s hs t ht => ?_
    have h := hαlip.dist_le_mul (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
      (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa only [dist_neg_neg] using h
  obtain ⟨εl, hεl, βrev, hβrev_eq, hβrev⟩ :=
    exists_extension_Ioo_right hv hvcont (by linarith : -b < -a) hαrev hαrev_lip
  let βl : ℝ → E := fun t => βrev (-t)
  have hβl_eq : EqOn βl α (Ioo a b) := by
    intro t ht
    have h := hβrev_eq (x := -t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa only [neg_neg] using h
  have hβl : ∀ t ∈ Ioo (a - εl) b, HasDerivAt βl (f t (βl t)) t := by
    intro t ht
    have h := (hβrev (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩).scomp t (hasDerivAt_neg t)
    simpa [βl, v, Function.comp_def] using h
  let c : ℝ := (a + b) / 2
  have hac : a < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  let β : ℝ → E := fun t => if t ≤ c then βl t else βr t
  have hβα : EqOn β α (Ioo a b) := by
    intro t ht
    dsimp [β]
    split_ifs with htc
    · exact hβl_eq ht
    · exact hβr_eq ht
  refine ⟨min εl εr, lt_min hεl hεr, β, hβα, fun t ht => ?_⟩
  by_cases hta : t ≤ a
  · have htc : t < c := hta.trans_lt hac
    have hβeq : β =ᶠ[𝓝 t] βl := by
      filter_upwards [Iio_mem_nhds htc] with s hs
      simp only [β, ite_eq_left hs.le]
    rw [hβeq.eq_of_nhds]
    apply (hβl t ⟨?_, hta.trans_lt hab⟩).congr_of_eventuallyEq hβeq
    linarith [ht.1, min_le_left εl εr]
  · have hat : a < t := lt_of_not_ge hta
    by_cases htb : t < b
    · rw [hβα ⟨hat, htb⟩]
      apply (hα t ⟨hat, htb⟩).congr_of_eventuallyEq
      filter_upwards [isOpen_Ioo.mem_nhds ⟨hat, htb⟩] with s hs using hβα hs
    · have hct : c < t := hcb.trans_le (le_of_not_gt htb)
      have hβeq : β =ᶠ[𝓝 t] βr := by
        filter_upwards [Ioi_mem_nhds hct] with s hs
        simp only [β, ite_eq_right (not_le.mpr hs)]
      rw [hβeq.eq_of_nhds]
      apply (hβr t ⟨hat, ?_⟩).congr_of_eventuallyEq hβeq
      linarith [ht.2, min_le_right εl εr]

end ODE
