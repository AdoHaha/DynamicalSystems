/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.MeasureTheory.MovingIntervalCompactness
public import DynamicalSystems.OptimalControl.ContinuousTime.CesariCompactnessArgument

/-!
# Cesari extraction on moving time intervals

Endpoint extraction and weak L1 compactness preserve the actual limiting
trajectory and boundary condition. At each interior time, the original epigraph
membership is eventually valid. Extending the limiting epigraph by a nonnegative
cost half-space outside the interval permits global Mazur/Fatou lower closure,
and restricting the resulting cost majorant cannot increase its integral.

This joins Steps 1 and 3 of BM Theorem 5.4.4 for extended minimizing sequences.
The construction of finite-atomic relaxed controls and the complete objective
comparison remain separate.
-/

@[expose] public section

open Set Filter MeasureTheory Topology
open DynamicalSystems.EquiIntegrableTrajectories
open scoped ENNReal BoundedContinuousFunction

namespace OptimalControl

section ConstantEpigraph

variable {T E F : Type*} [PseudoMetricSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Property (Q) depends only on the state fibers at the specified time. -/
theorem hasWeakCesariProperty_congr_at_time
    (Q R : T → E → Set F) (t : T) (x : E) (h : Q t = R t) :
    HasWeakCesariProperty Q t x ↔ HasWeakCesariProperty R t x := by
  unfold HasWeakCesariProperty cesariCore cesariHull cesariTube
  rw [h]

/-- A constant closed convex epigraph has property (Q). This is used only for
the exterior cost half-space in the moving-interval lower-closure proof. -/
theorem hasWeakCesariProperty_const_of_isClosed_of_convex
    (S : Set F) (hS : IsClosed S) (hconv : Convex ℝ S) (t : T) (x : E) :
    HasWeakCesariProperty (fun _ _ ↦ S) t x := by
  intro p hp
  have hsub : cesariTube (fun (_ : T) (_ : E) ↦ S) t x 1 ⊆ S := by
    intro z hz
    simp only [cesariTube, mem_iUnion] at hz
    obtain ⟨_, _, hz⟩ := hz
    exact hz
  have hcore := (mem_cesariCore_iff _ _ _ _).mp hp 1 zero_lt_one
  exact (hS.closure_subset_iff.mpr (convexHull_min hsub hconv)) hcore

end ConstantEpigraph

section Extraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {a b : ℝ}

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Constant extension preserves membership in the state projection of the
original time–state constraint set. No product enlargement of property (Q) is needed. -/
theorem mem_state_projection_of_constant_extension
    (x : ℕ → Icc a b →ᵇ E) (l r : ℕ → Icc a b) (R : Set (ℝ × E))
    (hstate : ∀ n (t : Icc a b), (t : ℝ) ∈ Icc (l n : ℝ) (r n : ℝ) → ((t : ℝ), x n t) ∈ R)
    (hordered : ∀ n, (l n : ℝ) ≤ r n)
    (hleft : ∀ n (t : Icc a b), (t : ℝ) ≤ l n → x n t = x n (l n))
    (hright : ∀ n (t : Icc a b), (r n : ℝ) ≤ t → x n t = x n (r n)) :
    ∀ n t, x n t ∈ Prod.snd '' R := by
  intro n t
  by_cases hl : (t : ℝ) ≤ l n
  · rw [hleft n t hl]
    exact ⟨((l n : ℝ), x n (l n)), hstate n (l n) ⟨le_rfl, hordered n⟩, rfl⟩
  by_cases hr : (r n : ℝ) ≤ t
  · rw [hright n t hr]
    exact ⟨((r n : ℝ), x n (r n)), hstate n (r n) ⟨hordered n, le_rfl⟩, rfl⟩
  exact ⟨((t : ℝ), x n t), hstate n t ⟨(not_le.mp hl).le, (not_le.mp hr).le⟩, rfl⟩

/-- Uniform trajectory, endpoint, and weak L1 derivative extraction followed by
Cesari/Fatou lower closure on the actual limiting interval. Original epigraph
feasibility is required only inside each original moving interval. The limiting
closed boundary condition and exterior constancy are conclusions.
This is the moving-interval analytic extraction in BM Theorem 5.4.4, Steps 1/3;
no supplied weak limit or recovery certificate is used. -/
theorem exists_limit_endpoints_cost_epigraph_of_unifIntegrable
    (hab : a ≤ b) (x : ℕ → Icc a b →ᵇ E)
    (w : ℕ → Lp E 1 (volume.restrict (Icc a b))) (l r : ℕ → Icc a b)
    (Q : ℝ → E → Set (E × ℝ)) (c : ℕ → ℝ → ℝ) (γ : ℝ)
    (R : Set (ℝ × E)) (hR : IsCompact R)
    (hstate : ∀ n (t : Icc a b), (t : ℝ) ∈ Icc (l n : ℝ) (r n : ℝ) → ((t : ℝ), x n t) ∈ R)
    (hUI : UnifIntegrable (fun n t ↦ w n t) 1 (volume.restrict (Icc a b)))
    (hlaw : ∀ n (s t : Icc a b), x n t - x n s =
      ∫ z in (s : ℝ)..(t : ℝ), w n z ∂volume.restrict (Icc a b))
    (hleft : ∀ n (t : Icc a b), (t : ℝ) ≤ l n → x n t = x n (l n))
    (hright : ∀ n (t : Icc a b), (r n : ℝ) ≤ t → x n t = x n (r n))
    (B : Set (ℝ × E × ℝ × E)) (hB : IsClosed B)
    (hBtime : ∀ p ∈ B, p.1 < p.2.2.1)
    (hboundary : ∀ n, ((l n : ℝ), x n (l n), (r n : ℝ), x n (r n)) ∈ B)
    (hcesari : ∀ p ∈ R, HasWeakCesariProperty Q p.1 p.2)
    (hw : ∀ n, ∀ᵐ t ∂volume.restrict (Icc a b), t ∈ Ioo (l n : ℝ) (r n : ℝ) →
      (w n t, c n t) ∈ Q t (intervalPathValue (x n) t))
    (hc : ∀ n, ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ c n t)
    (hci : ∀ n, Integrable (c n) (volume.restrict (Icc a b)))
    (hcost : Tendsto (fun n ↦ ∫ t, c n t ∂volume.restrict (Icc a b)) atTop (𝓝 γ)) :
    ∃ (xlim : Icc a b →ᵇ E) (v : Lp E 1 (volume.restrict (Icc a b)))
      (l₀ r₀ : Icc a b) (costLimit : ℝ → ℝ) (k : ℕ → ℕ), StrictMono k ∧
      Tendsto (x ∘ k) atTop (𝓝 xlim) ∧ (∀ t, xlim t ∈ Prod.snd '' R) ∧
      Tendsto (l ∘ k) atTop (𝓝 l₀) ∧ Tendsto (r ∘ k) atTop (𝓝 r₀) ∧
      (l₀ : ℝ) < r₀ ∧ ((l₀ : ℝ), xlim l₀, (r₀ : ℝ), xlim r₀) ∈ B ∧
      Tendsto (fun n ↦ toWeakSpace ℝ (Lp E 1 (volume.restrict (Icc a b))) (w (k n)))
        atTop (𝓝 (toWeakSpace ℝ (Lp E 1 (volume.restrict (Icc a b))) v)) ∧
      (∀ t : Icc a b, xlim t - xlim ⟨a, le_rfl, hab⟩ =
        ∫ z in Ioc a (t : ℝ), v z ∂volume.restrict (Icc a b)) ∧
      (∀ t : Icc (l₀ : ℝ) (r₀ : ℝ),
        xlim ⟨t, l₀.property.1.trans t.property.1, t.property.2.trans r₀.property.2⟩ - xlim l₀ =
          ∫ z in Ioc (l₀ : ℝ) (t : ℝ), v z
            ∂volume.restrict (Icc (l₀ : ℝ) (r₀ : ℝ))) ∧
      (∀ t : Icc a b, (t : ℝ) ≤ l₀ → xlim t = xlim l₀) ∧
      (∀ t : Icc a b, (r₀ : ℝ) ≤ t → xlim t = xlim r₀) ∧
      Integrable costLimit (volume.restrict (Icc (l₀ : ℝ) (r₀ : ℝ))) ∧
      (∀ᵐ t ∂volume.restrict (Icc (l₀ : ℝ) (r₀ : ℝ)),
        (v t, costLimit t) ∈ Q t (intervalPathValue xlim t)) ∧
      (∫ t, costLimit t ∂volume.restrict (Icc (l₀ : ℝ) (r₀ : ℝ))) ≤ γ := by
  classical
  let K := Prod.snd '' R
  have hK : IsCompact K := hR.image continuous_snd
  have hvalues : ∀ n t, x n t ∈ K := mem_state_projection_of_constant_extension
    x l r R hstate (fun n ↦ (hBtime _ (hboundary n)).le) hleft hright
  obtain ⟨xlim, v, l₀, r₀, k, hk, hx, hvalueslim, hl, hr, hlr, hboundarylim,
    hweak, hlawlim, hleftlim, hrightlim⟩ :=
    exists_uniform_limit_endpoints_weak_L1_integral_law hab x w l r K hK hvalues hUI
      hlaw hleft hright B hB hBtime hboundary
  let Qext (t : ℝ) (y : E) : Set (E × ℝ) :=
    if t ∈ Ioo (l₀ : ℝ) (r₀ : ℝ) then Q t y else {p | 0 ≤ p.2}
  have hhalf : ∀ (t : ℝ) (y : E), HasWeakCesariProperty (fun _ _ ↦ {p : E × ℝ | 0 ≤ p.2}) t y :=
    hasWeakCesariProperty_const_of_isClosed_of_convex _
      (isClosed_le continuous_const continuous_snd)
      ((convex_Ici (0 : ℝ)).linear_preimage (LinearMap.snd ℝ E ℝ))
  have hxR : ∀ t : Icc a b, (t : ℝ) ∈ Ioo (l₀ : ℝ) (r₀ : ℝ) →
      ((t : ℝ), xlim t) ∈ R := by
    intro t ht
    apply hR.isClosed.mem_of_tendsto (tendsto_const_nhds.prodMk_nhds (hx.eval_const t))
    have hint := eventually_mem_Ioo_of_endpoint_tendsto
      ((continuous_subtype_val.tendsto l₀).comp hl)
      ((continuous_subtype_val.tendsto r₀).comp hr) ht
    exact hint.mono fun n hn ↦ hstate (k n) t ⟨hn.1.le, hn.2.le⟩
  have hcesarilim : ∀ᵐ t ∂volume.restrict (Icc a b),
      HasWeakCesariProperty Qext t (intervalPathValue xlim t) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    by_cases hi : t ∈ Ioo (l₀ : ℝ) (r₀ : ℝ)
    · apply (hasWeakCesariProperty_congr_at_time Qext Q t _
        (by funext y; simp only [Qext, ite_eq_left hi])).mpr
      have h : HasWeakCesariProperty Q t (xlim ⟨t, ht⟩) :=
        hcesari (t, xlim ⟨t, ht⟩) (hxR ⟨t, ht⟩ hi)
      exact (intervalPathValue_of_mem xlim t ht).symm ▸ h
    · apply (hasWeakCesariProperty_congr_at_time Qext
        (fun _ _ ↦ {p : E × ℝ | 0 ≤ p.2}) t _
        (by funext y; simp only [Qext, ite_eq_right hi])).mpr
      exact hhalf t (intervalPathValue xlim t)
  have hxlim : ∀ᵐ t ∂volume.restrict (Icc a b),
      Tendsto (fun n ↦ intervalPathValue (x (k n)) t) atTop
        (𝓝 (intervalPathValue xlim t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [intervalPathValue_of_mem _ t ht, Function.comp_apply] using
      hx.eval_const ⟨t, ht⟩
  have hfeasible : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ᶠ n in atTop,
      (w (k n) t, c (k n) t) ∈ Qext t (intervalPathValue (x (k n)) t) := by
    filter_upwards [ae_all_iff.mpr hw, ae_all_iff.mpr hc] with t hwt hct
    by_cases hi : t ∈ Ioo (l₀ : ℝ) (r₀ : ℝ)
    · have hint := eventually_mem_Ioo_of_endpoint_tendsto
        ((continuous_subtype_val.tendsto l₀).comp hl)
        ((continuous_subtype_val.tendsto r₀).comp hr) hi
      exact hint.mono fun n hn ↦ by simpa only [Qext, ite_eq_left hi] using hwt (k n) hn
    · exact Eventually.of_forall fun n ↦ by
        simpa only [Qext, ite_eq_right hi, mem_ofPred_eq] using hct (k n)
  obtain ⟨costLimit, hcostInt, hepi, hbound⟩ :=
    exists_integrable_cost_epigraph_of_weak_Lp_tendsto_of_eventually_mem
      Qext (intervalPathValue xlim) (fun n ↦ intervalPathValue (x (k n)))
      (fun n ↦ w (k n)) (fun n ↦ c (k n)) v γ hcesarilim hxlim hfeasible
      (fun n ↦ hc (k n)) (fun n ↦ hci (k n)) (hcost.comp hk.tendsto_atTop) hweak
  have hsubset : Icc (l₀ : ℝ) (r₀ : ℝ) ⊆ Icc a b := fun t ht ↦
    ⟨l₀.property.1.trans ht.1, ht.2.trans r₀.property.2⟩
  have hrestrict : (volume.restrict (Icc a b)).restrict (Icc (l₀ : ℝ) (r₀ : ℝ)) =
      volume.restrict (Icc (l₀ : ℝ) (r₀ : ℝ)) := by
    rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hsubset]
  have hepilim := hepi.filter_mono
    (ae_mono (Measure.restrict_le_self :
      (volume.restrict (Icc a b)).restrict (Icc (l₀ : ℝ) (r₀ : ℝ)) ≤ _))
  rw [hrestrict] at hepilim
  have hinside : ∀ᵐ t ∂volume.restrict (Icc (l₀ : ℝ) (r₀ : ℝ)),
      t ∈ Ioo (l₀ : ℝ) (r₀ : ℝ) := by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ioo
  have hcostIntlim : Integrable costLimit (volume.restrict (Icc (l₀ : ℝ) (r₀ : ℝ))) := by
    rw [← hrestrict]
    exact hcostInt.restrict
  refine ⟨xlim, v, l₀, r₀, costLimit, k, hk, hx, hvalueslim, hl, hr, hlr, hboundarylim,
    hweak, hlawlim,
    (fun t ↦ integral_difference_law_on_subinterval hab xlim v hlawlim l₀ r₀ t),
    hleftlim, hrightlim, hcostIntlim, ?_, ?_⟩
  · filter_upwards [hepilim, hinside] with t ht hi
    simpa only [Qext, ite_eq_left hi] using ht
  · rw [← hrestrict, ← integral_indicator measurableSet_Icc]
    apply le_trans (integral_mono_ae (hcostInt.indicator measurableSet_Icc) hcostInt ?_) hbound
    filter_upwards [hepi] with t ht
    by_cases hi : t ∈ Icc (l₀ : ℝ) (r₀ : ℝ)
    · simp only [indicator_of_mem hi, le_refl]
    · have hnot : t ∉ Ioo (l₀ : ℝ) (r₀ : ℝ) := fun h ↦ hi ⟨h.1.le, h.2.le⟩
      simpa only [indicator_of_notMem hi, Qext, ite_eq_right hnot, mem_ofPred_eq] using ht

end Extraction

section Objective

variable {Z : Type*} [TopologicalSpace Z]

/-- Lower semicontinuity of the terminal cost on the compact endpoint set and
nonnegative running costs yield a convergent running-cost subsequence from a
convergent total minimizing cost. The bounded cost subsequence is constructed.
This is BM Theorem 5.4.4, Step 2. -/
theorem exists_runningCost_tendsto_subseq_of_tendsto_totalCost
    (S : Set Z) (hS : IsCompact S) (g : Z → ℝ) (hg : LowerSemicontinuousOn g S)
    (e : ℕ → Z) (he : ∀ n, e n ∈ S) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n)
    (m : ℝ) (hcost : Tendsto (fun n ↦ g (e n) + c n) atTop (𝓝 m)) :
    ∃ (γ : ℝ) (k : ℕ → ℕ), StrictMono k ∧ Tendsto (c ∘ k) atTop (𝓝 γ) := by
  obtain ⟨A, hA⟩ := hg.bddBelow_of_isCompact hS
  obtain ⟨M, hM⟩ := hcost.isBoundedUnder_le
  obtain ⟨N, hN⟩ := eventually_atTop.mp hM
  have hbound : ∀ n, c (n + N) ∈ Icc 0 (M - A) := by
    intro n
    refine ⟨hc _, ?_⟩
    have ha : A ≤ g (e (n + N)) := hA ⟨e (n + N), he _, rfl⟩
    have hm := hN (n + N) (Nat.le_add_left N n)
    change g (e (n + N)) + c (n + N) ≤ M at hm
    linarith
  obtain ⟨γ, _, k, hk, hlim⟩ := isCompact_Icc.tendsto_subseq hbound
  exact ⟨γ, fun n ↦ k n + N,
    fun i j hij ↦ Nat.add_lt_add_right (hk hij) N, hlim⟩

/-- A lower semicontinuous terminal cost passes to limiting endpoints when the
running integrals and total objectives converge. Combining this with the Fatou
running-cost bound is the objective comparison in BM Theorem 5.4.4, Step 5. -/
theorem terminalCost_add_le_of_tendsto_totalCost
    (B : Set Z) (hB : IsClosed B) (g : Z → ℝ) (hg : LowerSemicontinuousOn g B)
    (e : ℕ → Z) (e₀ : Z) (he : ∀ n, e n ∈ B) (helim : Tendsto e atTop (𝓝 e₀))
    (c : ℕ → ℝ) (γ m : ℝ) (hc : Tendsto c atTop (𝓝 γ))
    (hcost : Tendsto (fun n ↦ g (e n) + c n) atTop (𝓝 m)) : g e₀ + γ ≤ m := by
  have hgcost : Tendsto (fun n ↦ g (e n)) atTop (𝓝 (m - γ)) := by
    simpa only [add_sub_cancel_right] using hcost.sub hc
  have hclosed := (lowerSemicontinuousOn_iff_isClosed_epigraph hB).mp hg
  have hmem : (e₀, m - γ) ∈ {p : Z × ℝ | p.1 ∈ B ∧ g p.1 ≤ p.2} :=
    hclosed.mem_of_tendsto (helim.prodMk_nhds hgcost)
      (Eventually.of_forall fun n ↦ ⟨he n, le_rfl⟩)
  linarith [hmem.2]

end Objective

section ObjectiveExtraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {a b : ℝ}

/-- Moving-endpoint extraction and Cesari/Fatou lower closure from a convergent
complete minimizing objective. The running-cost subsequence and terminal-cost
comparison are proved from the compact range and lower semicontinuous boundary
cost. This joins the analytic Steps 1, 2, 3, and 5 of BM Theorem 5.4.4.
The result is an objective epigraph; control realization and the full relaxed
problem admissibility are not supplied as assumptions or asserted as conclusions. -/
theorem exists_limit_endpoints_objective_epigraph_of_unifIntegrable
    (hab : a ≤ b) (x : ℕ → Icc a b →ᵇ E)
    (w : ℕ → Lp E 1 (volume.restrict (Icc a b))) (l r : ℕ → Icc a b)
    (Q : ℝ → E → Set (E × ℝ)) (c : ℕ → ℝ → ℝ)
    (R : Set (ℝ × E)) (hR : IsCompact R)
    (hstate : ∀ n (t : Icc a b), (t : ℝ) ∈ Icc (l n : ℝ) (r n : ℝ) → ((t : ℝ), x n t) ∈ R)
    (hUI : UnifIntegrable (fun n t ↦ w n t) 1 (volume.restrict (Icc a b)))
    (hlaw : ∀ n (s t : Icc a b), x n t - x n s =
      ∫ z in (s : ℝ)..(t : ℝ), w n z ∂volume.restrict (Icc a b))
    (hleft : ∀ n (t : Icc a b), (t : ℝ) ≤ l n → x n t = x n (l n))
    (hright : ∀ n (t : Icc a b), (r n : ℝ) ≤ t → x n t = x n (r n))
    (B : Set (ℝ × E × ℝ × E)) (hB : IsClosed B)
    (hBtime : ∀ p ∈ B, p.1 < p.2.2.1)
    (hboundary : ∀ n, ((l n : ℝ), x n (l n), (r n : ℝ), x n (r n)) ∈ B)
    (g : ℝ × E × ℝ × E → ℝ) (hg : LowerSemicontinuousOn g B)
    (hcesari : ∀ p ∈ R, HasWeakCesariProperty Q p.1 p.2)
    (hw : ∀ n, ∀ᵐ t ∂volume.restrict (Icc a b), t ∈ Ioo (l n : ℝ) (r n : ℝ) →
      (w n t, c n t) ∈ Q t (intervalPathValue (x n) t))
    (hc : ∀ n, ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ c n t)
    (hci : ∀ n, Integrable (c n) (volume.restrict (Icc a b)))
    (m : ℝ) (hcost : Tendsto (fun n ↦
      g ((l n : ℝ), x n (l n), (r n : ℝ), x n (r n)) +
        ∫ t, c n t ∂volume.restrict (Icc a b)) atTop (𝓝 m)) :
    ∃ (xlim : Icc a b →ᵇ E) (v : Lp E 1 (volume.restrict (Icc a b)))
      (l₀ r₀ : Icc a b) (costLimit : ℝ → ℝ) (k : ℕ → ℕ), StrictMono k ∧
      Tendsto (x ∘ k) atTop (𝓝 xlim) ∧ (∀ t, xlim t ∈ Prod.snd '' R) ∧
      Tendsto (l ∘ k) atTop (𝓝 l₀) ∧ Tendsto (r ∘ k) atTop (𝓝 r₀) ∧
      (l₀ : ℝ) < r₀ ∧ ((l₀ : ℝ), xlim l₀, (r₀ : ℝ), xlim r₀) ∈ B ∧
      Tendsto (fun n ↦ toWeakSpace ℝ (Lp E 1 (volume.restrict (Icc a b))) (w (k n)))
        atTop (𝓝 (toWeakSpace ℝ (Lp E 1 (volume.restrict (Icc a b))) v)) ∧
      (∀ t : Icc (l₀ : ℝ) (r₀ : ℝ),
        xlim ⟨t, l₀.property.1.trans t.property.1, t.property.2.trans r₀.property.2⟩ - xlim l₀ =
          ∫ z in Ioc (l₀ : ℝ) (t : ℝ), v z
            ∂volume.restrict (Icc (l₀ : ℝ) (r₀ : ℝ))) ∧
      (∀ t : Icc a b, (t : ℝ) ≤ l₀ → xlim t = xlim l₀) ∧
      (∀ t : Icc a b, (r₀ : ℝ) ≤ t → xlim t = xlim r₀) ∧
      Integrable costLimit (volume.restrict (Icc (l₀ : ℝ) (r₀ : ℝ))) ∧
      (∀ᵐ t ∂volume.restrict (Icc (l₀ : ℝ) (r₀ : ℝ)),
        (v t, costLimit t) ∈ Q t (intervalPathValue xlim t)) ∧
      g ((l₀ : ℝ), xlim l₀, (r₀ : ℝ), xlim r₀) +
        (∫ t, costLimit t ∂volume.restrict (Icc (l₀ : ℝ) (r₀ : ℝ))) ≤ m := by
  let K := Prod.snd '' R
  have hK : IsCompact K := hR.image continuous_snd
  have hvalues : ∀ n t, x n t ∈ K := mem_state_projection_of_constant_extension
    x l r R hstate (fun n ↦ (hBtime _ (hboundary n)).le) hleft hright
  let S : Set (ℝ × E × ℝ × E) := (Icc a b ×ˢ (K ×ˢ (Icc a b ×ˢ K))) ∩ B
  have hS : IsCompact S :=
    (isCompact_Icc.prod (hK.prod (isCompact_Icc.prod hK))).inter_right hB
  let e n := ((l n : ℝ), x n (l n), (r n : ℝ), x n (r n))
  have heS : ∀ n, e n ∈ S := fun n ↦
    ⟨⟨(l n).property, hvalues n _, (r n).property, hvalues n _⟩, hboundary n⟩
  obtain ⟨γ, j, hj, hrun⟩ := exists_runningCost_tendsto_subseq_of_tendsto_totalCost
    S hS g (hg.mono inter_subset_right) e heS
    (fun n ↦ ∫ t, c n t ∂volume.restrict (Icc a b))
    (fun n ↦ integral_nonneg_of_ae (hc n)) m hcost
  obtain ⟨xlim, v, l₀, r₀, costLimit, k, hk, hx, hvalueslim, hl, hr, hlr, hboundarylim,
    hweak, _, hlawlim, hleftlim, hrightlim, hcostInt, hepi, hbound⟩ :=
    exists_limit_endpoints_cost_epigraph_of_unifIntegrable hab (fun n ↦ x (j n))
      (fun n ↦ w (j n)) (fun n ↦ l (j n)) (fun n ↦ r (j n)) Q (fun n ↦ c (j n)) γ
      R hR (fun n ↦ hstate (j n)) (hUI.comp j) (fun n ↦ hlaw (j n))
      (fun n ↦ hleft (j n)) (fun n ↦ hright (j n)) B hB hBtime
      (fun n ↦ hboundary (j n)) hcesari (fun n ↦ hw (j n))
      (fun n ↦ hc (j n)) (fun n ↦ hci (j n)) hrun
  have helim : Tendsto (fun n ↦ e (j (k n))) atTop
      (𝓝 ((l₀ : ℝ), xlim l₀, (r₀ : ℝ), xlim r₀)) :=
    ((continuous_subtype_val.tendsto l₀).comp hl).prodMk_nhds
      ((hx.eval hl).prodMk_nhds
        (((continuous_subtype_val.tendsto r₀).comp hr).prodMk_nhds (hx.eval hr)))
  have hterminal := terminalCost_add_le_of_tendsto_totalCost B hB g hg
    (fun n ↦ e (j (k n))) _ (fun n ↦ hboundary (j (k n))) helim
    (fun n ↦ ∫ t, c (j (k n)) t ∂volume.restrict (Icc a b)) γ m
    (hrun.comp hk.tendsto_atTop) (hcost.comp (hj.comp hk).tendsto_atTop)
  exact ⟨xlim, v, l₀, r₀, costLimit, j ∘ k, hj.comp hk, hx, hvalueslim, hl, hr, hlr,
    hboundarylim, hweak, hlawlim, hleftlim, hrightlim, hcostInt, hepi,
    (add_le_add (le_refl _) hbound).trans hterminal⟩

end ObjectiveExtraction

end OptimalControl
