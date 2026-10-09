/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.CesariExistence
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Cesari lower closure for convexified minimizing sequences

This module proves the pointwise and integral lower-closure step in the proof of
Berkovitz & Medhin, Theorem 5.4.4, Step 3, equations (5.4.29)–(5.4.32).
Velocity combinations converge strongly; cost combinations need only have a finite
nonnegative liminf. A cost-dependent subsequence and the weak Cesari property recover
feasibility. Fatou gives the cost bound and almost-everywhere finiteness.

Common Mazur weights and a.e. convergence are constructed from weak Lp convergence.
The extraction of an equi-absolutely-continuous trajectory subsequence, weak L¹
derivative convergence, and measurable relaxed recovery are not asserted here.
In particular this module does not yet prove existence of a
relaxed minimizer under the full noncompact hypotheses of Theorem 5.4.4.
-/

@[expose] public section

open Set Filter MeasureTheory Topology
open scoped ENNReal

namespace OptimalControl

section TailCombinations

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A finite convex combination supported after `N` lies in the convex hull of that tail.
This supplies the common velocity–cost combinations in (5.4.29) and (5.4.31). -/
theorem sum_mem_convexHull_tail (w : ℕ → F) (N : ℕ) (s : Finset ℕ) (a : ℕ → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hsum : ∑ i ∈ s, a i = 1)
    (hN : ∀ i ∈ s, N ≤ i) :
    (∑ i ∈ s, a i • w i) ∈ convexHull ℝ (w '' Ici N) := by
  exact (convex_convexHull ℝ _).sum_mem ha hsum fun i hi ↦
    subset_convexHull ℝ _ ⟨i, hN i hi, rfl⟩

/-- A point in the convex hull of a sequence tail has finite nonnegative weights
on the original sequence indices. This keeps the velocity and cost weights identical. -/
theorem exists_weights_of_mem_convexHull_tail (w : ℕ → F) (N : ℕ) (z : F)
    (hz : z ∈ convexHull ℝ (w '' Ici N)) :
    ∃ (s : Finset ℕ) (a : ℕ → ℝ), (∀ i ∈ s, 0 ≤ a i) ∧
      (∑ i ∈ s, a i = 1) ∧ (∀ i ∈ s, N ≤ i) ∧ ∑ i ∈ s, a i • w i = z := by
  classical
  have hrange : range (fun i : Ici N ↦ w i) = w '' Ici N := by
    ext y
    simp only [mem_range, mem_image, mem_Ici]
    exact ⟨fun ⟨i, hi⟩ ↦ ⟨i, i.property, hi⟩,
      fun ⟨i, hi, hy⟩ ↦ ⟨⟨i, hi⟩, hy⟩⟩
  rw [← hrange, convexHull_range_eq_exists_affineCombination] at hz
  obtain ⟨s, b, hb, hsum, heq⟩ := hz
  let a i := if hi : N ≤ i then b ⟨i, hi⟩ else 0
  have ha : ∀ i : Ici N, a i = b i := fun i ↦ by
    simp [a, show N ≤ (i : ℕ) from i.property]
  refine ⟨s.image Subtype.val, a, ?_, ?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
    rw [ha]
    exact hb k hk
  · rw [Finset.sum_image (fun _ _ _ _ h ↦ Subtype.val_injective h)]
    simpa only [ha] using hsum
  · intro i hi
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
    exact k.property
  · rw [Finset.sum_image (fun _ _ _ _ h ↦ Subtype.val_injective h)]
    simp_rw [ha]
    rw [Finset.affineCombination_eq_linear_combination s _ b hsum] at heq
    exact heq

end TailCombinations

section Mazur

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The constructive sequential form of Mazur's lemma (Berkovitz & Medhin,
Lemma 5.3.6): a weak limit is a strong limit of convex combinations of escaping tails.
The proof uses the equality of weak and norm closures of convex sets. -/
theorem exists_tendsto_tail_convex_combinations_of_weak_tendsto
    (w : ℕ → F) (z : F)
    (hw : Tendsto (fun j ↦ toWeakSpace ℝ F (w j)) atTop
      (𝓝 (toWeakSpace ℝ F z))) :
    ∃ zs : ℕ → F, (∀ j, zs j ∈ convexHull ℝ (w '' Ici j)) ∧
      Tendsto zs atTop (𝓝 z) := by
  have hcl : ∀ N, z ∈ closure (convexHull ℝ (w '' Ici N)) := by
    intro N
    have hweak : toWeakSpace ℝ F z ∈
        closure (toWeakSpace ℝ F '' convexHull ℝ (w '' Ici N)) := by
      refine mem_closure_of_tendsto hw ?_
      filter_upwards [eventually_ge_atTop N] with j hj
      exact ⟨w j, subset_convexHull ℝ _ ⟨j, hj, rfl⟩, rfl⟩
    rw [← (convex_convexHull ℝ _).toWeakSpace_closure ℝ] at hweak
    simpa only [Set.mem_image, (toWeakSpace ℝ F).injective.eq_iff, exists_eq_right] using hweak
  have happ : ∀ j : ℕ, ∃ y ∈ convexHull ℝ (w '' Ici j),
      dist z y < 1 / ((j : ℝ) + 1) := by
    intro j
    exact Metric.mem_closure_iff.mp (hcl j) _ (by positivity)
  choose zs hz hd using happ
  refine ⟨zs, hz, Metric.tendsto_atTop.mpr ?_⟩
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) ε hε
  refine ⟨N, fun j hj ↦ ?_⟩
  rw [dist_comm]
  have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  exact (hd j).trans (by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hpos] using (hN j hj))

/-- Tail convex combinations preserve a convergent sequence's limit. This is the
content needed from Berkovitz & Medhin Lemma 5.3.7 for the minimizing costs. -/
theorem tendsto_tail_convex_combinations (w zs : ℕ → F) (z : F)
    (hw : Tendsto w atTop (𝓝 z))
    (hz : ∀ j, zs j ∈ convexHull ℝ (w '' Ici j)) :
    Tendsto zs atTop (𝓝 z) := by
  refine Metric.tendsto_atTop.mpr fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hw ε hε
  refine ⟨N, fun j hj ↦ ?_⟩
  have hsub : w '' Ici j ⊆ Metric.ball z ε := by
    rintro _ ⟨i, hi, rfl⟩
    exact hN i (hj.trans hi)
  exact (convexHull_min hsub (convex_ball z ε)) (hz j)

/-- Weak convergence in Lp yields convex combinations of escaping tails with
a subsequence converging almost everywhere to the same weak limit. This applies
to L¹ derivatives as well as to L². It assumes weak convergence, not compactness. -/
theorem exists_ae_tendsto_tail_convex_combinations_of_weak_Lp_tendsto
    {T : Type*} [MeasurableSpace T] {μ : Measure T} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (w : ℕ → Lp F p μ) (z : Lp F p μ)
    (hw : Tendsto (fun j ↦ toWeakSpace ℝ (Lp F p μ) (w j)) atTop
      (𝓝 (toWeakSpace ℝ (Lp F p μ) z))) :
    ∃ (zs : ℕ → Lp F p μ) (k : ℕ → ℕ),
      (∀ j, zs j ∈ convexHull ℝ (w '' Ici j)) ∧ StrictMono k ∧
      ∀ᵐ t ∂μ, Tendsto (fun j ↦ zs (k j) t) atTop (𝓝 (z t)) := by
  obtain ⟨zs, hz, hlim⟩ := exists_tendsto_tail_convex_combinations_of_weak_tendsto w z hw
  obtain ⟨k, hk, hkae⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  exact ⟨zs, k, hz, hk, hkae⟩

/-- Mazur's common finite tail weights, with a.e. velocity convergence, obtained
from weak Lp convergence. The weights depend on the sequence index, not on time. -/
theorem exists_weights_ae_tendsto_of_weak_Lp_tendsto
    {T : Type*} [MeasurableSpace T] {μ : Measure T} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (w : ℕ → Lp F p μ) (z : Lp F p μ)
    (hw : Tendsto (fun j ↦ toWeakSpace ℝ (Lp F p μ) (w j)) atTop
      (𝓝 (toWeakSpace ℝ (Lp F p μ) z))) :
    ∃ (s : ℕ → Finset ℕ) (a : ℕ → ℕ → ℝ),
      (∀ j i, i ∈ s j → 0 ≤ a j i) ∧ (∀ j, ∑ i ∈ s j, a j i = 1) ∧
      (∀ j i, i ∈ s j → j ≤ i) ∧
      ∀ᵐ t ∂μ, Tendsto (fun j ↦ ∑ i ∈ s j, a j i • w i t) atTop (𝓝 (z t)) := by
  obtain ⟨zs, k, hz, hk, hkae⟩ :=
    exists_ae_tendsto_tail_convex_combinations_of_weak_Lp_tendsto w z hw
  have hweights := fun j ↦ exists_weights_of_mem_convexHull_tail w (k j) (zs (k j))
    (hz (k j))
  choose s a ha hsum htail heq using hweights
  refine ⟨s, a, ha, hsum, fun j i hi ↦ (hk.id_le j).trans (htail j i hi), ?_⟩
  have hcoe : ∀ j, (fun t ↦ zs (k j) t) =ᵐ[μ]
      fun t ↦ ∑ i ∈ s j, a j i • w i t := by
    intro j
    rw [← heq j]
    have h := (Lp.coeFn_finsetSum (s j) (fun i ↦ a j i • w i)).trans
      (eventuallyEq_sum fun i _ ↦ Lp.coeFn_smul (a j i) (w i))
    filter_upwards [h] with t ht
    simpa only [Finset.sum_apply, Pi.smul_apply] using ht
  filter_upwards [hkae, ae_all_iff.mpr hcoe] with t ht heqt
  simpa only [heqt] using ht

end Mazur

section Pointwise

variable {T E F : Type*} [PseudoMetricSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Cesari lower closure for limits of moving-tail convex combinations, rather than limits
of the original velocity–cost sequence. No convexity of the original fibers is assumed. -/
theorem mem_of_weakCesariProperty_of_tail_combinations
    (Q : T → E → Set F) (t : T) (x : E) (xs : ℕ → E) (ws zs : ℕ → F) (z : F)
    (hcesari : HasWeakCesariProperty Q t x)
    (hx : Tendsto xs atTop (𝓝 x)) (hw : ∀ i, ws i ∈ Q t (xs i))
    (hz : ∀ j, zs j ∈ convexHull ℝ (ws '' Ici j))
    (hlim : Tendsto zs atTop (𝓝 z)) : z ∈ Q t x := by
  refine mem_of_weakCesariProperty_of_tail_convexHull Q t x xs ws hcesari hx hw z ?_
  intro N
  refine (isClosed_closure).mem_of_tendsto hlim ?_
  filter_upwards [eventually_ge_atTop N] with j hj
  exact subset_closure ((convexHull_mono (image_mono (Ici_subset_Ici.mpr hj))) (hz j))

/-- Cesari lower closure ignores any finite prefix of infeasible epigraph points.
Reindexing the feasible tail reduces this to the existing lower-closure theorem.
This is the eventual membership needed inside a limiting moving time interval. -/
theorem mem_of_weakCesariProperty_of_eventually_mem_of_tail_convexHull
    (Q : T → E → Set F) (t : T) (x : E) (xs : ℕ → E) (ws : ℕ → F) (z : F)
    (hcesari : HasWeakCesariProperty Q t x) (hx : Tendsto xs atTop (𝓝 x))
    (hw : ∀ᶠ i in atTop, ws i ∈ Q t (xs i))
    (hz : ∀ N, z ∈ closure (convexHull ℝ (ws '' Ici N))) : z ∈ Q t x := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hw
  apply mem_of_weakCesariProperty_of_tail_convexHull Q t x
    (fun i ↦ xs (i + N)) (fun i ↦ ws (i + N)) hcesari
    (hx.comp (tendsto_add_atTop_nat N))
    (fun i ↦ hN (i + N) (Nat.le_add_left N i)) z
  intro M
  have himage : (fun i ↦ ws (i + N)) '' Ici M = ws '' Ici (M + N) := by
    ext y
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i + N, Nat.add_le_add_right hi N, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      change M + N ≤ i at hi
      have hNi : N ≤ i := by omega
      refine ⟨i - N, (show M ≤ i - N by omega), ?_⟩
      change ws (i - N + N) = ws i
      rw [Nat.sub_add_cancel hNi]
  rw [himage]
  exact hz (M + N)

/-- Cesari lower closure with epigraph membership only eventually at each time.
The finite infeasible prefix may depend on time. This is the moving-interval
version of BM Theorem 5.4.4, Step 3; property (Q) remains load-bearing. -/
theorem velocityCost_liminf_mem_of_weakCesariProperty_of_eventually_mem
    (Q : T → E → Set (F × ℝ)) (t : T) (x : E) (xs : ℕ → E)
    (ws : ℕ → F × ℝ) (v : ℕ → F) (c : ℕ → ℝ) (vlim : F)
    (hcesari : HasWeakCesariProperty Q t x)
    (hx : Tendsto xs atTop (𝓝 x)) (hw : ∀ᶠ i in atTop, ws i ∈ Q t (xs i))
    (hcombo : ∀ j, (v j, c j) ∈ convexHull ℝ (ws '' Ici j))
    (hv : Tendsto v atTop (𝓝 vlim)) (hc : ∀ j, 0 ≤ c j)
    (hfinite : liminf (fun j ↦ ENNReal.ofReal (c j)) atTop ≠ ∞) :
    (vlim, (liminf (fun j ↦ ENNReal.ofReal (c j)) atTop).toReal) ∈ Q t x := by
  obtain ⟨k, hkcost, hk⟩ :=
    exists_seq_tendsto_liminf (u := fun j ↦ ENNReal.ofReal (c j)) (f := atTop)
  have hcost : Tendsto (fun j ↦ c (k j)) atTop
      (𝓝 (liminf (fun j ↦ ENNReal.ofReal (c j)) atTop).toReal) := by
    simpa only [Function.comp_def, ENNReal.toReal_ofReal (hc _)] using
      (ENNReal.tendsto_toReal hfinite).comp hkcost
  refine mem_of_weakCesariProperty_of_eventually_mem_of_tail_convexHull
    Q t x xs ws _ hcesari hx hw ?_
  intro N
  refine isClosed_closure.mem_of_tendsto ((hv.comp hk).prodMk_nhds hcost) ?_
  filter_upwards [hk.eventually (eventually_ge_atTop N)] with j hj
  exact subset_closure
    ((convexHull_mono (image_mono (Ici_subset_Ici.mpr hj))) (hcombo (k j)))

/-- The pointwise liminf step of Theorem 5.4.4, Step 3. Only the velocity converges;
the nonnegative costs can oscillate or diverge along other subsequences. The finite
cost liminf selects its own subsequence, which still has escaping tail support. -/
theorem velocityCost_liminf_mem_of_weakCesariProperty
    (Q : T → E → Set (F × ℝ)) (t : T) (x : E) (xs : ℕ → E)
    (ws : ℕ → F × ℝ) (v : ℕ → F) (c : ℕ → ℝ) (vlim : F)
    (hcesari : HasWeakCesariProperty Q t x)
    (hx : Tendsto xs atTop (𝓝 x)) (hw : ∀ i, ws i ∈ Q t (xs i))
    (hcombo : ∀ j, (v j, c j) ∈ convexHull ℝ (ws '' Ici j))
    (hv : Tendsto v atTop (𝓝 vlim)) (hc : ∀ j, 0 ≤ c j)
    (hfinite : liminf (fun j ↦ ENNReal.ofReal (c j)) atTop ≠ ∞) :
    (vlim, (liminf (fun j ↦ ENNReal.ofReal (c j)) atTop).toReal) ∈ Q t x := by
  exact velocityCost_liminf_mem_of_weakCesariProperty_of_eventually_mem Q t x xs ws v c vlim
    hcesari hx (Eventually.of_forall hw) hcombo hv hc hfinite

end Pointwise

section Integral

variable {T E F : Type*} [MeasurableSpace T] {μ : Measure T}
  [PseudoMetricSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Cesari lower closure with epigraph membership only eventually at each time.
The finite infeasible prefix may depend on time. This is the moving-interval
version of BM Theorem 5.4.4, Step 3; property (Q) remains load-bearing. -/
theorem ae_velocityCost_liminf_mem_and_lintegral_le_of_eventually_mem
    (Q : T → E → Set (F × ℝ)) (x : T → E) (xs : ℕ → T → E)
    (ws : ℕ → T → F × ℝ) (v : ℕ → T → F) (c : ℕ → T → ℝ) (vlim : T → F)
    (hcesari : ∀ᵐ t ∂μ, HasWeakCesariProperty Q t (x t))
    (hx : ∀ᵐ t ∂μ, Tendsto (fun i ↦ xs i t) atTop (𝓝 (x t)))
    (hw : ∀ᵐ t ∂μ, ∀ᶠ i in atTop, ws i t ∈ Q t (xs i t))
    (hcombo : ∀ j, ∀ᵐ t ∂μ,
      (v j t, c j t) ∈ convexHull ℝ ((fun i ↦ ws i t) '' Ici j))
    (hv : ∀ᵐ t ∂μ, Tendsto (fun j ↦ v j t) atTop (𝓝 (vlim t)))
    (hc : ∀ j, ∀ᵐ t ∂μ, 0 ≤ c j t)
    (hmeas : ∀ j, AEMeasurable (fun t ↦ ENNReal.ofReal (c j t)) μ)
    (B : ℝ≥0∞) (hB : B ≠ ∞)
    (hbound : liminf (fun j ↦ ∫⁻ t, ENNReal.ofReal (c j t) ∂μ) atTop ≤ B) :
    (∀ᵐ t ∂μ,
      (vlim t, (liminf (fun j ↦ ENNReal.ofReal (c j t)) atTop).toReal) ∈ Q t (x t)) ∧
      (∫⁻ t, liminf (fun j ↦ ENNReal.ofReal (c j t)) atTop ∂μ) ≤ B := by
  have hfatou := (lintegral_liminf_le' hmeas).trans hbound
  have hfin := ae_lt_top' (AEMeasurable.liminf hmeas)
    (ne_top_of_le_ne_top hB hfatou)
  refine ⟨?_, hfatou⟩
  filter_upwards [hcesari, hx, hw, ae_all_iff.mpr hcombo,
    hv, ae_all_iff.mpr hc, hfin] with t ht hxt hwt hct hvt hnn hft
  exact velocityCost_liminf_mem_of_weakCesariProperty_of_eventually_mem Q t (x t)
    (fun i ↦ xs i t) (fun i ↦ ws i t) (fun j ↦ v j t) (fun j ↦ c j t)
    (vlim t) ht hxt hwt hct hvt hnn hft.ne

/-- The Cesari–Fatou lower-closure step of Theorem 5.4.4. A finite upper bound on
the liminf of the integral costs ensures the pointwise cost liminf is finite a.e.;
property (Q) then makes the limiting velocity–cost pair feasible a.e.
This conclusion is an epigraph inclusion and a cost bound, not control recovery. -/
theorem ae_velocityCost_liminf_mem_and_lintegral_le
    (Q : T → E → Set (F × ℝ)) (x : T → E) (xs : ℕ → T → E)
    (ws : ℕ → T → F × ℝ) (v : ℕ → T → F) (c : ℕ → T → ℝ) (vlim : T → F)
    (hcesari : ∀ᵐ t ∂μ, HasWeakCesariProperty Q t (x t))
    (hx : ∀ᵐ t ∂μ, Tendsto (fun i ↦ xs i t) atTop (𝓝 (x t)))
    (hw : ∀ i, ∀ᵐ t ∂μ, ws i t ∈ Q t (xs i t))
    (hcombo : ∀ j, ∀ᵐ t ∂μ,
      (v j t, c j t) ∈ convexHull ℝ ((fun i ↦ ws i t) '' Ici j))
    (hv : ∀ᵐ t ∂μ, Tendsto (fun j ↦ v j t) atTop (𝓝 (vlim t)))
    (hc : ∀ j, ∀ᵐ t ∂μ, 0 ≤ c j t)
    (hmeas : ∀ j, AEMeasurable (fun t ↦ ENNReal.ofReal (c j t)) μ)
    (B : ℝ≥0∞) (hB : B ≠ ∞)
    (hbound : liminf (fun j ↦ ∫⁻ t, ENNReal.ofReal (c j t) ∂μ) atTop ≤ B) :
    (∀ᵐ t ∂μ,
      (vlim t, (liminf (fun j ↦ ENNReal.ofReal (c j t)) atTop).toReal) ∈ Q t (x t)) ∧
      (∫⁻ t, liminf (fun j ↦ ENNReal.ofReal (c j t)) atTop ∂μ) ≤ B := by
  apply ae_velocityCost_liminf_mem_and_lintegral_le_of_eventually_mem
    Q x xs ws v c vlim hcesari hx ?_
    hcombo hv hc hmeas B hB hbound
  exact (ae_all_iff.mpr hw).mono fun t ht ↦ Eventually.of_forall ht

/-- Cesari lower closure with epigraph membership only eventually at each time.
The finite infeasible prefix may depend on time. This is the moving-interval
version of BM Theorem 5.4.4, Step 3; property (Q) remains load-bearing. -/
theorem exists_integrable_cost_epigraph_of_cesari_combinations_of_eventually_mem
    (Q : T → E → Set (F × ℝ)) (x : T → E) (xs : ℕ → T → E)
    (w : ℕ → T → F) (c : ℕ → T → ℝ) (vlim : T → F)
    (s : ℕ → Finset ℕ) (a : ℕ → ℕ → ℝ) (γ : ℝ)
    (hcesari : ∀ᵐ t ∂μ, HasWeakCesariProperty Q t (x t))
    (hx : ∀ᵐ t ∂μ, Tendsto (fun i ↦ xs i t) atTop (𝓝 (x t)))
    (hw : ∀ᵐ t ∂μ, ∀ᶠ i in atTop, (w i t, c i t) ∈ Q t (xs i t))
    (hc : ∀ i, ∀ᵐ t ∂μ, 0 ≤ c i t) (hci : ∀ i, Integrable (c i) μ)
    (hcost : Tendsto (fun i ↦ ∫ t, c i t ∂μ) atTop (𝓝 γ))
    (ha : ∀ j i, i ∈ s j → 0 ≤ a j i)
    (hsum : ∀ j, ∑ i ∈ s j, a j i = 1)
    (htail : ∀ j i, i ∈ s j → j ≤ i)
    (hv : ∀ᵐ t ∂μ, Tendsto (fun j ↦ ∑ i ∈ s j, a j i • w i t)
      atTop (𝓝 (vlim t))) :
    ∃ costLimit : T → ℝ, Integrable costLimit μ ∧
      (∀ᵐ t ∂μ, (vlim t, costLimit t) ∈ Q t (x t)) ∧
      (∫ t, costLimit t ∂μ) ≤ γ := by
  let v j t := ∑ i ∈ s j, a j i • w i t
  let d j t := ∑ i ∈ s j, a j i * c i t
  have hdint : ∀ j, Integrable (d j) μ := fun j ↦
    integrable_finsetSum _ fun i _ ↦ (hci i).const_mul (a j i)
  have hdnonneg : ∀ j, ∀ᵐ t ∂μ, 0 ≤ d j t := by
    intro j
    filter_upwards [ae_all_iff.mpr hc] with t ht
    exact Finset.sum_nonneg fun i hi ↦ mul_nonneg (ha j i hi) (ht i)
  have hdformula : ∀ j, (∫ t, d j t ∂μ) = ∑ i ∈ s j, a j i * ∫ t, c i t ∂μ := by
    intro j
    rw [show d j = fun t ↦ ∑ i ∈ s j, a j i * c i t from rfl,
      integral_finsetSum _ (fun i _ ↦ (hci i).const_mul (a j i))]
    simp only [integral_const_mul]
  have hdlim : Tendsto (fun j ↦ ∫ t, d j t ∂μ) atTop (𝓝 γ) := by
    refine tendsto_tail_convex_combinations _ _ γ hcost ?_
    intro j
    rw [hdformula j]
    exact sum_mem_convexHull_tail (fun i ↦ ∫ t, c i t ∂μ) j (s j) (a j)
      (ha j) (hsum j) (htail j)
  have hγ : 0 ≤ γ := ge_of_tendsto hdlim (Eventually.of_forall fun j ↦
    integral_nonneg_of_ae (hdnonneg j))
  have hdmeas : ∀ j, AEMeasurable (fun t ↦ ENNReal.ofReal (d j t)) μ :=
    fun j ↦ (hdint j).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hdbound : liminf (fun j ↦ ∫⁻ t, ENNReal.ofReal (d j t) ∂μ) atTop =
      ENNReal.ofReal γ := by
    have hdl : Tendsto (fun j ↦ ENNReal.ofReal (∫ t, d j t ∂μ)) atTop
        (𝓝 (ENNReal.ofReal γ)) := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hdlim
    have heq : (fun j ↦ ENNReal.ofReal (∫ t, d j t ∂μ)) =
        (fun j ↦ ∫⁻ t, ENNReal.ofReal (d j t) ∂μ) := by
      funext j
      exact ofReal_integral_eq_lintegral_ofReal (hdint j) (hdnonneg j)
    rw [heq] at hdl
    exact hdl.liminf_eq
  have hcombo : ∀ j, ∀ᵐ t ∂μ, (v j t, d j t) ∈
      convexHull ℝ ((fun i ↦ (w i t, c i t)) '' Ici j) := by
    intro j
    filter_upwards [] with t
    convert sum_mem_convexHull_tail (fun i ↦ (w i t, c i t)) j (s j) (a j)
      (ha j) (hsum j) (htail j) using 1
    apply Prod.ext
    · simp [v, Prod.fst_sum]
    · simp [d, Prod.snd_sum]
  obtain ⟨hmem, hfatou⟩ := ae_velocityCost_liminf_mem_and_lintegral_le_of_eventually_mem Q x xs
    (fun i t ↦ (w i t, c i t)) v d vlim hcesari hx hw hcombo hv hdnonneg hdmeas
    (ENNReal.ofReal γ) ENNReal.ofReal_ne_top hdbound.le
  let L t := liminf (fun j ↦ ENNReal.ofReal (d j t)) atTop
  have hLmeas : AEMeasurable L μ := AEMeasurable.liminf hdmeas
  have hLfin : (∫⁻ t, L t ∂μ) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfatou
  have hLae := ae_lt_top' hLmeas hLfin
  refine ⟨fun t ↦ (L t).toReal, integrable_toReal_of_lintegral_ne_top hLmeas hLfin,
    hmem, ?_⟩
  rw [integral_toReal hLmeas hLae]
  simpa only [ENNReal.toReal_ofReal hγ] using
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top hfatou)

/-- The full common-weights Cesari–Fatou step (Theorem 5.4.4, Step 3).
The original costs have minimizing integrals, and the same finite tail weights are
used for velocities and costs. Only the velocity combinations must converge a.e.
The conclusion constructs an integrable feasible cost majorant with no increase
in total cost. Trajectory extraction and measurable control recovery remain separate. -/
theorem exists_integrable_cost_epigraph_of_cesari_combinations
    (Q : T → E → Set (F × ℝ)) (x : T → E) (xs : ℕ → T → E)
    (w : ℕ → T → F) (c : ℕ → T → ℝ) (vlim : T → F)
    (s : ℕ → Finset ℕ) (a : ℕ → ℕ → ℝ) (γ : ℝ)
    (hcesari : ∀ᵐ t ∂μ, HasWeakCesariProperty Q t (x t))
    (hx : ∀ᵐ t ∂μ, Tendsto (fun i ↦ xs i t) atTop (𝓝 (x t)))
    (hw : ∀ i, ∀ᵐ t ∂μ, (w i t, c i t) ∈ Q t (xs i t))
    (hc : ∀ i, ∀ᵐ t ∂μ, 0 ≤ c i t) (hci : ∀ i, Integrable (c i) μ)
    (hcost : Tendsto (fun i ↦ ∫ t, c i t ∂μ) atTop (𝓝 γ))
    (ha : ∀ j i, i ∈ s j → 0 ≤ a j i)
    (hsum : ∀ j, ∑ i ∈ s j, a j i = 1)
    (htail : ∀ j i, i ∈ s j → j ≤ i)
    (hv : ∀ᵐ t ∂μ, Tendsto (fun j ↦ ∑ i ∈ s j, a j i • w i t)
      atTop (𝓝 (vlim t))) :
    ∃ costLimit : T → ℝ, Integrable costLimit μ ∧
      (∀ᵐ t ∂μ, (vlim t, costLimit t) ∈ Q t (x t)) ∧
      (∫ t, costLimit t ∂μ) ≤ γ := by
  apply exists_integrable_cost_epigraph_of_cesari_combinations_of_eventually_mem
    Q x xs w c vlim s a γ
    hcesari hx ?_ hc hci hcost ha hsum htail hv
  exact (ae_all_iff.mpr hw).mono fun t ht ↦ Eventually.of_forall ht

/-- Cesari lower closure with epigraph membership only eventually at each time.
The finite infeasible prefix may depend on time. This is the moving-interval
version of BM Theorem 5.4.4, Step 3; property (Q) remains load-bearing. -/
theorem exists_integrable_cost_epigraph_of_weak_Lp_tendsto_of_eventually_mem
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (Q : T → E → Set (F × ℝ)) (x : T → E) (xs : ℕ → T → E)
    (w : ℕ → Lp F p μ) (c : ℕ → T → ℝ) (vlim : Lp F p μ) (γ : ℝ)
    (hcesari : ∀ᵐ t ∂μ, HasWeakCesariProperty Q t (x t))
    (hx : ∀ᵐ t ∂μ, Tendsto (fun i ↦ xs i t) atTop (𝓝 (x t)))
    (hw : ∀ᵐ t ∂μ, ∀ᶠ i in atTop, (w i t, c i t) ∈ Q t (xs i t))
    (hc : ∀ i, ∀ᵐ t ∂μ, 0 ≤ c i t) (hci : ∀ i, Integrable (c i) μ)
    (hcost : Tendsto (fun i ↦ ∫ t, c i t ∂μ) atTop (𝓝 γ))
    (hweak : Tendsto (fun j ↦ toWeakSpace ℝ (Lp F p μ) (w j)) atTop
      (𝓝 (toWeakSpace ℝ (Lp F p μ) vlim))) :
    ∃ costLimit : T → ℝ, Integrable costLimit μ ∧
      (∀ᵐ t ∂μ, (vlim t, costLimit t) ∈ Q t (x t)) ∧
      (∫ t, costLimit t ∂μ) ≤ γ := by
  obtain ⟨s, a, ha, hsum, htail, hv⟩ :=
    exists_weights_ae_tendsto_of_weak_Lp_tendsto w vlim hweak
  exact exists_integrable_cost_epigraph_of_cesari_combinations_of_eventually_mem
    Q x xs (fun i ↦ w i)
    c vlim s a γ hcesari hx hw hc hci hcost ha hsum htail hv

/-- Cesari integral lower closure from weak Lp velocity convergence and minimizing
cost integrals (Theorem 5.4.4, Step 3, using Lemmas 5.3.6–5.3.7).
The common finite weights and the a.e. velocity convergence are constructed, not
assumed. Property (Q) is used to recover the feasible limiting epigraph point.
This is the analytic lower-closure step; it does not assert trajectory compactness
or measurable realization by a relaxed control. -/
theorem exists_integrable_cost_epigraph_of_weak_Lp_tendsto
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (Q : T → E → Set (F × ℝ)) (x : T → E) (xs : ℕ → T → E)
    (w : ℕ → Lp F p μ) (c : ℕ → T → ℝ) (vlim : Lp F p μ) (γ : ℝ)
    (hcesari : ∀ᵐ t ∂μ, HasWeakCesariProperty Q t (x t))
    (hx : ∀ᵐ t ∂μ, Tendsto (fun i ↦ xs i t) atTop (𝓝 (x t)))
    (hw : ∀ i, ∀ᵐ t ∂μ, (w i t, c i t) ∈ Q t (xs i t))
    (hc : ∀ i, ∀ᵐ t ∂μ, 0 ≤ c i t) (hci : ∀ i, Integrable (c i) μ)
    (hcost : Tendsto (fun i ↦ ∫ t, c i t ∂μ) atTop (𝓝 γ))
    (hweak : Tendsto (fun j ↦ toWeakSpace ℝ (Lp F p μ) (w j)) atTop
      (𝓝 (toWeakSpace ℝ (Lp F p μ) vlim))) :
    ∃ costLimit : T → ℝ, Integrable costLimit μ ∧
      (∀ᵐ t ∂μ, (vlim t, costLimit t) ∈ Q t (x t)) ∧
      (∫ t, costLimit t ∂μ) ≤ γ := by
  apply exists_integrable_cost_epigraph_of_weak_Lp_tendsto_of_eventually_mem Q x xs w c vlim γ
    hcesari hx ?_ hc hci hcost hweak
  exact (ae_all_iff.mpr hw).mono fun t ht ↦ Eventually.of_forall ht

end Integral

end OptimalControl
