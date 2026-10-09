/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.MeasureTheory.WeakL2Compactness
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Topology.MetricSpace.Cauchy
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Weak compactness through uniform norm approximation

Uniformly small norm errors allow weakly compact approximations in a Banach space
to produce weak cluster points. This is the truncation mechanism for weak L1
compactness of uniformly integrable derivatives in the Cesari existence argument.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal

namespace DynamicalSystems.WeakL1

section Approximation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A uniform norm bound passes to a weak limit, by weak closedness of convex balls. -/
theorem norm_le_of_weak_tendsto {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → E} {v : E} {C : ℝ}
    (hu : Tendsto (fun i ↦ toWeakSpace ℝ E (u i)) l (𝓝 (toWeakSpace ℝ E v)))
    (hb : ∀ᶠ i in l, ‖u i‖ ≤ C) : ‖v‖ ≤ C := by
  have hclosed : IsClosed (toWeakSpace ℝ E '' Metric.closedBall (0 : E) C) := by
    rw [← closure_eq_iff_isClosed, ← (convex_closedBall (0 : E) C).toWeakSpace_closure ℝ,
      Metric.isClosed_closedBall.closure_eq]
  have hmem := hclosed.mem_of_tendsto hu (hb.mono fun i hi ↦
    ⟨u i, by simpa using hi, rfl⟩)
  obtain ⟨w, hw, heq⟩ := hmem
  have : w = v := (toWeakSpace ℝ E).injective heq
  simpa [this] using hw

/-- A scalar continuous linear observation of a weak cluster point agrees with
the limit of that observation along the entire sequence. -/
theorem dual_apply_eq_of_weak_clusterPoint_of_tendsto (u : ℕ → E) (v : E)
    (hv : ClusterPt (toWeakSpace ℝ E v) (map (fun n ↦ toWeakSpace ℝ E (u n)) atTop))
    (φ : E →L[ℝ] ℝ) (c : ℝ) (hc : Tendsto (fun n ↦ φ (u n)) atTop (𝓝 c)) :
    φ v = c := by
  have hobs : MapClusterPt (φ v) atTop (fun n ↦ φ (u n)) :=
    MapClusterPt.continuousAt_comp (X := WeakSpace ℝ E)
      (WeakBilin.eval_continuous (topDualPairing ℝ E).flip φ).continuousAt hv
  obtain ⟨k, hk, hlim⟩ := hobs.tendsto_subseq
  exact tendsto_nhds_unique hlim (hc.comp hk.tendsto_atTop)

variable [CompleteSpace E]

/-- Uniform norm approximation by weakly compact sets produces a weak cluster
point of any sequence. Compactness of the original sequence is not assumed. -/
theorem exists_weak_clusterPoint_of_uniform_norm_approximation
    (u : ℕ → E) (a : ℕ → ℕ → E) (K : ℕ → Set E) (ε : ℕ → ℝ)
    (hK : ∀ k, IsCompact (toWeakSpace ℝ E '' K k))
    (ha : ∀ k n, a k n ∈ K k)
    (herr : ∀ k n, ‖u n - a k n‖ ≤ ε k)
    (hε : Tendsto ε atTop (𝓝 0)) :
    ∃ v : E, ClusterPt (toWeakSpace ℝ E v) (map (fun n ↦ toWeakSpace ℝ E (u n)) atTop) := by
  classical
  let U := Ultrafilter.of (atTop : Filter ℕ)
  have hlim : ∀ k, ∃ v : E,
      Tendsto (fun n ↦ toWeakSpace ℝ E (a k n)) U (𝓝 (toWeakSpace ℝ E v)) := by
    intro k
    obtain ⟨w, ⟨v, _, rfl⟩, hw⟩ := (hK k).ultrafilter_le_nhds'
      (U.map fun n ↦ toWeakSpace ℝ E (a k n))
      (by change (fun n ↦ toWeakSpace ℝ E (a k n)) ⁻¹' (toWeakSpace ℝ E '' K k) ∈ U
          exact Filter.Eventually.of_forall fun n ↦ ⟨a k n, ha k n, rfl⟩)
    exact ⟨v, hw⟩
  choose v hv using hlim
  have hdist : ∀ k j, ‖v k - v j‖ ≤ ε k + ε j := by
    intro k j
    apply norm_le_of_weak_tendsto (E := E) (u := fun n ↦ a k n - a j n)
      (v := v k - v j) (by simpa only [map_sub] using (hv k).sub (hv j))
    apply Filter.Eventually.of_forall
    intro n
    calc
      ‖a k n - a j n‖ ≤ ‖a k n - u n‖ + ‖u n - a j n‖ := by
        simpa [dist_eq_norm] using dist_triangle (a k n) (u n) (a j n)
      _ ≤ ε k + ε j := by rw [norm_sub_rev]; exact add_le_add (herr k n) (herr j n)
  have hc : CauchySeq v := by
    apply Metric.cauchySeq_iff.mpr
    intro r hr
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hε.eventually (gt_mem_nhds (half_pos hr)))
    refine ⟨N, fun k hk j hj ↦ ?_⟩
    rw [dist_eq_norm]
    exact (hdist k j).trans_lt (by linarith [hN k hk, hN j hj])
  obtain ⟨v₀, hv₀⟩ := cauchySeq_tendsto_of_complete hc
  have hu : Tendsto (fun n ↦ toWeakSpace ℝ E (u n)) U (𝓝 (toWeakSpace ℝ E v₀)) := by
    apply (WeakBilin.tendsto_iff_forall_eval_tendsto (topDualPairing ℝ E).flip
      (separatingDual_iff_injective.mp (inferInstance : SeparatingDual ℝ E))).mpr
    intro φ
    change Tendsto (fun n ↦ φ (u n)) U (𝓝 (φ v₀))
    apply Metric.tendsto_nhds.mpr
    intro r hr
    let d := r / (3 * (‖φ‖ + 1))
    have hd : 0 < d := div_pos hr (by positivity)
    obtain ⟨k, hkε, hkv⟩ := ((hε.eventually (gt_mem_nhds hd)).and
      (hv₀.eventually (Metric.ball_mem_nhds v₀ hd))).exists
    have hscalar := ((WeakBilin.eval_continuous (topDualPairing ℝ E).flip φ).tendsto
      (toWeakSpace ℝ E (v k))).comp (hv k)
    have hev := (Metric.tendsto_nhds.mp hscalar) (r / 3) (by positivity)
    filter_upwards [hev] with n hn
    have h1 : ‖φ (u n) - φ (a k n)‖ ≤ ‖φ‖ * ε k := by
      rw [← map_sub]
      exact (φ.le_opNorm _).trans (mul_le_mul_of_nonneg_left (herr k n) (norm_nonneg _))
    have h3 : ‖φ (v k) - φ v₀‖ ≤ ‖φ‖ * ‖v k - v₀‖ := by
      rw [← map_sub]; exact φ.le_opNorm _
    have hkd : ‖v k - v₀‖ < d := by simpa [Metric.mem_ball, dist_eq_norm] using hkv
    have hdφ : ‖φ‖ * d < r / 3 := by
      have heq : d * (3 * (‖φ‖ + 1)) = r := div_mul_cancel₀ r (by positivity)
      nlinarith [norm_nonneg φ]
    have h1' : ‖φ (u n) - φ (a k n)‖ < r / 3 :=
      h1.trans_lt ((mul_le_mul_of_nonneg_left hkε.le (norm_nonneg _)).trans_lt hdφ)
    have h3' : ‖φ (v k) - φ v₀‖ < r / 3 :=
      h3.trans_lt ((mul_le_mul_of_nonneg_left hkd.le (norm_nonneg _)).trans_lt hdφ)
    change dist (φ (a k n)) (φ (v k)) < r / 3 at hn
    rw [dist_eq_norm] at hn ⊢
    have hb := dist_triangle (φ (u n)) (φ (a k n)) (φ v₀)
    have hb' := dist_triangle (φ (a k n)) (φ (v k)) (φ v₀)
    simp only [dist_eq_norm] at hb hb'
    linarith
  refine ⟨v₀, ?_⟩
  apply ClusterPt.mono ?_ (map_mono (Ultrafilter.of_le atTop))
  exact ClusterPt.of_le_nhds hu

end Approximation

section Inclusion

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The natural continuous linear inclusion from L2 to L1 on a finite measure space. -/
noncomputable def l2ToL1 : Lp E 2 μ →L[ℝ] Lp E 1 μ := by
  have hp : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  let A : Lp E 2 μ →ₗ[ℝ] Lp E 1 μ :=
    { toFun := fun f ↦ ((Lp.memLp f).mono_exponent hp).toLp f
      map_add' := fun f g ↦ by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (f + g)).mono_exponent hp),
          MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent hp),
          MemLp.coeFn_toLp ((Lp.memLp g).mono_exponent hp),
          Lp.coeFn_add f g,
          Lp.coeFn_add (((Lp.memLp f).mono_exponent hp).toLp f)
            (((Lp.memLp g).mono_exponent hp).toLp g)] with x hfg hf hg hsum hsum'
        simpa only [Pi.add_apply] using hfg.trans (hsum.trans (hsum'.trans
          (congrArg₂ (· + ·) hf hg)).symm)
      map_smul' := fun c f ↦ by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp ((Lp.memLp (c • f)).mono_exponent hp),
          MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent hp),
          Lp.coeFn_smul c f,
          Lp.coeFn_smul c (((Lp.memLp f).mono_exponent hp).toLp f)]
          with x hcf hf hsmul hsmul'
        simpa only [Pi.smul_apply, RingHom.id_apply] using hcf.trans (hsmul.trans
          (hsmul'.trans (congrArg (c • ·) hf)).symm) }
  refine A.mkContinuous ((μ univ ^ (1 / 2 : ℝ)).toReal) fun f ↦ ?_
  change ‖((Lp.memLp f).mono_exponent hp).toLp f‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def, mul_comm]
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    hp (Lp.aestronglyMeasurable f)
  norm_num at h
  simpa only [ENNReal.toReal_mul] using ENNReal.toReal_mono (by finiteness) h

/-- The L2 to L1 inclusion preserves the function almost everywhere. -/
theorem l2ToL1_coeFn (f : Lp E 2 μ) : l2ToL1 f =ᵐ[μ] f :=
  MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2))

end Inclusion

section HilbertInclusion

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The L2 to L1 inclusion sends weakly compact Hilbert balls to weakly compact L1 sets. -/
theorem isCompact_weak_l2ToL1_closedBall
    (r : ℝ) :
    IsCompact (toWeakSpace ℝ (Lp E 1 μ) ''
      (l2ToL1 (μ := μ) '' Metric.closedBall (0 : Lp E 2 μ) r)) := by
  let A := l2ToL1 (μ := μ) (E := E)
  have hc : Continuous (fun x : WeakSpace ℝ (Lp E 2 μ) ↦
      toWeakSpace ℝ (Lp E 1 μ) (A ((toWeakSpace ℝ (Lp E 2 μ)).symm x))) :=
    WeakBilin.continuous_of_continuous_eval _ fun φ ↦
      WeakBilin.eval_continuous (topDualPairing ℝ (Lp E 2 μ)).flip (φ.comp A)
  simpa only [image_image, LinearEquiv.symm_apply_apply] using
    (WeakL2.isCompact_toWeakSpace_image_closedBall (Lp E 2 μ) r).image hc

end HilbertInclusion

section UniformIntegrability

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Uniformly integrable L1 sequences have weak L1 cluster points on finite measure
spaces. No L2 bound on the original sequence is required: truncations provide
weakly compact approximations with uniformly vanishing L1 errors. This is the
Dunford–Pettis compactness mechanism needed in BM Theorem 5.4.4, Step 1. -/
theorem exists_weak_L1_clusterPoint_of_uniformIntegrable (u : ℕ → Lp E 1 μ)
    (hUI : UniformIntegrable (fun n x ↦ u n x) 1 μ) :
    ∃ v : Lp E 1 μ, ClusterPt (toWeakSpace ℝ (Lp E 1 μ) v)
      (map (fun n ↦ toWeakSpace ℝ (Lp E 1 μ) (u n)) atTop) := by
  classical
  let ε (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)
  have hεpos : ∀ k, 0 < ε k := fun k ↦ by dsimp [ε]; positivity
  have htail : ∀ k, ∃ C : ℝ≥0, ∀ n,
      eLpNorm ({x | C ≤ ‖u n x‖₊}.indicator (u n)) 1 μ ≤ ENNReal.ofReal (ε k) :=
    fun k ↦ hUI.spec (by norm_num) (by norm_num)
      (ENNReal.ofReal_pos.mpr (hεpos k))
  choose C hC using htail
  let g k n := {x | ‖u n x‖₊ < C k}.indicator (u n)
  have hgmeas : ∀ k n, AEStronglyMeasurable (g k n) μ := fun k n ↦
    ((Lp.stronglyMeasurable (u n)).indicator
      ((Lp.stronglyMeasurable (u n)).nnnorm.measurableSet_lt
        stronglyMeasurable_const)).aestronglyMeasurable
  have hgbound : ∀ k n x, ‖g k n x‖ ≤ (C k : ℝ) := by
    intro k n x
    by_cases hx : ‖u n x‖₊ < C k
    · simpa [g, hx] using (show (‖u n x‖₊ : ℝ) ≤ C k from
        NNReal.coe_le_coe.mpr hx.le)
    · simp [g, hx]
  have hg : ∀ k n, MemLp (g k n) 2 μ := fun k n ↦
    MemLp.of_bound (hgmeas k n) (C k) (.of_forall (hgbound k n))
  let b k n := (hg k n).toLp (g k n)
  let R k : ℝ := (measureUnivNNReal μ : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹ * C k
  have hb : ∀ k n, b k n ∈ Metric.closedBall (0 : Lp E 2 μ) (R k) := by
    intro k n
    simp only [Metric.mem_closedBall, dist_zero_right]
    apply Lp.norm_le_of_ae_bound (C k).coe_nonneg
    filter_upwards [MemLp.coeFn_toLp (hg k n)] with x hx
    rw [hx]
    exact hgbound k n x
  have herr : ∀ k n, ‖u n - l2ToL1 (b k n)‖ ≤ ε k := by
    intro k n
    have heq : (u n - l2ToL1 (b k n) : Lp E 1 μ) =ᵐ[μ]
        {x | C k ≤ ‖u n x‖₊}.indicator (u n) := by
      filter_upwards [Lp.coeFn_sub (u n) (l2ToL1 (b k n)),
        l2ToL1_coeFn (b k n), MemLp.coeFn_toLp (hg k n)] with x hsub hinc hbx
      rw [hsub, Pi.sub_apply, hinc, hbx]
      by_cases hx : ‖u n x‖₊ < C k
      · simp [g, hx, not_le.mpr hx]
      · simp [g, hx, le_of_not_gt hx]
    rw [Lp.norm_def, eLpNorm_congr_ae heq]
    simpa only [ENNReal.toReal_ofReal (hεpos k).le] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hC k n)
  exact exists_weak_clusterPoint_of_uniform_norm_approximation u
    (fun k n ↦ l2ToL1 (b k n))
    (fun k ↦ l2ToL1 '' Metric.closedBall (0 : Lp E 2 μ) (R k)) ε
    (fun k ↦ isCompact_weak_l2ToL1_closedBall (R k))
    (fun k n ↦ ⟨b k n, hb k n, rfl⟩) herr
    tendsto_one_div_add_atTop_nhds_zero_nat

end UniformIntegrability

end DynamicalSystems.WeakL1
