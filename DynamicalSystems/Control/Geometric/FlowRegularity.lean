/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.JointFlow

/-! # Continuous differentiability of local flows

Uniform continuous dependence of linear variational equations on their
coefficients supplies continuity of the spatial flow derivative. This completes
the local `C¹` regularity needed for the usual differential formulation of
simultaneous rectification. The argument is classical; see Hartman, *Ordinary
Differential Equations*, Chapter V, and Sontag, *Mathematical Control Theory*,
Chapter 4, §4.2.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology NNReal

section LinearFamily

variable {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [PseudoMetricSpace Y]

/-- A uniformly bounded family of linear equations has jointly continuous
fundamental solutions when its coefficients vary uniformly continuously in the
parameter. The time interval is fixed before the continuity tolerance. -/
theorem continuousOn_linearODE_family
    {A J : ℝ → Y → E →L[ℝ] E} {U : Set Y} {T K : ℝ}
    (hT : 0 < T) (hK : 0 < K)
    (hzero : ∀ y ∈ U, J 0 y = ContinuousLinearMap.id ℝ E)
    (hderiv : ∀ y ∈ U, ∀ t ∈ Ioo (-T) T,
      HasDerivAt (fun u ↦ J u y) ((A t y).comp (J t y)) t)
    (hbound : ∀ y ∈ U, ∀ t ∈ Ioo (-T) T, ‖A t y‖ ≤ K)
    (hmod : ∀ η > 0, ∃ δ > 0, ∀ y ∈ U, ∀ z ∈ U, dist z y < δ →
      ∀ t ∈ Ioo (-T) T, ‖A t z - A t y‖ ≤ η) :
    ContinuousOn (fun p : ℝ × Y ↦ J p.1 p.2) (Ioo (-T) T ×ˢ U) := by
  obtain ⟨C, hC, hgronwall⟩ :=
    norm_le_mul_of_deriv_le_symmetric (X := E →L[ℝ] E) hT hK
  let I : E →L[ℝ] E := ContinuousLinearMap.id ℝ E
  let M : ℝ := C * (K * ‖I‖) + ‖I‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hJbound : ∀ y ∈ U, ∀ t ∈ Ioo (-T) T, ‖J t y‖ ≤ M := by
    intro y hy t ht
    have he0 : (fun u ↦ J u y - I) 0 = 0 := by simp [I, hzero y hy]
    have he : ∀ u ∈ Ioo (-T) T, HasDerivAt (fun v ↦ J v y - I)
        ((A u y).comp (J u y)) u := by
      intro u hu
      simpa only [sub_zero] using (hderiv y hy u hu).sub_const I
    have hest : ∀ u ∈ Ioo (-T) T,
        ‖(A u y).comp (J u y)‖ ≤ K * ‖J u y - I‖ + K * ‖I‖ := by
      intro u hu
      calc
        ‖(A u y).comp (J u y)‖ ≤ ‖A u y‖ * ‖J u y‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ K * (‖J u y - I‖ + ‖I‖) :=
          mul_le_mul (hbound y hy u hu) (norm_le_norm_sub_add _ _)
            (norm_nonneg _) hK.le
        _ = K * ‖J u y - I‖ + K * ‖I‖ := mul_add _ _ _
    have hb := hgronwall (mul_nonneg hK.le (norm_nonneg I)) he0 he hest t ht
    calc
      ‖J t y‖ ≤ ‖J t y - I‖ + ‖I‖ := norm_le_norm_sub_add _ _
      _ ≤ C * (K * ‖I‖) + ‖I‖ := by linarith
      _ ≤ M := by dsimp [M]; linarith
  have hspace : ∀ t ∈ Ioo (-T) T, UniformContinuousOn (J t) U := by
    intro t ht
    apply uniformContinuousOn_iff.mpr
    intro ε hε
    let η := ε / (2 * C * M)
    have hη : 0 < η := by dsimp [η]; positivity
    obtain ⟨δ, hδ, hδmod⟩ := hmod η hη
    refine ⟨δ, hδ, fun z hz y hy hdist ↦ ?_⟩
    have he0 : (fun u ↦ J u z - J u y) 0 = 0 := by simp [hzero z hz, hzero y hy]
    have he : ∀ u ∈ Ioo (-T) T, HasDerivAt (fun v ↦ J v z - J v y)
        ((A u z).comp (J u z) - (A u y).comp (J u y)) u :=
      fun u hu ↦ (hderiv z hz u hu).sub (hderiv y hy u hu)
    have hest : ∀ u ∈ Ioo (-T) T,
        ‖(A u z).comp (J u z) - (A u y).comp (J u y)‖
          ≤ K * ‖J u z - J u y‖ + η * M := by
      intro u hu
      have heq : (A u z).comp (J u z) - (A u y).comp (J u y) =
          (A u z).comp (J u z - J u y) + (A u z - A u y).comp (J u y) := by
        ext v
        simp only [sub_apply, add_apply,
          ContinuousLinearMap.comp_apply, map_sub]
        abel
      rw [heq]
      calc
        _ ≤ ‖(A u z).comp (J u z - J u y)‖
            + ‖(A u z - A u y).comp (J u y)‖ := norm_add_le _ _
        _ ≤ ‖A u z‖ * ‖J u z - J u y‖ + ‖A u z - A u y‖ * ‖J u y‖ :=
          add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
            (ContinuousLinearMap.opNorm_comp_le _ _)
        _ ≤ K * ‖J u z - J u y‖ + η * M :=
          add_le_add (mul_le_mul_of_nonneg_right (hbound z hz u hu) (norm_nonneg _))
            (mul_le_mul (hδmod y hy z hz hdist u hu) (hJbound y hy u hu)
              (norm_nonneg _) hη.le)
    have hb := hgronwall (mul_nonneg hη.le hM.le) he0 he hest t ht
    rw [dist_eq_norm]
    calc
      ‖J t z - J t y‖ ≤ C * (η * M) := hb
      _ = ε / 2 := by dsimp [η]; field_simp
      _ < ε := by linarith
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ ⟨K * M, mul_nonneg hK.le hM.le⟩
  · exact fun t ht ↦ (hspace t ht).continuousOn
  · intro y hy
    apply (convex_Ioo (-T) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun t ht ↦ (hderiv y hy t ht).hasDerivWithinAt)
    intro t ht
    change ‖(A t y).comp (J t y)‖ ≤ K * M
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hbound y hy t ht) (hJbound y hy t ht) (norm_nonneg _) hK.le)

end LinearFamily

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [CompleteSpace X] [FiniteDimensional ℝ X]

/-- The spatial derivative of a continuously differentiable local flow is
jointly continuous on some product neighbourhood of the initial point. -/
theorem exists_continuousOn_fderiv_localFlow_spatial
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    ∃ T > 0, ∃ r > 0,
      ContinuousOn (fun p : ℝ × X ↦ fderiv ℝ (localFlow hf p.1) p.2)
        (Ioo (-T) T ×ˢ ball x₀ r) := by
  obtain ⟨D⟩ := CommonFlowDomain.nonempty_of_contDiffAt hf hf
  obtain ⟨TJ, hTJ, rJ, hrJ, hmain⟩ := uniformTangentSolution_onBox D
  obtain ⟨TF, hTF, rF, hrF, hstay⟩ := uniformFlowInvariance D
  obtain ⟨C₀, hC₀⟩ := D.uniform_fderiv_bound
  have hC₀nn : 0 ≤ C₀ := (norm_nonneg _).trans
    (hC₀ x₀ (mem_closedBall_self D.hr.le)).1
  let d := getLocalFlowData hf
  let T := min TJ (min TF d.ε)
  let r := min rJ (min rF d.r)
  let K := C₀ + 1
  have hT : 0 < T := lt_min hTJ (lt_min hTF d.hε)
  have hr : 0 < r := lt_min hrJ (lt_min hrF d.hr)
  have hK : 0 < K := by dsimp [K]; linarith
  have hTle : T ≤ TJ ∧ T ≤ TF ∧ T ≤ d.ε := by
    dsimp [T]
    exact ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  have hrle : r ≤ rJ ∧ r ≤ rF ∧ r ≤ d.r := by
    dsimp [r]
    exact ⟨min_le_left _ _, (min_le_right _ _).trans (min_le_left _ _),
      (min_le_right _ _).trans (min_le_right _ _)⟩
  let A : ℝ → X → X →L[ℝ] X := fun t y ↦ fderiv ℝ f (localFlow hf t y)
  let J : ℝ → X → X →L[ℝ] X := fun t y ↦ fderiv ℝ (localFlow hf t) y
  have hzero : ∀ y ∈ ball x₀ r, J 0 y = ContinuousLinearMap.id ℝ X := by
    intro y hy
    obtain ⟨Jy, hJy0, -, hJyident⟩ := hmain y (ball_subset_ball hrle.1 hy)
    exact ((hJyident 0 (by simpa using hTJ)).fderiv).trans hJy0
  have hderiv : ∀ y ∈ ball x₀ r, ∀ t ∈ Ioo (-T) T,
      HasDerivAt (fun u ↦ J u y) ((A t y).comp (J t y)) t := by
    intro y hy t ht
    obtain ⟨Jy, -, hJyode, hJyident⟩ := hmain y (ball_subset_ball hrle.1 hy)
    have htJ : t ∈ Ioo (-TJ) TJ := abs_lt.mp ((abs_lt.mpr ht).trans_le hTle.1)
    have heq : (fun u ↦ J u y) =ᶠ[𝓝 t] Jy := by
      filter_upwards [Ioo_mem_nhds htJ.1 htJ.2] with u hu
      exact (hJyident u (abs_lt.mpr hu)).fderiv
    have h := (hJyode t (abs_lt.mpr htJ)).congr_of_eventuallyEq heq
    rwa [← (hJyident t (abs_lt.mpr htJ)).fderiv] at h
  have hmem : ∀ y ∈ ball x₀ r, ∀ t ∈ Ioo (-T) T,
      localFlow hf t y ∈ closedBall x₀ D.r := by
    intro y hy t ht
    exact (hstay t ((abs_lt.mpr ht).trans_le hTle.2.1) y
      (ball_subset_ball hrle.2.1 hy)).1
  have hbound : ∀ y ∈ ball x₀ r, ∀ t ∈ Ioo (-T) T, ‖A t y‖ ≤ K := by
    intro y hy t ht
    exact ((hC₀ _ (hmem y hy t ht)).1).trans (by dsimp [K]; linarith)
  have hDfcont : ContinuousOn (fderiv ℝ f) (closedBall x₀ D.r) :=
    fun y hy ↦ ((D.hf y hy).continuousAt_fderiv one_ne_zero).continuousWithinAt
  have hDfuc := (isCompact_closedBall x₀ D.r).uniformContinuousOn_of_continuous hDfcont
  have hmod : ∀ η > 0, ∃ δ > 0, ∀ y ∈ ball x₀ r, ∀ z ∈ ball x₀ r,
      dist z y < δ → ∀ t ∈ Ioo (-T) T, ‖A t z - A t y‖ ≤ η := by
    intro η hη
    obtain ⟨δA, hδA, hδmod⟩ := uniformContinuousOn_iff.mp hDfuc η hη
    let L : ℝ := (d.L' : ℝ) + 1
    have hL : 0 < L := by dsimp [L]; positivity
    refine ⟨δA / L, div_pos hδA hL, fun y hy z hz hdist t ht ↦ ?_⟩
    have htime : t ∈ Icc (-d.ε) d.ε :=
      Ioo_subset_Icc_self (abs_lt.mp ((abs_lt.mpr ht).trans_le hTle.2.2))
    have hyball : y ∈ closedBall x₀ d.r :=
      ball_subset_closedBall (ball_subset_ball hrle.2.2 hy)
    have hzball : z ∈ closedBall x₀ d.r :=
      ball_subset_closedBall (ball_subset_ball hrle.2.2 hz)
    have hdistflow : dist (localFlow hf t z) (localFlow hf t y) < δA := by
      calc
        _ ≤ (d.L' : ℝ) * dist z y :=
          (d.ϕ_lipschitz t htime).dist_le_mul z hzball y hyball
        _ ≤ L * dist z y := by
          apply mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) dist_nonneg
        _ < L * (δA / L) := mul_lt_mul_of_pos_left hdist hL
        _ = δA := mul_div_cancel₀ _ hL.ne'
    simpa only [dist_eq_norm] using
      (hδmod _ (hmem z hz t ht) _ (hmem y hy t ht) hdistflow).le
  exact ⟨T, hT, r, hr, continuousOn_linearODE_family hT hK hzero hderiv hbound hmod⟩

/-- The spatial derivative of the fixed local flow is jointly continuous at
every point of a neighbourhood of time zero and the base point. -/
theorem eventually_continuousAt_fderiv_localFlow_spatial
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    ∀ᶠ p : ℝ × X in 𝓝 (0, x₀),
      ContinuousAt (fun q : ℝ × X ↦ fderiv ℝ (localFlow hf q.1) q.2) p := by
  obtain ⟨T, hT, r, hr, hcont⟩ := exists_continuousOn_fderiv_localFlow_spatial hf
  filter_upwards [prod_mem_nhds (Ioo_mem_nhds (neg_neg_of_pos hT) hT)
    (ball_mem_nhds x₀ hr)] with p hp
  exact hcont.continuousAt ((isOpen_Ioo.prod isOpen_ball).mem_nhds hp)

/-- A local flow of a `C¹` vector field is `C¹` jointly in time and initial
state near time zero and its base point. -/
theorem contDiffAt_localFlow_joint
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    ContDiffAt ℝ 1 (fun p : ℝ × X ↦ localFlow hf p.1 p.2) (0, x₀) := by
  let L : ℝ × X → (ℝ × X) →L[ℝ] X := fun p ↦
    (fderiv ℝ (localFlow hf p.1) p.2).comp (ContinuousLinearMap.snd ℝ ℝ X) +
      (ContinuousLinearMap.fst ℝ ℝ X).smulRight (f (localFlow hf p.1 p.2))
  have hbase : Tendsto (fun p : ℝ × X ↦ localFlow hf p.1 p.2)
      (𝓝 (0, x₀)) (𝓝 x₀) := by
    have h := (localFlow_continuousAt f x₀ hf).tendsto
    simpa only [localFlow_zero_apply f x₀ hf] using h
  have hregular := hbase.eventually (hf.eventually (by simp))
  have hL : ∀ᶠ p : ℝ × X in 𝓝 (0, x₀), ContinuousAt L p ∧
      HasFDerivAt (fun q : ℝ × X ↦ localFlow hf q.1 q.2) (L p) p := by
    filter_upwards [eventually_continuousAt_fderiv_localFlow_spatial hf,
      eventually_continuousAt_localFlow_joint hf, hregular,
      eventually_hasFDerivAt_localFlow_joint hf] with p hspace hflow hreg hderiv
    refine ⟨?_, hderiv⟩
    exact (hspace.clm_comp continuousAt_const).add
      ((ContinuousLinearMap.smulRightL ℝ (ℝ × X) X
        (ContinuousLinearMap.fst ℝ ℝ X)).continuous.continuousAt.comp
          (ContinuousAt.comp (f := fun q : ℝ × X ↦ localFlow hf q.1 q.2)
            (x := p) hreg.continuousAt hflow))
  exact contDiffAt_one_iff.mpr ⟨L, _, hL,
    fun _ hp ↦ hp.1.continuousWithinAt, fun _ hp ↦ hp.2⟩

/-- Joint `C¹` regularity holds throughout a neighbourhood of the base point
of the local flow. -/
theorem eventually_contDiffAt_localFlow_joint
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    ∀ᶠ p : ℝ × X in 𝓝 (0, x₀),
      ContDiffAt ℝ 1 (fun q : ℝ × X ↦ localFlow hf q.1 q.2) p :=
  (contDiffAt_localFlow_joint hf).eventually (by simp)
