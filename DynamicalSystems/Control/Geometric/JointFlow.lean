/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.FlowBox
public import Mathlib.Analysis.Calculus.FDeriv.Partial

/-! # Joint differentiability of the local flow

The time derivative of a local flow is jointly continuous, because the vector
field is continuous and the flow is jointly continuous. Together with spatial
differentiability, this gives differentiability in time and initial condition.
Only the time partial derivative needs to be continuous for this argument.
-/

@[expose] public section

open Set Filter Metric Asymptotics
open scoped Topology

section Partial

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A jointly continuous first partial derivative and a second partial
derivative at the base point give the full derivative there. This is the
ordinary differentiability counterpart of the two-partial strict-derivative
criterion in `Mathlib.Analysis.Calculus.FDeriv.Partial`. -/
theorem hasFDerivAt_uncurry_coprod_of_continuous_left
    {f : E → F → G} {u : E × F} {A : E × F → E →L[ℝ] G} {B : F →L[ℝ] G}
    (hA : ∀ᶠ p in 𝓝 u, HasFDerivAt (fun t ↦ f t p.2) (A p) p.1)
    (hAc : ContinuousAt A u) (hB : HasFDerivAt (f u.1) B u.2) :
    HasFDerivAt (fun p : E × F ↦ f p.1 p.2) ((A u).coprod B) u := by
  have hmap : Tendsto (fun q : (E × F) × E ↦ (q.2, q.1.2))
      (𝓝 u ×ˢ 𝓝 u.1) (𝓝 u) := by
    exact tendsto_snd.prodMk_nhds
      (continuous_snd.continuousAt.tendsto.comp tendsto_fst)
  have hleft : (fun p : E × F ↦ f p.1 p.2 - f u.1 p.2 - A u (p.1 - u.1))
      =o[𝓝 u] (fun p ↦ p.1 - u.1) := by
    rw [isLittleO_iff]
    intro ε hε
    have hder : ∀ᶠ q : (E × F) × E in 𝓝 u ×ˢ 𝓝[univ] u.1,
        HasFDerivAt (fun t ↦ f t q.1.2) (A (q.2, q.1.2)) q.2 := by
      simpa only [nhdsWithin_univ] using hmap.eventually hA
    have hbound : ∀ᶠ q : (E × F) × E in 𝓝 u ×ˢ 𝓝[univ] u.1,
        ‖A (q.2, q.1.2) - A u‖ < ε := by
      have h := (hAc.tendsto.comp hmap).eventually (ball_mem_nhds (A u) hε)
      simpa only [nhdsWithin_univ, mem_ball, dist_eq_norm, Function.comp_def] using h
    have hseg : ∀ᶠ p : E × F in 𝓝 u, segment ℝ u.1 p.1 ⊆ (univ : Set E) :=
      Eventually.of_forall fun _ ↦ subset_univ _
    have hd : ∀ᶠ p : E × F in 𝓝 u, ∀ t ∈ segment ℝ u.1 p.1,
        HasFDerivAt (fun s ↦ f s p.2) (A (t, p.2)) t :=
      hder.segment_of_prod_nhdsWithin tendsto_const_nhds
        continuous_fst.continuousAt.tendsto hseg
    have hb : ∀ᶠ p : E × F in 𝓝 u, ∀ t ∈ segment ℝ u.1 p.1,
        ‖A (t, p.2) - A u‖ < ε :=
      hbound.segment_of_prod_nhdsWithin tendsto_const_nhds
        continuous_fst.continuousAt.tendsto hseg
    filter_upwards [hd, hb] with p hp hb
    exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (fun t ht ↦ (hp t ht).hasFDerivWithinAt) (fun t ht ↦ (hb t ht).le)
      (convex_segment ..) (left_mem_segment ..) (right_mem_segment ..)
  have hright : (fun p : E × F ↦ f u.1 p.2 - f u.1 u.2 - B (p.2 - u.2))
      =o[𝓝 u] (fun p ↦ p.2 - u.2) :=
    hB.isLittleO.comp_tendsto continuous_snd.continuousAt.tendsto
  apply HasFDerivAt.of_isLittleO
  have h := (hleft.trans_isBigO (isBigO_of_le (𝓝 u)
    (fun p ↦ norm_fst_le (p - u)))).add
      (hright.trans_isBigO (isBigO_of_le (𝓝 u) (fun p ↦ norm_snd_le (p - u))))
  convert h using 1
  ext p
  simp only [ContinuousLinearMap.coprod_apply, Prod.fst_sub, Prod.snd_sub]
  abel

end Partial

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [CompleteSpace X] [FiniteDimensional ℝ X]

omit [FiniteDimensional ℝ X] in
/-- The chosen local flow is jointly continuous on its open time and space
domain; uniform spatial Lipschitz continuity supplies the product continuity. -/
theorem localFlow_continuousOn_product {f : X → X} {x₀ : X}
    (hf : ContDiffAt ℝ 1 f x₀) :
    ContinuousOn (fun p : ℝ × X ↦ localFlow hf p.1 p.2)
      (Ioo (-(getLocalFlowData hf).ε) (getLocalFlowData hf).ε ×ˢ
        ball x₀ (getLocalFlowData hf).r) := by
  let d := getLocalFlowData hf
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith' _ d.L'
  · intro t ht
    exact (d.ϕ_lipschitz t (Ioo_subset_Icc_self ht)).mono ball_subset_closedBall
  · intro y hy
    exact HasDerivAt.continuousOn fun t ht ↦
      d.ϕ_hasDerivAt t ht y (ball_subset_closedBall hy)

omit [FiniteDimensional ℝ X] in
/-- Joint continuity holds at every point of a neighborhood of `(0, x₀)`. -/
theorem eventually_continuousAt_localFlow_joint {f : X → X} {x₀ : X}
    (hf : ContDiffAt ℝ 1 f x₀) :
    ∀ᶠ p : ℝ × X in 𝓝 (0, x₀),
      ContinuousAt (fun q : ℝ × X ↦ localFlow hf q.1 q.2) p := by
  let d := getLocalFlowData hf
  have hdomain : Ioo (-d.ε) d.ε ×ˢ ball x₀ d.r ∈ 𝓝 (0, x₀) :=
    prod_mem_nhds (Ioo_mem_nhds (neg_neg_of_pos d.hε) d.hε) (ball_mem_nhds x₀ d.hr)
  filter_upwards [hdomain] with p hp
  exact (localFlow_continuousOn_product hf).continuousAt
    ((isOpen_Ioo.prod isOpen_ball).mem_nhds hp)

/-- The joint derivative of the local flow consists of its spatial derivative
and the vector field as its time derivative, uniformly near `(0, x₀)`. -/
theorem eventually_hasFDerivAt_localFlow_joint {f : X → X} {x₀ : X}
    (hf : ContDiffAt ℝ 1 f x₀) :
    ∀ᶠ p : ℝ × X in 𝓝 (0, x₀),
      HasFDerivAt (fun q : ℝ × X ↦ localFlow hf q.1 q.2)
        ((fderiv ℝ (localFlow hf p.1) p.2).comp (ContinuousLinearMap.snd ℝ ℝ X) +
          (ContinuousLinearMap.fst ℝ ℝ X).smulRight (f (localFlow hf p.1 p.2))) p := by
  have hbase : Tendsto (fun p : ℝ × X ↦ localFlow hf p.1 p.2)
      (𝓝 (0, x₀)) (𝓝 x₀) := by
    have h := (localFlow_continuousAt f x₀ hf).tendsto
    simpa only [localFlow_zero_apply f x₀ hf] using h
  have hregular := hbase.eventually (hf.eventually (by simp))
  filter_upwards [(eventually_hasDerivAt_localFlow_time hf).eventually_nhds,
    eventually_differentiableAt_localFlow_spatial hf,
    eventually_continuousAt_localFlow_joint hf, hregular] with p htime hspace hcont hreg
  let A : ℝ × X → ℝ →L[ℝ] X := fun q ↦
    (1 : ℝ →L[ℝ] ℝ).smulRight (f (localFlow hf q.1 q.2))
  have hA : ∀ᶠ q in 𝓝 p,
      HasFDerivAt (fun t ↦ localFlow hf t q.2) (A q) q.1 := by
    filter_upwards [htime] with q hq using hq.hasFDerivAt
  have hfield : ContinuousAt (fun q : ℝ × X ↦ f (localFlow hf q.1 q.2)) p :=
    hreg.continuousAt.comp (f := fun q : ℝ × X ↦ localFlow hf q.1 q.2) hcont
  have hAc : ContinuousAt A p :=
    (ContinuousLinearMap.smulRightL ℝ ℝ X 1).continuous.continuousAt.comp
      (f := fun q : ℝ × X ↦ f (localFlow hf q.1 q.2)) hfield
  have h := hasFDerivAt_uncurry_coprod_of_continuous_left hA hAc hspace.hasFDerivAt
  convert h using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [A, add_comm]

/-- The fixed local flow is differentiable jointly in time and initial state
throughout a neighborhood of `(0, x₀)`. -/
theorem eventually_differentiableAt_localFlow_joint {f : X → X} {x₀ : X}
    (hf : ContDiffAt ℝ 1 f x₀) :
    ∀ᶠ p : ℝ × X in 𝓝 (0, x₀),
      DifferentiableAt ℝ (fun q : ℝ × X ↦ localFlow hf q.1 q.2) p := by
  filter_upwards [eventually_hasFDerivAt_localFlow_joint hf] with p hp
  exact hp.differentiableAt
