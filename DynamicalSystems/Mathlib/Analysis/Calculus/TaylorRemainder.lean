/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.Asymptotics.Uniform
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Taylor remainder estimates

The actual spatial Taylor error of a function along a segment, its derivative
and Lipschitz bounds, and uniform estimates along a compact reference graph.
These are generic calculus statements; no control-theoretic data appears.
-/

@[expose] public section

open Set Filter MeasureTheory Asymptotics
open scoped Topology Interval


section Normed

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The actual spatial error after subtracting the proposed linearization. -/
def taylorError (F : E → G) (A : E →L[ℝ] G) (x y : E) : G :=
  F y - F x - A (y - x)

/-- A spatial derivative modulus on the actual segment gives a Taylor bound.
The derivative at intermediate points is supplied and checked through
`HasFDerivAt`; no Taylor _root_.needleCostRemainder estimate is assumed. -/
theorem norm_taylorError_le_of_derivative_bound
    {F : E → G} {D : E → E →L[ℝ] G} {A : E →L[ℝ] G} {x y : E} {b : ℝ}
    (hD : ∀ z ∈ segment ℝ x y, HasFDerivAt F (D z) z)
    (hbound : ∀ z ∈ segment ℝ x y, ‖D z - A‖ ≤ b) :
    ‖taylorError F A x y‖ ≤ b * ‖y - x‖ := by
  have h := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun z => F z - A z) (f' := fun z => D z - A)
    (fun z hz => ((hD z hz).sub A.hasFDerivAt).hasFDerivWithinAt)
    hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [taylorError, map_sub, sub_sub_sub_comm] using h

/-- A Lipschitz bound for the spatial derivative gives a quadratic error.
The non-sharp constant avoids needing a Taylor integral formula. -/
theorem norm_taylorError_le_quadratic
    {F : E → G} {D : E → E →L[ℝ] G} {x y : E} {B : ℝ}
    (hB : 0 ≤ B)
    (hD : ∀ z ∈ segment ℝ x y, HasFDerivAt F (D z) z)
    (hLip : ∀ z ∈ segment ℝ x y, ‖D z - D x‖ ≤ B * ‖z - x‖) :
    ‖taylorError F (D x) x y‖ ≤ B * ‖y - x‖ ^ 2 := by
  have h := norm_taylorError_le_of_derivative_bound hD
    (b := B * ‖y - x‖) (fun z hz => (hLip z hz).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hB))
  convert h using 1
  ring

/-- Spatial Taylor's estimate uniformly along a compact reference graph.
Only continuity at the graph points is required of the derivative; the
nearby evaluation points need not belong to the graph or a compact tube. -/
theorem uniform_taylorError_near_reference
    {F : ℝ → E → G} {D : ℝ → E → E →L[ℝ] G} {x : ℝ → E}
    {a b : ℝ}
    (hx : ContinuousOn x (Icc a b))
    (hD : ∀ t ∈ Icc a b, ∀ y, HasFDerivAt (F t) (D t y) y)
    (hDc : ∀ t ∈ Icc a b, ContinuousAt (fun q : ℝ × E => D q.1 q.2) (t, x t))
    {η : ℝ} (hη : 0 < η) :
    ∃ δ > 0, ∀ t ∈ Icc a b, ∀ y, ‖y - x t‖ < δ →
      ‖taylorError (F t) (D t (x t)) (x t) y‖ ≤ η * ‖y - x t‖ := by
  let K : Set (ℝ × E) := (fun t => (t, x t)) '' Icc a b
  have hK : IsCompact K :=
    isCompact_Icc.image_of_continuousOn (continuousOn_id.prodMk hx)
  have hcont : ∀ q ∈ K, ContinuousAt (fun q : ℝ × E => D q.1 q.2) q := by
    rintro q ⟨t, ht, rfl⟩
    exact hDc t ht
  have hunif := hK.uniformContinuousAt_of_continuousAt
    (fun q : ℝ × E => D q.1 q.2) hcont (Metric.dist_mem_uniformity hη)
  obtain ⟨δ, hδ, hclose⟩ := Metric.mem_uniformity_dist.mp hunif
  refine ⟨δ, hδ, fun t ht y hy => ?_⟩
  apply norm_taylorError_le_of_derivative_bound (fun z _ => hD t ht z)
  intro z hz
  have hzclose : dist (t, x t) (t, z) < δ := by
    rw [dist_prod_same_left, dist_eq_norm, norm_sub_rev]
    exact (norm_sub_le_of_mem_segment hz).trans_lt hy
  have hh := hclose hzclose (show (t, x t) ∈ K from ⟨t, ht, rfl⟩)
  change dist (D t (x t)) (D t z) < η at hh
  rw [dist_eq_norm, norm_sub_rev] at hh
  exact hh.le


/-- Continuous spatial derivatives along the compact reference graph give a
uniform local Lipschitz increment bound, without any global Lipschitz premise. -/
theorem exists_uniform_increment_bound_near_reference
    {F : ℝ → E → G} {D : ℝ → E → E →L[ℝ] G} {x : ℝ → E} {a b : ℝ}
    (hx : ContinuousOn x (Icc a b))
    (hD : ∀ t ∈ Icc a b, ∀ z, HasFDerivAt (F t) (D t z) z)
    (hDc : ∀ t ∈ Icc a b, ContinuousAt (fun q : ℝ × E => D q.1 q.2) (t, x t)) :
    ∃ δ > 0, ∃ M ≥ 0, ∀ t ∈ Icc a b, ∀ y, ‖y - x t‖ < δ →
      ‖F t y - F t (x t)‖ ≤ M * ‖y - x t‖ := by
  obtain ⟨δ, hδ, hTaylor⟩ := uniform_taylorError_near_reference hx hD hDc zero_lt_one
  have hDpath : ContinuousOn (fun t => D t (x t)) (Icc a b) := by
    intro t ht
    exact (hDc t ht).comp_continuousWithinAt (f := fun r : ℝ => (r, x r))
      (continuousWithinAt_id.prodMk (hx t ht))
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hDpath
  refine ⟨δ, hδ, max B 0 + 1, by positivity, fun t ht y hy => ?_⟩
  calc
    ‖F t y - F t (x t)‖ =
        ‖taylorError (F t) (D t (x t)) (x t) y + D t (x t) (y - x t)‖ := by
      rw [taylorError, sub_add_cancel]
    _ ≤ ‖taylorError (F t) (D t (x t)) (x t) y‖ + ‖D t (x t) (y - x t)‖ :=
      norm_add_le _ _
    _ ≤ 1 * ‖y - x t‖ + max B 0 * ‖y - x t‖ := by
      apply add_le_add (hTaylor t ht y hy)
      exact (D t (x t)).le_opNorm (y - x t) |>.trans
        (mul_le_mul_of_nonneg_right ((hB t ht).trans (le_max_left _ _)) (norm_nonneg _))
    _ = (max B 0 + 1) * ‖y - x t‖ := by ring

/-- Actual `O(ε)` displacements eventually lie in the derived local Lipschitz
neighborhood; their nonlinear function increments are uniformly `O(ε)`. -/
theorem exists_eventually_increment_le_linear
    {F : ℝ → E → G} {D : ℝ → E → E →L[ℝ] G}
    {x : ℝ → E} {y : ℝ → ℝ → E} {a b C : ℝ}
    (hC : 0 ≤ C)
    (hx : ContinuousOn x (Icc a b))
    (hD : ∀ t ∈ Icc a b, ∀ z, HasFDerivAt (F t) (D t z) z)
    (hDc : ∀ t ∈ Icc a b, ContinuousAt (fun q : ℝ × E => D q.1 q.2) (t, x t))
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc a b, ‖y ε t - x t‖ ≤ C * ε) :
    ∃ B ≥ 0, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc a b,
      ‖F t (y ε t) - F t (x t)‖ ≤ B * ε := by
  obtain ⟨δ, hδ, M, hM, hlocal⟩ :=
    exists_uniform_increment_bound_near_reference hx hD hDc
  have hεsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), C * ε < δ := by
    have ht : Tendsto (fun ε : ℝ => C * ε) (𝓝[>] 0) (𝓝 0) := by
      simpa using tendsto_const_nhds.mul
        (tendsto_id.mono_left nhdsWithin_le_nhds :
          Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
    exact ht.eventually (gt_mem_nhds hδ)
  refine ⟨M * C, mul_nonneg hM hC, ?_⟩
  filter_upwards [hbound, hεsmall] with ε hε heδ
  intro t ht
  calc
    _ ≤ M * ‖y ε t - x t‖ := hlocal t ht (y ε t) ((hε t ht).trans_lt heδ)
    _ ≤ M * (C * ε) := mul_le_mul_of_nonneg_left (hε t ht) hM
    _ = (M * C) * ε := by ring

/-- Uniform `O(ε)` trajectory displacement makes the actual nominal Taylor
error uniformly `o(ε)`, using only the continuous spatial derivative. -/
theorem uniformSmall_taylorError
    {F : ℝ → E → G} {D : ℝ → E → E →L[ℝ] G}
    {x : ℝ → E} {y : ℝ → ℝ → E} {a b C : ℝ}
    (hC : 0 ≤ C)
    (hx : ContinuousOn x (Icc a b))
    (hD : ∀ t ∈ Icc a b, ∀ z, HasFDerivAt (F t) (D t z) z)
    (hDc : ∀ t ∈ Icc a b, ContinuousAt (fun q : ℝ × E => D q.1 q.2) (t, x t))
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc a b, ‖y ε t - x t‖ ≤ C * ε) :
    UniformSmall (fun ε t => taylorError (F t) (D t (x t)) (x t) (y ε t))
      (Icc a b) := by
  intro η hη
  have hCp : 0 < C + 1 := by linarith
  obtain ⟨δ, hδ, hTaylor⟩ := uniform_taylorError_near_reference hx hD hDc
    (div_pos hη hCp)
  have hεsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), C * ε < δ := by
    have ht : Tendsto (fun ε : ℝ => C * ε) (𝓝[>] 0) (𝓝 0) := by
      simpa using tendsto_const_nhds.mul
        (tendsto_id.mono_left nhdsWithin_le_nhds :
          Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
    exact ht.eventually (gt_mem_nhds hδ)
  filter_upwards [hbound, hεsmall, self_mem_nhdsWithin] with ε hε hsmall hpos
  intro t ht
  have hεpos : 0 < ε := hpos
  calc
    _ ≤ (η / (C + 1)) * ‖y ε t - x t‖ :=
      hTaylor t ht (y ε t) ((hε t ht).trans_lt hsmall)
    _ ≤ (η / (C + 1)) * (C * ε) :=
      mul_le_mul_of_nonneg_left (hε t ht) (div_nonneg hη.le hCp.le)
    _ ≤ η * ε := by
      have hcfrac : C / (C + 1) ≤ 1 := (div_le_one hCp).mpr (by linarith)
      calc
        _ = (η * ε) * (C / (C + 1)) := by ring
        _ ≤ (η * ε) * 1 := mul_le_mul_of_nonneg_left hcfrac (by positivity)
        _ = _ := mul_one _

end Normed


section Terminal

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Terminal Taylor error needs only Fréchet differentiability at the
reference endpoint, together with an actual `O(ε)` endpoint displacement. -/
theorem tendsto_scaled_terminal_taylorError
    {K : E → G} {k : E →L[ℝ] G} {x : E} {y : ℝ → E} {C : ℝ}
    (hK : HasFDerivAt K k x)
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖y ε - x‖ ≤ C * ε) :
    Tendsto (fun ε : ℝ => ε⁻¹ • taylorError K k x (y ε)) (𝓝[>] 0) (𝓝 0) := by
  have ht : Tendsto (fun ε : ℝ => C * ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
  have hd : Tendsto (fun ε => y ε - x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound ht)
  have hy : Tendsto y (𝓝[>] (0 : ℝ)) (𝓝 x) := by
    simpa only [sub_add_cancel, zero_add] using hd.add_const x
  have hbig : (fun ε => y ε - x) =O[𝓝[>] (0 : ℝ)] (fun ε : ℝ => ε) := by
    apply IsBigO.of_bound C
    filter_upwards [hbound, self_mem_nhdsWithin] with ε hε hpos
    simpa only [Real.norm_eq_abs, abs_of_pos (show 0 < ε from hpos)] using hε
  exact ((hK.isLittleO.comp_tendsto hy).trans_isBigO hbig).tendsto_inv_smul_nhds_zero

end Terminal
