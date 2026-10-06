/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.MeasureTheory.PositiveFunctionalMeasure
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Necessary measure multipliers for continuous path constraints

An actual optimum of a convex problem with continuous, pointwise-convex path
constraints produces a finite nonnegative measure and a nonnegative cost
multiplier. The path-constraint upper image has nonempty interior because of
strict slack, even though its ambient space is infinite-dimensional. Separation
and Riesz representation are therefore applicable without a supplied separator,
measure, Lagrangian minimum, or constraint qualification.

The cost multiplier is not normalized and may vanish. Complementarity is both
an integral identity and concentration of the measure on active constraints.
The index space can include finitely many constraint channels as a product.
-/

@[expose] public section

open Set Filter MeasureTheory

namespace OptimalControl

variable {X S : Type*} [AddCommGroup X] [Module ℝ X]
  [TopologicalSpace S] [CompactSpace S] [T2Space S]

/-- Achievable path-constraint/cost upper image at the reference decision. -/
def pathCostUpperImage (D : Set X) (G : X → C(S, ℝ)) (J : X → ℝ) (u : X) :
    Set (C(S, ℝ) × ℝ) :=
  {z | ∃ v ∈ D, G v ≤ z.1 ∧ J v - J u ≤ z.2}

omit [CompactSpace S] [T2Space S] in
/-- Convexity of the upper image follows from the actual convex objective and
pointwise convex constraint functions. -/
theorem convex_pathCostUpperImage (D : Set X) (G : X → C(S, ℝ)) (J : X → ℝ)
    (hJ : ConvexOn ℝ D J) (hG : ∀ t, ConvexOn ℝ D (fun v => G v t)) (u : X) :
    Convex ℝ (pathCostUpperImage D G J u) := by
  rintro x ⟨v, hv, hxG, hxJ⟩ y ⟨w, hw, hyG, hyJ⟩ a b ha hb hab
  refine ⟨a • v + b • w, hJ.1 hv hw ha hb hab, ?_, ?_⟩
  · intro t
    exact ((hG t).2 hv hw ha hb hab).trans
      (add_le_add (mul_le_mul_of_nonneg_left (hxG t) ha)
        (mul_le_mul_of_nonneg_left (hyG t) hb))
  · have hj := hJ.2 hv hw ha hb hab
    change _ ≤ a * x.2 + b * y.2
    change J (a • v + b • w) ≤ a * J v + b * J w at hj
    have he : a * J u + b * J u = J u := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hxJ), mul_nonneg hb (sub_nonneg.mpr hyJ)]

omit [AddCommGroup X] [Module ℝ X] [T2Space S] in
/-- Positive path and cost slacks construct an actual interior point. No
finite-dimensionality hypothesis on the path space is used. -/
theorem interior_pathCostUpperImage_nonempty (D : Set X) (G : X → C(S, ℝ))
    (J : X → ℝ) (u : X) (hu : u ∈ D) :
    (interior (pathCostUpperImage D G J u)).Nonempty := by
  let z : C(S, ℝ) × ℝ := (G u + ContinuousMap.const S 1, 1)
  refine ⟨z, mem_interior_iff_mem_nhds.mpr ?_⟩
  apply Metric.mem_nhds_iff.mpr
  refine ⟨1 / 2, by norm_num, ?_⟩
  intro w hw
  rw [Metric.mem_ball, dist_eq_norm, Prod.norm_def] at hw
  have hGnorm := (max_lt_iff.mp hw).1
  have hJnorm := (max_lt_iff.mp hw).2
  refine ⟨u, hu, ?_, ?_⟩
  · intro t
    have ht := (w.1 - z.1).norm_coe_le_norm t
    have ht' : |w.1 t - (G u t + 1)| < 1 / 2 := by
      exact lt_of_le_of_lt ht hGnorm
    have hlo := (abs_lt.mp ht').1
    change G u t ≤ w.1 t
    linarith
  · have hlo : -(1 / 2 : ℝ) < w.2 - 1 := (abs_lt.mp hJnorm).1
    linarith

omit [AddCommGroup X] [Module ℝ X] [T2Space S] in
/-- A strictly negative vertical perturbation would be a feasible strict
improvement, so actual constrained optimality puts zero outside the interior. -/
theorem zero_notMem_interior_pathCostUpperImage (D : Set X) (G : X → C(S, ℝ))
    (J : X → ℝ) (u : X)
    (hopt : ∀ v ∈ D, G v ≤ 0 → J u ≤ J v) :
    (0 : C(S, ℝ) × ℝ) ∉ interior (pathCostUpperImage D G J u) := by
  intro hi
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hi)
  have hm : ((0 : C(S, ℝ)), -ε / 2) ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def]
    simp only [norm_zero, Real.norm_eq_abs]
    rw [abs_of_neg (by linarith : -ε / 2 < 0)]
    simp only [neg_div, neg_neg]
    exact max_lt hε (by linarith)
  obtain ⟨v, hv, hGv, hJv⟩ := hball hm
  have ho := hopt v hv hGv
  change J v - J u ≤ -ε / 2 at hJv
  linarith

omit [T2Space S] in
/-- A nontrivial positive path functional and nonnegative cost multiplier are
constructed from actual constrained optimality. The multiplier can be abnormal. -/
theorem exists_path_functional_multipliers (D : Set X) (G : X → C(S, ℝ)) (J : X → ℝ)
    (hJ : ConvexOn ℝ D J) (hG : ∀ t, ConvexOn ℝ D (fun v => G v t))
    (u : X) (hu : u ∈ D) (hGu : G u ≤ 0)
    (hopt : ∀ v ∈ D, G v ≤ 0 → J u ≤ J v) :
    ∃ (q : C(S, ℝ) →L[ℝ] ℝ) (α : ℝ),
      (∀ f, 0 ≤ f → 0 ≤ q f) ∧ 0 ≤ α ∧ (q ≠ 0 ∨ α ≠ 0) ∧
      q (G u) = 0 ∧ ∀ v ∈ D, α * J u ≤ α * J v + q (G v) := by
  obtain ⟨f, hf, hs⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (convex_pathCostUpperImage D G J hJ hG u)
    (zero_notMem_interior_pathCostUpperImage D G J u hopt)
    (interior_pathCostUpperImage_nonempty D G J u hu)
  let F := -f
  have hF : F ≠ 0 := neg_ne_zero.mpr hf
  have hsupport : ∀ z ∈ pathCostUpperImage D G J u, 0 ≤ F z := by
    intro z hz
    have h := hs z hz
    simpa only [map_zero, F, neg_apply, neg_nonneg] using h
  let q : C(S, ℝ) →L[ℝ] ℝ := F.comp (ContinuousLinearMap.inl ℝ C(S, ℝ) ℝ)
  let α : ℝ := F (0, 1)
  have hdecomp : ∀ z : C(S, ℝ) × ℝ, F z = q z.1 + α * z.2 := by
    intro z
    have he : z = (z.1, 0) + z.2 • ((0 : C(S, ℝ)), (1 : ℝ)) := by ext <;> simp
    calc
      F z = F ((z.1, 0) + z.2 • ((0 : C(S, ℝ)), (1 : ℝ))) := congrArg F he
      _ = _ := by
        rw [map_add, map_smul]
        change q z.1 + z.2 * α = q z.1 + α * z.2
        ring
  have hq : ∀ g : C(S, ℝ), 0 ≤ g → 0 ≤ q g := by
    intro g hg
    have hs := hsupport (g, 0) ⟨u, hu, hGu.trans hg, by simp⟩
    simpa only [hdecomp, mul_zero, add_zero] using hs
  have hα : 0 ≤ α := by
    have hs := hsupport (0, 1) ⟨u, hu, hGu, by simp⟩
    simpa only [hdecomp, map_zero, mul_one, zero_add] using hs
  have hcomp : q (G u) = 0 := by
    have hlo := hsupport (G u, 0) ⟨u, hu, le_rfl, by simp⟩
    have hup := hq (-G u) (fun t => neg_nonneg.mpr (hGu t))
    simp only [hdecomp, mul_zero, add_zero] at hlo
    simp only [map_neg, neg_nonneg] at hup
    exact le_antisymm hup hlo
  refine ⟨q, α, hq, hα, ?_, hcomp, ?_⟩
  · by_contra hn
    push Not at hn
    apply hF
    apply ContinuousLinearMap.ext
    intro z
    change F z = 0
    rw [hdecomp, hn.1, hn.2]
    simp
  · intro v hv
    have hs := hsupport (G v, J v - J u) ⟨v, hv, le_rfl, le_rfl⟩
    rw [hdecomp] at hs
    nlinarith

variable [MeasurableSpace S] [BorelSpace S]

/-- **Necessary finite measure multipliers for continuous path constraints.**
The conclusion includes genuine nontriviality, integral complementarity,
concentration on the active set, and a global Lagrangian minimum. The measure
and multiplier are derived; no Slater condition or normality is assumed. -/
theorem exists_path_measure_multipliers (D : Set X) (G : X → C(S, ℝ)) (J : X → ℝ)
    (hJ : ConvexOn ℝ D J) (hG : ∀ t, ConvexOn ℝ D (fun v => G v t))
    (u : X) (hu : u ∈ D) (hGu : G u ≤ 0)
    (hopt : ∀ v ∈ D, G v ≤ 0 → J u ≤ J v) :
    ∃ (μ : Measure S) (α : ℝ), IsFiniteMeasure μ ∧ 0 ≤ α ∧ (μ ≠ 0 ∨ α ≠ 0) ∧
      (∫ t, G u t ∂μ) = 0 ∧ μ {t | G u t < 0} = 0 ∧
      ∀ v ∈ D, α * J u ≤ α * J v + ∫ t, G v t ∂μ := by
  obtain ⟨q, α, hq, hα, hne, hcomp, hmin⟩ :=
    exists_path_functional_multipliers D G J hJ hG u hu hGu hopt
  let μ := q.positiveRepresentingMeasure hq
  have hi : ∀ g : C(S, ℝ), (∫ t, g t ∂μ) = q g := q.integral_positiveRepresentingMeasure hq
  have hc : (∫ t, G u t ∂μ) = 0 := (hi (G u)).trans hcomp
  have hneg : (fun t => -(G u t)) =ᵐ[μ] 0 := by
    apply (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun t => neg_nonneg.mpr (hGu t))
      ((G u).continuous.neg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).mp
    rw [integral_neg]
    change -(∫ t, G u t ∂μ) = 0
    rw [hc, neg_zero]
  refine ⟨μ, α, inferInstance, hα, ?_, hc, ?_, ?_⟩
  · exact hne.imp (q.positiveRepresentingMeasure_ne_zero hq) id
  · apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hneg] with t ht
    have hz : G u t = 0 := neg_eq_zero.mp ht
    simp [hz]
  · intro v hv
    rw [hi]
    exact hmin v hv

omit [AddCommGroup X] [Module ℝ X] [T2Space S] in
/-- Strict feasibility forces every nontrivial multiplier pair satisfying the
Lagrangian inequality to be normal. No division is performed before positivity
has been established. -/
theorem path_costMultiplier_pos_of_slater (D : Set X) (G : X → C(S, ℝ)) (J : X → ℝ)
    (u : X) (μ : Measure S) [IsFiniteMeasure μ] (α : ℝ)
    (hα : 0 ≤ α) (hne : μ ≠ 0 ∨ α ≠ 0)
    (hmin : ∀ v ∈ D, α * J u ≤ α * J v + ∫ t, G v t ∂μ)
    (hslater : ∃ v ∈ D, ∀ t, G v t < 0) : 0 < α := by
  by_contra hn
  have hα0 : α = 0 := le_antisymm (not_lt.mp hn) hα
  have hμ : μ ≠ 0 := hne.resolve_right (not_ne_iff.mpr hα0)
  obtain ⟨v, hv, hGv⟩ := hslater
  have hpos : 0 < ∫ t, -(G v t) ∂μ := by
    apply (integral_pos_iff_support_of_nonneg
      (fun t => (neg_pos.mpr (hGv t)).le)
      ((G v).continuous.neg.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))).mpr
    have hs : Function.support (fun t => -(G v t)) = univ := by
      ext t
      simp only [Function.mem_support, mem_univ, iff_true]
      exact ne_of_gt (neg_pos.mpr (hGv t))
    rw [hs]
    exact Measure.measure_univ_pos.mpr hμ
  have hm := hmin v hv
  simp only [hα0, zero_mul, zero_add] at hm
  rw [integral_neg] at hpos
  change 0 < -(∫ t, G v t ∂μ) at hpos
  linarith

end OptimalControl
