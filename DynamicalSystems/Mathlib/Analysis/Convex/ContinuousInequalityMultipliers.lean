/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Ordered
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Necessary multipliers for continuously indexed convex inequalities

The candidate space need not be finite-dimensional. The positive cone in
`R × C(time,R)` has interior, even when the feasible candidate set does not.
This gives nontrivial multipliers without a constraint qualification. No
separator or Lagrangian minimum is assumed. The cost multiplier may vanish.
-/

@[expose] public section

open Set

namespace ConvexProgramming

variable {τ X : Type*} [TopologicalSpace τ] [CompactSpace τ]

/-- Upward epigraph of actual objective differences and constraint residuals.
The residual is not shifted by its reference value, retaining slackness. -/
def continuousConstraintEpigraph (S : Set X) (J : X → ℝ) (G : X → C(τ, ℝ))
    (x₀ : X) : Set (ℝ × C(τ, ℝ)) :=
  {z | ∃ x ∈ S, J x - J x₀ ≤ z.1 ∧ G x ≤ z.2}

/-- An intermediate mixing interface; the convex-programming entry point
below discharges it from the original objective and constraint functions. -/
theorem convex_continuousConstraintEpigraph_of_mixing
    (S : Set X) (J : X → ℝ) (G : X → C(τ, ℝ)) (x₀ : X)
    (hmix : ∀ x ∈ S, ∀ y ∈ S, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ∃ z ∈ S, J z ≤ a * J x + b * J y ∧ ∀ t, G z t ≤ a * G x t + b * G y t) :
    Convex ℝ (continuousConstraintEpigraph S J G x₀) := by
  rintro p ⟨x, hx, hjx, hgx⟩ q ⟨y, hy, hjy, hgy⟩ a b ha hb hab
  obtain ⟨z, hz, hjz, hgz⟩ := hmix x hx y hy a b ha hb hab
  refine ⟨z, hz, ?_, ?_⟩
  · change J z - J x₀ ≤ a * p.1 + b * q.1
    have hJ₀ : a * J x₀ + b * J x₀ = J x₀ := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hjx),
      mul_nonneg hb (sub_nonneg.mpr hjy)]
  · intro t
    change G z t ≤ a * p.2 t + b * q.2 t
    exact (hgz t).trans (add_le_add (mul_le_mul_of_nonneg_left (hgx t) ha)
      (mul_le_mul_of_nonneg_left (hgy t) hb))

/-- The slack epigraph has interior. Neither feasible-set interior nor a
Slater point is assumed. -/
theorem continuousConstraintEpigraph_nonempty_interior
    (S : Set X) (J : X → ℝ) (G : X → C(τ, ℝ)) (x₀ : X)
    (hx₀ : x₀ ∈ S) (hg₀ : G x₀ ≤ 0) :
    (interior (continuousConstraintEpigraph S J G x₀)).Nonempty := by
  let e : ℝ × C(τ, ℝ) := (1, ContinuousMap.const τ 1)
  refine ⟨e, mem_interior_iff_mem_nhds.mpr (Metric.mem_nhds_iff.mpr
    ⟨1 / 2, by norm_num, ?_⟩)⟩
  intro z hz
  have hz' : ‖z - e‖ < (1 : ℝ) / 2 := by simpa only [dist_eq_norm] using hz
  have hz₁ : ‖z.1 - 1‖ < (1 : ℝ) / 2 :=
    lt_of_le_of_lt (le_max_left _ _) hz'
  have hz₂ : ‖z.2 - ContinuousMap.const τ 1‖ < (1 : ℝ) / 2 :=
    lt_of_le_of_lt (le_max_right _ _) hz'
  refine ⟨x₀, hx₀, ?_, ?_⟩
  · rw [sub_self]
    have := (abs_lt.mp (show |z.1 - 1| < 1 / 2 from hz₁)).1
    linarith
  · intro t
    have ht := lt_of_le_of_lt ((z.2 - ContinuousMap.const τ 1).norm_coe_le_norm t) hz₂
    change |z.2 t - 1| < 1 / 2 at ht
    have ht' := (abs_lt.mp ht).1
    have hg : G x₀ t ≤ 0 := hg₀ t
    change G x₀ t ≤ z.2 t
    linarith

/-- Actual constrained optimality excludes an interior point at the origin. -/
theorem zero_notMem_interior_continuousConstraintEpigraph
    (S : Set X) (J : X → ℝ) (G : X → C(τ, ℝ)) (x₀ : X)
    (hopt : ∀ x ∈ S, G x ≤ 0 → J x₀ ≤ J x) :
    (0 : ℝ × C(τ, ℝ)) ∉ interior (continuousConstraintEpigraph S J G x₀) := by
  intro h
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp h)
  have hm : ((-ε / 2 : ℝ), (0 : C(τ, ℝ))) ∈ Metric.ball 0 ε := by
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def]
    simp only [norm_zero, Real.norm_eq_abs]
    rw [abs_of_neg (by linarith : -ε / 2 < 0)]
    exact max_lt (by linarith) hε
  obtain ⟨x, hx, hj, hg⟩ := hball hm
  have ho := hopt x hx hg
  change J x - J x₀ ≤ -ε / 2 at hj
  linarith

/-- Functional multiplier necessity for continuously indexed convex
inequalities. Nontriviality includes abnormal cost multipliers. -/
theorem exists_continuousInequality_functional_of_mixing
    (S : Set X) (J : X → ℝ) (G : X → C(τ, ℝ)) (x₀ : X)
    (hx₀ : x₀ ∈ S) (hg₀ : G x₀ ≤ 0)
    (hmix : ∀ x ∈ S, ∀ y ∈ S, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ∃ z ∈ S, J z ≤ a * J x + b * J y ∧ ∀ t, G z t ≤ a * G x t + b * G y t)
    (hopt : ∀ x ∈ S, G x ≤ 0 → J x₀ ≤ J x) :
    ∃ (α : ℝ) (Λ : C(τ, ℝ) →L[ℝ] ℝ),
      0 ≤ α ∧ (α ≠ 0 ∨ Λ ≠ 0) ∧ (∀ g, 0 ≤ g → 0 ≤ Λ g) ∧
      Λ (G x₀) = 0 ∧ ∀ x ∈ S, α * J x₀ ≤ α * J x + Λ (G x) := by
  let C := continuousConstraintEpigraph S J G x₀
  obtain ⟨l, hl, hsep⟩ := geometric_hahn_banach_of_nonempty_interior_point
    (convex_continuousConstraintEpigraph_of_mixing S J G x₀ hmix)
    (zero_notMem_interior_continuousConstraintEpigraph S J G x₀ hopt)
    (continuousConstraintEpigraph_nonempty_interior S J G x₀ hx₀ hg₀)
  let q := -l
  have hq : q ≠ 0 := neg_ne_zero.mpr hl
  have hsupport : ∀ z ∈ C, 0 ≤ q z := by
    intro z hz
    have h := hsep z hz
    change 0 ≤ -l z
    simpa only [map_zero, neg_nonneg] using h
  let α : ℝ := q (1, 0)
  let Λ : C(τ, ℝ) →L[ℝ] ℝ := q.comp (ContinuousLinearMap.inr ℝ ℝ C(τ, ℝ))
  have hsplit : ∀ z : ℝ × C(τ, ℝ), q z = α * z.1 + Λ z.2 := by
    intro z
    have he : z = z.1 • (1, (0 : C(τ, ℝ))) + (0, z.2) := by ext <;> simp
    calc
      q z = q (z.1 • (1, (0 : C(τ, ℝ))) + (0, z.2)) := congrArg q he
      _ = α * z.1 + Λ z.2 := by
        rw [map_add, map_smul]
        change z.1 * α + Λ z.2 = α * z.1 + Λ z.2
        ring
  have hα : 0 ≤ α := hsupport (1, 0) ⟨x₀, hx₀, by simp, hg₀⟩
  have hΛ : ∀ g : C(τ, ℝ), 0 ≤ g → 0 ≤ Λ g := by
    intro g hg
    exact hsupport (0, g) ⟨x₀, hx₀, by simp, hg₀.trans hg⟩
  have hcomp : Λ (G x₀) = 0 := by
    apply le_antisymm
    · have h := hΛ (-(G x₀)) (fun t => neg_nonneg.mpr (hg₀ t))
      simpa only [map_neg, neg_nonneg] using h
    · exact hsupport (0, G x₀) ⟨x₀, hx₀, by simp, le_rfl⟩
  refine ⟨α, Λ, hα, ?_, hΛ, hcomp, ?_⟩
  · by_contra hn
    push Not at hn
    apply hq
    ext z
    rw [hsplit, hn.1, hn.2]
    simp
  · intro x hx
    have h := hsupport (J x - J x₀, G x) ⟨x, hx, le_rfl, le_rfl⟩
    rw [hsplit] at h
    dsimp at h
    nlinarith

variable [AddCommGroup X] [Module ℝ X]

/-- Convex-programming entry point: all epigraph/mixing conditions are proved
from the original convex set, convex objective, and pointwise convex constraints. -/
theorem exists_continuousInequality_functional
    {S : Set X} (hS : Convex ℝ S) (J : X → ℝ) (G : X → C(τ, ℝ)) (x₀ : X)
    (hJ : ConvexOn ℝ S J) (hG : ∀ t, ConvexOn ℝ S (fun x => G x t))
    (hx₀ : x₀ ∈ S) (hg₀ : G x₀ ≤ 0)
    (hopt : ∀ x ∈ S, G x ≤ 0 → J x₀ ≤ J x) :
    ∃ (α : ℝ) (Λ : C(τ, ℝ) →L[ℝ] ℝ),
      0 ≤ α ∧ (α ≠ 0 ∨ Λ ≠ 0) ∧ (∀ g, 0 ≤ g → 0 ≤ Λ g) ∧
      Λ (G x₀) = 0 ∧ ∀ x ∈ S, α * J x₀ ≤ α * J x + Λ (G x) := by
  apply exists_continuousInequality_functional_of_mixing S J G x₀ hx₀ hg₀ ?_ hopt
  intro x hx y hy a b ha hb hab
  exact ⟨a • x + b • y, hS hx hy ha hb hab, hJ.2 hx hy ha hb hab,
    fun t => (hG t).2 hx hy ha hb hab⟩

end ConvexProgramming
