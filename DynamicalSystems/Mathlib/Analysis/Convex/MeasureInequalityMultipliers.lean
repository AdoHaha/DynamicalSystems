/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.Convex.ContinuousInequalityMultipliers
public import DynamicalSystems.Mathlib.MeasureTheory.PositiveFunctionalMeasure

/-!
# Finite measure multipliers for continuously indexed convex constraints

Geometric separation and Riesz representation construct the multiplier.
Complementary slackness implies that its measure is zero outside the active
constraint set. Abnormal cost multipliers are retained. Uniform strict
feasibility is used only in the separate normality theorem.
-/

@[expose] public section
open Set Filter MeasureTheory
namespace ConvexProgramming
variable {τ X : Type*} [TopologicalSpace τ] [CompactSpace τ] [T2Space τ]
  [MeasurableSpace τ] [BorelSpace τ]

/-- Complementarity for a nonpositive continuous residual forces the
measure to be concentrated on its zero set. -/
theorem measure_inactive_eq_zero (μ : Measure τ) [IsFiniteMeasure μ]
    (g : C(τ, ℝ)) (hg : ∀ t, g t ≤ 0) (hcomp : (∫ t, g t ∂μ) = 0) :
    μ {t | g t ≠ 0} = 0 := by
  have hgi : Integrable (fun t => g t) μ :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hzero : (∫ t, -g t ∂μ) = 0 := by rw [integral_neg, hcomp, neg_zero]
  have hae := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun t => neg_nonneg.mpr (hg t)) hgi.neg).mp hzero
  have hae' : ∀ᵐ t ∂μ, g t = 0 := by
    filter_upwards [hae] with t ht
    exact neg_eq_zero.mp ht
  exact ae_iff.mp hae'

/-- Necessary finite positive measure multipliers, constructed from actual
optimality and an intermediate convex-mixture interface. -/
theorem exists_continuousInequality_measure_of_mixing
    (S : Set X) (J : X → ℝ) (G : X → C(τ, ℝ)) (x₀ : X)
    (hx₀ : x₀ ∈ S) (hg₀ : G x₀ ≤ 0)
    (hmix : ∀ x ∈ S, ∀ y ∈ S, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      ∃ z ∈ S, J z ≤ a * J x + b * J y ∧ ∀ t, G z t ≤ a * G x t + b * G y t)
    (hopt : ∀ x ∈ S, G x ≤ 0 → J x₀ ≤ J x) :
    ∃ (α : ℝ) (μ : Measure τ), IsFiniteMeasure μ ∧ 0 ≤ α ∧ (α ≠ 0 ∨ μ ≠ 0) ∧
      (∫ t, G x₀ t ∂μ) = 0 ∧ μ {t | G x₀ t ≠ 0} = 0 ∧
      ∀ x ∈ S, α * J x₀ ≤ α * J x + ∫ t, G x t ∂μ := by
  obtain ⟨α, Λ, hα, hne, hΛ, hcomp, hmin⟩ :=
    exists_continuousInequality_functional_of_mixing S J G x₀ hx₀ hg₀ hmix hopt
  let μ := PositiveFunctional.measure Λ hΛ
  have hi : ∀ g : C(τ, ℝ), (∫ t, g t ∂μ) = Λ g := PositiveFunctional.integral_eq Λ hΛ
  have hc : (∫ t, G x₀ t ∂μ) = 0 := (hi (G x₀)).trans hcomp
  refine ⟨α, μ, inferInstance, hα, ?_, hc, measure_inactive_eq_zero μ (G x₀) hg₀ hc, ?_⟩
  · exact hne.imp id (PositiveFunctional.ne_zero_of_ne_zero Λ hΛ)
  · intro x hx
    rw [hi]
    exact hmin x hx

variable [AddCommGroup X] [Module ℝ X]

/-- Convex programming with a compact continuum of constraints has necessary
nontrivial measure multipliers. No finite-dimensional candidate space,
constraint qualification, separator, or Lagrangian certificate is supplied. -/
theorem exists_continuousInequality_measure
    {S : Set X} (hS : Convex ℝ S) (J : X → ℝ) (G : X → C(τ, ℝ)) (x₀ : X)
    (hJ : ConvexOn ℝ S J) (hG : ∀ t, ConvexOn ℝ S (fun x => G x t))
    (hx₀ : x₀ ∈ S) (hg₀ : G x₀ ≤ 0)
    (hopt : ∀ x ∈ S, G x ≤ 0 → J x₀ ≤ J x) :
    ∃ (α : ℝ) (μ : Measure τ), IsFiniteMeasure μ ∧ 0 ≤ α ∧ (α ≠ 0 ∨ μ ≠ 0) ∧
      (∫ t, G x₀ t ∂μ) = 0 ∧ μ {t | G x₀ t ≠ 0} = 0 ∧
      ∀ x ∈ S, α * J x₀ ≤ α * J x + ∫ t, G x t ∂μ := by
  apply exists_continuousInequality_measure_of_mixing S J G x₀ hx₀ hg₀ ?_ hopt
  intro x hx y hy a b ha hb hab
  exact ⟨a • x + b • y, hS hx hy ha hb hab, hJ.2 hx hy ha hb hab,
    fun t => (hG t).2 hx hy ha hb hab⟩

omit [AddCommGroup X] [Module ℝ X] in
/-- Uniform strict feasibility rules out abnormal multipliers. This is a
separate proved constraint qualification, not an implicit normalization. -/
theorem costMultiplier_pos_of_uniform_slater
    (S : Set X) (J : X → ℝ) (G : X → C(τ, ℝ)) (x₀ : X)
    (α : ℝ) (μ : Measure τ) [IsFiniteMeasure μ]
    (hα : 0 ≤ α) (hne : α ≠ 0 ∨ μ ≠ 0)
    (hmin : ∀ x ∈ S, α * J x₀ ≤ α * J x + ∫ t, G x t ∂μ)
    (hstrict : ∃ x ∈ S, ∃ δ : ℝ, 0 < δ ∧ ∀ t, G x t ≤ -δ) : 0 < α := by
  by_contra hn
  have hα₀ : α = 0 := le_antisymm (le_of_not_gt hn) hα
  have hμ : μ ≠ 0 := hne.resolve_left (by simp [hα₀])
  letI : NeZero μ := ⟨hμ⟩
  have hm : 0 < μ.real univ := measureReal_univ_pos
  obtain ⟨x, hx, δ, hδ, hg⟩ := hstrict
  have hi : Integrable (fun t => G x t) μ :=
    (G x).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hb : (∫ t, G x t ∂μ) ≤ -δ * μ.real univ := by
    calc
      (∫ t, G x t ∂μ) ≤ ∫ _ : τ, -δ ∂μ := integral_mono hi (integrable_const _) hg
      _ = -δ * μ.real univ := by simp [integral_const, mul_comm]
  have hp : 0 ≤ ∫ t, G x t ∂μ := by simpa [hα₀] using hmin x hx
  nlinarith

end ConvexProgramming
