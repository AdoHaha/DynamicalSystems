/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.UniformlyLocallyLipschitzUniqueness
public import Mathlib.Analysis.ODE.Transform
public import Mathlib.Dynamics.Flow

/-!
# Fundamental solutions and complete vector fields

This file contains the basic predicates, uniqueness, and the autonomous composition
law. Continuous dependence is proved in `ContinuousDependence`, the inhomogeneous
linear formula in `Duhamel`, and completeness under local Lipschitz and linear
growth assumptions in `GlobalExistenceContinuation` (using the estimates and
endpoint extension lemmas in `GlobalExistenceGrowth`).
-/

@[expose] public noncomputable section

open Topology Filter

variable {E E' F : Type*}

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

section NonAutonomous

/-- A fundamental solution for non-autonomous systems. -/
structure IsFundamentalSolution (Φ : ℝ → E → ℝ → E) (f : ℝ → E → E) : Prop where
  isIntegralCurve : ∀ t₀ x, IsIntegralCurve (Φ t₀ x) f
  initial : ∀ t₀ x₀, Φ t₀ x₀ t₀ = x₀

namespace IsFundamentalSolution

variable {Φ Φ' : ℝ → E → ℝ → E} {f : ℝ → E → E}

protected
theorem deriv (hΦ : IsFundamentalSolution Φ f) {t₀ t : ℝ} {x₀ : E} :
    deriv (Φ t₀ x₀) t = f t (Φ t₀ x₀ t) :=
  (hΦ.isIntegralCurve t₀ x₀ t).deriv

protected
theorem differentiableAt (hΦ : IsFundamentalSolution Φ f) (t₀ t : ℝ) (x₀ : E) :
    DifferentiableAt ℝ (Φ t₀ x₀) t :=
  (hΦ.isIntegralCurve t₀ x₀ t).differentiableAt

theorem _root_.IsIntegralCurve.eq_of_uniformlyLocallyLipschitz
    {v : ℝ → E → E} {γ₁ γ₂ : ℝ → E} {t₀ : ℝ}
    (hf : UniformlyLocallyLipschitz v)
    (h1 : IsIntegralCurve γ₁ v) (h2 : IsIntegralCurve γ₂ v)
    (heq : γ₁ t₀ = γ₂ t₀) : γ₁ = γ₂ := by
  ext t
  have h₀ : t₀ ∈ Set.Ioo (min t t₀ - 1) (max t t₀ + 1) :=
    ⟨by linarith [min_le_right t t₀], by linarith [le_max_right t t₀]⟩
  have ht : t ∈ Set.Ioo (min t t₀ - 1) (max t t₀ + 1) :=
    ⟨by linarith [min_le_left t t₀], by linarith [le_max_left t t₀]⟩
  exact IsIntegralCurveOn.eqOn_Ioo_of_uniformlyLocallyLipschitz hf h₀
    (h1.isIntegralCurveOn _) (h2.isIntegralCurveOn _) heq ht

theorem unique (hΦ : IsFundamentalSolution Φ f) (hΦ' : IsFundamentalSolution Φ' f)
    (hf : UniformlyLocallyLipschitz f) :
    Φ = Φ' := by
  ext t₀ x₀ : 2
  apply (hΦ.isIntegralCurve t₀ x₀).eq_of_uniformlyLocallyLipschitz hf (hΦ'.isIntegralCurve t₀ x₀)
  rw [hΦ.initial, hΦ'.initial]

section Linear

variable (L : ℝ → E →L[ℝ] E) (X : ℝ → ℝ → E →L[ℝ] E)

theorem linear_fundamental_solution (hX₀ : ∀ t₀, X t₀ t₀ = ContinuousLinearMap.id _ _)
    (hX : ∀ t₀ t, HasDerivAt (X t₀ ·) (L t ∘L X t₀ t) t) :
    IsFundamentalSolution (fun t₀ x t ↦ X t₀ t x) (L · ·) where
  initial := by intro t₀ x₀; simp [hX₀]
  isIntegralCurve := by
    intro t₀ x₀ t
    simpa using (hX t₀ t).clm_apply (hasDerivAt_const t x₀)

theorem linear_fundamental_solution' (hX₀ : ∀ t₀, X t₀ t₀ = ContinuousLinearMap.id _ _)
    (hX' : ∀ t₀ t, DifferentiableAt ℝ (X t₀ ·) t)
    (hX : ∀ t₀ t, deriv (X t₀ ·) t = L t ∘L X t₀ t) :
    IsFundamentalSolution (fun t₀ x t ↦ X t₀ t x) (L · ·) :=
  linear_fundamental_solution L X hX₀ (fun t₀ t ↦ hX t₀ t ▸ (hX' t₀ t).hasDerivAt)

/-- The operator solving the inhomogeneous ODE `d/dx x = L(t) x + g t` given a solution operator
`X : ℝ → ℝ → E →L[ℝ] E`. -/
def duhamelOperator (X : ℝ → ℝ → E →L[ℝ] E) (g : ℝ → E) (t₀ : ℝ) (x₀ : E) (t : ℝ) : E :=
  X t₀ t x₀ + ∫ τ in t₀..t, X τ t (g τ)

variable {g : ℝ → E}

theorem duhamelOperator_initial (hX₀ : ∀ t₀, X t₀ t₀ = ContinuousLinearMap.id _ _)
    (t₀ : ℝ) (x₀ : E) : duhamelOperator X g t₀ x₀ t₀ = x₀ := by
  simp [duhamelOperator, hX₀ t₀]

end Linear

end IsFundamentalSolution

/-- A vector field is complete if for every point there exists a global integral curve
`γ : ℝ → E`. -/
def IsCompleteVectorField (f : ℝ → E → E) : Prop :=
  ∀ t₀ x₀, ∃ γ : ℝ → E, γ t₀ = x₀ ∧ IsIntegralCurve γ f

namespace IsCompleteVectorField

variable {f : ℝ → E → E}

/-- The flow of a vector field at a point `x`. -/
def flowAt (hf : IsCompleteVectorField f) (t₀ : ℝ) (x₀ : E) : ℝ → E :=
  (hf t₀ x₀).choose

@[simp]
theorem flowAt_zero (hf : IsCompleteVectorField f) (t₀ : ℝ) (x₀ : E) :
    hf.flowAt t₀ x₀ t₀ = x₀ :=
  (hf t₀ x₀).choose_spec.left

theorem flowAt_isIntegralCurve (hf : IsCompleteVectorField f) (t₀ : ℝ) (x₀ : E) :
    IsIntegralCurve (hf.flowAt t₀ x₀) f :=
  (hf t₀ x₀).choose_spec.right

theorem flowAt_isFundamentalSolution (hf : IsCompleteVectorField f) :
    IsFundamentalSolution hf.flowAt f where
  isIntegralCurve := hf.flowAt_isIntegralCurve
  initial := hf.flowAt_zero

@[fun_prop]
theorem differentiable_flowAt (hf : IsCompleteVectorField f) (t₀ : ℝ) (x₀ : E) :
    Differentiable ℝ (hf.flowAt t₀ x₀) :=
  (hf.flowAt_isIntegralCurve t₀ x₀ · |>.differentiableAt)

/-- The flow of a vector field as a continuous map `ℝ → E`. -/
def contFlowAt (hf : IsCompleteVectorField f) (t₀ : ℝ) (x₀ : E) : C(ℝ, E) where
  toFun := hf.flowAt t₀ x₀
  continuous_toFun := (hf.differentiable_flowAt _ _).continuous

@[simp]
theorem contFlowAt_apply (hf : IsCompleteVectorField f) (t₀ : ℝ) (x₀ : E) (t : ℝ) :
  hf.contFlowAt t₀ x₀ t = hf.flowAt t₀ x₀ t := rfl

end IsCompleteVectorField

end NonAutonomous

section Autonomous

variable (f : E → E) (Φ : E → ℝ → E)

theorem isFundamentalSolution_iff' :
    IsFundamentalSolution (fun t₀ x t ↦ Φ x (t - t₀)) (fun _ ↦ f) ↔
    ∀ x, IsIntegralCurve (Φ x) (fun _ ↦ f) ∧ Φ x 0 = x := by
  constructor
  · intro h x
    exact ⟨by simpa using h.isIntegralCurve 0 x, by simpa using h.initial 0 x⟩
  · intro h
    refine ⟨fun t₀ x₀ ↦ (h x₀).1.comp_sub t₀, fun t₀ x₀ ↦ by simpa using (h x₀).2⟩

variable {K : NNReal}

/-- The fundamental solution satisfies the group property, `Φ t ∘ Φ t' = Φ (t + t')`. -/
theorem IsFundamentalSolution.add_apply'
    (hΦ : IsFundamentalSolution (fun t₀ x t ↦ Φ x (t - t₀)) (fun _ ↦ f))
    (hv : LipschitzWith K f) (t t' : ℝ) (x : E) :
    Φ (Φ x t') t = Φ x (t + t') := by
  set γ₁ := Φ (Φ x t')
  set γ₂ := fun t ↦ Φ x (t + t')
  rw [isFundamentalSolution_iff'] at hΦ
  have := (hΦ x).1.comp_add t'
  have hf : IsIntegralCurve γ₁ (fun _ ↦ f) := (hΦ (Φ x t')).1
  have hg : IsIntegralCurve γ₂ (fun _ ↦ f) := (hΦ x).1.comp_add t'
  have ht₀ : γ₁ 0 = γ₂ 0 := by
    unfold γ₁ γ₂
    simp [(hΦ (Φ x t')).2]
  rw [hf.eq (fun _ ↦ hv.lipschitzOnWith) (fun _ ↦ Set.mem_univ _) hg
    (fun _ ↦ Set.mem_univ _) ht₀]

variable {Φ' : ℝ → E → ℝ → E}

/-- The fundamental solution satisfies the group property, `Φ t ∘ Φ t' = Φ (t + t')`. -/
theorem IsFundamentalSolution.add_apply''
    (hΦ : IsFundamentalSolution Φ' (fun _ ↦ f))
    (hv : LocallyLipschitz f) (t t' : ℝ) (x : E) :
    Φ' 0 (Φ' 0 x t') t = Φ' 0 x (t + t') := by
  set γ₁ := Φ' 0 (Φ' 0 x t')
  set γ₂ := fun t ↦ Φ' 0 x (t + t')
  have hf : IsIntegralCurve γ₁ (fun _ ↦ f) := hΦ.isIntegralCurve 0 (Φ' 0 x t')
  have hg : IsIntegralCurve γ₂ (fun _ ↦ f) := (hΦ.isIntegralCurve 0 x).comp_add t'
  have ht₀ : γ₁ 0 = γ₂ 0 := by
    simp [γ₁, γ₂, hΦ.initial]
  have heq := hf.eq_of_uniformlyLocallyLipschitz hv.uniformlyLocallyLipschitz hg ht₀
  rw [heq]

/-- The fundamental solution satisfies the group property, `Φ t ∘ Φ t' = Φ (t + t')`. -/
theorem IsFundamentalSolution.add_apply
    (hΦ : IsFundamentalSolution (fun t₀ x t ↦ Φ x (t - t₀)) (fun _ ↦ f))
    (hv : LocallyLipschitz f) (t t' : ℝ) (x : E) :
    Φ (Φ x t') t = Φ x (t + t') := by
  set γ₁ := Φ (Φ x t')
  set γ₂ := fun t ↦ Φ x (t + t')
  rw [isFundamentalSolution_iff'] at hΦ
  have hf : IsIntegralCurve γ₁ (fun _ ↦ f) := (hΦ (Φ x t')).1
  have hg : IsIntegralCurve γ₂ (fun _ ↦ f) := (hΦ x).1.comp_add t'
  have ht₀ : γ₁ 0 = γ₂ 0 := by
    simp [γ₁, γ₂, (hΦ (Φ x t')).2]
  have heq := hf.eq_of_uniformlyLocallyLipschitz hv.uniformlyLocallyLipschitz hg ht₀
  rw [heq]

end Autonomous
