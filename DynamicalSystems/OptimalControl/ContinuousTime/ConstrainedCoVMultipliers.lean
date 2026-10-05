/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.CalculusOfVariations
public import Mathlib.Analysis.Calculus.LagrangeMultipliers

/-!
# Multiplier extraction for isoperimetric variation families

The multiplier is extracted from a genuine constrained minimum and strict
derivatives of the actual cost and constraint functionals. A nonzero derivative
of the scalar constraint rules out an abnormal multiplier and permits the cost
multiplier to be normalized to one.

The curve-family adapter applies this result to `cvFunctional` itself. The
caller must still prove strict differentiability of the parameter-dependent
integrals and identify their derivatives with the first-variation expressions.
This module does not claim those analytic interchange results or an entire
constrained Euler–Lagrange theorem.
-/

@[expose] public section

namespace IsoperimetricVariation

section Multipliers

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Extract and normalize a Lagrange multiplier. The condition `C' ≠ 0` is the
scalar constraint qualification; without it, normality would be unjustified. -/
theorem exists_normal_multiplier
    {J C : V → ℝ} {v₀ : V} {J' C' : V →L[ℝ] ℝ}
    (hmin : IsLocalMinOn J {v | C v = C v₀} v₀)
    (hJ : HasStrictFDerivAt J J' v₀) (hC : HasStrictFDerivAt C C' v₀)
    (hregular : C' ≠ 0) :
    ∃ lam : ℝ, J' + lam • C' = 0 := by
  have hextr : IsLocalExtrOn J {v | C v = C v₀} v₀ := Or.inl hmin
  obtain ⟨a, b, hab, heq⟩ :=
    hextr.exists_multipliers_of_hasStrictFDerivAt_1d hC hJ
  have hb : b ≠ 0 := by
    intro hb
    have ha : a ≠ 0 := by
      intro ha
      apply hab
      simp [ha, hb]
    have hzero : a • C' = 0 := by simpa [hb] using heq
    exact hregular ((smul_eq_zero.mp hzero).resolve_left ha)
  have hscaled := congrArg (fun D : V →L[ℝ] ℝ ↦ b⁻¹ • D) heq
  simp only [smul_add, smul_smul, smul_zero, inv_mul_cancel₀ hb, one_smul] at hscaled
  refine ⟨a / b, ?_⟩
  simpa only [div_eq_mul_inv, mul_comm, add_comm] using hscaled

/-- The extracted multiplier annihilates every parameter direction. This is a
consequence of the extracted linear-map equation, not an input variation law. -/
theorem exists_normal_multiplier_apply
    {J C : V → ℝ} {v₀ : V} {J' C' : V →L[ℝ] ℝ}
    (hmin : IsLocalMinOn J {v | C v = C v₀} v₀)
    (hJ : HasStrictFDerivAt J J' v₀) (hC : HasStrictFDerivAt C C' v₀)
    (hregular : C' ≠ 0) :
    ∃ lam : ℝ, ∀ v, J' v + lam * C' v = 0 := by
  obtain ⟨lam, hlam⟩ := exists_normal_multiplier hmin hJ hC hregular
  refine ⟨lam, fun v ↦ ?_⟩
  simpa using congrArg (fun D : V →L[ℝ] ℝ ↦ D v) hlam

/-- For finitely many scalar constraints, linear independence of their actual
derivatives rules out an abnormal multiplier and yields a normal multiplier
vector. This works on a Banach parameter space, not just on Euclidean space. -/
theorem exists_normal_multipliers
    {ι : Type*} [Fintype ι]
    {J : V → ℝ} {C : ι → V → ℝ} {v₀ : V}
    {J' : V →L[ℝ] ℝ} {C' : ι → V →L[ℝ] ℝ}
    (hmin : IsLocalMinOn J {v | ∀ i, C i v = C i v₀} v₀)
    (hJ : HasStrictFDerivAt J J' v₀)
    (hC : ∀ i, HasStrictFDerivAt (C i) (C' i) v₀)
    (hregular : LinearIndependent ℝ C') :
    ∃ lam : ι → ℝ, J' + ∑ i, lam i • C' i = 0 := by
  classical
  have hextr : IsLocalExtrOn J {v | ∀ i, C i v = C i v₀} v₀ := Or.inl hmin
  obtain ⟨a, b, hab, heq⟩ :=
    hextr.exists_multipliers_of_hasStrictFDerivAt hC hJ
  have hb : b ≠ 0 := by
    intro hb
    have hzero : ∑ i, a i • C' i = 0 := by simpa [hb] using heq
    have ha : a = 0 := by
      funext i
      exact (Fintype.linearIndependent_iff.mp hregular) a hzero i
    exact hab (Prod.ext ha hb)
  have hscaled := congrArg (fun D : V →L[ℝ] ℝ ↦ b⁻¹ • D) heq
  simp only [smul_add, Finset.smul_sum, smul_smul, smul_zero,
    inv_mul_cancel₀ hb, one_smul] at hscaled
  refine ⟨fun i ↦ a i / b, ?_⟩
  simpa only [div_eq_mul_inv, mul_comm, add_comm] using hscaled

end Multipliers

section CurveFamily

variable {V E : Type*}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An actual constrained minimum of `cvFunctional` induces an extracted normal
multiplier on any admissible parameterized curve family through the reference.

The set `S` records the admissible curves (for example smooth curves with fixed
endpoints and integrable cost and constraint integrands). The optimality premise
compares actual integral costs on `S` at a fixed integral constraint value.
Strict derivatives here are of those actual integral functionals. -/
theorem exists_normal_multiplier_of_curve_family
    (L G : ℝ → E → E → ℝ) (K : E → ℝ) (T : ℝ)
    (S : Set (ℝ → E)) (x : ℝ → E) (Γ : V → ℝ → E)
    (hΓ₀ : Γ 0 = x) (hΓ : ∀ v, Γ v ∈ S)
    (hopt : IsMinOn (cvFunctional L K T)
      {y | y ∈ S ∧ cvFunctional G (fun _ ↦ 0) T y =
        cvFunctional G (fun _ ↦ 0) T x} x)
    (J' C' : V →L[ℝ] ℝ)
    (hJ : HasStrictFDerivAt (fun v ↦ cvFunctional L K T (Γ v)) J' 0)
    (hC : HasStrictFDerivAt
      (fun v ↦ cvFunctional G (fun _ ↦ 0) T (Γ v)) C' 0)
    (hregular : C' ≠ 0) :
    ∃ lam : ℝ, ∀ v, J' v + lam * C' v = 0 := by
  have hmin : IsMinOn (fun v ↦ cvFunctional L K T (Γ v))
      {v | cvFunctional G (fun _ ↦ 0) T (Γ v) =
        cvFunctional G (fun _ ↦ 0) T (Γ 0)} 0 := by
    intro v hv
    change cvFunctional G (fun _ ↦ 0) T (Γ v) =
      cvFunctional G (fun _ ↦ 0) T (Γ 0) at hv
    change cvFunctional L K T (Γ 0) ≤ cvFunctional L K T (Γ v)
    rw [hΓ₀] at hv ⊢
    exact hopt ⟨hΓ v, hv⟩
  exact exists_normal_multiplier_apply hmin.isLocalMinOn hJ hC hregular

/-- Once the *actual functional derivatives* are identified with the explicit
first variations, the extracted multiplier gives their constrained combination
in every direction represented by the family. -/
theorem exists_firstVariation_multiplier_of_curve_family
    (L G : ℝ → E → E → ℝ) (K : E → ℝ) (T : ℝ)
    (S : Set (ℝ → E)) (x : ℝ → E) (Γ η : V → ℝ → E)
    (hΓ₀ : Γ 0 = x) (hΓ : ∀ v, Γ v ∈ S)
    (hopt : IsMinOn (cvFunctional L K T)
      {y | y ∈ S ∧ cvFunctional G (fun _ ↦ 0) T y =
        cvFunctional G (fun _ ↦ 0) T x} x)
    (J' C' : V →L[ℝ] ℝ)
    (hJ : HasStrictFDerivAt (fun v ↦ cvFunctional L K T (Γ v)) J' 0)
    (hC : HasStrictFDerivAt
      (fun v ↦ cvFunctional G (fun _ ↦ 0) T (Γ v)) C' 0)
    (hregular : C' ≠ 0)
    (hJvariation : ∀ v, J' v = firstVariation L K T x (η v))
    (hCvariation : ∀ v, C' v = firstVariation G (fun _ ↦ 0) T x (η v)) :
    ∃ lam : ℝ, ∀ v, firstVariation L K T x (η v) +
      lam * firstVariation G (fun _ ↦ 0) T x (η v) = 0 := by
  obtain ⟨lam, hlam⟩ := exists_normal_multiplier_of_curve_family L G K T S x Γ
    hΓ₀ hΓ hopt J' C' hJ hC hregular
  exact ⟨lam, fun v ↦ by simpa only [hJvariation, hCvariation] using hlam v⟩

end CurveFamily

end IsoperimetricVariation
