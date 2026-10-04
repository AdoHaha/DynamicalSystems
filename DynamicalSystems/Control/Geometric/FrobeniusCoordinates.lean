/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.Frobenius

/-! # Linear base coordinates for the Frobenius equation

A continuous linear change of horizontal coordinates preserves the regularity
and compatibility of a graph connection. Solutions in those coordinates pull
back to solutions in the original base space. This permits the finite-coordinate
construction to apply to any finite-dimensional real base space.

The coordinate argument is classical; see Sontag, *Mathematical Control Theory*,
second edition, Chapter 4, §4.4. The compatibility tensor follows the definitions
ported from Khavkine–Růžička in `Frobenius.lean`.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

variable {B X Y : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Express a graph connection after a linear change of base coordinates. -/
noncomputable def frobeniusBaseChange (e : B ≃L[ℝ] X)
    (g : X × Y → X →L[ℝ] Y) : B × Y → B →L[ℝ] Y :=
  fun p ↦ (g (e p.1, p.2)).comp (e : B →L[ℝ] X)

@[simp] theorem frobeniusBaseChange_apply (e : B ≃L[ℝ] X)
    (g : X × Y → X →L[ℝ] Y) (p : B × Y) (d : B) :
    frobeniusBaseChange e g p d = g (e p.1, p.2) (e d) := rfl

/-- A linear change of horizontal coordinates preserves every regularity order. -/
theorem contDiff_frobeniusBaseChange (e : B ≃L[ℝ] X)
    {g : X × Y → X →L[ℝ] Y} {n : ℕ∞ω} (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (frobeniusBaseChange e g) := by
  change ContDiff ℝ n (fun p : B × Y ↦
    (g (e p.1, p.2)).comp (e : B →L[ℝ] X))
  exact (hg.comp ((e.contDiff.comp contDiff_fst).prodMk contDiff_snd)).clm_comp
    contDiff_const

/-- The derivative of a transformed connection applies the same linear change
to the base variation and to the horizontal vector. -/
theorem fderiv_frobeniusBaseChange_apply (e : B ≃L[ℝ] X)
    (g : X × Y → X →L[ℝ] Y) (p v : B × Y) (d : B)
    (hg : DifferentiableAt ℝ g (e p.1, p.2)) :
    fderiv ℝ (frobeniusBaseChange e g) p v d =
      fderiv ℝ g (e p.1, p.2) (e v.1, v.2) (e d) := by
  let P : B × Y →L[ℝ] X × Y :=
    ((e : B →L[ℝ] X).comp (ContinuousLinearMap.fst ℝ B Y)).prod
      (ContinuousLinearMap.snd ℝ B Y)
  let Q : (X →L[ℝ] Y) →L[ℝ] B →L[ℝ] Y :=
    (ContinuousLinearMap.compL ℝ B X Y).flip (e : B →L[ℝ] X)
  have hd : HasFDerivAt (frobeniusBaseChange e g)
      (Q.comp ((fderiv ℝ g (e p.1, p.2)).comp P)) p :=
    Q.hasFDerivAt.comp p (hg.hasFDerivAt.comp p P.hasFDerivAt)
  rw [hd.fderiv]
  rfl

/-- Curvature transforms covariantly in its two horizontal arguments. -/
theorem curvature_frobeniusBaseChange (e : B ≃L[ℝ] X)
    (g : X × Y → X →L[ℝ] Y) (p : B × Y) (d₁ d₂ : B)
    (hg : DifferentiableAt ℝ g (e p.1, p.2)) :
    Curvature (frobeniusBaseChange e g) p d₁ d₂ =
      Curvature g (e p.1, p.2) (e d₁) (e d₂) := by
  simp only [Curvature, fderiv_frobeniusBaseChange_apply e g p _ _ hg,
    frobeniusBaseChange_apply, map_zero]

/-- The global compatibility condition is preserved by linear base coordinates. -/
theorem totalFderivCompat_frobeniusBaseChange (e : B ≃L[ℝ] X)
    {g : X × Y → X →L[ℝ] Y} (hg : Differentiable ℝ g)
    (hcompat : TotalFderivCompat g univ) :
    TotalFderivCompat (frobeniusBaseChange e g) univ := by
  intro p _ d₁ d₂
  rw [curvature_frobeniusBaseChange e g p d₁ d₂ (hg _)]
  exact hcompat _ (mem_univ _) _ _

/-- A solution of the transformed equation satisfies the original equation
after composition with the inverse base coordinate map. -/
theorem hasFDerivAt_solution_of_frobeniusBaseChange (e : B ≃L[ℝ] X)
    {g : X × Y → X →L[ℝ] Y} {w : B → Y} {x : X}
    (hw : HasFDerivAt w
      (frobeniusBaseChange e g (e.symm x, w (e.symm x))) (e.symm x)) :
    HasFDerivAt (fun y : X ↦ w (e.symm y)) (g (x, w (e.symm x))) x := by
  have h : HasFDerivAt (fun y : X ↦ w (e.symm y))
      ((frobeniusBaseChange e g (e.symm x, w (e.symm x))).comp
        (e.symm : X →L[ℝ] B)) x := hw.comp x e.symm.hasFDerivAt
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro d
  simp

/-- Regularity of a solution is preserved when returning to the original base. -/
theorem contDiffOn_solution_of_frobeniusBaseChange (e : B ≃L[ℝ] X)
    {w : B → Y} {U : Set B} {n : ℕ∞ω} (hw : ContDiffOn ℝ n w U) :
    ContDiffOn ℝ n (fun x : X ↦ w (e.symm x)) (e.symm ⁻¹' U) :=
  hw.comp e.symm.contDiff.contDiffOn (fun _ hx ↦ hx)

/-- A local solution in any linear coordinates gives a local solution on the
original base, with an open domain and the same initial value. -/
theorem exists_local_solution_of_baseChange (e : B ≃L[ℝ] X)
    (g : X × Y → X →L[ℝ] Y) (x₀ : X) (z : Y)
    (hsol : ∃ U : Set B, IsOpen U ∧ e.symm x₀ ∈ U ∧
      ∃ w : B → Y, w (e.symm x₀) = z ∧
        ∀ x ∈ U, HasFDerivAt w (frobeniusBaseChange e g (x, w x)) x) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ ∃ w : X → Y, w x₀ = z ∧
      ∀ x ∈ U, HasFDerivAt w (g (x, w x)) x := by
  obtain ⟨U, hU, hx₀, w, hw₀, hw⟩ := hsol
  refine ⟨e.symm ⁻¹' U, hU.preimage e.symm.continuous, hx₀,
    fun x ↦ w (e.symm x), hw₀, fun x hx ↦ ?_⟩
  exact hasFDerivAt_solution_of_frobeniusBaseChange e (hw _ hx)
