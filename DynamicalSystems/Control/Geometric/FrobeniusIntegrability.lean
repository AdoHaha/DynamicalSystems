/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.FrobeniusGraph
public import DynamicalSystems.Control.Geometric.FrobeniusCoordinates
public import DynamicalSystems.Control.Geometric.FrobeniusRegularity

/-! # The smooth Frobenius existence theorem

A compatible graph connection on finite-dimensional real normed spaces has a smooth
local solution through every prescribed point. The finite flow construction gives
a differentiable graph solution in linear coordinates. The total differential
equation then improves its regularity to smoothness on the same open neighborhood.

`exists_sol_of_fderiv_compat` records the solution with an open domain and actual
Fréchet derivatives. `frobeniusTheorem_holds` proves the previously recorded target
`frobeniusTheorem`, preserving that interface.

The target follows Khavkine–Růžička, *lean-dg-frobenius*, `Frobenius/Basic.lean`
(Apache 2.0). The proof is the classical Frobenius construction; see Krener,
*Differential Geometric Methods in Nonlinear Control*, Encyclopedia of Systems and
Control, second edition, and Sontag, *Mathematical Control Theory*, Chapter 4, §4.4.
-/

@[expose] public section

open Set Filter
open scoped Topology ContDiff

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [CompleteSpace X] [CompleteSpace Y]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]

omit [CompleteSpace X] in
/-- A `C¹` compatible graph connection has a local differentiable solution through
each prescribed point, on an open neighborhood in an arbitrary finite-dimensional base. -/
theorem exists_local_solution_of_totalFderivCompat
    (g : X × Y → X →L[ℝ] Y) (hg : ContDiff ℝ 1 g)
    (hcompat : TotalFderivCompat g univ) (x₀ : X) (z : Y) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ ∃ w : X → Y, w x₀ = z ∧
      ∀ x ∈ U, HasFDerivAt w (g (x, w x)) x := by
  let e := (Module.finBasis ℝ X).equivFunL.symm
  have hg' : ContDiff ℝ 1 (frobeniusBaseChange e g) :=
    contDiff_frobeniusBaseChange e hg
  have hc' : TotalFderivCompat (frobeniusBaseChange e g) univ :=
    totalFderivCompat_frobeniusBaseChange e (hg.differentiable (by simp)) hcompat
  exact exists_local_solution_of_baseChange e g x₀ z
    (exists_local_graph_solution (frobeniusBaseChange e g) hg' hc' (e.symm x₀) z)

omit [CompleteSpace X] in
/-- Frobenius existence for a smooth compatible graph connection. The solution is
smooth on one open neighborhood and has the prescribed full derivative at every point there. -/
theorem exists_sol_of_fderiv_compat
    (g : X × Y → X →L[ℝ] Y) (hg : ContDiff ℝ ∞ g)
    (hcompat : TotalFderivCompat g univ) (x₀ : X) (z : Y) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ ∃ w : X → Y,
      ContDiffOn ℝ ∞ w U ∧ w x₀ = z ∧
        ∀ x ∈ U, HasFDerivAt w (g (x, w x)) x := by
  obtain ⟨U, hU, hx₀, w, hw₀, hw⟩ :=
    exists_local_solution_of_totalFderivCompat g (hg.of_le (by simp)) hcompat x₀ z
  exact ⟨U, hU, hx₀, w, contDiffOn_infty_of_hasFDerivAt_eq hU hg hw, hw₀, hw⟩

omit [CompleteSpace X] [CompleteSpace Y] [FiniteDimensional ℝ X]
  [FiniteDimensional ℝ Y] in
/-- The recorded smooth Frobenius target is true. The open solution domain makes
its interior equal to itself, so the within-derivative conclusion follows directly. -/
theorem frobeniusTheorem_holds : frobeniusTheorem (X := X) (Y := Y) := by
  intro g hg hcompat _ _ _ _ x₀ z
  obtain ⟨U, hU, hx₀, w, hwreg, hw₀, hw⟩ :=
    exists_sol_of_fderiv_compat g hg hcompat x₀ z
  refine ⟨U, hU.mem_nhds hx₀, w, ?_, hw₀, ?_⟩
  · simpa only [hU.interior_eq] using hwreg
  · intro x hx
    rw [hU.interior_eq, fderivWithin_of_mem_nhds (hU.mem_nhds hx)]
    exact (hw x hx).fderiv

end
