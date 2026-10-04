/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Smoothness of solutions of a total differential equation

Once a differentiable function solves `Dw(x) = g(x, w(x))`, smoothness of the
coefficient gives smoothness of the solution on the same open domain. At each
induction step, composition gives one more continuous derivative. This argument
does not require finite-dimensionality or completeness.

The regularity order is `∞`, the order of infinitely differentiable functions.
This bootstrap does not assert analytic regularity. See Sontag, *Mathematical
Control Theory*, second edition, Chapter 4, §4.4, for the total differential
equation formulation of Frobenius integrability.
-/

@[expose] public section

open Set
open scoped ContDiff

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A solution of a smooth total differential equation is smooth on its open
domain. The coefficient need only be smooth on a set containing the solution's
graph. -/
theorem contDiffOn_infty_of_hasFDerivAt_eq_on
    {U : Set X} {V : Set (X × Y)} {g : X × Y → X →L[ℝ] Y} {w : X → Y}
    (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g V)
    (hgraph : MapsTo (fun x ↦ (x, w x)) U V)
    (hw : ∀ x ∈ U, HasFDerivAt w (g (x, w x)) x) :
    ContDiffOn ℝ ∞ w U := by
  apply contDiffOn_infty.mpr
  intro n
  induction n with
  | zero =>
    exact contDiffOn_zero.mpr
      (fun x hx ↦ (hw x hx).continuousAt.continuousWithinAt)
  | succ n ih =>
    have hderiv : ContDiffOn ℝ n (fun x ↦ g (x, w x)) U :=
      (contDiffOn_infty.mp hg n).comp (contDiffOn_id.prodMk ih) hgraph
    have hnext : ContDiffOn ℝ ((n : ℕ∞ω) + 1) w U :=
      (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hU.uniqueDiffOn).mpr
        ⟨by simp, fun x ↦ g (x, w x), hderiv, fun x hx ↦ (hw x hx).hasFDerivWithinAt⟩
    simpa only [Nat.cast_add, Nat.cast_one] using hnext

/-- A solution of a globally smooth total differential equation is smooth on
its open domain. Existence of the displayed derivatives already supplies the
initial continuity needed by the bootstrap. -/
theorem contDiffOn_infty_of_hasFDerivAt_eq
    {U : Set X} {g : X × Y → X →L[ℝ] Y} {w : X → Y}
    (hU : IsOpen U) (hg : ContDiff ℝ ∞ g)
    (hw : ∀ x ∈ U, HasFDerivAt w (g (x, w x)) x) :
    ContDiffOn ℝ ∞ w U :=
  contDiffOn_infty_of_hasFDerivAt_eq_on hU hg.contDiffOn (mapsTo_univ _ _) hw
