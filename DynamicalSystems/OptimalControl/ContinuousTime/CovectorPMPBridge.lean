/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.MinimumPrinciple
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# From a separated covector to the existing vector PMP predicates

The geometric construction naturally produces a covector-valued adjoint.
Transport through the Riesz isometry gives a vector costate. The actual spatial
derivatives identify its ODE with the repository's Hamiltonian-gradient costate
equation. Terminal equality and needle generator inequalities then give the
other two project predicates.
-/

@[expose] public section

open Set


variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Riesz representation of a covector-valued curve. -/
noncomputable def vectorCostate (q : ℝ → E →L[ℝ] ℝ) (t : ℝ) : E :=
  (InnerProductSpace.toDual ℝ E).symm (q t)

@[simp] theorem inner_vectorCostate
    (q : ℝ → E →L[ℝ] ℝ) (t : ℝ) (z : E) :
    inner ℝ (vectorCostate q t) z = q t z := by
  change InnerProductSpace.toDual ℝ E ((InnerProductSpace.toDual ℝ E).symm (q t)) z = q t z
  rw [(InnerProductSpace.toDual ℝ E).apply_symm_apply]

/-- Actual spatial derivatives and the dual adjoint equation give the exact
gradient-based costate equation used by the project. -/
theorem costateEquation_of_covector
    (prob : ContinuousOCP E U) (x : ℝ → E) (u : ℝ → U)
    (q : ℝ → E →L[ℝ] ℝ) (A : ℝ → E →L[ℝ] E) (ell : ℝ → E →L[ℝ] ℝ)
    (hq : ∀ t ∈ Icc 0 prob.T,
      HasDerivAt q (-(ell t + (q t).comp (A t))) t)
    (hf : ∀ t ∈ Icc 0 prob.T,
      HasFDerivAt (fun y => prob.f t y (u t)) (A t) (x t))
    (hL : ∀ t ∈ Icc 0 prob.T,
      HasFDerivAt (fun y => prob.L t y (u t)) (ell t) (x t)) :
    costateEquation prob.L prob.f prob.T x u (vectorCostate q) := by
  intro t ht
  have hH : HasFDerivAt
      (fun y => hamiltonianOf prob.L prob.f t y (u t) (vectorCostate q t))
      (ell t + (q t).comp (A t)) (x t) := by
    simp only [hamiltonianOf, inner_vectorCostate]
    exact (hL t ht).add ((q t).hasFDerivAt.comp (x t) (hf t ht))
  let R : (E →L[ℝ] ℝ) →L[ℝ] E :=
    (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hp := R.hasFDerivAt.comp_hasDerivAt t (hq t ht)
  change HasDerivAt (vectorCostate q)
    ((InnerProductSpace.toDual ℝ E).symm (-(ell t + (q t).comp (A t)))) t at hp
  rw [hH.hasGradientAt.gradient]
  simpa only [map_neg] using hp

/-- A differentiated terminal cost turns the terminal covector into the
existing terminal-gradient condition. -/
theorem transversalityCondition_of_covector
    (prob : ContinuousOCP E U) (x : ℝ → E) (q : ℝ → E →L[ℝ] ℝ) (k : E →L[ℝ] ℝ)
    (hqT : q prob.T = k) (hK : HasFDerivAt prob.K k (x prob.T)) :
    transversalityCondition prob.K prob.T x (vectorCostate q) := by
  change (InnerProductSpace.toDual ℝ E).symm (q prob.T) = gradient prob.K (x prob.T)
  rw [hqT, hK.hasGradientAt.gradient]

/-- Nonnegative needle-generator pairings give pointwise Hamiltonian
minimization for the Riesz-represented costate. -/
theorem HamiltonianMinimizing_of_covector
    (prob : ContinuousOCP E U) (x : ℝ → E) (u : ℝ → U) (q : ℝ → E →L[ℝ] ℝ)
    (hneedle : ∀ t ∈ Icc 0 prob.T, ∀ v ∈ prob.controlSet,
      0 ≤ prob.L t (x t) v - prob.L t (x t) (u t) +
        q t (prob.f t (x t) v - prob.f t (x t) (u t))) :
    HamiltonianMinimizing prob.L prob.f prob.controlSet prob.T x u (vectorCostate q) := by
  intro t ht v hv
  have h := hneedle t ht v hv
  simp only [hamiltonianOf, inner_vectorCostate]
  rw [map_sub] at h
  linarith

/-- Complete adapter from the covector conclusions of geometric separation
to all three existing project PMP predicates. -/
theorem _root_.pmpConditions_of_covector
    (prob : ContinuousOCP E U) (x : ℝ → E) (u : ℝ → U)
    (q : ℝ → E →L[ℝ] ℝ) (A : ℝ → E →L[ℝ] E) (ell : ℝ → E →L[ℝ] ℝ)
    (k : E →L[ℝ] ℝ)
    (hq : ∀ t ∈ Icc 0 prob.T,
      HasDerivAt q (-(ell t + (q t).comp (A t))) t)
    (hqT : q prob.T = k)
    (hf : ∀ t ∈ Icc 0 prob.T,
      HasFDerivAt (fun y => prob.f t y (u t)) (A t) (x t))
    (hL : ∀ t ∈ Icc 0 prob.T,
      HasFDerivAt (fun y => prob.L t y (u t)) (ell t) (x t))
    (hK : HasFDerivAt prob.K k (x prob.T))
    (hneedle : ∀ t ∈ Icc 0 prob.T, ∀ v ∈ prob.controlSet,
      0 ≤ prob.L t (x t) v - prob.L t (x t) (u t) +
        q t (prob.f t (x t) v - prob.f t (x t) (u t))) :
    costateEquation prob.L prob.f prob.T x u (vectorCostate q) ∧
      transversalityCondition prob.K prob.T x (vectorCostate q) ∧
      HamiltonianMinimizing prob.L prob.f prob.controlSet prob.T x u (vectorCostate q) := by
  exact ⟨costateEquation_of_covector prob x u q A ell hq hf hL,
    transversalityCondition_of_covector prob x q k hqT hK,
    HamiltonianMinimizing_of_covector prob x u q hneedle⟩

