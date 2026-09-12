/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.Hautus
public import Mathlib.Data.Complex.Basic

/-! # Concrete algebraic examples for the linear-system pair APIs

This file collects the concrete, kernel-checked examples required by the
release obligations for the linear-control development. They exercise the
*public* algebraic pair API of `DynamicalSystems.Linear.Subspaces`,
`DynamicalSystems.Linear.Kalman`, `DynamicalSystems.Linear.Duality` and
`DynamicalSystems.Linear.Hautus`, rather than re-deriving the general theory.

## Contents

* `doubleIntegratorA`, `doubleIntegratorB`, `doubleIntegratorC`: the double
  integrator `A (x₁, x₂) = (x₂, 0)`, `B u = (0, u)`, `C (x₁, x₂) = x₁`,
  with `doubleIntegrator_controllable` and `doubleIntegrator_observable`;
* `uncontrollableA`: a nonzero input map that cannot reach all states, with
  `uncontrollable_not_controllable`;
* `unobservableC`: a nonzero readout with nontrivial unobservable subspace,
  with `unobservable_not_observable`;
* `doubleIntegratorSystem` and the coordinate swap `stateSwap`, transported
  through `LinearSystem.changeState`, with explicit formulas for the
  transformed maps;
* `zeroDim_controllable`, `zeroDim_observable`: the zero-dimensional case;
* the real rotation `rotationA = [[0, -1], [1, 0]]` with zero readout
  `rotationC = 0`. The pair is not observable, and the failure is witnessed at
  the **non-real** complex eigenvalue `Complex.I` with eigenvector `(I, 1)`.
  This exercises the real PBH complexification bridge
  `LinearMap.isObservable_complexify_iff` /
  `LinearMap.isObservable_iff_hautus_complex`.

## Norms and Gramians

Everything in this file is purely algebraic: no topology, no measure theory
and no inner product is used. In particular the coordinate space `Fin n → ℝ`
carries the *plain function-space* norm (the supremum norm), which is **not**
the Euclidean norm. No Gramian example is claimed here, and no statement in
this file should be read as a Gramian or Hilbert-space result.

## References

* H. L. Trentelman, A. A. Stoorvogel, M. Hautus, *Control Theory for Linear
  Systems*, Springer, 2001, Sections 3.2–3.5.
-/

@[expose] public section

namespace DynamicalSystems.Linear.Examples

open LinearMap

/-! ## The double integrator -/

/-- State map of the double integrator: `A (x₁, x₂) = (x₂, 0)`. -/
noncomputable def doubleIntegratorA : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  (LinearMap.snd ℝ ℝ ℝ).prod 0

/-- Input map of the double integrator: `B u = (0, u)`. -/
noncomputable def doubleIntegratorB : ℝ →ₗ[ℝ] (ℝ × ℝ) :=
  (0 : ℝ →ₗ[ℝ] ℝ).prod LinearMap.id

/-- Readout of the double integrator: `C (x₁, x₂) = x₁`. -/
noncomputable def doubleIntegratorC : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.fst ℝ ℝ ℝ

@[simp]
theorem doubleIntegratorA_apply (x : ℝ × ℝ) :
    doubleIntegratorA x = (x.2, 0) := rfl

@[simp]
theorem doubleIntegratorB_apply (u : ℝ) :
    doubleIntegratorB u = (0, u) := rfl

@[simp]
theorem doubleIntegratorC_apply (x : ℝ × ℝ) :
    doubleIntegratorC x = x.1 := rfl

/-- The double integrator is controllable: `(x₁, x₂) = A (B x₁) + B x₂`. -/
theorem doubleIntegrator_controllable :
    IsControllable doubleIntegratorA doubleIntegratorB := by
  rw [isControllable_iff, eq_top_iff]
  rintro ⟨x₁, x₂⟩ -
  have h₁ : (x₁, 0) ∈ reachableSubspace doubleIntegratorA doubleIntegratorB := by
    simpa using mem_reachableSubspace_of_mem doubleIntegratorA doubleIntegratorB 1 x₁
  have h₂ : (0, x₂) ∈ reachableSubspace doubleIntegratorA doubleIntegratorB := by
    simpa using mem_reachableSubspace_of_mem doubleIntegratorA doubleIntegratorB 0 x₂
  simpa using Submodule.add_mem _ h₁ h₂

/-- The double integrator is observable: a state annihilated by `C` and `C A`
is zero. -/
theorem doubleIntegrator_observable :
    IsObservable doubleIntegratorC doubleIntegratorA := by
  rw [isObservable_iff, Submodule.eq_bot_iff]
  rintro ⟨x₁, x₂⟩ hx
  rw [mem_unobservableSubspace] at hx
  have h₀ : x₁ = 0 := by
    simpa using hx 0
  have h₁ : x₂ = 0 := by
    simpa using hx 1
  exact Prod.ext h₀ h₁

/-! ## Uncontrollable and unobservable variants -/

/-- The zero state map. Together with the double-integrator input `B` it leaves
the first coordinate unreachable. -/
noncomputable def uncontrollableA : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) := 0

@[simp]
theorem uncontrollableA_apply (x : ℝ × ℝ) :
    uncontrollableA x = 0 := rfl

/-- This one-dimensional input cannot compensate the zero state map: `(1, 0)` is never
reachable, so the pair is not controllable. -/
theorem uncontrollable_not_controllable :
    ¬ IsControllable uncontrollableA doubleIntegratorB := by
  intro h
  have hle : reachableSubspace uncontrollableA doubleIntegratorB ≤
      LinearMap.range (LinearMap.inr ℝ ℝ ℝ) := by
    refine reachableSubspace_le _ _ ?_ ?_
    · rintro _ ⟨u, rfl⟩
      exact ⟨u, by simp [LinearMap.inr]⟩
    · rintro _ ⟨x, _hx, rfl⟩
      simp
  have hmem : (1, 0) ∈ reachableSubspace uncontrollableA doubleIntegratorB := by
    rw [h]
    exact Submodule.mem_top
  obtain ⟨y, hy⟩ := hle hmem
  simp [LinearMap.inr] at hy

/-- Output map that only reads the second coordinate: with the double-integrator
state map the state `(1, 0)` is unobservable. -/
noncomputable def unobservableC : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.snd ℝ ℝ ℝ

@[simp]
theorem unobservableC_apply (x : ℝ × ℝ) :
    unobservableC x = x.2 := rfl

/-- The output `C (x₁, x₂) = x₂` is blind to the first coordinate, so the pair
is not observable; the witness is `(1, 0)` with eigenvalue `0`. -/
theorem unobservable_not_observable :
    ¬ IsObservable unobservableC doubleIntegratorA :=
  hautus_witness_implies_not_isObservable unobservableC doubleIntegratorA 0 (1, 0)
    (by simp) (by simp) (by simp)

/-! ## Transport through a nontrivial state equivalence -/

/-- The double integrator as a bundled `LinearSystem` with zero feedthrough. -/
noncomputable def doubleIntegratorSystem : LinearSystem ℝ (ℝ × ℝ) ℝ ℝ :=
  ⟨doubleIntegratorA, doubleIntegratorB, doubleIntegratorC, 0⟩

/-- The coordinate swap `(x₁, x₂) ↦ (x₂, x₁)`, a nontrivial state-space
equivalence. -/
noncomputable def stateSwap : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) :=
  LinearEquiv.prodComm ℝ ℝ ℝ

@[simp]
theorem stateSwap_apply (x : ℝ × ℝ) :
    stateSwap x = (x.2, x.1) := rfl

theorem stateSwap_nontrivial : stateSwap (1, 0) = (0, 1) := by
  simp

/-- The transformed state map is `(x₁, x₂) ↦ (0, x₁)`. -/
theorem transportedA_apply (x : ℝ × ℝ) :
    (doubleIntegratorSystem.changeState stateSwap).A x = (0, x.1) := by
  simp [LinearSystem.changeState, stateSwap, doubleIntegratorSystem, doubleIntegratorA]

/-- The transformed input map is `u ↦ (u, 0)`. -/
theorem transportedB_apply (u : ℝ) :
    (doubleIntegratorSystem.changeState stateSwap).B u = (u, 0) := by
  simp [LinearSystem.changeState, stateSwap, doubleIntegratorSystem, doubleIntegratorB]

/-- The transformed readout is `(x₁, x₂) ↦ x₂`. -/
theorem transportedC_apply (x : ℝ × ℝ) :
    (doubleIntegratorSystem.changeState stateSwap).C x = x.2 := by
  simp [LinearSystem.changeState, doubleIntegratorSystem, doubleIntegratorC]

/-- Controllability is preserved by the nontrivial coordinate swap. -/
theorem transported_controllable :
    IsControllable (doubleIntegratorSystem.changeState stateSwap).A
      (doubleIntegratorSystem.changeState stateSwap).B :=
  (LinearSystem.isControllable_changeState doubleIntegratorSystem stateSwap).mp
    doubleIntegrator_controllable

/-- Observability is preserved by the nontrivial coordinate swap. -/
theorem transported_observable :
    IsObservable (doubleIntegratorSystem.changeState stateSwap).C
      (doubleIntegratorSystem.changeState stateSwap).A :=
  (LinearSystem.isObservable_changeState doubleIntegratorSystem stateSwap).mp
    doubleIntegrator_observable

/-! ## The zero-dimensional case -/

/-- The zero-dimensional real state space. -/
abbrev ZeroState : Type := Fin 0 → ℝ

/-- Every pair on the zero-dimensional space is controllable, since the space
is a subsingleton. -/
theorem zeroDim_controllable :
    IsControllable (0 : ZeroState →ₗ[ℝ] ZeroState)
      (0 : ZeroState →ₗ[ℝ] ZeroState) := by
  rw [isControllable_iff, eq_top_iff]
  intro x _
  rw [Subsingleton.elim x 0]
  exact Submodule.zero_mem _

/-- Every pair on the zero-dimensional space is observable, since the space is
a subsingleton. -/
theorem zeroDim_observable :
    IsObservable (0 : ZeroState →ₗ[ℝ] ZeroState)
      (0 : ZeroState →ₗ[ℝ] ZeroState) := by
  rw [isObservable_iff, Submodule.eq_bot_iff]
  intro x _
  exact Subsingleton.elim x 0

/-- The finite Kalman controllability test also handles the empty state space. -/
theorem zeroDim_kalman_surjective :
    Function.Surjective (kalmanControllabilityMap (0 : ZeroState →ₗ[ℝ] ZeroState)
      (0 : ZeroState →ₗ[ℝ] ZeroState) (Module.finrank ℝ ZeroState)) :=
  (isControllable_iff_surjective_kalmanControllabilityMap _ _).mp zeroDim_controllable

/-- The finite observability test has no exceptional positive-dimension hypothesis. -/
theorem zeroDim_kalman_injective :
    Function.Injective (kalmanObservabilityMap (0 : ZeroState →ₗ[ℝ] ZeroState)
      (0 : ZeroState →ₗ[ℝ] ZeroState) (Module.finrank ℝ ZeroState)) :=
  (isObservable_iff_injective_kalmanObservabilityMap _ _).mp zeroDim_observable

/-! ## A real rotation with zero readout: non-real PBH witness -/

/-- The real rotation matrix `[[0, -1], [1, 0]]`. -/
noncomputable def rotationA : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

/-- The zero readout. -/
noncomputable def rotationC : Matrix (Fin 1) (Fin 2) ℝ := 0

/-- The complex eigenvector `(I, 1)` of the rotation at eigenvalue `I`. -/
noncomputable def rotationWitness : Fin 2 → ℂ := ![Complex.I, 1]

theorem rotationWitness_ne_zero : rotationWitness ≠ 0 := by
  intro hv
  have h0 := congrFun hv 0
  simp [rotationWitness] at h0

theorem rotationA_complex_mulVec :
    (Matrix.mulVecLin (rotationA.map (algebraMap ℝ ℂ))) rotationWitness =
      Complex.I • rotationWitness := by
  ext i
  fin_cases i <;> simp [rotationA, rotationWitness, Matrix.mulVec, dotProduct]

theorem rotationC_complex_mulVec :
    (Matrix.mulVecLin (rotationC.map (algebraMap ℝ ℂ))) rotationWitness = 0 := by
  simp [rotationC]

/-- The complexified rotation with zero readout is not observable: the
eigenvector `(I, 1)` at the non-real eigenvalue `I` lies in the kernel of the
Hautus map. -/
theorem rotation_complex_not_observable :
    ¬ IsObservable (Matrix.mulVecLin (rotationC.map (algebraMap ℝ ℂ)))
      (Matrix.mulVecLin (rotationA.map (algebraMap ℝ ℂ))) :=
  hautus_witness_implies_not_isObservable _ _ Complex.I rotationWitness
    rotationWitness_ne_zero rotationA_complex_mulVec rotationC_complex_mulVec

/-- The real rotation with zero readout is not observable, transported through
the real-matrix complexification bridge `isObservable_complexify_iff`. -/
theorem rotation_real_not_observable :
    ¬ IsObservable (Matrix.mulVecLin rotationC) (Matrix.mulVecLin rotationA) := by
  intro h
  exact rotation_complex_not_observable
    ((isObservable_complexify_iff rotationC rotationA).mp h)

/-- The witness `(I, 1)` lies in the kernel of the complexified Hautus
observability map at `μ = I`. -/
theorem rotationWitness_mem_hautus_ker :
    rotationWitness ∈ ker (hautusObservabilityMap
      (Matrix.mulVecLin (rotationC.map (algebraMap ℝ ℂ)))
      (Matrix.mulVecLin (rotationA.map (algebraMap ℝ ℂ))) Complex.I) := by
  rw [ker_hautusObservabilityMap]
  exact Submodule.mem_inf.mpr
    ⟨Module.End.mem_eigenspace_iff.mpr rotationA_complex_mulVec,
      mem_ker.mpr rotationC_complex_mulVec⟩

/-- The real PBH criterion fails at the complex eigenvalue `I`, so the real pair
is not observable. This is the real PBH corollary form of
`rotation_real_not_observable`. -/
theorem rotation_real_not_observable_hautus :
    ¬ IsObservable (Matrix.mulVecLin rotationC) (Matrix.mulVecLin rotationA) := by
  rw [isObservable_iff_hautus_complex]
  intro h
  have hmem := rotationWitness_mem_hautus_ker
  rw [h Complex.I] at hmem
  exact rotationWitness_ne_zero (by simpa using hmem)

/-- The witnessing eigenvalue is genuinely non-real: it is not the image of a
real scalar under the embedding `ℝ → ℂ`. -/
theorem rotationWitness_eigenvalue_not_real :
    ¬ ∃ r : ℝ, (r : ℂ) = Complex.I := by
  rintro ⟨r, hr⟩
  have h := congrArg Complex.im hr
  simp at h

end DynamicalSystems.Linear.Examples
