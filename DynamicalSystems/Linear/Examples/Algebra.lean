/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.Hautus
public import DynamicalSystems.Linear.Observer
public import DynamicalSystems.Linear.DisturbanceDecoupling
public import Mathlib.Data.Complex.Basic

/-! # Concrete algebraic examples for the linear-system pair APIs

This file collects the concrete, kernel-checked examples required by the
release obligations for the linear-control development. They exercise the
*public* algebraic pair API of `DynamicalSystems.Linear.Subspaces`,
`DynamicalSystems.Linear.Kalman`, `DynamicalSystems.Linear.Duality` and
`DynamicalSystems.Linear.Hautus`, together with the observer, disturbance
decoupling and trajectory APIs of `DynamicalSystems.Linear.Observer`,
`DynamicalSystems.Linear.DisturbanceDecoupling` and
`DynamicalSystems.Linear.Trajectory`.

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
  `LinearMap.isObservable_iff_hautus_complex`;
* `feedthroughSystem`: the double integrator with the **nonzero** direct
  feedthrough `D = 1`. The innovation `y - C ξ - D u` cancels `D u`, the error
  dynamics is `A - L C` and hence independent of `D`, and observability yields
  a convergent (`exists_observer_stable_attractive_of_isObservable`) observer
  (`feedthroughSystem_exists_stable_observer`);
* `decoupling_possible_velocity`, `decoupling_impossible_position` and
  `decoupling_impossible_velocity`: possible and impossible disturbance
  decoupling by state feedback on the double integrator, together with the
  static obstruction `not_isStateFeedbackDisturbanceDecoupled_of_apply_ne_zero`;
* `filterOutput` and `filterSystem`: the scalar output filter `ẏ = -c y + f`
  of the local switching-limited-tracking development, together with the
  proved representation bridge `filterOutput_eq_variationOfConstants`, which
  identifies the closed-form filter with the variation-of-constants trajectory
  of the one-dimensional `LinearSystem`.

## Norms and Gramians

The double-integrator, decoupling and rotation material is purely algebraic:
no topology, no measure theory and no inner product is used. In particular the
coordinate space `Fin n → ℝ` carries the *plain function-space* norm (the
supremum norm), which is **not** the Euclidean norm. The observer-convergence
and filter-bridge statements do use the real topology, the operator
exponential and Bochner integration, but no Gramian example is claimed here
and no statement in this file should be read as a Gramian or Hilbert-space
result.

## References

* H. L. Trentelman, A. A. Stoorvogel, M. Hautus, *Control Theory for Linear
  Systems*, Springer, 2001, Sections 3.2–3.5, 3.11, 4.2 and 6.1.
* The scalar filter source is the local draft project file
  `notes/draft_scripts/switching_limited_tracking/lean/NominalOutput.lean`.
  Its declarations `filterOutput` and `filterOutput_derivative` are ported
  verbatim; the representation bridge
  `filterOutput_eq_variationOfConstants` is new.
-/

@[expose] public section

namespace DynamicalSystems.Linear.Examples

open LinearMap Filter Topology Set MeasureTheory

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

/-! ## Nonzero-feedthrough observer

The abstract observer error analysis of `DynamicalSystems.Linear.Observer`
already handles a nonzero direct feedthrough `D : U →ₗ[ℝ] Y`. This section
instantiates it on a concrete plant that genuinely has `D ≠ 0`, demonstrating
that the innovation subtracts `D u` and that the observer error dynamics
`A - L C` is independent of `D`. Observability of the pair `(C, A)` is inherited
from the double integrator, so the existence theorem produces a convergent
observer even though a direct input term is present in the measurement. -/

/-- The identity direct feedthrough `D u = u`, a nonzero element of
`ℝ →ₗ[ℝ] ℝ`. -/
noncomputable def feedthroughD : ℝ →ₗ[ℝ] ℝ := LinearMap.id

theorem feedthroughD_ne_zero : feedthroughD ≠ 0 := by
  intro h
  have h1 := LinearMap.congr_fun h 1
  simp [feedthroughD] at h1

/-- The double integrator observed through `C (x₁, x₂) = x₁` with the nonzero
direct feedthrough `D = 1`. -/
noncomputable def feedthroughSystem : LinearSystem ℝ (ℝ × ℝ) ℝ ℝ :=
  ⟨doubleIntegratorA, doubleIntegratorB, doubleIntegratorC, feedthroughD⟩

@[simp]
theorem feedthroughSystem_A : feedthroughSystem.A = doubleIntegratorA := rfl

@[simp]
theorem feedthroughSystem_C : feedthroughSystem.C = doubleIntegratorC := rfl

@[simp]
theorem feedthroughSystem_D : feedthroughSystem.D = feedthroughD := rfl

theorem feedthroughSystem_D_ne_zero : feedthroughSystem.D ≠ 0 := feedthroughD_ne_zero

/-- The pair `(C, A)` of the feedthrough plant is observable, inherited from the
double integrator; the feedthrough `D` is irrelevant to observability. -/
theorem feedthroughSystem_observable :
    IsObservable feedthroughSystem.C feedthroughSystem.A := by
  simpa only [feedthroughSystem_C, feedthroughSystem_A] using doubleIntegrator_observable

/-- The readout of the feedthrough plant is `y = x₁ + u`, exhibiting the
nonzero direct term `D u`. This is a display lemma rather than a registered
`simp` lemma: `LinearSystem.readout_apply` and the projection lemmas already
reduce the left-hand side to `x.1 + feedthroughD u`, so the statement is not in
`simp` normal form as written. -/
theorem feedthroughSystem_readout_apply (x : ℝ × ℝ) (u : ℝ) :
    feedthroughSystem.readout x u = x.1 + u := by
  simp [LinearSystem.readout_apply, feedthroughD, doubleIntegratorC]

/-- On an exact trajectory the innovation is the readout of the estimation
error; the nonzero feedthrough `D u` cancels. -/
theorem feedthroughSystem_innovation_readout (ξ x : ℝ × ℝ) (u : ℝ) :
    feedthroughSystem.innovation ξ (feedthroughSystem.readout x u) u =
      feedthroughSystem.C (x - ξ) :=
  feedthroughSystem.innovation_readout ξ x u

/-- The naive innovation `y - C ξ` that omits the feedthrough does **not**
cancel the direct term: it leaves the residual `D u = u`. This is why the
feedthrough-aware innovation subtracts `D u`, and it is the obstruction that a
strictly proper observer formula would have to ignore. -/
theorem feedthroughSystem_naive_innovation_readout (ξ x : ℝ × ℝ) (u : ℝ) :
    feedthroughSystem.readout x u - feedthroughSystem.C ξ =
      feedthroughSystem.C (x - ξ) + feedthroughSystem.D u := by
  simp [LinearSystem.readout_apply, feedthroughD, doubleIntegratorC]
  ring

/-- The observer error dynamics `e' = (A - L C) e` on the feedthrough plant.
The right-hand side does not mention `D`, which is the algebraic content of
feedthrough cancellation. -/
theorem feedthroughSystem_observerError_dynamics (L : ℝ →ₗ[ℝ] (ℝ × ℝ))
    (ξ x : ℝ × ℝ) (u : ℝ) :
    feedthroughSystem.observerVectorField L ξ (feedthroughSystem.readout x u) u -
        feedthroughSystem.dynamics x u =
      (feedthroughSystem.A - L.comp feedthroughSystem.C) (ξ - x) :=
  feedthroughSystem.observerError_dynamics L ξ x u

/-- **A convergent observer for a nonzero-feedthrough plant.** Because the
readout pair is observable, there is an output injection `L` whose error flow
is stable and attractive at the origin; the direct feedthrough `D = 1` does not
prevent this. The gain is constructed by the general existence theorem, not
assumed. -/
theorem feedthroughSystem_exists_stable_observer :
    ∃ L : ℝ →ₗ[ℝ] (ℝ × ℝ),
      (𝓝 (0 : ℝ × ℝ)).IsStableOn (fun (t : ℝ) (x : ℝ × ℝ) =>
        NormedSpace.exp
          (t • (feedthroughSystem.A - L.comp feedthroughSystem.C).toContinuousLinearMap) x)
        (Set.Ici 0) ∧
      Filter.IsAttractive (l := 𝓝 (0 : ℝ × ℝ)) (Φ := fun (t : ℝ) (x : ℝ × ℝ) =>
        NormedSpace.exp
          (t • (feedthroughSystem.A - L.comp feedthroughSystem.C).toContinuousLinearMap) x)
        (l' := Filter.atTop) :=
  LinearMap.exists_observer_stable_attractive_of_isObservable
    feedthroughSystem.C feedthroughSystem.A feedthroughSystem_observable

/-! ## Disturbance decoupling: possible and impossible instances

The pair API of `DynamicalSystems.Linear.DisturbanceDecoupling` characterises
disturbance decoupling by state feedback as the existence of a controlled
invariant subspace between `im E` and `ker H` (Theorem 4.8). We instantiate both
outcomes on the double integrator: a velocity disturbance seen through a
position readout can be decoupled by feedback acting on the position channel,
while a position disturbance read out directly can never be decoupled. -/

/-- **A static obstruction to decoupling.** If the readout does not already
annihilate some disturbance direction, `H (E w) ≠ 0`, then no state feedback can
decouple the channel: the zeroth Markov parameter `H E` is independent of the
feedback. -/
theorem not_isStateFeedbackDisturbanceDecoupled_of_apply_ne_zero
    {𝕜 X U W Z : Type*} [Field 𝕜]
    [AddCommGroup X] [Module 𝕜 X] [AddCommGroup U] [Module 𝕜 U]
    [AddCommGroup W] [Module 𝕜 W] [AddCommGroup Z] [Module 𝕜 Z]
    (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (E : W →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z)
    (w : W) (h : H (E w) ≠ 0) :
    ¬ IsStateFeedbackDisturbanceDecoupled A B E H := by
  rintro ⟨F, hF⟩
  exact h (by simpa [disturbanceResponse] using LinearMap.congr_fun (hF 0) w)

/-- A position disturbance read out directly at the position can never be
decoupled: no state feedback changes the instantaneous term `H E = 1`. -/
theorem decoupling_impossible_position :
    ¬ IsStateFeedbackDisturbanceDecoupled doubleIntegratorStateMap
        doubleIntegratorPositionDisturbance doubleIntegratorPositionDisturbance
        doubleIntegratorPositionReadout :=
  not_isStateFeedbackDisturbanceDecoupled_of_apply_ne_zero _ _ _ _ 1 (by norm_num)

/-- A velocity disturbance seen through a position readout **can** be decoupled
by state feedback: with `u = -x₂ + v` the closed-loop state map is zero, so the
disturbance never reaches the output. -/
theorem decoupling_possible_velocity :
    IsStateFeedbackDisturbanceDecoupled doubleIntegratorStateMap
        doubleIntegratorPositionDisturbance doubleIntegratorVelocityDisturbance
        doubleIntegratorPositionReadout := by
  refine ⟨-doubleIntegratorVelocityReadout, ?_⟩
  have hA : doubleIntegratorStateMap +
      doubleIntegratorPositionDisturbance.comp (-doubleIntegratorVelocityReadout) = 0 := by
    ext <;>
      simp [doubleIntegratorStateMap, doubleIntegratorPositionDisturbance,
        doubleIntegratorVelocityReadout]
  rw [hA]
  refine isDisturbanceDecoupled_of_map_range_eq_bot 0 _ _ ?_ ?_
  · simp
  · intro x hx
    obtain ⟨d, rfl⟩ := hx
    simp [doubleIntegratorVelocityDisturbance, doubleIntegratorPositionReadout]

/-- Even when `H E = 0`, decoupling can fail for a structural reason. With the
input and the disturbance both entering the velocity channel of the double
integrator, the position readout sees the disturbance after one step, and no
state feedback can remove it. -/
theorem decoupling_impossible_velocity :
    ¬ IsStateFeedbackDisturbanceDecoupled doubleIntegratorStateMap
        doubleIntegratorVelocityDisturbance doubleIntegratorVelocityDisturbance
        doubleIntegratorPositionReadout := by
  rintro ⟨F, hF⟩
  have hresp : ∀ w : ℝ,
      disturbanceResponse (doubleIntegratorStateMap +
          doubleIntegratorVelocityDisturbance.comp F)
        doubleIntegratorVelocityDisturbance doubleIntegratorPositionReadout 1 w = w := by
    intro w
    have hstep : (doubleIntegratorStateMap +
        doubleIntegratorVelocityDisturbance.comp F) (0, w) = (w, F (0, w)) := by
      ext <;> simp [doubleIntegratorStateMap, doubleIntegratorVelocityDisturbance]
    simp only [disturbanceResponse, pow_one, LinearMap.comp_apply,
      doubleIntegratorVelocityDisturbance_apply, hstep,
      doubleIntegratorPositionReadout_apply]
  have h1 := hresp 1
  rw [hF 1] at h1
  norm_num at h1

/-! ## Application bridge: the scalar output filter

The scalar first-order filter `ẏ = -c y + f` used by the local
switching-limited-tracking development is ported here and connected to the
abstract `LinearSystem` API. The filter is represented by the one-dimensional
system whose state map is multiplication by `-c` and whose input map is the
identity; the bridge theorem `filterOutput_eq_variationOfConstants` states that
the closed-form filter output is exactly the variation-of-constants trajectory
of that system.

Source: `notes/draft_scripts/switching_limited_tracking/lean/NominalOutput.lean`,
declarations `filterOutput` and `filterOutput_derivative`. The port keeps those
two statements and adds the representation bridge; no other result of that
separate project is imported or assumed. -/

/-- The scalar filter output
`y(t) = exp (-c t) (y₀ + ∫₀ᵗ exp (c s) f(s) ds)`, the solution of
`ẏ = -c y + f` with `y(0) = y₀`. -/
noncomputable def filterOutput (c y0 : ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-c * t) * (y0 + ∫ u in (0 : ℝ)..t, Real.exp (c * u) * f u)

/-- Evaluation lemma for `filterOutput`. -/
theorem filterOutput_apply (c y0 : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    filterOutput c y0 f t =
      Real.exp (-c * t) * (y0 + ∫ u in (0 : ℝ)..t, Real.exp (c * u) * f u) :=
  rfl

theorem exp_cancel (c t : ℝ) : Real.exp (-c * t) * Real.exp (c * t) = 1 := by
  rw [← Real.exp_add, show -c * t + c * t = 0 by ring, Real.exp_zero]

/-- The filter output at time `0` is the initial condition. -/
@[simp]
theorem filterOutput_initial (c y0 : ℝ) (f : ℝ → ℝ) :
    filterOutput c y0 f 0 = y0 := by
  simp [filterOutput]

/-- The filter output obeys `ẏ = f - c y` at every time. This is the ported
`filterOutput_derivative` of the local switching-limited-tracking development. -/
theorem filterOutput_derivative (c y0 : ℝ) (f : ℝ → ℝ) (hf : Continuous f) (t : ℝ) :
    HasDerivAt (filterOutput c y0 f) (f t - c * filterOutput c y0 f t) t := by
  have hw : Continuous (fun u : ℝ => Real.exp (c * u) * f u) := by fun_prop
  have hi := intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable 0 t)
    hw.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuousAt
  have hd := (((hasDerivAt_id t).const_mul (-c)).exp).mul (hi.const_add y0)
  change HasDerivAt (fun t => Real.exp (-c * t) *
    (y0 + ∫ u in (0 : ℝ)..t, Real.exp (c * u) * f u)) _ t
  convert hd using 1 <;> try rfl
  simp only [id_eq, mul_one, filterOutput]
  rw [show Real.exp (-c * t) * (Real.exp (c * t) * f t) = f t by
    rw [← mul_assoc, exp_cancel, one_mul]]
  ring

/-- The filter output is continuous for continuous input. -/
theorem filterOutput_continuous (c y0 : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (filterOutput c y0 f) :=
  continuous_iff_continuousAt.mpr fun t =>
    (filterOutput_derivative c y0 f hf t).continuousAt

/-- The state map of the one-dimensional filter, `y ↦ -c y`. -/
noncomputable def filterStateMap (c : ℝ) : ℝ →ₗ[ℝ] ℝ where
  toFun y := -c * y
  map_add' y z := by ring
  map_smul' a y := by
    change -c * (a * y) = a * (-c * y)
    ring

@[simp]
theorem filterStateMap_apply (c y : ℝ) : filterStateMap c y = -c * y := rfl

/-- The one-dimensional `LinearSystem` representing the scalar filter:
`ẏ = -c y + u`, with full state readout and no feedthrough. -/
noncomputable def filterSystem (c : ℝ) : LinearSystem ℝ ℝ ℝ ℝ where
  A := filterStateMap c
  B := LinearMap.id
  C := LinearMap.id
  D := 0

theorem filterSystem_dynamics_apply (c y u : ℝ) :
    (filterSystem c).dynamics y u = u - c * y := by
  rw [LinearSystem.dynamics_apply]
  simp [filterSystem, filterStateMap]
  ring_nf

/-- The filter output satisfies the integral equation of the abstract
one-dimensional system. -/
theorem filterOutput_integral (c y0 : ℝ) (f : ℝ → ℝ) (hf : Continuous f) (t : ℝ) :
    filterOutput c y0 f t =
      y0 + ∫ s in (0 : ℝ)..t,
        (filterSystem c).dynamics (filterOutput c y0 f s) (f s) := by
  have hcont : Continuous (fun s : ℝ =>
      (filterSystem c).dynamics (filterOutput c y0 f s) (f s)) := by
    simp only [filterSystem_dynamics_apply]
    exact hf.sub (continuous_const.mul (filterOutput_continuous c y0 f hf))
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) t,
      HasDerivAt (filterOutput c y0 f)
        ((filterSystem c).dynamics (filterOutput c y0 f s) (f s)) s := by
    intro s _
    rw [filterSystem_dynamics_apply]
    exact filterOutput_derivative c y0 f hf s
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable (0 : ℝ) t)
  rw [filterOutput_initial] at h
  linarith

/-- **Representation bridge.** The closed-form scalar filter output is exactly
the variation-of-constants trajectory of the abstract one-dimensional
`LinearSystem`. This is the proved equivalence between the local filter result
and the library's trajectory API. -/
theorem filterOutput_eq_variationOfConstants (c y0 : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f) :
    filterOutput c y0 f =
      (filterSystem c).variationOfConstants 0 y0 f := by
  have hf_loc : LocallyIntegrable f volume := hf.locallyIntegrable
  exact LinearSystem.integralSolution_unique (filterSystem c) 0 y0 f hf_loc
    (filterOutput_continuous c y0 f hf) (filterOutput_initial c y0 f)
    (filterOutput_integral c y0 f hf)
    (LinearSystem.continuous_variationOfConstants (filterSystem c) 0 y0 f hf_loc)
    (LinearSystem.variationOfConstants_self (filterSystem c) 0 y0 f)
    (fun t => LinearSystem.variationOfConstants_integral (filterSystem c) 0 y0 f hf_loc t)

end DynamicalSystems.Linear.Examples
