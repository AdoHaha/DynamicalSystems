/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.Stabilization
public import DynamicalSystems.Linear.Trajectory

/-! # Luenberger state observers for real linear systems

This file develops the observer theory of Trentelman, Stoorvogel and Hautus,
*Control Theory for Linear Systems*, Section 3.11, on top of the accepted
trajectory API and the stabilization results of
`DynamicalSystems.Linear.Stabilization`.

The plant is

```
x' = A x + B u,
y  = C x + D u.
```

A Luenberger observer with output-injection gain `L` is the finite-dimensional
linear system

```
ξ' = A ξ + B u + L (y - C ξ - D u),
```

whose input is the pair `(u, y)` and whose state `ξ` estimates `x`. The term
`y - C ξ - D u` is the *feedthrough-aware innovation*: subtracting `D u` is
essential because the readout has a direct input term, and omitting it would
leave a copy of `u` in the error dynamics.

## Main results

* `LinearSystem.innovation`: the feedthrough-aware innovation `y - C ξ - D u`.
* `LinearSystem.innovation_readout`: on an exact trajectory
  (`y = C x + D u`) the innovation is `C (x - ξ)`.
* `LinearSystem.observerVectorField`: the observer right-hand side.
* `LinearSystem.observerError_dynamics`: the *pointwise algebraic* error
  dynamics `ξ' - x' = (A - L C) (ξ - x)`. The feedthrough `D` cancels exactly,
  so the error is driven only by the observer injection and is independent of
  the input `u` and of any state feedback.
* `LinearSystem.observerError_dynamics_stateFeedback`: with state feedback
  `u = F ξ` the error still obeys `e' = (A - L C) e`.
* `LinearSystem.separation_error_independent_of_feedback`: the observer error
  dynamics does not depend on the state-feedback gain `F`. This is the
  algebraic content of the separation principle.
* `LinearMap.exists_observer_attractive_of_isObservable`: from observability,
  there is an injection `L` whose error flow is attractive at the origin. The
  gain is built by dual pole placement and the decay is derived from the
  `(X + 1)^n` characteristic polynomial, so the observer really converges.
* `LinearMap.exists_observer_stable_attractive_of_isObservable`: the same
  construction gives an observer whose error flow is simultaneously Lyapunov
  stable and attractive, the full asymptotic-stability statement for the
  Luenberger observer.
* `LinearMap.separation_principle_observer`: if `F` stabilizes the state dynamics and `L`
  yields a convergent observer error, then the assembled closed-loop block
  operator `[[A + B F, B F], [0, A - L C]]` of the observer-based controller is
  Hurwitz. This is the spectral form of the separation principle and is derived
  from `LinearMap.charpoly_blockOperator`.
* `LinearMap.not_unobservableEigenvalue_of_isDetectable`: conversely, a convergent observer
  excludes unobservable eigenvalues in the closed right half-plane, restating
  `LinearMap.isDetectable_converse_of_unobservableEigenvalue` in observer
  vocabulary.

## References

* H. L. Trentelman, A. A. Stoorvogel, M. Hautus, *Control Theory for Linear
  Systems*, Springer, 2001, Section 3.11, equations (3.40)–(3.43).
-/

@[expose] public section

open LinearMap Filter Topology
open scoped Topology

namespace LinearSystem

variable {X U Y : Type*}
variable [AddCommGroup X] [Module ℝ X]
variable [AddCommGroup U] [Module ℝ U]
variable [AddCommGroup Y] [Module ℝ Y]

/-! ## Feedthrough-aware innovation -/

/-- The **innovation** of a Luenberger observer: the difference between the
measured output `y` and the estimated output `C ξ + D u`. Subtracting the
feedthrough term `D u` is what makes the error dynamics free of the input.

Source: Trentelman–Stoorvogel–Hautus, Section 3.11, the term `y - η` with
`η = C ξ` for the strictly proper case and equation (3.42). -/
noncomputable def innovation (sys : LinearSystem ℝ X U Y) (ξ : X) (y : Y) (u : U) : Y :=
  y - sys.C ξ - sys.D u

/-- Evaluation lemma for `LinearSystem.innovation`. -/
@[simp]
theorem innovation_apply (sys : LinearSystem ℝ X U Y) (ξ : X) (y : Y) (u : U) :
    sys.innovation ξ y u = y - sys.C ξ - sys.D u := rfl

/-- On an exact plant trajectory the innovation collapses to the output of the
estimation error, `C (x - ξ)`. This is where the feedthrough `D u` cancels:
`C x + D u - C ξ - D u = C (x - ξ)`. -/
theorem innovation_readout (sys : LinearSystem ℝ X U Y) (ξ x : X) (u : U) :
    sys.innovation ξ (sys.readout x u) u = sys.C (x - ξ) := by
  simp only [innovation_apply, readout_apply, map_sub]
  abel

/-- The innovation vanishes when the estimate is exact. -/
theorem innovation_self (sys : LinearSystem ℝ X U Y) (x : X) (u : U) :
    sys.innovation x (sys.readout x u) u = 0 := by
  rw [innovation_readout]
  simp

/-! ## The observer vector field and the error dynamics -/

/-- The right-hand side of the Luenberger observer
`ξ' = A ξ + B u + L (y - C ξ - D u)`. -/
noncomputable def observerVectorField (sys : LinearSystem ℝ X U Y) (L : Y →ₗ[ℝ] X)
    (ξ : X) (y : Y) (u : U) : X :=
  sys.A ξ + sys.B u + L (sys.innovation ξ y u)

/-- Evaluation lemma for `LinearSystem.observerVectorField`. -/
@[simp]
theorem observerVectorField_apply (sys : LinearSystem ℝ X U Y) (L : Y →ₗ[ℝ] X)
    (ξ : X) (y : Y) (u : U) :
    sys.observerVectorField L ξ y u = sys.A ξ + sys.B u + L (sys.innovation ξ y u) :=
  rfl

/-- The observer can be rewritten in the familiar form
`ξ' = A ξ + B u + L (y - C ξ - D u)`, i.e. the innovation is used directly. -/
theorem observerVectorField_eq (sys : LinearSystem ℝ X U Y) (L : Y →ₗ[ℝ] X)
    (ξ : X) (y : Y) (u : U) :
    sys.observerVectorField L ξ y u
      = sys.A ξ + sys.B u + L (y - sys.C ξ - sys.D u) := rfl

/-- **Pointwise observer error dynamics.** If `(x, u)` satisfies the plant
equation with readout `y = C x + D u`, then the observer error `ξ - x` evolves
according to the homogeneous linear equation with state map `A - L C`:

`ξ' - x' = (A - L C) (ξ - x)`.

The proof is the algebraic cancellation of the input term `B u` and of the
feedthrough `D u`. This is a genuine statement about the right-hand sides, not
an assumed solution formula.

Source: Trentelman–Stoorvogel–Hautus, Section 3.11, equation (3.43). -/
theorem observerError_dynamics (sys : LinearSystem ℝ X U Y) (L : Y →ₗ[ℝ] X)
    (ξ x : X) (u : U) :
    sys.observerVectorField L ξ (sys.readout x u) u - sys.dynamics x u
      = (sys.A - L.comp sys.C) (ξ - x) := by
  simp only [observerVectorField_apply, innovation_readout, dynamics_apply,
    LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
  abel

/-- **Observer error dynamics under state feedback.** When the observer-based
controller applies `u = F ξ`, the plant reads `x' = A x + B (F ξ)` and the
observer reads `ξ' = A ξ + B (F ξ) + L (y - C ξ - D (F ξ))`. The error still
obeys `e' = (A - L C) e`, with no residual `F`-dependence.

This is the algebraic separation of the state-feedback and observer designs.

Source: Trentelman–Stoorvogel–Hautus, Section 3.12, the derivation of
equation (3.44) and the following error equation. -/
theorem observerError_dynamics_stateFeedback (sys : LinearSystem ℝ X U Y)
    (L : Y →ₗ[ℝ] X) (F : X →ₗ[ℝ] U) (ξ x : X) :
    sys.observerVectorField L ξ (sys.readout x (F ξ)) (F ξ) - sys.dynamics x (F ξ)
      = (sys.A - L.comp sys.C) (ξ - x) :=
  sys.observerError_dynamics L ξ x (F ξ)

/-- **Separation principle (algebraic form).** The error right-hand side is
independent of the state-feedback gain: the same observer injection `L` yields
the error map `A - L C` for every feedback `F`. Thus the observer design can be
carried out without reference to the stabilization gain. -/
theorem separation_error_independent_of_feedback (sys : LinearSystem ℝ X U Y)
    (L : Y →ₗ[ℝ] X) (F₁ F₂ : X →ₗ[ℝ] U) (ξ x : X) :
    sys.observerVectorField L ξ (sys.readout x (F₁ ξ)) (F₁ ξ) - sys.dynamics x (F₁ ξ)
      = sys.observerVectorField L ξ (sys.readout x (F₂ ξ)) (F₂ ξ)
        - sys.dynamics x (F₂ ξ) := by
  rw [observerError_dynamics_stateFeedback, observerError_dynamics_stateFeedback]

/-- The observer error dynamics `e' = (A - L C) e` is detected (rendered
attractive) exactly when the output injection `L` makes `A - L C` Hurwitz, i.e.
when `(C, A)` is detectable. This records the definitional bridge between the
observer and the stabilization side; existence of such an `L` is proved in
`LinearMap.isDetectable_of_isObservable`. -/
theorem exists_stable_observer_iff_isDetectable [FiniteDimensional ℝ X]
    (sys : LinearSystem ℝ X U Y) :
    (∃ L : Y →ₗ[ℝ] X, IsHurwitz (sys.A - L.comp sys.C)) ↔
      IsDetectable sys.C sys.A :=
  Iff.rfl

end LinearSystem

namespace LinearMap

/-! ## Convergence of the observer error

The decay bridge of `DynamicalSystems.Linear.Stabilization` applies to the
error map `A - L C`. The observer gain produced from observability by the dual
pole-placement argument has characteristic polynomial `(X + 1)^n`, so the error
flow is attractive at the origin. This is the convergence statement for the
Luenberger observer: the estimation error actually tends to zero. -/

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

/-- **A detectable observer gain with certified convergent error.** If `(C, A)`
is observable then there is an output injection `L` whose error dynamics
`e' = (A - L C) e` is attractive at the origin. The gain is constructed by
dual pole placement and the convergence is derived from the characteristic
polynomial `(X + 1)^n`; neither the gain nor the decay is assumed.

This is the observer counterpart of
`LinearMap.exists_stabilizing_feedback_attractive`. -/
theorem exists_observer_attractive_of_isObservable
    (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) (h : IsObservable C A) :
    ∃ L : Y →ₗ[ℝ] X,
      Filter.IsAttractive (l := 𝓝 (0 : X)) (Φ := fun (t : ℝ) (x : X) =>
        NormedSpace.exp (t • (A - L.comp C).toContinuousLinearMap) x) (l' := atTop) := by
  set n : ℕ := Module.finrank ℝ X with hn
  set p : Polynomial ℝ := (Polynomial.X + Polynomial.C (1 : ℝ)) ^ n with hp
  have hpmonic : p.Monic := (Polynomial.monic_X_add_C (1 : ℝ)).pow n
  have hpdeg : p.natDegree = Module.finrank ℝ X := by
    rw [hp, Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C, mul_one]
  have hpdeg' : p.natDegree = Module.finrank ℝ (Module.Dual ℝ X) := by
    rw [hpdeg, Subspace.dual_finrank_eq]
  have hc : IsControllable A.dualMap C.dualMap :=
    (isObservable_iff_isControllable_dualMap C A).mp h
  obtain ⟨F, hF⟩ := exists_feedback_charpoly_of_isControllable
    A.dualMap C.dualMap hc p hpmonic hpdeg'
  obtain ⟨L, hL⟩ := dualMap_surjective (Y := Y) (X := X) (-F)
  refine ⟨L, ?_⟩
  have hdual : (A - L.comp C).dualMap = A.dualMap + C.dualMap.comp F := by
    rw [dualMap_sub, ← dualMap_comp_dualMap C L, hL, comp_neg]
    abel
  have hchar : (A - L.comp C).charpoly = p := by
    rw [← charpoly_dualMap (A - L.comp C), hdual, hF]
  exact isAttractive_expFlow_of_charpoly_eq_pow_X_add_one (A - L.comp C) n hchar

/-- **Observer error dynamics that is simultaneously stable and attractive.**
If `(C, A)` is observable then there is an output injection `L` whose error flow
is Lyapunov stable and attractive at the origin, i.e. the estimation error
converges to zero without leaving any prescribed neighbourhood. The gain is
built by dual pole placement and both properties are derived from the
characteristic polynomial `(X + 1)^n`, so no gain and no decay is assumed.

This is the observer counterpart of
`LinearMap.exists_stabilizing_feedback_stable_attractive` and completes the
Luenberger convergence statement. -/
theorem exists_observer_stable_attractive_of_isObservable
    (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) (h : IsObservable C A) :
    ∃ L : Y →ₗ[ℝ] X,
      (𝓝 (0 : X)).IsStableOn (fun (t : ℝ) (x : X) =>
        NormedSpace.exp (t • (A - L.comp C).toContinuousLinearMap) x) (Set.Ici 0) ∧
      Filter.IsAttractive (l := 𝓝 (0 : X)) (Φ := fun (t : ℝ) (x : X) =>
        NormedSpace.exp (t • (A - L.comp C).toContinuousLinearMap) x) (l' := atTop) := by
  set n : ℕ := Module.finrank ℝ X with hn
  set p : Polynomial ℝ := (Polynomial.X + Polynomial.C (1 : ℝ)) ^ n with hp
  have hpmonic : p.Monic := (Polynomial.monic_X_add_C (1 : ℝ)).pow n
  have hpdeg : p.natDegree = Module.finrank ℝ X := by
    rw [hp, Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C, mul_one]
  have hpdeg' : p.natDegree = Module.finrank ℝ (Module.Dual ℝ X) := by
    rw [hpdeg, Subspace.dual_finrank_eq]
  have hc : IsControllable A.dualMap C.dualMap :=
    (isObservable_iff_isControllable_dualMap C A).mp h
  obtain ⟨F, hF⟩ := exists_feedback_charpoly_of_isControllable
    A.dualMap C.dualMap hc p hpmonic hpdeg'
  obtain ⟨L, hL⟩ := dualMap_surjective (Y := Y) (X := X) (-F)
  refine ⟨L, ?_, ?_⟩
  · have hdual : (A - L.comp C).dualMap = A.dualMap + C.dualMap.comp F := by
      rw [dualMap_sub, ← dualMap_comp_dualMap C L, hL, comp_neg]
      abel
    have hchar : (A - L.comp C).charpoly = p := by
      rw [← charpoly_dualMap (A - L.comp C), hdual, hF]
    exact isStableOn_expFlow_of_charpoly_eq_pow_X_add_one (A - L.comp C) n hchar
  · have hdual : (A - L.comp C).dualMap = A.dualMap + C.dualMap.comp F := by
      rw [dualMap_sub, ← dualMap_comp_dualMap C L, hL, comp_neg]
      abel
    have hchar : (A - L.comp C).charpoly = p := by
      rw [← charpoly_dualMap (A - L.comp C), hdual, hF]
    exact isAttractive_expFlow_of_charpoly_eq_pow_X_add_one (A - L.comp C) n hchar

end LinearMap

/-! ## The separation principle for the observer-based controller

The observer-based controller feeds the state feedback `u = F ξ` from the
estimate back into the plant. In the coordinates `(x, e)` with the estimation
error `e = ξ - x`, the coupled dynamics is

```
x' = (A + B F) x + B F e,
e' = (A - L C) e,
```

so the closed-loop coefficient operator is the block matrix
`[[A + B F, B F], [0, A - L C]]`. The spectrum factorization of that block
operator, proved in `DynamicalSystems.Linear.Stabilization`, then yields the
separation principle: the state-feedback and observer designs are independent,
and their composite closed loop is Hurwitz exactly when both factors are. -/

namespace LinearMap

section SeparationPrinciple

variable {X U Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [AddCommGroup U] [Module ℝ U]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- **Separation principle for the Luenberger observer.** If `F` stabilizes the
state dynamics (`A + B F` Hurwitz) and `L` yields a convergent observer error
(`A - L C` Hurwitz), then the assembled closed-loop operator
`[[A + B F, B F], [0, A - L C]]` is Hurwitz. The gain `F` is designed purely
from the plant and the gain `L` purely from the readout, confirming that the two
designs can be carried out independently. -/
theorem separation_principle_observer
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (C : X →ₗ[ℝ] Y)
    (F : X →ₗ[ℝ] U) (L : Y →ₗ[ℝ] X)
    (hF : IsHurwitz (A + B.comp F)) (hL : IsHurwitz (A - L.comp C)) :
    IsHurwitz (blockOperator (A + B.comp F) (B.comp F) (A - L.comp C)) :=
  isHurwitz_separationOperator A B C F L hF hL

/-- **A stable observer excludes unobservable eigenvalues in the closed right
half-plane.** This restates the converse detectability criterion in the
observer vocabulary: if the estimation error can be made to converge, then no
unobservable eigenvalue of the readout can have nonnegative real part. -/
theorem not_unobservableEigenvalue_of_isDetectable
    (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) (h : IsDetectable C A)
    {μ : ℂ} (hμ : IsUnobservableEigenvalue C A μ) :
    ¬ 0 ≤ μ.re := fun hre => absurd (isDetectable_converse_of_unobservableEigenvalue C A h hμ)
      (not_lt.mpr hre)

end SeparationPrinciple

end LinearMap
