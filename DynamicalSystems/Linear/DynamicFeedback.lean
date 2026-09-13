/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.DisturbanceDecoupling
public import DynamicalSystems.Linear.Stabilization
public import DynamicalSystems.Linear.Trajectory

/-! # Dynamic measurement-feedback: algebraic foundations

This file lays the algebraic foundations of Chapter 6 of Trentelman, Stoorvogel
and Hautus, *Control Theory for Linear Systems*: the **dynamic measurement
feedback** interconnection of a plant with a finite-dimensional linear
time-invariant controller, in the presence of a feedthrough from the control
input to the measurement.

The plant `Σ = (A, B, C, D)` is an ordinary `LinearSystem` with state `X`,
control input `U` and measurement output `Y`, and it is driven by a disturbance
input `d : D` through a **state channel** `E : D →ₗ[𝕜] X` and a **measurement
channel** `F : D →ₗ[𝕜] Y`; the controlled output is the **output channel**
`H : X →ₗ[𝕜] Z`:

```
x'(t) = A x(t) + B u(t) + E d(t),
y(t)  = C x(t) + D u(t) + F d(t),
z(t)  = H x(t).
```

The controller `Κ = (K, L, M, N)` (Trentelman–Stoorvogel–Hautus, equation (6.2))
is a finite-dimensional linear system with state `W`, input the measurement `Y`
and output the control `U`:

```
w'(t) = K w(t) + L y(t),
u(t)  = M w(t) + N y(t).
```

## The algebraic loop and well-posedness

When the plant has a control feedthrough `D ≠ 0` and the controller has a
measurement feedthrough `N ≠ 0`, the equations `y = C x + D u` and
`u = M w + N y` are coupled algebraically. Substituting the controller output
into the measurement gives the **algebraic loop equation**

`(I - D N) y = C x + D M w`.

The interconnection is **well posed** precisely when the loop map
`1 - D ∘ N : Y →ₗ[𝕜] Y` is bijective
(`DynamicInterconnection.IsWellPosed`), which is the invertibility condition of
Trentelman–Stoorvogel–Hautus, exercise 6.3. Well-posedness makes the loop
equation uniquely solvable (`solvedMeasurement_unique`), and we use the inverse
`loopInv` to build the resolved measurement and control signals
`solvedMeasurement` and `solvedInput`.

## The closed loop

With the loop resolved, the closed loop is again a linear time-invariant system
on the extended state space `X × W`, with disturbance input `D` and controlled
output `Z`:

```
p'(t) = Ae p(t) + Be d(t),
z(t)  = He p(t),
```

where `p = (x, w)` and `Ae = closedLoopMap`, `Be = disturbanceMap`,
`He = outputMap` (`closedLoopSystem`). For a nonzero measurement channel `F`
the total disturbance map is `disturbanceMapWithF`, which combines `E`, `F` and
the resolved loop; it reduces to `disturbanceMap` when `F = 0`
(`disturbanceMapWithF_of_F_eq_zero`). The main algebraic law below is the
composition identity `closedLoopSystem_dynamics`, which decomposes the
closed-loop right-hand side into the autonomous extended map plus the disturbance
channel; its `F`-channel counterpart is `closedLoopDynamicsWithF_eq`.

## Zero-disturbance and zero-initial-state lemmas

Setting `d = 0` collapses `disturbanceMap` to zero:
`closedLoopSystem_dynamics_zero_disturbance`. With moreover `p = 0` every
resolved signal and every closed-loop state map vanishes
(`solvedMeasurement_zero`, `solvedInput_zero`, `closedLoopMap_zero`) and the
closed-loop trajectory from the origin under zero disturbance is identically
zero (`closedLoopSystem_variationOfConstants_zero`,
`closedLoopSystem_readout_variationOfConstants_zero`). These are the algebraic
and trajectory identities on which the later decoupling and internal-stability
theorems rest.

## Strictly proper plant: the classical block operator

For a strictly proper plant (`D = 0`) well-posedness is automatic
(`isWellPosed_of_D_eq_zero`) and the closed-loop state map is the familiar
block operator of Trentelman–Stoorvogel–Hautus, equation (6.3):

`Ae (x, w) = ((A + B N C) x + B M w, L C x + K w)`

(`closedLoopMap_of_D_eq_zero`).

## Closed-loop spectrum factorization and internal stability

Under `D = 0` the controller (6.7) is an observer-based controller. In the
observer-error coordinates `(x, e) = (x, x - w)` its closed loop is block upper
triangular with state-feedback block `A + B F` and observer-error block
`A + G C`, so `χ(Ae) = χ(A + B F) · χ(A + G C)` and the closed loop is Hurwitz —
hence internally asymptotically stable — as soon as both blocks are. The
observer-error coordinate change is `observerErrorEquiv`; the sign convention is
that the injection `+G C` of (6.7) is the contract's `A - L.comp C` with
`L = -G` (`observerErrorBlock_eq`).

## Scope

This file contains the algebraic foundations of Chapter 6 together with the
**dynamic decoupling synthesis** of Theorem 6.4 / Corollary 6.7 and the
**geometric extraction (necessity)** of Theorem 6.2 / Theorem 6.6, so the
following is now claimed and proved here:

* a `(C, A, B)`-pair between `im E` and `ker H` yields the controller `(6.7)`
  with state space `W = X`, and its closed loop is disturbance decoupled
  (`exists_dynamicController_of_isCABPairBetween`,
  `isClosedLoopDisturbanceDecoupled_of_isCABPairBetween`). The output feedback
  `N` of Lemma 6.3 is constructed abstractly as
  `exists_outputFeedback_of_isCABPair`;

* the converse (necessity) extraction of a `(C, A, B)`-pair from a decoupled
  closed loop (Theorem 6.2 and the forward half of Theorem 6.6): passing from an
  `Ae`-invariant extended subspace to its intersection `i(Ve)` and projection
  `p(Ve)` yields a `(C, A, B)`-pair between `im E` and `ker H`
  (`isCABPair_extendedIntersection_extendedProjection`,
  `exists_isCABPairBetween_of_isClosedLoopDisturbanceDecoupled`). Together with
  the synthesis direction this gives the full Theorem 6.6 equivalence for a
  strictly proper plant
  (`exists_dynamicController_disturbanceDecoupled_iff_isCABPairBetween`);

* the **closed-loop spectrum factorization and internal-stability layer** of
  Sections 6.3–6.4 for the controller (6.7): for a strictly proper plant the
  extended closed-loop map is similar, via the observer-error coordinate change
  `observerErrorEquiv` `(x, w) ↦ (x, x - w)`, to the separation-principle block
  operator `[[A + B F, -B (F - N C)], [0, A + G C]]`
  (`cabPairController_closedLoopMap_conj`); hence
  `χ(Ae) = χ(A + B F) · χ(A + G C)`
  (`charpoly_closedLoopMap_cabPairController`), the closed loop is Hurwitz as
  soon as `A + B F` and `A + G C` are
  (`isHurwitz_closedLoopMap_cabPairController`), and it is internally
  asymptotically stable in the senses of `Filter.IsStableOn` and
  `Filter.IsAttractive`
  (`isStableOn_closedLoopSystem_cabPairController`,
  `isAttractive_closedLoopSystem_cabPairController`,
  `isAsymptoticallyStable_closedLoopSystem_cabPairController`);

For a strictly proper plant the two directions combine into the exact
Theorem 6.6 equivalence. The extraction below only needs well-posedness, so it
also applies to plants with a control feedthrough; the synthesis direction at
present requires `D = 0`. The following remain the next milestones and are *not*
claimed here, so that no unproved strengthening is read into the present
declarations:

* the **decoupling synthesis theorem for a nonzero measurement disturbance
  channel** `F`: the channel itself, its resolved measured signal and input, the
  zero-channel and zero-disturbance reductions and the closed-loop disturbance
  bookkeeping are formalised here, but no nonzero-`F` decoupling existence
  theorem is claimed (the synthesis of Theorem 6.4 fixes `F = 0`);
* the transfer-function form of decoupling and the external stabilization of
  Section 6.6;
* nonlinear (Conte–Moog–Perdon) dynamic feedback, which stays in the documented
  future roadmap.

## Main definitions

* `LinearSystem.DynamicController`: the controller `(K, L, M, N)`.
* `LinearSystem.DynamicInterconnection`: plant, controller and the disturbance
  and output channels.
* `DynamicInterconnection.loopMap`, `DynamicInterconnection.IsWellPosed`,
  `DynamicInterconnection.loopInv`
* `DynamicInterconnection.solvedMeasurement`, `DynamicInterconnection.solvedInput`
* `DynamicInterconnection.disturbanceMeasurement`,
  `DynamicInterconnection.measuredSignal`, `DynamicInterconnection.disturbanceInput`,
  `DynamicInterconnection.resolvedInput`
* `DynamicInterconnection.closedLoopMap`, `disturbanceMap`,
  `disturbanceMapWithF`, `outputMap`
* `DynamicInterconnection.closedLoopSystem`,
  `DynamicInterconnection.closedLoopDynamicsWithF`
* `DynamicInterconnection.IsClosedLoopDisturbanceDecoupled`,
  `DynamicInterconnection.IsClosedLoopDisturbanceDecoupledWithF`
* `DynamicInterconnection.extendedIntersection`,
  `DynamicInterconnection.extendedProjection`
* `LinearSystem.cabPairController`, `LinearSystem.cabPairInterconnection`
* `LinearSystem.observerErrorEquiv`: the observer-error coordinate change

## Main results

* `DynamicInterconnection.measurement_eq_plant_readout`
* `DynamicInterconnection.measurement_eq_of_plant_readout`
* `DynamicInterconnection.measuredSignal_eq_plant_readout`
* `DynamicInterconnection.measuredSignal_unique`
* `DynamicInterconnection.measuredSignal_of_F_eq_zero`,
  `DynamicInterconnection.resolvedInput_of_F_eq_zero`
* `DynamicInterconnection.disturbanceMapWithF_of_F_eq_zero`
* `DynamicInterconnection.closedLoopDynamicsWithF_eq`
* `DynamicInterconnection.isClosedLoopDisturbanceDecoupledWithF_of_F_eq_zero`
* `DynamicInterconnection.closedLoopSystem_dynamics`
* `DynamicInterconnection.closedLoopSystem_dynamics_zero_disturbance`
* `DynamicInterconnection.closedLoopMap_of_D_eq_zero`
* `DynamicInterconnection.closedLoopSystem_variationOfConstants_zero`
* `LinearSystem.exists_outputFeedback_of_isCABPair`
* `LinearSystem.isClosedLoopDisturbanceDecoupled_of_isCABPairBetween`
* `LinearSystem.exists_dynamicController_of_isCABPairBetween`
* `DynamicInterconnection.isCABPair_extendedIntersection_extendedProjection`
* `DynamicInterconnection.exists_isCABPairBetween_of_isClosedLoopDisturbanceDecoupled`
* `LinearSystem.exists_dynamicController_disturbanceDecoupled_iff_isCABPairBetween`
* `LinearSystem.observerErrorBlock_eq`
* `LinearSystem.cabPairController_closedLoopMap_conj`
* `LinearSystem.charpoly_closedLoopMap_cabPairController`
* `LinearSystem.isHurwitz_closedLoopMap_cabPairController`
* `LinearSystem.isStableOn_closedLoopSystem_cabPairController`
* `LinearSystem.isAttractive_closedLoopSystem_cabPairController`
* `LinearSystem.isAsymptoticallyStable_closedLoopSystem_cabPairController`
* `LinearSystem.exists_hurwitz_cabPair_gains`
* `LinearSystem.exists_hurwitz_closedLoopMap_of_isControllable_isObservable`

## References

* H. L. Trentelman, A. A. Stoorvogel, M. Hautus, *Control Theory for Linear
  Systems*, Springer, 2001, Section 3.13 and Chapter 6, in particular
  equations (6.2)–(6.4), Definition 6.1 and exercise 6.3.
-/

@[expose] public section

namespace LinearSystem

variable {𝕜 W Y U : Type*}
variable [Field 𝕜]
variable [AddCommGroup W] [Module 𝕜 W]
variable [AddCommGroup Y] [Module 𝕜 Y]
variable [AddCommGroup U] [Module 𝕜 U]

/-! ## The dynamic controller -/

/-- A finite-dimensional linear time-invariant **dynamic controller**
`Κ = (K, L, M, N)`, whose input is the measurement `y : Y` and whose output is
the control `u : U`:

```
w' = K w + L y,
u  = M w + N y.
```

The state space `W` is the controller's dynamic order.

Source: Trentelman–Stoorvogel–Hautus, equation (6.2). -/
structure DynamicController (𝕜 W Y U : Type*) [Field 𝕜]
    [AddCommGroup W] [Module 𝕜 W]
    [AddCommGroup Y] [Module 𝕜 Y]
    [AddCommGroup U] [Module 𝕜 U] where
  /-- Controller state map `K : W →ₗ[𝕜] W`. -/
  K : W →ₗ[𝕜] W
  /-- Controller input map `L : Y →ₗ[𝕜] W`. -/
  L : Y →ₗ[𝕜] W
  /-- Controller output map `M : W →ₗ[𝕜] U`. -/
  M : W →ₗ[𝕜] U
  /-- Controller feedthrough map `N : Y →ₗ[𝕜] U`. -/
  N : Y →ₗ[𝕜] U

namespace DynamicController

variable (ctrl : DynamicController 𝕜 W Y U)

/-- The controller as an ordinary `LinearSystem` with state `W`, input the
measurement `Y` and output the control `U`. Its fields are `K, L, M, N` in the
order `A, B, C, D`. This lets the controller reuse the whole `LinearSystem`
API (flows, trajectories, coordinate changes). -/
def toLinearSystem (ctrl : DynamicController 𝕜 W Y U) : LinearSystem 𝕜 W Y U where
  A := ctrl.K
  B := ctrl.L
  C := ctrl.M
  D := ctrl.N

@[simp]
theorem toLinearSystem_A : ctrl.toLinearSystem.A = ctrl.K := rfl

@[simp]
theorem toLinearSystem_B : ctrl.toLinearSystem.B = ctrl.L := rfl

@[simp]
theorem toLinearSystem_C : ctrl.toLinearSystem.C = ctrl.M := rfl

@[simp]
theorem toLinearSystem_D : ctrl.toLinearSystem.D = ctrl.N := rfl

/-- The controller state equation `w' = K w + L y`. -/
def dynamics (ctrl : DynamicController 𝕜 W Y U) (w : W) (y : Y) : W :=
  ctrl.K w + ctrl.L y

@[simp]
theorem dynamics_apply (w : W) (y : Y) :
    ctrl.dynamics w y = ctrl.K w + ctrl.L y := rfl

/-- The controller output equation `u = M w + N y`. -/
def output (ctrl : DynamicController 𝕜 W Y U) (w : W) (y : Y) : U :=
  ctrl.M w + ctrl.N y

@[simp]
theorem output_apply (w : W) (y : Y) :
    ctrl.output w y = ctrl.M w + ctrl.N y := rfl

/-- The controller dynamics is the `LinearSystem` dynamics of `toLinearSystem`. -/
theorem dynamics_eq_toLinearSystem_dynamics :
    ctrl.dynamics = ctrl.toLinearSystem.dynamics := rfl

/-- The controller output is the `LinearSystem` readout of `toLinearSystem`. -/
theorem output_eq_toLinearSystem_readout :
    ctrl.output = ctrl.toLinearSystem.readout := rfl

/-- With zero measurement the controller dynamics is the autonomous state map. -/
theorem dynamics_zero_input (w : W) : ctrl.dynamics w 0 = ctrl.K w := by
  simp [dynamics]

/-- At the controller origin the dynamics is the input map applied to the
measurement. -/
theorem dynamics_zero_state (y : Y) : ctrl.dynamics 0 y = ctrl.L y := by
  simp [dynamics]

/-- With zero measurement the controller output is `M w`. -/
theorem output_zero_input (w : W) : ctrl.output w 0 = ctrl.M w := by
  simp [output]

/-- At the controller origin the output is the feedthrough applied to the
measurement. -/
theorem output_zero_state (y : Y) : ctrl.output 0 y = ctrl.N y := by
  simp [output]

end DynamicController

/-! ## The measurement-feedback interconnection -/

variable {X D Z : Type*}
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup D] [Module 𝕜 D]
variable [AddCommGroup Z] [Module 𝕜 Z]

/-- A **dynamic measurement-feedback interconnection**: a plant `Σ = (A, B, C, D)`
with state `X`, control input `U` and measurement `Y`, a dynamic controller
`Κ = (K, L, M, N)` with state `W`, a state disturbance channel
`E : D →ₗ[𝕜] X` and a controlled-output map `H : X →ₗ[𝕜] Z`.

The associated (implicit) equations are

```
x' = A x + B u + E d,
y  = C x + D u,
u  = M w + N y,
w' = K w + L y,
z  = H x.
```

Source: Trentelman–Stoorvogel–Hautus, equations (6.11)–(6.12) together with the
control/measurement feedthrough variant of exercise 6.3. -/
structure DynamicInterconnection (𝕜 X U Y W D Z : Type*) [Field 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup U] [Module 𝕜 U]
    [AddCommGroup Y] [Module 𝕜 Y]
    [AddCommGroup W] [Module 𝕜 W]
    [AddCommGroup D] [Module 𝕜 D]
    [AddCommGroup Z] [Module 𝕜 Z] where
  /-- The plant `Σ = (A, B, C, D)`. -/
  plant : LinearSystem 𝕜 X U Y
  /-- The dynamic controller `Κ = (K, L, M, N)`. -/
  controller : DynamicController 𝕜 W Y U
  /-- State disturbance channel `E : D →ₗ[𝕜] X`. -/
  E : D →ₗ[𝕜] X
  /-- Measurement disturbance channel `F : D →ₗ[𝕜] Y`. -/
  F : D →ₗ[𝕜] Y
  /-- Controlled-output map `H : X →ₗ[𝕜] Z`. -/
  H : X →ₗ[𝕜] Z

namespace DynamicInterconnection

variable (ic : DynamicInterconnection 𝕜 X U Y W D Z)

/-! ### The algebraic loop and well-posedness -/

/-- The **algebraic-loop map** `1 - D ∘ N : Y →ₗ[𝕜] Y` of a dynamic
measurement-feedback interconnection. Its bijectivity is exactly the
well-posedness condition of Trentelman–Stoorvogel–Hautus, exercise 6.3. -/
def loopMap : Y →ₗ[𝕜] Y :=
  (1 : Y →ₗ[𝕜] Y) - ic.plant.D.comp ic.controller.N

@[simp]
theorem loopMap_apply (y : Y) :
    ic.loopMap y = y - ic.plant.D (ic.controller.N y) := rfl

/-- The interconnection is **well posed** when the algebraic-loop map is
bijective, i.e. when `I - D N` is invertible. -/
def IsWellPosed : Prop := Function.Bijective ic.loopMap

/-- **Well-posedness is unique solvability of the algebraic loop.** The loop map
is bijective exactly when every right-hand side has a unique preimage, which is
the abstract form of "the interconnection equations have a unique solution". -/
theorem isWellPosed_iff_forall_existsUnique_loopSolution :
    ic.IsWellPosed ↔ ∀ b : Y, ∃! y : Y, ic.loopMap y = b :=
  Function.bijective_iff_existsUnique ic.loopMap

/-- The loop map is injective under well-posedness. -/
theorem loopMap_injective (h : ic.IsWellPosed) : Function.Injective ic.loopMap := h.1

/-- The loop map is surjective under well-posedness. -/
theorem loopMap_surjective (h : ic.IsWellPosed) : Function.Surjective ic.loopMap := h.2

/-- The inverse of the algebraic-loop map, obtained from well-posedness. -/
noncomputable def loopInv (h : ic.IsWellPosed) : Y →ₗ[𝕜] Y :=
  (LinearEquiv.ofBijective ic.loopMap h).symm.toLinearMap

/-- The loop inverse is a right inverse of the loop map. -/
theorem loopMap_loopInv (h : ic.IsWellPosed) :
    ic.loopMap.comp (ic.loopInv h) = 1 := by
  ext y
  change (LinearEquiv.ofBijective ic.loopMap h)
      ((LinearEquiv.ofBijective ic.loopMap h).symm y) = y
  exact LinearEquiv.apply_symm_apply _ y

/-- The loop inverse is a left inverse of the loop map. -/
theorem loopInv_loopMap (h : ic.IsWellPosed) :
    (ic.loopInv h).comp ic.loopMap = 1 := by
  ext y
  change (LinearEquiv.ofBijective ic.loopMap h).symm
      ((LinearEquiv.ofBijective ic.loopMap h) y) = y
  exact LinearEquiv.symm_apply_apply _ y

/-- Uniqueness of the loop solution: the loop inverse returns the unique
preimage of a given right-hand side. -/
theorem loopInv_eq_of_loopMap_eq (h : ic.IsWellPosed) {y z : Y}
    (hy : ic.loopMap y = z) : ic.loopInv h z = y := by
  rw [← hy]
  exact LinearMap.congr_fun (ic.loopInv_loopMap h) y

/-- The unresolved right-hand side of the algebraic loop, `C x + D M w`, as a
linear map `X × W →ₗ[𝕜] Y`. -/
def loopForcing : X × W →ₗ[𝕜] Y :=
  ic.plant.C.comp (LinearMap.fst 𝕜 X W) +
    (ic.plant.D.comp ic.controller.M).comp (LinearMap.snd 𝕜 X W)

@[simp]
theorem loopForcing_apply (p : X × W) :
    ic.loopForcing p = ic.plant.C p.1 + ic.plant.D (ic.controller.M p.2) := rfl

/-- The **resolved measurement** `y = (1 - D N)⁻¹ (C x + D M w)`. This is the
unique solution of the algebraic loop. -/
noncomputable def solvedMeasurement (h : ic.IsWellPosed) : X × W →ₗ[𝕜] Y :=
  (ic.loopInv h).comp ic.loopForcing

@[simp]
theorem solvedMeasurement_apply (h : ic.IsWellPosed) (p : X × W) :
    ic.solvedMeasurement h p = ic.loopInv h (ic.loopForcing p) := rfl

/-- The resolved measurement solves the loop equation
`(1 - D N) y = C x + D M w`. -/
theorem loopMap_solvedMeasurement (h : ic.IsWellPosed) (p : X × W) :
    ic.loopMap (ic.solvedMeasurement h p) = ic.loopForcing p :=
  LinearMap.congr_fun (ic.loopMap_loopInv h) (ic.loopForcing p)

/-- The **resolved control** `u = M w + N y` at the resolved measurement. -/
noncomputable def solvedInput (h : ic.IsWellPosed) : X × W →ₗ[𝕜] U :=
  (ic.controller.M.comp (LinearMap.snd 𝕜 X W)) +
    ic.controller.N.comp (ic.solvedMeasurement h)

@[simp]
theorem solvedInput_apply (h : ic.IsWellPosed) (p : X × W) :
    ic.solvedInput h p = ic.controller.M p.2 + ic.controller.N (ic.solvedMeasurement h p) :=
  rfl

/-- **The resolved measurement satisfies the plant readout.** On the resolved
loop, `y = C x + D u` holds exactly, i.e. the loop has been solved. -/
theorem measurement_eq_plant_readout (h : ic.IsWellPosed) (p : X × W) :
    ic.solvedMeasurement h p = ic.plant.C p.1 + ic.plant.D (ic.solvedInput h p) := by
  have hloop := ic.loopMap_solvedMeasurement h p
  simp only [loopMap_apply, loopForcing_apply] at hloop
  have hy : ic.solvedMeasurement h p =
      ic.plant.C p.1 + ic.plant.D (ic.controller.M p.2) +
        ic.plant.D (ic.controller.N (ic.solvedMeasurement h p)) := by
    rw [← hloop]
    abel
  rw [solvedInput_apply]
  calc ic.solvedMeasurement h p
      = ic.plant.C p.1 + ic.plant.D (ic.controller.M p.2) +
          ic.plant.D (ic.controller.N (ic.solvedMeasurement h p)) := hy
    _ = ic.plant.C p.1 + ic.plant.D (ic.controller.M p.2 +
          ic.controller.N (ic.solvedMeasurement h p)) := by
          rw [map_add]
          abel

/-- **Uniqueness in the algebraic loop.** Any measurement `y` satisfying the loop
equation with the resolved control is the resolved measurement. Thus
well-posedness pins down the loop solution. -/
theorem solvedMeasurement_unique (h : ic.IsWellPosed) {p : X × W} {y : Y}
    (hy : ic.plant.C p.1 + ic.plant.D (ic.controller.M p.2 + ic.controller.N y) = y) :
    y = ic.solvedMeasurement h p := by
  apply h.1
  rw [ic.loopMap_solvedMeasurement h p]
  simp only [loopMap_apply, loopForcing_apply]
  have hy_exp : ic.plant.C p.1 + (ic.plant.D (ic.controller.M p.2) +
      ic.plant.D (ic.controller.N y)) = y := by
    rw [map_add] at hy
    exact hy
  rw [sub_eq_iff_eq_add]
  exact hy_exp.symm.trans (by abel)

/-- **The resolved measurement satisfies any plant readout.** If a measurement
`y` together with a control `u = M w + N y` satisfies the readout
`y = C x + D u`, then `y` is the resolved measurement. This is the
well-posedness statement in its readout form. -/
theorem measurement_eq_of_plant_readout (h : ic.IsWellPosed) {p : X × W} {y : Y}
    (hy : y = ic.plant.C p.1 + ic.plant.D (ic.controller.M p.2 + ic.controller.N y)) :
    y = ic.solvedMeasurement h p :=
  ic.solvedMeasurement_unique h hy.symm

/-- **Unique solvability of the loop equation.** For every extended state `p`
there is exactly one resolved measurement solving the algebraic loop. -/
theorem existsUnique_loopSolution (h : ic.IsWellPosed) (p : X × W) :
    ∃! y : Y, ic.loopMap y = ic.loopForcing p := by
  refine ⟨ic.solvedMeasurement h p, ic.loopMap_solvedMeasurement h p, ?_⟩
  intro y hy
  apply h.1
  rw [hy, ic.loopMap_solvedMeasurement h p]

/-- **Unique solvability in readout form.** For every extended state `p` there is
exactly one measurement satisfying the plant readout with the resolved control. -/
theorem existsUnique_readoutSolution (h : ic.IsWellPosed) (p : X × W) :
    ∃! y : Y, y = ic.plant.C p.1 +
      ic.plant.D (ic.controller.M p.2 + ic.controller.N y) := by
  refine ⟨ic.solvedMeasurement h p, ic.measurement_eq_plant_readout h p, ?_⟩
  intro y hy
  exact ic.measurement_eq_of_plant_readout h hy

/-! ### The closed-loop maps -/

/-- The **closed-loop (extended) system map** `Ae : X × W →ₗ[𝕜] X × W` with zero
disturbance. In components,

`Ae (x, w) = (A x + B u, K w + L y)`

where `u` and `y` are the resolved control and measurement.

Source: Trentelman–Stoorvogel–Hautus, equations (6.3)–(6.4). -/
noncomputable def closedLoopMap (h : ic.IsWellPosed) : X × W →ₗ[𝕜] X × W :=
  LinearMap.prod
    (ic.plant.A.comp (LinearMap.fst 𝕜 X W) +
      ic.plant.B.comp (ic.solvedInput h))
    (ic.controller.K.comp (LinearMap.snd 𝕜 X W) +
      ic.controller.L.comp (ic.solvedMeasurement h))

@[simp]
theorem closedLoopMap_apply (h : ic.IsWellPosed) (p : X × W) :
    ic.closedLoopMap h p =
      (ic.plant.A p.1 + ic.plant.B (ic.solvedInput h p),
       ic.controller.K p.2 + ic.controller.L (ic.solvedMeasurement h p)) := rfl

/-- The plant component of the closed-loop map. -/
theorem closedLoopMap_fst (h : ic.IsWellPosed) (p : X × W) :
    (ic.closedLoopMap h p).1 =
      ic.plant.A p.1 + ic.plant.B (ic.solvedInput h p) := rfl

/-- The controller component of the closed-loop map. -/
theorem closedLoopMap_snd (h : ic.IsWellPosed) (p : X × W) :
    (ic.closedLoopMap h p).2 =
      ic.controller.K p.2 + ic.controller.L (ic.solvedMeasurement h p) := rfl

/-- The **closed-loop disturbance map** `Be : D →ₗ[𝕜] X × W`, the embedding of
the state disturbance into the extended state space, `Be d = (E d, 0)`. -/
def disturbanceMap : D →ₗ[𝕜] X × W :=
  LinearMap.prod ic.E 0

@[simp]
theorem disturbanceMap_apply (d : D) : ic.disturbanceMap d = (ic.E d, 0) := rfl

/-- The **closed-loop controlled-output map** `He = H ∘ fst : X × W →ₗ[𝕜] Z`. -/
def outputMap : X × W →ₗ[𝕜] Z :=
  ic.H.comp (LinearMap.fst 𝕜 X W)

@[simp]
theorem outputMap_apply (p : X × W) : ic.outputMap p = ic.H p.1 := rfl

/-- The closed loop as a `LinearSystem` on the extended state space `X × W`,
with disturbance input `D` and controlled output `Z`:

```
p' = Ae p + Be d,
z  = He p.
```

Source: Trentelman–Stoorvogel–Hautus, equation (6.12). -/
noncomputable def closedLoopSystem (h : ic.IsWellPosed) : LinearSystem 𝕜 (X × W) D Z where
  A := ic.closedLoopMap h
  B := ic.disturbanceMap
  C := ic.outputMap
  D := 0

@[simp]
theorem closedLoopSystem_A (h : ic.IsWellPosed) :
    (ic.closedLoopSystem h).A = ic.closedLoopMap h := rfl

@[simp]
theorem closedLoopSystem_B (h : ic.IsWellPosed) :
    (ic.closedLoopSystem h).B = ic.disturbanceMap := rfl

@[simp]
theorem closedLoopSystem_C (h : ic.IsWellPosed) :
    (ic.closedLoopSystem h).C = ic.outputMap := rfl

@[simp]
theorem closedLoopSystem_D (h : ic.IsWellPosed) :
    (ic.closedLoopSystem h).D = 0 := rfl

/-- **The closed-loop right-hand side decomposes into the autonomous extended
map plus the disturbance channel.** This is the algebraic composition identity
behind the closed-loop system `p' = Ae p + Be d`. -/
theorem closedLoopSystem_dynamics (h : ic.IsWellPosed) (p : X × W) (d : D) :
    (ic.closedLoopSystem h).dynamics p d =
      ic.closedLoopMap h p + ic.disturbanceMap d := rfl

/-- The plant component of the closed-loop dynamics. -/
theorem closedLoopSystem_dynamics_fst (h : ic.IsWellPosed) (p : X × W) (d : D) :
    ((ic.closedLoopSystem h).dynamics p d).1 =
      ic.plant.A p.1 + ic.plant.B (ic.solvedInput h p) + ic.E d := by
  simp [LinearSystem.dynamics, closedLoopSystem, closedLoopMap_apply, disturbanceMap_apply,
    map_add]

/-- The controller component of the closed-loop dynamics. -/
theorem closedLoopSystem_dynamics_snd (h : ic.IsWellPosed) (p : X × W) (d : D) :
    ((ic.closedLoopSystem h).dynamics p d).2 =
      ic.controller.K p.2 + ic.controller.L (ic.solvedMeasurement h p) := by
  simp [LinearSystem.dynamics, closedLoopSystem, closedLoopMap_apply, disturbanceMap_apply]

/-- The resolved control is the controller output at the resolved measurement. -/
theorem solvedInput_eq_controller_output (h : ic.IsWellPosed) (p : X × W) :
    ic.solvedInput h p = ic.controller.output p.2 (ic.solvedMeasurement h p) := rfl

/-! ### The measurement-disturbance channel

With a measurement disturbance channel `F : D →ₗ[𝕜] Y` the plant readout reads

`y = C x + D u + F d`,

so the resolved measurement and control acquire an additive, linear-in-`d`
contribution. Since the algebraic-loop map `1 - D N` does not involve `d`, this
contribution is `(1 - D N)⁻¹ (F d)` and the loop remains uniquely solvable for
every disturbance. The constructions below reduce to the channel-free resolved
measurement and control when `F = 0`, and to the resolved measurement and control
of the extended state when `d = 0`.

The full channel-decoupling synthesis theorem for nonzero `F` is **not** claimed
here: only the signal, reduction and bookkeeping identities are proved. -/

/-- The **disturbance contribution to the measurement**, the part of the resolved
measurement proportional to the disturbance, `(1 - D N)⁻¹ F d : D →ₗ[𝕜] Y`. -/
noncomputable def disturbanceMeasurement (h : ic.IsWellPosed) : D →ₗ[𝕜] Y :=
  (ic.loopInv h).comp ic.F

@[simp]
theorem disturbanceMeasurement_apply (h : ic.IsWellPosed) (d : D) :
    ic.disturbanceMeasurement h d = ic.loopInv h (ic.F d) := rfl

/-- The **measured signal** with the measurement disturbance: the resolved
measurement shifted by the disturbance contribution. It solves

`y = C x + D (M w + N y) + F d`, i.e. `y = (1 - D N)⁻¹ (C x + D M w + F d)`. -/
noncomputable def measuredSignal (h : ic.IsWellPosed) (p : X × W) (d : D) : Y :=
  ic.solvedMeasurement h p + ic.disturbanceMeasurement h d

@[simp]
theorem measuredSignal_apply (h : ic.IsWellPosed) (p : X × W) (d : D) :
    ic.measuredSignal h p d =
      ic.solvedMeasurement h p + ic.loopInv h (ic.F d) := rfl

/-- The **disturbance contribution to the control**, `N (1 - D N)⁻¹ F d`. -/
noncomputable def disturbanceInput (h : ic.IsWellPosed) : D →ₗ[𝕜] U :=
  ic.controller.N.comp (ic.disturbanceMeasurement h)

@[simp]
theorem disturbanceInput_apply (h : ic.IsWellPosed) (d : D) :
    ic.disturbanceInput h d = ic.controller.N (ic.disturbanceMeasurement h d) := rfl

/-- The **resolved controller input** with the measurement disturbance,
`u = M w + N y` at the measured signal. -/
noncomputable def resolvedInput (h : ic.IsWellPosed) (p : X × W) (d : D) : U :=
  ic.solvedInput h p + ic.disturbanceInput h d

@[simp]
theorem resolvedInput_apply (h : ic.IsWellPosed) (p : X × W) (d : D) :
    ic.resolvedInput h p d =
      ic.solvedInput h p + ic.controller.N (ic.disturbanceMeasurement h d) := rfl

/-- The measured signal is the resolved measurement shifted by the disturbance
contribution. -/
theorem measuredSignal_eq_solvedMeasurement_add (h : ic.IsWellPosed) (p : X × W) (d : D) :
    ic.measuredSignal h p d =
      ic.solvedMeasurement h p + ic.disturbanceMeasurement h d := rfl

/-- The resolved input is the resolved control shifted by the disturbance
contribution. -/
theorem resolvedInput_eq_solvedInput_add (h : ic.IsWellPosed) (p : X × W) (d : D) :
    ic.resolvedInput h p d = ic.solvedInput h p + ic.disturbanceInput h d := rfl

/-- **The measured signal solves the algebraic loop** with the measurement
disturbance: `(1 - D N) y = C x + D M w + F d`. -/
theorem loopMap_measuredSignal (h : ic.IsWellPosed) (p : X × W) (d : D) :
    ic.loopMap (ic.measuredSignal h p d) = ic.loopForcing p + ic.F d := by
  rw [measuredSignal_eq_solvedMeasurement_add, map_add, ic.loopMap_solvedMeasurement h p,
    disturbanceMeasurement_apply]
  exact congrArg (fun z => ic.loopForcing p + z)
    (LinearMap.congr_fun (ic.loopMap_loopInv h) (ic.F d))

/-- **The measured signal satisfies the plant readout** including the measurement
disturbance, `y = C x + D u + F d` with `u = resolvedInput`. -/
theorem measuredSignal_eq_plant_readout (h : ic.IsWellPosed) (p : X × W) (d : D) :
    ic.measuredSignal h p d =
      ic.plant.C p.1 + ic.plant.D (ic.resolvedInput h p d) + ic.F d := by
  have h1 := ic.loopMap_solvedMeasurement h p
  have h2 : ic.loopMap (ic.disturbanceMeasurement h d) = ic.F d := by
    rw [disturbanceMeasurement_apply]
    exact LinearMap.congr_fun (ic.loopMap_loopInv h) (ic.F d)
  simp only [loopMap_apply, loopForcing_apply] at h1 h2
  have h1' : ic.solvedMeasurement h p =
      (ic.plant.C p.1 + ic.plant.D (ic.controller.M p.2)) +
        ic.plant.D (ic.controller.N (ic.solvedMeasurement h p)) :=
    sub_eq_iff_eq_add.mp h1
  have h2' : ic.disturbanceMeasurement h d =
      ic.F d + ic.plant.D (ic.controller.N (ic.disturbanceMeasurement h d)) :=
    sub_eq_iff_eq_add.mp h2
  conv_lhs => rw [measuredSignal_eq_solvedMeasurement_add, h1', h2']
  rw [resolvedInput_apply, solvedInput_apply]
  simp only [map_add]
  abel

/-- **Uniqueness of the measured signal.** Any measurement satisfying the readout
with the measurement disturbance is the measured signal. -/
theorem measuredSignal_unique (h : ic.IsWellPosed) {p : X × W} {d : D} {y : Y}
    (hy : y = ic.plant.C p.1 +
      ic.plant.D (ic.controller.M p.2 + ic.controller.N y) + ic.F d) :
    y = ic.measuredSignal h p d := by
  apply h.1
  rw [ic.loopMap_measuredSignal h p d, loopMap_apply, loopForcing_apply]
  rw [sub_eq_iff_eq_add]
  calc y = ic.plant.C p.1 +
        ic.plant.D (ic.controller.M p.2 + ic.controller.N y) + ic.F d := hy
    _ = (ic.plant.C p.1 + ic.plant.D (ic.controller.M p.2) + ic.F d) +
          ic.plant.D (ic.controller.N y) := by
          rw [map_add]
          abel

/-- With no measurement disturbance channel the disturbance contribution to the
measurement vanishes. -/
theorem disturbanceMeasurement_of_F_eq_zero (h : ic.IsWellPosed) (hF : ic.F = 0) :
    ic.disturbanceMeasurement h = 0 := by
  rw [disturbanceMeasurement, hF, LinearMap.comp_zero]

/-- With no measurement disturbance channel the disturbance contribution to the
control vanishes. -/
theorem disturbanceInput_of_F_eq_zero (h : ic.IsWellPosed) (hF : ic.F = 0) :
    ic.disturbanceInput h = 0 := by
  rw [disturbanceInput, ic.disturbanceMeasurement_of_F_eq_zero h hF, LinearMap.comp_zero]

/-- **Zero-channel reduction of the measured signal.** With no measurement
disturbance channel (`F = 0`) the measured signal is the resolved measurement. -/
theorem measuredSignal_of_F_eq_zero (h : ic.IsWellPosed) (hF : ic.F = 0)
    (p : X × W) (d : D) :
    ic.measuredSignal h p d = ic.solvedMeasurement h p := by
  rw [measuredSignal_eq_solvedMeasurement_add, ic.disturbanceMeasurement_of_F_eq_zero h hF,
    LinearMap.zero_apply, add_zero]

/-- **Zero-channel reduction of the resolved input.** With `F = 0` the resolved
input is the resolved control. -/
theorem resolvedInput_of_F_eq_zero (h : ic.IsWellPosed) (hF : ic.F = 0)
    (p : X × W) (d : D) :
    ic.resolvedInput h p d = ic.solvedInput h p := by
  rw [resolvedInput_eq_solvedInput_add, ic.disturbanceInput_of_F_eq_zero h hF,
    LinearMap.zero_apply, add_zero]

/-- **Zero-disturbance reduction.** With no disturbance the measured signal is the
resolved measurement. -/
theorem measuredSignal_zero_disturbance (h : ic.IsWellPosed) (p : X × W) :
    ic.measuredSignal h p 0 = ic.solvedMeasurement h p :=
  by simp [measuredSignal]

/-- **Zero-disturbance reduction of the resolved input.** -/
theorem resolvedInput_zero_disturbance (h : ic.IsWellPosed) (p : X × W) :
    ic.resolvedInput h p 0 = ic.solvedInput h p :=
  by simp [resolvedInput]

theorem disturbanceMeasurement_zero (h : ic.IsWellPosed) :
    ic.disturbanceMeasurement h (0 : D) = 0 := map_zero _

theorem disturbanceInput_zero (h : ic.IsWellPosed) :
    ic.disturbanceInput h (0 : D) = 0 := map_zero _

/-- The **closed-loop disturbance map with the measurement channel**: the total
disturbance input of `p' = closedLoopMap p + Be d`, combining the state channel
`E d` with the disturbance contributions to the resolved control and measurement. -/
noncomputable def disturbanceMapWithF (h : ic.IsWellPosed) : D →ₗ[𝕜] X × W :=
  LinearMap.prod (ic.E + ic.plant.B.comp (ic.disturbanceInput h))
    (ic.controller.L.comp (ic.disturbanceMeasurement h))

@[simp]
theorem disturbanceMapWithF_apply (h : ic.IsWellPosed) (d : D) :
    ic.disturbanceMapWithF h d =
      (ic.E d + ic.plant.B (ic.disturbanceInput h d),
        ic.controller.L (ic.disturbanceMeasurement h d)) := rfl

/-- **Zero-channel reduction of the disturbance map.** With `F = 0` the
extended disturbance map is the state-only disturbance map. -/
theorem disturbanceMapWithF_of_F_eq_zero (h : ic.IsWellPosed) (hF : ic.F = 0) :
    ic.disturbanceMapWithF h = ic.disturbanceMap := by
  apply LinearMap.ext
  intro d
  rw [disturbanceMapWithF_apply, ic.disturbanceInput_of_F_eq_zero h hF,
    ic.disturbanceMeasurement_of_F_eq_zero h hF, disturbanceMap_apply]
  simp

/-- The **closed-loop dynamics with the measurement disturbance**: the extended
state derivative `(A x + B u + E d, K w + L y)` with `u` the resolved input and
`y` the measured signal. -/
noncomputable def closedLoopDynamicsWithF (h : ic.IsWellPosed) (p : X × W) (d : D) :
    X × W :=
  (ic.plant.A p.1 + ic.plant.B (ic.resolvedInput h p d) + ic.E d,
    ic.controller.K p.2 + ic.controller.L (ic.measuredSignal h p d))

/-- **Bookkeeping identity for the closed loop with the measurement disturbance.**
The extended dynamics decomposes into the autonomous extended map and the total
disturbance map `disturbanceMapWithF`. -/
theorem closedLoopDynamicsWithF_eq (h : ic.IsWellPosed) (p : X × W) (d : D) :
    ic.closedLoopDynamicsWithF h p d = ic.closedLoopMap h p + ic.disturbanceMapWithF h d := by
  apply Prod.ext
  · simp only [closedLoopDynamicsWithF, closedLoopMap_apply, disturbanceMapWithF_apply,
      resolvedInput_eq_solvedInput_add, solvedInput_apply, disturbanceInput_apply, map_add,
      Prod.fst_add]
    abel
  · simp only [closedLoopDynamicsWithF, closedLoopMap_apply, disturbanceMapWithF_apply,
      measuredSignal_eq_solvedMeasurement_add, map_add, Prod.snd_add]
    abel

/-! ### Well-posedness for a strictly proper plant -/

/-- For a strictly proper plant (`D = 0`) the algebraic-loop map is the
identity, so the interconnection is automatically well posed. -/
theorem loopMap_eq_one_of_D_eq_zero (hD : ic.plant.D = 0) : ic.loopMap = 1 := by
  rw [loopMap, hD, LinearMap.zero_comp, sub_zero]

/-- A strictly proper plant makes the dynamic measurement-feedback
interconnection well posed. -/
theorem isWellPosed_of_D_eq_zero (hD : ic.plant.D = 0) : ic.IsWellPosed := by
  rw [IsWellPosed, ic.loopMap_eq_one_of_D_eq_zero hD]
  exact Function.bijective_id

/-- For a strictly proper plant the resolved measurement is the plant output
`C x`. -/
theorem solvedMeasurement_of_D_eq_zero (hD : ic.plant.D = 0) (h : ic.IsWellPosed)
    (p : X × W) :
    ic.solvedMeasurement h p = ic.plant.C p.1 := by
  apply h.1
  rw [ic.loopMap_solvedMeasurement h p]
  simp only [loopMap_apply, loopForcing_apply]
  rw [hD]
  simp

/-- For a strictly proper plant the resolved control is `M w + N (C x)`. -/
theorem solvedInput_of_D_eq_zero (hD : ic.plant.D = 0) (h : ic.IsWellPosed)
    (p : X × W) :
    ic.solvedInput h p = ic.controller.M p.2 + ic.controller.N (ic.plant.C p.1) := by
  rw [solvedInput_apply, ic.solvedMeasurement_of_D_eq_zero hD h p]

/-- **The classical block operator.** For a strictly proper plant (`D = 0`) the
closed-loop state map is the block operator of
Trentelman–Stoorvogel–Hautus, equation (6.3):

`Ae (x, w) = ((A + B N C) x + B M w, L C x + K w)`. -/
theorem closedLoopMap_of_D_eq_zero (hD : ic.plant.D = 0) (h : ic.IsWellPosed)
    (p : X × W) :
    ic.closedLoopMap h p =
      ((ic.plant.A + ic.plant.B.comp (ic.controller.N.comp ic.plant.C)) p.1 +
        ic.plant.B (ic.controller.M p.2),
       ic.controller.L (ic.plant.C p.1) + ic.controller.K p.2) := by
  rw [ic.closedLoopMap_apply, ic.solvedInput_of_D_eq_zero hD h p,
    ic.solvedMeasurement_of_D_eq_zero hD h p]
  apply Prod.ext <;>
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add] <;> abel

/-! ### Zero-disturbance and zero-initial-state lemmas -/

theorem loopForcing_zero : ic.loopForcing (0 : X × W) = 0 := map_zero _

theorem solvedMeasurement_zero (h : ic.IsWellPosed) :
    ic.solvedMeasurement h (0 : X × W) = 0 := by
  simp [solvedMeasurement]

theorem solvedInput_zero (h : ic.IsWellPosed) :
    ic.solvedInput h (0 : X × W) = 0 := by
  simp [solvedInput, solvedMeasurement]

theorem closedLoopMap_zero (h : ic.IsWellPosed) :
    ic.closedLoopMap h (0 : X × W) = 0 := map_zero _

theorem disturbanceMap_zero : ic.disturbanceMap (0 : D) = 0 := map_zero _

theorem outputMap_zero : ic.outputMap (0 : X × W) = 0 := map_zero _

/-- **Zero disturbance.** With `d = 0` the closed-loop dynamics is the
autonomous extended map `Ae`. -/
theorem closedLoopSystem_dynamics_zero_disturbance (h : ic.IsWellPosed) (p : X × W) :
    (ic.closedLoopSystem h).dynamics p 0 = ic.closedLoopMap h p := by
  rw [ic.closedLoopSystem_dynamics h p 0, disturbanceMap_zero, add_zero]

/-- With zero disturbance and zero extended state the closed-loop dynamics
vanishes. -/
theorem closedLoopSystem_dynamics_zero_state_zero_disturbance (h : ic.IsWellPosed) :
    (ic.closedLoopSystem h).dynamics (0 : X × W) 0 = 0 := by
  rw [ic.closedLoopSystem_dynamics_zero_disturbance h (0 : X × W), closedLoopMap_zero]

/-- With zero disturbance and zero extended state the controlled output
vanishes. -/
theorem outputMap_zero_state : ic.outputMap (0 : X × W) = 0 :=
  ic.outputMap_zero

/-! ### The closed-loop disturbance channel -/

/-- The algebraic **disturbance-decoupling predicate of the closed loop**: the
controlled output is independent of the disturbance input, i.e. the Markov
parameters `He Ae^k Be` all vanish. This is the exact predicate whose
feasibility the deferred dynamic decoupling theorem will settle; here it is only
defined and related to the closed-loop maps. -/
noncomputable def IsClosedLoopDisturbanceDecoupled (h : ic.IsWellPosed) : Prop :=
  LinearMap.IsDisturbanceDecoupled (ic.closedLoopMap h) ic.disturbanceMap ic.outputMap

/-- Unfolding of `IsClosedLoopDisturbanceDecoupled` in terms of the closed-loop
system. -/
theorem isClosedLoopDisturbanceDecoupled_iff (h : ic.IsWellPosed) :
    ic.IsClosedLoopDisturbanceDecoupled h ↔
      LinearMap.IsDisturbanceDecoupled (ic.closedLoopSystem h).A
        (ic.closedLoopSystem h).B (ic.closedLoopSystem h).C := Iff.rfl

/-- The closed-loop disturbance channel is decoupled exactly when the closed
loop's reachable subspace from the disturbance is unobservable at the controlled
output. This is the closed-loop instance of the accepted algebraic Theorem 4.6. -/
theorem isClosedLoopDisturbanceDecoupled_iff_reachableSubspace_le_ker
    (h : ic.IsWellPosed) :
    ic.IsClosedLoopDisturbanceDecoupled h ↔
      LinearMap.reachableSubspace (ic.closedLoopMap h) ic.disturbanceMap ≤
        LinearMap.ker ic.outputMap :=
  LinearMap.isDisturbanceDecoupled_iff_reachableSubspace_le_ker _ _ _

/-! ### The closed-loop disturbance channel with the measurement disturbance

The predicate `IsClosedLoopDisturbanceDecoupled` above is the state-disturbance
predicate built from `disturbanceMap`. With the measurement disturbance `F` the
correct closed-loop disturbance channel is `disturbanceMapWithF`, and the scoped
predicate `IsClosedLoopDisturbanceDecoupledWithF` records decoupling for that
channel. Its only use below is the zero-channel reduction to the accepted
predicate: the full channel-decoupling synthesis theorem for nonzero `F` is
**not** claimed. -/

/-- The closed-loop **with the measurement disturbance channel**: the controlled
output is independent of the disturbance when every Markov parameter of the
extended channel `(closedLoopMap, disturbanceMapWithF)` vanishes. -/
noncomputable def IsClosedLoopDisturbanceDecoupledWithF (h : ic.IsWellPosed) : Prop :=
  LinearMap.IsDisturbanceDecoupled (ic.closedLoopMap h) (ic.disturbanceMapWithF h)
    ic.outputMap

/-- **Zero-channel reduction of decoupling.** With `F = 0` the extended
decoupling predicate is the accepted state-disturbance predicate. -/
theorem isClosedLoopDisturbanceDecoupledWithF_of_F_eq_zero (h : ic.IsWellPosed)
    (hF : ic.F = 0) :
    ic.IsClosedLoopDisturbanceDecoupledWithF h ↔ ic.IsClosedLoopDisturbanceDecoupled h := by
  rw [IsClosedLoopDisturbanceDecoupledWithF, IsClosedLoopDisturbanceDecoupled,
    ic.disturbanceMapWithF_of_F_eq_zero h hF]

/-- Pointwise (Markov-parameter) form of the extended decoupling predicate. -/
theorem isClosedLoopDisturbanceDecoupledWithF_iff_forall (h : ic.IsWellPosed) :
    ic.IsClosedLoopDisturbanceDecoupledWithF h ↔
      ∀ k : ℕ, ∀ d : D,
        ic.outputMap ((ic.closedLoopMap h ^ k) (ic.disturbanceMapWithF h d)) = 0 :=
  LinearMap.isDisturbanceDecoupled_iff_forall _ _ _

/-- Reachable-subspace form of the extended decoupling predicate. -/
theorem isClosedLoopDisturbanceDecoupledWithF_iff_reachableSubspace_le_ker
    (h : ic.IsWellPosed) :
    ic.IsClosedLoopDisturbanceDecoupledWithF h ↔
      LinearMap.reachableSubspace (ic.closedLoopMap h) (ic.disturbanceMapWithF h) ≤
        LinearMap.ker ic.outputMap :=
  LinearMap.isDisturbanceDecoupled_iff_reachableSubspace_le_ker _ _ _

end DynamicInterconnection

/-! ## Trajectory lemmas for the closed loop

Over the reals and in finite dimension the closed-loop system `closedLoopSystem`
inherits the whole accepted variation-of-constants API of
`DynamicalSystems.Linear.Trajectory`. The zero-initial-state, zero-disturbance
trajectory and its controlled output are identically zero. -/

namespace DynamicInterconnection

section Analytic

variable {X U Y W D Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [AddCommGroup U] [Module ℝ U] [AddCommGroup Y] [Module ℝ Y]
variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ W] [FiniteDimensional ℝ D]
variable (ic : DynamicInterconnection ℝ X U Y W D Z)

/-- The closed-loop forcing integrand vanishes for the zero disturbance. -/
theorem closedLoopSystem_forcing_zero (h : ic.IsWellPosed) (t₀ : ℝ) :
    (ic.closedLoopSystem h).forcing t₀ (0 : ℝ → D) = 0 := by
  funext s
  simp only [LinearSystem.forcing, Pi.zero_apply]
  rw [map_zero, map_zero]

/-- **Zero-initial-state, zero-disturbance trajectory.** The closed-loop
trajectory from the origin under no disturbance is identically zero. -/
theorem closedLoopSystem_variationOfConstants_zero
    (h : ic.IsWellPosed) (t₀ t : ℝ) :
    (ic.closedLoopSystem h).variationOfConstants t₀ (0 : X × W) (0 : ℝ → D) t = 0 := by
  rw [LinearSystem.variationOfConstants, ic.closedLoopSystem_forcing_zero h t₀]
  simp

/-- **Zero-initial-state, zero-disturbance output.** The controlled output of
the closed-loop trajectory from the origin under no disturbance is zero. -/
theorem closedLoopSystem_readout_variationOfConstants_zero
    (h : ic.IsWellPosed) (t₀ t : ℝ) :
    (ic.closedLoopSystem h).readout
        ((ic.closedLoopSystem h).variationOfConstants t₀ (0 : X × W) (0 : ℝ → D) t) 0 = 0 := by
  rw [ic.closedLoopSystem_variationOfConstants_zero h t₀ t]
  simp [LinearSystem.readout]

/-- With zero disturbance the variation-of-constants trajectory of the closed
loop is the autonomous homogeneous solution. This is the trajectory form of
`closedLoopSystem_dynamics_zero_disturbance`. -/
theorem closedLoopSystem_variationOfConstants_eq_homogeneous (h : ic.IsWellPosed)
    (t₀ : ℝ) (p₀ : X × W) :
    (ic.closedLoopSystem h).variationOfConstants t₀ p₀ (0 : ℝ → D) =
      (ic.closedLoopSystem h).homogeneousSolution t₀ p₀ := by
  funext t
  rw [LinearSystem.variationOfConstants, LinearSystem.homogeneousSolution,
    ic.closedLoopSystem_forcing_zero h t₀]
  simp

end Analytic

end DynamicInterconnection

/-! ## The converse: extended geometry and the necessity direction

Section 6.1 of Trentelman–Stoorvogel–Hautus associates with a subspace `Ve` of
the extended state space `X × W` the two subspaces of the original state space

`i(Ve) = {x | (x, 0) ∈ Ve}`,  `p(Ve) = {x | ∃ w, (x, w) ∈ Ve}`

(equations (6.5)–(6.6)): `i(Ve)` is the intersection of `Ve` with the
`X`-plane and `p(Ve)` is its projection onto that plane. Theorem 6.2 states that
if `Ve` is invariant under an extended system mapping, then `(i(Ve), p(Ve))` is a
`(C, A, B)`-pair. This is the geometric extraction used in the necessity direction
of disturbance decoupling by measurement feedback (the `⇒` half of Theorem 6.6):
a decoupled closed loop supplies an `Ae`-invariant `Ve` between `im Ee` and
`ker He`, whose intersection and projection then form a `(C, A, B)`-pair between
`im E` and `ker H`.

The extraction is purely algebraic and does not require a strictly proper plant:
only well-posedness of the interconnection is used, so that the resolved
measurement of `(x, 0)` vanishes when `C x = 0`. -/

namespace DynamicInterconnection

variable (ic : DynamicInterconnection 𝕜 X U Y W D Z)

/-- The **intersection** `i(Ve)` of an extended subspace `Ve ≤ X × W` with the
`X`-plane: `i(Ve) = {x : X | (x, 0) ∈ Ve}`.

Source: Trentelman–Stoorvogel–Hautus, equation (6.6). -/
def extendedIntersection (Ve : Submodule 𝕜 (X × W)) : Submodule 𝕜 X :=
  Ve.comap (LinearMap.inl 𝕜 X W)

theorem mem_extendedIntersection {Ve : Submodule 𝕜 (X × W)} {x : X} :
    x ∈ extendedIntersection Ve ↔ (x, 0) ∈ Ve := by
  rw [extendedIntersection, Submodule.mem_comap, LinearMap.inl_apply]

/-- The **projection** `p(Ve)` of an extended subspace `Ve ≤ X × W` onto the
`X`-plane: `p(Ve) = {x : X | ∃ w : W, (x, w) ∈ Ve}`.

Source: Trentelman–Stoorvogel–Hautus, equation (6.5). -/
def extendedProjection (Ve : Submodule 𝕜 (X × W)) : Submodule 𝕜 X :=
  Ve.map (LinearMap.fst 𝕜 X W)

theorem mem_extendedProjection {Ve : Submodule 𝕜 (X × W)} {x : X} :
    x ∈ extendedProjection Ve ↔ ∃ w : W, (x, w) ∈ Ve := by
  constructor
  · intro hx
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    exact ⟨p.2, by simpa using hp⟩
  · rintro ⟨w, hw⟩
    exact Submodule.mem_map.mpr ⟨(x, w), hw, rfl⟩

/-- **Theorem 6.2 (conditioned invariance of the intersection).** If `Ve` is
invariant under the closed-loop map `Ae`, then its intersection `i(Ve)` with the
`X`-plane is `(C, A)`-invariant.

For `x ∈ i(Ve) ∩ ker C` the resolved measurement of `(x, 0)` vanishes, so
`Ae (x, 0) = (A x, 0) ∈ Ve`. -/
theorem isConditionedInvariant_extendedIntersection
    (h : ic.IsWellPosed) (Ve : Submodule 𝕜 (X × W))
    (hVe : Submodule.map (ic.closedLoopMap h) Ve ≤ Ve) :
    LinearMap.IsConditionedInvariant ic.plant.C ic.plant.A
      (extendedIntersection Ve) := by
  rw [LinearMap.isConditionedInvariant_iff]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  obtain ⟨hxS, hxC⟩ := Submodule.mem_inf.mp hx
  rw [mem_extendedIntersection]
  have hxV : (x, 0) ∈ Ve := (mem_extendedIntersection).mp hxS
  have hAe : ic.closedLoopMap h (x, 0) ∈ Ve := hVe ⟨(x, 0), hxV, rfl⟩
  have hy0 : ic.solvedMeasurement h (x, 0) = 0 := by
    apply h.1
    rw [ic.loopMap_solvedMeasurement h (x, 0), map_zero]
    simp only [loopForcing_apply, map_zero, add_zero]
    exact LinearMap.mem_ker.mp hxC
  have hu0 : ic.solvedInput h (x, 0) = 0 := by
    rw [ic.solvedInput_apply, hy0]
    simp
  have hAe0 : ic.closedLoopMap h (x, 0) = (ic.plant.A x, 0) := by
    rw [ic.closedLoopMap_apply, hu0, hy0]
    simp
  simpa [hAe0] using hAe

/-- **Theorem 6.2 (controlled invariance of the projection).** If `Ve` is
invariant under the closed-loop map `Ae`, then its projection `p(Ve)` onto the
`X`-plane contains `A p(Ve)` modulo the input channel `im B`.

For `(x, w) ∈ Ve` the first component of `Ae (x, w)` is `A x + B u`, so
`A x ∈ p(Ve) + im B`. -/
theorem isControlledInvariant_extendedProjection
    (h : ic.IsWellPosed) (Ve : Submodule 𝕜 (X × W))
    (hVe : Submodule.map (ic.closedLoopMap h) Ve ≤ Ve) :
    LinearMap.IsControlledInvariant ic.plant.A ic.plant.B
      (extendedProjection Ve) := by
  rw [LinearMap.isControlledInvariant_iff]
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
  obtain ⟨w, hw⟩ := (mem_extendedProjection).mp hx
  have hAe : ic.closedLoopMap h (x, w) ∈ Ve := hVe ⟨(x, w), hw, rfl⟩
  have hmemV : ic.plant.A x + ic.plant.B (ic.solvedInput h (x, w)) ∈
      extendedProjection Ve := by
    refine Submodule.mem_map.mpr ⟨ic.closedLoopMap h (x, w), hAe, ?_⟩
    simp
  have hsub : (ic.plant.A x + ic.plant.B (ic.solvedInput h (x, w))) -
      ic.plant.B (ic.solvedInput h (x, w)) ∈
      extendedProjection Ve ⊔ LinearMap.range ic.plant.B :=
    Submodule.sub_mem_sup hmemV (LinearMap.mem_range.mpr ⟨ic.solvedInput h (x, w), rfl⟩)
  rwa [add_sub_cancel_right] at hsub

/-- **Theorem 6.2.** An `Ae`-invariant subspace `Ve` of the extended state space
gives rise to a `(C, A, B)`-pair `(i(Ve), p(Ve))`, the intersection and the
projection of `Ve`.

Source: Trentelman–Stoorvogel–Hautus, Theorem 6.2. -/
theorem isCABPair_extendedIntersection_extendedProjection
    (h : ic.IsWellPosed) (Ve : Submodule 𝕜 (X × W))
    (hVe : Submodule.map (ic.closedLoopMap h) Ve ≤ Ve) :
    LinearMap.IsCABPair ic.plant.C ic.plant.A ic.plant.B
      (extendedIntersection Ve) (extendedProjection Ve) := by
  refine ⟨?_, ic.isConditionedInvariant_extendedIntersection h Ve hVe,
    ic.isControlledInvariant_extendedProjection h Ve hVe⟩
  intro x hx
  exact (mem_extendedProjection).mpr ⟨0, (mem_extendedIntersection).mp hx⟩

/-- **Necessity half of Theorem 6.6.** A well-posed, disturbance-decoupled
dynamic measurement-feedback interconnection yields a `(C, A, B)`-pair between
`im E` and `ker H`.

By Theorem 4.6 the decoupling supplies an `Ae`-invariant extended subspace `Ve`
with `im Ee ≤ Ve ≤ ker He`; its intersection `i(Ve)` and projection `p(Ve)` form
the required `(C, A, B)`-pair by Theorem 6.2, and the two inclusions transfer
because `Ee d = (E d, 0)` and `He (x, w) = H x`. -/
theorem exists_isCABPairBetween_of_isClosedLoopDisturbanceDecoupled
    (h : ic.IsWellPosed) (hdec : ic.IsClosedLoopDisturbanceDecoupled h) :
    ∃ S V : Submodule 𝕜 X,
      LinearMap.IsCABPairBetween ic.plant.C ic.plant.A ic.plant.B ic.E ic.H S V := by
  obtain ⟨Ve, hEe, hHe, hVe⟩ :=
    (LinearMap.isDisturbanceDecoupled_iff_exists_invariant
      (ic.closedLoopMap h) ic.disturbanceMap ic.outputMap).mp hdec
  refine ⟨extendedIntersection Ve, extendedProjection Ve,
    ic.isCABPair_extendedIntersection_extendedProjection h Ve hVe, ?_, ?_⟩
  · rintro _ ⟨d, rfl⟩
    rw [mem_extendedIntersection]
    exact hEe ⟨d, ic.disturbanceMap_apply d⟩
  · intro x hx
    obtain ⟨w, hw⟩ := (mem_extendedProjection).mp hx
    have h0 : ic.H x = 0 := by
      have := LinearMap.mem_ker.mp (hHe hw)
      rwa [ic.outputMap_apply] at this
    exact LinearMap.mem_ker.mpr h0

end DynamicInterconnection

/-! ## Dynamic decoupling synthesis (Chapter 6)

This section implements the constructive direction of
Trentelman–Stoorvogel–Hautus, Theorem 6.4 and Corollary 6.7: from a
`(C, A, B)`-pair `(S, V)` between `im E` and `ker H` we build the controller
`(6.7)`

`w' = (A + B F + G C - B N C) w + (B N - G) y`, `u = (F - N C) w + N y`,

with state space `W = X`, and prove that its closed loop is disturbance
decoupled. The three gain maps are the ones supplied by the accepted
geometric-invariance API (`exists_stateFeedback_of_isControlledInvariant`,
`exists_outputInjection_of_isConditionedInvariant`) together with the output
feedback `N` of Lemma 6.3 (`exists_outputFeedback_of_isCABPair`). -/

section Synthesis

variable {𝕜 X U Y Z D : Type*}
variable [Field 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup Y] [Module 𝕜 Y]
variable [AddCommGroup Z] [Module 𝕜 Z]
variable [AddCommGroup D] [Module 𝕜 D]

/-- **Lemma 6.3 (output feedback).** If `S ≤ V`, `S` is `(C, A)`-invariant and
`V` is `(A, B)`-invariant, then there is an output feedback `N : Y →ₗ[𝕜] U`
with `(A + B N C) S ≤ V`.

The map `S ∋ s ↦ A s mod V` vanishes on `S ∩ ker C` (conditioned invariance),
so it descends through `C|_S`; its range lies in the range of `B mod V`
(controlled invariance), so it lifts through `B`. Extending the resulting map
from `C S` to all of `Y` gives `N`.

Source: Trentelman–Stoorvogel–Hautus, Lemma 6.3. -/
theorem exists_outputFeedback_of_isCABPair
    {C : X →ₗ[𝕜] Y} {A : X →ₗ[𝕜] X} {B : U →ₗ[𝕜] X} {S V : Submodule 𝕜 X}
    (hSV : S ≤ V) (hS : LinearMap.IsConditionedInvariant C A S)
    (hV : LinearMap.IsControlledInvariant A B V) :
    ∃ N : Y →ₗ[𝕜] U, Submodule.map (A + B.comp (N.comp C)) S ≤ V := by
  let f : S →ₗ[𝕜] X ⧸ V := V.mkQ.comp (A.comp S.subtype)
  let g : U →ₗ[𝕜] X ⧸ V := V.mkQ.comp B
  have hker : LinearMap.ker (C.comp S.subtype) ≤ LinearMap.ker f := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [LinearMap.comp_apply] at hx
    change V.mkQ (A (x : X)) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hSV (hS ⟨x, Submodule.mem_inf.mpr ⟨x.2, hx⟩, rfl⟩)
  have hrange : LinearMap.range f ≤ LinearMap.range g := by
    rintro _ ⟨s, rfl⟩
    have hAv : A (s : X) ∈ V ⊔ LinearMap.range B := hV ⟨(s : X), hSV s.2, rfl⟩
    rw [Submodule.mem_sup] at hAv
    obtain ⟨v, hv, w, hw, hvw⟩ := hAv
    obtain ⟨u, rfl⟩ := hw
    refine ⟨u, ?_⟩
    have hA : V.mkQ (A (s : X)) = V.mkQ (B u) := by
      rw [← hvw, map_add, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero V).mpr hv,
        zero_add]
    exact hA.symm
  let fbar : S ⧸ LinearMap.ker (C.comp S.subtype) →ₗ[𝕜] X ⧸ V :=
    (LinearMap.ker (C.comp S.subtype)).liftQ f hker
  let e := (C.comp S.subtype).quotKerEquivRange
  let ψ : LinearMap.range (C.comp S.subtype) →ₗ[𝕜] X ⧸ V := fbar.comp e.symm.toLinearMap
  have hψrange : LinearMap.range ψ ≤ LinearMap.range g := by
    have h1 : LinearMap.range ψ = LinearMap.range fbar := by
      dsimp only [ψ]
      rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr e.symm.surjective,
        Submodule.map_top]
    have h2 : LinearMap.range fbar = LinearMap.range f := by
      dsimp only [fbar]
      exact Submodule.range_liftQ (LinearMap.ker (C.comp S.subtype)) f hker
    rw [h1, h2]
    exact hrange
  let g' : U →ₗ[𝕜] LinearMap.range g := g.codRestrict (LinearMap.range g) (fun u => ⟨u, rfl⟩)
  have hg'surj : Function.Surjective g' := by
    rintro ⟨y, hy⟩
    obtain ⟨u, rfl⟩ := hy
    exact ⟨u, Subtype.ext rfl⟩
  let ψ' : LinearMap.range (C.comp S.subtype) →ₗ[𝕜] LinearMap.range g :=
    ψ.codRestrict (LinearMap.range g) (fun p => hψrange ⟨p, rfl⟩)
  obtain ⟨χ, hχ⟩ := Module.projective_lifting_property g' ψ' hg'surj
  obtain ⟨N, hN⟩ := LinearMap.exists_extend (-χ)
  refine ⟨N, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  change A s + B (N (C s)) ∈ V
  rw [← Submodule.Quotient.mk_eq_zero V]
  change V.mkQ (A s + B (N (C s))) = 0
  have hNs : N (C s) = -χ ⟨C s, ⟨⟨s, hs⟩, rfl⟩⟩ := by
    have := congrArg (fun h => h ⟨C s, ⟨⟨s, hs⟩, rfl⟩⟩) hN
    simpa [LinearMap.comp_apply] using this
  have hψs : ψ ⟨C s, ⟨⟨s, hs⟩, rfl⟩⟩ = V.mkQ (A s) := by
    have he : e (Submodule.Quotient.mk ⟨s, hs⟩) = ⟨C s, ⟨⟨s, hs⟩, rfl⟩⟩ := by
      apply Subtype.ext
      rw [LinearMap.quotKerEquivRange_apply_mk]
      rfl
    have hes : e.symm ⟨C s, ⟨⟨s, hs⟩, rfl⟩⟩ = Submodule.Quotient.mk ⟨s, hs⟩ := by
      rw [← he, LinearEquiv.symm_apply_apply]
    simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, hes, fbar,
      Submodule.liftQ_apply, f, Submodule.mkQ_apply]
    rfl
  have hgχ : g (χ ⟨C s, ⟨⟨s, hs⟩, rfl⟩⟩) = ψ ⟨C s, ⟨⟨s, hs⟩, rfl⟩⟩ := by
    have := congrArg (fun h => h ⟨C s, ⟨⟨s, hs⟩, rfl⟩⟩) hχ
    exact congrArg Subtype.val this
  rw [map_add]
  change V.mkQ (A s) + g (N (C s)) = 0
  rw [hNs, map_neg, hgχ, hψs, add_neg_cancel]

/-- The controller `(6.7)` of Trentelman–Stoorvogel–Hautus associated with a
`(C, A, B)`-pair: `K = A + B F + G C - B N C`, `L = B N - G`, `M = F - N C`,
with state space `W = X`. -/
def cabPairController (sys : LinearSystem 𝕜 X U Y) (F : X →ₗ[𝕜] U)
    (G : Y →ₗ[𝕜] X) (N : Y →ₗ[𝕜] U) : DynamicController 𝕜 X Y U where
  K := sys.A + sys.B.comp F + G.comp sys.C - sys.B.comp (N.comp sys.C)
  L := sys.B.comp N - G
  M := F - N.comp sys.C
  N := N

/-- The dynamic measurement-feedback interconnection obtained from a plant, a
controller with state space `X`, a state disturbance channel `E` and a
controlled-output map `H`. -/
def cabPairInterconnection (sys : LinearSystem 𝕜 X U Y)
    (ctrl : DynamicController 𝕜 X Y U) (E : D →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z) :
    DynamicInterconnection 𝕜 X U Y X D Z :=
  ⟨sys, ctrl, E, 0, H⟩

/-- The synthesis interconnection of Theorem 6.4 has a zero measurement
disturbance channel: the construction of Chapter 6 only uses the state
disturbance `E`, so the extended decoupling predicate coincides with the
state-disturbance one. -/
@[simp]
theorem cabPairInterconnection_F (sys : LinearSystem 𝕜 X U Y)
    (ctrl : DynamicController 𝕜 X Y U) (E : D →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z) :
    (cabPairInterconnection sys ctrl E H).F = 0 := rfl

/-- **Theorem 6.4 / Corollary 6.7 (synthesis).** For a strictly proper plant
(`D = 0`), any `(C, A, B)`-pair `(S, V)` between `im E` and `ker H`, together
with gains `F`, `G`, `N` satisfying
`(A + B F) V ≤ V`, `(A + G C) S ≤ S` and `(A + B N C) S ≤ V`, produces a
controller whose closed loop is disturbance decoupled.

The invariant extended subspace is `V_e = {(x₁,0) + (x₂,x₂) | x₁ ∈ S, x₂ ∈ V}`
(Trentelman–Stoorvogel–Hautus, equation (6.16)); it contains the disturbance
image and lies in the kernel of the controlled output, so Theorem 4.6 applies. -/
theorem isClosedLoopDisturbanceDecoupled_of_isCABPairBetween
    (sys : LinearSystem 𝕜 X U Y) (hD : sys.D = 0)
    (E : D →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z) (S V : Submodule 𝕜 X)
    (hpair : LinearMap.IsCABPairBetween sys.C sys.A sys.B E H S V)
    (F : X →ₗ[𝕜] U) (G : Y →ₗ[𝕜] X) (N : Y →ₗ[𝕜] U)
    (hF : Submodule.map (sys.A + sys.B.comp F) V ≤ V)
    (hG : Submodule.map (sys.A + G.comp sys.C) S ≤ S)
    (hN : Submodule.map (sys.A + sys.B.comp (N.comp sys.C)) S ≤ V)
    (hwp : (cabPairInterconnection sys (cabPairController sys F G N) E H).IsWellPosed) :
    (cabPairInterconnection sys (cabPairController sys F G N) E H).IsClosedLoopDisturbanceDecoupled
      hwp := by
  obtain ⟨⟨hSV, hS, hV⟩, hE, hH⟩ := hpair
  let ic : DynamicInterconnection 𝕜 X U Y X D Z :=
    cabPairInterconnection sys (cabPairController sys F G N) E H
  have hcl0 : ∀ x : X, ic.closedLoopMap hwp (x, 0) =
      (sys.A x + sys.B (N (sys.C x)), sys.B (N (sys.C x)) - G (sys.C x)) := by
    intro x
    rw [ic.closedLoopMap_of_D_eq_zero hD hwp (x, 0)]
    ext <;> simp only [ic, cabPairInterconnection, cabPairController, map_zero,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, add_zero]
  have hcl2 : ∀ x : X, ic.closedLoopMap hwp (x, x) =
      ((sys.A + sys.B.comp F) x, (sys.A + sys.B.comp F) x) := by
    intro x
    rw [ic.closedLoopMap_of_D_eq_zero hD hwp (x, x)]
    ext <;> simp only [ic, cabPairInterconnection, cabPairController, LinearMap.add_apply,
      LinearMap.sub_apply, LinearMap.comp_apply, map_sub] <;> abel
  refine (LinearMap.isDisturbanceDecoupled_iff_exists_invariant _ _ _).mpr ?_
  let φ : S × V →ₗ[𝕜] X × X :=
    LinearMap.prod (S.subtype.coprod V.subtype) (V.subtype.comp (LinearMap.snd 𝕜 S V))
  let Ve : Submodule 𝕜 (X × X) := LinearMap.range φ
  refine ⟨Ve, ?_, ?_, ?_⟩
  · rintro _ ⟨d, rfl⟩
    exact ⟨(⟨E d, hE ⟨d, rfl⟩⟩, ⟨0, V.zero_mem⟩), by
      ext <;> simp [φ, LinearMap.coprod_apply, cabPairInterconnection]⟩
  · rintro _ ⟨q, rfl⟩
    obtain ⟨x1, x2⟩ := q
    change H ((x1 : X) + (x2 : X)) = 0
    rw [map_add, LinearMap.mem_ker.mp (hH (hSV x1.2)),
      LinearMap.mem_ker.mp (hH x2.2), add_zero]
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨p, rfl⟩ := hq
    obtain ⟨x1, x2⟩ := p
    have hdecomp : φ (x1, x2) = ((x1 : X), 0) + ((x2 : X), (x2 : X)) := by
      ext <;> simp [φ, LinearMap.coprod_apply]
    rw [hdecomp, map_add]
    refine Ve.add_mem ?_ ?_
    · have hNx1 : (sys.A + sys.B.comp (N.comp sys.C)) (x1 : X) ∈ V :=
        hN ⟨(x1 : X), x1.2, rfl⟩
      have hGx1 : (sys.A + G.comp sys.C) (x1 : X) ∈ S :=
        hG ⟨(x1 : X), x1.2, rfl⟩
      refine ⟨(⟨(sys.A + G.comp sys.C) (x1 : X), hGx1⟩,
        ⟨sys.B (N (sys.C (x1 : X))) - G (sys.C (x1 : X)), ?_⟩), ?_⟩
      · have hsub : (sys.A + sys.B.comp (N.comp sys.C)) (x1 : X) -
            (sys.A + G.comp sys.C) (x1 : X) ∈ V :=
          V.sub_mem hNx1 (hSV hGx1)
        simpa [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply] using hsub
      · rw [hcl0 (x1 : X)]
        ext <;> simp [φ, LinearMap.coprod_apply]
    · have hFx2 : (sys.A + sys.B.comp F) (x2 : X) ∈ V :=
        hF ⟨(x2 : X), x2.2, rfl⟩
      refine ⟨(⟨0, S.zero_mem⟩, ⟨(sys.A + sys.B.comp F) (x2 : X), hFx2⟩), ?_⟩
      rw [hcl2 (x2 : X)]
      ext <;> simp [φ, LinearMap.coprod_apply]

/-- **The synthesis also satisfies the extended decoupling predicate.** Because
the controller (6.7) is built with a zero measurement-disturbance channel, its
closed loop is disturbance decoupled for the extended channel as well. This is
the only sense in which the synthesis touches the `F`-channel; no nonzero-`F`
decoupling statement is made. -/
theorem isClosedLoopDisturbanceDecoupledWithF_of_isCABPairBetween
    (sys : LinearSystem 𝕜 X U Y) (hD : sys.D = 0)
    (E : D →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z) (S V : Submodule 𝕜 X)
    (hpair : LinearMap.IsCABPairBetween sys.C sys.A sys.B E H S V)
    (F : X →ₗ[𝕜] U) (G : Y →ₗ[𝕜] X) (N : Y →ₗ[𝕜] U)
    (hF : Submodule.map (sys.A + sys.B.comp F) V ≤ V)
    (hG : Submodule.map (sys.A + G.comp sys.C) S ≤ S)
    (hN : Submodule.map (sys.A + sys.B.comp (N.comp sys.C)) S ≤ V)
    (hwp : (cabPairInterconnection sys (cabPairController sys F G N) E H).IsWellPosed) :
    (cabPairInterconnection sys (cabPairController sys F G N) E
      H).IsClosedLoopDisturbanceDecoupledWithF hwp := by
  let ic : DynamicInterconnection 𝕜 X U Y X D Z :=
    cabPairInterconnection sys (cabPairController sys F G N) E H
  have hF0 : ic.F = 0 := rfl
  exact (ic.isClosedLoopDisturbanceDecoupledWithF_of_F_eq_zero hwp hF0).mpr
    (isClosedLoopDisturbanceDecoupled_of_isCABPairBetween sys hD E H S V hpair F G N
      hF hG hN hwp)

/-- **Theorem 6.6 / Corollary 6.7 (existence of a decoupling controller).** For a
strictly proper plant (`D = 0`), a `(C, A, B)`-pair between `im E` and `ker H`
yields a finite-dimensional dynamic measurement-feedback controller which is
well posed and whose closed loop is disturbance decoupled.

The controller is the one of equation `(6.7)`: the gains `F`, `G` come from the
controlled- and conditioned-invariance certificates and `N` from Lemma 6.3;
well-posedness is automatic for a strictly proper plant. -/
theorem exists_dynamicController_of_isCABPairBetween
    (sys : LinearSystem 𝕜 X U Y) (hD : sys.D = 0)
    (E : D →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z) (S V : Submodule 𝕜 X)
    (hpair : LinearMap.IsCABPairBetween sys.C sys.A sys.B E H S V) :
    ∃ ctrl : DynamicController 𝕜 X Y U,
      (cabPairInterconnection sys ctrl E H).IsClosedLoopDisturbanceDecoupled
        ((cabPairInterconnection sys ctrl E H).isWellPosed_of_D_eq_zero hD) := by
  have hpair' := hpair
  obtain ⟨⟨hSV, hS, hV⟩, -, -⟩ := hpair'
  obtain ⟨F, hF⟩ := LinearMap.exists_stateFeedback_of_isControlledInvariant hV
  obtain ⟨G, hG⟩ := LinearMap.exists_outputInjection_of_isConditionedInvariant hS
  obtain ⟨N, hN⟩ := exists_outputFeedback_of_isCABPair hSV hS hV
  exact ⟨cabPairController sys F G N,
    isClosedLoopDisturbanceDecoupled_of_isCABPairBetween sys hD E H S V hpair F G N hF hG hN
      ((cabPairInterconnection sys (cabPairController sys F G N) E H).isWellPosed_of_D_eq_zero hD)⟩

/-- **Theorem 6.6 (necessity and sufficiency) for a strictly proper plant.**
Disturbance decoupling by dynamic measurement feedback is possible if and only
if there is a `(C, A, B)`-pair between `im E` and `ker H`.

The sufficiency direction is the constructive synthesis of Theorem 6.4
(`exists_dynamicController_of_isCABPairBetween`); the necessity direction
extracts the pair from an invariant extended subspace of a decoupled closed loop
(`exists_isCABPairBetween_of_isClosedLoopDisturbanceDecoupled`). The claim is
stated for a strictly proper plant, where well-posedness is automatic: the
extraction only needs well-posedness, while the synthesis uses `D = 0`. -/
theorem exists_dynamicController_disturbanceDecoupled_iff_isCABPairBetween
    (sys : LinearSystem 𝕜 X U Y) (hD : sys.D = 0)
    (E : D →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z) :
    (∃ ctrl : DynamicController 𝕜 X Y U,
        (cabPairInterconnection sys ctrl E H).IsClosedLoopDisturbanceDecoupled
          ((cabPairInterconnection sys ctrl E H).isWellPosed_of_D_eq_zero hD)) ↔
      ∃ S V : Submodule 𝕜 X,
        LinearMap.IsCABPairBetween sys.C sys.A sys.B E H S V := by
  constructor
  · rintro ⟨ctrl, hdec⟩
    let ic := cabPairInterconnection sys ctrl E H
    have hwp : ic.IsWellPosed := ic.isWellPosed_of_D_eq_zero hD
    exact ic.exists_isCABPairBetween_of_isClosedLoopDisturbanceDecoupled hwp hdec
  · rintro ⟨S, V, hpair⟩
    exact exists_dynamicController_of_isCABPairBetween sys hD E H S V hpair

end Synthesis

section ObserverErrorEquiv

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

/-- The **observer-error coordinate change** `(x, w) ↦ (x, x - w)` on the
extended state space `X × X`. It is an involution, so it is its own inverse. In
these coordinates the closed loop of the observer-based controller (6.7) becomes
block upper triangular with state-feedback block `A + B F` and observer-error
block `A + G C`.

Sign convention: the second coordinate is the observer error `e = x - w`
(`x` the plant state, `w` the controller state). The controller (6.7) injects the
measurement through `+G C`, so the error block is `A + G C`; the Luenberger form
`A - L.comp C` of the task contract is recovered by the substitution `L = -G`
(see `observerErrorBlock_eq`). -/
noncomputable def observerErrorEquiv (X : Type*) [AddCommGroup X] [Module ℝ X] :
    (X × X) ≃ₗ[ℝ] (X × X) where
  toFun p := (p.1, p.1 - p.2)
  invFun p := (p.1, p.1 - p.2)
  left_inv p := by rcases p with ⟨x, w⟩; simp
  right_inv p := by rcases p with ⟨x, e⟩; simp
  map_add' p q := by
    rcases p with ⟨x₁, w₁⟩; rcases q with ⟨x₂, w₂⟩
    simp only [Prod.mk_add_mk]
    abel_nf
  map_smul' c p := by
    rcases p with ⟨x, w⟩
    ext <;> simp [smul_sub]

@[simp]
theorem observerErrorEquiv_apply (p : X × X) :
    observerErrorEquiv X p = (p.1, p.1 - p.2) := rfl

@[simp]
theorem observerErrorEquiv_symm_apply (p : X × X) :
    (observerErrorEquiv X).symm p = (p.1, p.1 - p.2) := rfl

end ObserverErrorEquiv

section RealClosedLoopSpectrumAlgebra

variable {X U Y Z D : Type*}
variable [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]
variable [AddCommGroup U] [Module ℝ U]
variable [AddCommGroup Y] [Module ℝ Y]
variable [AddCommGroup Z] [Module ℝ Z]
variable [AddCommGroup D] [Module ℝ D]

omit [FiniteDimensional ℝ X] in
/-- **Sign convention.** The observer-error block of the controller (6.7) is the
output injection `A + G C`. It agrees with the contract's Luenberger error
`A - L.comp C` under the gain substitution `L = -G`. -/
theorem observerErrorBlock_eq (sys : LinearSystem ℝ X U Y) (G : Y →ₗ[ℝ] X) :
    sys.A + G.comp sys.C = sys.A - (-G).comp sys.C := by
  rw [LinearMap.neg_comp]
  abel

omit [FiniteDimensional ℝ X] in
/-- **Closed-loop similarity to the separation block operator.** For a strictly
proper plant (`D = 0`) the closed loop of the controller (6.7) is similar, via
the observer-error coordinate change `observerErrorEquiv`, to the block
upper-triangular operator

`[[A + B F, -B (F - N C)], [0, A + G C]]`.

The state-feedback block is `A + B F` and the observer-error block is `A + G C`;
the off-diagonal block feeds the observer error back into the plant but does not
enter the characteristic polynomial.

Source: Trentelman–Stoorvogel–Hautus, Section 6.3, the closed-loop matrix
preceding the internal-stability results. -/
theorem cabPairController_closedLoopMap_conj (sys : LinearSystem ℝ X U Y)
    (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (F : X →ₗ[ℝ] U) (G : Y →ₗ[ℝ] X) (N : Y →ₗ[ℝ] U)
    (hwp : (cabPairInterconnection sys (cabPairController sys F G N) E H).IsWellPosed) :
    (observerErrorEquiv X).conj
      ((cabPairInterconnection sys (cabPairController sys F G N) E H).closedLoopMap hwp) =
      LinearMap.blockOperator (sys.A + sys.B.comp F)
        (-(sys.B.comp (F - N.comp sys.C))) (sys.A + G.comp sys.C) := by
  let ic : DynamicInterconnection ℝ X U Y X D Z :=
    cabPairInterconnection sys (cabPairController sys F G N) E H
  change (observerErrorEquiv X).conj (ic.closedLoopMap hwp) = _
  apply LinearMap.ext
  intro p
  obtain ⟨x, e⟩ := p
  rw [LinearEquiv.conj_apply_apply]
  simp only [observerErrorEquiv_symm_apply, observerErrorEquiv_apply]
  rw [ic.closedLoopMap_of_D_eq_zero hD hwp (x, x - e)]
  apply Prod.ext
  · simp only [ic, cabPairInterconnection, cabPairController, LinearMap.blockOperator_apply,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
      LinearMap.neg_apply]
    abel
  · simp only [ic, cabPairInterconnection, cabPairController, LinearMap.blockOperator_apply,
      LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, map_sub,
      LinearMap.neg_apply]
    abel

/-- `IsHurwitz` depends only on the characteristic polynomial. -/
theorem isHurwitz_of_charpoly_eq {T S : X →ₗ[ℝ] X}
    (h : T.charpoly = S.charpoly) (hS : LinearMap.IsHurwitz S) : LinearMap.IsHurwitz T := by
  intro z hz
  apply hS z
  rwa [h] at hz

/-- **Closed-loop characteristic-polynomial factorization.** For a strictly
proper plant (`D = 0`) the characteristic polynomial of the extended closed-loop
map of the controller (6.7) factors as the product of the state-feedback and
observer-error characteristic polynomials:

`χ(Ae) = χ(A + B F) · χ(A + G C)`.

Consequently the complex spectrum of the closed loop is the union
`σ(A + B F) ∪ σ(A + G C)` of the two block spectra. -/
theorem charpoly_closedLoopMap_cabPairController (sys : LinearSystem ℝ X U Y)
    (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (F : X →ₗ[ℝ] U) (G : Y →ₗ[ℝ] X) (N : Y →ₗ[ℝ] U)
    (hwp : (cabPairInterconnection sys (cabPairController sys F G N) E H).IsWellPosed) :
    ((cabPairInterconnection sys (cabPairController sys F G N) E H).closedLoopMap
        hwp).charpoly =
      (sys.A + sys.B.comp F).charpoly * (sys.A + G.comp sys.C).charpoly := by
  let ic : DynamicInterconnection ℝ X U Y X D Z :=
    cabPairInterconnection sys (cabPairController sys F G N) E H
  have hconj := cabPairController_closedLoopMap_conj sys hD E H F G N hwp
  change (ic.closedLoopMap hwp).charpoly = _
  rw [← LinearEquiv.charpoly_conj (observerErrorEquiv X) (ic.closedLoopMap hwp), hconj,
    LinearMap.charpoly_blockOperator]

/-- **Hurwitz decomposition of the extended closed loop.** For a strictly proper
plant (`D = 0`), if the state-feedback block `A + B F` and the observer-error
block `A + G C` are both Hurwitz then so is the whole extended closed-loop map.
This is the spectral content of the separation principle for the dynamic
controller (6.7), read off the characteristic-polynomial factorization. -/
theorem isHurwitz_closedLoopMap_cabPairController (sys : LinearSystem ℝ X U Y)
    (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (F : X →ₗ[ℝ] U) (G : Y →ₗ[ℝ] X) (N : Y →ₗ[ℝ] U)
    (hwp : (cabPairInterconnection sys (cabPairController sys F G N) E H).IsWellPosed)
    (hF : LinearMap.IsHurwitz (sys.A + sys.B.comp F))
    (hG : LinearMap.IsHurwitz (sys.A + G.comp sys.C)) :
    LinearMap.IsHurwitz
      ((cabPairInterconnection sys (cabPairController sys F G N) E H).closedLoopMap hwp) := by
  let ic : DynamicInterconnection ℝ X U Y X D Z :=
    cabPairInterconnection sys (cabPairController sys F G N) E H
  have hchar : (ic.closedLoopMap hwp).charpoly =
      (LinearMap.blockOperator (sys.A + sys.B.comp F)
        (-(sys.B.comp (F - N.comp sys.C))) (sys.A + G.comp sys.C)).charpoly := by
    rw [charpoly_closedLoopMap_cabPairController sys hD E H F G N hwp,
      LinearMap.charpoly_blockOperator]
  exact isHurwitz_of_charpoly_eq hchar
    (LinearMap.isHurwitz_blockOperator _ _ _ hF hG)

end RealClosedLoopSpectrumAlgebra

section RealClosedLoopSpectrumAnalytic

open Filter

variable {X U Y Z D : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [AddCommGroup U] [Module ℝ U]
variable [AddCommGroup Y] [Module ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- **Exponential attractivity of the extended closed loop.** For a strictly
proper plant (`D = 0`), if the state-feedback and observer-error blocks are
Hurwitz then every closed-loop trajectory of the controller (6.7) tends to the
origin: the extended closed-loop flow is attractive at `0`. The decay is derived
from the spectral Hurwitz hypothesis through the accepted real Hurwitz decay
theorem `LinearMap.tendsto_exp_of_isHurwitz`; no decay is assumed. -/
theorem isAttractive_closedLoopSystem_cabPairController (sys : LinearSystem ℝ X U Y)
    (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (F : X →ₗ[ℝ] U) (G : Y →ₗ[ℝ] X) (N : Y →ₗ[ℝ] U)
    (hwp : (cabPairInterconnection sys (cabPairController sys F G N) E H).IsWellPosed)
    (hF : LinearMap.IsHurwitz (sys.A + sys.B.comp F))
    (hG : LinearMap.IsHurwitz (sys.A + G.comp sys.C)) :
    Filter.IsAttractive (l := nhds (0 : X × X))
      (Φ := fun (t : ℝ) (p : X × X) =>
        ((cabPairInterconnection sys (cabPairController sys F G N) E H).closedLoopSystem
          hwp).expFlow t p) (l' := atTop) := by
  have hH := isHurwitz_closedLoopMap_cabPairController sys hD E H F G N hwp hF hG
  refine Filter.Eventually.of_forall (fun p => ?_)
  let ic : DynamicInterconnection ℝ X U Y X D Z :=
    cabPairInterconnection sys (cabPairController sys F G N) E H
  have hgoal : (fun t : ℝ => (ic.closedLoopSystem hwp).expFlow t p) =
      fun t : ℝ => NormedSpace.exp (t • (ic.closedLoopMap hwp).toContinuousLinearMap) p := by
    funext t
    simp [LinearSystem.expFlow, LinearSystem.continuousA]
  rw [hgoal]
  convert LinearMap.tendsto_exp_of_isHurwitz (ic.closedLoopMap hwp) hH p using 1

/-- **Lyapunov stability of the extended closed loop.** Under the same
hypotheses, the extended closed-loop flow of the controller (6.7) is Lyapunov
stable at the origin in the sense of `Filter.IsStableOn`. The uniform bound is
supplied by the accepted theorem `LinearMap.isStableOn_expFlow_of_isHurwitz`. -/
theorem isStableOn_closedLoopSystem_cabPairController (sys : LinearSystem ℝ X U Y)
    (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (F : X →ₗ[ℝ] U) (G : Y →ₗ[ℝ] X) (N : Y →ₗ[ℝ] U)
    (hwp : (cabPairInterconnection sys (cabPairController sys F G N) E H).IsWellPosed)
    (hF : LinearMap.IsHurwitz (sys.A + sys.B.comp F))
    (hG : LinearMap.IsHurwitz (sys.A + G.comp sys.C)) :
    (nhds (0 : X × X)).IsStableOn
      (fun (t : ℝ) (p : X × X) =>
        ((cabPairInterconnection sys (cabPairController sys F G N) E H).closedLoopSystem
          hwp).expFlow t p) (Set.Ici 0) := by
  have hH := isHurwitz_closedLoopMap_cabPairController sys hD E H F G N hwp hF hG
  let ic : DynamicInterconnection ℝ X U Y X D Z :=
    cabPairInterconnection sys (cabPairController sys F G N) E H
  have hgoal : (fun (t : ℝ) (p : X × X) => (ic.closedLoopSystem hwp).expFlow t p) =
      fun (t : ℝ) (p : X × X) =>
        NormedSpace.exp (t • (ic.closedLoopMap hwp).toContinuousLinearMap) p := by
    funext t p
    simp [LinearSystem.expFlow, LinearSystem.continuousA]
  rw [hgoal]
  convert LinearMap.isStableOn_expFlow_of_isHurwitz (ic.closedLoopMap hwp) hH using 1

/-- **Internal asymptotic stability of the extended closed loop.** Combining
`isStableOn_closedLoopSystem_cabPairController` and
`isAttractive_closedLoopSystem_cabPairController`, the closed loop of the
controller (6.7) is asymptotically stable at the extended origin whenever the
state-feedback block `A + B F` and the observer-error block `A + G C` are
Hurwitz. -/
theorem isAsymptoticallyStable_closedLoopSystem_cabPairController
    (sys : LinearSystem ℝ X U Y)
    (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (F : X →ₗ[ℝ] U) (G : Y →ₗ[ℝ] X) (N : Y →ₗ[ℝ] U)
    (hwp : (cabPairInterconnection sys (cabPairController sys F G N) E H).IsWellPosed)
    (hF : LinearMap.IsHurwitz (sys.A + sys.B.comp F))
    (hG : LinearMap.IsHurwitz (sys.A + G.comp sys.C)) :
    (nhds (0 : X × X)).IsStableOn
        (fun (t : ℝ) (p : X × X) =>
          ((cabPairInterconnection sys (cabPairController sys F G N) E H).closedLoopSystem
            hwp).expFlow t p) (Set.Ici 0) ∧
      Filter.IsAttractive (l := nhds (0 : X × X))
        (Φ := fun (t : ℝ) (p : X × X) =>
          ((cabPairInterconnection sys (cabPairController sys F G N) E H).closedLoopSystem
            hwp).expFlow t p) (l' := atTop) :=
  ⟨isStableOn_closedLoopSystem_cabPairController sys hD E H F G N hwp hF hG,
    isAttractive_closedLoopSystem_cabPairController sys hD E H F G N hwp hF hG⟩

end RealClosedLoopSpectrumAnalytic

section RealClosedLoopSpectrumExistence

variable {X U Y : Type*}
variable [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]
variable [AddCommGroup U] [Module ℝ U]
variable [AddCommGroup Y] [Module ℝ Y] [FiniteDimensional ℝ Y]

/-- **Existence of stabilizing gains.** A controllable and observable plant
admits a state-feedback gain `F` and an output-injection gain `G` for which both
the state-feedback block `A + B F` and the observer-error block `A + G C` are
Hurwitz. The gains are produced by the accepted stabilization and detection
theorems, so the hypotheses of the Hurwitz decomposition and internal-stability
results are satisfiable and those results are not vacuous. -/
theorem exists_hurwitz_cabPair_gains (sys : LinearSystem ℝ X U Y)
    (hcont : LinearMap.IsControllable sys.A sys.B)
    (hobs : LinearMap.IsObservable sys.C sys.A) :
    ∃ F : X →ₗ[ℝ] U, ∃ G : Y →ₗ[ℝ] X,
      LinearMap.IsHurwitz (sys.A + sys.B.comp F) ∧
        LinearMap.IsHurwitz (sys.A + G.comp sys.C) := by
  obtain ⟨F, hF⟩ := LinearMap.isStabilizable_of_isControllable sys.A sys.B hcont
  obtain ⟨L, hL⟩ := LinearMap.isDetectable_of_isObservable sys.C sys.A hobs
  refine ⟨F, -L, hF, ?_⟩
  rw [show sys.A + (-L).comp sys.C = sys.A - L.comp sys.C by
    rw [LinearMap.neg_comp]; abel]
  exact hL

/-- **A controllable and observable strictly proper plant admits a dynamic
controller whose closed loop is Hurwitz.** This packages the gain existence with
the Hurwitz decomposition of the controller (6.7), showing that the internal
stability layer applies to a nonempty class of plants. The controller state
space is `X` and the constructed gain `N` is zero. -/
theorem exists_hurwitz_closedLoopMap_of_isControllable_isObservable
    {Z D : Type*} [AddCommGroup Z] [Module ℝ Z] [AddCommGroup D] [Module ℝ D]
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (hcont : LinearMap.IsControllable sys.A sys.B)
    (hobs : LinearMap.IsObservable sys.C sys.A) :
    ∃ F : X →ₗ[ℝ] U, ∃ G : Y →ₗ[ℝ] X, ∃ N : Y →ₗ[ℝ] U,
      LinearMap.IsHurwitz
        ((cabPairInterconnection sys (cabPairController sys F G N) E H).closedLoopMap
          ((cabPairInterconnection sys (cabPairController sys F G N) E H).isWellPosed_of_D_eq_zero
            hD)) := by
  obtain ⟨F, G, hF, hG⟩ := exists_hurwitz_cabPair_gains sys hcont hobs
  refine ⟨F, G, 0, ?_⟩
  exact isHurwitz_closedLoopMap_cabPairController sys hD E H F G 0 _ hF hG

end RealClosedLoopSpectrumExistence

end LinearSystem
