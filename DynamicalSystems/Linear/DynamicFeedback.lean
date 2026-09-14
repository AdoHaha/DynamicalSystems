/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.DisturbanceDecoupling
public import DynamicalSystems.Linear.Stabilization
public import DynamicalSystems.Linear.Trajectory
public import Mathlib.MeasureTheory.Integral.ExpDecay

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

## External stabilization of the forced channel

External stabilization (Sections 4.8 and 6.6) is the forced counterpart of the
above. The closed-loop impulse response of the disturbance channel (6.12) is the
forced response `H_e e^{A_e t} B_e` (`externalResponse`), where `B_e` is the
total channel `disturbanceMapWithF`. Because the project stability vocabulary
`Filter.IsStableOn` / `Filter.IsAttractive` is stated for an endomorphism, the
predicate `IsExternallyStable` packages the disturbance direction and the
controlled output into the flow `(d, z) ↦ (0, H_e e^{A_e t} B_e d)`
(`externalFlow`) and asks that this flow be stable and attractive at the origin.
It is derived from Hurwitzness of the extended closed loop
(`isExternallyStable_of_isHurwitz_closedLoopMap`), which is the state-space form
of Theorem 3.23 (internal stability implies external stability). The stronger
BIBO/integrability content of Theorem 3.21 is supplied separately by the
predicate `IsBIBOStable` and the bridge
`isBIBOStable_externalResponse_of_isHurwitz`.

## Scope

This file contains the algebraic foundations of Chapter 6 together with the
**dynamic decoupling synthesis** of Theorem 6.4 / Corollary 6.7 and the
**geometric extraction (necessity)** of Theorem 6.2 / Theorem 6.6, so the
following is now claimed and proved here:

* the **external-stabilization sufficient direction** (Sections 4.8 and 6.6): a
  Hurwitz extended closed loop is externally stable, and a
  controllable/observable plant admits a cabPair controller with accepted
  Hurwitz gains whose closed loop is externally stable
  (`isExternallyStable_closedLoopSystem_cabPairController`,
  `exists_externallyStabilizing_cabPair_gains`);

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
  bookkeeping are formalised here, and the observer-form synthesis
  (`isClosedLoopDisturbanceDecoupledWithF_of_observerGain`,
  `exists_dynamicController_withF_of_isCABPairBetween`) decouples the full
  `F`-channel whenever the state disturbance is a function of the measurement
  disturbance (`G F = -E`, equivalently `ker F ≤ ker E`). The source's
  Theorem 6.4 is the `F = 0` case, and unconditional nonzero-`F` decoupling is
  not claimed because that factorization is not automatic;
* the **external stabilization** sufficient direction of Sections 4.8 and 6.6:
the forced disturbance-to-controlled-output response of the controller (6.7) is
externally stable whenever the extended closed loop is Hurwitz
(`DynamicInterconnection.isExternallyStable_of_isHurwitz_closedLoopMap`,
`LinearSystem.isExternallyStable_closedLoopSystem_cabPairController`), and a
controllable/observable plant admits such externally stabilizing gains
(`LinearSystem.exists_externallyStabilizing_cabPair_gains`);
* the **external BIBO/integrability bridge** of Theorem 3.21: the closed-loop
impulse response is Bochner integrable on `[0, ∞)` and the forced
disturbance-to-controlled-output channel is bounded-input bounded-output
whenever the extended closed loop is Hurwitz
(`DynamicInterconnection.IsBIBOStable`,
`LinearSystem.externalResponse_integrable_of_isHurwitz`,
`LinearSystem.isBIBOStable_externalResponse_of_isHurwitz`), with the convolution
kernel identified in the accepted disturbance-convolution API.

The **geometric external zero-response criterion** is proved as
`LinearSystem.externalStability_iff_geometricCertificate`: a strictly proper
plant admits a dynamic measurement-feedback controller whose *exact* external
impulse response `H_e e^{A_e t} B_e` vanishes identically if and only if there
is a `(C, A, B)`-pair between `im E` and `ker H`. The extraction direction is
`LinearSystem.exists_isCABPairBetween_of_externalStability`, and the analytic
bridge between the identically vanishing forced response and the Markov-parameter
predicate is
`DynamicInterconnection.hasExternalZeroResponse_iff_isClosedLoopDisturbanceDecoupledWithF`.
The *geometric subspace conditions* of the full external-stabilization
Corollary 6.22 (`im E ⊂ V*(ker H) + Xstab` and `S*(im E) ∩ Xdet ⊂ ker H`) are
recorded by `LinearSystem.ExternalStabilizationConditions` and are now extracted
from the certificate and from the exact external zero response
(`LinearSystem.externalStabilizationConditions_of_isCABPairBetween`,
`LinearSystem.externalStabilizationConditions_of_externalStability`); the
integrated form is
`LinearSystem.externalStability_iff_geometricCertificate_and_conditions`. The
remaining analytic direction — a merely stable *nonzero* transfer function —
still requires the trajectory characterisation
`W_g(ker H) = V*(ker H) + Xstab` (Trentelman Theorem 4.37) and the
quotient-spectrum transfer lemma (Lemma 4.35), which are not available in the
pinned library. In particular the
zero-response predicate above must not be read as BIBO/external asymptotic
stability; the two are separated by
`LinearSystem.bibo_and_externalZeroResponse_of_geometricCertificate_hurwitz`,
which obtains BIBO *and* zero response only after adjoining Hurwitz feedback and
injection gains to the geometric certificate. The transfer-function form of
decoupling and nonlinear (Conte–Moog–Perdon) dynamic feedback stay in the
documented future roadmap.

## Main definitions

* `LinearSystem.DynamicController`: the controller `(K, L, M, N)`.
* `LinearSystem.DynamicInterconnection`: plant, controller and the disturbance
  and output channels.
* `DynamicInterconnection.loopMap`, `DynamicInterconnection.IsWellPosed`,
  `DynamicInterconnection.loopInv`
* `DynamicInterconnection.solvedMeasurement`, `DynamicInterconnection.solvedInput`
* `DynamicInterconnection.loopInv_of_D_eq_zero`,
  `DynamicInterconnection.disturbanceMeasurement_of_D_eq_zero`
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
* `LinearSystem.cabPairController`, `LinearSystem.cabPairInterconnection`,
  `LinearSystem.measurementInterconnection`
* `LinearSystem.observerErrorEquiv`: the observer-error coordinate change
* `DynamicInterconnection.externalResponse`: the forced disturbance-to-output
  impulse response `H_e e^{A_e t} B_e`
* `DynamicInterconnection.externalFlow`, `DynamicInterconnection.IsExternallyStable`:
  the forced-response flow and its external asymptotic stability predicate
* `DynamicInterconnection.externalResponseOperator`: the forced impulse response
  `H_e e^{A_e t} B_e` bundled as a continuous linear operator `D →L[ℝ] Z`
* `DynamicInterconnection.IsBIBOStable`: Bochner integrability on `[0, ∞)` plus
  the bounded-input bounded-output property of the forced channel
* `DynamicInterconnection.HasExternalZeroResponse`: identical vanishing of the
  forced closed-loop external response `H_e e^{A_e t} B_e`
* `LinearSystem.GeometricCertificate`: existence of a `(C, A, B)`-pair between
  `im E` and `ker H`
* `LinearSystem.ExternalStability`: existence of a strictly proper dynamic
  measurement-feedback controller with identically zero external response

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
* `LinearSystem.isClosedLoopDisturbanceDecoupledWithF_of_observerGain`
* `LinearSystem.exists_dynamicController_withF_of_isCABPairBetween`
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
* `DynamicInterconnection.isExternallyStable_of_isHurwitz_closedLoopMap`
* `LinearSystem.isExternallyStable_closedLoopSystem_cabPairController`
* `LinearSystem.exists_externallyStabilizing_cabPair_gains`
* `DynamicInterconnection.externalResponse_eq_disturbanceImpulseResponse`
* `DynamicInterconnection.disturbanceContribution_eq_convolution_externalResponse`
* `DynamicInterconnection.externalResponse_integrable`
* `DynamicInterconnection.isBIBOStable_of_isHurwitz`
* `LinearSystem.externalResponse_integrable_of_isHurwitz`
* `LinearSystem.isBIBOStable_externalResponse_of_isHurwitz`
* `LinearSystem.isBIBOStable_externalResponse_cabPairController`
* `LinearSystem.exists_biboStable_cabPair_gains`
* `DynamicInterconnection.hasExternalZeroResponse_iff_isClosedLoopDisturbanceDecoupledWithF`
* `LinearSystem.exists_isCABPairBetween_of_externalStability`
* `LinearSystem.externalStabilizationConditions_of_isCABPairBetween`
* `LinearSystem.externalStabilizationConditions_of_externalStability`
* `LinearSystem.externalStability_iff_geometricCertificate`
* `LinearSystem.externalStability_iff_geometricCertificate_and_conditions`
* `LinearSystem.bibo_and_externalZeroResponse_of_geometricCertificate_hurwitz`

## References

* H. L. Trentelman, A. A. Stoorvogel, M. Hautus, *Control Theory for Linear
  Systems*, Springer, 2001, Section 3.13, Sections 4.8 and 6.6 (external
  stabilization), and Chapter 6, in particular equations (6.2)–(6.4), (6.12),
  Definitions 4.36, 6.1 and 6.19, Theorems 3.23, 3.21 and exercise 6.3.
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

The full channel-decoupling synthesis theorem for nonzero `F` is proved in the
synthesis section below (`isClosedLoopDisturbanceDecoupledWithF_of_observerGain`)
under the observer factorization hypothesis; here only the signal, reduction and
bookkeeping identities are established. -/

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

/-- For a strictly proper plant the loop inverse is the identity. -/
theorem loopInv_of_D_eq_zero (hD : ic.plant.D = 0) (h : ic.IsWellPosed) :
    ic.loopInv h = 1 := by
  have h1 := ic.loopMap_loopInv h
  rw [ic.loopMap_eq_one_of_D_eq_zero hD] at h1
  change (1 : Y →ₗ[𝕜] Y) * ic.loopInv h = (1 : Y →ₗ[𝕜] Y) at h1
  rw [one_mul] at h1
  exact h1

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

/-- For a strictly proper plant the measurement-disturbance contribution to the
measurement is the raw channel `F d`, since the loop inverse is the identity. -/
theorem disturbanceMeasurement_of_D_eq_zero (hD : ic.plant.D = 0) (h : ic.IsWellPosed) :
    ic.disturbanceMeasurement h = ic.F := by
  ext d
  apply h.1
  change ic.loopMap (ic.loopInv h (ic.F d)) = ic.loopMap (ic.F d)
  rw [← LinearMap.comp_apply, ic.loopMap_loopInv h, ic.loopMap_eq_one_of_D_eq_zero hD]

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
channel. The synthesis section below proves the nonzero-`F` decoupling theorem
`isClosedLoopDisturbanceDecoupledWithF_of_observerGain` and its existence form
`exists_dynamicController_withF_of_isCABPairBetween`, under a factorization
hypothesis on the disturbance channel. -/

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

open Filter

/-! ### The forced disturbance-to-output channel and external stability

External stabilization (Trentelman–Stoorvogel–Hautus, Sections 4.8 and 6.6)
concerns the *forced* disturbance-to-controlled-output response of the closed
loop rather than the unforced extended state. The closed-loop impulse response
of the channel (6.12) is `H_e e^{A_e t} B_e`, where `B_e` is the total
disturbance map `disturbanceMapWithF`; its decay is the state-space counterpart
of stability of the closed-loop transfer function `G(s) = H_e (s I - A_e)⁻¹ B_e`.

The predicate `IsExternallyStable` records that this impulse response is both
Lyapunov stable (`Filter.IsStableOn`) and attractive (`Filter.IsAttractive`) at
the origin, and `isExternallyStable_of_isHurwitz_closedLoopMap` derives it from
the Hurwitz property of the extended closed-loop map. This is the formal content
of Theorem 3.23 (internal stability implies external stability) for the dynamic
closed loop. The stronger Bochner-integrability and bounded-input bounded-output
statement of Theorem 3.21 is supplied below by the predicate `IsBIBOStable` and
the bridge `isBIBOStable_of_isHurwitz`, using the accepted exponential
operator-norm bound `LinearMap.exists_exponential_norm_bound_of_isHurwitz`. -/

/-- The **forced disturbance-to-output response** of the closed loop: the
controlled output of the autonomous extended flow started from the disturbance
image `disturbanceMapWithF h d`. This is the state-space impulse response
`H_e e^{A_e t} B_e` of the closed loop (6.12) evaluated at the disturbance
direction `d`, with the measurement channel included through
`disturbanceMapWithF`. -/
noncomputable def externalResponse (h : ic.IsWellPosed) (t : ℝ) (d : D) : Z :=
  ic.outputMap ((ic.closedLoopSystem h).expFlow t (ic.disturbanceMapWithF h d))

omit [FiniteDimensional ℝ D] in
@[simp]
theorem externalResponse_apply (h : ic.IsWellPosed) (t : ℝ) (d : D) :
    ic.externalResponse h t d =
      ic.outputMap ((ic.closedLoopSystem h).expFlow t (ic.disturbanceMapWithF h d)) := rfl

/-- The **external flow** of the forced disturbance-to-output channel. The
project stability vocabulary (`Filter.IsStableOn`, `Filter.IsAttractive`) is
stated for an endomorphism `ι → E → E`, whereas the forced response is a map
`D → Z`. We therefore package the disturbance direction and the controlled
output in the product `D × Z` and set
`(d, z) ↦ (0, H_e e^{A_e t} B_e d)`: the first coordinate records that the
channel is driven from the disturbance image, the second is the impulse response
of the closed-loop output. -/
noncomputable def externalFlow (h : ic.IsWellPosed) (t : ℝ) (q : D × Z) : D × Z :=
  (0, ic.externalResponse h t q.1)

omit [FiniteDimensional ℝ D] in
@[simp]
theorem externalFlow_apply (h : ic.IsWellPosed) (t : ℝ) (q : D × Z) :
    ic.externalFlow h t q = (0, ic.externalResponse h t q.1) := rfl

/-- **External asymptotic stability of the forced disturbance-to-output
channel.** The state-space impulse response `H_e e^{A_e t} B_e` of the closed
loop with the total disturbance channel `disturbanceMapWithF h` is Lyapunov
stable at the origin (`Filter.IsStableOn`) and attractive at `+∞`
(`Filter.IsAttractive`) in the project stability vocabulary, applied to the
external flow `(d, z) ↦ (0, H_e e^{A_e t} B_e d)` of `externalFlow`.

This is the forced-response analogue of the internal asymptotic-stability
predicate: it concerns only the response generated by the disturbance channel,
so it is genuinely external. It is the formal counterpart of stability of the
closed-loop transfer function `G(s) = H_e (s I - A_e)⁻¹ B_e` required by
external stabilization.

The source definition is Trentelman–Stoorvogel–Hautus, Definition 6.19 (PDF
page 156 / printed page 142): *“The problem of external stabilization by
measurement feedback, ESPM, is to find a controller Κ such that the closed loop
transfer function G_Κ(s) is stable.”* The state-space channel is
`G_Κ(s) = H_e (s I - A_e)⁻¹ B_e` of equation (6.12). The predicate below records
the Lyapunov stability and attractivity of the impulse response, which is the
analytic decay content implied by `A_e` Hurwitz when the initial extended state
is the disturbance image `B_e d` (zero plant/controller state together with an
impulsive disturbance).

The stronger Bochner-integrability and bounded-input bounded-output statement of
Theorem 3.21 is recorded by the separate predicate `IsBIBOStable`. The
*geometric* necessary-and-sufficient conditions of Corollary 6.22 (PDF pages
159–160 / printed pages 145–146) are **not** asserted. -/
noncomputable def IsExternallyStable (h : ic.IsWellPosed) : Prop :=
  (nhds (0 : D × Z)).IsStableOn (fun t q => ic.externalFlow h t q) (Set.Ici 0) ∧
    Filter.IsAttractive (l := nhds (0 : D × Z))
      (Φ := fun t q => ic.externalFlow h t q) (l' := atTop)

omit [FiniteDimensional ℝ D] in
/-- The closed-loop flow is the operator exponential of the closed-loop map. -/
theorem closedLoopSystem_expFlow_eq (h : ic.IsWellPosed) (t : ℝ) :
    (ic.closedLoopSystem h).expFlow t =
      NormedSpace.exp (t • (ic.closedLoopMap h).toContinuousLinearMap) := by
  simp [LinearSystem.expFlow, LinearSystem.continuousA]

/-- **Internal Hurwitz stability implies external stability of the forced
channel.** If the extended closed-loop map is Hurwitz then the forced
disturbance-to-output response is both Lyapunov stable and attractive at the
origin, i.e. the closed loop is externally stable. The decay of the impulse
response is derived from the accepted real Hurwitz theorem
`LinearMap.tendsto_exp_of_isHurwitz`; no stability of the forced response is
assumed.

This is the external-stabilization bridge of Trentelman–Stoorvogel–Hautus,
Theorem 3.23 (internal stability implies external stability) applied to the
closed loop (6.12). -/
theorem isExternallyStable_of_isHurwitz_closedLoopMap (h : ic.IsWellPosed)
    (hH : LinearMap.IsHurwitz (ic.closedLoopMap h)) :
    ic.IsExternallyStable h := by
  have hexp : ∀ t : ℝ, (ic.closedLoopSystem h).expFlow t =
      NormedSpace.exp (t • (ic.closedLoopMap h).toContinuousLinearMap) :=
    ic.closedLoopSystem_expFlow_eq h
  have hstable := LinearMap.isStableOn_expFlow_of_isHurwitz (ic.closedLoopMap h) hH
  constructor
  · intro s hs
    obtain ⟨sD, hsD, sZ, hsZ, hsDZ⟩ :=
      mem_nhds_prod_iff.mp (show s ∈ nhds ((0 : D), (0 : Z)) from hs)
    have hsOut : (ic.outputMap.toContinuousLinearMap) ⁻¹' sZ ∈ nhds (0 : X × W) :=
      ic.outputMap.toContinuousLinearMap.continuous.continuousAt.preimage_mem_nhds
        (by rw [map_zero]; exact hsZ)
    obtain ⟨u, hu, hflow⟩ := hstable _ hsOut
    have hDmem : (ic.disturbanceMapWithF h).toContinuousLinearMap ⁻¹' u ∈ nhds (0 : D) :=
      (ic.disturbanceMapWithF h).toContinuousLinearMap.continuous.continuousAt.preimage_mem_nhds
        (by rw [map_zero]; exact hu)
    refine ⟨((ic.disturbanceMapWithF h).toContinuousLinearMap ⁻¹' u) ×ˢ (Set.univ : Set Z),
      ?_, ?_⟩
    · rw [nhds_prod_eq]
      exact Filter.prod_mem_prod hDmem Filter.univ_mem
    · intro t ht q hq
      obtain ⟨d, z⟩ := q
      have hdu : (ic.disturbanceMapWithF h) d ∈ u := hq.1
      have hmem := hflow t ht ((ic.disturbanceMapWithF h) d) hdu
      have hpair : ((0 : D), ic.outputMap ((ic.closedLoopSystem h).expFlow t
          ((ic.disturbanceMapWithF h) d))) ∈ sD ×ˢ sZ :=
        ⟨mem_of_mem_nhds hsD, by simpa [hexp t] using hmem⟩
      simpa [externalFlow, externalResponse] using hsDZ hpair
  · refine Filter.Eventually.of_forall (fun q => ?_)
    obtain ⟨d, z⟩ := q
    have hd : Tendsto (fun t : ℝ =>
        NormedSpace.exp (t • (ic.closedLoopMap h).toContinuousLinearMap)
          (ic.disturbanceMapWithF h d)) atTop (nhds 0) :=
      LinearMap.tendsto_exp_of_isHurwitz (ic.closedLoopMap h) hH _
    have hd' : Tendsto (fun t : ℝ => (ic.closedLoopSystem h).expFlow t
        (ic.disturbanceMapWithF h d)) atTop (nhds 0) :=
      by simpa [hexp] using hd
    have hz : Tendsto (fun t : ℝ => ic.outputMap ((ic.closedLoopSystem h).expFlow t
        (ic.disturbanceMapWithF h d))) atTop (nhds 0) := by
      have hcomp := (ic.outputMap.toContinuousLinearMap.continuous.tendsto 0).comp hd'
      rw [map_zero] at hcomp
      exact hcomp
    have hpair := (tendsto_const_nhds (x := (0 : D))).prodMk_nhds hz
    have hgoal : (fun t : ℝ => ic.externalFlow h t (d, z)) =
        fun t : ℝ => ((0 : D), ic.outputMap ((ic.closedLoopSystem h).expFlow t
          (ic.disturbanceMapWithF h d))) := by
      funext t
      rfl
    rw [hgoal]
    exact hpair

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

/-- The dynamic measurement-feedback interconnection with an **explicit**
measurement-disturbance channel `F : D →ₗ[𝕜] Y`. It generalises
`cabPairInterconnection`, which is the special case `F = 0`, and is the
interconnection on which the nonzero-`F` synthesis is carried out. -/
def measurementInterconnection (sys : LinearSystem 𝕜 X U Y)
    (ctrl : DynamicController 𝕜 X Y U) (E : D →ₗ[𝕜] X) (F : D →ₗ[𝕜] Y)
    (H : X →ₗ[𝕜] Z) : DynamicInterconnection 𝕜 X U Y X D Z :=
  ⟨sys, ctrl, E, F, H⟩

@[simp]
theorem measurementInterconnection_F (sys : LinearSystem 𝕜 X U Y)
    (ctrl : DynamicController 𝕜 X Y U) (E : D →ₗ[𝕜] X) (F : D →ₗ[𝕜] Y)
    (H : X →ₗ[𝕜] Z) :
    (measurementInterconnection sys ctrl E F H).F = F := rfl

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
closed loop is disturbance decoupled for the extended channel as well. The
nonzero-`F` generalization is the observer-form theorem
`isClosedLoopDisturbanceDecoupledWithF_of_observerGain` below. -/
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

/-- **Nonzero-`F` decoupling synthesis (observer form).** Let `V` be a subspace
with `(A + B F_v) V ≤ V`, `im E ≤ V` and `V ≤ ker H`, and suppose the state
disturbance is a function of the measurement disturbance: there is an output map
`G` with `G F = -E`, i.e. `E d = -G (F d)` for every disturbance value `d`.
Then the observer-based controller
`w' = (A + B F_v + G C) w - G y`, `u = F_v w` (the `cabPairController` with
zero measurement feedthrough) has a closed loop that is decoupled for the full
measurement-disturbance channel `disturbanceMapWithF`.

Indeed, the observer error `e = w - x` then satisfies the disturbance-free
equation `e' = (A + G C) e`, so the diagonal subspace `{(x, x) | x ∈ V}` is
`closedLoopMap`-invariant, contains the image of `disturbanceMapWithF` and lies
in `ker outputMap`. The factorization `G F = -E` is the extra hypothesis that is
missing when `F ≠ 0`; it is equivalent to `ker F ≤ ker E`. -/
theorem isClosedLoopDisturbanceDecoupledWithF_of_observerGain
    (sys : LinearSystem 𝕜 X U Y) (hD : sys.D = 0)
    (E : D →ₗ[𝕜] X) (F : D →ₗ[𝕜] Y) (H : X →ₗ[𝕜] Z) (V : Submodule 𝕜 X)
    (Fv : X →ₗ[𝕜] U) (G : Y →ₗ[𝕜] X)
    (hV : Submodule.map (sys.A + sys.B.comp Fv) V ≤ V)
    (hE : LinearMap.range E ≤ V) (hH : V ≤ LinearMap.ker H)
    (hGF : G.comp F = -E)
    (hwp : (measurementInterconnection sys (cabPairController sys Fv G 0) E F
      H).IsWellPosed) :
    (measurementInterconnection sys (cabPairController sys Fv G 0) E F
      H).IsClosedLoopDisturbanceDecoupledWithF hwp := by
  let ic : DynamicInterconnection 𝕜 X U Y X D Z :=
    measurementInterconnection sys (cabPairController sys Fv G 0) E F H
  have hBe : ∀ d : D, ic.disturbanceMapWithF hwp d = (E d, E d) := by
    intro d
    have hdm : ic.disturbanceMeasurement hwp d = F d := by
      rw [ic.disturbanceMeasurement_apply, ic.loopInv_of_D_eq_zero hD hwp]
      simp [ic, measurementInterconnection]
    have hdi : ic.disturbanceInput hwp d = 0 := by
      rw [ic.disturbanceInput_apply, hdm]
      simp [ic, measurementInterconnection, cabPairController]
    have hGFd := LinearMap.congr_fun hGF d
    simp only [LinearMap.comp_apply, LinearMap.neg_apply] at hGFd
    rw [ic.disturbanceMapWithF_apply, hdi, hdm]
    simp only [map_zero, add_zero]
    apply Prod.ext
    · rfl
    · change (cabPairController sys Fv G 0).L (F d) = E d
      simp only [cabPairController, LinearMap.sub_apply, LinearMap.comp_apply,
        LinearMap.zero_apply]
      rw [hGFd]
      simp
  have hAe : ∀ x : X, ic.closedLoopMap hwp (x, x) =
      ((sys.A + sys.B.comp Fv) x, (sys.A + sys.B.comp Fv) x) := by
    intro x
    rw [ic.closedLoopMap_of_D_eq_zero hD hwp (x, x)]
    apply Prod.ext <;>
      simp only [ic, measurementInterconnection, cabPairController, LinearMap.add_apply,
        LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.sub_apply,
        map_zero] <;> abel
  refine (LinearMap.isDisturbanceDecoupled_iff_exists_invariant
    (ic.closedLoopMap hwp) (ic.disturbanceMapWithF hwp) ic.outputMap).mpr ?_
  let diag : V →ₗ[𝕜] X × X := V.subtype.prod V.subtype
  refine ⟨LinearMap.range diag, ?_, ?_, ?_⟩
  · rintro _ ⟨d, rfl⟩
    rw [hBe d]
    exact ⟨⟨E d, hE ⟨d, rfl⟩⟩, rfl⟩
  · rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, ic.outputMap_apply]
    exact LinearMap.mem_ker.mp (hH v.2)
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨v, rfl⟩ := hq
    change ic.closedLoopMap hwp ((v : X), (v : X)) ∈ LinearMap.range diag
    rw [hAe (v : X)]
    exact ⟨⟨(sys.A + sys.B.comp Fv) (v : X), hV ⟨(v : X), v.2, rfl⟩⟩, rfl⟩

/-- **Nonzero-`F` dynamic decoupling synthesis.** For a strictly proper plant
(`D = 0`), a `(C, A, B)`-pair between `im E` and `ker H` together with the
factorization `G F = -E` of the state disturbance through the measurement
disturbance yields a finite-dimensional dynamic measurement-feedback controller
which is well posed and whose closed loop is decoupled for the **full**
measurement-disturbance channel `disturbanceMapWithF`.

The controller is the observer form `w' = (A + B F_v + G C) w - G y`, `u = F_v w`
of `isClosedLoopDisturbanceDecoupledWithF_of_observerGain`, with `F_v` supplied
by the controlled invariance of `V`. The hypothesis `G F = -E` is the extra
requirement for this observer-form synthesis: the measurement disturbance must
determine the state disturbance, so that the observer error can be made
disturbance-free. It is satisfied in particular when `F` is injective, and it
reduces to `E = 0` when `F = 0`. The accepted zero-channel theorem
`exists_dynamicController_of_isCABPairBetween` is the `F = 0` case; no
unconditional nonzero-`F` statement is made. -/
theorem exists_dynamicController_withF_of_isCABPairBetween
    (sys : LinearSystem 𝕜 X U Y) (hD : sys.D = 0)
    (E : D →ₗ[𝕜] X) (F : D →ₗ[𝕜] Y) (H : X →ₗ[𝕜] Z) (S V : Submodule 𝕜 X)
    (hpair : LinearMap.IsCABPairBetween sys.C sys.A sys.B E H S V)
    (hfac : ∃ G : Y →ₗ[𝕜] X, G.comp F = -E) :
    ∃ ctrl : DynamicController 𝕜 X Y U,
      (measurementInterconnection sys ctrl E F H).IsClosedLoopDisturbanceDecoupledWithF
        ((measurementInterconnection sys ctrl E F H).isWellPosed_of_D_eq_zero hD) := by
  obtain ⟨⟨hSV, -, hV⟩, hE, hH⟩ := hpair
  obtain ⟨Fv, hFv⟩ := LinearMap.exists_stateFeedback_of_isControlledInvariant hV
  obtain ⟨G, hGF⟩ := hfac
  refine ⟨cabPairController sys Fv G 0, ?_⟩
  exact isClosedLoopDisturbanceDecoupledWithF_of_observerGain sys hD E F H V Fv G
    hFv (hE.trans hSV) hH hGF _

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

section RealClosedLoopExternalStability

open Filter

variable {X U Y Z D : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [AddCommGroup U] [Module ℝ U]
variable [AddCommGroup Y] [Module ℝ Y] [FiniteDimensional ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

omit [FiniteDimensional ℝ Y] in
/-- **External stability of the closed loop of the controller (6.7).** For a
strictly proper plant (`D = 0`), if the state-feedback block `A + B F` and the
observer-error block `A + G C` are Hurwitz, then the forced
disturbance-to-controlled-output response of the cabPair controller (6.7) is
externally stable: its impulse response `H e^{A_e t} B_e` is Lyapunov stable
and attractive at the origin. The extended closed loop is Hurwitz by
`isHurwitz_closedLoopMap_cabPairController`, and external stability is derived
from it through `isExternallyStable_of_isHurwitz_closedLoopMap`; decay is never
assumed.

Source: Trentelman–Stoorvogel–Hautus, Section 6.6 and Definitions 4.36/6.19;
the sufficiency direction here is the state-space form of Theorem 3.23
(internal stability implies external stability).

The hypotheses are exactly the strictly proper plant (`hD : sys.D = 0`), the
well-posed interconnection (`hwp`, automatic for `D = 0` but kept explicit) and
the Hurwitz gains (`hF`, `hG`); no decay or stability is assumed. Because the
predicate is impulse-response attractivity, no admissible locally-integrable
disturbance or zero-initial-state hypothesis is needed here. The general forced
(convolution) response to locally integrable disturbances, and its BIBO
consequence, are the missing bridge documented at `IsExternallyStable`. -/
theorem isExternallyStable_closedLoopSystem_cabPairController
    (sys : LinearSystem ℝ X U Y)
    (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (F : X →ₗ[ℝ] U) (G : Y →ₗ[ℝ] X) (N : Y →ₗ[ℝ] U)
    (hwp : (cabPairInterconnection sys (cabPairController sys F G N) E H).IsWellPosed)
    (hF : LinearMap.IsHurwitz (sys.A + sys.B.comp F))
    (hG : LinearMap.IsHurwitz (sys.A + G.comp sys.C)) :
    (cabPairInterconnection sys (cabPairController sys F G N) E H).IsExternallyStable hwp :=
  DynamicInterconnection.isExternallyStable_of_isHurwitz_closedLoopMap
    (cabPairInterconnection sys (cabPairController sys F G N) E H) hwp
    (isHurwitz_closedLoopMap_cabPairController sys hD E H F G N hwp hF hG)

/-- **Existence of externally stabilizing dynamic measurement feedback.** A
controllable and observable strictly proper plant admits a cabPair controller
whose closed loop is externally stable: the forced disturbance-to-output
response of (6.12) is Lyapunov stable and attractive at the origin. The gains
`F`, `G` are the accepted Hurwitz gains of `exists_hurwitz_cabPair_gains` and
`N = 0`; external stability is derived from the Hurwitz closed loop, not assumed.

This is the dynamic measurement-feedback counterpart of the sufficient
direction of external stabilization (Trentelman–Stoorvogel–Hautus, Section 6.6);
the geometric necessary-and-sufficient conditions of Corollary 6.22 remain
future work. The only hypotheses are controllability and observability of the
strictly proper plant; the gains exist without being assumed and external
stability is derived from their Hurwitz closed loop. -/
theorem exists_externallyStabilizing_cabPair_gains (sys : LinearSystem ℝ X U Y)
    (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (hcont : LinearMap.IsControllable sys.A sys.B)
    (hobs : LinearMap.IsObservable sys.C sys.A) :
    ∃ F : X →ₗ[ℝ] U, ∃ G : Y →ₗ[ℝ] X, ∃ N : Y →ₗ[ℝ] U,
      (cabPairInterconnection sys (cabPairController sys F G N) E H).IsExternallyStable
        ((cabPairInterconnection sys (cabPairController sys F G N) E H).isWellPosed_of_D_eq_zero
          hD) := by
  obtain ⟨F, G, hF, hG⟩ := exists_hurwitz_cabPair_gains sys hcont hobs
  refine ⟨F, G, 0, ?_⟩
  exact isExternallyStable_closedLoopSystem_cabPairController sys hD E H F G 0 _ hF hG

end RealClosedLoopExternalStability

/-! ## Bochner integrability and BIBO stability of the external response

The external-stabilization predicate `IsExternallyStable` records only Lyapunov
stability and attractivity of the closed-loop impulse response
`t ↦ H_e e^{A_e t} B_e`. The stronger content of Theorem 3.21 is that this
impulse response is *Bochner integrable* on `[0, ∞)` and that the forced
disturbance response is *bounded-input bounded-output* (BIBO): a bounded,
admissible (locally integrable) disturbance produces a bounded controlled
output, with a bound proportional to the input bound.

Both facts follow from the accepted quantitative operator-norm bound
`LinearMap.exists_exponential_norm_bound_of_isHurwitz`: a Hurwitz closed-loop map
`A_e = closedLoopMap h` satisfies `‖e^{t A_e}‖ ≤ C e^{-γ t}` with `C, γ > 0`, so
the impulse-response operator

`externalResponseOperator h t = H_e ∘ e^{t A_e} ∘ B_e : D →L[ℝ] Z`

is exponentially bounded and integrable on `[0, ∞)`. The BIBO estimate then
bounds the Bochner convolution integral

`y(t) = ∫_0^t H_e e^{(t - s) A_e} B_e (d(s)) ds`

of a bounded locally integrable disturbance by the total mass of the impulse
response. The impulse response is identified with the kernel of the accepted
disturbance-convolution API through
`externalResponse_eq_disturbanceImpulseResponse` and
`disturbanceContribution_eq_convolution_externalResponse` (zero initial state,
locally integrable disturbance explicit).

The predicate `IsBIBOStable` records precisely the Bochner integrability of the
impulse response and the BIBO bound, keeping the zero initial state and the
admissible locally integrable disturbances explicit. The geometric
necessary-and-sufficient conditions of Corollary 6.22 are *not* claimed here.

Source: Trentelman–Stoorvogel–Hautus, Theorem 3.21 and Section 6.6 (PDF pages
156, 159, 164). -/

open MeasureTheory Filter Set
open scoped Interval

namespace DynamicInterconnection

section BIBO

variable {X U Y W D Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [AddCommGroup U] [Module ℝ U] [AddCommGroup Y] [Module ℝ Y]
variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ W] [FiniteDimensional ℝ D]
variable (ic : DynamicInterconnection ℝ X U Y W D Z)

/-- The external impulse response `H_e e^{A_e t} B_e` bundled as a continuous
linear operator `D →L[ℝ] Z`. The continuity is automatic because `D` and the
closed-loop state space `X × W` are finite-dimensional. This is the operator
whose norm the accepted Hurwitz exponential bound controls. -/
noncomputable def externalResponseOperator (h : ic.IsWellPosed) (t : ℝ) : D →L[ℝ] Z :=
  (ic.outputMap.toContinuousLinearMap).comp
    (((ic.closedLoopSystem h).expFlow t).comp
      (ic.disturbanceMapWithF h).toContinuousLinearMap)

/-- Evaluation of the bundled external impulse response is the forced response
`externalResponse`. -/
@[simp]
theorem externalResponseOperator_apply (h : ic.IsWellPosed) (t : ℝ) (d : D) :
    ic.externalResponseOperator h t d = ic.externalResponse h t d := rfl

omit [FiniteDimensional ℝ D] in
/-- The forced disturbance-to-output response is continuous in time at each
disturbance direction. -/
theorem continuous_externalResponse (h : ic.IsWellPosed) (d : D) :
    Continuous (fun t : ℝ => ic.externalResponse h t d) := by
  have hflow : Continuous (fun t : ℝ => (ic.closedLoopSystem h).expFlow t) := by
    simpa using continuous_expFlow_sub (ic.closedLoopSystem h) 0
  have hv : Continuous (fun t : ℝ =>
      (ic.closedLoopSystem h).expFlow t (ic.disturbanceMapWithF h d)) :=
    hflow.clm_apply continuous_const
  change Continuous (fun t : ℝ => ic.outputMap
    ((ic.closedLoopSystem h).expFlow t (ic.disturbanceMapWithF h d)))
  exact ic.outputMap.toContinuousLinearMap.continuous.comp hv

/-- The bundled external impulse response is continuous in time. -/
theorem continuous_externalResponseOperator (h : ic.IsWellPosed) :
    Continuous (fun t : ℝ => ic.externalResponseOperator h t) := by
  have hflow : Continuous (fun t : ℝ => (ic.closedLoopSystem h).expFlow t) := by
    simpa using continuous_expFlow_sub (ic.closedLoopSystem h) 0
  have h2 : Continuous (fun t : ℝ =>
      ((ic.closedLoopSystem h).expFlow t).comp
        (ic.disturbanceMapWithF h).toContinuousLinearMap) :=
    hflow.clm_comp continuous_const
  have h3 : Continuous (fun t : ℝ =>
      (ic.outputMap.toContinuousLinearMap).comp
        (((ic.closedLoopSystem h).expFlow t).comp
          (ic.disturbanceMapWithF h).toContinuousLinearMap)) :=
    continuous_const.clm_comp h2
  simpa only [externalResponseOperator] using h3

/-- **Exponential operator-norm bound for the external impulse response.** For
a Hurwitz extended closed loop there are `A ≥ 0` and `γ > 0` with
`‖externalResponseOperator h t‖ ≤ A e^{-γ t}` for every `t ≥ 0`. This pushes the
accepted bound `LinearMap.exists_exponential_norm_bound_of_isHurwitz` through
the bounded factors `H_e` and `B_e`. -/
theorem norm_externalResponseOperator_le (h : ic.IsWellPosed)
    (hH : LinearMap.IsHurwitz (ic.closedLoopMap h)) :
    ∃ A γ : ℝ, 0 ≤ A ∧ 0 < γ ∧
      ∀ t : ℝ, 0 ≤ t → ‖ic.externalResponseOperator h t‖ ≤ A * Real.exp (-γ * t) := by
  obtain ⟨C, hCpos, γ, hγpos, hbound⟩ :=
    LinearMap.exists_exponential_norm_bound_of_isHurwitz (ic.closedLoopMap h) hH
  refine ⟨‖ic.outputMap.toContinuousLinearMap‖ *
      ‖(ic.disturbanceMapWithF h).toContinuousLinearMap‖ * C, γ, ?_, hγpos, ?_⟩
  · exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hCpos.le
  · intro t ht
    have hexp : (ic.closedLoopSystem h).expFlow t =
        NormedSpace.exp (t • (ic.closedLoopMap h).toContinuousLinearMap) :=
      ic.closedLoopSystem_expFlow_eq h t
    rw [externalResponseOperator, hexp]
    calc ‖(ic.outputMap.toContinuousLinearMap).comp
          ((NormedSpace.exp (t • (ic.closedLoopMap h).toContinuousLinearMap)).comp
            (ic.disturbanceMapWithF h).toContinuousLinearMap)‖
        ≤ ‖ic.outputMap.toContinuousLinearMap‖ *
            ‖(NormedSpace.exp (t • (ic.closedLoopMap h).toContinuousLinearMap)).comp
              (ic.disturbanceMapWithF h).toContinuousLinearMap‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖ic.outputMap.toContinuousLinearMap‖ *
            (‖NormedSpace.exp (t • (ic.closedLoopMap h).toContinuousLinearMap)‖ *
              ‖(ic.disturbanceMapWithF h).toContinuousLinearMap‖) := by
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖ic.outputMap.toContinuousLinearMap‖ *
            ((C * Real.exp (-γ * t)) *
              ‖(ic.disturbanceMapWithF h).toContinuousLinearMap‖) := by
          gcongr
          exact hbound t ht
      _ = (‖ic.outputMap.toContinuousLinearMap‖ *
            ‖(ic.disturbanceMapWithF h).toContinuousLinearMap‖ * C) *
            Real.exp (-γ * t) := by ring

/-- The external impulse-response operator is Bochner integrable on `[0, ∞)`
when the closed loop is Hurwitz. -/
theorem externalResponseOperator_integrable (h : ic.IsWellPosed)
    (hH : LinearMap.IsHurwitz (ic.closedLoopMap h)) :
    IntegrableOn (fun t : ℝ => ic.externalResponseOperator h t) (Set.Ici 0) := by
  obtain ⟨A, γ, hA, hγ, hbound⟩ := ic.norm_externalResponseOperator_le h hH
  have hg : IntegrableOn (fun t : ℝ => A * Real.exp (-γ * t)) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi
      (f := fun t : ℝ => A * Real.exp (-γ * t)) (b := 0)).mpr
      ((exp_neg_integrableOn_Ioi 0 hγ).const_mul A)
  refine Integrable.mono' hg ?_ ?_
  · exact (ic.continuous_externalResponseOperator h).aestronglyMeasurable.restrict
  · filter_upwards [self_mem_ae_restrict measurableSet_Ici] with t ht
    exact hbound t ht

/-- The norm of the external impulse-response operator is integrable on
`[0, ∞)` when the closed loop is Hurwitz. Its total mass is the BIBO constant. -/
theorem norm_externalResponseOperator_integrable (h : ic.IsWellPosed)
    (hH : LinearMap.IsHurwitz (ic.closedLoopMap h)) :
    IntegrableOn (fun t : ℝ => ‖ic.externalResponseOperator h t‖) (Set.Ici 0) :=
  (ic.externalResponseOperator_integrable h hH).norm

/-- **Bochner integrability of the external response.** Under a Hurwitz closed
loop the forced response `t ↦ externalResponse h t d` is integrable on `[0, ∞)`
for every disturbance direction `d`. -/
theorem externalResponse_integrable (h : ic.IsWellPosed)
    (hH : LinearMap.IsHurwitz (ic.closedLoopMap h)) (d : D) :
    IntegrableOn (fun t : ℝ => ic.externalResponse h t d) (Set.Ici 0) := by
  have hKn := ic.norm_externalResponseOperator_integrable h hH
  have hg : IntegrableOn
      (fun t : ℝ => ‖ic.externalResponseOperator h t‖ * ‖d‖) (Set.Ici 0) :=
    hKn.mul_const ‖d‖
  refine Integrable.mono' hg ?_ ?_
  · exact (ic.continuous_externalResponse h d).aestronglyMeasurable.restrict
  · filter_upwards [self_mem_ae_restrict measurableSet_Ici] with t ht
    calc ‖ic.externalResponse h t d‖
        = ‖ic.externalResponseOperator h t d‖ := by rw [externalResponseOperator_apply]
      _ ≤ ‖ic.externalResponseOperator h t‖ * ‖d‖ :=
          (ic.externalResponseOperator h t).le_opNorm d

omit [FiniteDimensional ℝ D] in
/-- **The forced response is the disturbance impulse response of the closed
loop.** This is the bridge to the disturbance-convolution API: the closed-loop
impulse response `externalResponse` is exactly
`LinearMap.disturbanceImpulseResponse` of the channel
`(closedLoopMap h, disturbanceMapWithF h, outputMap)`. -/
theorem externalResponse_eq_disturbanceImpulseResponse (h : ic.IsWellPosed)
    (t : ℝ) (d : D) :
    ic.externalResponse h t d =
      LinearMap.disturbanceImpulseResponse (ic.closedLoopMap h) (ic.disturbanceMapWithF h)
        ic.outputMap t d := rfl

/-- **Convolution form of the closed-loop forced output.** For a locally
integrable disturbance and zero initial state, the closed-loop disturbance
contribution is the convolution of `externalResponse` with the disturbance.
This is `LinearMap.disturbanceContribution_eq_convolution` for the closed-loop
channel, with the zero initial state and the admissible locally integrable input
kept explicit. -/
theorem disturbanceContribution_eq_convolution_externalResponse [CompleteSpace Z]
    (h : ic.IsWellPosed) {d : ℝ → D} (hd : LocallyIntegrable d volume) (t : ℝ) :
    LinearMap.disturbanceContribution (ic.closedLoopMap h) (ic.disturbanceMapWithF h)
        ic.outputMap 0 d t =
      ∫ s in (0 : ℝ)..t, ic.externalResponse h (t - s) (d s) := by
  rw [LinearMap.disturbanceContribution_eq_convolution _ _ _ hd t]
  apply intervalIntegral.integral_congr
  intro s _
  exact (ic.externalResponse_eq_disturbanceImpulseResponse h (t - s) (d s)).symm

/-- **Bochner integrability and bounded-input bounded-output stability of the
external response.** The forced disturbance-to-controlled-output channel of a
well-posed interconnection with Hurwitz extended closed loop is

* Bochner integrable on `[0, ∞)` in every disturbance direction, and
* bounded-input bounded-output: the convolution of the impulse response with a
  bounded, admissible (locally integrable) disturbance is bounded by the total
  mass of the impulse response, independently of the disturbance and of time.

This is the BIBO/integrability bridge of Trentelman–Stoorvogel–Hautus, Theorem
3.21, for the closed loop (6.12). The geometric necessary-and-sufficient
conditions of Corollary 6.22 are not part of this predicate. -/
noncomputable def IsBIBOStable (h : ic.IsWellPosed) : Prop :=
  (∀ d : D, IntegrableOn (fun t : ℝ => ic.externalResponse h t d) (Set.Ici 0)) ∧
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (d : ℝ → D), LocallyIntegrable d volume →
        (∀ t : ℝ, 0 ≤ t → ‖d t‖ ≤ 1) →
          ∀ t : ℝ, 0 ≤ t →
            ‖∫ s in (0 : ℝ)..t, ic.externalResponse h (t - s) (d s)‖ ≤ M

/-- **Hurwitz closed loop implies BIBO stability.** The BIBO constant is the
total mass `∫_0^∞ ‖H_e e^{t A_e} B_e‖ dt` of the impulse-response operator, whose
integrability is the exponential bound of `norm_externalResponseOperator_le`. -/
theorem isBIBOStable_of_isHurwitz (h : ic.IsWellPosed)
    (hH : LinearMap.IsHurwitz (ic.closedLoopMap h)) : ic.IsBIBOStable h := by
  refine ⟨fun d => ic.externalResponse_integrable h hH d, ?_⟩
  have hKn : IntegrableOn (fun t : ℝ => ‖ic.externalResponseOperator h t‖) (Set.Ici 0) :=
    ic.norm_externalResponseOperator_integrable h hH
  refine ⟨∫ t in Set.Ici (0 : ℝ), ‖ic.externalResponseOperator h t‖,
    integral_nonneg_of_ae (Eventually.of_forall fun _ => norm_nonneg _), ?_⟩
  intro d _hd hd_bound t ht
  have hg_int : IntervalIntegrable
      (fun s : ℝ => ‖ic.externalResponseOperator h (t - s)‖) volume 0 t := by
    have hcont : Continuous (fun s : ℝ => ic.externalResponseOperator h (t - s)) :=
      (ic.continuous_externalResponseOperator h).comp (by fun_prop)
    exact hcont.norm.intervalIntegrable 0 t
  have hle : ‖∫ s in (0 : ℝ)..t, ic.externalResponse h (t - s) (d s)‖ ≤
      ∫ s in (0 : ℝ)..t, ‖ic.externalResponseOperator h (t - s)‖ := by
    refine intervalIntegral.norm_integral_le_of_norm_le ht ?_ hg_int
    filter_upwards with s hs
    calc ‖ic.externalResponse h (t - s) (d s)‖
        = ‖ic.externalResponseOperator h (t - s) (d s)‖ := by
          rw [externalResponseOperator_apply]
      _ ≤ ‖ic.externalResponseOperator h (t - s)‖ * ‖d s‖ :=
          (ic.externalResponseOperator h (t - s)).le_opNorm (d s)
      _ ≤ ‖ic.externalResponseOperator h (t - s)‖ * 1 := by
          gcongr
          exact hd_bound s (le_of_lt hs.1)
      _ = ‖ic.externalResponseOperator h (t - s)‖ := mul_one _
  refine hle.trans ?_
  have hsubst : (∫ s in (0 : ℝ)..t, ‖ic.externalResponseOperator h (t - s)‖) =
      ∫ u in (0 : ℝ)..t, ‖ic.externalResponseOperator h u‖ := by
    simpa using intervalIntegral.integral_comp_sub_left (a := 0) (b := t)
      (fun u : ℝ => ‖ic.externalResponseOperator h u‖) t
  rw [hsubst, intervalIntegral.integral_of_le ht]
  exact setIntegral_mono_set hKn
    (Eventually.of_forall fun _ => norm_nonneg _)
    (Eventually.of_forall fun x hx => le_of_lt hx.1)

end BIBO

end DynamicInterconnection

section RealClosedLoopBIBO

variable {X U Y W D Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
variable [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [AddCommGroup U] [Module ℝ U] [AddCommGroup Y] [Module ℝ Y]
variable (ic : DynamicInterconnection ℝ X U Y W D Z)

/-- **Bochner integrability of the closed-loop impulse response.** If the
extended closed-loop map `A_e` of a well-posed interconnection is Hurwitz then
the forced disturbance-to-output impulse response is Bochner integrable on
`[0, ∞)` in every disturbance direction. This is the integrability half of the
external BIBO bridge (Trentelman–Stoorvogel–Hautus, Theorem 3.21). -/
theorem externalResponse_integrable_of_isHurwitz (h : ic.IsWellPosed)
    (hH : LinearMap.IsHurwitz (ic.closedLoopMap h)) (d : D) :
    IntegrableOn (fun t : ℝ => ic.externalResponse h t d) (Set.Ici 0) :=
  ic.externalResponse_integrable h hH d

/-- **BIBO stability of the closed-loop impulse response.** If the extended
closed-loop map `A_e` is Hurwitz then the forced disturbance-to-controlled-output
channel is bounded-input bounded-output for every bounded, admissible (locally
integrable) disturbance, with zero initial state. This is the BIBO half of the
external bridge (Trentelman–Stoorvogel–Hautus, Theorem 3.21); the geometric
necessary-and-sufficient conditions of Corollary 6.22 are not claimed. -/
theorem isBIBOStable_externalResponse_of_isHurwitz (h : ic.IsWellPosed)
    (hH : LinearMap.IsHurwitz (ic.closedLoopMap h)) :
    ic.IsBIBOStable h :=
  ic.isBIBOStable_of_isHurwitz h hH

/-- **BIBO stability for the strictly proper cabPair controller.** For a strictly
proper plant (`D = 0`) whose cabPair controller (6.7) has Hurwitz state-feedback
and observer-error blocks, the closed-loop disturbance-to-output channel is BIBO
stable. This specializes the Hurwitz bridge to the accepted controller of
Sections 6.3–6.6 and makes the strictly proper, well-posed hypotheses explicit. -/
theorem isBIBOStable_externalResponse_cabPairController
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (F : X →ₗ[ℝ] U) (G : Y →ₗ[ℝ] X) (N : Y →ₗ[ℝ] U)
    (hwp : (cabPairInterconnection sys (cabPairController sys F G N) E H).IsWellPosed)
    (hF : LinearMap.IsHurwitz (sys.A + sys.B.comp F))
    (hG : LinearMap.IsHurwitz (sys.A + G.comp sys.C)) :
    (cabPairInterconnection sys (cabPairController sys F G N) E H).IsBIBOStable hwp :=
  isBIBOStable_externalResponse_of_isHurwitz _ hwp
    (isHurwitz_closedLoopMap_cabPairController sys hD E H F G N hwp hF hG)

end RealClosedLoopBIBO

section RealClosedLoopBIBOExistence

variable {X U Y D Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [AddCommGroup U] [Module ℝ U]
variable [AddCommGroup Y] [Module ℝ Y] [FiniteDimensional ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

/-- **Existence of a BIBO-stabilizing dynamic measurement feedback.** A
controllable and observable strictly proper plant admits a cabPair controller
with accepted Hurwitz gains whose closed-loop disturbance-to-output channel is
BIBO stable. The gains are those of `exists_hurwitz_cabPair_gains`, so the BIBO
bridge is not vacuous. -/
theorem exists_biboStable_cabPair_gains (sys : LinearSystem ℝ X U Y)
    (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (hcont : LinearMap.IsControllable sys.A sys.B)
    (hobs : LinearMap.IsObservable sys.C sys.A) :
    ∃ F : X →ₗ[ℝ] U, ∃ G : Y →ₗ[ℝ] X, ∃ N : Y →ₗ[ℝ] U,
      (cabPairInterconnection sys (cabPairController sys F G N) E H).IsBIBOStable
        ((cabPairInterconnection sys (cabPairController sys F G N) E H).isWellPosed_of_D_eq_zero
          hD) := by
  obtain ⟨F, G, hF, hG⟩ := exists_hurwitz_cabPair_gains sys hcont hobs
  refine ⟨F, G, 0, ?_⟩
  exact isBIBOStable_externalResponse_cabPairController sys hD E H F G 0 _ hF hG

end RealClosedLoopBIBOExistence

/-! ## The geometric external zero-response criterion

This final section states the geometric necessary-and-sufficient criterion for
the *exact* external zero response of a strictly proper plant under dynamic
measurement feedback, and separates it from BIBO stability.

The Trentelman–Stoorvogel–Hautus external-stabilization problem (Definition 6.19)
asks for a controller making the closed-loop transfer function
`G_Κ(s) = H_e (s I - A_e)⁻¹ B_e` *stable*. Corollary 6.22 characterises this by
`im E ⊂ V*(ker H) + Xstab` together with `S*(im E) ∩ Xdet ⊂ ker H`, where
`Xstab` is the stabilizable subspace of `(A, B)` and `Xdet` the undetectable
subspace of `(C, A)`. Neither subspace (nor its spectral characterisation) is
available in the pinned library, so the full Corollary 6.22 is **not** formalised
here; the package `external-stability-subspaces` records the gap.

What *is* formalised is the exact-decoupling idealisation: the forced external
impulse response `t ↦ H_e e^{t A_e} B_e` vanishes identically. By the analytic
Markov-parameter bridge this is exactly the Chapter 6 disturbance-decoupling
predicate, whose geometric certificate is a `(C, A, B)`-pair between `im E` and
`ker H`. This is strictly stronger than BIBO stability, and the two are only
combined after adjoining Hurwitz gains (`bibo_and_externalZeroResponse_…`). -/

namespace DynamicInterconnection

section AnalyticZeroResponse

variable {X U Y W D Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [AddCommGroup U] [Module ℝ U] [AddCommGroup Y] [Module ℝ Y]
variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ W]
variable (ic : DynamicInterconnection ℝ X U Y W D Z)

/-- **Identically vanishing external response.** The forced disturbance-to-output
impulse response `H_e e^{t A_e} B_e` of a well-posed interconnection is zero in
every disturbance direction and at every time. This is the exact zero-response
(external disturbance decoupling) property.

It is *not* the same as bounded-input bounded-output stability: a nonzero but
decaying impulse response is BIBO stable yet does not satisfy this predicate. The
separation is made explicit by
`bibo_and_externalZeroResponse_of_geometricCertificate_hurwitz`, which derives
BIBO *and* zero response only after adjoining Hurwitz gains to the geometric
certificate. -/
noncomputable def HasExternalZeroResponse (h : ic.IsWellPosed) : Prop :=
  ∀ t : ℝ, ∀ d : D, ic.externalResponse h t d = 0

/-- **Analytic bridge for the external zero response.** For a well-posed
interconnection the forced external response vanishes identically if and only if
the closed loop is disturbance decoupled for the full measurement-disturbance
channel `disturbanceMapWithF`, i.e. all Markov parameters
`H_e A_e^k B_e` vanish. Both sides use the same extended system, and the operator
exponential of `disturbanceSystem` agrees with the closed-loop flow.

This is the analytic (impulse-response) form of the Chapter 4/6 decoupling
predicate and the entry point for the geometric extraction below. -/
theorem hasExternalZeroResponse_iff_isClosedLoopDisturbanceDecoupledWithF
    (h : ic.IsWellPosed) :
    ic.HasExternalZeroResponse h ↔ ic.IsClosedLoopDisturbanceDecoupledWithF h := by
  rw [IsClosedLoopDisturbanceDecoupledWithF,
    LinearMap.isDisturbanceDecoupled_iff_forall_expFlow]
  have hflow : ∀ t : ℝ,
      (LinearMap.disturbanceSystem (ic.closedLoopMap h) (ic.disturbanceMapWithF h)
        ic.outputMap).expFlow t = (ic.closedLoopSystem h).expFlow t := by
    intro t
    simp only [LinearSystem.expFlow, LinearSystem.continuousA,
      LinearMap.disturbanceSystem, ic.closedLoopSystem_A h]
  constructor
  · intro hz d t
    have hd := hz t d
    simpa [externalResponse, hflow t] using hd
  · intro hdec t d
    have hd := hdec d t
    simpa [externalResponse, hflow t] using hd

end AnalyticZeroResponse

end DynamicInterconnection

section GeometricExternalZeroResponse

variable {X U Y D Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [AddCommGroup U] [Module ℝ U] [AddCommGroup Y] [Module ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [FiniteDimensional ℝ X] [FiniteDimensional ℝ D]

/-- **Geometric external zero-response certificate.** A strictly proper plant
`sys` with disturbance map `E` and controlled output `H` admits the geometric
certificate when there is a `(C, A, B)`-pair `(S, V)` between `im E` and
`ker H`: `S` conditioned invariant, `V` controlled invariant, `S ≤ V`,
`im E ≤ S` and `V ≤ ker H`.

Source: Trentelman–Stoorvogel–Hautus, Definition 6.1 and Corollary 6.7 (the
zero-response/decoupling certificate). -/
def GeometricCertificate (sys : LinearSystem ℝ X U Y) (E : D →ₗ[ℝ] X)
    (H : X →ₗ[ℝ] Z) : Prop :=
  ∃ S V : Submodule ℝ X, LinearMap.IsCABPairBetween sys.C sys.A sys.B E H S V

/-- **External zero-response property of a plant.** There exists a
finite-dimensional dynamic measurement-feedback controller (with state space `X`
and the strictly proper `cabPairInterconnection`, i.e. zero measurement
disturbance channel and zero control feedthrough) that is well posed and whose
forced external response vanishes identically.

This is the exact-decoupling reading of external stability. It is explicitly the
zero-response predicate, not BIBO stability; the latter requires additional
Hurwitz gain data and is the subject of
`bibo_and_externalZeroResponse_of_geometricCertificate_hurwitz`. -/
noncomputable def ExternalStability (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) : Prop :=
  ∃ ctrl : DynamicController ℝ X Y U,
    DynamicInterconnection.HasExternalZeroResponse
      (ic := cabPairInterconnection sys ctrl E H)
      ((cabPairInterconnection sys ctrl E H).isWellPosed_of_D_eq_zero hD)

omit [FiniteDimensional ℝ D] in
/-- **Necessity: geometric certificate from external zero response.** A strictly
proper plant admitting a dynamic measurement-feedback controller with identically
zero external response carries a `(C, A, B)`-pair between `im E` and `ker H`.

The external response is converted to the closed-loop Markov-parameter predicate
by `hasExternalZeroResponse_iff_isClosedLoopDisturbanceDecoupledWithF`, then the
accepted Theorem 6.2 extraction
`exists_isCABPairBetween_of_isClosedLoopDisturbanceDecoupled` produces the pair.

Source: Trentelman–Stoorvogel–Hautus, Theorem 6.2 and the forward half of
Theorem 6.6. -/
theorem exists_isCABPairBetween_of_externalStability
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : ExternalStability sys hD E H) :
    ∃ S V : Submodule ℝ X, LinearMap.IsCABPairBetween sys.C sys.A sys.B E H S V := by
  obtain ⟨ctrl, hz⟩ := h
  let ic : DynamicInterconnection ℝ X U Y X D Z := cabPairInterconnection sys ctrl E H
  have hwp : ic.IsWellPosed := ic.isWellPosed_of_D_eq_zero hD
  have hz' : ic.HasExternalZeroResponse hwp := by
    simpa only [ic] using hz
  have hdecF : ic.IsClosedLoopDisturbanceDecoupledWithF hwp :=
    (ic.hasExternalZeroResponse_iff_isClosedLoopDisturbanceDecoupledWithF hwp).mp hz'
  have hdec : ic.IsClosedLoopDisturbanceDecoupled hwp :=
    (ic.isClosedLoopDisturbanceDecoupledWithF_of_F_eq_zero hwp rfl).mp hdecF
  exact ic.exists_isCABPairBetween_of_isClosedLoopDisturbanceDecoupled hwp hdec

omit [FiniteDimensional ℝ D] in
/-- **The geometric external zero-response criterion.** For a strictly proper
plant, the existence of a dynamic measurement-feedback controller whose forced
external response vanishes identically is equivalent to the geometric
certificate: a `(C, A, B)`-pair between `im E` and `ker H`.

The necessity direction is
`exists_isCABPairBetween_of_externalStability`; the sufficiency direction
synthesises the controller (6.7) from the pair
(`exists_dynamicController_of_isCABPairBetween`) and invokes the analytic bridge.

This is the externally-stated form of the Chapter 6 exact-decoupling criterion
(Theorem 6.6 / Corollary 6.7). It concerns the *zero* response, not merely
stability of the transfer function: the full external-stabilization Corollary
6.22 additionally needs `Xstab`/`Xdet` and is not claimed here. -/
theorem externalStability_iff_geometricCertificate
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    ExternalStability sys hD E H ↔ GeometricCertificate sys E H := by
  constructor
  · intro h
    exact exists_isCABPairBetween_of_externalStability sys hD E H h
  · rintro ⟨S, V, hpair⟩
    obtain ⟨ctrl, hdec⟩ :=
      exists_dynamicController_of_isCABPairBetween sys hD E H S V hpair
    refine ⟨ctrl, ?_⟩
    let ic : DynamicInterconnection ℝ X U Y X D Z := cabPairInterconnection sys ctrl E H
    have hwp : ic.IsWellPosed := ic.isWellPosed_of_D_eq_zero hD
    have hdec' : ic.IsClosedLoopDisturbanceDecoupled hwp := by
      simpa only [ic] using hdec
    have hdecF : ic.IsClosedLoopDisturbanceDecoupledWithF hwp :=
      (ic.isClosedLoopDisturbanceDecoupledWithF_of_F_eq_zero hwp rfl).mpr hdec'
    exact (ic.hasExternalZeroResponse_iff_isClosedLoopDisturbanceDecoupledWithF hwp).mpr hdecF

/-! ### The geometric subspace conditions of Corollary 6.22

The full geometric external-stabilization criterion of
Trentelman–Stoorvogel–Hautus, Corollary 6.22, states that an externally
stabilizing controller exists exactly when

* `im E ≤ V*(ker H) + Xstab` (`Xstab = stabilizableSubspace A B`), and
* `S*(im E) ∩ Xdet ≤ ker H` (`S* = conditionedInvariantSubspace C A`,
  `Xdet = detectableSubspace C A`).

The two inclusions are recorded by
`ExternalStabilizationConditions`; the accepted
`(C, A, B)`-pair certificate already entails both, and the necessary-direction
extraction `externalStabilizationConditions_of_externalStability` obtains them
from the exact external zero response. The genuinely analytic converse (a stable
but nonzero transfer function) additionally requires the trajectory
characterisation `W_g(ker H) = V*(ker H) + Xstab` (Theorem 4.37) and the
quotient-spectrum transfer lemma (Lemma 4.35); those are **not** available and are
recorded in the handoff rather than assumed. -/

/-- **The geometric subspace conditions of Corollary 6.22.** The disturbance
image lies in the sum of the largest controlled invariant subspace inside
`ker H` and the stabilizable subspace, and dually the smallest conditioned
invariant subspace containing `im E` meets the detectable subspace inside
`ker H`.

Source: Trentelman–Stoorvogel–Hautus, Corollary 6.22, displays (6.30) and
(6.32) (PDF pages 159–160 / printed pages 145–146). -/
def ExternalStabilizationConditions (sys : LinearSystem ℝ X U Y) (E : D →ₗ[ℝ] X)
    (H : X →ₗ[ℝ] Z) : Prop :=
  LinearMap.range E ≤
      LinearMap.controlledInvariantSubspace sys.A sys.B (LinearMap.ker H) ⊔
        LinearMap.stabilizableSubspace sys.A sys.B ∧
    LinearMap.conditionedInvariantSubspace sys.C sys.A (LinearMap.range E) ⊓
        LinearMap.detectableSubspace sys.C sys.A ≤ LinearMap.ker H

omit [FiniteDimensional ℝ D] in
/-- **A `(C, A, B)`-pair entails the two Corollary 6.22 conditions.** This is the
order-theoretic half of the Corollary: `im E ≤ S ≤ V*(ker H)`, and
`S*(im E) ∩ Xdet ≤ S*(im E) ≤ S ≤ V ≤ ker H` because `S*(im E)` is the least
conditioned invariant subspace containing `im E` and `V*(ker H)` is the greatest
controlled invariant subspace inside `ker H`.

Source: Trentelman–Stoorvogel–Hautus, Corollary 6.22 and the proof of
Lemma 6.21 (PDF pages 159–160 / printed pages 145–146). -/
theorem externalStabilizationConditions_of_isCABPairBetween
    (sys : LinearSystem ℝ X U Y) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (S V : Submodule ℝ X)
    (hpair : LinearMap.IsCABPairBetween sys.C sys.A sys.B E H S V) :
    ExternalStabilizationConditions sys E H := by
  obtain ⟨⟨hSV, hS, hV⟩, hE, hH⟩ := hpair
  refine ⟨?_, ?_⟩
  · calc LinearMap.range E ≤ S := hE
      _ ≤ V := hSV
      _ ≤ LinearMap.controlledInvariantSubspace sys.A sys.B (LinearMap.ker H) :=
            LinearMap.le_controlledInvariantSubspace hH hV
      _ ≤ LinearMap.controlledInvariantSubspace sys.A sys.B (LinearMap.ker H) ⊔
            LinearMap.stabilizableSubspace sys.A sys.B := le_sup_left
  · calc LinearMap.conditionedInvariantSubspace sys.C sys.A (LinearMap.range E) ⊓
          LinearMap.detectableSubspace sys.C sys.A
        ≤ LinearMap.conditionedInvariantSubspace sys.C sys.A (LinearMap.range E) := inf_le_left
      _ ≤ S := LinearMap.conditionedInvariantSubspace_le hE hS
      _ ≤ V := hSV
      _ ≤ LinearMap.ker H := hH

omit [FiniteDimensional ℝ D] in
/-- **Necessity of the Corollary 6.22 conditions from exact external zero
response.** The accepted extraction of a `(C, A, B)`-pair from the identically
vanishing forced response is combined with
`externalStabilizationConditions_of_isCABPairBetween` to obtain both Corollary
6.22 inclusions. This is the necessary direction under the stronger
zero-response premise; the converse from a merely stable nonzero transfer
function is not claimed (see the section note). -/
theorem externalStabilizationConditions_of_externalStability
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : ExternalStability sys hD E H) :
    ExternalStabilizationConditions sys E H := by
  obtain ⟨S, V, hpair⟩ := exists_isCABPairBetween_of_externalStability sys hD E H h
  exact externalStabilizationConditions_of_isCABPairBetween sys E H S V hpair

omit [FiniteDimensional ℝ D] in
/-- **Integrated geometric external-stability criterion.** The exact external
zero-response property of the strictly proper plant is equivalent to the
conjunction of the accepted `(C, A, B)`-pair certificate and the two geometric
subspace conditions of Corollary 6.22. The forward direction extracts both the
pair (`exists_isCABPairBetween_of_externalStability`, equivalently
`externalStability_iff_geometricCertificate`) and the stabilizable/detectable
inclusions (`externalStabilizationConditions_of_externalStability`); the backward
direction synthesises the controller from the pair through the accepted
Theorem 6.6 equivalence.

Because a `(C, A, B)`-pair entails the two inclusions, the conjunction is
logically equivalent to the pair certificate alone; it is stated explicitly so
that the Corollary 6.22 conditions are part of the certified output of the
theorem. -/
theorem externalStability_iff_geometricCertificate_and_conditions
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    ExternalStability sys hD E H ↔
      GeometricCertificate sys E H ∧ ExternalStabilizationConditions sys E H := by
  constructor
  · intro h
    exact ⟨(externalStability_iff_geometricCertificate sys hD E H).mp h,
      externalStabilizationConditions_of_externalStability sys hD E H h⟩
  · rintro ⟨hgc, _⟩
    exact (externalStability_iff_geometricCertificate sys hD E H).mpr hgc

/-- **BIBO stability and external zero response from a stabilising certificate.**
Suppose the geometric certificate `(S, V)` is equipped with gains `F`, `G`, `N`
that preserve the pair (`(A + B F) V ≤ V`, `(A + G C) S ≤ S`,
`(A + B N C) S ≤ V`) and for which the state-feedback block `A + B F` and the
observer-error block `A + G C` are Hurwitz. Then the cabPair controller (6.7) is
well posed, its forced disturbance-to-output channel is BIBO stable (accepted BIBO
bridge) **and** its external response vanishes identically (Theorem 6.6 plus the
analytic bridge).

This is the point at which the zero-response (decoupling) content and the BIBO
(stability) content are combined: the geometric pair alone gives only the former;
the Hurwitz gains are the extra data needed for the latter. No identification of
the two notions is made. -/
theorem bibo_and_externalZeroResponse_of_geometricCertificate_hurwitz
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (S V : Submodule ℝ X) (hpair : LinearMap.IsCABPairBetween sys.C sys.A sys.B E H S V)
    (F : X →ₗ[ℝ] U) (G : Y →ₗ[ℝ] X) (N : Y →ₗ[ℝ] U)
    (hF : Submodule.map (sys.A + sys.B.comp F) V ≤ V)
    (hG : Submodule.map (sys.A + G.comp sys.C) S ≤ S)
    (hN : Submodule.map (sys.A + sys.B.comp (N.comp sys.C)) S ≤ V)
    (hFh : LinearMap.IsHurwitz (sys.A + sys.B.comp F))
    (hGh : LinearMap.IsHurwitz (sys.A + G.comp sys.C)) :
    let ic : DynamicInterconnection ℝ X U Y X D Z :=
      cabPairInterconnection sys (cabPairController sys F G N) E H
    ic.IsBIBOStable (ic.isWellPosed_of_D_eq_zero hD) ∧
      ic.HasExternalZeroResponse (ic.isWellPosed_of_D_eq_zero hD) := by
  let ic : DynamicInterconnection ℝ X U Y X D Z :=
    cabPairInterconnection sys (cabPairController sys F G N) E H
  have hwp : ic.IsWellPosed := ic.isWellPosed_of_D_eq_zero hD
  have hdec : ic.IsClosedLoopDisturbanceDecoupled hwp :=
    isClosedLoopDisturbanceDecoupled_of_isCABPairBetween sys hD E H S V hpair F G N
      hF hG hN hwp
  have hbibo : ic.IsBIBOStable hwp :=
    isBIBOStable_externalResponse_cabPairController sys hD E H F G N hwp hFh hGh
  have hzero : ic.HasExternalZeroResponse hwp := by
    have hdecF : ic.IsClosedLoopDisturbanceDecoupledWithF hwp :=
      (ic.isClosedLoopDisturbanceDecoupledWithF_of_F_eq_zero hwp rfl).mpr hdec
    exact (ic.hasExternalZeroResponse_iff_isClosedLoopDisturbanceDecoupledWithF hwp).mpr hdecF
  exact ⟨hbibo, hzero⟩

end GeometricExternalZeroResponse

/-! ## The trajectory/spectral external-stability bridge

Trentelman–Stoorvogel–Hautus, Theorem 4.37 and Lemma 4.35, characterise the
states from which the controlled output can be made stable by a state feedback
through `W_g(ker H) = V*(ker H) + Xstab`. The analytic content of Lemma 4.35 is
that a quotient-spectrum condition transfers to a decay statement for the
controlled-output trajectory. This section records that bridge.

The reusable core is `clm_map_exp_smul`: for continuous linear maps `L`, `A`,
`B` with `L ∘ A = B ∘ L`, the exponential of `A` pushes forward along `L` to the
exponential of `B`. Specialising to the quotient `X ⧸ V` by an `A`-invariant
subspace `V` gives `tendsto_readout_exp_of_isHurwitz_mapQ`: if the readout `H`
vanishes on `V` and the induced map on `X ⧸ V` is Hurwitz, then the readout of
any `A`-trajectory decays. The state-feedback form
`tendsto_readout_exp_of_isHurwitz_quotient_on` restricts to an `(A + B F)`-
invariant subspace `W` containing the disturbance image, so only the quotient
`W / V` need be Hurwitz.

The remaining source obligation — constructing the feedback `F` of Lemma 4.38
from `im E ≤ V*(ker H) + Xstab` so that `σ(A_F | W_g/V*) ⊂ C_g` — is **not**
formalised here; it is recorded as the handoff item. These theorems supply the
analytic half of the bridge with the spectral hypothesis explicit. -/

set_option linter.style.haveILetI false

set_option maxHeartbeats 800000 in
-- The infinite-sum manipulation in the exponential push-forward lemma needs a
-- larger heartbeat budget than the default.
/-- **Push-forward of the exponential along an intertwining continuous linear
map.** If `L ∘ A = B ∘ L` for continuous linear maps over `ℝ`, then applying
`L` commutes with the one-parameter exponential groups,
`L (exp (t • A) x) = exp (t • B) (L x)`.

This is the general form of the quotient-spectrum-to-trajectory step: the
exponential series pushes forward because `L` is continuous and intertwines the
powers `A^n` and `B^n`; uniqueness of the sum then identifies the two sides. -/
theorem clm_map_exp_smul
    {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (L : X →L[ℝ] Y) (A : X →L[ℝ] X) (B : Y →L[ℝ] Y)
    (h : L.comp A = B.comp L) (t : ℝ) (x : X) :
    L (NormedSpace.exp (t • A) x) = NormedSpace.exp (t • B) (L x) := by
  have hscalar : ∀ y : X, L ((t • A) y) = (t • B) (L y) := by
    intro y
    have hy : L (A y) = B (L y) := congrFun (congrArg DFunLike.coe h) y
    simp only [smul_apply, map_smul, hy]
  have hpow : ∀ n : ℕ, ∀ y : X, L (((t • A) ^ n) y) = ((t • B) ^ n) (L y) := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ, pow_succ, mul_apply_eq_comp, ih, hscalar, mul_apply_eq_comp]
  have hAtsum : NormedSpace.exp (t • A) x =
      ∑' n : ℕ, ((n.factorial : ℝ))⁻¹ • (((t • A) ^ n) x) :=
    LinearMap.exp_smul_apply_eq_tsum A t x
  have hBtsum : NormedSpace.exp (t • B) (L x) =
      ∑' n : ℕ, ((n.factorial : ℝ))⁻¹ • (((t • B) ^ n) (L x)) :=
    LinearMap.exp_smul_apply_eq_tsum B t (L x)
  rw [hAtsum, hBtsum]
  change L (∑' n : ℕ, ((n.factorial : ℝ))⁻¹ • (((t • A) ^ n) x)) =
    ∑' n : ℕ, ((n.factorial : ℝ))⁻¹ • (((t • B) ^ n) (L x))
  rw [ContinuousLinearMap.map_tsum]
  · apply tsum_congr; intro n
    rw [map_smul, hpow n]
  · have hball : (t • A) ∈ Metric.eball (0 : X →L[ℝ] X)
        (NormedSpace.expSeries ℝ (X →L[ℝ] X)).radius :=
      (NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _
    have hmap := (NormedSpace.expSeries_summable_of_mem_ball' (t • A) hball).mapL
      ((ContinuousLinearMap.apply ℝ X) x)
    simpa only [ContinuousLinearMap.apply_apply, smul_apply] using hmap

section TrajectorySpectralBridge

variable {X Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- **Quotient-spectrum readout decay.** Let `V` be an `A`-invariant subspace on
which the readout `H` vanishes, and suppose the induced map
`A : X ⧸ V → X ⧸ V` is Hurwitz. Then the controlled output of every
`A`-trajectory decays:
`t ↦ H (exp (t • A) x)` tends to `0` at `+∞`.

This is the analytic content of Trentelman–Stoorvogel–Hautus, Lemma 4.35: the
readout factors through the quotient because `V ≤ ker H`, the exponential
pushes forward along the quotient map by `clm_map_exp_smul`, and the quotient
trajectory decays by the accepted real Hurwitz decay theorem
`LinearMap.tendsto_exp_of_isHurwitz`. No stability of the readout is assumed. -/
theorem tendsto_readout_exp_of_isHurwitz_mapQ
    (A : X →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) (V : Submodule ℝ X)
    (hV : V ≤ V.comap A) (hVH : V ≤ LinearMap.ker H)
    (hH : LinearMap.IsHurwitz (V.mapQ V A hV)) (x : X) :
    Tendsto (fun t : ℝ => H (NormedSpace.exp (t • A.toContinuousLinearMap) x))
      atTop (nhds 0) := by
  haveI : IsClosed (V : Set X) := V.closed_of_finiteDimensional
  letI : IsTopologicalRing ((X ⧸ V) →L[ℝ] (X ⧸ V)) :=
    { continuous_add := continuous_add
      continuous_mul := Continuous.clm_comp continuous_fst continuous_snd
      continuous_neg := continuous_neg }
  let q : X →L[ℝ] X ⧸ V := V.mkQ.toContinuousLinearMap
  let Aq : X ⧸ V →ₗ[ℝ] X ⧸ V := V.mapQ V A hV
  have hqA : q.comp A.toContinuousLinearMap = Aq.toContinuousLinearMap.comp q := by
    ext y
    change V.mkQ (A y) = Aq (V.mkQ y)
    exact (congrFun (congrArg DFunLike.coe (Submodule.mapQ_mkQ V V A (h := hV))) y).symm
  let Hbar : X ⧸ V →ₗ[ℝ] Z := Submodule.liftQ V H hVH
  have hHbar : Hbar.comp V.mkQ = H := Submodule.liftQ_mkQ V H hVH
  have hdesc : ∀ y : X, H y = Hbar (V.mkQ y) := by
    intro y
    have := congrFun (congrArg DFunLike.coe hHbar) y
    exact this.symm
  have hflow : ∀ t : ℝ, q (NormedSpace.exp (t • A.toContinuousLinearMap) x) =
      NormedSpace.exp (t • Aq.toContinuousLinearMap) (q x) := by
    intro t
    exact clm_map_exp_smul q A.toContinuousLinearMap Aq.toContinuousLinearMap hqA t x
  have hqconv : Tendsto (fun t : ℝ =>
      NormedSpace.exp (t • Aq.toContinuousLinearMap) (q x)) atTop (nhds 0) :=
    LinearMap.tendsto_exp_of_isHurwitz Aq hH (q x)
  have hHcont : Continuous (Hbar.toContinuousLinearMap) :=
    Hbar.toContinuousLinearMap.continuous
  have hcomp := hHcont.tendsto 0 |>.comp hqconv
  rw [map_zero] at hcomp
  refine hcomp.congr' (Filter.Eventually.of_forall fun t => ?_)
  simp only [Function.comp_apply]
  rw [hdesc (NormedSpace.exp (t • A.toContinuousLinearMap) x), ← hflow t]
  rfl

variable {U D : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- **State-feedback external stabilization.** Let `F` be a state-feedback gain
for which the closed loop preserves an invariant subspace `W` containing the
disturbance image `im E`, and let `V ≤ W` be a closed-loop-invariant subspace
with `V ≤ ker H`. If the map induced by `A + B F` on the quotient `W / V` is
Hurwitz, then the closed-loop controlled output of every disturbance direction
decays: `t ↦ H (exp (t • (A + B F)) (E d))` tends to `0` at `+∞`.

This is the state-feedback form of Lemma 4.35 (the sufficiency step of
Theorem 4.39): the disturbance enters through `im E ≤ W`, `W` is closed-loop
invariant, the readout vanishes on `V`, and only the quotient `W / V` carries the
spectral stability hypothesis. The construction of such an `F` from the
geometric condition `im E ≤ V*(ker H) + Xstab` (Lemma 4.38) is the remaining
source obligation and is not assumed here. -/
theorem tendsto_readout_exp_of_isHurwitz_quotient_on
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) (E : D →ₗ[ℝ] X)
    (V W : Submodule ℝ X) (F : X →ₗ[ℝ] U)
    (hW : Submodule.map (A + B.comp F) W ≤ W)
    (hV : Submodule.map (A + B.comp F) V ≤ V)
    (hVH : V ≤ LinearMap.ker H)
    (hE : LinearMap.range E ≤ W)
    (hQ : LinearMap.IsHurwitz
      (Submodule.mapQ (V.comap W.subtype) (V.comap W.subtype)
        ((A + B.comp F).restrict (fun x hx => hW ⟨x, hx, rfl⟩))
        (fun x hx => by simpa using hV ⟨(x : X), hx, rfl⟩)))
    (d : D) :
    Tendsto (fun t : ℝ => H (NormedSpace.exp
      (t • (A + B.comp F).toContinuousLinearMap) (E d))) atTop (nhds 0) := by
  let VW : Submodule ℝ W := V.comap W.subtype
  let AW : W →ₗ[ℝ] W := (A + B.comp F).restrict (fun x hx => hW ⟨x, hx, rfl⟩)
  let HW : W →ₗ[ℝ] Z := H.comp W.subtype
  have hVW' : VW ≤ VW.comap AW := by
    intro x hx
    change (A + B.comp F) (x : X) ∈ V
    exact hV ⟨(x : X), hx, rfl⟩
  have hVWH : VW ≤ LinearMap.ker HW := by
    intro x hx
    exact hVH hx
  have hxW : E d ∈ W := hE ⟨d, rfl⟩
  letI : IsTopologicalRing (W →L[ℝ] W) :=
    { continuous_add := continuous_add
      continuous_mul := Continuous.clm_comp continuous_fst continuous_snd
      continuous_neg := continuous_neg }
  have hmain := tendsto_readout_exp_of_isHurwitz_mapQ AW HW VW hVW' hVWH hQ ⟨E d, hxW⟩
  have hsub : W.subtype.toContinuousLinearMap.comp AW.toContinuousLinearMap =
      (A + B.comp F).toContinuousLinearMap.comp W.subtype.toContinuousLinearMap := by
    ext x
    rfl
  have hflow : ∀ t : ℝ,
      W.subtype.toContinuousLinearMap
        (NormedSpace.exp (t • AW.toContinuousLinearMap) ⟨E d, hxW⟩) =
      NormedSpace.exp (t • (A + B.comp F).toContinuousLinearMap) (E d) := by
    intro t
    have := clm_map_exp_smul W.subtype.toContinuousLinearMap AW.toContinuousLinearMap
      (A + B.comp F).toContinuousLinearMap hsub t ⟨E d, hxW⟩
    simpa using this
  have hgoal : (fun t : ℝ => H (NormedSpace.exp
        (t • (A + B.comp F).toContinuousLinearMap) (E d))) =
      fun t : ℝ => HW (NormedSpace.exp (t • AW.toContinuousLinearMap) ⟨E d, hxW⟩) := by
    funext t
    rw [← hflow t]
    rfl
  rw [hgoal]
  exact hmain

end TrajectorySpectralBridge

/-! ## The geometric feedback construction: reduction lemmas

Trentelman–Stoorvogel–Hautus, Lemma 4.38 constructs a state feedback `F` from
the geometric condition `im E ≤ W_g(ker H) = V*(ker H) + Xstab(A, B)` of
Theorem 4.37, preserving the controlled-invariant witness `V*` and making the
induced quotient map on `W_g / V*` Hurwitz. Theorem 4.39 then derives external
stability of the closed-loop transfer function through the analytic Lemma 4.35,
already formalised as
`tendsto_readout_exp_of_isHurwitz_quotient_on`.

The construction of `F` (the genuinely missing step) is not formalised here.
What *is* formalised in this section are the two structural facts about the
geometric subspace `W = V*(ker H) ⊔ Xstab(A, B)` on which Lemma 4.38 and
Lemma 4.35 operate:

* `range_le_sup_stabilizableSubspace`: the input image `im B` lies in `W`, so
  `W` is a strongly invariant subspace once it is invariant;
* `map_sup_stabilizableSubspace_le`: `W` is `A`-invariant, and
  `map_add_feedback_sup_stabilizableSubspace_le`: any feedback that preserves the
  controlled-invariant witness `V` also preserves `W`.

These lemmas supply `hW` and `range E ≤ W` for the accepted quotient-decay
bridge once an `F` with `(A + B F) V ≤ V` and `W/V` Hurwitz is available; the
construction of that `F` from the geometric inclusion is recorded as the handoff
item (see the module note above and `gaps.json`). -/

section GeometricFeedbackConstruction

variable {X U Z D : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- **The input image lies in the geometric external-stability subspace.** For
any candidate controlled-invariant subspace `V`, the image of the input map `B`
is contained in `V ⊔ Xstab(A, B)`, because it is contained in the reachable
subspace and the reachable subspace is contained in the stabilizable subspace.
This is the `im B ⊂ W_g` remark following Trentelman–Stoorvogel–Hautus
Theorem 4.37. -/
theorem range_le_sup_stabilizableSubspace (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (V : Submodule ℝ X) :
    LinearMap.range B ≤ V ⊔ LinearMap.stabilizableSubspace A B :=
  le_trans (LinearMap.range_le_reachableSubspace A B)
    (le_trans (LinearMap.reachableSubspace_le_stabilizableSubspace A B) le_sup_right)

/-- **The geometric external-stability subspace is `A`-invariant.** If `V` is
controlled invariant for `(A, B)` then `W = V ⊔ Xstab(A, B)` satisfies
`A W ⊆ W`: the `V` part maps into `V ⊔ im B ⊆ W` by controlled invariance, the
stabilizable summand maps into itself, and `im B ⊆ W` by
`range_le_sup_stabilizableSubspace`.

This is the `AW_g + im B ⊂ W_g` structural remark following
Trentelman–Stoorvogel–Hautus Theorem 4.37. -/
theorem map_sup_stabilizableSubspace_le (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    {V : Submodule ℝ X} (hV : Submodule.map A V ≤ V ⊔ LinearMap.range B) :
    Submodule.map A (V ⊔ LinearMap.stabilizableSubspace A B) ≤
      V ⊔ LinearMap.stabilizableSubspace A B := by
  rw [Submodule.map_sup]
  refine sup_le ?_ ?_
  · refine le_trans hV (sup_le_sup_left ?_ V)
    exact le_trans (LinearMap.range_le_reachableSubspace A B)
      (LinearMap.reachableSubspace_le_stabilizableSubspace A B)
  · exact le_trans (LinearMap.map_stabilizableSubspace_le A B) le_sup_right

/-- **The stabilizable subspace is preserved by every state feedback.** For any
`F`, the map `A + B F` sends `Xstab(A, B)` into itself: the `A` part preserves it
and the `B F` part lands in `im B ⊆ Xstab(A, B)`. -/
theorem map_add_feedback_stabilizableSubspace_le (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (F : X →ₗ[ℝ] U) :
    Submodule.map (A + B.comp F) (LinearMap.stabilizableSubspace A B) ≤
      LinearMap.stabilizableSubspace A B := by
  rintro y ⟨x, hx, rfl⟩
  simp only [LinearMap.add_apply, LinearMap.comp_apply]
  exact (LinearMap.stabilizableSubspace A B).add_mem
    (LinearMap.map_stabilizableSubspace_le A B ⟨x, hx, rfl⟩)
    (le_trans (LinearMap.range_le_reachableSubspace A B)
      (LinearMap.reachableSubspace_le_stabilizableSubspace A B) ⟨F x, rfl⟩)

/-- **Every feedback preserving the controlled-invariant witness preserves the
geometric external-stability subspace.** If `(A + B F) V ⊆ V` then
`(A + B F) W ⊆ W` for `W = V ⊔ Xstab(A, B)`.

This supplies the `hW` hypothesis of the accepted quotient-decay bridge
`tendsto_readout_exp_of_isHurwitz_quotient_on` from the feedback-preservation
`(A + B F) V ≤ V` alone. -/
theorem map_add_feedback_sup_stabilizableSubspace_le (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    {V : Submodule ℝ X} (F : X →ₗ[ℝ] U)
    (hFV : Submodule.map (A + B.comp F) V ≤ V) :
    Submodule.map (A + B.comp F) (V ⊔ LinearMap.stabilizableSubspace A B) ≤
      V ⊔ LinearMap.stabilizableSubspace A B := by
  rw [Submodule.map_sup]
  exact sup_le (le_trans hFV le_sup_left)
    (le_trans (map_add_feedback_stabilizableSubspace_le A B F) le_sup_right)

open scoped TensorProduct in
/-- **An uncontrollable eigenvalue annihilated by a controlled-invariant
subspace is stable.** Let `AW` act on a finite-dimensional real space `W`, let
`VW ⊔ Xstab(AW, BW) = ⊤`, and let `η` be a nonzero complex left eigenvector of
`AW` with eigenvalue `μ` that annihilates `range BW` and the subspace `VW`.
Then `μ.re < 0`.

Equivalently: the only possibly-unstable uncontrollable directions of `(AW, BW)`
lie in `VW`, so a left eigenvector that vanishes on `VW` (as produced by
descending to `W / VW`) cannot be unstable. The proof evaluates `η` on the
real generators `w ↦ 1 ⊗ w`, shows its kernel `L` contains `VW` and the
reachable subspace, decomposes a vector on which `η` is nonzero along
`W = VW + X_g(AW) + ⟨AW | im BW⟩`, restricts the eigenvector to the Hurwitz
subspace `X_g(AW)`, and concludes from the accepted
`isStabilizable_converse_of_uncontrollableEigenvalue` applied to the Hurwitz
restriction.

This isolates the spectral heart of Trentelman–Stoorvogel–Hautus Lemma 4.38
(the uncontrollable part of `W_g / V*` is a quotient of the stable subspace). -/
theorem isUncontrollableEigenvalue_stable_of_sup_stabilizableSubspace
    {W U' : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup U'] [NormedSpace ℝ U']
    (AW : W →ₗ[ℝ] W) (BW : U' →ₗ[ℝ] W) (VW : Submodule ℝ W)
    (hVW : VW ⊔ LinearMap.stabilizableSubspace AW BW = ⊤)
    (η : (ℂ ⊗[ℝ] W) →ₗ[ℂ] ℂ) (μ : ℂ) (hη : η ≠ 0)
    (hAη : η.comp (AW.baseChange ℂ) = μ • η)
    (hBη : η.comp (BW.baseChange ℂ) = 0)
    (hVη : ∀ x : VW, η ((1 : ℂ) ⊗ₜ[ℝ] (x : W)) = 0) :
    μ.re < 0 := by
  let evalη : W →ₗ[ℝ] ℂ := (η.restrictScalars ℝ).comp (TensorProduct.mk ℝ ℂ W 1)
  let L : Submodule ℝ W := LinearMap.ker evalη
  have hB_L : LinearMap.range BW ≤ L := by
    rintro y ⟨u, rfl⟩
    change evalη (BW u) = 0
    change η ((1 : ℂ) ⊗ₜ[ℝ] (BW u)) = 0
    rw [show (1 : ℂ) ⊗ₜ[ℝ] (BW u) = BW.baseChange ℂ ((1 : ℂ) ⊗ₜ[ℝ] u) from
      (LinearMap.baseChange_tmul (A := ℂ) (f := BW) (1 : ℂ) u).symm]
    have h := congrFun (congrArg DFunLike.coe hBη) ((1 : ℂ) ⊗ₜ[ℝ] u)
    simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using h
  have hA_L : Submodule.map AW L ≤ L := by
    rintro y ⟨x, hx, rfl⟩
    change evalη (AW x) = 0
    change η ((1 : ℂ) ⊗ₜ[ℝ] (AW x)) = 0
    rw [show (1 : ℂ) ⊗ₜ[ℝ] (AW x) = AW.baseChange ℂ ((1 : ℂ) ⊗ₜ[ℝ] x) from
      (LinearMap.baseChange_tmul (A := ℂ) (f := AW) (1 : ℂ) x).symm]
    have hx' : η ((1 : ℂ) ⊗ₜ[ℝ] x) = 0 := hx
    have h := congrFun (congrArg DFunLike.coe hAη) ((1 : ℂ) ⊗ₜ[ℝ] x)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at h
    rw [h, hx', mul_zero]
  have hR_L : LinearMap.reachableSubspace AW BW ≤ L :=
    LinearMap.reachableSubspace_le AW BW hB_L hA_L
  have hV_L : VW ≤ L := by
    intro x hx
    change evalη x = 0
    change η ((1 : ℂ) ⊗ₜ[ℝ] x) = 0
    simpa using hVη ⟨x, hx⟩
  have hsup : VW ⊔ LinearMap.hurwitzSubspace AW ⊔ LinearMap.reachableSubspace AW BW = ⊤ := by
    rw [← hVW, LinearMap.stabilizableSubspace, sup_assoc]
  have hex : ∃ w : W, evalη w ≠ 0 := by
    by_contra h
    push Not at h
    apply hη
    refine LinearMap.ext fun z => ?_
    change η z = 0
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c w =>
        have hcw : c ⊗ₜ[ℝ] w = c • ((1 : ℂ) ⊗ₜ[ℝ] w) := by
          rw [TensorProduct.smul_tmul']
          simp
        have hw' : η ((1 : ℂ) ⊗ₜ[ℝ] w) = 0 := h w
        rw [hcw, map_smul, hw', smul_zero]
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
  obtain ⟨w, hw⟩ := hex
  have hwmem : w ∈ VW ⊔ LinearMap.hurwitzSubspace AW ⊔
      LinearMap.reachableSubspace AW BW := by rw [hsup]; trivial
  obtain ⟨a, ha, r, hr, rfl⟩ := Submodule.mem_sup.mp hwmem
  obtain ⟨v, hv, h, hh, rfl⟩ := Submodule.mem_sup.mp ha
  have hr0 : evalη r = 0 := hR_L hr
  have hv0 : evalη v = 0 := hV_L hv
  have hh0 : evalη h ≠ 0 := by
    have hsum : evalη (v + h + r) = evalη h := by
      rw [map_add, map_add, hv0, hr0, zero_add, add_zero]
    rwa [hsum] at hw
  let H : Submodule ℝ W := LinearMap.hurwitzSubspace AW
  have hHinv : ∀ x ∈ H, AW x ∈ H := fun x hx =>
    LinearMap.map_hurwitzSubspace_le AW ⟨x, hx, rfl⟩
  let TH : H →ₗ[ℝ] H := AW.restrict hHinv
  have hUH : LinearMap.unstableSubspace TH = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx' : (H.subtype x : W) ∈ LinearMap.unstableSubspace AW :=
      LinearMap.map_unstableSubspace_restrict_le AW H hHinv ⟨x, hx, rfl⟩
    have hxinf : (H.subtype x : W) ∈ H ⊓ LinearMap.unstableSubspace AW := ⟨x.2, hx'⟩
    have hdisj := disjoint_iff.mp (LinearMap.disjoint_hurwitzSubspace_unstableSubspace AW)
    rw [hdisj, Submodule.mem_bot] at hxinf
    exact Subtype.ext hxinf
  have hTH : LinearMap.IsHurwitz TH := LinearMap.isHurwitz_of_unstableSubspace_eq_bot TH hUH
  have hsub : H.subtype.comp TH = AW.comp H.subtype := by
    ext x
    rfl
  have hcomp : (η.comp (H.subtype.baseChange ℂ)).comp (TH.baseChange ℂ) =
      μ • (η.comp (H.subtype.baseChange ℂ)) := by
    have hbc := congrArg (fun f => f.baseChange ℂ) hsub
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at hbc
    calc (η.comp (H.subtype.baseChange ℂ)).comp (TH.baseChange ℂ)
        = η.comp ((H.subtype.baseChange ℂ).comp (TH.baseChange ℂ)) := by
          rw [LinearMap.comp_assoc]
      _ = η.comp ((AW.baseChange ℂ).comp (H.subtype.baseChange ℂ)) := by rw [hbc]
      _ = (η.comp (AW.baseChange ℂ)).comp (H.subtype.baseChange ℂ) := by
          rw [LinearMap.comp_assoc]
      _ = (μ • η).comp (H.subtype.baseChange ℂ) := by rw [hAη]
      _ = μ • (η.comp (H.subtype.baseChange ℂ)) := by rw [LinearMap.smul_comp]
  have hηH : η.comp (H.subtype.baseChange ℂ) ≠ 0 := by
    intro hzero
    apply hh0
    have h := congrFun (congrArg DFunLike.coe hzero) ((1 : ℂ) ⊗ₜ[ℝ] ⟨h, hh⟩)
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
    rw [LinearMap.baseChange_tmul] at h
    simpa [evalη] using h
  have hunit : LinearMap.IsUncontrollableEigenvalue TH (0 : U' →ₗ[ℝ] H) μ :=
    ⟨η.comp (H.subtype.baseChange ℂ), hηH, hcomp, by simp⟩
  have hstab : LinearMap.IsStabilizable TH (0 : U' →ₗ[ℝ] H) :=
    LinearMap.isStabilizable_of_isHurwitz TH (0 : U' →ₗ[ℝ] H) hTH
  exact LinearMap.isStabilizable_converse_of_uncontrollableEigenvalue TH
    (0 : U' →ₗ[ℝ] H) hstab hunit

/-- **External-response decay from a quotient-Hurwitz feedback preserving the
controlled-invariant witness.** Let `V` be a controlled-invariant subspace
contained in `ker H`, let `W = V ⊔ Xstab(A, B)` be the geometric
external-stability subspace, and let `F` be a gain with `(A + B F) V ≤ V` and
with the induced map on `W/V` Hurwitz. Then the closed-loop controlled output of
every disturbance direction in `im E ≤ W` decays to zero,
`t ↦ H (exp (t (A + B F)) (E d)) → 0`.

This is exactly the state-feedback sufficiency step of
Trentelman–Stoorvogel–Hautus Theorem 4.39: `(A + B F) W ≤ W` is supplied by
`map_add_feedback_sup_stabilizableSubspace_le`, and the accepted quotient-decay
bridge `tendsto_readout_exp_of_isHurwitz_quotient_on` finishes the argument.

The *construction* of the gain `F` from the geometric inclusion
`im E ≤ V ⊔ Xstab(A, B)` (Lemma 4.38) is the hypothesis `hQ` and is not
produced here; see the module handoff. -/
theorem tendsto_readout_exp_of_geometricCondition
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) (E : D →ₗ[ℝ] X)
    (V : Submodule ℝ X) (F : X →ₗ[ℝ] U)
    (hFV : Submodule.map (A + B.comp F) V ≤ V)
    (hVH : V ≤ LinearMap.ker H)
    (hE : LinearMap.range E ≤ V ⊔ LinearMap.stabilizableSubspace A B)
    (hQ : LinearMap.IsHurwitz
      (Submodule.mapQ (V.comap (V ⊔ LinearMap.stabilizableSubspace A B).subtype)
        (V.comap (V ⊔ LinearMap.stabilizableSubspace A B).subtype)
        ((A + B.comp F).restrict (fun x hx =>
          map_add_feedback_sup_stabilizableSubspace_le A B F hFV ⟨x, hx, rfl⟩))
        (fun x hx => by
          simpa using hFV ⟨(x : X), hx, rfl⟩)))
    (d : D) :
    Tendsto (fun t : ℝ => H (NormedSpace.exp
      (t • (A + B.comp F).toContinuousLinearMap) (E d))) atTop (nhds 0) :=
  tendsto_readout_exp_of_isHurwitz_quotient_on A B H E V
    (V ⊔ LinearMap.stabilizableSubspace A B) F
    (map_add_feedback_sup_stabilizableSubspace_le A B F hFV) hFV hVH hE hQ d

/-! ## The isolated quotient-feedback lift

This section closes the blocker left by the previous attempt: the subspace
transport identity for the stabilizable subspace, the reachable/stable transport
lemmas it rests on, and the `baseChange`/`mkQ` eigenvector lift that turns an
uncontrollable eigenvalue of the quotient pair `(A|_W / V, B|_W)` into an
uncontrollable eigenvalue of `(A|_W, B|_W)` annihilating `V`. Together with the
accepted PBH lemma `isUncontrollableEigenvalue_stable_of_sup_stabilizableSubspace`
this yields the quotient stabilizing feedback of Trentelman–Stoorvogel–Hautus
Lemma 4.38. -/

section QuotientFeedbackLift

open scoped TensorProduct

omit [FiniteDimensional ℝ X] in
/-- **Reachable transport.** If `W` is `A`-invariant and contains `im B`, the
reachable subspace of the restricted pair `(A|_W, B|_W)`, pushed forward along
`W ↪ X`, is exactly the reachable subspace of `(A, B)`. -/
theorem map_reachableSubspace_restrict_eq (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (W : Submodule ℝ X) (hW : ∀ x ∈ W, A x ∈ W) (hB : LinearMap.range B ≤ W) :
    Submodule.map W.subtype
        (LinearMap.reachableSubspace (A.restrict hW)
          (B.codRestrict W (fun u => hB (LinearMap.mem_range_self B u)))) =
      LinearMap.reachableSubspace A B := by
  apply le_antisymm
  · rw [Submodule.map_le_iff_le_comap]
    apply LinearMap.reachableSubspace_le
    · intro y hy
      obtain ⟨u, rfl⟩ := hy
      exact LinearMap.range_le_reachableSubspace A B ⟨u, rfl⟩
    · rintro y ⟨x, hx, rfl⟩
      exact Submodule.mem_comap.mpr (LinearMap.map_reachableSubspace_le A B
        ⟨(x : X), Submodule.mem_comap.mp hx, rfl⟩)
  · apply LinearMap.reachableSubspace_le
    · rintro u ⟨v, rfl⟩
      exact ⟨(B.codRestrict W (fun u => hB (LinearMap.mem_range_self B u))) v,
        LinearMap.range_le_reachableSubspace _ _ (LinearMap.mem_range_self _ v), rfl⟩
    · rintro y ⟨x, hx, rfl⟩
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hx
      exact ⟨(A.restrict hW) w,
        LinearMap.map_reachableSubspace_le _ _ ⟨w, hw, rfl⟩, rfl⟩

/-- **Reverse stable transport.** The `A`-stable part of an `A`-invariant
subspace `W` is stable for the restriction `A|_W`. The proof decomposes a vector
of `W` along the stable/antistable splitting of `A|_W`, transports its antistable
part forward to `X` (`map_unstableSubspace_restrict_le`) and uses disjointness of
the stable and antistable spectral subspaces of `A`. -/
theorem hurwitzSubspace_inf_le_map_hurwitzSubspace_restrict
    (A : X →ₗ[ℝ] X) (W : Submodule ℝ X) (hW : ∀ x ∈ W, A x ∈ W) :
    LinearMap.hurwitzSubspace A ⊓ W ≤
      Submodule.map W.subtype (LinearMap.hurwitzSubspace (A.restrict hW)) := by
  intro x hx
  obtain ⟨hxA, hxW⟩ := hx
  let xW : W := ⟨x, hxW⟩
  have hsup := LinearMap.hurwitzSubspace_sup_unstableSubspace_eq_top (A.restrict hW)
  have hxmem : xW ∈ LinearMap.hurwitzSubspace (A.restrict hW) ⊔
      LinearMap.unstableSubspace (A.restrict hW) := by
    rw [hsup]; trivial
  obtain ⟨g, hg, b, hb, hgb⟩ := Submodule.mem_sup.mp hxmem
  refine ⟨g, hg, ?_⟩
  have hgX : (g : X) ∈ LinearMap.hurwitzSubspace A :=
    LinearMap.map_hurwitzSubspace_restrict_le A W hW ⟨g, hg, rfl⟩
  have hbX : (b : X) ∈ LinearMap.unstableSubspace A :=
    LinearMap.map_unstableSubspace_restrict_le A W hW ⟨b, hb, rfl⟩
  have hb_eq : (b : X) = x - (g : X) := by
    have h := congrArg (Subtype.val) hgb
    simp only [Submodule.coe_add] at h
    rw [eq_sub_iff_add_eq, add_comm]
    exact h
  have hbH : (b : X) ∈ LinearMap.hurwitzSubspace A := by
    rw [hb_eq]
    exact Submodule.sub_mem _ hxA hgX
  have hb0 : (b : X) = 0 := by
    have hmem : (b : X) ∈ LinearMap.hurwitzSubspace A ⊓ LinearMap.unstableSubspace A :=
      ⟨hbH, hbX⟩
    rw [disjoint_iff.mp (LinearMap.disjoint_hurwitzSubspace_unstableSubspace A),
      Submodule.mem_bot] at hmem
    exact hmem
  have hgx : (g : X) = x := by
    have h := congrArg (Subtype.val) hgb
    simp only [Submodule.coe_add] at h
    rw [hb0, add_zero] at h
    exact h
  exact hgx

/-- **Reverse stable transport, comap form.** A vector of `W` whose image in `X`
lies in the stable subspace of `A` lies in the stable subspace of `A|_W`. -/
theorem comap_hurwitzSubspace_le_hurwitzSubspace_restrict
    (A : X →ₗ[ℝ] X) (W : Submodule ℝ X) (hW : ∀ x ∈ W, A x ∈ W) :
    (LinearMap.hurwitzSubspace A).comap W.subtype ≤
      LinearMap.hurwitzSubspace (A.restrict hW) := by
  intro x hx
  rw [Submodule.mem_comap] at hx
  obtain ⟨g, hg, hgx⟩ : ∃ g ∈ LinearMap.hurwitzSubspace (A.restrict hW),
      (g : X) = (x : X) :=
    hurwitzSubspace_inf_le_map_hurwitzSubspace_restrict A W hW ⟨hx, x.2⟩
  rw [← Subtype.ext hgx]
  exact hg

omit [FiniteDimensional ℝ X] in
/-- **Reverse reachable transport, comap form.** -/
theorem comap_reachableSubspace_le_reachableSubspace_restrict
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (W : Submodule ℝ X) (hW : ∀ x ∈ W, A x ∈ W) (hB : LinearMap.range B ≤ W) :
    (LinearMap.reachableSubspace A B).comap W.subtype ≤
      LinearMap.reachableSubspace (A.restrict hW)
        (B.codRestrict W (fun u => hB (LinearMap.mem_range_self B u))) := by
  intro x hx
  rw [Submodule.mem_comap] at hx
  rw [← map_reachableSubspace_restrict_eq A B W hW hB] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  rw [show y = x from Subtype.ext hyx] at hy
  exact hy

/-- **Stabilizable-subspace transport.** For an `A`-invariant subspace `W`
containing `im B`, the stabilizable subspace of the restricted pair `(A|_W, B|_W)`
is exactly the trace of the ambient stabilizable subspace:
`Xstab(A|_W, B|_W) = W ∩ Xstab(A, B)`.

Trentelman–Stoorvogel–Hautus, Lemma 4.38, uses this as "the stabilizable
subspace of `(A₀, B)` is equal to `Xstab`". -/
theorem stabilizableSubspace_restrict_eq (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (W : Submodule ℝ X) (hW : ∀ x ∈ W, A x ∈ W) (hB : LinearMap.range B ≤ W) :
    LinearMap.stabilizableSubspace (A.restrict hW)
        (B.codRestrict W (fun u => hB (LinearMap.mem_range_self B u))) =
      (LinearMap.stabilizableSubspace A B).comap W.subtype := by
  apply le_antisymm
  · intro x hx
    rw [LinearMap.stabilizableSubspace, Submodule.mem_sup] at hx
    obtain ⟨h, hh, r, hr, hhr⟩ := hx
    rw [Submodule.mem_comap, LinearMap.stabilizableSubspace, Submodule.mem_sup]
    refine ⟨(h : X), LinearMap.map_hurwitzSubspace_restrict_le A W hW ⟨h, hh, rfl⟩,
      (r : X), ?_, ?_⟩
    · rw [← map_reachableSubspace_restrict_eq A B W hW hB]
      exact ⟨r, hr, rfl⟩
    · exact congrArg (Subtype.val) hhr
  · intro x hx
    rw [Submodule.mem_comap, LinearMap.stabilizableSubspace, Submodule.mem_sup] at hx
    obtain ⟨h, hh, r, hr, hhr⟩ := hx
    have hRW : LinearMap.reachableSubspace A B ≤ W :=
      LinearMap.reachableSubspace_le A B hB (by
        rintro y ⟨w, hw, rfl⟩; exact hW w hw)
    have hrW : r ∈ W := hRW hr
    have hhW : h ∈ W := by
      have heq : h = (x : X) - r := eq_sub_iff_add_eq.mpr hhr
      rw [heq]
      exact W.sub_mem x.2 hrW
    have hr' : (⟨r, hrW⟩ : W) ∈ LinearMap.reachableSubspace (A.restrict hW)
        (B.codRestrict W (fun u => hB (LinearMap.mem_range_self B u))) :=
      comap_reachableSubspace_le_reachableSubspace_restrict A B W hW hB
        (by rw [Submodule.mem_comap]; exact hr)
    have hh' : (⟨h, hhW⟩ : W) ∈ LinearMap.hurwitzSubspace (A.restrict hW) :=
      comap_hurwitzSubspace_le_hurwitzSubspace_restrict A W hW
        (by rw [Submodule.mem_comap]; exact hh)
    rw [LinearMap.stabilizableSubspace, Submodule.mem_sup]
    refine ⟨⟨h, hhW⟩, hh', ⟨r, hrW⟩, hr', ?_⟩
    apply Subtype.ext
    rw [Submodule.coe_add]; exact hhr

/-- **Stabilizability is invariant under state feedback.** Replacing `A` by
`A + B.comp F` does not change whether the pair admits a stabilizing feedback:
the gains shift by `F`, and `B.comp` is additive in the gain. -/
theorem isStabilizable_add_comp (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (F : X →ₗ[ℝ] U) :
    LinearMap.IsStabilizable (A + B.comp F) B ↔ LinearMap.IsStabilizable A B := by
  constructor
  · rintro ⟨G, hG⟩
    refine ⟨F + G, ?_⟩
    have h : A + B.comp (F + G) = (A + B.comp F) + B.comp G := by
      rw [LinearMap.comp_add]; abel
    rwa [h]
  · rintro ⟨G, hG⟩
    refine ⟨G - F, ?_⟩
    have h : (A + B.comp F) + B.comp (G - F) = A + B.comp G := by
      rw [LinearMap.comp_sub]; abel
    rwa [h]

/-- **The stabilizable subspace grows under state feedback.** Replacing `A` by
`A + B.comp F` can only enlarge `Xstab`: every state that can be asymptotically
driven to the origin using `(A, B)` can also be driven there using
`(A + B F, B)` with the adjusted input, so
`Xstab(A, B) ≤ Xstab(A + B F, B)`.

The proof avoids the trajectory characterisation. It shows that
`S = Xstab(A, B)` is stabilizable as a pair in its own right: restricting to `S`,
the stabilizable-subspace transport identity gives
`Xstab(A|_S, B|_S) = S ∩ Xstab(A, B) = S`, so `(A|_S, B|_S)` is stabilizable and,
by feedback invariance `isStabilizable_add_comp`, so is `(M|_S, B|_S)` for
`M = A + B F`. Applying the transport identity to `M` then gives
`S ∩ Xstab(M, B) = S`, i.e. `S ≤ Xstab(M, B)`. -/
theorem stabilizableSubspace_le_add_feedback (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (F : X →ₗ[ℝ] U) :
    LinearMap.stabilizableSubspace A B ≤
      LinearMap.stabilizableSubspace (A + B.comp F) B := by
  let S : Submodule ℝ X := LinearMap.stabilizableSubspace A B
  have hAinv : ∀ x ∈ S, A x ∈ S := fun x hx =>
    LinearMap.map_stabilizableSubspace_le A B ⟨x, hx, rfl⟩
  have hBle : LinearMap.range B ≤ S :=
    le_trans (LinearMap.range_le_reachableSubspace A B)
      (LinearMap.reachableSubspace_le_stabilizableSubspace A B)
  have hA_stab : LinearMap.IsStabilizable (A.restrict hAinv)
      (B.codRestrict S (fun u => hBle (LinearMap.mem_range_self B u))) := by
    apply LinearMap.isStabilizable_of_stabilizableSubspace_eq_top
    rw [stabilizableSubspace_restrict_eq A B S hAinv hBle]
    apply le_antisymm le_top
    intro x _
    rw [Submodule.mem_comap]
    exact x.2
  have hMinv : ∀ x ∈ S, (A + B.comp F) x ∈ S := by
    intro x hx
    simp only [LinearMap.add_apply, LinearMap.comp_apply]
    exact S.add_mem (hAinv x hx) (hBle (LinearMap.mem_range_self B (F x)))
  have hM_stab : LinearMap.IsStabilizable ((A + B.comp F).restrict hMinv)
      (B.codRestrict S (fun u => hBle (LinearMap.mem_range_self B u))) := by
    have hsplit : (A + B.comp F).restrict hMinv =
        (A.restrict hAinv) +
          (B.codRestrict S (fun u => hBle (LinearMap.mem_range_self B u))).comp
            (F.comp S.subtype) := by
      apply LinearMap.ext
      intro x
      exact Subtype.ext rfl
    rw [hsplit]
    exact (isStabilizable_add_comp (A.restrict hAinv)
      (B.codRestrict S (fun u => hBle (LinearMap.mem_range_self B u)))
      (F.comp S.subtype)).mpr hA_stab
  have htop : LinearMap.stabilizableSubspace ((A + B.comp F).restrict hMinv)
      (B.codRestrict S (fun u => hBle (LinearMap.mem_range_self B u))) = ⊤ :=
    LinearMap.stabilizableSubspace_eq_top_of_isStabilizable _ _ hM_stab
  rw [stabilizableSubspace_restrict_eq (A + B.comp F) B S hMinv hBle] at htop
  intro x hx
  have hx' : (⟨x, hx⟩ : S) ∈
      (LinearMap.stabilizableSubspace (A + B.comp F) B).comap S.subtype := by
    rw [htop]; exact Submodule.mem_top
  exact hx'

/-- **The quotient eigenvector lift.** Let `η` be a nonzero complex linear
functional on `ℂ ⊗ (W ⧸ V)` whose pullback along `mkQ.baseChange` is a left
eigenvector of `A|_W` at `μ` and which annihilates `B`, and suppose
`V ⊔ Xstab(A|_W, B|_W) = ⊤`. Then `μ` is stable. This is the `baseChange`/`mkQ`
functoriality step: pulling back along the (surjective) base change of the
quotient map preserves the eigenvector equation, annihilates `B`, and vanishes
on `V`, so the accepted PBH lemma
`isUncontrollableEigenvalue_stable_of_sup_stabilizableSubspace` applies. -/
theorem isUncontrollableEigenvalue_stable_of_quotient
    {W U' : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup U'] [NormedSpace ℝ U']
    (AW : W →ₗ[ℝ] W) (BW : U' →ₗ[ℝ] W) (VW : Submodule ℝ W)
    (hVW : VW ⊔ LinearMap.stabilizableSubspace AW BW = ⊤)
    (μ : ℂ) (η : (ℂ ⊗[ℝ] (W ⧸ VW)) →ₗ[ℂ] ℂ) (hη : η ≠ 0)
    (hBη : η.comp ((VW.mkQ.comp BW).baseChange ℂ) = 0)
    (hAη : (η.comp (VW.mkQ.baseChange ℂ)).comp (AW.baseChange ℂ) =
      μ • (η.comp (VW.mkQ.baseChange ℂ))) :
    μ.re < 0 := by
  let ηt : (ℂ ⊗[ℝ] W) →ₗ[ℂ] ℂ := η.comp (VW.mkQ.baseChange ℂ)
  have hsurj : Function.Surjective (VW.mkQ.baseChange ℂ) :=
    LinearMap.baseChange_surjective ℂ (Submodule.mkQ_surjective VW)
  have hηne : ηt ≠ 0 := by
    intro h0
    apply hη
    apply LinearMap.ext
    intro y
    obtain ⟨z, rfl⟩ := hsurj y
    have hz := congrArg (fun f : (ℂ ⊗[ℝ] W) →ₗ[ℂ] ℂ => f z) h0
    simpa [ηt, LinearMap.comp_apply] using hz
  have hηA : ηt.comp (AW.baseChange ℂ) = μ • ηt :=
    hAη
  have hηB : ηt.comp (BW.baseChange ℂ) = 0 := by
    have hbc : (VW.mkQ.comp BW).baseChange ℂ =
        (VW.mkQ.baseChange ℂ).comp (BW.baseChange ℂ) :=
      LinearMap.baseChange_comp BW VW.mkQ
    calc ηt.comp (BW.baseChange ℂ)
        = η.comp ((VW.mkQ.baseChange ℂ).comp (BW.baseChange ℂ)) := by
          rw [← LinearMap.comp_assoc]
      _ = η.comp ((VW.mkQ.comp BW).baseChange ℂ) := by rw [hbc]
      _ = 0 := hBη
  have hVη : ∀ x : VW, ηt ((1 : ℂ) ⊗ₜ[ℝ] (x : W)) = 0 := by
    intro x
    have hx0 : VW.mkQ (x : W) = 0 :=
      LinearMap.mem_ker.mp (by rw [Submodule.ker_mkQ]; exact x.2)
    have h1 : (VW.mkQ.baseChange ℂ) ((1 : ℂ) ⊗ₜ[ℝ] (x : W)) = 0 := by
      simp [LinearMap.baseChange_tmul, hx0]
    change η ((VW.mkQ.baseChange ℂ) ((1 : ℂ) ⊗ₜ[ℝ] (x : W))) = 0
    rw [h1, map_zero]
  exact isUncontrollableEigenvalue_stable_of_sup_stabilizableSubspace AW BW VW
    hVW ηt μ hηne hηA hηB hVη

/-- **Quotient PBH from the eigenvector lift.** If `VW` is `AW`-invariant and
`VW ⊔ Xstab(AW, B) = ⊤`, then every uncontrollable eigenvalue of the quotient pair
is stable. This is the PBH input consumed by
`isStabilizable_of_uncontrollableEigenvalues_hurwitz`. -/
theorem isUncontrollableEigenvalue_stable_of_quotient_mapQ
    {W U' : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup U'] [NormedSpace ℝ U']
    (AW : W →ₗ[ℝ] W) (BW : U' →ₗ[ℝ] W) (VW : Submodule ℝ W)
    (hmap : ∀ v ∈ VW, AW v ∈ VW)
    (hVW : VW ⊔ LinearMap.stabilizableSubspace AW BW = ⊤)
    (μ : ℂ) (η : (ℂ ⊗[ℝ] (W ⧸ VW)) →ₗ[ℂ] ℂ) (hη : η ≠ 0)
    (hAη : η.comp ((Submodule.mapQ VW VW AW hmap).baseChange ℂ) = μ • η)
    (hBη : η.comp ((VW.mkQ.comp BW).baseChange ℂ) = 0) :
    μ.re < 0 := by
  apply isUncontrollableEigenvalue_stable_of_quotient AW BW VW hVW μ η hη hBη
  have hbc : VW.mkQ.baseChange ℂ ∘ₗ AW.baseChange ℂ =
      (Submodule.mapQ VW VW AW hmap).baseChange ℂ ∘ₗ VW.mkQ.baseChange ℂ := by
    have h := congrArg (fun f : W →ₗ[ℝ] (W ⧸ VW) => f.baseChange ℂ)
      (Submodule.mapQ_mkQ (p := VW) (q := VW) (f := AW) (h := hmap))
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at h
    exact h.symm
  calc (η.comp (VW.mkQ.baseChange ℂ)).comp (AW.baseChange ℂ)
      = η.comp ((VW.mkQ.baseChange ℂ).comp (AW.baseChange ℂ)) := by
        rw [LinearMap.comp_assoc]
    _ = η.comp ((Submodule.mapQ VW VW AW hmap).baseChange ℂ ∘ₗ VW.mkQ.baseChange ℂ) := by
        rw [hbc]
    _ = (η.comp ((Submodule.mapQ VW VW AW hmap).baseChange ℂ)).comp
          (VW.mkQ.baseChange ℂ) := by rw [← LinearMap.comp_assoc]
    _ = μ • (η.comp (VW.mkQ.baseChange ℂ)) := by rw [hAη, LinearMap.smul_comp]

/-- **The quotient stabilizing feedback exists.** If `VW` is `AW`-invariant and
`VW ⊔ Xstab(AW, B) = ⊤`, the quotient pair
`(A|_W / V, B|_W)` admits a stabilizing feedback `G : W ⧸ VW → U'`. This is the
feedback constructed in Trentelman–Stoorvogel–Hautus Lemma 4.38, before it is
lifted back to `W`. -/
theorem isStabilizable_quotient_of_sup_stabilizableSubspace
    {W U' : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup U'] [NormedSpace ℝ U']
    (AW : W →ₗ[ℝ] W) (BW : U' →ₗ[ℝ] W) (VW : Submodule ℝ W)
    (hmap : ∀ v ∈ VW, AW v ∈ VW)
    (hVW : VW ⊔ LinearMap.stabilizableSubspace AW BW = ⊤) :
    LinearMap.IsStabilizable (Submodule.mapQ VW VW AW hmap) (VW.mkQ.comp BW) := by
  apply LinearMap.isStabilizable_of_uncontrollableEigenvalues_hurwitz
  intro μ hμ
  obtain ⟨η, hη, hAη, hBη⟩ := hμ
  exact isUncontrollableEigenvalue_stable_of_quotient_mapQ AW BW VW hmap hVW μ η
    hη hAη hBη

omit [FiniteDimensional ℝ X] in
/-- Pulling back a spanning decomposition along a subspace inclusion keeps the
spanning decomposition. If `V ⊔ S = W` and both summands lie in `W`, then the
preimages of `V` and `S` in `W` span `W`. -/
theorem comap_sup_subtype_eq_top {V S W : Submodule ℝ X} (hVW : V ≤ W)
    (hSW : S ≤ W) (h : V ⊔ S = W) :
    V.comap W.subtype ⊔ S.comap W.subtype = ⊤ := by
  apply le_antisymm le_top
  intro x _
  have hx : (x : X) ∈ V ⊔ S := by rw [h]; exact x.2
  obtain ⟨v, hv, s, hs, hvs⟩ := Submodule.mem_sup.mp hx
  refine Submodule.mem_sup.mpr ⟨⟨v, hVW hv⟩, ?_, ⟨s, hSW hs⟩, ?_, ?_⟩
  · rw [Submodule.mem_comap]; exact hv
  · rw [Submodule.mem_comap]; exact hs
  · apply Subtype.ext; simpa using hvs

/-- **The external-stabilization state feedback of Trentelman–Stoorvogel–Hautus
Lemma 4.38 / Theorem 4.39.** Let `V` be a controlled-invariant subspace
contained in `ker H`, and suppose the disturbance image satisfies
`im E ≤ V + Xstab(A, B)`. Then there is a state feedback `F` that preserves `V`
and makes the closed loop externally stable, in the sense that the controlled
output of every disturbance direction decays to zero:
`t ↦ H (exp (t (A + B F)) (E d)) → 0`.

The gain is assembled from the friend gain `F₀` produced by the controlled
invariance of `V`, the quotient stabilising gain `G` of
`isStabilizable_quotient_of_sup_stabilizableSubspace` on `W / V` (where
`W = V ⊔ Xstab(A, B)`), the transport identity
`stabilizableSubspace_restrict_eq`, the feedback monotonicity
`stabilizableSubspace_le_add_feedback`, and the analytic quotient-decay bridge
`tendsto_readout_exp_of_geometricCondition`. -/
theorem exists_feedback_tendsto_readout_of_geometricCondition
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) (E : D →ₗ[ℝ] X)
    (V : Submodule ℝ X)
    (hV : Submodule.map A V ≤ V ⊔ LinearMap.range B)
    (hVH : V ≤ LinearMap.ker H)
    (hE : LinearMap.range E ≤ V ⊔ LinearMap.stabilizableSubspace A B) :
    ∃ F : X →ₗ[ℝ] U,
      Submodule.map (A + B.comp F) V ≤ V ∧
      ∀ d : D, Tendsto (fun t : ℝ => H (NormedSpace.exp
        (t • (A + B.comp F).toContinuousLinearMap) (E d))) atTop (nhds 0) := by
  classical
  obtain ⟨F₀, hF₀⟩ := LinearMap.exists_stateFeedback_of_isControlledInvariant hV
  let W : Submodule ℝ X := V ⊔ LinearMap.stabilizableSubspace A B
  have hWle : V ≤ W := le_sup_left
  have hBleW : LinearMap.range B ≤ W := range_le_sup_stabilizableSubspace A B V
  have hWinv : ∀ x ∈ W, (A + B.comp F₀) x ∈ W := fun x hx =>
    map_add_feedback_sup_stabilizableSubspace_le A B F₀ hF₀ ⟨x, hx, rfl⟩
  let AW : W →ₗ[ℝ] W := (A + B.comp F₀).restrict hWinv
  let BW : U →ₗ[ℝ] W :=
    B.codRestrict W (fun u => hBleW (LinearMap.mem_range_self B u))
  let VW : Submodule ℝ W := V.comap W.subtype
  have hVWinv : ∀ v ∈ VW, AW v ∈ VW := by
    intro v hv
    rw [Submodule.mem_comap] at hv ⊢
    exact hF₀ ⟨(v : X), hv, rfl⟩
  have hmono : (LinearMap.stabilizableSubspace A B).comap W.subtype ≤
      (LinearMap.stabilizableSubspace (A + B.comp F₀) B).comap W.subtype :=
    Submodule.comap_mono (stabilizableSubspace_le_add_feedback A B F₀)
  have hsupV : VW ⊔ (LinearMap.stabilizableSubspace A B).comap W.subtype = ⊤ :=
    comap_sup_subtype_eq_top hWle le_sup_right (by rfl)
  have hsup : VW ⊔ LinearMap.stabilizableSubspace AW BW = ⊤ := by
    rw [stabilizableSubspace_restrict_eq (A + B.comp F₀) B W hWinv hBleW]
    apply le_antisymm le_top
    calc ⊤ = VW ⊔ (LinearMap.stabilizableSubspace A B).comap W.subtype := hsupV.symm
      _ ≤ VW ⊔ (LinearMap.stabilizableSubspace (A + B.comp F₀) B).comap W.subtype :=
          sup_le_sup_left hmono _
  have hstabQ : LinearMap.IsStabilizable (Submodule.mapQ VW VW AW hVWinv)
      (VW.mkQ.comp BW) :=
    isStabilizable_quotient_of_sup_stabilizableSubspace AW BW VW hVWinv hsup
  obtain ⟨G, hG⟩ := hstabQ
  obtain ⟨F₁, hF₁⟩ := LinearMap.exists_extend (G.comp VW.mkQ)
  let F : X →ₗ[ℝ] U := F₀ + F₁
  have hFV : Submodule.map (A + B.comp F) V ≤ V := by
    rintro y ⟨v, hv, rfl⟩
    have hvW : v ∈ W := hWle hv
    have hvVW : (⟨v, hvW⟩ : W) ∈ VW := by
      rw [Submodule.mem_comap]; exact hv
    have hF1v : F₁ v = 0 := by
      have h := congrArg (fun f : W →ₗ[ℝ] U => f ⟨v, hvW⟩) hF₁
      have h' : F₁ (W.subtype ⟨v, hvW⟩) = G (VW.mkQ ⟨v, hvW⟩) := by
        simpa only [LinearMap.comp_apply] using h
      have hv' : W.subtype ⟨v, hvW⟩ = v := rfl
      have hG0 : G (VW.mkQ ⟨v, hvW⟩) = 0 := by
        have hmk : VW.mkQ ⟨v, hvW⟩ = 0 := by
          rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
          exact hvVW
        rw [hmk, map_zero]
      rw [hv'] at h'
      rw [h', hG0]
    have hEq : (A + B.comp F) v = (A + B.comp F₀) v := by
      simp [F, hF1v]
    rw [hEq]
    exact hF₀ ⟨v, hv, rfl⟩
  refine ⟨F, hFV, fun d => ?_⟩
  have hMinv : ∀ x ∈ W, (A + B.comp F) x ∈ W :=
    fun x hx => map_add_feedback_sup_stabilizableSubspace_le A B F hFV ⟨x, hx, rfl⟩
  have hmap : ∀ x ∈ VW, ((A + B.comp F).restrict hMinv) x ∈ VW := fun x hx => by
    have hxV : (x : X) ∈ V := hx
    change (((A + B.comp F).restrict hMinv) x : X) ∈ V
    have hrestrict : (((A + B.comp F).restrict hMinv) x : X) =
        (A + B.comp F) (x : X) := rfl
    rw [hrestrict]
    exact hFV ⟨(x : X), hxV, rfl⟩
  have hmapEq : Submodule.mapQ VW VW ((A + B.comp F).restrict hMinv) hmap =
      Submodule.mapQ VW VW AW hVWinv + (VW.mkQ.comp BW).comp G := by
    apply LinearMap.ext
    intro y
    refine Submodule.Quotient.induction_on (p := VW) y ?_
    intro x
    have hF1x : F₁ x = G (VW.mkQ x) := by
      have := congrArg (fun f : W →ₗ[ℝ] U => f x) hF₁
      simpa using this
    have hxM : ((A + B.comp F).restrict hMinv) x = AW x + BW (G (VW.mkQ x)) := by
      apply Subtype.ext
      simp only [LinearMap.restrict_apply, LinearMap.add_apply, LinearMap.comp_apply,
        Submodule.coe_add, AW, F, hF1x, map_add]
      abel
    simp only [Submodule.mapQ_apply, LinearMap.add_apply, LinearMap.comp_apply,
      Submodule.mkQ_apply, hxM]
    rw [← Submodule.Quotient.mk_add]
  have hQ : LinearMap.IsHurwitz
      (Submodule.mapQ VW VW ((A + B.comp F).restrict hMinv) hmap) := by
    rw [hmapEq]; exact hG
  exact tendsto_readout_exp_of_geometricCondition A B H E V F hFV hVH hE hQ d

/-- **State-feedback external stabilization from the geometric condition of
Corollary 6.22.** Specialising the general construction to the largest
controlled-invariant subspace `V*(ker H) = controlledInvariantSubspace A B
(ker H)`: if the disturbance image lies in `V*(ker H) ⊔ Xstab(A, B)`, then there
is a state feedback `F` that preserves `V*(ker H)` and makes the closed-loop
controlled output of every disturbance direction decay to zero. This is the
state-feedback sufficiency direction of Trentelman–Stoorvogel–Hautus Theorem
4.39 / Corollary 6.22, with the geometric condition exactly as in the source. -/
theorem exists_feedback_tendsto_readout_of_corollary622
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) (E : D →ₗ[ℝ] X)
    (hE : LinearMap.range E ≤
      LinearMap.controlledInvariantSubspace A B (LinearMap.ker H) ⊔
        LinearMap.stabilizableSubspace A B) :
    ∃ F : X →ₗ[ℝ] U,
      Submodule.map (A + B.comp F)
        (LinearMap.controlledInvariantSubspace A B (LinearMap.ker H)) ≤
        LinearMap.controlledInvariantSubspace A B (LinearMap.ker H) ∧
      ∀ d : D, Tendsto (fun t : ℝ => H (NormedSpace.exp
        (t • (A + B.comp F).toContinuousLinearMap) (E d))) atTop (nhds 0) :=
  exists_feedback_tendsto_readout_of_geometricCondition A B H E
    (LinearMap.controlledInvariantSubspace A B (LinearMap.ker H))
    (LinearMap.isControlledInvariant_controlledInvariantSubspace A B (LinearMap.ker H))
    (LinearMap.controlledInvariantSubspace_le_K A B (LinearMap.ker H)) hE

end QuotientFeedbackLift

end GeometricFeedbackConstruction

end LinearSystem

/-! ## The dual output-injection (detectable) half: annihilator duality

Corollary 6.22 of Trentelman–Stoorvogel–Hautus pairs the primal state-feedback
condition `im E ≤ V*(ker H) + Xstab(A, B)` with the dual output-injection
condition `S*(im E) ∩ Xdet(C, A) ≤ ker H`. The state-feedback half is assembled
in the previous section; this section records the geometric duality bridge that
the dual half rests on.

The smallest conditioned invariant subspace `S*(E) = conditionedInvariantSubspace
C A E` is, by the duality of Theorem 5.6, the annihilator of the largest
controlled invariant subspace of the transposed pair that is contained in
`Eᵃⁿⁿ = ker E.dualMap`. The two CISA/ISA recurrences dualize step by step, so
the identity holds without any characteristic-polynomial or spectral input. -/

namespace LinearMap

variable {𝕜 X Y : Type*}
variable [Field 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup Y] [Module 𝕜 Y]

/-- **Step-by-step duality of the CISA and ISA recurrences.** The annihilator of
the `n`-th conditioned-invariant iterate is the `n`-th controlled-invariant
iterate of the transposed pair, starting from the annihilator `Eᵃⁿⁿ`.

This is the finite-step form of Trentelman–Stoorvogel–Hautus, display (5.5)
under the duality of Theorem 5.6. -/
theorem dualAnnihilator_conditionedInvariantSeq (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X)
    (E : Submodule 𝕜 X) (n : ℕ) :
    (conditionedInvariantSeq C A E n).dualAnnihilator =
      controlledInvariantSeq A.dualMap C.dualMap E.dualAnnihilator n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [conditionedInvariantSeq_succ, controlledInvariantSeq_succ,
        Submodule.dualAnnihilator_sup_eq, dualAnnihilator_map_inf_ker, ih]

/-- **Duality of `S*` and `V*`.** The annihilator of the smallest conditioned
invariant subspace containing `E` is the largest controlled invariant subspace
of the transposed pair contained in `Eᵃⁿⁿ = ker E.dualMap`:

`S*(E)ᵃⁿⁿ = V*(Eᵃⁿⁿ)`.

This is the geometric duality between the primal and dual halves of Corollary
6.22 and the precise bridge used to restate the output-injection condition
`S*(im E) ∩ Xdet ≤ ker H` as a state-feedback condition on the transposed
system. -/
theorem dualAnnihilator_conditionedInvariantSubspace (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X)
    (E : Submodule 𝕜 X) :
    (conditionedInvariantSubspace C A E).dualAnnihilator =
      controlledInvariantSubspace A.dualMap C.dualMap E.dualAnnihilator := by
  rw [conditionedInvariantSubspace, controlledInvariantSubspace,
    Submodule.dualAnnihilator_iSup_eq]
  exact iInf_congr fun n => dualAnnihilator_conditionedInvariantSeq C A E n

end LinearMap

/-! ### The dual condition as an algebraic condition on the transposed pair

The remaining ingredient of the output-injection half is the detectability
subspace `Xdet(C, A) = ⟨ker C | A⟩ ∩ X_b(A)`, whose annihilator we expand below.
The reachable part dualizes by the accepted
`reachableSubspace_dualMap`; the antistable part `(X_b(A))ᵃⁿⁿ` is kept as an
explicit algebraic object, because the stable subspace `X_g(A.dualMap)` cannot
be written down in this way without first putting a norm (and hence a `Module.finBasis`)
on the algebraic dual `Module.Dual ℝ X`. This is exactly the missing bridge;
the results below isolate it precisely and the section note records it as the
handoff item. -/

namespace LinearMap

variable {X Y Z D : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [AddCommGroup Y] [Module ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- **Annihilator of the detectability subspace.** The detectability subspace
`Xdet(C, A) = ⟨ker C | A⟩ ∩ X_b(A)` has annihilator
`⟨Aᵀ | im Cᵀ⟩ ⊔ (X_b(A))ᵃⁿⁿ`. The first summand is the reachable subspace of
the transposed pair (`reachableSubspace_dualMap`); the second is the annihilator
of the antistable subspace, the only part that is not expressible through the
algebraic dual alone. -/
theorem dualAnnihilator_detectableSubspace (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) :
    (detectableSubspace C A).dualAnnihilator =
      reachableSubspace A.dualMap C.dualMap ⊔ (unstableSubspace A).dualAnnihilator := by
  rw [detectableSubspace, Subspace.dualAnnihilator_inf_eq, ← reachableSubspace_dualMap]

/-- **Dual form of the Corollary 6.22 output-injection condition.** The source's
second condition `S*(im E) ∩ Xdet(C, A) ≤ ker H` is equivalent to the purely
algebraic condition on the transposed pair

`im Hᵀ ≤ V*(ker Eᵀ) ⊔ (⟨Aᵀ | im Cᵀ⟩ ⊔ (X_b(A))ᵃⁿⁿ)`

where `V*(ker Eᵀ) = controlledInvariantSubspace A.dualMap C.dualMap
(im E)ᵃⁿⁿ = S*(im E)ᵃⁿⁿ` by `dualAnnihilator_conditionedInvariantSubspace`.

The only remaining identification needed to match the primal geometric condition
`im E ≤ V*(ker H) + Xstab(A, B)` is `(X_b(A))ᵃⁿⁿ = X_g(Aᵀ)`, i.e. the transpose
stable/antistable duality; because `Module.Dual ℝ X` carries no norm and no
`Module.finBasis`, `X_g(A.dualMap)` is not currently a definable object here.
This equivalence is therefore the precise reusable bridge and the point at which
the output-injection half is blocked. -/
theorem conditionedInvariant_inf_detectable_le_ker_iff_dualAlgebraicCondition
    (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    conditionedInvariantSubspace C A (LinearMap.range E) ⊓ detectableSubspace C A ≤
        LinearMap.ker H ↔
      LinearMap.range H.dualMap ≤
        controlledInvariantSubspace A.dualMap C.dualMap
            (LinearMap.range E).dualAnnihilator ⊔
          (reachableSubspace A.dualMap C.dualMap ⊔
            (unstableSubspace A).dualAnnihilator) := by
  rw [← Subspace.dualAnnihilator_le_dualAnnihilator_iff (W := LinearMap.ker H)
    (W' := conditionedInvariantSubspace C A (LinearMap.range E) ⊓ detectableSubspace C A)]
  rw [Subspace.dualAnnihilator_inf_eq, dualAnnihilator_conditionedInvariantSubspace,
    dualAnnihilator_detectableSubspace, LinearMap.range_dualMap_eq_dualAnnihilator_ker]

/-- **Dual output-injection condition in real-coordinate (stable-subspace)
form.** Replacing the antistable annihilator `(X_b(A))ᵃⁿⁿ` by the stable subspace
of the algebraic transpose with the completed real-coordinate transport
`dualAnnihilator_unstableSubspace_eq_stableSubspace_dualMap`, the dual algebraic
condition of Corollary 6.22 becomes

`im Hᵀ ≤ V*(ker Eᵀ) ⊔ (⟨Aᵀ | im Cᵀ⟩ ⊔ X_g(Aᵀ))`,

the transpose of the primal geometric condition `im E ≤ V*(ker H) + Xstab(A, B)`.
This exposes the completed transport to the output-injection layer without
introducing a norm or a basis on `Module.Dual ℝ X` beyond the canonical finite
basis `Module.finBasis ℝ (Module.Dual ℝ X)`. -/
theorem conditionedInvariant_inf_detectable_le_ker_iff_dualStableCondition
    (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    conditionedInvariantSubspace C A (LinearMap.range E) ⊓ detectableSubspace C A ≤
        LinearMap.ker H ↔
      LinearMap.range H.dualMap ≤
        controlledInvariantSubspace A.dualMap C.dualMap
            (LinearMap.range E).dualAnnihilator ⊔
          (reachableSubspace A.dualMap C.dualMap ⊔
            stableSubspaceOfBasis (Module.finBasis ℝ (Module.Dual ℝ X)) A.dualMap) := by
  rw [conditionedInvariant_inf_detectable_le_ker_iff_dualAlgebraicCondition,
    dualAnnihilator_unstableSubspace_eq_stableSubspace_dualMap]

end LinearMap

/-! ### Handoff: the remaining output-injection bridge

The dual output-injection half of Corollary 6.22 is now reduced to a single
missing declaration. After the accepted commit `0229756` the antistable
annihilator `(X_b(A))ᵃⁿⁿ` has not yet been identified with the stable subspace
of the transpose. The stabilizable/stable spaces are available on any
finite-dimensional real vector space through the norm-free API in
`DynamicalSystems/Linear/Stabilization.lean`
(`stableSubspaceOfBasis`, `unstableSubspaceOfBasis`, with
`stableSubspaceOfBasis_finBasis_eq_hurwitzSubspace` recovering the accepted
`hurwitzSubspace` definitionally). The missing reusable lemma is therefore now
well-typed:

`(unstableSubspace A).dualAnnihilator =
   stableSubspaceOfBasis (Module.finBasis ℝ (Module.Dual ℝ X)) A.dualMap`,

equivalently, after basis independence, `(detectableSubspace C A).dualAnnihilator
= stabilizableSubspace` of the transposed pair.

**Completed in the current attempt** (all in
`DynamicalSystems/Linear/Stabilization.lean`, compiled and audited):

1. **Arbitrary-basis `baseChange` dictionary.**
   `baseChange_eq_basis_gen`, `baseChange_repr_comp_gen` and
   `baseChange_equivFun_symm_one_tmul_gen` generalise the accepted
   `baseChange`/`baseChange_repr_comp`/`baseChange_equivFun_symm_one_tmul`
   lemmas from `Module.finBasis` to an arbitrary finite basis `b`, with no norm
   hypotheses. `baseChange_repr_comp_gen` states that `b.equivFun` intertwines
   `A.baseChange ℂ` with the complexified coordinate matrix
   `(toMatrix b b A).map (algebraMap ℝ ℂ)`.
2. **Basis independence.** The canonical complex objects
   `complexStableSubspace A`/`complexUnstableSubspace A` live in
   `ℂ ⊗[ℝ] M`; `map_complexStableSubspace`/`map_complexUnstableSubspace`
   identify their coordinate pull-backs with
   `complexSpectralSubspaceOfBasis` in any basis via the accepted
   `map_maxGenEigenspace_of_equiv`.
   `mem_stableSubspaceOfBasis_iff`/`mem_unstableSubspaceOfBasis_iff` give the
   basis-free characterisation `x ∈ stableSubspaceOfBasis b A ↔
   1 ⊗ₜ x ∈ complexStableSubspace A`, and
   `stableSubspaceOfBasis_eq_of_basis`/`unstableSubspaceOfBasis_eq_of_basis`
   prove that the stable and antistable subspaces do not depend on `b`. This is
   what makes `stableSubspaceOfBasis` on the algebraic dual `Module.Dual ℝ X`
   well defined.
3. **Per-eigenvalue transpose dimension match.**
   `finrank_maxGenEigenspace_dualMap`: over `ℂ`, the generalized eigenspaces of
   `A` and `A.dualMap` at `μ` have equal `finrank`, from rank–nullity plus the
   accepted `range_dualMap_eq_dualAnnihilator_ker`. This is the dimension input
   for the transpose duality.

**Complex transpose spectral duality, equality form.** The abstract
finite-dimensional complex statement

`(⨆_{re μ ≥ 0} X_μ(f)).dualAnnihilator = ⨆_{re ν < 0} X_ν(f.dualMap)`

is now proved for every finite-dimensional complex endomorphism `f` as
`dualAnnihilator_antistable_eq_stable`. The `≤` half is
`stable_le_dualAnnihilator_antistable` (`maxGenEigenspace_le_genEigenrange_of_ne`
plus the accepted `dualAnnihilator_genEigenrange_finrank_eq_maxGenEigenspace`).
For the reverse half, the finite-support dimension formula is supplied by
`finset_supIndep_finrank_sup_eq_sum`, `finrank_iSup_fintype`,
`finrank_iSup_of_iSupIndep` and the filtered form
`finrank_iSup_subtype_eq_sum_filter`. Applied to the generalized-eigenspace
families of `f` and `f.dualMap`, these give
`finrank U + finrank V = finrank E` for `U = ⨆_{re μ ≥ 0} X_μ(f)` and
`V = ⨆_{re ν < 0} X_ν(f.dualMap)`: the full decomposition
`⨆_μ X_μ(f) = ⊤` (`Module.End.iSup_maxGenEigenspace_eq_top`) splits the sum
into the antistable and stable parts, and `finrank_maxGenEigenspace_dualMap`
makes the two stable partial sums agree pointwise. With
`Subspace.finrank_add_finrank_dualAnnihilator_eq` the dimensions force the
inclusion to be an equality.

The named lemmas `LinearMap.finrank_maxGenEigenspace_eq` (Mathlib,
`finrank X_μ(f) = f.charpoly.rootMultiplicity μ`) and
`LinearMap.charpoly_dualMap_ofField` (already proved in
`Stabilization.lean`, `f.dualMap.charpoly = f.charpoly` over any field) are
available, but the dimension input here is obtained more directly from the
finite-dimensional generalized-eigenspace decomposition plus
`finrank_maxGenEigenspace_dualMap`, so neither is needed in the argument.

The remaining step to the real statement
`(unstableSubspace A).dualAnnihilator =
stableSubspaceOfBasis (Module.finBasis ℝ (Module.Dual ℝ X)) A.dualMap` is the
transport across `IsBaseChange.toDualBaseChange` (base change commutes with the
dual), which is **not** formalised here. Once that transport is available the
accepted state-feedback construction
`exists_feedback_tendsto_readout_of_geometricCondition` can be run on the
transposed pair and the resulting gain transposed back with
`dualMap_surjective`, yielding the observer gain `G` of
Trentelman–Stoorvogel–Hautus Lemma 6.20/6.21. Until then no output-injection
statement is claimed. -/

/-! ### Update: the real-coordinate transport is complete

The transport recorded above as missing is now formalised in
`DynamicalSystems/Linear/Stabilization.lean`:

* `span_inter_range_ofRealPi_eq_of_star_mem`: the complex span of the real
  points of a conjugation-stable subspace of `ι → ℂ` is the subspace itself.
* `complexUnstableSubspace_eq_baseChange_unstableSubspace`: the abstract
  complexification `complexUnstableSubspace A` is the base change of the real
  antistable subspace `unstableSubspace A`.
* `dualAnnihilator_baseChange_iff`: annihilators commute with the base change
  `ℝ → ℂ`.
* `toDualBaseChange_one_tmul` and `map_toDualBaseChange_complexStableSubspace`:
  the ℂ-linear dual base-change equivalence
  `IsBaseChange.toDualBaseChange` sends `1 ⊗ φ` to the base-changed functional
  and intertwines the stable subspaces of `A.dualMap` and
  `(A.baseChange ℂ).dualMap`.
* `dualAnnihilator_unstableSubspace_eq_stableSubspace_dualMap`: the real
  statement
  `(unstableSubspace A).dualAnnihilator =
   stableSubspaceOfBasis (Module.finBasis ℝ (Module.Dual ℝ X)) A.dualMap`,

the missing bridge `(X_b(A))ᵃⁿⁿ = X_g(Aᵀ)`. With it, the dual algebraic
condition of Corollary 6.22 is exposed in real-coordinate form as
`conditionedInvariant_inf_detectable_le_ker_iff_dualStableCondition`.

The next milestone is to run the accepted state-feedback construction on the
transposed dual pair, with the roles of the disturbance channel `E` and the
controlled output `H` exchanged, and then transpose the resulting gain back with
`dualMap_surjective`, yielding the observer injection `G` of
Trentelman–Stoorvogel–Hautus Lemma 6.20/6.21 and the corresponding dual
external-stability theorem. That observer construction is not claimed here.
-/

/-! ## The dual observer/output-injection gain assembly

The final step of Corollary 6.22 is to run the accepted state-feedback
geometric-condition decay theorem on the transposed pair and transport the
resulting feedback back to an output injection by `dualMap_surjective`. The
transposed pair has algebraic-dual state space `Module.Dual ℝ X`. The algebraic
dual of a finite-dimensional real space carries no norm instance in the pinned
library, so the first two declarations below install the basis-coordinate norm
on `Module.Dual ℝ X`; this is the norm-free `Module.finBasis` coordinate norm and
is compatible with the canonical `AddCommGroup`/`Module` structure of the dual,
so it can be used by `LinearMap.toContinuousLinearMap` and `NormedSpace.exp`. The
output of the construction is an output injection `G` whose dual observer-error
operator `A - G C` has transposed readout decaying to zero for every disturbance
direction. -/

namespace LinearMap

/-- **Basis-coordinate norm on the algebraic dual.** For a finite-dimensional
real vector space `X`, the algebraic dual `Module.Dual ℝ X` is given the norm
`‖φ‖ = ‖(Module.finBasis ℝ (Module.Dual ℝ X)).equivFun φ‖` of its coordinates.
This is the norm instance that makes `Module.Dual ℝ X` a normed space without
introducing a topology through `LinearMap.toContinuousLinearMap`; it reuses the
canonical linear structure of the dual, so the classical/continuous dual
dictionary stays dense. -/
noncomputable instance instNormedAddCommGroupDual (X : Type*) [AddCommGroup X]
    [Module ℝ X] [FiniteDimensional ℝ X] : NormedAddCommGroup (Module.Dual ℝ X) := by
  letI : Norm (Module.Dual ℝ X) :=
    ⟨fun x => ‖(Module.finBasis ℝ (Module.Dual ℝ X)).equivFun x‖⟩
  exact NormedAddCommGroup.ofCore (𝕜 := ℝ)
    { norm_nonneg := fun x => by
        change 0 ≤ ‖(Module.finBasis ℝ (Module.Dual ℝ X)).equivFun x‖
        exact norm_nonneg _
      norm_smul := fun c x => by
        change ‖(Module.finBasis ℝ (Module.Dual ℝ X)).equivFun (c • x)‖ =
          ‖c‖ * ‖(Module.finBasis ℝ (Module.Dual ℝ X)).equivFun x‖
        rw [map_smul, norm_smul]
      norm_triangle := fun x y => by
        change ‖(Module.finBasis ℝ (Module.Dual ℝ X)).equivFun (x + y)‖ ≤
          ‖(Module.finBasis ℝ (Module.Dual ℝ X)).equivFun x‖ +
            ‖(Module.finBasis ℝ (Module.Dual ℝ X)).equivFun y‖
        rw [map_add]
        exact norm_add_le _ _
      norm_eq_zero_iff := fun x => by
        change ‖(Module.finBasis ℝ (Module.Dual ℝ X)).equivFun x‖ = 0 ↔ x = 0
        rw [norm_eq_zero, (Module.finBasis ℝ (Module.Dual ℝ X)).equivFun.map_eq_zero_iff] }

/-- **Normed-space structure on the algebraic dual** generated by the
basis-coordinate norm of `instNormedAddCommGroupDual`. -/
noncomputable instance instNormedSpaceDual (X : Type*) [AddCommGroup X]
    [Module ℝ X] [FiniteDimensional ℝ X] : NormedSpace ℝ (Module.Dual ℝ X) := by
  letI : Norm (Module.Dual ℝ X) :=
    ⟨fun x => ‖(Module.finBasis ℝ (Module.Dual ℝ X)).equivFun x‖⟩
  let core : NormedSpace.Core ℝ (Module.Dual ℝ X) :=
    { norm_nonneg := fun x => by
        change 0 ≤ ‖(Module.finBasis ℝ (Module.Dual ℝ X)).equivFun x‖
        exact norm_nonneg _
      norm_smul := fun c x => by
        change ‖(Module.finBasis ℝ (Module.Dual ℝ X)).equivFun (c • x)‖ =
          ‖c‖ * ‖(Module.finBasis ℝ (Module.Dual ℝ X)).equivFun x‖
        rw [map_smul, norm_smul]
      norm_triangle := fun x y => by
        change ‖(Module.finBasis ℝ (Module.Dual ℝ X)).equivFun (x + y)‖ ≤
          ‖(Module.finBasis ℝ (Module.Dual ℝ X)).equivFun x‖ +
            ‖(Module.finBasis ℝ (Module.Dual ℝ X)).equivFun y‖
        rw [map_add]
        exact norm_add_le _ _
      norm_eq_zero_iff := fun x => by
        change ‖(Module.finBasis ℝ (Module.Dual ℝ X)).equivFun x‖ = 0 ↔ x = 0
        rw [norm_eq_zero, (Module.finBasis ℝ (Module.Dual ℝ X)).equivFun.map_eq_zero_iff] }
  letI : NormedAddCommGroup (Module.Dual ℝ X) := NormedAddCommGroup.ofCore (𝕜 := ℝ) core
  exact NormedSpace.ofCore core

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

/-! ### Transpose naturality of the exponential

The exponential of the algebraic transpose is the transpose of the exponential:
for a real endomorphism `T` of a finite-dimensional space and every `t : ℝ`,

`exp (t • Tᵀ) = (exp (t • T))ᵀ`.

The algebraic transpose is an algebra *anti*-homomorphism (`(S ∘ R)ᵀ = Rᵀ ∘ Sᵀ`),
so it is realised below as the ring homomorphism `dualMapRingHom` into the
multiplicative opposite ring, which is exactly the shape `NormedSpace.map_exp`
accepts; `NormedSpace.exp_op` then removes the opposite. The pointwise form
`exp_smul_dualMap_apply` is the pairing identity used to turn the accepted dual
observer readout into the primal readout. -/

/-- The algebraic transpose as an ℝ-linear map from the continuous endomorphisms
of `X` to the continuous endomorphisms of the algebraic dual `Module.Dual ℝ X`.
This is the underlying linear map of `dualMapRingHom`; being a linear map between
finite-dimensional normed spaces it is automatically continuous, which is what
lets `NormedSpace.exp` commute with the transpose. -/
noncomputable def dualMapLinearMap :
    (X →L[ℝ] X) →ₗ[ℝ] (Module.Dual ℝ X →L[ℝ] Module.Dual ℝ X) where
  toFun S := ((S : X →ₗ[ℝ] X).dualMap).toContinuousLinearMap
  map_add' S R := by
    ext φ x
    simp [LinearMap.dualMap_apply]
  map_smul' c S := by
    ext φ x
    simp [LinearMap.dualMap_apply]

/-- The algebraic transpose bundled as a ring homomorphism into the
multiplicative opposite of the endomorphism ring of the algebraic dual. The
multiplicative opposite is required because the transpose reverses products:
`(S ∘ R)ᵀ = Rᵀ ∘ Sᵀ`. This is the form needed by `NormedSpace.map_exp`. -/
noncomputable def dualMapRingHom :
    (X →L[ℝ] X) →+* (Module.Dual ℝ X →L[ℝ] Module.Dual ℝ X)ᵐᵒᵖ where
  toFun S := MulOpposite.op (((S : X →ₗ[ℝ] X).dualMap).toContinuousLinearMap)
  map_one' := by
    apply MulOpposite.unop_injective
    ext φ x
    simp [LinearMap.dualMap_apply]
  map_mul' S R := by
    apply MulOpposite.unop_injective
    ext φ x
    simp [LinearMap.dualMap_apply]
  map_zero' := by
    apply MulOpposite.unop_injective
    ext φ x
    simp [LinearMap.dualMap_apply]
  map_add' S R := by
    apply MulOpposite.unop_injective
    ext φ x
    simp [LinearMap.dualMap_apply]

/-- **Transpose naturality of the exponential.** For a real endomorphism `T` of a
finite-dimensional real normed space and every `t : ℝ`, the exponential of the
scaled transpose equals the transpose of the exponential of the scaled map:

`exp (t • Tᵀ) = (exp (t • T))ᵀ`

where the exponential on the left lives in the endomorphism algebra of the
algebraic dual `Module.Dual ℝ X` and the transpose on the right is the algebraic
transpose of the continuous endomorphism `exp (t • T)`. This is the missing
bridge between the dual observer gain and the primal readout; it is proved by
transporting `NormedSpace.map_exp` along the anti-homomorphism `dualMapRingHom`. -/
theorem exp_smul_dualMap_eq (T : X →ₗ[ℝ] X) (t : ℝ) :
    NormedSpace.exp (t • T.dualMap.toContinuousLinearMap) =
      (((NormedSpace.exp (t • T.toContinuousLinearMap) : X →L[ℝ] X) :
        X →ₗ[ℝ] X).dualMap).toContinuousLinearMap := by
  have hcont : Continuous (dualMapRingHom (X := X)) := by
    change Continuous (fun S : X →L[ℝ] X =>
      MulOpposite.op (((S : X →ₗ[ℝ] X).dualMap).toContinuousLinearMap))
    exact MulOpposite.opHomeomorph.continuous.comp
      (dualMapLinearMap (X := X)).continuous_of_finiteDimensional
  have hx : (t • T.toContinuousLinearMap) ∈
      Metric.eball (0 : X →L[ℝ] X) (NormedSpace.expSeries ℝ (X →L[ℝ] X)).radius := by
    rw [NormedSpace.expSeries_radius_eq_top]
    exact edist_lt_top _ _
  have h := NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (dualMapRingHom (X := X)) hcont
    (t • T.toContinuousLinearMap) hx
  have hsmul : dualMapRingHom (X := X) (t • T.toContinuousLinearMap) =
      MulOpposite.op (t • T.dualMap.toContinuousLinearMap) := by
    apply MulOpposite.unop_injective
    ext φ x
    simp only [dualMapRingHom, MulOpposite.unop_op]
    simp [LinearMap.dualMap_apply]
  rw [hsmul, NormedSpace.exp_op] at h
  exact (MulOpposite.op_injective h).symm

/-- **Transpose naturality of the exponential, linear-map form.** Restating
`exp_smul_dualMap_eq` as an equality of linear maps on the algebraic dual:

`(exp (t • Tᵀ)).toLinearMap = (exp (t • T))ᵀ`.

This makes explicit that the exponential of the transpose is the transpose of
the exponential, without the `toContinuousLinearMap` bookkeeping needed for the
equality of continuous linear maps. -/
theorem exp_smul_dualMap_toLinearMap_eq (T : X →ₗ[ℝ] X) (t : ℝ) :
    (NormedSpace.exp (t • T.dualMap.toContinuousLinearMap)).toLinearMap =
      ((NormedSpace.exp (t • T.toContinuousLinearMap) : X →L[ℝ] X) : X →ₗ[ℝ] X).dualMap :=
  by
  rw [exp_smul_dualMap_eq]
  rfl

/-- **Pointwise transpose-exponential pairing.** The transpose-naturality
identity `exp_smul_dualMap_eq` in evaluation form: for every dual vector `φ` and
vector `x`,

`(exp (t • Tᵀ) φ) x = φ ((exp (t • T)) x)`.

This is the form in which the exponential/transpose bridge is consumed by the
observer readout: pairing the transposed dual readout against a disturbance
direction produces exactly the primal readout evaluated through the functional. -/
theorem exp_smul_dualMap_apply (T : X →ₗ[ℝ] X) (t : ℝ) (φ : Module.Dual ℝ X) (x : X) :
    (NormedSpace.exp (t • T.dualMap.toContinuousLinearMap)) φ x =
      φ ((NormedSpace.exp (t • T.toContinuousLinearMap)) x) := by
  rw [exp_smul_dualMap_eq]
  simp [LinearMap.dualMap_apply]

end LinearMap

namespace LinearSystem

section ObserverGainAssembly

variable {X Y Z D : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [AddCommGroup Y] [Module ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ D]

/-- **Observer/output-injection assembly from the dual geometric condition.**
Assume the Corollary 6.22 output-injection condition
`S*(im E) ∩ Xdet(C, A) ≤ ker H`. Then there is an output injection
`G : Y →ₗ[ℝ] X`, in the `A + G C` convention of `observerErrorBlock_eq`, such
that for every `z` in the readout dual the transposed readout function

`t ↦ Eᵀ (exp (t • (A + G C)ᵀ)) (Hᵀ z)`

tends to zero. This is the transposed form of the observer-error readout decay:
with `L = -G` the observer error operator is `A - L C = A + G C` and, pairing
the dual statement against a disturbance direction `d`, the decay is exactly
`z (H (exp (t • (A + G C)) (E d))) → 0` in the DynamicInterconnection model.

The gain is the transpose of the state feedback supplied by
`exists_feedback_tendsto_readout_of_corollary622` applied to the transposed pair
`(Aᵀ, Cᵀ, Eᵀ, Hᵀ)`, transported back with `dualMap_surjective`; the passage from
the primal condition to the transposed geometric condition is the accepted real
dual annihilator/stable-subspace identity
`conditionedInvariant_inf_detectable_le_ker_iff_dualStableCondition`. -/
theorem exists_outputInjection_dualReadout_tendsto_of_dualCondition
    (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : LinearMap.conditionedInvariantSubspace C A (LinearMap.range E) ⊓
        LinearMap.detectableSubspace C A ≤ LinearMap.ker H) :
    ∃ G : Y →ₗ[ℝ] X,
      ∀ z : Module.Dual ℝ Z, Filter.Tendsto (fun t : ℝ => E.dualMap (NormedSpace.exp
        (t • ((A + G.comp C).dualMap).toContinuousLinearMap) (H.dualMap z)))
        Filter.atTop (nhds 0) := by
  have hdual :=
    (LinearMap.conditionedInvariant_inf_detectable_le_ker_iff_dualStableCondition
      C A E H).mp h
  have hstab : LinearMap.stabilizableSubspace A.dualMap C.dualMap =
      LinearMap.reachableSubspace A.dualMap C.dualMap ⊔
        LinearMap.stableSubspaceOfBasis
          (Module.finBasis ℝ (Module.Dual ℝ X)) A.dualMap := by
    rw [LinearMap.stabilizableSubspace,
      ← LinearMap.stableSubspaceOfBasis_finBasis_eq_hurwitzSubspace A.dualMap, sup_comm]
  have hE : LinearMap.range H.dualMap ≤
      LinearMap.controlledInvariantSubspace A.dualMap C.dualMap (LinearMap.ker E.dualMap) ⊔
        LinearMap.stabilizableSubspace A.dualMap C.dualMap := by
    rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range, hstab]
    exact hdual
  obtain ⟨F', -, hdecay⟩ :=
    LinearSystem.exists_feedback_tendsto_readout_of_corollary622
      A.dualMap C.dualMap E.dualMap H.dualMap hE
  obtain ⟨G, hG⟩ := LinearMap.dualMap_surjective (X := X) (Y := Y) F'
  refine ⟨G, fun z => ?_⟩
  have hmaps : A.dualMap + C.dualMap.comp F' = (A + G.comp C).dualMap := by
    rw [LinearMap.dualMap_add, ← LinearMap.dualMap_comp_dualMap C G, hG]
  rw [← hmaps]
  exact hdecay z

/-- **Observer error decay in the observer-error operator convention.** The
contract's observer error is `A - L.comp C`; the assembled output injection of
`exists_outputInjection_dualReadout_tendsto_of_dualCondition` is `L = -G` in that
convention. This restatement is the direct observer-error form of the preceding
transposed readout decay. -/
theorem exists_observerError_dualReadout_tendsto_of_dualCondition
    (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : LinearMap.conditionedInvariantSubspace C A (LinearMap.range E) ⊓
        LinearMap.detectableSubspace C A ≤ LinearMap.ker H) :
    ∃ L : Y →ₗ[ℝ] X,
      ∀ z : Module.Dual ℝ Z, Filter.Tendsto (fun t : ℝ => E.dualMap (NormedSpace.exp
        (t • ((A - L.comp C).dualMap).toContinuousLinearMap) (H.dualMap z)))
        Filter.atTop (nhds 0) := by
  obtain ⟨G, hG⟩ := exists_outputInjection_dualReadout_tendsto_of_dualCondition C A E H h
  refine ⟨-G, ?_⟩
  have hLG : A - (-G).comp C = A + G.comp C := by
    rw [LinearMap.neg_comp]
    abel
  rwa [hLG]

end ObserverGainAssembly

/-! ## The primal observer-error readout

The transpose-exponential pairing turns the accepted dual observer-gain readout
into the primal one. The remaining ingredient is that a finite-dimensional real
space is separated by its algebraic dual *in the norm topology*: coordinatewise
convergence (which is what the dual pairing supplies) upgrades to norm
convergence because any linear equivalence onto a coordinate space is a
homeomorphism. This is the `Module.finBasis` step at the end of
`exists_observerError_readout_tendsto_of_dualCondition`.

The resulting statement is the *stable nonzero* observer-error readout: the
observer-error output `H (exp (t • (A - L C)) (E d))` decays to zero for every
disturbance direction `d`, with the gain `L` produced from the Corollary 6.22
output-injection condition. The exact-zero statement (`E d = 0`, or a zero
initial error, stays zero) is the separate decoupling layer and is not conflated
with this decay statement. -/

section PrimalObserverReadout

variable {X U Y Z D : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [AddCommGroup U] [Module ℝ U]
variable [AddCommGroup Y] [Module ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z] [FiniteDimensional ℝ D]

/-- **Primal observer-error readout decay from the dual observer condition.**
Assume the Corollary 6.22 output-injection condition
`S*(im E) ∩ Xdet(C, A) ≤ ker H`. Then there is an observer gain
`L : Y →ₗ[ℝ] X`, in the contract's `A - L C` observer-error convention, such that
the primal observer-error readout

`t ↦ H (exp (t • (A - L.comp C)) (E d))`

decays to zero for every disturbance direction `d`.

This is obtained from the accepted dual statement
`exists_observerError_dualReadout_tendsto_of_dualCondition` by the
transpose-exponential pairing `exp_smul_dualMap_apply` (which identifies the
transposed readout with `z (H (exp (t • (A - L.comp C)) (E d)))` for every
functional `z`) and the finite-dimensional fact that the algebraic dual separates
points in the norm topology. -/
theorem exists_observerError_readout_tendsto_of_dualCondition
    (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : LinearMap.conditionedInvariantSubspace C A (LinearMap.range E) ⊓
        LinearMap.detectableSubspace C A ≤ LinearMap.ker H) :
    ∃ L : Y →ₗ[ℝ] X, ∀ d : D,
      Filter.Tendsto (fun t : ℝ =>
        H (NormedSpace.exp (t • (A - L.comp C).toContinuousLinearMap) (E d)))
        Filter.atTop (nhds 0) := by
  obtain ⟨L, hL⟩ := exists_observerError_dualReadout_tendsto_of_dualCondition C A E H h
  refine ⟨L, fun d => ?_⟩
  let b := Module.finBasis ℝ Z
  have hz : ∀ z : Module.Dual ℝ Z, Filter.Tendsto (fun t : ℝ =>
      z (H (NormedSpace.exp (t • (A - L.comp C).toContinuousLinearMap) (E d))))
      Filter.atTop (nhds 0) := by
    intro z
    have hpair : ∀ t : ℝ,
        (E.dualMap (NormedSpace.exp
          (t • ((A - L.comp C).dualMap).toContinuousLinearMap) (H.dualMap z))) d =
        z (H (NormedSpace.exp (t • (A - L.comp C).toContinuousLinearMap) (E d))) := by
      intro t
      rw [LinearMap.dualMap_apply, LinearMap.exp_smul_dualMap_apply,
        LinearMap.dualMap_apply]
    have hev : Continuous (fun ψ : Module.Dual ℝ D => ψ d) :=
      (LinearMap.continuous_of_finiteDimensional
        ({ toFun := fun ψ => ψ d
           map_add' := fun a b => rfl
           map_smul' := fun c a => rfl } : Module.Dual ℝ D →ₗ[ℝ] ℝ))
    have h1 : Filter.Tendsto (fun t : ℝ =>
        (E.dualMap (NormedSpace.exp
          (t • ((A - L.comp C).dualMap).toContinuousLinearMap) (H.dualMap z))) d)
        Filter.atTop (nhds 0) :=
      (hev.tendsto 0).comp (hL z)
    rw [show (fun t : ℝ => z (H (NormedSpace.exp
        (t • (A - L.comp C).toContinuousLinearMap) (E d))))
        = (fun t : ℝ => (E.dualMap (NormedSpace.exp
          (t • ((A - L.comp C).dualMap).toContinuousLinearMap) (H.dualMap z))) d)
        from funext (fun t => (hpair t).symm)]
    exact h1
  have hcoord : Filter.Tendsto (fun t : ℝ => b.equivFun
      (H (NormedSpace.exp (t • (A - L.comp C).toContinuousLinearMap) (E d))))
      Filter.atTop (nhds 0) := by
    rw [tendsto_pi_nhds]
    intro i
    have := hz (b.coord i)
    simpa [Module.Basis.equivFun_apply, Module.Basis.coord_apply] using this
  have hcont : Continuous (fun x : Fin (Module.finrank ℝ Z) → ℝ => b.equivFun.symm x) :=
    b.equivFun.toContinuousLinearEquiv.symm.continuous
  have h2 : Filter.Tendsto (fun t : ℝ => b.equivFun.symm (b.equivFun
      (H (NormedSpace.exp (t • (A - L.comp C).toContinuousLinearMap) (E d)))))
      Filter.atTop (nhds (b.equivFun.symm 0)) :=
    (hcont.tendsto 0).comp hcoord
  rw [map_zero] at h2
  exact Filter.Tendsto.congr (fun t => b.equivFun.symm_apply_apply _) h2

/-- **Primal observer-error readout decay from the Corollary 6.22 conditions.**
The packaged form of `exists_observerError_readout_tendsto_of_dualCondition`:
under the full Corollary 6.22 geometric subspace conditions
`ExternalStabilizationConditions`, the second conjunct (the output-injection
condition) supplies the observer gain `L` in the contract's `A - L C`
convention for which the primal observer-error readout decays to zero for every
disturbance direction. The first conjunct (the state-feedback condition) is not
needed for the observer half and is retained only so that the hypothesis matches
the source criterion. -/
theorem exists_observerError_readout_tendsto_of_externalStabilizationConditions
    (sys : LinearSystem ℝ X U Y) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : ExternalStabilizationConditions sys E H) :
    ∃ L : Y →ₗ[ℝ] X, ∀ d : D,
      Filter.Tendsto (fun t : ℝ =>
        H (NormedSpace.exp (t • (sys.A - L.comp sys.C).toContinuousLinearMap) (E d)))
        Filter.atTop (nhds 0) :=
  exists_observerError_readout_tendsto_of_dualCondition sys.C sys.A E H h.2

end PrimalObserverReadout

end LinearSystem

/-! ### The transpose-exponential bridge and the primal observer readout

The syntactic bridge recorded in the previous handoff is now complete.

* `LinearMap.exp_smul_dualMap_eq` is the operator identity
  `exp (t • Tᵀ) = (exp (t • T))ᵀ` for a real endomorphism `T`. It is proved by
  bundling the algebraic transpose as the ring homomorphism
  `LinearMap.dualMapRingHom` into the multiplicative opposite (the transpose is
  an algebra anti-homomorphism, `(S ∘ R)ᵀ = Rᵀ ∘ Sᵀ`), applying
  `NormedSpace.map_exp`, and removing the opposite with `NormedSpace.exp_op`.
  `LinearMap.exp_smul_dualMap_apply` is the equivalent pointwise pairing form
  `(exp (t • Tᵀ) φ) x = φ ((exp (t • T)) x)`.
* `LinearSystem.exists_observerError_readout_tendsto_of_dualCondition`
  converts the accepted dual observer-error readout decay into the primal
  statement `H (exp (t • (A - L.comp C)) (E d)) → 0` for every disturbance
  direction `d`, with `L` the observer gain in the contract's `A - L C`
  convention. The pairing identifies the transposed readout with
  `z (H (exp (t • (A - L C)) (E d)))` for every functional `z`, and the
  finite-dimensional `Module.finBasis` coordinate argument upgrades the
  coordinatewise convergence supplied by the algebraic dual to norm convergence.
* `LinearSystem.exists_observerError_readout_tendsto_of_externalStabilizationConditions`
  packages the same conclusion under the full Corollary 6.22 subspace
  conditions `ExternalStabilizationConditions`.

The exact-zero (decoupling) and stable-nonzero (decay) readings remain distinct:
this layer proves only the decay of the observer-error readout; it does not
collapse it into the identically-zero external-response predicate. -/
