/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.DisturbanceDecoupling
public import DynamicalSystems.Linear.Stabilization
public import DynamicalSystems.Linear.Trajectory
public import DynamicalSystems.Linear.Trajectories
public import Mathlib.MeasureTheory.Integral.ExpDecay
public import Mathlib.Analysis.Normed.Module.HahnBanach

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
trajectory/spectral direction — a merely stable *nonzero* transfer function — is
now supported by the formalised quotient-decay bridge
`tendsto_readout_exp_of_isHurwitz_mapQ`, the geometric state-feedback
construction of Lemma 4.38 `exists_feedback_tendsto_readout_of_corollary622`,
and its observer dual
`exists_observerError_readout_tendsto_of_externalStabilizationConditions`; the
full necessary-and-sufficient dynamic-controller form of Corollary 6.22 is not
claimed. In particular the
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
* `LinearSystem.readout_functional_variationOfConstants_eq_expFlow`
* `LinearSystem.not_isOutputStabilizable_of_antistable_readout_functional`
* `LinearSystem.readout_functional_eq_zero_on_unstable_of_isOutputStabilizable`

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

/-- The extended subspace associated with a pair `(S,V)` in Theorem 6.18:
`{(s + v, v) | s ∈ S, v ∈ V}`. -/
def extendedPairSubspace (S V : Submodule 𝕜 X) : Submodule 𝕜 (X × X) :=
  LinearMap.range
    (LinearMap.prod (S.subtype.coprod V.subtype)
      (V.subtype.comp (LinearMap.snd 𝕜 S V)))

/-- Elementwise description of the extended subspace of a `(C,A,B)`-pair. -/
theorem mem_extendedPairSubspace (S V : Submodule 𝕜 X) (p : X × X) :
    p ∈ extendedPairSubspace S V ↔
      ∃ s ∈ S, ∃ v ∈ V, p = (s + v, v) := by
  constructor
  · rintro ⟨⟨s, v⟩, h⟩
    refine ⟨s, s.2, v, v.2, ?_⟩
    simpa [extendedPairSubspace, LinearMap.coprod_apply] using h.symm
  · rintro ⟨s, hs, v, hv, rfl⟩
    exact ⟨(⟨s, hs⟩, ⟨v, hv⟩), by
      ext <;> simp [LinearMap.coprod_apply]⟩

/-- Nested `(S,V)` pairs give nested extended subspaces. -/
theorem extendedPairSubspace_mono {S₁ S₂ V₁ V₂ : Submodule 𝕜 X}
    (hS : S₁ ≤ S₂) (hV : V₁ ≤ V₂) :
    extendedPairSubspace S₁ V₁ ≤ extendedPairSubspace S₂ V₂ := by
  intro p hp
  obtain ⟨s, hs, v, hv, rfl⟩ := (mem_extendedPairSubspace S₁ V₁ p).mp hp
  exact (mem_extendedPairSubspace S₂ V₂ _).mpr ⟨s, hS hs, v, hV hv, rfl⟩

/-- The state-disturbance image lies in the extended pair whenever `im E ≤ S`. -/
theorem disturbanceMap_range_le_extendedPairSubspace
    (sys : LinearSystem 𝕜 X U Y) (ctrl : DynamicController 𝕜 X Y U)
    (E : D →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z) (S V : Submodule 𝕜 X)
    (hE : LinearMap.range E ≤ S) :
    LinearMap.range (cabPairInterconnection sys ctrl E H).disturbanceMap ≤
      extendedPairSubspace S V := by
  rintro _ ⟨d, rfl⟩
  exact (mem_extendedPairSubspace S V _).mpr
    ⟨E d, hE ⟨d, rfl⟩, 0, V.zero_mem, by simp [cabPairInterconnection]⟩

/-- The extended pair is invisible to the controlled output when both
component subspaces lie in `ker H`. -/
theorem extendedPairSubspace_le_outputMap_ker
    (sys : LinearSystem 𝕜 X U Y) (ctrl : DynamicController 𝕜 X Y U)
    (E : D →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z) (S V : Submodule 𝕜 X)
    (hS : S ≤ LinearMap.ker H) (hV : V ≤ LinearMap.ker H) :
    extendedPairSubspace S V ≤
      LinearMap.ker (cabPairInterconnection sys ctrl E H).outputMap := by
  intro p hp
  obtain ⟨s, hs, v, hv, rfl⟩ := (mem_extendedPairSubspace S V p).mp hp
  change H (s + v) = 0
  rw [map_add, LinearMap.mem_ker.mp (hS hs), LinearMap.mem_ker.mp (hV hv), zero_add]

/-- Controller-state/error coordinates `(x,w) ↦ (w,x-w)`. In these coordinates
the extended pair `Vₑ(S,V)` becomes the product `V × S`. -/
def controllerStateErrorEquiv (X : Type*) [AddCommGroup X] [Module 𝕜 X] :
    (X × X) ≃ₗ[𝕜] (X × X) where
  toFun p := (p.2, p.1 - p.2)
  invFun p := (p.1 + p.2, p.1)
  left_inv p := by rcases p with ⟨x, w⟩; simp
  right_inv p := by rcases p with ⟨w, e⟩; simp
  map_add' p q := by
    rcases p with ⟨x, w⟩
    rcases q with ⟨y, v⟩
    ext <;> simp
    abel
  map_smul' c p := by
    rcases p with ⟨x, w⟩
    ext <;> simp [smul_sub]

/-- The coordinate change identifies the book's extended pair with the
product of its two component subspaces. -/
theorem controllerStateErrorEquiv_map_extendedPairSubspace (S V : Submodule 𝕜 X) :
    (extendedPairSubspace S V).map (controllerStateErrorEquiv (𝕜 := 𝕜) X).toLinearMap =
      Submodule.prod V S := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨s, hs, v, hv, rfl⟩ := (mem_extendedPairSubspace S V q).mp hq
    change v ∈ V ∧ (s + v - v) ∈ S
    exact ⟨hv, by simpa using hs⟩
  · intro hp
    obtain ⟨v, s⟩ := p
    change v ∈ V ∧ s ∈ S at hp
    refine ⟨(s + v, v), (mem_extendedPairSubspace S V _).mpr
      ⟨s, hp.2, v, hp.1, rfl⟩, ?_⟩
    simp [controllerStateErrorEquiv]

/-- The two invariant subspaces of Lemma 6.21 are instances of this
invariance criterion for the controller with `N = 0`. Besides preservation by
the feedback and injection gains, it only needs `A S ≤ V`. -/
theorem extendedPairSubspace_invariant_cabPairController_zero
    (sys : LinearSystem 𝕜 X U Y) (hD : sys.D = 0)
    (E : D →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z)
    (S V : Submodule 𝕜 X) (F : X →ₗ[𝕜] U) (G : Y →ₗ[𝕜] X)
    (hSV : S ≤ V) (hAS : Submodule.map sys.A S ≤ V)
    (hF : Submodule.map (sys.A + sys.B.comp F) V ≤ V)
    (hG : Submodule.map (sys.A + G.comp sys.C) S ≤ S)
    (hwp : (cabPairInterconnection sys (cabPairController sys F G 0) E H).IsWellPosed) :
    Submodule.map
      ((cabPairInterconnection sys (cabPairController sys F G 0) E H).closedLoopMap hwp)
      (extendedPairSubspace S V) ≤ extendedPairSubspace S V := by
  let ic : DynamicInterconnection 𝕜 X U Y X D Z :=
    cabPairInterconnection sys (cabPairController sys F G 0) E H
  have hcl0 : ∀ x : X, ic.closedLoopMap hwp (x, 0) =
      (sys.A x, -G (sys.C x)) := by
    intro x
    rw [ic.closedLoopMap_of_D_eq_zero hD hwp (x, 0)]
    ext <;> simp [ic, cabPairInterconnection, cabPairController,
      LinearMap.add_apply, LinearMap.comp_apply]
  have hcl2 : ∀ x : X, ic.closedLoopMap hwp (x, x) =
      ((sys.A + sys.B.comp F) x, (sys.A + sys.B.comp F) x) := by
    intro x
    rw [ic.closedLoopMap_of_D_eq_zero hD hwp (x, x)]
    ext <;> simp only [ic, cabPairInterconnection, cabPairController, LinearMap.add_apply,
      LinearMap.sub_apply, LinearMap.comp_apply, map_sub] <;> abel
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨s, hs, v, hv, rfl⟩ := (mem_extendedPairSubspace S V p).mp hp
  have hGs : (sys.A + G.comp sys.C) s ∈ S := hG ⟨s, hs, rfl⟩
  have hnegGs : -G (sys.C s) ∈ V := by
    have hdiff : sys.A s - (sys.A + G.comp sys.C) s ∈ V :=
      V.sub_mem (hAS ⟨s, hs, rfl⟩) (hSV hGs)
    simpa [LinearMap.add_apply, LinearMap.comp_apply] using hdiff
  have hFv : (sys.A + sys.B.comp F) v ∈ V := hF ⟨v, hv, rfl⟩
  have hdecomp : (s + v, v) = (s, 0) + (v, v) := by
    ext <;> simp
  have himage : ic.closedLoopMap hwp (s + v, v) =
      ((sys.A + G.comp sys.C) s +
          (-G (sys.C s) + (sys.A + sys.B.comp F) v),
        -G (sys.C s) + (sys.A + sys.B.comp F) v) := by
    rw [hdecomp, map_add, hcl0, hcl2]
    ext <;> simp [LinearMap.add_apply, LinearMap.comp_apply]
  rw [himage]
  exact (mem_extendedPairSubspace S V _).mpr
    ⟨(sys.A + G.comp sys.C) s, hGs,
      -G (sys.C s) + (sys.A + sys.B.comp F) v, V.add_mem hnegGs hFv, rfl⟩

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

omit [FiniteDimensional ℝ X] in
/-- In controller-state/error coordinates, the `N = 0` closed loop has
diagonal blocks `A + B F` and `A + G C` and cross block `-G C`. The extended
pair `Vₑ(S,V)` is exactly `V × S` in these same coordinates. -/
theorem cabPairController_closedLoopMap_controllerStateError_conj
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (F : X →ₗ[ℝ] U) (G : Y →ₗ[ℝ] X)
    (hwp : (cabPairInterconnection sys (cabPairController sys F G 0) E H).IsWellPosed) :
    (controllerStateErrorEquiv (𝕜 := ℝ) X).conj
      ((cabPairInterconnection sys (cabPairController sys F G 0) E H).closedLoopMap hwp) =
      LinearMap.blockOperator (sys.A + sys.B.comp F) (-(G.comp sys.C))
        (sys.A + G.comp sys.C) := by
  let ic : DynamicInterconnection ℝ X U Y X D Z :=
    cabPairInterconnection sys (cabPairController sys F G 0) E H
  change (controllerStateErrorEquiv (𝕜 := ℝ) X).conj (ic.closedLoopMap hwp) = _
  apply LinearMap.ext
  intro p
  obtain ⟨w, e⟩ := p
  rw [LinearEquiv.conj_apply_apply]
  change (controllerStateErrorEquiv (𝕜 := ℝ) X)
      (ic.closedLoopMap hwp (w + e, w)) = _
  rw [ic.closedLoopMap_of_D_eq_zero hD hwp (w + e, w)]
  apply Prod.ext
  · simp [controllerStateErrorEquiv, ic, cabPairInterconnection,
      cabPairController, LinearMap.blockOperator_apply, LinearMap.add_apply,
      LinearMap.comp_apply, map_add, LinearMap.neg_apply]
    abel
  · simp [controllerStateErrorEquiv, ic, cabPairInterconnection,
      cabPairController, LinearMap.blockOperator_apply, LinearMap.add_apply,
      LinearMap.comp_apply, map_add, LinearMap.neg_apply]
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
from the exact external zero response. The trajectory/spectral stable-nonzero
direction is now supported by the formalised quotient-decay bridge
`tendsto_readout_exp_of_isHurwitz_mapQ` and the geometric state-feedback
construction `exists_feedback_tendsto_readout_of_corollary622`, with observer dual
`exists_observerError_readout_tendsto_of_externalStabilizationConditions`; the
full necessary-and-sufficient dynamic-controller form of Corollary 6.22 is not
claimed. -/

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

/-! ### Stable nonzero external response versus exact zero response

The two external-behaviour notions are kept apart:

* `ExternalStability` asks for a controller making the forced external response
  *identically zero* (external disturbance decoupling);
* `StableNonzeroExternalResponse` asks only that the forced external response
  *decay to zero*, the state-space counterpart of stability of the closed-loop
  transfer function `G_Κ(s) = H_e (s I - A_e)⁻¹ B_e`
  (Trentelman–Stoorvogel–Hautus, Definition 6.19).

The second is strictly weaker: a nonzero but exponentially decaying impulse
response satisfies it and not the first. The exact-zero predicate implies the
stable-nonzero one (`externalStability_imp_stableNonzeroExternalResponse`); the
converse is not claimed, and the exact-zero geometric certificate
`GeometricCertificate` is correspondingly stronger than the Corollary 6.22
conditions. -/

/-- **Stable nonzero external response.** There is a finite-dimensional dynamic
measurement-feedback controller (state space `X`, strictly proper
`cabPairInterconnection`) whose forced external response decays to zero in every
disturbance direction: `t ↦ H_e e^{t A_e} B_e d → 0` as `t → +∞`.

This is the state-space form of stability of the closed-loop transfer function
`G_Κ(s)` (Trentelman–Stoorvogel–Hautus, Definition 6.19). It is the *stable
nonzero* reading and is explicitly not identified with the identically-zero
response `ExternalStability`; the latter implies it, while a decaying nonzero
impulse response witnesses the strict difference. -/
noncomputable def StableNonzeroExternalResponse (sys : LinearSystem ℝ X U Y)
    (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) : Prop :=
  ∃ ctrl : DynamicController ℝ X Y U,
    ∀ d : D, Filter.Tendsto
      (fun t : ℝ => (cabPairInterconnection sys ctrl E H).externalResponse
        ((cabPairInterconnection sys ctrl E H).isWellPosed_of_D_eq_zero hD) t d)
      Filter.atTop (nhds 0)

omit [FiniteDimensional ℝ D] in
/-- **Exact zero response implies stable nonzero response.** If a controller
makes the forced external response identically zero then a fortiori it decays to
zero, so `ExternalStability` entails `StableNonzeroExternalResponse`.

The converse is false in general: a nonzero exponentially decaying impulse
response is stable but not identically zero, which is why the two predicates are
kept distinct (and why the exact-zero geometric certificate `GeometricCertificate`
is strictly stronger than the Corollary 6.22 conditions). -/
theorem externalStability_imp_stableNonzeroExternalResponse
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : ExternalStability sys hD E H) :
    StableNonzeroExternalResponse sys hD E H := by
  obtain ⟨ctrl, hz⟩ := h
  refine ⟨ctrl, fun d => ?_⟩
  have hfun : (fun t : ℝ => (cabPairInterconnection sys ctrl E H).externalResponse
      ((cabPairInterconnection sys ctrl E H).isWellPosed_of_D_eq_zero hD) t d) =
      fun _ : ℝ => (0 : Z) := by
    funext t
    exact hz t d
  rw [hfun]
  exact tendsto_const_nhds

omit [FiniteDimensional ℝ D] in
/-- **Stable nonzero response from Hurwitz cabPair gains.** If the
state-feedback block `A + B F` and the observer-error block `A + G C` of the
controller (6.7) are both Hurwitz then its forced external response decays, so
the strictly proper plant admits a stable (nonzero) external response.

This reuses the accepted separation-principle factorization
`isHurwitz_closedLoopMap_cabPairController` and the real Hurwitz decay theorem
`LinearMap.tendsto_exp_of_isHurwitz`; no decay is assumed. -/
theorem stableNonzeroExternalResponse_of_isHurwitz_cabPair
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (F : X →ₗ[ℝ] U) (G : Y →ₗ[ℝ] X) (N : Y →ₗ[ℝ] U)
    (hF : LinearMap.IsHurwitz (sys.A + sys.B.comp F))
    (hG : LinearMap.IsHurwitz (sys.A + G.comp sys.C)) :
    StableNonzeroExternalResponse sys hD E H := by
  refine ⟨cabPairController sys F G N, fun d => ?_⟩
  let ic : DynamicInterconnection ℝ X U Y X D Z :=
    cabPairInterconnection sys (cabPairController sys F G N) E H
  have hwp : ic.IsWellPosed := ic.isWellPosed_of_D_eq_zero hD
  change Filter.Tendsto (fun t : ℝ => ic.externalResponse hwp t d) Filter.atTop (nhds 0)
  have hH : LinearMap.IsHurwitz (ic.closedLoopMap hwp) :=
    isHurwitz_closedLoopMap_cabPairController sys hD E H F G N hwp hF hG
  have hflow : (fun t : ℝ => ic.externalResponse hwp t d) =
      fun t : ℝ => ic.outputMap (NormedSpace.exp
        (t • (ic.closedLoopMap hwp).toContinuousLinearMap)
        (ic.disturbanceMapWithF hwp d)) := by
    funext t
    rw [ic.externalResponse_apply, ic.closedLoopSystem_expFlow_eq hwp t]
  rw [hflow]
  have htend : Filter.Tendsto (fun t : ℝ => NormedSpace.exp
      (t • (ic.closedLoopMap hwp).toContinuousLinearMap)
      (ic.disturbanceMapWithF hwp d)) Filter.atTop (nhds 0) :=
    LinearMap.tendsto_exp_of_isHurwitz (ic.closedLoopMap hwp) hH _
  have hcont := (ic.outputMap.toContinuousLinearMap.continuous.tendsto 0).comp htend
  rw [map_zero] at hcont
  exact hcont

section StableNonzeroExistence

variable [FiniteDimensional ℝ Y]

omit [FiniteDimensional ℝ D] in
/-- **Existence of a stable-nonzero external response.** A controllable and
observable strictly proper plant admits a dynamic measurement-feedback
controller whose forced external response decays. The gains are those of
`exists_hurwitz_cabPair_gains`, so the predicate is not vacuous. -/
theorem exists_stableNonzeroExternalResponse_cabPair_gains
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (hcont : LinearMap.IsControllable sys.A sys.B)
    (hobs : LinearMap.IsObservable sys.C sys.A) :
    StableNonzeroExternalResponse sys hD E H := by
  obtain ⟨F, G, hF, hG⟩ := exists_hurwitz_cabPair_gains sys hcont hobs
  exact stableNonzeroExternalResponse_of_isHurwitz_cabPair sys hD E H F G 0 hF hG

end StableNonzeroExistence

/-! ### Handoff: the exact remaining blocker for the full stable-nonzero iff

The Corollary 6.22 stable-nonzero criterion would read

`StableNonzeroExternalResponse sys hD E H ↔ ExternalStabilizationConditions sys E H`.

Its two directions split as follows.

* **Sufficiency** (`ExternalStabilizationConditions → StableNonzeroExternalResponse`).
  The state-feedback half is `exists_feedback_tendsto_readout_of_corollary622`
  (`H e^{t(A+BF)} (E d) → 0`) and the observer half is
  `exists_observerError_readout_tendsto_of_externalStabilizationConditions`
  (`H e^{t(A-LC)} (E d) → 0`). The generic forced-readout consumer
  `externalResponse_tendsto_zero_of_quotient_hurwitz` is also proved below.
  The remaining step is to construct the extended invariant pair `(Ve, We)`
  of Lemma 6.21 for the controller (6.39), containing the disturbance image,
  annihilated by the external readout on `Ve`, and with Hurwitz quotient
  `We / Ve` as in Theorem 6.18. The current feedback/observer theorems export
  readout decay, but not yet the quotient data needed for this assembly.

* **Necessity** (`StableNonzeroExternalResponse → ExternalStabilizationConditions`).
  The source derives `im E ⊂ V*(ker H) + Xstab` from the definition of `W_g(ker H)`
  as the set of states from which an open-loop control can make the controlled
  output decay, together with Theorem 4.37 (`W_g(ker H) = V*(ker H) + Xstab`),
  and then dualises the argument for `S*(im E) ∩ Xdet ⊂ ker H`. The missing
  finite-Bohl forcing-image version of this open-loop characterisation is now
  `finiteBohlWBridge`. Applying it to a generic real controller still requires
  real-to-complexification transport (the controller's state and input may have
  odd real dimension), plant-trajectory extraction from the closed-loop orbit,
  and a transposed closed-loop realization for the dual condition. The exact-zero
  case already has both halves
  (`externalStabilizationConditions_of_externalStability`), but it rests on the
  stronger zero-response premise and does not cover the merely stable response.

Until these two statements are available the genuine iff is not claimed; only the
strictly weaker exact-zero criterion (`externalStability_iff_geometricCertificate_and_conditions`)
and the stable-nonzero synthesis under the additional Hurwitz hypothesis
(`stableNonzeroExternalResponse_of_isHurwitz_cabPair`,
`exists_stableNonzeroExternalResponse_cabPair_gains`) are asserted. -/

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

The feedback construction of Lemma 4.38 — producing `F` from
`im E ≤ V*(ker H) + Xstab` so that `σ(A_F | W_g/V*) ⊂ C_g` — is formalised as
`exists_feedback_tendsto_readout_of_geometricCondition` and its Corollary 6.22
specialisation `exists_feedback_tendsto_readout_of_corollary622`; the observer
dual is `exists_observerError_readout_tendsto_of_externalStabilizationConditions`.
These theorems supply the analytic half of the bridge with the spectral
hypothesis explicit. -/

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
geometric condition `im E ≤ V*(ker H) + Xstab` (Lemma 4.38) is supplied
separately by `exists_feedback_tendsto_readout_of_geometricCondition`; it is not
assumed here. -/
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

/-! ## Forced/convolution quotient decay for the dynamic closed loop

The accepted bridge `tendsto_readout_exp_of_isHurwitz_quotient_on` is stated with
a feedback term `A + B F`; the dynamic closed loop is an autonomous map, so this
section records the feedback-free specialisation
`tendsto_readout_exp_of_isHurwitz_mapQ_on` and then applies it to the forced
disturbance-to-output channel of a dynamic measurement-feedback interconnection.

The resulting wrapper `externalResponse_tendsto_zero_of_quotient_hurwitz` is the
smallest theorem that can feed `StableNonzeroExternalResponse`: it needs only an
unobservable closed-loop-invariant subspace `Ve ⊆ ker H_e`, a closed-loop-
invariant window `We ⊇ im B_e` carrying the disturbance image, and the Hurwitz
property of the induced map on `We / Ve`. No global Hurwitz property of the
extended map is assumed, so the *stable-nonzero* forced response is obtained from
the same quotient spectral data that the geometric Corollary 6.22 construction
supplies for the two separation-principle blocks. The identically-zero response
(`ExternalStability`) is not identified with this decay statement.

The general forced output of the channel is the convolution of the impulse
response `s ↦ H_e e^{s A_e} B_e` with the locally integrable disturbance; the
zero-initial-state response `externalResponse` is exactly that impulse response,
so its decay is the convolution kernel statement needed for external stability.
Strict-properness (`D = 0`) enters only through the well-posedness proof; the
well-posed *feedthrough* case is covered by keeping `IsWellPosed` explicit. -/

section FeedbackFreeQuotientDecay

variable {X D Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- **Feedback-free quotient window decay.** If `A` preserves a subspace `V` on
which the readout `H` vanishes and an intermediate window `W ⊇ V`, if the
disturbance image `im E` lies in `W`, and if the induced map on `W ⧸ V` is
Hurwitz, then the readout of every `A`-trajectory starting in `im E` decays:
`t ↦ H (exp (t A) (E d)) → 0`.

This is the feedback-free form of `tendsto_readout_exp_of_isHurwitz_quotient_on`:
the state stays in the closed-loop-invariant window `W`, the readout is blind to
the invariant subspace `V`, and only `W ⧸ V` carries the spectral hypothesis. It
is the analytic content of Trentelman–Stoorvogel–Hautus, Lemma 4.35, used here
for the autonomous extended closed loop of equation (6.12). -/
theorem tendsto_readout_exp_of_isHurwitz_mapQ_on
    (A : X →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) (E : D →ₗ[ℝ] X)
    (V W : Submodule ℝ X)
    (hW : Submodule.map A W ≤ W)
    (hV : Submodule.map A V ≤ V)
    (hVH : V ≤ LinearMap.ker H)
    (hE : LinearMap.range E ≤ W)
    (hQ : LinearMap.IsHurwitz
      (Submodule.mapQ (V.comap W.subtype) (V.comap W.subtype)
        (A.restrict (fun x hx => hW ⟨x, hx, rfl⟩))
        (fun x hx => hV ⟨(x : X), hx, rfl⟩)))
    (d : D) :
    Tendsto (fun t : ℝ => H (NormedSpace.exp
      (t • A.toContinuousLinearMap) (E d))) atTop (nhds 0) := by
  let VW : Submodule ℝ W := V.comap W.subtype
  let AW : W →ₗ[ℝ] W := A.restrict (fun x hx => hW ⟨x, hx, rfl⟩)
  let HW : W →ₗ[ℝ] Z := H.comp W.subtype
  have hVW' : VW ≤ VW.comap AW := by
    intro x hx
    change A (x : X) ∈ V
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
      A.toContinuousLinearMap.comp W.subtype.toContinuousLinearMap := by
    ext x
    rfl
  have hflow : ∀ t : ℝ,
      W.subtype.toContinuousLinearMap
        (NormedSpace.exp (t • AW.toContinuousLinearMap) ⟨E d, hxW⟩) =
      NormedSpace.exp (t • A.toContinuousLinearMap) (E d) := by
    intro t
    have := clm_map_exp_smul W.subtype.toContinuousLinearMap AW.toContinuousLinearMap
      A.toContinuousLinearMap hsub t ⟨E d, hxW⟩
    simpa using this
  have hgoal : (fun t : ℝ => H (NormedSpace.exp
        (t • A.toContinuousLinearMap) (E d))) =
      fun t : ℝ => HW (NormedSpace.exp (t • AW.toContinuousLinearMap) ⟨E d, hxW⟩) := by
    funext t
    rw [← hflow t]
    rfl
  rw [hgoal]
  exact hmain

end FeedbackFreeQuotientDecay

section ForcedExternalResponseDecay

variable {X U Y W D Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [AddCommGroup U] [Module ℝ U]
variable [AddCommGroup Y] [Module ℝ Y]
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable (ic : DynamicInterconnection ℝ X U Y W D Z)

/-- **Forced external readout decay from a quotient-Hurwitz window.** For a
well-posed dynamic interconnection, if the extended closed-loop map preserves a
subspace `Ve` on which the controlled output `He` vanishes, if it preserves a
window `We ⊇ Ve` that contains the total disturbance image `im Be`, and if the
induced map `We ⧸ Ve` is Hurwitz, then the forced disturbance-to-output response
decays to zero in every disturbance direction,
`t ↦ H_e e^{t A_e} B_e d → 0`.

This is the smallest theorem that can feed `StableNonzeroExternalResponse`: it
reuses the accepted quotient-spectrum decay
`tendsto_readout_exp_of_isHurwitz_mapQ_on` on the extended state space and the
variation-of-constants identification of the forced channel with the closed-loop
exponential `closedLoopSystem_expFlow_eq`. It is stated for a general
well-posed interconnection so that both the strictly proper and the feedthrough
well-posedness hypotheses are explicit. -/
theorem externalResponse_tendsto_zero_of_quotient_hurwitz
    (h : ic.IsWellPosed) (Ve We : Submodule ℝ (X × W))
    (hWe : Submodule.map (ic.closedLoopMap h) We ≤ We)
    (hVe : Submodule.map (ic.closedLoopMap h) Ve ≤ Ve)
    (hVeH : Ve ≤ LinearMap.ker ic.outputMap)
    (hEe : LinearMap.range (ic.disturbanceMapWithF h) ≤ We)
    (hQ : LinearMap.IsHurwitz
      (Submodule.mapQ (Ve.comap We.subtype) (Ve.comap We.subtype)
        ((ic.closedLoopMap h).restrict (fun x hx => hWe ⟨x, hx, rfl⟩))
        (fun x hx => hVe ⟨(x : X × W), hx, rfl⟩)))
    (d : D) :
    Filter.Tendsto (fun t : ℝ => ic.externalResponse h t d) Filter.atTop (nhds 0) := by
  have hmain := tendsto_readout_exp_of_isHurwitz_mapQ_on
    (ic.closedLoopMap h) ic.outputMap (ic.disturbanceMapWithF h) Ve We
    hWe hVe hVeH hEe hQ d
  have hfun : (fun t : ℝ => ic.externalResponse h t d) =
      fun t : ℝ => ic.outputMap (NormedSpace.exp
        (t • (ic.closedLoopMap h).toContinuousLinearMap)
        (ic.disturbanceMapWithF h d)) := by
    funext t
    rw [ic.externalResponse_apply, ic.closedLoopSystem_expFlow_eq h t]
  rw [hfun]
  exact hmain

/-- **Forced external readout decay from a globally Hurwitz closed loop.** The
degenerate window `Ve = ⊥`, `We = ⊤` specialises the quotient bridge to a
globally Hurwitz extended map, recovering the forced-response decay used by
`stableNonzeroExternalResponse_of_isHurwitz_cabPair` directly from the
quotient-spectrum API. -/
theorem externalResponse_tendsto_zero_of_isHurwitz_closedLoopMap
    (h : ic.IsWellPosed) (hH : LinearMap.IsHurwitz (ic.closedLoopMap h)) (d : D) :
    Filter.Tendsto (fun t : ℝ => ic.externalResponse h t d) Filter.atTop (nhds 0) := by
  have hflow : (fun t : ℝ => ic.externalResponse h t d) =
      fun t : ℝ => ic.outputMap (NormedSpace.exp
        (t • (ic.closedLoopMap h).toContinuousLinearMap)
        (ic.disturbanceMapWithF h d)) := by
    funext t
    rw [ic.externalResponse_apply, ic.closedLoopSystem_expFlow_eq h t]
  rw [hflow]
  have htend : Filter.Tendsto (fun t : ℝ => NormedSpace.exp
      (t • (ic.closedLoopMap h).toContinuousLinearMap)
      (ic.disturbanceMapWithF h d)) Filter.atTop (nhds 0) :=
    LinearMap.tendsto_exp_of_isHurwitz (ic.closedLoopMap h) hH _
  have hcont := (ic.outputMap.toContinuousLinearMap.continuous.tendsto 0).comp htend
  rw [map_zero] at hcont
  exact hcont

end ForcedExternalResponseDecay

section StableNonzeroQuotientBridge

variable {X U Y D Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [AddCommGroup U] [Module ℝ U]
variable [AddCommGroup Y] [Module ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- **Stable-nonzero external response from a quotient-Hurwitz dynamic loop.**
For a strictly proper plant, a dynamic controller (with state space `X`) whose
extended closed loop admits an unobservable invariant subspace `Ve` and an
invariant window `We` with `im B_e ⊆ We`, `Ve ≤ ker H_e` and `We ⧸ Ve` Hurwitz,
realises the stable-nonzero external response. The well-posedness is automatic
from strict properness (`isWellPosed_of_D_eq_zero`); the decay is the forced
readout bridge `externalResponse_tendsto_zero_of_quotient_hurwitz`.

This is the *sufficiency* skeleton of the stable-nonzero Corollary 6.22
criterion: the geometric construction supplies `Ve`, `We` from the two
separation-principle blocks, and the quotient-Hurwitz hypothesis is the spectral
input. The exact-zero response is not used or claimed. -/
theorem stableNonzeroExternalResponse_of_quotient_hurwitz
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (ctrl : DynamicController ℝ X Y U) (Ve We : Submodule ℝ (X × X))
    (hWe : Submodule.map
      ((cabPairInterconnection sys ctrl E H).closedLoopMap
        ((cabPairInterconnection sys ctrl E H).isWellPosed_of_D_eq_zero hD)) We ≤ We)
    (hVe : Submodule.map
      ((cabPairInterconnection sys ctrl E H).closedLoopMap
        ((cabPairInterconnection sys ctrl E H).isWellPosed_of_D_eq_zero hD)) Ve ≤ Ve)
    (hVeH : Ve ≤ LinearMap.ker (cabPairInterconnection sys ctrl E H).outputMap)
    (hEe : LinearMap.range
      ((cabPairInterconnection sys ctrl E H).disturbanceMapWithF
        ((cabPairInterconnection sys ctrl E H).isWellPosed_of_D_eq_zero hD)) ≤ We)
    (hQ : LinearMap.IsHurwitz
      (Submodule.mapQ (Ve.comap We.subtype) (Ve.comap We.subtype)
        (((cabPairInterconnection sys ctrl E H).closedLoopMap
          ((cabPairInterconnection sys ctrl E H).isWellPosed_of_D_eq_zero hD)).restrict
            (fun x hx => hWe ⟨x, hx, rfl⟩))
        (fun x hx => hVe ⟨(x : X × X), hx, rfl⟩))) :
    StableNonzeroExternalResponse sys hD E H := by
  let ic : DynamicInterconnection ℝ X U Y X D Z := cabPairInterconnection sys ctrl E H
  have h : ic.IsWellPosed := ic.isWellPosed_of_D_eq_zero hD
  refine ⟨ctrl, fun d => ?_⟩
  change Filter.Tendsto (fun t : ℝ => ic.externalResponse h t d) Filter.atTop (nhds 0)
  exact externalResponse_tendsto_zero_of_quotient_hurwitz ic h Ve We hWe hVe hVeH hEe hQ d

/-- **Stable-nonzero external response from a globally Hurwitz dynamic loop.**
The generic controller form of the accepted
`stableNonzeroExternalResponse_of_isHurwitz_cabPair`: any dynamic controller
whose strictly proper extended closed loop is Hurwitz realises the
stable-nonzero external response. It is the `Ve = ⊥`, `We = ⊤` case of
`stableNonzeroExternalResponse_of_quotient_hurwitz` read through the direct
Hurwitz-exp decay, and it certifies that the quotient bridge is not vacuous. -/
theorem stableNonzeroExternalResponse_of_isHurwitz_closedLoopMap
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (ctrl : DynamicController ℝ X Y U)
    (hH : LinearMap.IsHurwitz
      ((cabPairInterconnection sys ctrl E H).closedLoopMap
        ((cabPairInterconnection sys ctrl E H).isWellPosed_of_D_eq_zero hD))) :
    StableNonzeroExternalResponse sys hD E H := by
  let ic : DynamicInterconnection ℝ X U Y X D Z := cabPairInterconnection sys ctrl E H
  have h : ic.IsWellPosed := ic.isWellPosed_of_D_eq_zero hD
  refine ⟨ctrl, fun d => ?_⟩
  change Filter.Tendsto (fun t : ℝ => ic.externalResponse h t d) Filter.atTop (nhds 0)
  exact externalResponse_tendsto_zero_of_isHurwitz_closedLoopMap ic h hH d

end StableNonzeroQuotientBridge

/-! ## The geometric feedback construction: reduction lemmas

Trentelman–Stoorvogel–Hautus, Lemma 4.38 constructs a state feedback `F` from
the geometric condition `im E ≤ W_g(ker H) = V*(ker H) + Xstab(A, B)` of
Theorem 4.37, preserving the controlled-invariant witness `V*` and making the
induced quotient map on `W_g / V*` Hurwitz. Theorem 4.39 then derives external
stability of the closed-loop transfer function through the analytic Lemma 4.35,
already formalised as
`tendsto_readout_exp_of_isHurwitz_quotient_on`.

The construction of `F` is formalised by
`exists_feedback_tendsto_readout_of_geometricCondition` and
`exists_feedback_tendsto_readout_of_corollary622`.
This section also records the structural facts about the
geometric subspace `W = V*(ker H) ⊔ Xstab(A, B)` on which Lemma 4.38 and
Lemma 4.35 operate:

* `range_le_sup_stabilizableSubspace`: the input image `im B` lies in `W`, so
  `W` is a strongly invariant subspace once it is invariant;
* `map_sup_stabilizableSubspace_le`: `W` is `A`-invariant, and
  `map_add_feedback_sup_stabilizableSubspace_le`: any feedback that preserves the
  controlled-invariant witness `V` also preserves `W`.

These lemmas supply `hW` and `range E ≤ W` for the quotient-decay bridge used by
the construction below; the construction of that `F` from the geometric
inclusion is provided by `exists_feedback_tendsto_readout_of_geometricCondition`
and its Corollary 6.22 specialisation. -/

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
`im E ≤ V ⊔ Xstab(A, B)` (Lemma 4.38), together with the quotient-Hurwitz
property, is produced by `exists_feedback_tendsto_readout_of_geometricCondition`;
here it is taken as data. -/
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

/-- **Quotient-Hurwitz feedback from the geometric condition.** Let `V` be
controlled invariant modulo the input image. There is a feedback preserving `V`
whose induced closed-loop map on `(V ⊔ Xstab(A, B)) / V` is Hurwitz.

This exposes the spectral witness in the construction underlying the external
stabilization theorem below. -/
theorem exists_feedback_isHurwitz_quotient_of_geometricCondition
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (V : Submodule ℝ X)
    (hV : Submodule.map A V ≤ V ⊔ LinearMap.range B) :
    ∃ F : X →ₗ[ℝ] U,
      Nonempty {hFV : Submodule.map (A + B.comp F) V ≤ V //
      let W : Submodule ℝ X := V ⊔ LinearMap.stabilizableSubspace A B
      let hWinv : ∀ x ∈ W, (A + B.comp F) x ∈ W := fun x hx =>
        map_add_feedback_sup_stabilizableSubspace_le A B F hFV ⟨x, hx, rfl⟩
      let VW : Submodule ℝ W := V.comap W.subtype
      let hmap : ∀ x ∈ VW, ((A + B.comp F).restrict hWinv) x ∈ VW := fun x hx => by
        change ((A + B.comp F) (x : X)) ∈ V
        exact hFV ⟨(x : X), hx, rfl⟩
      LinearMap.IsHurwitz (Submodule.mapQ VW VW ((A + B.comp F).restrict hWinv) hmap)} := by
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
  refine ⟨F, ⟨⟨hFV, ?_⟩⟩⟩
  simpa only [W, VW] using hQ

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
  obtain ⟨F, ⟨⟨hFV, hQ⟩⟩⟩ := exists_feedback_isHurwitz_quotient_of_geometricCondition A B V hV
  refine ⟨F, hFV, fun d => ?_⟩
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

/-- Invariance of an annihilator under the transpose implies invariance of the
original subspace under the primal map. -/
theorem map_le_of_dualMap_dualAnnihilator_le (T : X →ₗ[𝕜] X)
    (S : Submodule 𝕜 X)
    (h : Submodule.map T.dualMap S.dualAnnihilator ≤ S.dualAnnihilator) :
    Submodule.map T S ≤ S := by
  rintro _ ⟨x, hx, rfl⟩
  apply (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff S (T x)).mp
  intro φ hφ
  have hTφ : T.dualMap φ ∈ S.dualAnnihilator := h ⟨φ, hφ, rfl⟩
  have hz := (Submodule.mem_dualAnnihilator (W := S) (T.dualMap φ)).mp hTφ x hx
  simpa [LinearMap.dualMap_apply] using hz

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

/-- A feedback on the transposed controlled-invariant subspace gives an
output injection preserving the primal smallest conditioned-invariant
subspace. This is the friend transport used for Lemma 6.21. -/
theorem outputInjection_preserves_conditionedInvariant_of_dual_feedback
    {D : Type*} [AddCommGroup D] [Module 𝕜 D]
    (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (E : D →ₗ[𝕜] X) (G : Y →ₗ[𝕜] X)
    (hV : Submodule.map (A.dualMap + C.dualMap.comp G.dualMap)
      (controlledInvariantSubspace A.dualMap C.dualMap (LinearMap.ker E.dualMap)) ≤
      controlledInvariantSubspace A.dualMap C.dualMap (LinearMap.ker E.dualMap)) :
    Submodule.map (A + G.comp C)
      (conditionedInvariantSubspace C A (LinearMap.range E)) ≤
      conditionedInvariantSubspace C A (LinearMap.range E) := by
  let S := conditionedInvariantSubspace C A (LinearMap.range E)
  have hdual : S.dualAnnihilator =
      controlledInvariantSubspace A.dualMap C.dualMap (LinearMap.ker E.dualMap) := by
    dsimp [S]
    rw [dualAnnihilator_conditionedInvariantSubspace,
      ← LinearMap.ker_dualMap_eq_dualAnnihilator_range]
  have hmap : (A + G.comp C).dualMap =
      A.dualMap + C.dualMap.comp G.dualMap := by
    ext φ x
    simp [LinearMap.dualMap_apply, LinearMap.add_apply, LinearMap.comp_apply]
  apply map_le_of_dualMap_dualAnnihilator_le (A + G.comp C) S
  rw [hdual, hmap]
  exact hV

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

The identification needed to match the primal geometric condition
`im E ≤ V*(ker H) + Xstab(A, B)` is `(X_b(A))ᵃⁿⁿ = X_g(Aᵀ)`, i.e. the transpose
stable/antistable duality; it is provided by the accepted
`dualAnnihilator_unstableSubspace_eq_stableSubspace_dualMap` in
`DynamicalSystems/Linear/Stabilization.lean` and is consumed by
`conditionedInvariant_inf_detectable_le_ker_iff_dualStableCondition` below. -/
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

/-! ### The output-injection duality bridge

The dual output-injection half of Corollary 6.22 is formalised by
`exists_outputInjection_dualReadout_tendsto_of_dualCondition` and
`exists_observerError_readout_tendsto_of_externalStabilizationConditions`.
The antistable annihilator `(X_b(A))ᵃⁿⁿ` is identified with the stable subspace
of the transpose. The stabilizable/stable spaces are available on any
finite-dimensional real vector space through the norm-free API in
`DynamicalSystems/Linear/Stabilization.lean`
(`stableSubspaceOfBasis`, `unstableSubspaceOfBasis`, with
`stableSubspaceOfBasis_finBasis_eq_hurwitzSubspace` recovering the accepted
`hurwitzSubspace` definitionally). The reusable lemma is:

`(unstableSubspace A).dualAnnihilator =
   stableSubspaceOfBasis (Module.finBasis ℝ (Module.Dual ℝ X)) A.dualMap`,

equivalently, after basis independence, `(detectableSubspace C A).dualAnnihilator
= stabilizableSubspace` of the transposed pair. It is accepted as
`dualAnnihilator_unstableSubspace_eq_stableSubspace_dualMap`; the supporting
development is summarised below.

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

The step to the real statement
`(unstableSubspace A).dualAnnihilator =
stableSubspaceOfBasis (Module.finBasis ℝ (Module.Dual ℝ X)) A.dualMap` is the
transport across `IsBaseChange.toDualBaseChange` (base change commutes with the
dual), which is described in the update below. The accepted state-feedback
construction
`exists_feedback_tendsto_readout_of_geometricCondition` is then run on the
transposed pair and the resulting gain transposed back with
`dualMap_surjective`, yielding the observer gain `G` of
Trentelman–Stoorvogel–Hautus Lemma 6.20/6.21 in the observer-gain assembly
below. -/

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

Running the accepted state-feedback construction on the transposed dual pair,
with the roles of the disturbance channel `E` and the controlled output `H`
exchanged, and transposing the resulting gain back with `dualMap_surjective`
yields the observer injection `G` of Trentelman–Stoorvogel–Hautus Lemma 6.20/6.21;
this is formalised in the observer-gain assembly below as
`exists_outputInjection_dualReadout_tendsto_of_dualCondition`, its
observer-error form `exists_observerError_dualReadout_tendsto_of_dualCondition`,
and the primal statements
`exists_observerError_readout_tendsto_of_dualCondition` and
`exists_observerError_readout_tendsto_of_externalStabilizationConditions`.
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

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ D] in
/-- **The observer-side Hurwitz quotient in transpose coordinates.** Under the
output-injection condition of Corollary 6.22, the transpose of an output
injection preserves `V*(ker Eᵀ)` and is Hurwitz on
`(V*(ker Eᵀ) ⊔ Xstab(Aᵀ, Cᵀ)) / V*(ker Eᵀ)`. The disturbance readout image
`im Hᵀ` lies in the numerator. By the annihilator identities, this is the
dual-coordinate form of the quotient `S*(im E) / T_g` in Lemma 6.21. -/
theorem exists_outputInjection_isHurwitz_dualQuotient_of_dualCondition
    (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : LinearMap.conditionedInvariantSubspace C A (LinearMap.range E) ⊓
        LinearMap.detectableSubspace C A ≤ LinearMap.ker H) :
    ∃ G : Y →ₗ[ℝ] X,
      let V := LinearMap.controlledInvariantSubspace A.dualMap C.dualMap
        (LinearMap.ker E.dualMap)
      LinearMap.range H.dualMap ≤ V ⊔
        LinearMap.stabilizableSubspace A.dualMap C.dualMap ∧
      Nonempty {hFV : Submodule.map (A.dualMap + C.dualMap.comp G.dualMap) V ≤ V //
        let W : Submodule ℝ (Module.Dual ℝ X) :=
          V ⊔ LinearMap.stabilizableSubspace A.dualMap C.dualMap
        let hWinv : ∀ x ∈ W, (A.dualMap + C.dualMap.comp G.dualMap) x ∈ W :=
          fun x hx => map_add_feedback_sup_stabilizableSubspace_le
            A.dualMap C.dualMap G.dualMap hFV ⟨x, hx, rfl⟩
        let VW : Submodule ℝ W := V.comap W.subtype
        let hmap : ∀ x ∈ VW,
            ((A.dualMap + C.dualMap.comp G.dualMap).restrict hWinv) x ∈ VW :=
          fun x hx => by
            change (A.dualMap + C.dualMap.comp G.dualMap) (x : Module.Dual ℝ X) ∈ V
            exact hFV ⟨(x : Module.Dual ℝ X), hx, rfl⟩
        LinearMap.IsHurwitz
          (Submodule.mapQ VW VW
            ((A.dualMap + C.dualMap.comp G.dualMap).restrict hWinv) hmap)} := by
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
  let V := LinearMap.controlledInvariantSubspace A.dualMap C.dualMap
    (LinearMap.ker E.dualMap)
  obtain ⟨F', ⟨⟨hFV, hQ⟩⟩⟩ :=
    exists_feedback_isHurwitz_quotient_of_geometricCondition A.dualMap C.dualMap V
      (LinearMap.isControlledInvariant_controlledInvariantSubspace
        A.dualMap C.dualMap (LinearMap.ker E.dualMap))
  obtain ⟨G, hG⟩ := LinearMap.dualMap_surjective (X := X) (Y := Y) F'
  refine ⟨G, hE, ⟨⟨?_, ?_⟩⟩⟩
  · simpa only [hG] using hFV
  · simpa only [hG] using hQ

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

/-! ### Stable-nonzero forced-readout bridge: current status

The forced/convolution quotient-decay bridge isolated by the previous handoff is
now formalised in two layers:

* `LinearSystem.tendsto_readout_exp_of_isHurwitz_mapQ_on`: the feedback-free
  form of `tendsto_readout_exp_of_isHurwitz_quotient_on`, decay of
  `t ↦ H (exp (t A) (E d))` from an invariant window `W ⊇ im E` and an invariant
  `V ≤ ker H` with `W ⧸ V` Hurwitz.
* `LinearSystem.externalResponse_tendsto_zero_of_quotient_hurwitz` (and its
  `..._of_isHurwitz_closedLoopMap` specialisation): decay of the forced external
  readout `H_e e^{t A_e} B_e d` of a well-posed dynamic interconnection from an
  invariant `Ve ≤ ker H_e` and an invariant window `We ⊇ im B_e` with `We ⧸ Ve`
  Hurwitz.
* `LinearSystem.stableNonzeroExternalResponse_of_quotient_hurwitz`: the
  `StableNonzeroExternalResponse` feed for an arbitrary dynamic controller with
  explicit `Ve`, `We` data, together with the consistent
  `..._of_isHurwitz_closedLoopMap` global-Hurwitz case.

The remaining geometric obligation is to *construct* the extended subspace pair
`(Ve, We)` from the two Corollary 6.22 blocks — `We = V_{e,2}` and `Ve = V_{e,1}`
of Trentelman–Stoorvogel–Hautus Lemma 6.21, equations (6.40)–(6.41) — and to
derive `We ⧸ Ve` Hurwitz from the state-feedback quotient on `W_g / V*` and the
observer quotient on `S* / T_g` (Theorem 6.18). That construction, and the
matching necessity direction from the merely stable response, are not claimed
here; the exact-zero criterion
(`externalStability_iff_geometricCertificate_and_conditions`) and the
stable-nonzero synthesis under explicit Hurwitz/quotient-Hurwitz data remain the
certified statements. -/


/-! ## The `W_g(ker H)` necessity bridge: algebraic form and dual

Trentelman–Stoorvogel–Hautus, Theorem 4.37 (PDF page 115 / printed page 99)
identifies the *open-loop output-stabilizable* set

`W_g(ker H) = {x | ∃ Bohl input u, H x_u(·, x) is stable}`

with the algebraic sum `V*(ker H) + Xstab(A, B)`. The easy inclusion is
formalised here as `outputStabilizableSubspace` together with its structural
properties, and the state-feedback form of the reversed inclusion as
`exists_feedback_tendsto_readout_of_mem_outputStabilizableSubspace`. The dual
condition is derived from the transposed inclusion with the accepted
detectable-top-characterisation `isDetectable_iff_detectableSubspace_eq_bot`.
The spectral `W_g(ker H) ⊆ V*(ker H) + Xstab` step — decomposing a Bohl input
and trajectory into stable and antistable parts and splitting the error equation
at the spectrum — is **not** formalised; the section note at the end of the file
records the exact missing statement. -/

namespace LinearSystem

section WgSubspace

variable {X U Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- **The algebraic `W_g(ker H)`.** The sum of the largest controlled invariant
subspace contained in `ker H` and the stabilizable subspace of `(A, B)`. This is
the right-hand side of the Trentelman–Stoorvogel–Hautus Theorem 4.37 identity
`W_g(ker H) = V*(ker H) + Xstab`; the trajectory characterisation of the
left-hand side is recorded by `IsOutputStabilizable` and its relation to this
definition is the object of the necessity bridge. -/
noncomputable def outputStabilizableSubspace (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (H : X →ₗ[ℝ] Z) : Submodule ℝ X :=
  LinearMap.controlledInvariantSubspace A B (LinearMap.ker H) ⊔
    LinearMap.stabilizableSubspace A B

omit [FiniteDimensional ℝ U] in
/-- The controlled-invariant witness `V*(ker H)` is contained in `W_g(ker H)`. -/
theorem controlledInvariantSubspace_le_outputStabilizableSubspace
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    LinearMap.controlledInvariantSubspace A B (LinearMap.ker H) ≤
      outputStabilizableSubspace A B H := le_sup_left

omit [FiniteDimensional ℝ U] in
/-- The stabilizable subspace `Xstab(A, B)` is contained in `W_g(ker H)`. -/
theorem stabilizableSubspace_le_outputStabilizableSubspace
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    LinearMap.stabilizableSubspace A B ≤ outputStabilizableSubspace A B H :=
  le_sup_right

omit [FiniteDimensional ℝ U] in
/-- The input image lies in `W_g(ker H)`, because `im B ⊆ Xstab(A, B)`. This is
the `im B ⊂ W_g` remark following Theorem 4.37. -/
theorem range_le_outputStabilizableSubspace
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    LinearMap.range B ≤ outputStabilizableSubspace A B H :=
  le_trans (LinearMap.range_le_reachableSubspace A B)
    (le_trans (LinearMap.reachableSubspace_le_stabilizableSubspace A B)
      (stabilizableSubspace_le_outputStabilizableSubspace A B H))

omit [FiniteDimensional ℝ U] in
/-- **`W_g(ker H)` is `A`-invariant.** The `V*` component maps into
`V* ⊔ im B ⊆ W_g` by controlled invariance, the stabilizable component into
itself, and `im B ⊆ W_g`. This is the `AW_g ⊂ W_g` structural remark following
Theorem 4.37. -/
theorem map_outputStabilizableSubspace_le
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    Submodule.map A (outputStabilizableSubspace A B H) ≤
      outputStabilizableSubspace A B H :=
  map_sup_stabilizableSubspace_le A B
    (LinearMap.isControlledInvariant_controlledInvariantSubspace A B (LinearMap.ker H))

omit [FiniteDimensional ℝ U] in
/-- The first Corollary 6.22 inclusion places the least conditioned-invariant
subspace generated by the disturbance inside `W_g(ker H)`. -/
theorem conditionedInvariantSubspace_le_outputStabilizableSubspace
    {Y D : Type*} [AddCommGroup Y] [Module ℝ Y]
    [AddCommGroup D] [Module ℝ D]
    (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (H : X →ₗ[ℝ] Z) (E : D →ₗ[ℝ] X)
    (hE : LinearMap.range E ≤ outputStabilizableSubspace A B H) :
    LinearMap.conditionedInvariantSubspace C A (LinearMap.range E) ≤
      outputStabilizableSubspace A B H := by
  apply LinearMap.conditionedInvariantSubspace_le hE
  change Submodule.map A
      (outputStabilizableSubspace A B H ⊓ LinearMap.ker C) ≤
      outputStabilizableSubspace A B H
  exact (Submodule.map_mono inf_le_left).trans
    (map_outputStabilizableSubspace_le A B H)

/-- The subspace `T_g = S*(im E) ∩ Xdet` is `A`-invariant. -/
theorem map_conditionedInvariant_inf_detectable_le
    {Y D : Type*} [AddCommGroup Y] [Module ℝ Y] [FiniteDimensional ℝ Y]
    [AddCommGroup D] [Module ℝ D]
    (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) :
    Submodule.map A
      (LinearMap.conditionedInvariantSubspace C A (LinearMap.range E) ⊓
        LinearMap.detectableSubspace C A) ≤
      LinearMap.conditionedInvariantSubspace C A (LinearMap.range E) ⊓
        LinearMap.detectableSubspace C A := by
  let S := LinearMap.conditionedInvariantSubspace C A (LinearMap.range E)
  let T := S ⊓ LinearMap.detectableSubspace C A
  have hTker : T ≤ LinearMap.ker C :=
    (inf_le_right).trans ((LinearMap.detectableSubspace_le_unobservableSubspace C A).trans
      (LinearMap.unobservableSubspace_le_ker C A))
  have hS : LinearMap.IsConditionedInvariant C A S :=
    LinearMap.isConditionedInvariant_conditionedInvariantSubspace C A (LinearMap.range E)
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨?_, ?_⟩
  · exact hS ⟨x, ⟨hx.1, hTker hx⟩, rfl⟩
  · exact LinearMap.map_detectableSubspace_le C A ⟨x, hx.2, rfl⟩

omit [FiniteDimensional ℝ U] in
/-- **The algebraic extended-pair assembly of Lemma 6.21.** Once the two gains
preserve `V*(ker H)` and `S*(im E)`, the Corollary 6.22 conditions produce the
nested invariant subspaces `Vₑ,₁ = Vₑ(T_g,V*)` and
`Vₑ,₂ = Vₑ(S*,W_g)`, with the disturbance image in the latter and the former
inside the output kernel. The quotient-Hurwitz assertion is separate. -/
theorem extendedPairSubspaces_of_externalStabilizationConditions
    {Y : Type*} [AddCommGroup Y] [Module ℝ Y] [FiniteDimensional ℝ Y]
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : ExternalStabilizationConditions sys E H)
    (F : X →ₗ[ℝ] U) (G : Y →ₗ[ℝ] X)
    (hF : Submodule.map (sys.A + sys.B.comp F)
      (LinearMap.controlledInvariantSubspace sys.A sys.B (LinearMap.ker H)) ≤
      LinearMap.controlledInvariantSubspace sys.A sys.B (LinearMap.ker H))
    (hG : Submodule.map (sys.A + G.comp sys.C)
      (LinearMap.conditionedInvariantSubspace sys.C sys.A (LinearMap.range E)) ≤
      LinearMap.conditionedInvariantSubspace sys.C sys.A (LinearMap.range E))
    (hwp : (cabPairInterconnection sys (cabPairController sys F G 0) E H).IsWellPosed) :
    let V := LinearMap.controlledInvariantSubspace sys.A sys.B (LinearMap.ker H)
    let W := outputStabilizableSubspace sys.A sys.B H
    let S := LinearMap.conditionedInvariantSubspace sys.C sys.A (LinearMap.range E)
    let T := S ⊓ LinearMap.detectableSubspace sys.C sys.A
    let Vₑ₁ := extendedPairSubspace T V
    let Vₑ₂ := extendedPairSubspace S W
    Vₑ₁ ≤ Vₑ₂ ∧
      Submodule.map
        ((cabPairInterconnection sys (cabPairController sys F G 0) E H).closedLoopMap hwp)
        Vₑ₁ ≤ Vₑ₁ ∧
      Submodule.map
        ((cabPairInterconnection sys (cabPairController sys F G 0) E H).closedLoopMap hwp)
        Vₑ₂ ≤ Vₑ₂ ∧
      LinearMap.range
        (cabPairInterconnection sys (cabPairController sys F G 0) E H).disturbanceMap ≤ Vₑ₂ ∧
      Vₑ₁ ≤ LinearMap.ker
        (cabPairInterconnection sys (cabPairController sys F G 0) E H).outputMap := by
  let V := LinearMap.controlledInvariantSubspace sys.A sys.B (LinearMap.ker H)
  let W := outputStabilizableSubspace sys.A sys.B H
  let S := LinearMap.conditionedInvariantSubspace sys.C sys.A (LinearMap.range E)
  let T := S ⊓ LinearMap.detectableSubspace sys.C sys.A
  have hAT : Submodule.map sys.A T ≤ T :=
    map_conditionedInvariant_inf_detectable_le sys.C sys.A E
  have hTkerC : T ≤ LinearMap.ker sys.C :=
    (inf_le_right).trans
      ((LinearMap.detectableSubspace_le_unobservableSubspace sys.C sys.A).trans
        (LinearMap.unobservableSubspace_le_ker sys.C sys.A))
  have hTV : T ≤ V := by
    apply LinearMap.le_controlledInvariantSubspace h.2
    exact hAT.trans le_sup_left
  have hSW : S ≤ W :=
    conditionedInvariantSubspace_le_outputStabilizableSubspace
      sys.C sys.A sys.B H E h.1
  have hAW : Submodule.map sys.A W ≤ W := map_outputStabilizableSubspace_le sys.A sys.B H
  have hASW : Submodule.map sys.A S ≤ W := (Submodule.map_mono hSW).trans hAW
  have hATV : Submodule.map sys.A T ≤ V := hAT.trans hTV
  have hFW : Submodule.map (sys.A + sys.B.comp F) W ≤ W :=
    map_add_feedback_sup_stabilizableSubspace_le sys.A sys.B F hF
  have hGT : Submodule.map (sys.A + G.comp sys.C) T ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    have hCx : sys.C x = 0 := LinearMap.mem_ker.mp (hTkerC hx)
    simpa [LinearMap.add_apply, LinearMap.comp_apply, hCx] using hAT ⟨x, hx, rfl⟩
  have hE_S : LinearMap.range E ≤ S :=
    LinearMap.le_conditionedInvariantSubspace sys.C sys.A (LinearMap.range E)
  have hVker : V ≤ LinearMap.ker H :=
    LinearMap.controlledInvariantSubspace_le_K sys.A sys.B (LinearMap.ker H)
  dsimp
  refine ⟨extendedPairSubspace_mono inf_le_left le_sup_left, ?_, ?_, ?_, ?_⟩
  · exact extendedPairSubspace_invariant_cabPairController_zero
      sys hD E H T V F G hTV hATV hF hGT hwp
  · exact extendedPairSubspace_invariant_cabPairController_zero
      sys hD E H S W F G hSW hASW hFW hG hwp
  · exact disturbanceMap_range_le_extendedPairSubspace
      sys (cabPairController sys F G 0) E H S W hE_S
  · exact extendedPairSubspace_le_outputMap_ker
      sys (cabPairController sys F G 0) E H T V h.2 hVker

/-- **The open-loop output-stabilizability predicate.** A state `x` lies in the
source's `W_g(ker H)` if there is a locally integrable open-loop input `u` for
which the controlled output of the variation-of-constants trajectory decays:
`t ↦ H (x_u(t, x)) → 0`. The input quantifier is explicit and the disturbance
channel is absent: this is the *open-loop* output-stabilizable set of
Trentelman–Stoorvogel–Hautus, equation (4.28). -/
def IsOutputStabilizable (sys : LinearSystem ℝ X U Z) (H : X →ₗ[ℝ] Z)
    (x : X) : Prop :=
  ∃ u : ℝ → U, MeasureTheory.LocallyIntegrable u MeasureTheory.volume ∧
    Filter.Tendsto (fun t : ℝ => H (sys.variationOfConstants 0 x u t))
      Filter.atTop (nhds 0)

/-- **The open-loop output-stabilizable set is closed under addition.** If `u`
stabilizes `x` and `v` stabilizes `y`, then `u + v` stabilizes `x + y`, since
the variation-of-constants trajectory is additive in the pair `(x, u)`:
`x_{u+v}(t, x + y) = x_u(t, x) + x_v(t, y)`. This is the structural fact that
the source's `W_g(ker H)` is a subspace, and it is used whenever the
output-stabilizable set is manipulated as a submodule rather than as a raw
trajectory predicate. -/
theorem isOutputStabilizable_add (sys : LinearSystem ℝ X U Z) (H : X →ₗ[ℝ] Z)
    {x y : X} (hx : IsOutputStabilizable sys H x) (hy : IsOutputStabilizable sys H y) :
    IsOutputStabilizable sys H (x + y) := by
  obtain ⟨u, hu, hux⟩ := hx
  obtain ⟨v, hv, hvy⟩ := hy
  refine ⟨u + v, hu.add hv, ?_⟩
  have htraj : ∀ t : ℝ, sys.variationOfConstants 0 (x + y) (u + v) t =
      sys.variationOfConstants 0 x u t + sys.variationOfConstants 0 y v t := by
    intro t
    rw [variationOfConstants_eq, variationOfConstants_eq, variationOfConstants_eq]
    have hfor : (∫ s in (0 : ℝ)..t, sys.forcing 0 (u + v) s) =
        (∫ s in (0 : ℝ)..t, sys.forcing 0 u s) +
          (∫ s in (0 : ℝ)..t, sys.forcing 0 v s) := by
      rw [show sys.forcing 0 (u + v) = sys.forcing 0 u + sys.forcing 0 v from
        forcing_add sys u v]
      exact intervalIntegral.integral_add
        (intervalIntegrable_forcing sys 0 hu 0 t)
        (intervalIntegrable_forcing sys 0 hv 0 t)
    rw [hfor]
    have harg : x + y + ((∫ s in (0 : ℝ)..t, sys.forcing 0 u s) +
        (∫ s in (0 : ℝ)..t, sys.forcing 0 v s)) =
        (x + ∫ s in (0 : ℝ)..t, sys.forcing 0 u s) +
          (y + ∫ s in (0 : ℝ)..t, sys.forcing 0 v s) := by abel
    rw [harg, map_add]
  have hfun : (fun t : ℝ => H (sys.variationOfConstants 0 (x + y) (u + v) t)) =
      fun t : ℝ => H (sys.variationOfConstants 0 x u t) +
        H (sys.variationOfConstants 0 y v t) := by
    funext t
    rw [htraj t, map_add]
  rw [hfun]
  simpa using hux.add hvy

omit [FiniteDimensional ℝ U] in
/-- **State-feedback sufficiency for `W_g(ker H)`.** Every state in
`W_g(ker H) = V*(ker H) + Xstab(A, B)` admits a static state feedback `F` whose
closed-loop controlled output decays: `t ↦ H (e^{t(A + B F)} x) → 0`.

This is the state-feedback form of the easy inclusion of Theorem 4.37 combined
with Lemma 4.38/Theorem 4.39. It is obtained by applying the accepted geometric
construction `exists_feedback_tendsto_readout_of_geometricCondition` to the
one-dimensional disturbance map `c ↦ c • x`; the trajectory-to-open-loop
translation is the separate step of the necessity bridge and is not used here. -/
theorem exists_feedback_tendsto_readout_of_mem_outputStabilizableSubspace
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) {x : X}
    (hx : x ∈ outputStabilizableSubspace A B H) :
    ∃ F : X →ₗ[ℝ] U, Filter.Tendsto
      (fun t : ℝ => H (NormedSpace.exp
        (t • (A + B.comp F).toContinuousLinearMap) x)) Filter.atTop (nhds 0) := by
  let E : ℝ →ₗ[ℝ] X :=
    { toFun := fun c => c • x
      map_add' := fun c d => add_smul c d x
      map_smul' := fun c d => mul_smul c d x }
  have hE : LinearMap.range E ≤ outputStabilizableSubspace A B H := by
    rintro y ⟨c, rfl⟩
    exact (outputStabilizableSubspace A B H).smul_mem c hx
  obtain ⟨F, -, hdec⟩ := exists_feedback_tendsto_readout_of_geometricCondition A B H E
    (LinearMap.controlledInvariantSubspace A B (LinearMap.ker H))
    (LinearMap.isControlledInvariant_controlledInvariantSubspace A B (LinearMap.ker H))
    (LinearMap.controlledInvariantSubspace_le_K A B (LinearMap.ker H)) hE
  refine ⟨F, ?_⟩
  simpa [E] using hdec 1

/-! ### The `B = 0` spectral decomposition of `W_g(ker H)`

With no input channel (`B = 0`) the algebraic `W_g(ker H)` collapses to a sum of
pure spectral objects. A subspace is controlled invariant for `(A, 0)` exactly
when it is `A`-invariant and contained in `ker H`, so the largest one is the
unobservable subspace `⟨ker H | A⟩`; and the stabilizable subspace is the stable
subspace `X_g(A)` because the reachable subspace is trivial. Hence

`W_g(ker H) = X_g(A) ⊔ ⟨ker H | A⟩`.

The structural lemmas below record that reduction. They are the algebraic core
of the `B = 0` *spectral stable-observability necessity*: the missing analytic
step, isolated as the explicit `hspectral` hypothesis of
`mem_outputStabilizableSubspace_of_decay_of_B_eq_zero`, is the statement that an
antistable state whose readout decays must be unobservable (Trentelman–Stoorvogel–
Hautus, Theorem 4.37 necessity for the no-input case). The reduction of the
trajectory predicate `IsOutputStabilizable` to that spectral statement is
`mem_outputStabilizableSubspace_of_isOutputStabilizable_of_B_eq_zero`. -/

omit [FiniteDimensional ℝ U] in
/-- **The `B = 0` controlled-invariant subspace is the unobservable subspace.**
With no input channel a subspace is controlled invariant for `(A, 0)` exactly
when it is `A`-invariant and contained in `ker H`; consequently the largest such
subspace `V*(ker H)` is the unobservable subspace `⟨ker H | A⟩`.

This is the `im B = 0` degenerate case of `controlledInvariantSubspace`. -/
theorem controlledInvariantSubspace_zero_eq_unobservableSubspace
    (A : X →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    LinearMap.controlledInvariantSubspace A (0 : U →ₗ[ℝ] X) (LinearMap.ker H) =
      LinearMap.unobservableSubspace H A := by
  apply le_antisymm
  · have hV := LinearMap.isControlledInvariant_controlledInvariantSubspace A (0 : U →ₗ[ℝ] X)
      (LinearMap.ker H)
    have hVK := LinearMap.controlledInvariantSubspace_le_K A (0 : U →ₗ[ℝ] X) (LinearMap.ker H)
    apply LinearMap.le_unobservableSubspace H A hVK
    rw [LinearMap.IsControlledInvariant] at hV
    simpa using hV
  · apply LinearMap.le_controlledInvariantSubspace
    · exact LinearMap.unobservableSubspace_le_ker H A
    · rw [LinearMap.IsControlledInvariant]
      simpa using LinearMap.map_unobservableSubspace_le H A

omit [FiniteDimensional ℝ U] in
/-- **Spectral decomposition of `W_g(ker H)` when `B = 0`.** With no input
channel the algebraic `W_g(ker H) = V*(ker H) ⊔ Xstab(A, 0)` is
`X_g(A) ⊔ ⟨ker H | A⟩`: the controlled-invariant component is the unobservable
subspace and the stabilizable component is the stable subspace `X_g(A)`, because
the reachable subspace of `(A, 0)` is trivial. -/
theorem outputStabilizableSubspace_zero_eq_sup_unobservableSubspace
    (A : X →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    outputStabilizableSubspace A (0 : U →ₗ[ℝ] X) H =
      LinearMap.hurwitzSubspace A ⊔ LinearMap.unobservableSubspace H A := by
  rw [outputStabilizableSubspace, controlledInvariantSubspace_zero_eq_unobservableSubspace,
    LinearMap.stabilizableSubspace, LinearMap.reachableSubspace]
  rw [sup_comm]
  simp

/-- **Stable states have decaying readout.** A state in the stable subspace
`X_g(A)` has `t ↦ H (e^{t A} x) → 0` because the exponential orbit itself decays
(`tendsto_exp_restrict_hurwitzSubspace`) and `H` is continuous. -/
theorem tendsto_readout_exp_of_mem_hurwitzSubspace
    (A : X →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) {x : X} (hx : x ∈ LinearMap.hurwitzSubspace A) :
    Filter.Tendsto (fun t : ℝ => H (NormedSpace.exp (t • A.toContinuousLinearMap) x))
      Filter.atTop (nhds 0) := by
  have h := (H.continuous_of_finiteDimensional.tendsto 0).comp
    (LinearMap.tendsto_exp_restrict_hurwitzSubspace A hx)
  simpa [Function.comp_def] using h

/-- **Unobservable states have identically zero readout.** If `x ∈ ⟨ker H | A⟩`
then every derivative `H A^k x` vanishes, so `H (e^{t A} x) = 0` for all `t`.
This is the algebraic-to-trajectory direction of the accepted bridge
`continuousC_expFlow_eq_zero_of_mem_unobservableSubspace`. -/
theorem readout_exp_eq_zero_of_mem_unobservableSubspace
    (A : X →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) {x : X}
    (hx : x ∈ LinearMap.unobservableSubspace H A) (t : ℝ) :
    H (NormedSpace.exp (t • A.toContinuousLinearMap) x) = 0 := by
  let sys : LinearSystem ℝ X X Z := ⟨A, 0, H, 0⟩
  have hx' : x ∈ LinearMap.unobservableSubspace sys.C sys.A := by simpa [sys] using hx
  have h := continuousC_expFlow_eq_zero_of_mem_unobservableSubspace sys (z := x) hx' t
  simpa [sys, LinearSystem.expFlow, LinearSystem.continuousA] using h

omit [FiniteDimensional ℝ U] in
/-- **The `B = 0` spectral stable-observability necessity, reduced form.** Assume
the isolated spectral statement `hspectral`: every state in the antistable
subspace `X_b(A)` whose readout `t ↦ H (e^{t A} x)` decays is unobservable. Then
every state with decaying readout lies in `W_g(ker H) = X_g(A) ⊔ ⟨ker H | A⟩`.

Split `x = x_g + x_b` along the accepted stable/antistable direct sum. The stable
part is in `X_g(A)` by definition, and linearity transports the decay of `H e^{tA} x`
and of `H e^{tA} x_g` to the antistable part, so `hspectral` puts `x_b` in the
unobservable subspace. The analytic content of `hspectral` — that a nonzero
antistable orbit cannot have a decaying readout — is the remaining obligation and
is *not* assumed to hold for free; no witness for it is introduced here. -/
theorem mem_outputStabilizableSubspace_of_decay_of_B_eq_zero
    (A : X →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (hspectral : ∀ x : X, x ∈ LinearMap.unstableSubspace A →
      Filter.Tendsto (fun t : ℝ => H (NormedSpace.exp (t • A.toContinuousLinearMap) x))
        Filter.atTop (nhds 0) → x ∈ LinearMap.unobservableSubspace H A)
    {x : X}
    (hdec : Filter.Tendsto (fun t : ℝ => H (NormedSpace.exp (t • A.toContinuousLinearMap) x))
      Filter.atTop (nhds 0)) :
    x ∈ outputStabilizableSubspace A (0 : U →ₗ[ℝ] X) H := by
  rw [outputStabilizableSubspace_zero_eq_sup_unobservableSubspace]
  have hxmem : x ∈ LinearMap.hurwitzSubspace A ⊔ LinearMap.unstableSubspace A := by
    rw [LinearMap.hurwitzSubspace_sup_unstableSubspace_eq_top]; trivial
  obtain ⟨xg, hxg, xb, hxb, rfl⟩ := Submodule.mem_sup.mp hxmem
  have hgdec := tendsto_readout_exp_of_mem_hurwitzSubspace A H hxg
  have hxb_dec : Filter.Tendsto (fun t : ℝ =>
      H (NormedSpace.exp (t • A.toContinuousLinearMap) xb)) Filter.atTop (nhds 0) := by
    have h1 : (fun t : ℝ => H (NormedSpace.exp (t • A.toContinuousLinearMap) (xg + xb))) =
        fun t => H (NormedSpace.exp (t • A.toContinuousLinearMap) xg) +
          H (NormedSpace.exp (t • A.toContinuousLinearMap) xb) := by
      funext t; rw [map_add, map_add]
    rw [h1] at hdec
    simpa using hdec.sub hgdec
  exact Submodule.mem_sup.mpr ⟨xg, hxg, xb, hspectral xb hxb hxb_dec, rfl⟩

/-- **Zero input channel collapses variation of constants to the exponential
orbit.** With `B = 0` the forcing integrand vanishes, so the forced solution is
the homogeneous flow `t ↦ e^{t A} x`. -/
theorem variationOfConstants_of_B_eq_zero (sys : LinearSystem ℝ X U Z) (hB : sys.B = 0)
    (x : X) (u : ℝ → U) (t : ℝ) :
    sys.variationOfConstants 0 x u t = sys.expFlow t x := by
  simp [LinearSystem.variationOfConstants, LinearSystem.forcing, hB]

/-- **The `B = 0` necessity bridge from the trajectory predicate.** If `B = 0`,
then the open-loop output-stabilizability predicate `IsOutputStabilizable`
reduces to the zero-input readout decay `t ↦ H (e^{t A} x) → 0`
(`variationOfConstants_of_B_eq_zero`), so the reduced spectral bridge
`mem_outputStabilizableSubspace_of_decay_of_B_eq_zero` yields membership in
`W_g(ker H)`. The `hspectral` hypothesis is the isolated remaining spectral
obligation, exactly as in the reduced form above. -/
theorem mem_outputStabilizableSubspace_of_isOutputStabilizable_of_B_eq_zero
    (sys : LinearSystem ℝ X U Z) (H : X →ₗ[ℝ] Z) (x : X)
    (hspectral : ∀ x : X, x ∈ LinearMap.unstableSubspace sys.A →
      Filter.Tendsto (fun t : ℝ => H (NormedSpace.exp (t • sys.A.toContinuousLinearMap) x))
        Filter.atTop (nhds 0) → x ∈ LinearMap.unobservableSubspace H sys.A)
    (hB : sys.B = 0)
    (h : IsOutputStabilizable sys H x) :
    x ∈ outputStabilizableSubspace sys.A sys.B H := by
  obtain ⟨u, -, htend⟩ := h
  rw [hB]
  apply mem_outputStabilizableSubspace_of_decay_of_B_eq_zero sys.A H hspectral
  have hfun : (fun t : ℝ => H (NormedSpace.exp (t • sys.A.toContinuousLinearMap) x)) =
      fun t => H (sys.variationOfConstants 0 x u t) := by
    funext t
    rw [variationOfConstants_of_B_eq_zero sys hB x u t]
    rfl
  rwa [hfun]

/-- **The `B = 0` sufficiency direction of the trajectory characterisation.**
Every state in `W_g(ker H) = X_g(A) ⊔ ⟨ker H | A⟩` has decaying zero-input
readout when `B = 0`: a stable state decays by
`tendsto_readout_exp_of_mem_hurwitzSubspace` and an unobservable state has
identically zero readout by `readout_exp_eq_zero_of_mem_unobservableSubspace`.
Together with `mem_outputStabilizableSubspace_of_isOutputStabilizable_of_B_eq_zero`
this identifies the open-loop output-stabilizable set with the algebraic
`W_g(ker H)`, modulo the isolated antistable spectral obligation. -/
theorem isOutputStabilizable_of_mem_outputStabilizableSubspace_of_B_eq_zero
    (sys : LinearSystem ℝ X U Z) (H : X →ₗ[ℝ] Z) (hB : sys.B = 0) {x : X}
    (hx : x ∈ outputStabilizableSubspace sys.A sys.B H) :
    IsOutputStabilizable sys H x := by
  have hx' : x ∈ LinearMap.hurwitzSubspace sys.A ⊔
      LinearMap.unobservableSubspace H sys.A := by
    rw [hB] at hx
    rwa [outputStabilizableSubspace_zero_eq_sup_unobservableSubspace] at hx
  obtain ⟨xg, hxg, xb, hxb, rfl⟩ := Submodule.mem_sup.mp hx'
  refine ⟨fun _ => (0 : U), MeasureTheory.locallyIntegrable_zero, ?_⟩
  have hfun : (fun t : ℝ =>
      H (sys.variationOfConstants 0 (xg + xb) (fun _ => (0 : U)) t)) =
      fun t : ℝ => H (NormedSpace.exp (t • sys.A.toContinuousLinearMap) xg) +
        H (NormedSpace.exp (t • sys.A.toContinuousLinearMap) xb) := by
    funext t
    rw [variationOfConstants_of_B_eq_zero sys hB (xg + xb) (fun _ => (0 : U)) t]
    simp only [LinearSystem.expFlow, LinearSystem.continuousA, map_add]
  rw [hfun]
  have hb : (fun t : ℝ =>
      H (NormedSpace.exp (t • sys.A.toContinuousLinearMap) xb)) = fun _ : ℝ => (0 : Z) := by
    funext t
    exact readout_exp_eq_zero_of_mem_unobservableSubspace sys.A H hxb t
  have hbt : Filter.Tendsto
      (fun t : ℝ => H (NormedSpace.exp (t • sys.A.toContinuousLinearMap) xb))
      Filter.atTop (nhds 0) := by
    rw [hb]
    exact tendsto_const_nhds
  simpa using (tendsto_readout_exp_of_mem_hurwitzSubspace sys.A H hxg).add hbt

/-- **The `B = 0` open-loop trajectory characterisation.** The source's
output-stabilizable set equals the algebraic `W_g(ker H) = V*(ker H) ⊔ Xstab`
in the no-input case, modulo the single isolated antistable spectral statement
`hspectral`: an antistable state with decaying readout is unobservable. The
forward implication is
`mem_outputStabilizableSubspace_of_isOutputStabilizable_of_B_eq_zero`; the
unconditional converse is
`isOutputStabilizable_of_mem_outputStabilizableSubspace_of_B_eq_zero`. -/
theorem isOutputStabilizable_iff_mem_outputStabilizableSubspace_of_B_eq_zero
    (sys : LinearSystem ℝ X U Z) (H : X →ₗ[ℝ] Z)
    (hspectral : ∀ x : X, x ∈ LinearMap.unstableSubspace sys.A →
      Filter.Tendsto (fun t : ℝ => H (NormedSpace.exp (t • sys.A.toContinuousLinearMap) x))
        Filter.atTop (nhds 0) → x ∈ LinearMap.unobservableSubspace H sys.A)
    (hB : sys.B = 0) (x : X) :
    IsOutputStabilizable sys H x ↔ x ∈ outputStabilizableSubspace sys.A sys.B H :=
  ⟨mem_outputStabilizableSubspace_of_isOutputStabilizable_of_B_eq_zero sys H x hspectral hB,
   isOutputStabilizable_of_mem_outputStabilizableSubspace_of_B_eq_zero sys H hB⟩

omit [FiniteDimensional ℝ U] in
/-- The isolated antistable spectral obligation is discharged in the zero-operator
case: with `A = 0` the orbit is constant, so a readout tending to zero must
already be zero, hence the state is unobservable. This is a non-vacuity witness
for `hspectral` and covers the zero-eigenvalue spectrum `{0}`. -/
theorem hspectral_zero_operator (H : X →ₗ[ℝ] Z) :
    ∀ x : X, x ∈ LinearMap.unstableSubspace (0 : X →ₗ[ℝ] X) →
      Filter.Tendsto (fun t : ℝ => H (NormedSpace.exp
        (t • (0 : X →ₗ[ℝ] X).toContinuousLinearMap) x)) Filter.atTop (nhds 0) →
      x ∈ LinearMap.unobservableSubspace H (0 : X →ₗ[ℝ] X) := by
  intro x _ hdec
  have hconst : (fun t : ℝ => H (NormedSpace.exp
      (t • (0 : X →ₗ[ℝ] X).toContinuousLinearMap) x)) = fun _ : ℝ => H x := by
    funext t
    simp
  rw [hconst] at hdec
  have hHx : H x = 0 := tendsto_nhds_unique tendsto_const_nhds hdec
  rw [LinearMap.mem_unobservableSubspace]
  intro k
  cases k with
  | zero => simpa using hHx
  | succ k => simp

/-- **The `A = 0` open-loop trajectory characterisation, unconditionally.**
With the zero state map the isolated spectral obligation is discharged by
`hspectral_zero_operator`, so the `B = 0` characterisation holds without extra
hypotheses: a state is open-loop output-stabilizable exactly when its readout
vanishes. -/
theorem isOutputStabilizable_iff_mem_outputStabilizableSubspace_of_zero_operator
    (H : X →ₗ[ℝ] Z) (x : X) :
    IsOutputStabilizable (⟨0, 0, H, 0⟩ : LinearSystem ℝ X U Z) H x ↔
      x ∈ outputStabilizableSubspace (0 : X →ₗ[ℝ] X) (0 : U →ₗ[ℝ] X) H :=
  isOutputStabilizable_iff_mem_outputStabilizableSubspace_of_B_eq_zero
    (⟨0, 0, H, 0⟩ : LinearSystem ℝ X U Z) H
    (hspectral_zero_operator H) rfl x

/-- **The `hspectral` obligation is discharged.** The accepted antistable
readout theorem `LinearMap.antistable_readout_forces_unobservable` supplies
exactly the hypothesis isolated in
`mem_outputStabilizableSubspace_of_decay_of_B_eq_zero`: an antistable state whose
readout decays at `+∞` is unobservable. No spectral statement is assumed here. -/
theorem hspectral_holds (A : X →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    ∀ x : X, x ∈ LinearMap.unstableSubspace A →
      Filter.Tendsto (fun t : ℝ => H (NormedSpace.exp (t • A.toContinuousLinearMap) x))
        Filter.atTop (nhds 0) → x ∈ LinearMap.unobservableSubspace H A :=
  fun _ hx hdec => LinearMap.antistable_readout_forces_unobservable A H hx hdec

/-- **The `B = 0` open-loop trajectory characterisation, unconditionally.**
With the antistable readout theorem supplying `hspectral`, the source's
output-stabilizable set equals the algebraic `W_g(ker H)` in the no-input case
without any extra hypothesis: a state is open-loop output-stabilizable exactly
when it lies in `V*(ker H) ⊔ Xstab(A, 0)`. -/
theorem isOutputStabilizable_iff_mem_outputStabilizableSubspace_of_B_eq_zero'
    (sys : LinearSystem ℝ X U Z) (H : X →ₗ[ℝ] Z) (hB : sys.B = 0) (x : X) :
    IsOutputStabilizable sys H x ↔ x ∈ outputStabilizableSubspace sys.A sys.B H :=
  isOutputStabilizable_iff_mem_outputStabilizableSubspace_of_B_eq_zero sys H
    (hspectral_holds sys.A H) hB x

/-! ### State-feedback necessity for `W_g(ker H)`

The unconditional `B = 0` characterisation is now lifted to an arbitrary state
feedback. With `A_F = A + B F`, a decaying *closed-loop* readout
`t ↦ H (e^{t A_F} x) → 0` forces `x ∈ W_g(ker H) = V*(ker H) ⊔ Xstab(A, B)`.

The proof uses the accepted stable/antistable direct sum `X = X_g(A_F) ⊔ X_b(A_F)`.
The stable part already lies in `Xstab(A, B)`, and the antistable part is handled
by the unconditional antistable readout theorem
`LinearMap.antistable_readout_forces_unobservable`: a state in `X_b(A_F)` whose
readout decays is `A_F`-unobservable, hence `A_F`-invariant and contained in
`ker H`, hence `(A, B)`-controlled invariant because `A = A_F - B F`. -/

omit [FiniteDimensional ℝ U] in
/-- **State feedback does not change the stabilizable subspace.** Replacing the
state map `A` by `A + B F` leaves `Xstab(A, B)` invariant, because state feedback
only shifts the stabilizing gain. This is the reverse of the accepted
`stabilizableSubspace_le_add_feedback`, applied to `-F`. -/
theorem stabilizableSubspace_add_feedback_eq (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (F : X →ₗ[ℝ] U) :
    LinearMap.stabilizableSubspace (A + B.comp F) B = LinearMap.stabilizableSubspace A B := by
  apply le_antisymm
  · have h := stabilizableSubspace_le_add_feedback (A + B.comp F) B (-F)
    have hmap : (A + B.comp F) + B.comp (-F) = A := by
      ext x
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.neg_apply, map_neg]
      abel
    rwa [hmap] at h
  · exact stabilizableSubspace_le_add_feedback A B F

omit [FiniteDimensional ℝ U] in
/-- **The state-feedback `W_g(ker H)` necessity.** If some state feedback
`u = F x` makes the closed-loop controlled output decay,
`t ↦ H (e^{t (A + B F)} x) → 0`, then `x` already lies in the algebraic
`W_g(ker H) = V*(ker H) ⊔ Xstab(A, B)`. This is the state-feedback form of the
hard inclusion of Trentelman–Stoorvogel–Hautus Theorem 4.37, obtained from the
unconditional antistable readout theorem. The open-loop version quantifies over
an arbitrary locally integrable input and is a separate, strictly stronger
obligation. -/
theorem mem_outputStabilizableSubspace_of_feedback_decay
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) (F : X →ₗ[ℝ] U) {x : X}
    (hdec : Filter.Tendsto (fun t : ℝ => H (NormedSpace.exp
      (t • (A + B.comp F).toContinuousLinearMap) x)) Filter.atTop (nhds 0)) :
    x ∈ outputStabilizableSubspace A B H := by
  let AF : X →ₗ[ℝ] X := A + B.comp F
  have hxmem : x ∈ LinearMap.hurwitzSubspace AF ⊔ LinearMap.unstableSubspace AF := by
    rw [LinearMap.hurwitzSubspace_sup_unstableSubspace_eq_top]
    trivial
  obtain ⟨xg, hxg, xb, hxb, hxeq⟩ := Submodule.mem_sup.mp hxmem
  have hgdec : Filter.Tendsto (fun t : ℝ => H (NormedSpace.exp
      (t • AF.toContinuousLinearMap) xg)) Filter.atTop (nhds 0) :=
    tendsto_readout_exp_of_mem_hurwitzSubspace AF H hxg
  have hxb_dec : Filter.Tendsto (fun t : ℝ => H (NormedSpace.exp
      (t • AF.toContinuousLinearMap) xb)) Filter.atTop (nhds 0) := by
    have hsplit : (fun t : ℝ => H (NormedSpace.exp (t • AF.toContinuousLinearMap) x)) =
        fun t => H (NormedSpace.exp (t • AF.toContinuousLinearMap) xg) +
          H (NormedSpace.exp (t • AF.toContinuousLinearMap) xb) := by
      funext t
      rw [← hxeq, map_add, map_add]
    have h' := hdec
    rw [hsplit] at h'
    simpa using h'.sub hgdec
  have hxb_unobs : xb ∈ LinearMap.unobservableSubspace H AF :=
    LinearMap.antistable_readout_forces_unobservable AF H hxb hxb_dec
  have hUle : LinearMap.unobservableSubspace H AF ≤ LinearMap.ker H :=
    LinearMap.unobservableSubspace_le_ker H AF
  have hUctrl : LinearMap.IsControlledInvariant A B (LinearMap.unobservableSubspace H AF) := by
    rw [LinearMap.IsControlledInvariant]
    intro y hy
    rw [Submodule.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hAz : A z = AF z - B (F z) := by
      change A z = (A + B.comp F) z - B (F z)
      simp only [LinearMap.add_apply, LinearMap.comp_apply]
      abel
    rw [hAz]
    exact Submodule.sub_mem_sup
      (LinearMap.map_unobservableSubspace_le H AF ⟨z, hz, rfl⟩) ⟨F z, rfl⟩
  have hxb_ctrl : xb ∈ LinearMap.controlledInvariantSubspace A B (LinearMap.ker H) :=
    LinearMap.le_controlledInvariantSubspace hUle hUctrl hxb_unobs
  have hxg_stab : xg ∈ LinearMap.stabilizableSubspace A B := by
    have h1 : xg ∈ LinearMap.stabilizableSubspace (A + B.comp F) B :=
      LinearMap.hurwitzSubspace_le_stabilizableSubspace (A + B.comp F) B hxg
    rwa [stabilizableSubspace_add_feedback_eq A B F] at h1
  rw [outputStabilizableSubspace, ← hxeq, add_comm xg xb]
  exact Submodule.add_mem_sup hxb_ctrl hxg_stab

omit [FiniteDimensional ℝ U] in
/-- **The state-feedback `W_g(ker H)` characterisation, two-sided.** For the
general controlled pair `(A, B)` a state admits a state feedback `F` whose
closed-loop readout decays, `t ↦ H (e^{t(A + B F)} x) → 0`, if and only if
`x ∈ W_g(ker H) = V*(ker H) ⊔ Xstab(A, B)`. The forward direction is the new
state-feedback necessity `mem_outputStabilizableSubspace_of_feedback_decay`,
the converse is the accepted geometric construction
`exists_feedback_tendsto_readout_of_mem_outputStabilizableSubspace`. This is the
feedback form of the `B = 0` characterisation
`isOutputStabilizable_iff_mem_outputStabilizableSubspace_of_B_eq_zero'` lifted
to an arbitrary input map; the open-loop predicate `IsOutputStabilizable`
quantifies over an arbitrary locally integrable input and its necessity remains
the strictly stronger obligation. -/
theorem exists_feedback_tendsto_readout_iff_mem_outputStabilizableSubspace
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) (x : X) :
    (∃ F : X →ₗ[ℝ] U, Filter.Tendsto (fun t : ℝ => H (NormedSpace.exp
        (t • (A + B.comp F).toContinuousLinearMap) x)) Filter.atTop (nhds 0)) ↔
      x ∈ outputStabilizableSubspace A B H :=
  ⟨fun ⟨F, hF⟩ => mem_outputStabilizableSubspace_of_feedback_decay A B H F hF,
    fun hx => exists_feedback_tendsto_readout_of_mem_outputStabilizableSubspace A B H hx⟩

/-! ### The reachable-quotient cancellation lemma

The hard inclusion of Theorem 4.37 is an input-cancellation statement: an
arbitrary locally integrable open-loop input can cancel the antistable autonomous
readout only through the reachable subspace `R = ⟨A | im B⟩`. The first
structural fact is that the class of the forced trajectory modulo `R` is the
autonomous class. The forcing `exp (-s A) (B u(s))` is reachable and `R` is
`A`-invariant and closed, so the input term lies entirely in `R`; equivalently,
the reachable quotient `X ⧸ ⟨A | im B⟩` carries only the autonomous dynamics. -/

set_option linter.style.haveILetI false

/-- **Reachable-quotient cancellation.** For a locally integrable open-loop input
the variation-of-constants trajectory differs from the autonomous exponential
orbit by a state of the reachable subspace:
`x_u(t) - exp (t A) x ∈ ⟨A | im B⟩`.

This is proved by pushing both sides into the quotient `X ⧸ ⟨A | im B⟩`: the
forcing integrand dies there because `B` lands in the reachable subspace, so the
forced trajectory and the free trajectory have the same quotient class. -/
theorem variationOfConstants_sub_expFlow_mem_reachableSubspace
    (sys : LinearSystem ℝ X U Z) (x : X) {u : ℝ → U}
    (hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume) (t : ℝ) :
    sys.variationOfConstants 0 x u t - sys.expFlow t x ∈
      LinearMap.reachableSubspace sys.A sys.B := by
  let R := LinearMap.reachableSubspace sys.A sys.B
  have hR : R ≤ R.comap sys.A := fun y hy =>
    LinearMap.map_reachableSubspace_le sys.A sys.B ⟨y, hy, rfl⟩
  haveI : IsClosed (R : Set X) := R.closed_of_finiteDimensional
  letI : IsTopologicalRing (X ⧸ R →L[ℝ] X ⧸ R) :=
    { continuous_add := continuous_add
      continuous_mul := Continuous.clm_comp continuous_fst continuous_snd
      continuous_neg := continuous_neg }
  let q : X →L[ℝ] X ⧸ R := R.mkQ.toContinuousLinearMap
  let Aq : X ⧸ R →ₗ[ℝ] X ⧸ R := R.mapQ R sys.A hR
  have hqA : q.comp sys.A.toContinuousLinearMap = Aq.toContinuousLinearMap.comp q := by
    ext y
    change R.mkQ (sys.A y) = Aq (R.mkQ y)
    exact (congrFun (congrArg DFunLike.coe
      (Submodule.mapQ_mkQ R R sys.A (h := hR))) y).symm
  have hqB : ∀ y : X, y ∈ R → q y = 0 := by
    intro y hy
    change R.mkQ y = 0
    rw [Submodule.mkQ_apply]
    exact (Submodule.Quotient.mk_eq_zero R).mpr hy
  have hq_exp : ∀ y : X, q (sys.expFlow t y) =
      NormedSpace.exp (t • Aq.toContinuousLinearMap) (q y) := by
    intro y
    simpa only [LinearSystem.expFlow, LinearSystem.continuousA] using
      clm_map_exp_smul q sys.A.toContinuousLinearMap Aq.toContinuousLinearMap hqA t y
  have hqforcing : ∀ s : ℝ, q (sys.forcing 0 u s) = 0 := by
    intro s
    have hB := hqB (sys.continuousB (u s))
      (LinearMap.range_le_reachableSubspace sys.A sys.B ⟨u s, rfl⟩)
    have hstep : q (sys.forcing 0 u s) =
        NormedSpace.exp ((-(s - 0)) • Aq.toContinuousLinearMap)
          (q (sys.continuousB (u s))) := by
      simpa only [LinearSystem.forcing, LinearSystem.expFlow, LinearSystem.continuousA] using
        clm_map_exp_smul q sys.A.toContinuousLinearMap Aq.toContinuousLinearMap
          hqA (-(s - 0)) (sys.continuousB (u s))
    rw [hstep, hB, map_zero]
  have hq_int : q (∫ s in (0 : ℝ)..t, sys.forcing 0 u s) = 0 := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm q
      (LinearSystem.intervalIntegrable_forcing sys 0 hu 0 t)]
    simp [hqforcing]
  have hvar : sys.variationOfConstants 0 x u t =
      sys.expFlow t (x + ∫ s in (0 : ℝ)..t, sys.forcing 0 u s) := by
    simp [LinearSystem.variationOfConstants, sub_zero]
  have hq_var : q (sys.variationOfConstants 0 x u t) = q (sys.expFlow t x) := by
    rw [hvar, hq_exp]
    rw [map_add, hq_int, add_zero]
    exact (hq_exp x).symm
  have hzero : q (sys.variationOfConstants 0 x u t - sys.expFlow t x) = 0 := by
    rw [map_sub, hq_var, sub_self]
  change R.mkQ (sys.variationOfConstants 0 x u t - sys.expFlow t x) = 0 at hzero
  exact (Submodule.Quotient.mk_eq_zero R).mp hzero

/-! ### Quotient spectral non-cancellation of the reachable readout

The reachable-quotient cancellation above replaces the forced trajectory
`x_u(t)` by the autonomous orbit `e^{tA} x` modulo the reachable subspace
`R = ⟨A | im B⟩`. The spectral content of Theorem 4.37 is the *non-cancellation*
statement that this replacement is harmless for a readout functional that
already annihilates `R`: such a functional cannot see the input channel at all,
so the open-loop decay of its readout is exactly the autonomous decay, and the
antistable readout theorem applies.

Concretely, let `ρ : Z →L[ℝ] ℝ` be a continuous readout functional and let
`L = ρ ∘ H` be the induced state functional. If `L` vanishes on the reachable
subspace `R = ⟨A | im B⟩`, then for every locally integrable input `u`
`L x_u(t) = L (e^{tA} x)`. Hence a decaying readout forces the autonomous
functional trajectory `t ↦ L (e^{tA} x)` to decay, and the accepted antistable
readout theorem `LinearMap.antistable_readout_forces_unobservable` gives
`L x = 0` for every antistable `x`.

This is the correct replacement of the invalid single-functional PBH shortcut:
the functional must annihilate the whole reachable subspace (equivalently, all
Markov parameters `ρ H A^k B`), which is the *observability-chain* condition
needed to separate an uncontrollable mode from the forcing. The remaining
open-loop obligation is the PBH separation stating that every antistable state
outside `V*(ker H) + R` is detected by such a functional; that separation is
*not* proved here and is recorded in the handoff at the end of the file. -/

/-- **Readout functionals are blind to the reachable input channel.** If the
continuous readout functional `ρ` satisfies `ρ (sys.C ·) = 0` on the reachable
subspace `⟨sys.A | im sys.B⟩`, then the readout of the forced variation-of-
constants trajectory equals the readout of the autonomous orbit:
`ρ (sys.C x_u(t)) = ρ (sys.C (e^{tA} x))`.

This is `variationOfConstants_sub_expFlow_mem_reachableSubspace` combined with
the annihilation hypothesis: the forcing contribution is reachable, so `ρ`
forgets it. -/
theorem readout_functional_variationOfConstants_eq_expFlow
    (sys : LinearSystem ℝ X U Z) (ρ : Z →L[ℝ] ℝ)
    (hR : LinearMap.reachableSubspace sys.A sys.B ≤
      LinearMap.ker (ρ.toLinearMap.comp sys.C))
    (x : X) {u : ℝ → U} (hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume)
    (t : ℝ) :
    ρ (sys.C (sys.variationOfConstants 0 x u t)) =
      ρ (sys.C (NormedSpace.exp (t • sys.A.toContinuousLinearMap) x)) := by
  have hmem := variationOfConstants_sub_expFlow_mem_reachableSubspace sys x hu t
  set r : X := sys.variationOfConstants 0 x u t - sys.expFlow t x with hr
  have hrmem : r ∈ LinearMap.reachableSubspace sys.A sys.B := hmem
  have hker : ρ (sys.C r) = 0 := by
    have := hR hrmem
    simpa [LinearMap.mem_ker, LinearMap.comp_apply] using this
  have hvar : sys.variationOfConstants 0 x u t = sys.expFlow t x + r := by
    rw [hr]; abel
  rw [hvar, map_add, map_add, hker, add_zero]
  rfl

/-- **Reachable-quotient readout non-cancellation.** Let `ρ : Z →L[ℝ] ℝ` be a
continuous readout functional whose induced state functional `ρ ∘ H` annihilates
the reachable subspace `R = ⟨A | im B⟩`. If `x` is antistable and its readout is
not annihilated by `ρ`, then no locally integrable open-loop input can make the
controlled output decay.

Proof: the reachable-quotient cancellation writes the forced trajectory as
`x_u(t) = e^{tA} x + r_t` with `r_t ∈ R`; since `ρ H` vanishes on `R`,
`ρ (H x_u(t)) = ρ (H (e^{tA} x))`. Continuity of `ρ` transports the decay of
`H x_u(t)` to the scalar trajectory `t ↦ ρ (H (e^{tA} x))`, and the accepted
antistable readout theorem `LinearMap.antistable_readout_forces_unobservable`
forces `ρ (H x) = 0`, contradicting the detection hypothesis. -/
theorem not_isOutputStabilizable_of_antistable_readout_functional
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) (ρ : Z →L[ℝ] ℝ)
    (hR : LinearMap.reachableSubspace A B ≤ LinearMap.ker (ρ.toLinearMap.comp H))
    {x : X} (hx : x ∈ LinearMap.unstableSubspace A) (hxρ : ρ (H x) ≠ 0) :
    ¬ IsOutputStabilizable (⟨A, B, H, 0⟩ : LinearSystem ℝ X U Z) H x := by
  rintro ⟨u, hu, htend⟩
  let sys : LinearSystem ℝ X U Z := ⟨A, B, H, 0⟩
  have hR' : LinearMap.reachableSubspace sys.A sys.B ≤
      LinearMap.ker (ρ.toLinearMap.comp sys.C) := hR
  have hρtend : Filter.Tendsto (fun t : ℝ => ρ (H (sys.variationOfConstants 0 x u t)))
      Filter.atTop (nhds 0) := by
    have h1 := (ρ.continuous.tendsto 0).comp htend
    simpa [Function.comp_def, sys] using h1
  have hsame : ∀ t : ℝ, ρ (H (sys.variationOfConstants 0 x u t)) =
      ρ (H (NormedSpace.exp (t • A.toContinuousLinearMap) x)) :=
    fun t => readout_functional_variationOfConstants_eq_expFlow sys ρ hR' x hu t
  have hdecA : Filter.Tendsto
      (fun t : ℝ => ρ (H (NormedSpace.exp (t • A.toContinuousLinearMap) x)))
      Filter.atTop (nhds 0) :=
    hρtend.congr' (Filter.Eventually.of_forall fun t => hsame t)
  have hunobs := LinearMap.antistable_readout_forces_unobservable A
    (ρ.toLinearMap.comp H) hx hdecA
  have hxker : x ∈ LinearMap.ker (ρ.toLinearMap.comp H) :=
    LinearMap.unobservableSubspace_le_ker (ρ.toLinearMap.comp H) A hunobs
  exact hxρ (LinearMap.mem_ker.mp hxker)

/-- **Quotient spectral non-cancellation for a general state.** This is the
stable/antistable form of
`not_isOutputStabilizable_of_antistable_readout_functional` that isolates the
"antistable observable component". Let `x = x_g + x_b` with `x_g` in the stable
subspace `X_g(A)` and `x_b` in the antistable subspace `X_b(A)`. If `x` is
open-loop output-stabilizable and the readout functional `ρ ∘ H` annihilates the
reachable subspace, then the antistable part `x_b` is invisible to `ρ`:
`ρ (H x_b) = 0`.

Proof: the stable component has decaying readout
(`tendsto_readout_exp_of_mem_hurwitzSubspace`) and the reachable part is killed
by `ρ ∘ H`, so the decay of `H x_u(·)` transports to
`t ↦ ρ (H (e^{tA} x_b))`; the antistable readout theorem then gives
`ρ (H x_b) = 0`. -/
theorem readout_functional_eq_zero_on_unstable_of_isOutputStabilizable
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) (ρ : Z →L[ℝ] ℝ)
    (hR : LinearMap.reachableSubspace A B ≤ LinearMap.ker (ρ.toLinearMap.comp H))
    {x xg xb : X} (hx : x = xg + xb)
    (hg : xg ∈ LinearMap.hurwitzSubspace A) (hb : xb ∈ LinearMap.unstableSubspace A)
    (h : IsOutputStabilizable (⟨A, B, H, 0⟩ : LinearSystem ℝ X U Z) H x) :
    ρ (H xb) = 0 := by
  rcases h with ⟨u, hu, htend⟩
  let sys : LinearSystem ℝ X U Z := ⟨A, B, H, 0⟩
  have hR' : LinearMap.reachableSubspace sys.A sys.B ≤
      LinearMap.ker (ρ.toLinearMap.comp sys.C) := hR
  have hρtend : Filter.Tendsto (fun t : ℝ => ρ (H (sys.variationOfConstants 0 x u t)))
      Filter.atTop (nhds 0) := by
    have h1 := (ρ.continuous.tendsto 0).comp htend
    simpa [Function.comp_def, sys] using h1
  have hLvar : ∀ t : ℝ, ρ (H (sys.variationOfConstants 0 x u t)) =
      ρ (H (NormedSpace.exp (t • A.toContinuousLinearMap) x)) :=
    fun t => readout_functional_variationOfConstants_eq_expFlow sys ρ hR' x hu t
  have hdecA : Filter.Tendsto
      (fun t : ℝ => ρ (H (NormedSpace.exp (t • A.toContinuousLinearMap) x)))
      Filter.atTop (nhds 0) :=
    hρtend.congr' (Filter.Eventually.of_forall fun t => hLvar t)
  have hgdec : Filter.Tendsto
      (fun t : ℝ => ρ (H (NormedSpace.exp (t • A.toContinuousLinearMap) xg)))
      Filter.atTop (nhds 0) := by
    have hflow := tendsto_readout_exp_of_mem_hurwitzSubspace A (ρ.toLinearMap.comp H) hg
    simpa [LinearMap.comp_apply] using hflow
  have hxsplit : (fun t : ℝ => ρ (H (NormedSpace.exp (t • A.toContinuousLinearMap) x))) =
      fun t : ℝ => ρ (H (NormedSpace.exp (t • A.toContinuousLinearMap) xg)) +
        ρ (H (NormedSpace.exp (t • A.toContinuousLinearMap) xb)) := by
    funext t
    rw [hx, map_add, map_add, map_add]
  have hbdec : Filter.Tendsto
      (fun t : ℝ => ρ (H (NormedSpace.exp (t • A.toContinuousLinearMap) xb)))
      Filter.atTop (nhds 0) := by
    have h' := hdecA
    rw [hxsplit] at h'
    simpa using h'.sub hgdec
  have hunobs := LinearMap.antistable_readout_forces_unobservable A
    (ρ.toLinearMap.comp H) hb hbdec
  have hxker : xb ∈ LinearMap.ker (ρ.toLinearMap.comp H) :=
    LinearMap.unobservableSubspace_le_ker (ρ.toLinearMap.comp H) A hunobs
  exact LinearMap.mem_ker.mp hxker

end WgSubspace

/-! ### PBH/annihilator separation of the reachable sum

The functional route to the `W_g(ker H)` necessity replaces the forced open-loop
trajectory by the autonomous orbit modulo the reachable subspace: for every
locally integrable input `u`, `x_u(t) - e^{tA} x ∈ R = ⟨A | im B⟩`
(`variationOfConstants_sub_expFlow_mem_reachableSubspace`). Consequently a
continuous readout functional `ρ` with `R ≤ ker (ρ ∘ H)` sees only the
autonomous orbit (`readout_functional_variationOfConstants_eq_expFlow`), and a
decaying readout forces `ρ (H (e^{tA} x)) → 0`.

The separation question is therefore: *which states are detected by some such
`ρ`?* A single functional `ρ ∘ H` is not enough — the example
`A = [[0,1],[0,0]]`, `B = 0`, `H = e₁*` has `e₂ ∉ V*(ker H) + R` but
`H e₂ = 0`, so no readout functional can see it. The correct family is the
**observability chain** `ρ ∘ H ∘ Aᵏ`. Its common kernel is exactly
`V*(ker H ⊔ ⟨A | im B⟩)`:

* `mem_controlledInvariantSubspace_sup_reachableSubspace_iff` — the orbit
description `x ∈ V*(ker H ⊔ R) ↔ ∀ k, Aᵏ x ∈ ker H + R`;
* `exists_readout_functional_chain_of_notMem_controlledInvariantSubspace_sup_reachable`
— the PBH/annihilator separation: every `x ∉ V*(ker H ⊔ R)` is detected by
some `k` and `ρ` with `R ≤ ker (ρ ∘ H)` and `ρ (H (Aᵏ x)) ≠ 0`;
* `forall_readout_functional_chain_eq_zero_iff_mem` — the sharp annihilator
duality packaging the two directions.

The threshold is `V*(ker H ⊔ R)`, which can be strictly larger than
`V*(ker H) + R`; the separation is *false* for the weaker hypothesis
`x ∉ V*(ker H) + R` whenever `H` maps `R` onto the whole readout space (then
`R ≤ ker (ρ ∘ H)` forces `ρ = 0`). This is the exact obstruction recorded in the
handoff at the end of the file: the functional method alone cannot finish the
open-loop necessity, because the interesting states lie in
`V*(ker H ⊔ R) \ (V*(ker H) + R)`.

Source: Trentelman–Stoorvogel–Hautus, Theorem 4.37 (the identity
`W_g(ker H) = V*(ker H) + Xstab`) and its duality proof; the annihilator
separation is the finite-dimensional PBH statement on the quotient
`X ⧸ V*(ker H ⊔ R)`. -/

section ReachableSeparation

variable {X U Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- **Orbit description of `V*(ker H ⊔ ⟨A | im B⟩)`.** A state lies in the
largest controlled invariant subspace contained in `ker H ⊔ ⟨A | im B⟩` if and
only if its whole `A`-orbit stays in `ker H ⊔ ⟨A | im B⟩`.

The forward direction uses that `V := V*(ker H ⊔ R)` contains the reachable
subspace `R = ⟨A | im B⟩` (which is controlled invariant) and is therefore
`A`-invariant, since `A V ⊆ V + im B ⊆ V + R = V`. The backward direction exhibits
the orbit set itself as a controlled invariant subspace contained in
`ker H ⊔ R`, and applies maximality of `V*(·)`. -/
theorem mem_controlledInvariantSubspace_sup_reachableSubspace_iff
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) (x : X) :
    x ∈ LinearMap.controlledInvariantSubspace A B
        (LinearMap.ker H ⊔ LinearMap.reachableSubspace A B) ↔
      ∀ k : ℕ, (A ^ k) x ∈ LinearMap.ker H ⊔ LinearMap.reachableSubspace A B := by
  set K : Submodule ℝ X := LinearMap.ker H
  set R : Submodule ℝ X := LinearMap.reachableSubspace A B
  constructor
  · intro hx k
    set V : Submodule ℝ X := LinearMap.controlledInvariantSubspace A B (K ⊔ R)
    have hR_ci : LinearMap.IsControlledInvariant A B R := by
      intro y hy
      rw [Submodule.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      exact Submodule.mem_sup.mpr ⟨A z, LinearMap.map_reachableSubspace_le A B ⟨z, hz, rfl⟩,
        0, (LinearMap.range B).zero_mem, by simp⟩
    have hR_le_V : R ≤ V :=
      LinearMap.le_controlledInvariantSubspace le_sup_right hR_ci
    have hV_ci : LinearMap.IsControlledInvariant A B V :=
      LinearMap.isControlledInvariant_controlledInvariantSubspace A B (K ⊔ R)
    have hAV : Submodule.map A V ≤ V := by
      refine le_trans hV_ci ?_
      rw [sup_le_iff]
      exact ⟨le_rfl, le_trans (LinearMap.range_le_reachableSubspace A B) hR_le_V⟩
    exact LinearMap.controlledInvariantSubspace_le_K A B (K ⊔ R)
      (Submodule.map_pow_le hAV k ⟨x, hx, rfl⟩)
  · intro hx
    let W : Submodule ℝ X :=
      { carrier := {y | ∀ k : ℕ, (A ^ k) y ∈ K ⊔ R}
        zero_mem' := fun k => by rw [map_zero]; exact (K ⊔ R).zero_mem
        add_mem' := fun {y z} hy hz k => by
          rw [map_add]
          exact (K ⊔ R).add_mem (hy k) (hz k)
        smul_mem' := fun c {y} hy k => by
          rw [map_smul]
          exact (K ⊔ R).smul_mem c (hy k) }
    have hW_le : W ≤ K ⊔ R := fun y hy => hy 0
    have hW_ci : LinearMap.IsControlledInvariant A B W := by
      intro y hy
      rw [Submodule.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      refine Submodule.mem_sup.mpr ⟨A z, ?_, 0, (LinearMap.range B).zero_mem, by simp⟩
      intro k
      have h := hz (k + 1)
      rw [pow_succ] at h
      exact h
    exact LinearMap.le_controlledInvariantSubspace hW_le hW_ci hx

/-- **`V*(ker H) + ⟨A | im B⟩` lies in `V*(ker H ⊔ ⟨A | im B⟩)`.** The largest
controlled invariant subspace contained in `ker H` and the reachable subspace
are both contained in the largest controlled invariant subspace contained in
their sum.

This containment is what makes the PBH/annihilator separation a statement about
a *strictly larger* threshold than the task's request: the chain functionals have
common kernel `V*(ker H ⊔ R)`, so they cannot separate the intermediate states in
`V*(ker H ⊔ R) \ (V*(ker H) + R)`. -/
theorem sup_controlledInvariantSubspace_reachableSubspace_le
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    LinearMap.controlledInvariantSubspace A B (LinearMap.ker H) ⊔
        LinearMap.reachableSubspace A B ≤
      LinearMap.controlledInvariantSubspace A B
        (LinearMap.ker H ⊔ LinearMap.reachableSubspace A B) := by
  refine sup_le ?_ ?_
  · exact LinearMap.le_controlledInvariantSubspace
      (le_trans (LinearMap.controlledInvariantSubspace_le_K A B (LinearMap.ker H)) le_sup_left)
      (LinearMap.isControlledInvariant_controlledInvariantSubspace A B (LinearMap.ker H))
  · refine LinearMap.le_controlledInvariantSubspace le_sup_right ?_
    intro y hy
    rw [Submodule.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact Submodule.mem_sup.mpr ⟨A z, LinearMap.map_reachableSubspace_le A B ⟨z, hz, rfl⟩,
      0, (LinearMap.range B).zero_mem, by simp⟩

end ReachableSeparation

section ReadoutSeparation

variable {X U Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-- **PBH/annihilator separation.** Every state outside the largest controlled
invariant subspace contained in `ker H ⊔ ⟨A | im B⟩` is detected by some
functional in the observability chain: there are `k : ℕ` and `ρ : Z →L[ℝ] ℝ`
with `⟨A | im B⟩ ≤ ker (ρ ∘ H)` and `ρ (H (Aᵏ x)) ≠ 0`.

The proof is pure linear algebra once the orbit description
`mem_controlledInvariantSubspace_sup_reachableSubspace_iff` is available: if the
class of `H (Aᵏ x)` lay in `H ⟨A | im B⟩`, then `Aᵏ x` would lie in
`ker H + ⟨A | im B⟩`, contradicting the orbit description. The dual annihilator
`Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff` then produces an
algebraic functional vanishing on `H ⟨A | im B⟩` and nonzero at `H (Aᵏ x)`;
finite-dimensionality of the readout space makes it continuous.

No spectral (stable/antistable) hypothesis is needed: the separation holds for
every such state, in particular for the antistable states appearing in the
open-loop necessity. -/
theorem exists_readout_functional_chain_of_notMem_controlledInvariantSubspace_sup_reachable
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) {x : X}
    (hx : x ∉ LinearMap.controlledInvariantSubspace A B
        (LinearMap.ker H ⊔ LinearMap.reachableSubspace A B)) :
    ∃ (k : ℕ) (ρ : Z →L[ℝ] ℝ),
      LinearMap.reachableSubspace A B ≤ LinearMap.ker (ρ.toLinearMap.comp H) ∧
      ρ (H ((A ^ k) x)) ≠ 0 := by
  have hnot := (mem_controlledInvariantSubspace_sup_reachableSubspace_iff A B H x).not.mp hx
  push Not at hnot
  obtain ⟨k, hk⟩ := hnot
  have hv : H ((A ^ k) x) ∉ Submodule.map H (LinearMap.reachableSubspace A B) := by
    intro hv'
    rw [Submodule.mem_map] at hv'
    obtain ⟨r, hr, hHr⟩ := hv'
    apply hk
    refine Submodule.mem_sup.mpr ⟨(A ^ k) x - r, ?_, r, hr, by abel⟩
    rw [LinearMap.mem_ker, map_sub, hHr, sub_self]
  have hex : ∃ φ : Module.Dual ℝ Z,
      φ ∈ (Submodule.map H (LinearMap.reachableSubspace A B)).dualAnnihilator ∧
        φ (H ((A ^ k) x)) ≠ 0 := by
    by_contra h
    apply hv
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro φ hφ
    by_contra hφv
    exact h ⟨φ, hφ, hφv⟩
  obtain ⟨φ, hφmem, hφv⟩ := hex
  refine ⟨k, LinearMap.toContinuousLinearMap φ, ?_, ?_⟩
  · intro r hr
    have h0 : φ (H r) = 0 :=
      (Submodule.mem_dualAnnihilator φ).mp hφmem (H r) ⟨r, hr, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    simpa using h0
  · simpa using hφv

omit [FiniteDimensional ℝ X] in
/-- **Degree-zero separation.** If `x` is not already in `ker H ⊔ ⟨A | im B⟩`,
then a single continuous readout functional separates it: there is
`ρ : Z →L[ℝ] ℝ` with `⟨A | im B⟩ ≤ ker (ρ ∘ H)` and `ρ (H x) ≠ 0`.

This is the `k = 0` case of the chain separation, and the exact range of the
"readout functional" mechanism of the open-loop necessity. It shows why the
task's requested threshold `V*(ker H) + R` is not the right one for this
mechanism: states in `ker H \ V*(ker H)` (an example being
`A = [[0,1],[0,0]]`, `B = 0`, `H = e₁*`, `x = e₂`) satisfy the membership
hypothesis but are invisible to every such functional. -/
theorem exists_readout_functional_of_notMem_ker_sup_reachable
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) {x : X}
    (hx : x ∉ LinearMap.ker H ⊔ LinearMap.reachableSubspace A B) :
    ∃ ρ : Z →L[ℝ] ℝ,
      LinearMap.reachableSubspace A B ≤ LinearMap.ker (ρ.toLinearMap.comp H) ∧
      ρ (H x) ≠ 0 := by
  have hv : H x ∉ Submodule.map H (LinearMap.reachableSubspace A B) := by
    intro hv'
    rw [Submodule.mem_map] at hv'
    obtain ⟨r, hr, hHr⟩ := hv'
    apply hx
    refine Submodule.mem_sup.mpr ⟨x - r, ?_, r, hr, by abel⟩
    rw [LinearMap.mem_ker, map_sub, hHr, sub_self]
  have hex : ∃ φ : Module.Dual ℝ Z,
      φ ∈ (Submodule.map H (LinearMap.reachableSubspace A B)).dualAnnihilator ∧
        φ (H x) ≠ 0 := by
    by_contra h
    apply hv
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro φ hφ
    by_contra hφv
    exact h ⟨φ, hφ, hφv⟩
  obtain ⟨φ, hφmem, hφv⟩ := hex
  refine ⟨LinearMap.toContinuousLinearMap φ, ?_, ?_⟩
  · intro r hr
    have h0 : φ (H r) = 0 :=
      (Submodule.mem_dualAnnihilator φ).mp hφmem (H r) ⟨r, hr, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply]
    simpa using h0
  · simpa using hφv

/-- **Sharp annihilator duality.** The functionals `ρ ∘ H ∘ Aᵏ` with
`⟨A | im B⟩ ≤ ker (ρ ∘ H)` have common kernel exactly
`V*(ker H ⊔ ⟨A | im B⟩)`.

This packages the two directions of the PBH/annihilator separation: membership
in `V*(ker H ⊔ R)` is equivalent to the vanishing of every observability-chain
readout whose first factor annihilates the reachable subspace. -/
theorem forall_readout_functional_chain_eq_zero_iff_mem
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) (x : X) :
    (∀ (k : ℕ) (ρ : Z →L[ℝ] ℝ),
        LinearMap.reachableSubspace A B ≤ LinearMap.ker (ρ.toLinearMap.comp H) →
        ρ (H ((A ^ k) x)) = 0) ↔
      x ∈ LinearMap.controlledInvariantSubspace A B
        (LinearMap.ker H ⊔ LinearMap.reachableSubspace A B) := by
  constructor
  · intro h
    by_contra hx
    obtain ⟨k, ρ, hR, hρ⟩ :=
      exists_readout_functional_chain_of_notMem_controlledInvariantSubspace_sup_reachable
        A B H hx
    exact hρ (h k ρ hR)
  · intro hx k ρ hR
    have hmem := (mem_controlledInvariantSubspace_sup_reachableSubspace_iff A B H x).mp hx k
    rw [Submodule.mem_sup] at hmem
    obtain ⟨a, ha, r, hr, har⟩ := hmem
    have hker : H ((A ^ k) x) = H r := by
      rw [← har, map_add, LinearMap.mem_ker.mp ha, zero_add]
    rw [hker]
    have h0 := hR hr
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at h0
    exact h0

end ReadoutSeparation

/-! ### The dual conditioned-invariant/detectable condition

The second half of the Corollary 6.22 pair is the output-injection condition
`S*(im E) ∩ Xdet(C, A) ≤ ker H`. Its dual form is the transposed `W_g` inclusion
`im Hᵀ ≤ V*(ker Eᵀ) + Xstab(Aᵀ, Cᵀ)`. The derivation below rewrites
`Xstab(Aᵀ, Cᵀ)` as `⟨Aᵀ | im Cᵀ⟩ ⊔ X_g(Aᵀ)` using
`stabilizableSubspace` and the accepted basis-agnostic
`stableSubspaceOfBasis_finBasis_eq_hurwitzSubspace`, then applies the accepted
duality `conditionedInvariant_inf_detectable_le_ker_iff_dualStableCondition`.
The detectability content enters through the same duality as
`isDetectable_iff_detectableSubspace_eq_bot`: the subspace `Xdet` vanishes
exactly when `(C, A)` is detectable, so the inclusion is the detectable-top
statement of Trentelman–Stoorvogel–Hautus Theorem 5.16. -/

section DualCondition

variable {X Y D Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [AddCommGroup Y] [Module ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- **The conditioned-invariant/detectable condition from its dual `W_g`
inclusion.** If the transposed disturbance image `im Hᵀ` lies in the transposed
`W_g(Eᵀ) = V*(ker Eᵀ) + Xstab(Aᵀ, Cᵀ)`, then the primal output-injection
condition `S*(im E) ∩ Xdet(C, A) ≤ ker H` holds. This is the dual half of the
Theorem 4.37 necessity bridge: it turns the transposed algebraic `W_g`
characterisation into the conditioned-invariant condition used by Corollary
6.22, with `Xstab` expanded through `stabilizableSubspace` and the stable
subspace of the transpose. -/
theorem conditionedInvariant_inf_detectable_le_ker_of_dual_mem_outputStabilizableSubspace
    (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : LinearMap.range H.dualMap ≤
      LinearMap.controlledInvariantSubspace A.dualMap C.dualMap
          (LinearMap.range E).dualAnnihilator ⊔
        LinearMap.stabilizableSubspace A.dualMap C.dualMap) :
    LinearMap.conditionedInvariantSubspace C A (LinearMap.range E) ⊓
        LinearMap.detectableSubspace C A ≤ LinearMap.ker H := by
  rw [LinearMap.conditionedInvariant_inf_detectable_le_ker_iff_dualStableCondition]
  have hstab : LinearMap.stabilizableSubspace A.dualMap C.dualMap =
      LinearMap.reachableSubspace A.dualMap C.dualMap ⊔
        LinearMap.stableSubspaceOfBasis
          (Module.finBasis ℝ (Module.Dual ℝ X)) A.dualMap := by
    rw [LinearMap.stabilizableSubspace,
      ← LinearMap.stableSubspaceOfBasis_finBasis_eq_hurwitzSubspace A.dualMap, sup_comm]
  rwa [hstab] at h

end DualCondition

end LinearSystem

/-! ### Remaining blocker for unrestricted-input `W_g` necessity

The state-feedback *sufficiency* half of Trentelman–Stoorvogel–Hautus Theorem
4.37 / 4.39 is now available in algebraic form:

* `LinearSystem.outputStabilizableSubspace` — the algebraic `W_g(ker H)`,
  `V*(ker H) ⊔ Xstab(A, B)`;
* `LinearSystem.map_outputStabilizableSubspace_le`,
  `LinearSystem.range_le_outputStabilizableSubspace` — its structural
  properties (`A`-invariance and `im B ⊆ W_g`);
* `LinearSystem.exists_feedback_tendsto_readout_of_mem_outputStabilizableSubspace`
  — every `x ∈ W_g(ker H)` admits a state feedback `F` making
  `t ↦ H (e^{t(A + B F)} x)` decay to zero;
* `LinearSystem.IsOutputStabilizable` — the source's open-loop trajectory
  predicate, with the input quantifier explicit (`∃ u : ℝ → U,` locally
  integrable, `H (x_u(t, x)) → 0`);
* `LinearSystem.conditionedInvariant_inf_detectable_le_ker_of_dual_mem_outputStabilizableSubspace`
  — the conditioned-invariant/detectable dual condition derived from the
  transposed `W_g` inclusion (and hence, through
  `LinearMap.isDetectable_iff_detectableSubspace_eq_bot`, from the transposed
  detectable-top characterisation).

The necessity direction for an *arbitrary locally integrable input* is not
formalised. Its exact missing statement is:

```lean
theorem LinearSystem.mem_outputStabilizableSubspace_of_isOutputStabilizable
    (sys : LinearSystem ℝ X U Z) (H : X →ₗ[ℝ] Z) (x : X)
    (h : IsOutputStabilizable sys H x) :
    x ∈ outputStabilizableSubspace sys.A sys.B H
```

The source proof (PDF page 115 / printed page 99) decomposes a witness Bohl
input `u` and trajectory `x_u(·, x)` as `u = u₁ + u₂`,
`x = x₁ + x₂` with the spectra of `u₁, x₁` in `C_g` and of `u₂, x₂` in `C_b`,
uses that the two sides of the error equation have disjoint spectra to split it
into two state equations, concludes `x₁(0) ∈ Xstab` from the stable trajectory
and `x₂(0) ∈ V*(ker H)` from `H x₂ = 0`. The finite-Bohl *forcing-image*
version of this argument is now proved by `finiteBohlWBridge` below, using
quotient non-cancellation of the projected ODE residuals. It does not extend
the conclusion to every locally integrable input or settle the full
dynamic-controller equivalence of Corollary 6.22. -/

/-! ### The `B = 0` reduction added by the spectral-decomposition task

The `B = 0` case of the `W_g(ker H)` necessity is now reduced to a single explicit
spectral obligation. The algebraic collapses are
`controlledInvariantSubspace_zero_eq_unobservableSubspace` and
`outputStabilizableSubspace_zero_eq_sup_unobservableSubspace`; the stable and
unobservable readout facts are `tendsto_readout_exp_of_mem_hurwitzSubspace` and
`readout_exp_eq_zero_of_mem_unobservableSubspace`; the reduction is
`mem_outputStabilizableSubspace_of_decay_of_B_eq_zero` and its trajectory form
`mem_outputStabilizableSubspace_of_isOutputStabilizable_of_B_eq_zero`, both
taking as hypothesis the *only* missing analytic statement:

`∀ x : X, x ∈ X_b(A) → Tendsto (fun t ↦ H (e^{t A} x)) atTop (nhds 0) →
  x ∈ ⟨ker H | A⟩`.

That statement is not proved here; it is the precise remaining blocker. The
accepted stable/antistable direct sum `hurwitzSubspace_sup_unstableSubspace_eq_top`
and the accepted trajectory bridge
`mem_unobservableSubspace_of_forall_continuousC_expFlow_eq_zero` /
`continuousC_expFlow_eq_zero_of_mem_unobservableSubspace` are the tools a future
attempt needs for the unrestricted predicate. The finite-Bohl forcing-image
decomposition is formalised later in this file, but does not remove the
locally-integrable-input hypothesis here.

The `B = 0` characterisation is now two-sided. The unconditional converse is
`isOutputStabilizable_of_mem_outputStabilizableSubspace_of_B_eq_zero`, packaged
with the forward reduction as
`isOutputStabilizable_iff_mem_outputStabilizableSubspace_of_B_eq_zero`. The
zero-operator non-vacuity witness is `hspectral_zero_operator`, giving the
hypothesis-free instance `isOutputStabilizable_iff_mem_outputStabilizableSubspace_of_zero_operator`.
The general-`B`, unrestricted-input necessity
`mem_outputStabilizableSubspace_of_isOutputStabilizable` remains open. -/

/-! ### The character-independence bridge added by the antistable-readout task

The degree-zero case of the missing Bohl/spectral function decomposition is now
formalised in `Stabilization.lean`:

* `LinearMap.tendsto_inv_mul_geom_sum`: the Cesàro average of a unit-modulus
  geometric progression `n ↦ z ^ n` is `1` for `z = 1` and `0` otherwise;
* `LinearMap.tendsto_zero_of_sum_pow_smul`: a finite sum of *distinct*
  unit-modulus characters with coefficients in a complex normed space cannot
  tend to zero unless every coefficient vanishes.

The second lemma is the cancellation-free core of the antistable readout
statement: it is exactly the step that isolates one character from a sum. The
remaining reduction from this degree-zero statement to the full obligation
`∀ x ∈ X_b(A), Tendsto (fun t ↦ H (e^{tA} x)) atTop (nhds 0) → x ∈ ⟨ker H | A⟩`
is now a finite, precisely-scoped list:

1. *Polynomial-exponential reduction (basis-independent).* Prove that if
   `Σ_{i} exp (t * μ i) • q i t → 0` with `0 ≤ (μ i).re` and `q i` vector
   polynomials, then the whole sum is identically zero. Route: factor out the
   dominant real part `R = max (μ i).re` (multiplying by the bounded factor
   `e^{-Rt}`), discard the strictly smaller real parts (polynomial times a
   decaying exponential), divide by the top power `t^D`, apply
   `tendsto_zero_of_sum_pow_smul` to the resulting leading character sum, and
   induct on `D`. The single missing elementary ingredient is
   "a vector polynomial tending to `0` at `+∞` is identically `0`".
2. *Complex-linear readout transport.* Complexify the real readout `H` and the
   real coordinates of `Stabilization.lean` (`ofRealPi`), or test against
   continuous real-linear functionals and extend them to complex-linear ones
   (`ψ ↦ ψ - i ψ∘(i·)`), so that step 1 applies to `L (e^{t f} z)` for
   `z = ofRealPi (b.equivFun x)` in `unstableComplexSubspace A`.
3. *Differentiate at zero.* If `L (e^{t f} z) ≡ 0`, then all derivatives at
   `0` vanish, i.e. `L (f ^ k z) = 0`; transporting back gives
   `H (A ^ k x) = 0` for all `k`, hence `x ∈ ⟨ker H | A⟩`.

None of these three steps is claimed here. In particular, the `hspectral`
hypothesis of `mem_outputStabilizableSubspace_of_decay_of_B_eq_zero` is still an
explicit hypothesis, not a proved theorem, and the general-`B` necessity is not
claimed. -/

/-! ### The state-feedback lift added by the general-`B` task

The general-`B` necessity is now proved in its **state-feedback** form, and the
`hspectral` obligation is discharged (`hspectral_holds`, via the accepted
antistable readout theorem `LinearMap.antistable_readout_forces_unobservable`):

* `LinearSystem.stabilizableSubspace_add_feedback_eq` — the stabilizable
  subspace is unchanged by state feedback, `Xstab(A + B F, B) = Xstab(A, B)`;
* `LinearSystem.mem_outputStabilizableSubspace_of_feedback_decay` — if
  `t ↦ H (e^{t (A + B F)} x) → 0` for some `F`, then
  `x ∈ W_g(ker H) = V*(ker H) ⊔ Xstab(A, B)`;
* `LinearSystem.exists_feedback_tendsto_readout_iff_mem_outputStabilizableSubspace`
  — the resulting two-sided state-feedback characterisation, whose converse is
  the accepted `exists_feedback_tendsto_readout_of_mem_outputStabilizableSubspace`.

Proof route of the necessity: split `x = x_g + x_b` along the accepted
stable/antistable direct sum for `A_F = A + B F`. The stable part is in
`Xstab(A, B)` by `hurwitzSubspace_le_stabilizableSubspace` and the feedback
invariance above. From the decay of `H (e^{t A_F} x)` and of `H (e^{t A_F} x_g)`
the antistable part inherits `H (e^{t A_F} x_b) → 0`, so the accepted
`LinearMap.antistable_readout_forces_unobservable` makes `x_b` `A_F`-unobservable,
hence `A_F`-invariant and contained in `ker H`, hence `(A, B)`-controlled
invariant because `A = A_F - B F`; finally
`LinearMap.le_controlledInvariantSubspace` puts `x_b ∈ V*(ker H)`.

#### Exact remaining obligation

The **open-loop** predicate `IsOutputStabilizable` quantifies over an arbitrary
locally integrable input rather than a state feedback, so the chain
`feedback-decay ⟹ open-loop-decay` is the easy direction and the converse is the
strictly stronger obligation:

```lean
theorem LinearSystem.mem_outputStabilizableSubspace_of_isOutputStabilizable
    (sys : LinearSystem ℝ X U Z) (H : X →ₗ[ℝ] Z) (x : X)
    (h : IsOutputStabilizable sys H x) :
    x ∈ outputStabilizableSubspace sys.A sys.B H
```

It is **not** claimed here. The obstruction is genuinely the input-cancellation
term: writing `x_u(t) = e^{tA} x + r_t` with `r_t ∈ reachableSubspace A B`, one
has `H x_u(t) = H (e^{tA} x) + H r_t`, and the driven reachable readout `H r_t`
can cancel the autonomous antistable readout `H (e^{tA} x_b)` whenever the input
channel reaches the corresponding unstable mode. In the two-dimensional model
`A = diag(-1, 1)`, `B = e₁`, `H = a e₁* + b e₂*` (`a, b ≠ 0`) an unbounded input
`u(s) = -2 (b/a) e^{s}` makes `H x_u(t) = b e^{-t} → 0`; the cancellation succeeds
exactly because `H` detects the reachable direction, which in turn makes `ker H`
controlled invariant and pushes `x_b` into `V*(ker H)`. The general statement is
therefore a spectral statement: a state outside `V*(ker H) + Xstab` carries an
*uncontrollable* unstable generalized eigendirection whose readout cannot be
cancelled through `im B`.

A first attempt at a dual/PBH proof — pick a functional `L` with `L ∘ A = μ L`,
`L ∘ B = 0`, `L|ker H = 0`, `μ.re ≥ 0`, `L x ≠ 0`, write `L = λ ∘ H`, and read
off the contradiction `e^{μ t} L x = L x_u(t) = λ (H x_u(t)) → 0` — is
**insufficient as stated**: it cannot see a state `x ∈ ker H \ W` (where
`L x = 0` for every `L` vanishing on `ker H`), although such states are correctly
excluded, e.g. `A = [[0,1],[0,0]]`, `B = 0`, `H = e₁*`, `x = e₂`. The readout
functional must be taken from the whole observability chain, `L = λ ∘ H ∘ A ^ k`
(and the input-annihilation condition `L ∘ B = 0` then constrains it), which is
precisely the Bohl/spectral projection argument recorded in the two preceding
handoff notes. The accepted ingredients are the PBH converse criteria of
`Stabilization.lean`, the duality APIs of `Duality.lean`, the stable/antistable
direct sum, and the Gramian reachability characterization
`mem_reachableSubspace_orthogonal_of_forall_adjoint_expFlow_eq_zero`.

#### The reachable-quotient cancellation added by this task

The structural half of the input-cancellation obstruction is now formalised as
`LinearSystem.variationOfConstants_sub_expFlow_mem_reachableSubspace`: for every
locally integrable open-loop input the forced trajectory differs from the
autonomous orbit by a reachable state,
`x_u(t) - e^{tA} x ∈ R = ⟨A | im B⟩`, because the forcing
`e^{-(s - t₀)A} (B u(s))` is reachable and `R` is `A`-invariant and closed.
Equivalently, the reachable quotient `X ⧸ R` carries only the autonomous
dynamics: the input term is invisible there. The proof pushes both sides through
the quotient `R.mkQ`, uses `clm_map_exp_smul` to commute the exponential with the
quotient map, and uses `ContinuousLinearMap.intervalIntegral_comp_comm` to kill
the forcing integral because `q (forcing s) = 0` for every `s`.

This isolates the residual gap precisely. Writing `x_u(t) = e^{tA} x + r_t` with
`r_t ∈ R`, the open-loop necessity reduces to the statement that the readout on
the reachable part cannot cancel the autonomous antistable readout unless the
antistable state already lies in `V*(ker H) ⊔ R`. The quotient-autonomy lemma
removes the input from the quotient dynamics; what remains is the *spectral*
statement on the quotient `X ⧸ R`, equivalently on the observable `V*`-free
quotient `X ⧸ (V*(ker H) + R)` discussed above. No proof of that spectral
statement is claimed here; the accepted
`LinearMap.antistable_readout_forces_unobservable` disposes of the *feedback*
case but does not see the forced reachable readout.

#### The quotient spectral non-cancellation added by this task

The reachable-quotient cancellation is complemented by the readout-functional
non-cancellation, which is the correct replacement of the invalid
single-functional PBH shortcut:

* `LinearSystem.readout_functional_variationOfConstants_eq_expFlow` — if the
  continuous readout functional `ρ` annihilates the reachable subspace
  `R = ⟨A | im B⟩` in the sense that `R ≤ ker (ρ ∘ H)`, then for every locally
  integrable input `u` the readout of the forced variation-of-constants
  trajectory is exactly the autonomous readout,
  `ρ (H x_u(t)) = ρ (H (e^{tA} x))`;
* `LinearSystem.not_isOutputStabilizable_of_antistable_readout_functional` —
  an antistable state detected by such a functional (`ρ (H x) ≠ 0`) is not
  open-loop output-stabilizable, because the forced readout equals the
  autonomous readout and `LinearMap.antistable_readout_forces_unobservable`
  would force `ρ (H x) = 0`;
* `LinearSystem.readout_functional_eq_zero_on_unstable_of_isOutputStabilizable`
  — the "no antistable observable component" form: for any stable/antistable
  decomposition `x = x_g + x_b` (`x_g ∈ X_g(A)`, `x_b ∈ X_b(A)`), output
  stabilizability forces the antistable part to lie in the kernel,
  `ρ (H x_b) = 0`.

The functional must annihilate the *whole* reachable subspace (equivalently all
Markov parameters `ρ H A^k B`), which is the observability-chain condition that
separates an uncontrollable mode from the forcing. A single genuine
eigenfunctional is insufficient: the example `A = [[0,1],[0,0]]`, `B = 0`,
`H = e₁*`, `x = e₂` has an observable `x ∉ ker H` on which every functional
vanishing on `ker H` is zero.

#### Exact remaining obligation (PBH separation)

With the analytic half complete, the open-loop necessity reduces to a single
*separation* statement. Let `V = V*(ker H)` and `R = ⟨A | im B⟩`. The missing
lemma is: every antistable state `x_b ∈ X_b(A)` outside `V + R` is detected by a
continuous readout functional `ρ` with `R ≤ ker (ρ ∘ H)` and `ρ (H x_b) ≠ 0`.
Combined with `readout_functional_eq_zero_on_unstable_of_isOutputStabilizable`,
this gives `x_b ∈ V + R`, hence `x ∈ V + Xstab = outputStabilizableSubspace A B H`,
and with it the full open-loop theorem
`LinearSystem.mem_outputStabilizableSubspace_of_isOutputStabilizable`.

The separation is a finite-dimensional PBH/duality statement on the quotient
`X ⧸ (V + R)`: an antistable class of `X ⧸ (V + R)` must be visible to some
readout functional `ρ ∘ H` whose reachable part is annihilated. The accepted
ingredients are the PBH converse criteria
(`LinearMap.isStabilizable_converse_of_uncontrollableEigenvalue`,
`LinearMap.isDetectable_converse_of_unobservableEigenvalue`), the reachable/
unobservable duality `LinearMap.reachableSubspace_dualMap`, the stable/antistable
direct sum, and the maximality
`LinearMap.isGreatest_controlledInvariantSubspace`. This statement is **not**
proved here, and the full open-loop theorem
`LinearSystem.mem_outputStabilizableSubspace_of_isOutputStabilizable` is
consequently **not** claimed. -/

/-! ### PBH/annihilator separation added by this task

This attempt isolated and proved the sharp algebraic separation behind the
open-loop necessity. The new declarations are:

* `LinearSystem.mem_controlledInvariantSubspace_sup_reachableSubspace_iff` — the
  orbit description `x ∈ V*(ker H ⊔ ⟨A | im B⟩) ↔ ∀ k, Aᵏ x ∈ ker H + ⟨A | im B⟩`,
  proved from the extremal characterisations (`isGreatest_controlledInvariantSubspace`)
  and the fact that `V*(ker H ⊔ R)` is `A`-invariant;
* `LinearSystem.exists_readout_functional_chain_of_notMem_controlledInvariantSubspace_sup_reachable`
  — every `x ∉ V*(ker H ⊔ R)` is detected by some `k : ℕ` and continuous
  `ρ : Z →L[ℝ] ℝ` with `R ≤ ker (ρ ∘ H)` and `ρ (H (Aᵏ x)) ≠ 0`;
* `LinearSystem.forall_readout_functional_chain_eq_zero_iff_mem` — the sharp
  annihilator duality packaging the two directions;
* `LinearSystem.sup_controlledInvariantSubspace_reachableSubspace_le` — the
  containment `V*(ker H) + R ≤ V*(ker H ⊔ R)` showing that the chain threshold
  is strictly larger than the task's requested one;
* `LinearSystem.exists_readout_functional_of_notMem_ker_sup_reachable` — the
  degree-zero separation: if `x ∉ ker H + R` then a single `ρ` with
  `R ≤ ker (ρ ∘ H)` detects `x`, which is the exact reach of the readout
  functional when `k = 0`.

#### Why the requested statement is false as stated

The task's separation asks for `x_b ∉ V*(ker H) + R → ∃ ρ, R ≤ ker (ρ∘H) ∧
ρ (H x_b) ≠ 0`. This fails for two independent reasons:

1. *The single functional `ρ ∘ H` is blind to `ker H`.* The example
   `A = [[0,1],[0,0]]`, `B = 0`, `H = e₁*`, `x_b = e₂` has `V*(ker H) = R = 0`,
   so `x_b ∉ V*(ker H) + R`, but `H x_b = 0`, hence `ρ (H x_b) = 0` for every
   `ρ`. The observability chain `ρ ∘ H ∘ Aᵏ` is essential: here `k = 1` and
   `H (A x_b) = 1`.
2. *Even the chain cannot separate the weaker threshold `V*(ker H) + R`.* The
   common kernel of the chain functionals is exactly `V*(ker H ⊔ R)`, which can
   be strictly larger than `V*(ker H) + R`. The two agree only when the
   `im B`-channel adds nothing to `V*`; in general the largest controlled
   invariant subspace contained in `ker H + R` properly contains the sum of the
   largest controlled invariant subspace in `ker H` and `R`. A concrete
   obstruction: when `H` maps `R` onto the whole readout space `Z`, the condition
   `R ≤ ker (ρ ∘ H)` forces `ρ = 0`, so *no* readout functional separates any
   state, although such states may well lie outside `V*(ker H) + R`.

#### Exact remaining obligation

The accepted `readout_functional_eq_zero_on_unstable_of_isOutputStabilizable`
only gives, for the antistable part `x_b`, `ρ (H x_b) = 0` for all `ρ` with
`R ≤ ker (ρ ∘ H)`, i.e. `x_b ∈ ker H + R`. The chain separation would need the
decay of the *chain* readouts `t ↦ ρ (H (Aᵏ x_u(t)))`, which does **not** follow
from `H x_u(t) → 0` because the unobservability-chain operator `Aᵏ` is
unbounded. The states in `V*(ker H ⊔ R) \ (V*(ker H) + R)` are precisely those
the functional method cannot reach; deciding them is the genuine Bohl/spectral
input-cancellation obligation recorded above. The corresponding spectral
obstruction is the transfer-function pole structure of `H (sI - A)⁻¹ B`: an
unstable uncontrollable eigenvalue has no pole in `(sI - A)⁻¹ B`, so its
autonomous readout cannot be cancelled by the input, and the state is not
output-stabilizable. This is the PBH/spectral content, not a readout-functional
separation.

The full open-loop theorem
`LinearSystem.mem_outputStabilizableSubspace_of_isOutputStabilizable` is
therefore still **not** claimed, and no placeholder or unsupported assumption is
introduced. -/

/-! ### The Bohl/transfer-function input projection: nonzero autonomous residue

This task isolated the *pole/residue* content of the open-loop necessity. Let
`ρ : X →L[ℝ] ℝ` be a continuous linear readout functional that is a **left
eigenfunctional** of the state map,

`ρ (A y) = lam * ρ y`   with   `0 ≤ lam`,

and that **annihilates the input channel**, `ρ (B v) = 0` — equivalently `ρ`
vanishes on the reachable subspace `⟨A | im B⟩` (an *uncontrollable* mode).
Then `ρ` cannot see the forcing at all: the forced readout is exactly the
autonomous residue `ρ (x_u(t)) = e^{lam t} ρ x`. When `ρ x ≠ 0` this residue is
bounded away from zero because `e^{lam t} ≥ 1` for `t ≥ 0`. If in addition `ρ`
is the readout `ψ ∘ H`, then a decaying controlled output `H x_u(t) → 0` forces
`ρ x = 0`: the pole of the readout transfer expression at `lam` has nonzero
autonomous residue `ρ x`, while the input transfer `ρ (sI - A)⁻¹ B` has **no**
pole there because `ρ B = 0`, so the input channel cannot cancel the mode.

The declarations are:

* `LinearMap.eigenfunctional_exp_apply` — the residue identity
  `ρ (exp (t • A) y) = e^{lam t} ρ y` for a left eigenfunctional, proved by
  expanding the exponential series and using `ρ (Aⁿ y) = lamⁿ ρ y`;
* `LinearSystem.forcing_eigenfunctional_eq_zero` — the forcing integrand is
  annihilated, `ρ (exp (-(s - t₀) • A) (B u(s))) = 0`;
* `LinearSystem.variationOfConstants_eigenfunctional` — the transfer-function
  residue `ρ (x_u(t)) = e^{lam t} ρ x` for every locally integrable input;
* `LinearSystem.not_isOutputStabilizable_of_eigenfunctional_readout` — an
  uncontrollable antistable eigenfunctional that factors through the readout
  (`ρ = ψ ∘ H`) and detects `x` certifies that `x` is not open-loop
  output-stabilizable;
* the `_complex` companions `LinearMap.eigenfunctional_exp_apply_complex`,
  `LinearSystem.forcing_eigenfunctional_eq_zero_complex`,
  `LinearSystem.variationOfConstants_eigenfunctional_complex` and
  `LinearSystem.not_isOutputStabilizable_of_eigenfunctional_readout_complex`
  cover the non-real conjugate pole pairs of a real rotation, using only
  `|e^{t lam}| = e^{t lam.re} ≥ 1` for `t ≥ 0`.

Source: Trentelman–Stoorvogel–Hautus, Theorem 4.37 and Section 4.8 (external
stabilization); the pole/residue reading of the uncontrollable/observable
splitting. The full Bohl spectral-projection argument that would separate every
`x_b ∈ X_b(A) \ (V*(ker H) + Xstab)` — in particular the observability-chain
functionals `ψ ∘ H ∘ Aᵏ`, where the unbounded operator `Aᵏ` prevents the
chain readout from inheriting the decay of `H x_u(t)` — remains the exact
documented obligation; this task lands the rigorous finite-mode (pole/residue)
core, including the rotation/complex case. -/

namespace LinearMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Left eigenfunctionals commute with the exponential flow.** If `ρ` is a
continuous linear functional with `ρ (A y) = lam * ρ y`, then
`ρ (exp (t • A) y) = e^{lam t} ρ y`. This is the residue identity: the functional
reads off the single exponential character `e^{lam t}` from the flow. -/
theorem eigenfunctional_exp_apply [CompleteSpace X] (A : X →L[ℝ] X) (ρ : X →L[ℝ] ℝ)
    (lam : ℝ) (hA : ∀ y : X, ρ (A y) = lam * ρ y) (t : ℝ) (y : X) :
    ρ (NormedSpace.exp (t • A) y) = Real.exp (lam * t) * ρ y := by
  have hpow : ∀ n : ℕ, ∀ z : X, ρ ((A ^ n) z) = lam ^ n * ρ z := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ', mul_apply_eq_comp, hA, ih]
      ring
  have hterm : ∀ n : ℕ, ρ (((n.factorial : ℝ)⁻¹) • (((t • A) ^ n) y)) =
      ((n.factorial : ℝ)⁻¹) * (t ^ n * lam ^ n) * ρ y := by
    intro n
    simp only [map_smul, smul_pow, _root_.smul_apply, hpow n y, smul_eq_mul]
    ring
  have hsum : Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (((t • A) ^ n) y)) := by
    have hop : Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (t • A) ^ n) :=
      NormedSpace.expSeries_summable_of_mem_ball' (t • A)
        ((NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _)
    have := hop.mapL (ContinuousLinearMap.apply ℝ X y)
    simpa using this
  have htsum_aux : (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • (lam * t) ^ n) =
      NormedSpace.exp (lam * t) := by
    rw [← congrFun (NormedSpace.exp_eq_tsum ℝ) (lam * t)]
  have htsum : (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) * (t * lam) ^ n) = Real.exp (lam * t) := by
    rw [Real.exp_eq_exp_ℝ, ← htsum_aux]
    apply tsum_congr
    intro n
    rw [smul_eq_mul, mul_comm t lam]
  rw [exp_smul_apply_eq_tsum A t y, ContinuousLinearMap.map_tsum ρ hsum, tsum_congr hterm]
  rw [show (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) * (t ^ n * lam ^ n) * ρ y) =
      (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) * (t * lam) ^ n) * ρ y from by
    rw [← tsum_mul_right]
    apply tsum_congr
    intro n
    rw [mul_pow]]
  rw [htsum]

/-- **Complex left eigenfunctionals commute with the exponential flow.** The
complex-valued residue identity `ρ (exp (t • A) y) = e^{t lam} ρ y` for
`ρ : X →L[ℝ] ℂ` and `lam : ℂ`. This covers the non-real conjugate pole pairs of a
real rotation, where no real eigenfunctional exists. -/
theorem eigenfunctional_exp_apply_complex [CompleteSpace X] (A : X →L[ℝ] X) (ρ : X →L[ℝ] ℂ)
    (lam : ℂ) (hA : ∀ y : X, ρ (A y) = lam * ρ y) (t : ℝ) (y : X) :
    ρ (NormedSpace.exp (t • A) y) = Complex.exp (t * lam) * ρ y := by
  have hpow : ∀ n : ℕ, ∀ z : X, ρ ((A ^ n) z) = lam ^ n * ρ z := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ', mul_apply_eq_comp, hA, ih]
      ring
  have hterm : ∀ n : ℕ, ρ (((n.factorial : ℝ)⁻¹) • (((t • A) ^ n) y)) =
      (((n.factorial : ℝ)⁻¹ : ℂ) * (t * lam) ^ n) * ρ y := by
    intro n
    simp only [map_smul, smul_pow, _root_.smul_apply]
    rw [hpow n y]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ)]
    simp only [smul_eq_mul]
    push_cast
    rw [mul_pow]
    ac_rfl
  have hsum : Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (((t • A) ^ n) y)) := by
    have hop : Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (t • A) ^ n) :=
      NormedSpace.expSeries_summable_of_mem_ball' (t • A)
        ((NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _)
    have := hop.mapL (ContinuousLinearMap.apply ℝ X y)
    simpa using this
  have htsum_aux : (∑' n : ℕ, ((n.factorial : ℂ)⁻¹) • (t * lam) ^ n) =
      NormedSpace.exp (t * lam) := by
    rw [← congrFun (NormedSpace.exp_eq_tsum ℂ) (t * lam)]
  have htsum : (∑' n : ℕ, (((n.factorial : ℝ)⁻¹ : ℂ) * (t * lam) ^ n)) =
      Complex.exp (t * lam) := by
    rw [Complex.exp_eq_exp_ℂ, ← htsum_aux]
    apply tsum_congr
    intro n
    rw [smul_eq_mul]
    simp
  rw [exp_smul_apply_eq_tsum A t y, ContinuousLinearMap.map_tsum ρ hsum, tsum_congr hterm]
  rw [tsum_mul_right, htsum]

/-! ### Jordan-chain (generalized eigenmode) spectral projection

The single eigenfunctional residue lemmas above cover a *left eigenvector* of
`A`: a functional `ρ` with `ρ (A y) = λ ρ y`. A general antistable spectral
projection needs a **left Jordan chain** instead, a finite family
`ρ 0, …, ρ (m-1)` with

`ρ j ((A - λ) y) = ρ (j+1) y`,   `ρ m = 0`.

Writing `N = A - λ • 1`, the chain condition is `ρ j ∘ N = ρ (j+1)`, so the
orbit of `ρ 0` under the powers of `N` is exactly the chain:
`ρ 0 (N^k y) = ρ k y`. Splitting `t • A = (t λ) • 1 + t • N` (the two summands
commute) gives the **chain residue identity**

`ρ 0 (exp (t A) y) = e^{t λ} ∑_{j<m} (t^j / j!) ρ j y`,

a polynomial-exponential residue whose coefficients are the chain values. This
extends the single-eigenfunctional residue to genuine generalized eigenmodes and
is the finite-mode spectral projection behind the open-loop necessity for states
in `V*(ker H ⊔ reachableSubspace)`. -/

/-- **The exponential of a real multiple of the identity.** For a real scalar
`c`, `exp (c • 1) x = e^c • x`. This generalises the accepted negative-exponent
form `exp_smul_one_apply` to an arbitrary real exponent, which is exactly the
prefactor `e^{t λ}` appearing in the Jordan-chain residue identity. -/
theorem exp_smul_one_apply_real (c : ℝ) (x : X) :
    NormedSpace.exp (c • (1 : X →L[ℝ] X)) x = Real.exp c • x := by
  rw [← Algebra.algebraMap_eq_smul_one]
  rw [← NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := X →L[ℝ] X) c]
  rw [← Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one]
  rfl

/-- **Jordan-chain residue identity.** Let `ρ : ℕ → X →L[ℝ] ℝ` be a real left
Jordan chain at the mode `λ`, i.e. `ρ j ((A - λ • 1) y) = ρ (j+1) y`, with
`ρ m = 0` (so no functional beyond the `m`-th is used). Then for every starting
index `i`

`ρ i (exp (t A) y) = e^{t λ} ∑_{j<m} (t^j / j!) ρ (i+j) y`.

The proof sets `N = A - λ • 1`, shows `ρ i (N^k y) = ρ (i+k) y` by induction,
splits `t • A = (t λ) • 1 + t • N` with the commuting-exponential law, expands
`exp (t • N)` by its factorial series, and truncates the resulting `tsum` at the
first vanishing chain index. -/
theorem chain_eigenfunctional_exp_apply [CompleteSpace X]
    (A : X →L[ℝ] X) (ρ : ℕ → X →L[ℝ] ℝ) (lam : ℝ) (m : ℕ)
    (hchain : ∀ j y, ρ j ((A - lam • (1 : X →L[ℝ] X)) y) = ρ (j + 1) y)
    (hzero : ρ m = 0) (i : ℕ) (t : ℝ) (y : X) :
    ρ i (NormedSpace.exp (t • A) y) =
      Real.exp (lam * t) * ∑ j ∈ Finset.range m, (t ^ j / (j.factorial : ℝ)) * ρ (i + j) y := by
  set N : X →L[ℝ] X := A - lam • (1 : X →L[ℝ] X) with hN
  have hchain' : ∀ j y, ρ j (N y) = ρ (j + 1) y := by
    intro j y; rw [hN]; exact hchain j y
  have hpow : ∀ i k : ℕ, ∀ y : X, ρ i ((N ^ k) y) = ρ (i + k) y := by
    intro i k
    induction k generalizing i with
    | zero => intro y; simp
    | succ k ih =>
      intro y
      rw [pow_succ', mul_apply_eq_comp, hchain', ih]
      rw [show i + 1 + k = i + (k + 1) by omega]
  have hkm : ∀ d, ρ (m + d) = 0 := by
    intro d
    induction d with
    | zero => simpa using hzero
    | succ d ih =>
      ext y
      change ρ (m + (d + 1)) y = 0
      have hst : ρ (m + (d + 1)) y = ρ (m + d) (N y) := by
        rw [show m + (d + 1) = m + d + 1 by omega, ← hchain' (m + d) y]
      rw [hst, ih]
      rfl
  have hk0 : ∀ k, m ≤ k → ρ k = 0 := by
    intro k hk
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact hkm d
  have hsplit : t • A = (t * lam) • (1 : X →L[ℝ] X) + t • N := by
    rw [hN]; module
  have hcomm : Commute ((t * lam) • (1 : X →L[ℝ] X)) (t • N) :=
    Algebra.commute_algebraMap_left (t * lam) (t • N)
  have hexp : NormedSpace.exp (t • A) =
      NormedSpace.exp ((t * lam) • (1 : X →L[ℝ] X)) * NormedSpace.exp (t • N) := by
    rw [hsplit]
    exact NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hcomm
      ((NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _)
      ((NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _)
  have hstep : ∀ k : ℕ, ρ i (((k.factorial : ℝ)⁻¹) • (((t • N) ^ k) y)) =
      (k.factorial : ℝ)⁻¹ * (t ^ k * ρ (i + k) y) := by
    intro k
    rw [map_smul, smul_pow, _root_.smul_apply, map_smul, hpow i k y]
    simp only [smul_eq_mul]
  have hsum : Summable (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • (((t • N) ^ k) y)) := by
    have hop : Summable (fun k : ℕ => ((k.factorial : ℝ)⁻¹) • (t • N) ^ k) :=
      NormedSpace.expSeries_summable_of_mem_ball' (t • N)
        ((NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _)
    have := hop.mapL (ContinuousLinearMap.apply ℝ X y)
    simpa using this
  rw [hexp, mul_apply_eq_comp, exp_smul_one_apply_real, map_smul]
  rw [exp_smul_apply_eq_tsum N t y, ContinuousLinearMap.map_tsum (ρ i) hsum]
  rw [smul_eq_mul, ← tsum_mul_left]
  rw [tsum_congr (fun k => by rw [hstep])]
  rw [tsum_eq_sum (s := Finset.range m)]
  · rw [Finset.mul_sum, mul_comm lam t]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  · intro k hk
    rw [Finset.mem_range, not_lt] at hk
    rw [hk0 (i + k) (by omega)]
    simp

end LinearMap

namespace LinearSystem

variable {X U Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- **The forcing is annihilated by a left eigenfunctional of an uncontrollable
mode.** If `ρ (A y) = lam * ρ y` and `ρ (B v) = 0`, then the variation-of-
constants forcing integrand `forcing t₀ u s = exp (-(s - t₀) • A) (B u(s))` is
in the kernel of `ρ`: the input channel produces no residue at `lam`. -/
theorem forcing_eigenfunctional_eq_zero (sys : LinearSystem ℝ X U Z) (ρ : X →L[ℝ] ℝ)
    (lam : ℝ) (hA : ∀ y, ρ (sys.A y) = lam * ρ y) (hB : ∀ v, ρ (sys.B v) = 0)
    (t₀ : ℝ) (u : ℝ → U) (s : ℝ) :
    ρ (sys.forcing t₀ u s) = 0 := by
  have hAc : ∀ y, ρ (sys.continuousA y) = lam * ρ y := fun y => by simpa using hA y
  have h := LinearMap.eigenfunctional_exp_apply sys.continuousA ρ lam hAc (-(s - t₀))
    (sys.continuousB (u s))
  rw [LinearSystem.forcing, LinearSystem.expFlow, h,
    show ρ (sys.continuousB (u s)) = 0 from by simpa using hB (u s), mul_zero]

/-- **Transfer-function residue at an uncontrollable eigenmode.** For every
locally integrable input the forced readout is the autonomous residue
`ρ (x_u(t)) = e^{lam t} ρ x`: the forcing contributes nothing because `ρ`
annihilates `im B`, and the two exponentials commute with `ρ` by
`eigenfunctional_exp_apply`. -/
theorem variationOfConstants_eigenfunctional (sys : LinearSystem ℝ X U Z) (ρ : X →L[ℝ] ℝ)
    (lam : ℝ) (hA : ∀ y, ρ (sys.A y) = lam * ρ y) (hB : ∀ v, ρ (sys.B v) = 0)
    (x : X) {u : ℝ → U} (hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume)
    (t : ℝ) :
    ρ (sys.variationOfConstants 0 x u t) = Real.exp (lam * t) * ρ x := by
  have hAc : ∀ y, ρ (sys.continuousA y) = lam * ρ y := fun y => by simpa using hA y
  have hforcing : ∀ s, ρ (sys.forcing 0 u s) = 0 :=
    fun s => forcing_eigenfunctional_eq_zero sys ρ lam hA hB 0 u s
  have hInt : ρ (∫ s in (0:ℝ)..t, sys.forcing 0 u s) = 0 := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm ρ
      (LinearSystem.intervalIntegrable_forcing sys 0 hu 0 t)]
    simp only [hforcing, intervalIntegral.integral_zero]
  have houter := LinearMap.eigenfunctional_exp_apply sys.continuousA ρ lam hAc (t - 0)
    (x + ∫ s in (0:ℝ)..t, sys.forcing 0 u s)
  have harg : ρ (x + ∫ s in (0:ℝ)..t, sys.forcing 0 u s) = ρ x := by
    rw [map_add, hInt, add_zero]
  rw [LinearSystem.variationOfConstants, LinearSystem.expFlow, houter, harg]
  simp

/-- **Non-cancellation of an uncontrollable antistable eigenmode.** If the
continuous readout functional `ρ` is a left eigenfunctional of `A` with
`0 ≤ lam`, annihilates the input channel (`ρ ∘ B = 0`), factors through the
readout (`ρ = ψ ∘ H`), and detects the state `x` (`ρ x ≠ 0`), then no locally
integrable open-loop input makes the controlled output `H x_u(t)` decay: the
residue `ρ x` at the pole `lam` survives the input. -/
theorem not_isOutputStabilizable_of_eigenfunctional_readout
    (sys : LinearSystem ℝ X U Z) (ρ : X →L[ℝ] ℝ) (ψ : Z →L[ℝ] ℝ) (lam : ℝ)
    (hlam : 0 ≤ lam) (hA : ∀ y, ρ (sys.A y) = lam * ρ y) (hB : ∀ v, ρ (sys.B v) = 0)
    (hρ : ∀ y, ρ y = ψ (sys.C y)) {x : X} (hx : ρ x ≠ 0) :
    ¬ IsOutputStabilizable sys sys.C x := by
  rintro ⟨u, hu, htend⟩
  have hψ : Filter.Tendsto (fun t : ℝ => ψ (sys.C (sys.variationOfConstants 0 x u t)))
      Filter.atTop (nhds 0) := by
    have h1 := (ψ.continuous.tendsto 0).comp htend
    simpa [Function.comp_def] using h1
  have hlim : Filter.Tendsto (fun t : ℝ => Real.exp (lam * t) * ρ x) Filter.atTop (nhds 0) := by
    refine hψ.congr' (Filter.Eventually.of_forall fun t => ?_)
    rw [← hρ (sys.variationOfConstants 0 x u t),
      variationOfConstants_eigenfunctional sys ρ lam hA hB x hu t]
  have hnormlim : Filter.Tendsto (fun t : ℝ => ‖Real.exp (lam * t) * ρ x‖)
      Filter.atTop (nhds 0) := by
    simpa using hlim.norm
  have hb : ‖ρ x‖ ≤ 0 := by
    refine ge_of_tendsto hnormlim ?_
    filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with t ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos (lam * t))]
    exact le_mul_of_one_le_left (abs_nonneg (ρ x)) (Real.one_le_exp (mul_nonneg hlam ht))
  exact hx (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))

/-- **Complex forcing annihilation.** The complex-valued analogue of
`forcing_eigenfunctional_eq_zero`: a complex left eigenfunctional of an
uncontrollable mode annihilates the forcing integrand. -/
theorem forcing_eigenfunctional_eq_zero_complex (sys : LinearSystem ℝ X U Z) (ρ : X →L[ℝ] ℂ)
    (lam : ℂ) (hA : ∀ y, ρ (sys.A y) = lam * ρ y) (hB : ∀ v, ρ (sys.B v) = 0)
    (t₀ : ℝ) (u : ℝ → U) (s : ℝ) :
    ρ (sys.forcing t₀ u s) = 0 := by
  have hAc : ∀ y, ρ (sys.continuousA y) = lam * ρ y := fun y => by simpa using hA y
  have h := LinearMap.eigenfunctional_exp_apply_complex sys.continuousA ρ lam hAc (-(s - t₀))
    (sys.continuousB (u s))
  rw [LinearSystem.forcing, LinearSystem.expFlow, h,
    show ρ (sys.continuousB (u s)) = 0 from by simpa using hB (u s), mul_zero]

/-- **Complex transfer-function residue at an uncontrollable eigenmode.** For
every locally integrable input `ρ (x_u(t)) = e^{t lam} ρ x`, the complex
residue identity covering non-real poles. -/
theorem variationOfConstants_eigenfunctional_complex (sys : LinearSystem ℝ X U Z) (ρ : X →L[ℝ] ℂ)
    (lam : ℂ) (hA : ∀ y, ρ (sys.A y) = lam * ρ y) (hB : ∀ v, ρ (sys.B v) = 0)
    (x : X) {u : ℝ → U} (hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume)
    (t : ℝ) :
    ρ (sys.variationOfConstants 0 x u t) = Complex.exp (t * lam) * ρ x := by
  have hAc : ∀ y, ρ (sys.continuousA y) = lam * ρ y := fun y => by simpa using hA y
  have hforcing : ∀ s, ρ (sys.forcing 0 u s) = 0 :=
    fun s => forcing_eigenfunctional_eq_zero_complex sys ρ lam hA hB 0 u s
  have hInt : ρ (∫ s in (0:ℝ)..t, sys.forcing 0 u s) = 0 := by
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm ρ
      (LinearSystem.intervalIntegrable_forcing sys 0 hu 0 t)]
    simp only [hforcing, intervalIntegral.integral_zero]
  have houter := LinearMap.eigenfunctional_exp_apply_complex sys.continuousA ρ lam hAc (t - 0)
    (x + ∫ s in (0:ℝ)..t, sys.forcing 0 u s)
  have harg : ρ (x + ∫ s in (0:ℝ)..t, sys.forcing 0 u s) = ρ x := by
    rw [map_add, hInt, add_zero]
  rw [LinearSystem.variationOfConstants, LinearSystem.expFlow, houter, harg]
  simp

/-- **Complex non-cancellation of an uncontrollable antistable eigenmode.** If
the complex readout functional `ρ` is a left eigenfunctional of `A` with
`0 ≤ lam.re`, annihilates the input channel, factors through the readout
(`ρ = ψ ∘ H`), and detects `x`, then `x` is not open-loop output-stabilizable.
The real part condition is exactly `|e^{t lam}| = e^{t lam.re} ≥ 1` for `t ≥ 0`,
so a non-real conjugate pole pair (a rotation) is covered as well. -/
theorem not_isOutputStabilizable_of_eigenfunctional_readout_complex
    (sys : LinearSystem ℝ X U Z) (ρ : X →L[ℝ] ℂ) (ψ : Z →L[ℝ] ℂ) (lam : ℂ)
    (hlam : 0 ≤ lam.re) (hA : ∀ y, ρ (sys.A y) = lam * ρ y) (hB : ∀ v, ρ (sys.B v) = 0)
    (hρ : ∀ y, ρ y = ψ (sys.C y)) {x : X} (hx : ρ x ≠ 0) :
    ¬ IsOutputStabilizable sys sys.C x := by
  rintro ⟨u, hu, htend⟩
  have hψ : Filter.Tendsto (fun t : ℝ => ψ (sys.C (sys.variationOfConstants 0 x u t)))
      Filter.atTop (nhds 0) := by
    have h1 := (ψ.continuous.tendsto 0).comp htend
    simpa [Function.comp_def] using h1
  have hlim : Filter.Tendsto (fun t : ℝ => Complex.exp (t * lam) * ρ x)
      Filter.atTop (nhds 0) := by
    refine hψ.congr' (Filter.Eventually.of_forall fun t => ?_)
    rw [← hρ (sys.variationOfConstants 0 x u t),
      variationOfConstants_eigenfunctional_complex sys ρ lam hA hB x hu t]
  have hnormlim : Filter.Tendsto (fun t : ℝ => ‖Complex.exp (t * lam) * ρ x‖)
      Filter.atTop (nhds 0) := by
    simpa using hlim.norm
  have hb : ‖ρ x‖ ≤ 0 := by
    refine ge_of_tendsto hnormlim ?_
    filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with t ht
    rw [norm_mul, Complex.norm_exp]
    have hre : (t * lam).re = lam.re * t := by simp [Complex.mul_re, mul_comm]
    rw [hre]
    exact le_mul_of_one_le_left (norm_nonneg (ρ x)) (Real.one_le_exp (mul_nonneg hlam ht))
  exact hx (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))

/-! ### Jordan-chain non-cancellation of an uncontrollable antistable mode

The single-eigenfunctional non-cancellation theorems above handle a genuine left
eigenvector `ρ` of `A` with `ρ ∘ B = 0`. A state in
`V*(ker H ⊔ reachableSubspace)` but outside `V*(ker H) + reachableSubspace` need
not be detected by a single eigenfunctional: the relevant readout is a finite
**observability/Jordan chain**, whose residue is the polynomial-exponential
`e^{t λ} ∑_j (t^j / j!) ρ j x` produced by
`LinearMap.chain_eigenfunctional_exp_apply`.

If every functional of the chain annihilates the input channel,
`ρ j (B v) = 0`, then the forcing is invisible to the whole chain and the forced
trajectory readout equals the autonomous polynomial-exponential residue. When
`0 ≤ λ` this residue cannot tend to zero unless every chain functional vanishes
at `x`, so a state detected by some member of the chain is not open-loop output
stabilizable. The final step reuses the accepted multi-mode vanishing theorem
`LinearMap.tendsto_zero_of_sum_exp_polynomial`, so a sum of polynomial-exponential
antistable residues that decays must have all coefficients zero.

This is the finite-mode spectral projection whose explicit generalized-eigenspace
and readout-chain hypotheses are the content of the remaining open-loop necessity;
it does not assert the full Bohl/spectral input-cancellation theorem. -/

/-- **The forcing is annihilated by every functional of an uncontrollable
Jordan chain.** If `ρ` is a left Jordan chain of `A` at `λ` with `ρ m = 0` and
`ρ j (B v) = 0` for all `j`, then each chain functional kills the
variation-of-constants forcing integrand `exp (-(s - t₀) • A) (B u(s))`. -/
theorem forcing_chain_eq_zero (sys : LinearSystem ℝ X U Z) (ρ : ℕ → X →L[ℝ] ℝ)
    (lam : ℝ) (m : ℕ)
    (hchain : ∀ j y, ρ j (sys.A y) = lam * ρ j y + ρ (j + 1) y)
    (hzero : ρ m = 0) (hB : ∀ j v, ρ j (sys.B v) = 0)
    (t₀ : ℝ) (u : ℝ → U) (s : ℝ) (j : ℕ) :
    ρ j (sys.forcing t₀ u s) = 0 := by
  have hAc : ∀ k y, ρ k (sys.continuousA y) = lam * ρ k y + ρ (k + 1) y :=
    fun k y => by simpa using hchain k y
  have hN : ∀ k y, ρ k ((sys.continuousA - lam • (1 : X →L[ℝ] X)) y) = ρ (k + 1) y := by
    intro k y
    rw [_root_.sub_apply, map_sub, _root_.smul_apply, map_smul,
      smul_eq_mul, one_apply_eq_self, hAc k y]
    ring
  have h := LinearMap.chain_eigenfunctional_exp_apply sys.continuousA ρ lam m hN hzero j
    (-(s - t₀)) (sys.continuousB (u s))
  rw [LinearSystem.forcing, LinearSystem.expFlow, h]
  rw [Finset.sum_eq_zero]
  · simp
  · intro k hk
    rw [show ρ (j + k) (sys.continuousB (u s)) = 0 from by simpa using hB (j + k) (u s)]
    ring

/-- **Jordan-chain transfer-function residue.** For every locally integrable
input the forced trajectory readout of the first chain functional is the
autonomous polynomial-exponential residue
`ρ 0 (x_u(t)) = e^{t λ} ∑_j (t^j / j!) ρ j x`: because every chain functional
annihilates `im B`, the forcing contributes nothing to any member of the chain,
so the variation-of-constants integral stays in the common kernel. -/
theorem variationOfConstants_chain (sys : LinearSystem ℝ X U Z) (ρ : ℕ → X →L[ℝ] ℝ)
    (lam : ℝ) (m : ℕ)
    (hchain : ∀ j y, ρ j (sys.A y) = lam * ρ j y + ρ (j + 1) y)
    (hzero : ρ m = 0) (hB : ∀ j v, ρ j (sys.B v) = 0)
    (x : X) {u : ℝ → U} (hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume)
    (t : ℝ) :
    ρ 0 (sys.variationOfConstants 0 x u t) =
      Real.exp (lam * t) * ∑ j ∈ Finset.range m, (t ^ j / (j.factorial : ℝ)) * ρ j x := by
  have hAc : ∀ k y, ρ k (sys.continuousA y) = lam * ρ k y + ρ (k + 1) y :=
    fun k y => by simpa using hchain k y
  have hN : ∀ k y, ρ k ((sys.continuousA - lam • (1 : X →L[ℝ] X)) y) = ρ (k + 1) y := by
    intro k y
    rw [_root_.sub_apply, map_sub, _root_.smul_apply, map_smul,
      smul_eq_mul, one_apply_eq_self, hAc k y]
    ring
  have hforcing : ∀ j s, ρ j (sys.forcing 0 u s) = 0 :=
    fun j s => forcing_chain_eq_zero sys ρ lam m hchain hzero hB 0 u s j
  have hInt : ∀ j : ℕ, ρ j (∫ s in (0:ℝ)..t, sys.forcing 0 u s) = 0 := by
    intro j
    rw [← ContinuousLinearMap.intervalIntegral_comp_comm (ρ j)
      (LinearSystem.intervalIntegrable_forcing sys 0 hu 0 t)]
    simp only [hforcing j, intervalIntegral.integral_zero]
  have harg : ∀ j : ℕ, ρ j (x + ∫ s in (0:ℝ)..t, sys.forcing 0 u s) = ρ j x := by
    intro j; rw [map_add, hInt j, add_zero]
  have houter := LinearMap.chain_eigenfunctional_exp_apply sys.continuousA ρ lam m hN hzero 0
    (t - 0) (x + ∫ s in (0:ℝ)..t, sys.forcing 0 u s)
  rw [LinearSystem.variationOfConstants, LinearSystem.expFlow, houter]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro j hj
    rw [zero_add, harg j]
    simp

/-- **Non-cancellation of an uncontrollable antistable Jordan chain.** If the
readout `ψ ∘ H` factors the first functional `ρ 0` of a real left Jordan chain
at a mode `lam ≥ 0`, every functional of the chain annihilates `im B`, and some
functional of the chain detects `x`, then no locally integrable open-loop input
makes the controlled output decay. The polynomial-exponential residue
`e^{lam t} ∑_j (t^j / j!) ρ j x` survives the forcing, and the accepted
multi-mode vanishing theorem forces all its coefficients to vanish. -/
theorem not_isOutputStabilizable_of_chain_readout
    (sys : LinearSystem ℝ X U Z) (ρ : ℕ → X →L[ℝ] ℝ) (ψ : Z →L[ℝ] ℝ)
    (lam : ℝ) (m : ℕ) (hlam : 0 ≤ lam)
    (hchain : ∀ j y, ρ j (sys.A y) = lam * ρ j y + ρ (j + 1) y)
    (hzero : ρ m = 0) (hB : ∀ j v, ρ j (sys.B v) = 0)
    (hρ : ∀ y, ρ 0 y = ψ (sys.C y))
    {x : X} (hx : ∃ j, j < m ∧ ρ j x ≠ 0) :
    ¬ IsOutputStabilizable sys sys.C x := by
  rintro ⟨u, hu, htend⟩
  have hψ : Filter.Tendsto
      (fun t : ℝ => ψ (sys.C (sys.variationOfConstants 0 x u t)))
      Filter.atTop (nhds 0) := by
    have h1 := (ψ.continuous.tendsto 0).comp htend
    simpa [Function.comp_def] using h1
  have hid : ∀ t : ℝ, ψ (sys.C (sys.variationOfConstants 0 x u t)) =
      Real.exp (lam * t) * ∑ j ∈ Finset.range m,
        (t ^ j / (j.factorial : ℝ)) * ρ j x := by
    intro t
    rw [← hρ (sys.variationOfConstants 0 x u t),
      variationOfConstants_chain sys ρ lam m hchain hzero hB x hu t]
  have hp : Filter.Tendsto
      (fun t : ℝ => Real.exp (lam * t) *
        ∑ j ∈ Finset.range m, (t ^ j / (j.factorial : ℝ)) * ρ j x)
      Filter.atTop (nhds 0) :=
    hψ.congr' (Filter.Eventually.of_forall fun t => hid t)
  obtain ⟨j0, hj0, hρj0⟩ := hx
  have hmpos : 0 < m := lt_of_le_of_lt (Nat.zero_le j0) hj0
  set D : ℕ := m - 1 with hDdef
  have hD1 : D + 1 = m := Nat.succ_pred_eq_of_pos hmpos
  let a : Unit → ℕ → ℂ := fun _ k => ((k.factorial : ℝ)⁻¹ * ρ k x : ℂ)
  have hcomplex : Filter.Tendsto
      (fun t : ℝ => ∑ _i ∈ ({()} : Finset Unit),
        Complex.exp (t * (lam : ℂ)) •
          (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a () k))
      Filter.atTop (nhds 0) := by
    have hcoe : Filter.Tendsto
        (fun t : ℝ => ((Real.exp (lam * t) *
          ∑ j ∈ Finset.range m, (t ^ j / (j.factorial : ℝ)) * ρ j x : ℝ) : ℂ))
        Filter.atTop (nhds 0) :=
      (Complex.continuous_ofReal.tendsto 0).comp hp
    refine hcoe.congr' (Filter.Eventually.of_forall fun t => ?_)
    beta_reduce
    rw [hD1, Finset.sum_singleton]
    simp only [a]
    rw [Complex.ofReal_mul, Complex.ofReal_sum]
    congr 1
    · rw [Complex.ofReal_exp]
      congr 1
      push_cast; ring
    · apply Finset.sum_congr rfl
      intro k hk
      push_cast
      ring
  have hres := LinearMap.tendsto_zero_of_sum_exp_polynomial
    ({()} : Finset Unit) (fun _ : Unit => (lam : ℂ))
    (fun i _ => by simpa using hlam)
    (fun i _ j _ hij => by simp) D a hcomplex
  have hz := hres () (Finset.mem_singleton_self ()) j0 (by omega)
  have hz' : (j0.factorial : ℝ)⁻¹ * ρ j0 x = 0 := by
    have : ((j0.factorial : ℝ)⁻¹ * ρ j0 x : ℂ) = 0 := hz
    exact_mod_cast this
  exact hρj0 ((mul_eq_zero.mp hz').resolve_left
    (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j0))))

/-! ## Restricted-input open-loop necessity: eventually-zero inputs

The full open-loop necessity of Trentelman–Stoorvogel–Hautus Theorem 4.37 is

`IsOutputStabilizable sys H x → x ∈ W_g(ker H) = V*(ker H) + Xstab(A, B)`

for an *arbitrary* locally integrable input. Its source proof splits the Bohl
input and the forced trajectory into stable and antistable spectral parts and
then reads the two resulting state equations. For a merely locally integrable
input this splitting is unavailable. Writing the forced trajectory as
`x_u(t) = e^{tA} x + r_t` with `r_t ∈ R = ⟨A | im B⟩`, the missing analytic step
is that the reachable readout `H r_t` — the convolution of the Markov kernel
`H e^{tA} B` with `u` — cannot cancel the autonomous antistable readout
`H (e^{tA} x_b)`. This is a Titchmarsh/Laplace convolution-cancellation statement
(equivalently: the transfer function `H (sI - A)⁻¹ B` has no pole at an
uncontrollable mode), and the pinned library contains no Laplace-transform or
Bohl-function decomposition support for it.

This section lands the weakest *honest* admissibility condition under which the
autonomous-limit argument closes with the accepted spectral tools: inputs that
vanish for all sufficiently large times. For such an input the reachable part of
the trajectory is constant past a finite horizon and the forced trajectory
becomes the autonomous orbit of a single state, so the accepted antistable
readout theorem applies with no extra spectral input. The resulting theorem is a
genuine strict subclass of the general statement and therefore does **not**
imply the original Corollary 6.22 necessity; the exact remaining obligation is
the unrestricted locally-integrable statement recorded above. -/

section EventuallyZeroInput

open Filter MeasureTheory

/-- **Eventually-zero inputs.** An input `u` vanishes for all sufficiently large
times. This is the restricted admissibility class of
`mem_outputStabilizableSubspace_of_isOutputStabilizable_of_eventuallyZero`: it is
strictly contained in the locally integrable inputs (so the restricted theorem
does not imply the full open-loop necessity) but contains every compactly
supported input and every input switched off after a finite horizon. -/
def HasEventuallyZeroInput (u : ℝ → U) : Prop := ∃ T, ∀ t ≥ T, u t = 0

/-- **The forcing vanishes when the input does.** With `u s = 0` the variation-of-
constants forcing integrand `exp (-(s - t₀) • A) (B (u s))` is zero. -/
theorem forcing_eq_zero_of_input_eq_zero (sys : LinearSystem ℝ X U Z) (t₀ : ℝ)
    {u : ℝ → U} {s : ℝ} (hs : u s = 0) : sys.forcing t₀ u s = 0 := by
  simp [LinearSystem.forcing, hs]

omit [FiniteDimensional ℝ U] in
/-- **The exponential flow preserves an invariant submodule.** If `W` is
`A`-invariant (`Submodule.map A W ≤ W`), then `e^{tA} y ∈ W` for every `y ∈ W`
and every real `t`. This is the finite-dimensional closedness argument for the
exponential series: every partial sum `∑_{n<N} (n!)⁻¹ (tA)^n y` lies in `W`
because `A^n y ∈ W`, and `W` is closed. It is the reusable invariance ingredient
for carrying the algebraic `W_g(ker H)` along the flow. -/
theorem expFlow_mem_of_mem_of_map_le (sys : LinearSystem ℝ X U Z) (W : Submodule ℝ X)
    (hW : Submodule.map sys.A W ≤ W) (t : ℝ) {y : X} (hy : y ∈ W) :
    sys.expFlow t y ∈ W := by
  have hclosed : IsClosed (W : Set X) := W.closed_of_finiteDimensional
  have hpow : ∀ n : ℕ, (sys.A ^ n) y ∈ W := by
    intro n
    induction n with
    | zero => simpa using hy
    | succ n ih =>
      have hA : sys.A ((sys.A ^ n) y) ∈ W := hW ⟨(sys.A ^ n) y, ih, rfl⟩
      rwa [show (sys.A ^ (n + 1)) y = sys.A ((sys.A ^ n) y) by
        rw [pow_succ', Module.End.mul_apply]]
  have hterm : ∀ n : ℕ, ((n.factorial : ℝ)⁻¹ • (t • sys.continuousA) ^ n) y ∈ W := by
    intro n
    rw [smul_apply, smul_pow_continuousA_apply]
    exact W.smul_mem _ (W.smul_mem _ (hpow n))
  have hsum := (LinearSystem.expFlow_hasSum sys t).mapL (ContinuousLinearMap.apply ℝ X y)
  have htend := hsum.tendsto_sum_nat
  exact hclosed.mem_of_tendsto htend (Eventually.of_forall fun N =>
    W.sum_mem fun n _ => hterm n)

/-- **Finite-horizon forcing integral.** If `u` vanishes on `[T, ∞)` and `T ≤ t`,
then the forcing integral over `[0, t]` equals the one over `[0, T]`: the extra
piece over `[T, t]` integrates a function that is pointwise zero there. -/
theorem intervalIntegral_forcing_eq_of_eventuallyZero (sys : LinearSystem ℝ X U Z)
    {u : ℝ → U} (hu : LocallyIntegrable u volume) {T t : ℝ} (ht : T ≤ t)
    (hevent : ∀ s ≥ T, u s = 0) :
    ∫ s in (0 : ℝ)..t, sys.forcing 0 u s = ∫ s in (0 : ℝ)..T, sys.forcing 0 u s := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_forcing sys 0 hu 0 T) (intervalIntegrable_forcing sys 0 hu T t)]
  have hz : ∫ s in T..t, sys.forcing 0 u s = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards with s hs
    rw [Set.uIoc_of_le ht] at hs
    exact forcing_eq_zero_of_input_eq_zero sys 0 (hevent s (le_of_lt hs.1))
  rw [hz, add_zero]

/-- **Restricted open-loop output-stabilizability.** The open-loop predicate of
Trentelman–Stoorvogel–Hautus (4.28) with the input restricted to the
eventually-zero class `HasEventuallyZeroInput`. This is the clearly named
restricted-input variant: it is the source's finite-horizon control. -/
def IsOutputStabilizableWithEventuallyZeroInput (sys : LinearSystem ℝ X U Z)
    (H : X →ₗ[ℝ] Z) (x : X) : Prop :=
  ∃ u : ℝ → U, MeasureTheory.LocallyIntegrable u MeasureTheory.volume ∧
    HasEventuallyZeroInput u ∧
    Filter.Tendsto (fun t : ℝ => H (sys.variationOfConstants 0 x u t))
      Filter.atTop (nhds 0)

/-- **Restricted open-loop necessity.** If a locally integrable input that
vanishes eventually drives the readout `t ↦ H (x_u(t, x))` to zero, then
`x ∈ W_g(ker H) = V*(ker H) + Xstab(A, B)`.

Proof: let `T` be a time after which `u` vanishes and put `y = x_u(T)`. Since the
forcing integral is constant past `T`, the trajectory is the autonomous orbit
`x_u(t) = e^{(t-T)A} y` for `t ≥ T`, so `H (e^{sA} y) → 0`. Decompose
`y = y_g + y_b` along the accepted direct-sum identity `X = X_g(A) + X_b(A)`. The
stable component has decaying readout and the antistable component then inherits
it, so the accepted antistable readout theorem
`LinearMap.antistable_readout_forces_unobservable` makes `y_b` unobservable, hence
a member of `V*(ker H)`; the stable component lies in `Xstab(A, B)`. Thus
`y ∈ W_g(ker H)`. Finally, `y - e^{TA} x ∈ R = ⟨A | im B⟩ ⊆ W_g(ker H)`, so
`e^{TA} x ∈ W_g(ker H)`, and `expFlow_mem_of_mem_of_map_le` for the invariant
subspace `W_g(ker H)` at time `-T` recovers `x = e^{-TA} (e^{TA} x) ∈ W_g(ker H)`.

This is a strict subclass of the general locally integrable statement: it says
that no finite-horizon open-loop control can stabilize a state outside
`W_g(ker H)`, and it does not cover inputs with a persistent tail. The
unrestricted Corollary 6.22 necessity remains open. -/
theorem mem_outputStabilizableSubspace_of_isOutputStabilizable_of_eventuallyZero
    (sys : LinearSystem ℝ X U Z) (H : X →ₗ[ℝ] Z) {x : X} {u : ℝ → U}
    (hu : LocallyIntegrable u volume) (hevent : HasEventuallyZeroInput u)
    (htend : Tendsto (fun t : ℝ => H (sys.variationOfConstants 0 x u t)) atTop (nhds 0)) :
    x ∈ outputStabilizableSubspace sys.A sys.B H := by
  classical
  obtain ⟨T, hT⟩ := hevent
  set y : X := sys.variationOfConstants 0 x u T with hy
  have hstab : ∀ t : ℝ, T ≤ t →
      sys.variationOfConstants 0 x u t = sys.expFlow (t - T) y := by
    intro t ht
    rw [hy, variationOfConstants_eq, variationOfConstants_eq,
      intervalIntegral_forcing_eq_of_eventuallyZero sys hu ht hT]
    rw [show sys.expFlow t = sys.expFlow (t - T) * sys.expFlow T by
      rw [← expFlow_add, show t - T + T = t by ring]]
    rfl
  have hshift : Tendsto (fun t : ℝ => H (sys.expFlow (t - T) y)) atTop (nhds 0) := by
    refine htend.congr' ?_
    filter_upwards [eventually_ge_atTop T] with t ht
    rw [hstab t ht]
  have hauto : Tendsto (fun s : ℝ => H (sys.expFlow s y)) atTop (nhds 0) := by
    have h2 : Tendsto (fun s : ℝ => H (sys.expFlow ((s + T) - T) y)) atTop (nhds 0) :=
      hshift.comp (tendsto_atTop_add_const_right _ T tendsto_id)
    simpa using h2
  have hy_mem : y ∈ LinearMap.hurwitzSubspace sys.A ⊔ LinearMap.unstableSubspace sys.A := by
    rw [LinearMap.hurwitzSubspace_sup_unstableSubspace_eq_top]; trivial
  obtain ⟨yg, hyg, yb, hyb, hyeq⟩ := Submodule.mem_sup.mp hy_mem
  have hgdec : Tendsto (fun s : ℝ => H (sys.expFlow s yg)) atTop (nhds 0) := by
    have hh := tendsto_readout_exp_of_mem_hurwitzSubspace sys.A H hyg
    simpa [LinearSystem.expFlow, LinearSystem.continuousA] using hh
  have hbdec : Tendsto (fun s : ℝ => H (sys.expFlow s yb)) atTop (nhds 0) := by
    have hsplit : (fun s : ℝ => H (sys.expFlow s y)) =
        fun s => H (sys.expFlow s yg) + H (sys.expFlow s yb) := by
      funext s
      rw [← hyeq, map_add, map_add]
    have h' := hauto
    rw [hsplit] at h'
    simpa using h'.sub hgdec
  have hyb_unobs : yb ∈ LinearMap.unobservableSubspace H sys.A :=
    LinearMap.antistable_readout_forces_unobservable sys.A H hyb hbdec
  have hylabel : y ∈ outputStabilizableSubspace sys.A sys.B H := by
    have hb_ctrl : yb ∈ LinearMap.controlledInvariantSubspace sys.A sys.B (LinearMap.ker H) := by
      apply LinearMap.le_controlledInvariantSubspace
        (LinearMap.unobservableSubspace_le_ker H sys.A)
      · rw [LinearMap.IsControlledInvariant]
        exact le_trans (LinearMap.map_unobservableSubspace_le H sys.A) le_sup_left
      · exact hyb_unobs
    have hg_stab : yg ∈ LinearMap.stabilizableSubspace sys.A sys.B :=
      LinearMap.hurwitzSubspace_le_stabilizableSubspace sys.A sys.B hyg
    rw [outputStabilizableSubspace, ← hyeq, add_comm yg yb]
    exact Submodule.add_mem_sup hb_ctrl hg_stab
  have hexpT : sys.expFlow T x ∈ outputStabilizableSubspace sys.A sys.B H := by
    have hdiff := variationOfConstants_sub_expFlow_mem_reachableSubspace sys x hu T
    have hmemW : sys.variationOfConstants 0 x u T - sys.expFlow T x ∈
        outputStabilizableSubspace sys.A sys.B H :=
      stabilizableSubspace_le_outputStabilizableSubspace sys.A sys.B H
        (LinearMap.reachableSubspace_le_stabilizableSubspace sys.A sys.B hdiff)
    have hsub := sub_mem hylabel hmemW
    rwa [sub_sub_cancel] at hsub
  have hx : x = sys.expFlow (-T) (sys.expFlow T x) := by
    rw [← mul_apply_eq_comp,
      show sys.expFlow (-T) * sys.expFlow T = 1 by
        rw [← expFlow_add, neg_add_cancel, expFlow_zero],
      one_apply_eq_self]
  rw [hx]
  exact expFlow_mem_of_mem_of_map_le sys _
    (map_outputStabilizableSubspace_le sys.A sys.B H) (-T) hexpT

/-- **Restricted open-loop necessity, predicate form.** The eventually-zero
restricted open-loop predicate implies membership in `W_g(ker H)`. This is the
clearly scoped restricted-input consequence; it does not imply the unrestricted
Corollary 6.22 necessity. -/
theorem mem_outputStabilizableSubspace_of_eventuallyZeroInput
    (sys : LinearSystem ℝ X U Z) (H : X →ₗ[ℝ] Z) {x : X}
    (h : IsOutputStabilizableWithEventuallyZeroInput sys H x) :
    x ∈ outputStabilizableSubspace sys.A sys.B H := by
  obtain ⟨u, hu, hevent, htend⟩ := h
  exact mem_outputStabilizableSubspace_of_isOutputStabilizable_of_eventuallyZero
    sys H hu hevent htend

end EventuallyZeroInput

/-! ### Continuity of the trajectory in the input (`L¹` on a compact horizon)

The finite-Bohl quotient non-cancellation of the preceding sections applies to
inputs whose `B`-image is a finite exponential polynomial. The lemma below is the
elementary continuity estimate that a *truncation / step-function approximation*
argument from that class to a general locally integrable input would have to
consume: on a fixed compact horizon `[t₀, t]` the variation-of-constants
trajectory depends on the input only through its `L¹` distance, with a constant
that is uniform in the input and independent of the initial state.

Concretely, for locally integrable `u`, `v`, if `M` bounds
`‖exp (-(s - t₀) A)‖ · ‖B‖` for `s ∈ [t₀, t]`, then

`‖x_u(t) - x_v(t)‖ ≤ ‖exp ((t - t₀) A)‖ · M · ∫_{t₀}^{t} ‖u s - v s‖ ds`.

The initial state cancels in the difference of the two variation-of-constants
formulae, leaving the `exp ((t - t₀) A)`-image of the difference of the two
forcing integrals; the estimate then only uses the operator-norm inequality for
the bounded operators `exp (-(s - t₀) A)` and `B`. This is the
"reachable quotient is continuous in `L¹_loc`" half of the approximation
question, and it immediately yields `L¹`-continuity of the trajectory at each
fixed time (`tendsto_variationOfConstants_of_tendsto_integral_norm`).

It is deliberately *only* a compact-horizon estimate: the constant
`‖exp ((t - t₀) A)‖` grows with the horizon `t`, so an `L¹`-close sequence of
inputs does not inherit the decay of the readout `t ↦ C x(t)` at `+∞`. The lemma
therefore does **not** imply the unrestricted `W_g` necessity
`mem_outputStabilizableSubspace_of_isOutputStabilizable`: compact-time `L¹`
convergence of inputs controls the trajectory only on bounded time sets, while
decay at `+∞` is a global, spectral property of the *whole* forcing
(equivalently, of the transfer function `C (sI - A)⁻¹ B`). The finite-Bohl
non-cancellation cannot be transferred by this continuity alone, and no such
transfer is asserted. -/

section InputContinuity

/-- **`L¹` continuity of the LTI trajectory in its input on a compact horizon.**
If `M` bounds `‖exp (-(s - t₀) A)‖ · ‖B‖` for every `s ∈ [t₀, t]`, then the
difference of the two variation-of-constants trajectories from the same initial
state is controlled by the `L¹` distance of the inputs:
`‖x_u(t) - x_v(t)‖ ≤ ‖exp ((t - t₀) A)‖ · M · ∫_{t₀}^{t} ‖u s - v s‖`. -/
theorem norm_variationOfConstants_sub_le
    (sys : LinearSystem ℝ X U Z) (t₀ : ℝ) (x₀ : X) {u v : ℝ → U}
    (hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume)
    (hv : MeasureTheory.LocallyIntegrable v MeasureTheory.volume)
    {t M : ℝ} (ht : t₀ ≤ t)
    (hM : ∀ s ∈ Set.uIcc t₀ t, ‖sys.expFlow (-(s - t₀))‖ * ‖sys.continuousB‖ ≤ M) :
    ‖sys.variationOfConstants t₀ x₀ u t - sys.variationOfConstants t₀ x₀ v t‖ ≤
      ‖sys.expFlow (t - t₀)‖ * M * ∫ s in t₀..t, ‖u s - v s‖ := by
  have hforcing_sub : ∀ s : ℝ, sys.forcing t₀ u s - sys.forcing t₀ v s =
      sys.forcing t₀ (u - v) s := by
    intro s
    simp only [LinearSystem.forcing, Pi.sub_apply, map_sub]
  have hdiff : sys.variationOfConstants t₀ x₀ u t - sys.variationOfConstants t₀ x₀ v t =
      sys.expFlow (t - t₀) (∫ s in t₀..t, sys.forcing t₀ u s - sys.forcing t₀ v s) := by
    rw [LinearSystem.variationOfConstants, LinearSystem.variationOfConstants, ← map_sub]
    congr 1
    have h1 : (x₀ + ∫ s in t₀..t, sys.forcing t₀ u s) -
        (x₀ + ∫ s in t₀..t, sys.forcing t₀ v s) =
        (∫ s in t₀..t, sys.forcing t₀ u s) -
          (∫ s in t₀..t, sys.forcing t₀ v s) := by abel
    rw [h1, ← intervalIntegral.integral_sub
      (intervalIntegrable_forcing sys t₀ hu t₀ t)
      (intervalIntegrable_forcing sys t₀ hv t₀ t)]
  have hNormInt : IntervalIntegrable (fun s : ℝ => ‖(u - v) s‖) MeasureTheory.volume t₀ t :=
    intervalIntegrable_iff.mpr <|
      MeasureTheory.Integrable.norm
        (((hu.sub hv).integrableOn_isCompact isCompact_uIcc).mono_set Set.uIoc_subset_uIcc)
  have hBound : ‖∫ s in t₀..t, sys.forcing t₀ u s - sys.forcing t₀ v s‖ ≤
      M * ∫ s in t₀..t, ‖u s - v s‖ := by
    have hmono : (∫ s in t₀..t, ‖sys.forcing t₀ (u - v) s‖) ≤
        M * ∫ s in t₀..t, ‖(u - v) s‖ := by
      have h := intervalIntegral.integral_mono_on ht
        ((intervalIntegrable_forcing sys t₀ (hu.sub hv) t₀ t).norm)
        (hNormInt.const_mul M) (fun s hs => by
          have hs' : s ∈ Set.uIcc t₀ t := by
            rw [Set.uIcc_of_le ht]
            exact hs
          calc ‖sys.forcing t₀ (u - v) s‖
              = ‖sys.expFlow (-(s - t₀)) (sys.continuousB ((u - v) s))‖ := rfl
            _ ≤ ‖sys.expFlow (-(s - t₀))‖ * ‖sys.continuousB ((u - v) s)‖ :=
                (sys.expFlow (-(s - t₀))).le_opNorm _
            _ ≤ ‖sys.expFlow (-(s - t₀))‖ * (‖sys.continuousB‖ * ‖(u - v) s‖) :=
                mul_le_mul_of_nonneg_left (sys.continuousB.le_opNorm _) (norm_nonneg _)
            _ = (‖sys.expFlow (-(s - t₀))‖ * ‖sys.continuousB‖) * ‖(u - v) s‖ := by ring
            _ ≤ M * ‖(u - v) s‖ :=
                mul_le_mul_of_nonneg_right (hM s hs') (norm_nonneg _))
      rwa [intervalIntegral.integral_const_mul] at h
    have hIntEq : (∫ s in t₀..t, sys.forcing t₀ u s - sys.forcing t₀ v s) =
        ∫ s in t₀..t, sys.forcing t₀ (u - v) s :=
      intervalIntegral.integral_congr (fun s _ => hforcing_sub s)
    rw [hIntEq]
    calc ‖∫ s in t₀..t, sys.forcing t₀ (u - v) s‖
        ≤ ∫ s in t₀..t, ‖sys.forcing t₀ (u - v) s‖ :=
          intervalIntegral.norm_integral_le_integral_norm ht
      _ ≤ M * ∫ s in t₀..t, ‖(u - v) s‖ := hmono
      _ = M * ∫ s in t₀..t, ‖u s - v s‖ := rfl
  rw [hdiff]
  calc ‖sys.expFlow (t - t₀) (∫ s in t₀..t, sys.forcing t₀ u s - sys.forcing t₀ v s)‖
      ≤ ‖sys.expFlow (t - t₀)‖ * ‖∫ s in t₀..t,
          sys.forcing t₀ u s - sys.forcing t₀ v s‖ :=
        (sys.expFlow (t - t₀)).le_opNorm _
    _ ≤ ‖sys.expFlow (t - t₀)‖ * (M * ∫ s in t₀..t, ‖u s - v s‖) :=
        mul_le_mul_of_nonneg_left hBound (norm_nonneg _)
    _ = ‖sys.expFlow (t - t₀)‖ * M * ∫ s in t₀..t, ‖u s - v s‖ := by ring

/-- **Continuity of the trajectory in the input at a fixed time (`L¹`).** If a
sequence of locally integrable inputs `us n` converges to `u` in the `L¹`
interval norm, `∫_{t₀}^{t} ‖us n s - u s‖ → 0`, then the corresponding
trajectories converge at the fixed time `t`. This is the direct continuity
transport of `norm_variationOfConstants_sub_le`; the bound constant
`‖exp ((t - t₀) A)‖ · M` is uniform in the inputs. -/
theorem tendsto_variationOfConstants_of_tendsto_integral_norm
    (sys : LinearSystem ℝ X U Z) (t₀ : ℝ) (x₀ : X) {u : ℝ → U}
    (hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume) {us : ℕ → ℝ → U}
    (hus : ∀ n, MeasureTheory.LocallyIntegrable (us n) MeasureTheory.volume)
    {t : ℝ} (ht : t₀ ≤ t)
    (hconv : Filter.Tendsto (fun n => ∫ s in t₀..t, ‖us n s - u s‖)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => sys.variationOfConstants t₀ x₀ (us n) t)
      Filter.atTop (nhds (sys.variationOfConstants t₀ x₀ u t)) := by
  obtain ⟨M, hM⟩ := isCompact_uIcc.exists_bound_of_continuousOn
    ((continuous_forcing_operator sys t₀).norm.continuousOn)
  have hbound : ∀ n, ‖sys.variationOfConstants t₀ x₀ (us n) t -
      sys.variationOfConstants t₀ x₀ u t‖ ≤
      (‖sys.expFlow (t - t₀)‖ * (M * ‖sys.continuousB‖)) *
        ∫ s in t₀..t, ‖us n s - u s‖ :=
    fun n => norm_variationOfConstants_sub_le sys t₀ x₀ (hus n) hu ht
      (fun s hs => mul_le_mul_of_nonneg_right (by simpa using hM s hs) (norm_nonneg _))
  have hC : Filter.Tendsto (fun n =>
      (‖sys.expFlow (t - t₀)‖ * (M * ‖sys.continuousB‖)) *
        ∫ s in t₀..t, ‖us n s - u s‖) Filter.atTop (nhds 0) := by
    have h := hconv.const_mul (‖sys.expFlow (t - t₀)‖ * (M * ‖sys.continuousB‖))
    simpa using h
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hC
      (fun _ => norm_nonneg _) hbound)

end InputContinuity

/-! ### Repository/API audit for the state-level Bohl/spectral projection

Before this attempt the following searches were run against the pinned tree
(Lean `4.34.0-rc2`, Mathlib `4.34.0-rc2`, DynamicalSystems `8db9c3c`); the
results are the search evidence for the remaining gap.

* `grep -rli bohl Mathlib` — **0 files**. There is no Bohl-function,
  spectrum-of-a-function, or exponential-polynomial API beyond the finite-sum
  lemmas already in `DynamicalSystems.Linear.Stabilization`.
* `grep -rli laplace Mathlib` — 4 files
  (`LinearAlgebra/Matrix/Determinant/Bird/Correctness.lean` and
  `LinearAlgebra/Matrix/SemiringInverse.lean` — Laplace *determinant expansions*;
  `Analysis/Distribution/DerivNotation.lean` — the Laplace *operator* notation;
  `Analysis/Calculus/AbsolutelyMonotone.lean` — a citation). No transform of a
  signal.
* `grep -rli titchmarsh Mathlib` — **0 files**.
* One-parameter continuous semigroups: **0 files** (only
  `RepresentationTheory/Continuous/Basic.lean` for group representations). The
  `DynamicalSystems` semigroup API (`Basic/Autonomous.lean`,
  `Basic/NonAutonomous.lean`, `Stability/Floquet.lean`) is combinatorial and
  carries no spectral theory.
* Spectral/Riesz projection for operators: **0 files**.
* `Mathlib/MeasureTheory/Measure/ResolventTransform.lean` provides the
  Stieltjes/Cauchy transform of a *measure*, not the Laplace transform of a
  trajectory; `resolvent`/`resolventSet` exist and are already used by the
  accepted `LinearMap.eigenfunctional_resolvent_eq_zero` in this file.
* ODE layer: `DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistenceLinear`
  supplies global existence for a *globally Lipschitz / linear-growth field*
  (`exists_solution_Icc_of_linear_growth`, `global_existence`), not for merely
  locally integrable forcing; `...ODE.FundamentalSolution` supplies only the
  `IsFundamentalSolution` derivative lemmas, not a preconstructed LTI
  exponential flow. The accepted LTI flow is `LinearSystem.expFlow`.
* `Module.End.maxGenEigenspace` and the finite-dimensional generalized
  eigenspace decomposition (`Mathlib/LinearAlgebra/Eigenspace/*`) *are* present
  and are already used by `Stabilization.lean` for the autonomous antistable
  readout theorem `LinearMap.antistable_readout_forces_unobservable`.

Prior branches/commits: `linear-control-ralph`, `barbalat-ralph`, `pr67-ralph`
and `feat/input-output-graphs` were inspected. The only declarations absent from
this worktree concern unrelated files and are already merged
(`linear_fundamental_solution` in `GlobalExistence.lean`, `isCompleteVectorField`
in `Dynamics/Basic.lean`, `isGraph_inputOutput`/`isGraph_inputState` in
`InputOutput/ClosedLoop.lean`). No unmerged declaration supplies the Bohl/Laplace
input decomposition.

The one focused assembly attempt using the discovered APIs is the
reachable-invisible readout theorem below: it closes the unrestricted locally
integrable input quantifier in the case that the readout annihilates the whole
reachable subspace `⟨A | im B⟩` (so no input can affect the output at all). It
genuinely connects `variationOfConstants_sub_expFlow_mem_reachableSubspace` (the
reachable quotient-autonomy lemma) with
`LinearMap.antistable_readout_forces_unobservable` (the autonomous spectral
extraction). The general case is not reached because the input can add a
reachable readout `H r_t` that is not separated from the autonomous antistable
readout without a spectral projection of the *input*; this is the exact
remaining gap recorded at the end of the file. -/

/-- **Unrestricted open-loop necessity when the readout annihilates the
reachable subspace.** If `⟨A | im B⟩ ≤ ker H`, then the forced trajectory and the
autonomous orbit have the same readout (`variationOfConstants_sub_expFlow_mem_reachableSubspace`
kills the input contribution), so the input quantifier is vacuous and the
accepted spectral decomposition argument applies verbatim. Hence every
open-loop output-stabilizable state lies in `W_g(ker H) = V*(ker H) + Xstab`.

This is a genuine partial case of `mem_outputStabilizableSubspace_of_isOutputStabilizable`:
it covers, for example, every strictly proper system whose controlled output
does not see the reachable directions (and all of `B = 0`), while the general
case still needs the Bohl/spectral projection of the input recorded below. -/
theorem mem_outputStabilizableSubspace_of_isOutputStabilizable_of_reachable_le_ker
    (sys : LinearSystem ℝ X U Z) (H : X →ₗ[ℝ] Z)
    (hR : LinearMap.reachableSubspace sys.A sys.B ≤ LinearMap.ker H)
    {x : X} (h : IsOutputStabilizable sys H x) :
    x ∈ outputStabilizableSubspace sys.A sys.B H := by
  obtain ⟨u, hu, htend⟩ := h
  have hsame : (fun t : ℝ => H (sys.variationOfConstants 0 x u t)) =
      fun t : ℝ => H (NormedSpace.exp (t • sys.A.toContinuousLinearMap) x) := by
    funext t
    have hmem := variationOfConstants_sub_expFlow_mem_reachableSubspace sys x hu t
    have hzero : H (sys.variationOfConstants 0 x u t - sys.expFlow t x) = 0 :=
      LinearMap.mem_ker.mp (hR hmem)
    have hsplit : sys.variationOfConstants 0 x u t =
        sys.expFlow t x + (sys.variationOfConstants 0 x u t - sys.expFlow t x) := by
      abel
    rw [hsplit, map_add, hzero, add_zero]
    rfl
  have hdec : Filter.Tendsto
      (fun t : ℝ => H (NormedSpace.exp (t • sys.A.toContinuousLinearMap) x))
      Filter.atTop (nhds 0) := by
    rw [← hsame]
    exact htend
  have hxmem : x ∈ LinearMap.hurwitzSubspace sys.A ⊔ LinearMap.unstableSubspace sys.A := by
    rw [LinearMap.hurwitzSubspace_sup_unstableSubspace_eq_top]
    trivial
  obtain ⟨xg, hxg, xb, hxb, hxeq⟩ := Submodule.mem_sup.mp hxmem
  have hgdec : Filter.Tendsto
      (fun t : ℝ => H (NormedSpace.exp (t • sys.A.toContinuousLinearMap) xg))
      Filter.atTop (nhds 0) :=
    tendsto_readout_exp_of_mem_hurwitzSubspace sys.A H hxg
  have hbdec : Filter.Tendsto
      (fun t : ℝ => H (NormedSpace.exp (t • sys.A.toContinuousLinearMap) xb))
      Filter.atTop (nhds 0) := by
    have hsplit : (fun t : ℝ => H (NormedSpace.exp (t • sys.A.toContinuousLinearMap) x)) =
        fun t : ℝ => H (NormedSpace.exp (t • sys.A.toContinuousLinearMap) xg) +
          H (NormedSpace.exp (t • sys.A.toContinuousLinearMap) xb) := by
      funext t
      rw [← hxeq, map_add, map_add]
    have h' := hdec
    rw [hsplit] at h'
    simpa using h'.sub hgdec
  have hxb_unobs : xb ∈ LinearMap.unobservableSubspace H sys.A :=
    LinearMap.antistable_readout_forces_unobservable sys.A H hxb hbdec
  have hxb_ctrl : xb ∈ LinearMap.controlledInvariantSubspace sys.A sys.B (LinearMap.ker H) :=
    LinearMap.le_controlledInvariantSubspace
      (LinearMap.unobservableSubspace_le_ker H sys.A)
      (by
        rw [LinearMap.IsControlledInvariant]
        exact le_trans (LinearMap.map_unobservableSubspace_le H sys.A) le_sup_left)
      hxb_unobs
  have hxg_stab : xg ∈ LinearMap.stabilizableSubspace sys.A sys.B :=
    LinearMap.hurwitzSubspace_le_stabilizableSubspace sys.A sys.B hxg
  rw [outputStabilizableSubspace, ← hxeq, add_comm xg xb]
  exact Submodule.add_mem_sup hxb_ctrl hxg_stab

/-! ## Exponential-polynomial inputs: Laplace-transform uniqueness

The unrestricted open-loop necessity is obstructed at the ``reachable readout''
term `H r_t`, where `x_u(t) = e^{tA} x + r_t` with `r_t ∈ R = ⟨A | im B⟩`. This
section prepares the *Laplace-transform / exponential-polynomial* scoping of that
obstruction. The class of signals with a finite expansion in exponential
characters times polynomials is the natural one for which the Laplace transform
is a rational function and the representation is unique, so that a decaying
combination of antistable characters must vanish identically. That uniqueness is
`tendsto_zero_of_isAntistableExponentialPolynomial`, a direct consequence of the
accepted polynomial-exponential reduction
`LinearMap.tendsto_zero_of_sum_exp_polynomial`.

The frequency-domain companion of the time-domain autonomous-residue identity
`LinearMap.eigenfunctional_exp_apply` is proved separately in the `LinearMap`
namespace at the end of the file: the input transfer `ρ (s I - A)⁻¹ B` has **no**
value at an uncontrollable eigenmode, `ρ (resolvent A s (B v)) = 0` for
`s ≠ lam`. It is the Laplace-domain statement that the input channel has no pole
at `lam` because `ρ ∘ B = 0`. -/

/-- **Antistable exponential-polynomial functions.** A complex-valued function on
`ℝ` that is a finite sum of polynomial terms against complex exponential
characters whose frequencies have nonnegative real part:

`f t = ∑ i : Fin n, e^{t * μ i} * (∑ k < D + 1, t ^ k * a i k)`

with distinct `μ i` and `0 ≤ (μ i).re`. These are the finite-dimensional
``exponential-order'' signals whose Laplace transform is a rational function with
all poles in the closed right half-plane: a decaying such signal must vanish
identically (`tendsto_zero_of_isAntistableExponentialPolynomial`). -/
def IsAntistableExponentialPolynomial (f : ℝ → ℂ) : Prop :=
  ∃ (n D : ℕ) (μ : Fin n → ℂ) (a : Fin n → ℕ → ℂ),
    (∀ i, 0 ≤ (μ i).re) ∧ Function.Injective μ ∧
      ∀ t, f t = ∑ i : Fin n, Complex.exp ((t : ℂ) * μ i) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a i k)

/-- **Laplace-transform uniqueness for antistable exponential polynomials.** A
finite sum of polynomial terms times exponential characters with nonnegative
real parts that tends to `0` at `+∞` is identically zero: all polynomial
coefficients at every (antistable) frequency vanish. This is the elementary
uniqueness behind the convolution non-cancellation reading, and it is exactly the
accepted `LinearMap.tendsto_zero_of_sum_exp_polynomial` packaged for the named
exponential-polynomial class. -/
theorem tendsto_zero_of_isAntistableExponentialPolynomial {f : ℝ → ℂ}
    (hf : IsAntistableExponentialPolynomial f)
    (h : Filter.Tendsto f Filter.atTop (nhds 0)) : f = 0 := by
  obtain ⟨n, D, μ, a, hμ, hinj, hrepr⟩ := hf
  have hz : ∀ i : Fin n, ∀ k ≤ D, a i k = 0 := by
    have hz' : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ k ≤ D, a i k = 0 :=
      LinearMap.tendsto_zero_of_sum_exp_polynomial (Finset.univ : Finset (Fin n))
        μ (fun i _ => hμ i) (fun i _ j _ hij => hinj hij) D a (by
          have hfun : (fun t : ℝ => ∑ i : Fin n, Complex.exp ((t : ℂ) * μ i) •
              (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a i k)) = f := by
            funext t
            exact (hrepr t).symm
          rw [hfun]
          exact h)
    intro i k hk
    exact hz' i (Finset.mem_univ i) k hk
  funext t
  rw [hrepr t]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hinner : (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a i k) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [hz i k (Nat.lt_succ_iff.mp hk), smul_zero]
  rw [hinner, smul_zero]

end LinearSystem

namespace LinearMap

variable {X U : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]

private theorem map_spectralComplexSubspace_of_intertwining
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [FiniteDimensional ℝ X]
    (A : X →ₗ[ℝ] X) (T : Y →ₗ[ℝ] Y) (q : X →ₗ[ℝ] Y)
    (hq : q.comp A = T.comp q) (p : ℂ → Prop) :
    Submodule.map
      (Matrix.toLin' (((LinearMap.toMatrix (Module.finBasis ℝ X)
        (Module.finBasis ℝ Y) q).map (algebraMap ℝ ℂ))))
      (⨆ μ : {μ : ℂ // p μ}, Module.End.maxGenEigenspace
        (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) μ.1) ≤
      ⨆ μ : {μ : ℂ // p μ}, Module.End.maxGenEigenspace
        (Matrix.toLin' ((hurwitzMatrix T).map (algebraMap ℝ ℂ))) μ.1 := by
  let M := LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ Y) q
  have hmat : M * hurwitzMatrix A = hurwitzMatrix T * M := by
    dsimp [M, hurwitzMatrix]
    rw [← LinearMap.toMatrix_comp (v₁ := Module.finBasis ℝ X)
          (v₂ := Module.finBasis ℝ X) (v₃ := Module.finBasis ℝ Y) q A,
      hq, LinearMap.toMatrix_comp (v₁ := Module.finBasis ℝ X)
        (v₂ := Module.finBasis ℝ Y) (v₃ := Module.finBasis ℝ Y) T q]
  have hmatc : M.map (algebraMap ℝ ℂ) *
        (hurwitzMatrix A).map (algebraMap ℝ ℂ) =
      (hurwitzMatrix T).map (algebraMap ℝ ℂ) * M.map (algebraMap ℝ ℂ) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hmat]
  rw [Submodule.map_iSup]
  refine iSup_le fun μ => ?_
  exact le_iSup_of_le μ (map_toLin'_maxGenEigenspace _ _ _ μ.1 hmatc)

private theorem map_hurwitzSubspace_of_intertwining
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [FiniteDimensional ℝ X]
    (A : X →ₗ[ℝ] X) (T : Y →ₗ[ℝ] Y) (q : X →ₗ[ℝ] Y)
    (hq : q.comp A = T.comp q) :
    Submodule.map q (hurwitzSubspace A) ≤ hurwitzSubspace T := by
  have hmap := map_spectralComplexSubspace_of_intertwining A T q hq (fun μ => μ.re < 0)
  intro z hz
  rw [Submodule.mem_map] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  rw [mem_hurwitzSubspace] at hx ⊢
  rw [← ofRealPi_equivFun_toLin'_apply q x]
  exact hmap ⟨_, hx, rfl⟩

private theorem map_unstableSubspace_of_intertwining
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    [FiniteDimensional ℝ X]
    (A : X →ₗ[ℝ] X) (T : Y →ₗ[ℝ] Y) (q : X →ₗ[ℝ] Y)
    (hq : q.comp A = T.comp q) :
    Submodule.map q (unstableSubspace A) ≤ unstableSubspace T := by
  have hmap := map_spectralComplexSubspace_of_intertwining A T q hq (fun μ => ¬ μ.re < 0)
  intro z hz
  rw [Submodule.mem_map] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  rw [mem_unstableSubspace] at hx ⊢
  rw [← ofRealPi_equivFun_toLin'_apply q x]
  exact hmap ⟨_, hx, rfl⟩

/-- **Hurwitz spectral subspaces pass to the uncontrollable quotient.** The
quotient map by `reachableSubspace A B` intertwines `A` with
`quotientReachableA A B`, so it carries negative-real-part generalized modes to
negative-real-part generalized modes. The closedness assumption supplies the
normed quotient required by the Hurwitz-subspace definition. -/
theorem map_hurwitzSubspace_quotientReachable_le
    [FiniteDimensional ℝ X] (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    [IsClosed (reachableSubspace A B : Set X)] :
    Submodule.map (reachableSubspace A B).mkQ (hurwitzSubspace A) ≤
      hurwitzSubspace (quotientReachableA A B) := by
  let R := reachableSubspace A B
  let Aq : (X ⧸ R) →ₗ[ℝ] (X ⧸ R) := R.mapQ R A
    ((Submodule.map_le_iff_le_comap).mp (map_reachableSubspace_le A B))
  have hR : R ≤ R.comap A := fun x hx => map_reachableSubspace_le A B ⟨x, hx, rfl⟩
  have hq : R.mkQ.comp A = Aq.comp R.mkQ := by
    ext x
    exact (congrFun (congrArg DFunLike.coe
      (Submodule.mapQ_mkQ R R A (h := hR))) x).symm
  exact map_hurwitzSubspace_of_intertwining A Aq R.mkQ hq

/-- **Unstable spectral subspaces pass to the uncontrollable quotient.** This is
the closed-right-half-plane counterpart of
`map_hurwitzSubspace_quotientReachable_le`. -/
theorem map_unstableSubspace_quotientReachable_le
    [FiniteDimensional ℝ X] (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    [IsClosed (reachableSubspace A B : Set X)] :
    Submodule.map (reachableSubspace A B).mkQ (unstableSubspace A) ≤
      unstableSubspace (quotientReachableA A B) := by
  let R := reachableSubspace A B
  let Aq : (X ⧸ R) →ₗ[ℝ] (X ⧸ R) := R.mapQ R A
    ((Submodule.map_le_iff_le_comap).mp (map_reachableSubspace_le A B))
  have hR : R ≤ R.comap A := fun x hx => map_reachableSubspace_le A B ⟨x, hx, rfl⟩
  have hq : R.mkQ.comp A = Aq.comp R.mkQ := by
    ext x
    exact (congrFun (congrArg DFunLike.coe
      (Submodule.mapQ_mkQ R R A (h := hR))) x).symm
  exact map_unstableSubspace_of_intertwining A Aq R.mkQ hq

/-- **The stable quotient lifts to the stabilizable subspace.** The preimage
under the uncontrollable quotient map of its Hurwitz subspace is exactly the
sum of the original Hurwitz subspace and the reachable subspace, i.e. the
stabilizable subspace `Xstab(A, B)`. -/
theorem comap_hurwitzSubspace_quotientReachable_eq
    [FiniteDimensional ℝ X] (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    [IsClosed (reachableSubspace A B : Set X)] :
    Submodule.comap (reachableSubspace A B).mkQ
      (hurwitzSubspace (quotientReachableA A B)) =
      hurwitzSubspace A ⊔ reachableSubspace A B := by
  apply le_antisymm
  · let R := reachableSubspace A B
    let Aq : (X ⧸ R) →ₗ[ℝ] (X ⧸ R) := R.mapQ R A
      ((Submodule.map_le_iff_le_comap).mp (map_reachableSubspace_le A B))
    intro x hx
    have hxQ : R.mkQ x ∈ hurwitzSubspace Aq := by
      simpa [Aq, quotientReachableA, R] using hx
    have hxsplit : x ∈ hurwitzSubspace A ⊔ unstableSubspace A := by
      rw [hurwitzSubspace_sup_unstableSubspace_eq_top]
      trivial
    obtain ⟨xg, hxg, xb, hxb, hsum⟩ := Submodule.mem_sup.mp hxsplit
    have hxgQ : R.mkQ xg ∈ hurwitzSubspace Aq := by
      have h := map_hurwitzSubspace_quotientReachable_le A B ⟨xg, hxg, rfl⟩
      simpa [Aq, quotientReachableA, R] using h
    have hxbQ_unstable : R.mkQ xb ∈ unstableSubspace Aq := by
      have h := map_unstableSubspace_quotientReachable_le A B ⟨xb, hxb, rfl⟩
      simpa [Aq, quotientReachableA, R] using h
    have hsumQ : R.mkQ xg + R.mkQ xb = R.mkQ x := by
      rw [← hsum, map_add]
    have hxbQ_hurwitz : R.mkQ xb ∈ hurwitzSubspace Aq := by
      have hsub := (hurwitzSubspace Aq).sub_mem hxQ hxgQ
      have heq : R.mkQ xb = R.mkQ x - R.mkQ xg := by
        calc
          R.mkQ xb = R.mkQ xg + R.mkQ xb - R.mkQ xg := by abel
          _ = R.mkQ x - R.mkQ xg := by rw [hsumQ]
      rw [heq]
      exact hsub
    have hxbQ_bot : R.mkQ xb = 0 := by
      have hmem : R.mkQ xb ∈ hurwitzSubspace Aq ⊓ unstableSubspace Aq :=
        ⟨hxbQ_hurwitz, hxbQ_unstable⟩
      have hdisj := disjoint_iff.mp (disjoint_hurwitzSubspace_unstableSubspace Aq)
      rw [hdisj] at hmem
      simpa using hmem
    have hxbR : xb ∈ R := by
      rw [← Submodule.ker_mkQ R]
      exact hxbQ_bot
    exact Submodule.mem_sup.mpr ⟨xg, hxg, xb, hxbR, hsum⟩
  · intro x hx
    rw [Submodule.mem_comap]
    rw [Submodule.mem_sup] at hx
    obtain ⟨xg, hxg, xr, hxr, hsum⟩ := hx
    rw [← hsum, map_add]
    have hxgQ : (reachableSubspace A B).mkQ xg ∈
        hurwitzSubspace (quotientReachableA A B) :=
      map_hurwitzSubspace_quotientReachable_le A B ⟨xg, hxg, rfl⟩
    have hxrQ : (reachableSubspace A B).mkQ xr = 0 := by
      rw [Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hxr
    rw [hxrQ, add_zero]
    exact hxgQ

/-- **Laplace/transfer non-cancellation at an uncontrollable eigenmode.** Let
`ρ : X →L[ℝ] ℂ` be a complex left eigenfunctional of `A` at the mode `lam`,
`ρ (A y) = lam * ρ y`, and suppose `ρ` annihilates the input channel,
`ρ (B v) = 0`. If `R` is any right inverse of `s • 1 - A`
(`(s • 1 - A) * R = 1`), then the transfer value `ρ (R (B v))` vanishes unless
`s = lam`:

`(s - lam) * ρ (R (B v)) = ρ (B v) = 0`.

This is the frequency-domain counterpart of the time-domain autonomous-residue
identity `eigenfunctional_exp_apply`: the Laplace transform `ρ (s I - A)⁻¹ B` of
the input-to-readout channel has no pole at the uncontrollable mode `lam`. -/
theorem eigenfunctional_resolvent_apply_eq_zero
    (A : X →L[ℝ] X) (ρ : X →L[ℝ] ℂ) (lam : ℂ)
    (hA : ∀ y : X, ρ (A y) = lam * ρ y)
    (B : U →L[ℝ] X) (hB : ∀ v : U, ρ (B v) = 0)
    {s : ℝ} (R : X →L[ℝ] X) (hR : (s • (1 : X →L[ℝ] X) - A) * R = 1)
    (hs : (s : ℂ) ≠ lam) (v : U) :
    ρ (R (B v)) = 0 := by
  have hcomp : ρ (B v) = ((s : ℂ) - lam) * ρ (R (B v)) := by
    have h1 : (s • (1 : X →L[ℝ] X) - A) (R (B v)) = B v := by
      have := congrArg (fun g : X →L[ℝ] X => g (B v)) hR
      simpa using this
    calc ρ (B v) = ρ ((s • (1 : X →L[ℝ] X) - A) (R (B v))) := by rw [h1]
      _ = ρ (s • (R (B v)) - A (R (B v))) := by
            rw [_root_.sub_apply, _root_.smul_apply, one_apply_eq_self]
      _ = s • ρ (R (B v)) - ρ (A (R (B v))) := by rw [map_sub, map_smul]
      _ = s • ρ (R (B v)) - lam * ρ (R (B v)) := by rw [hA]
      _ = ((s : ℂ) - lam) * ρ (R (B v)) := by
            rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul, sub_mul]
            rfl
  have h0 : ((s : ℂ) - lam) * ρ (R (B v)) = 0 := by rw [← hcomp, hB v]
  rcases mul_eq_zero.mp h0 with h' | h'
  · exact absurd (sub_eq_zero.mp h') hs
  · exact h'

/-- **Resolvent form of the Laplace non-cancellation.** Specialising the right
inverse to the resolvent `R = resolvent A s`, for `s` in the resolvent set the
input transfer `ρ (resolvent A s (B v))` vanishes at every mode `lam ≠ s`. Hence
the transfer function of the input channel, evaluated through an uncontrollable
eigenfunctional, is zero wherever it is defined. -/
theorem eigenfunctional_resolvent_eq_zero
    (A : X →L[ℝ] X) (ρ : X →L[ℝ] ℂ) (lam : ℂ)
    (hA : ∀ y : X, ρ (A y) = lam * ρ y)
    (B : U →L[ℝ] X) (hB : ∀ v : U, ρ (B v) = 0)
    {s : ℝ} (hs : s ∈ resolventSet ℝ A) (hsl : (s : ℂ) ≠ lam) (v : U) :
    ρ (resolvent A s (B v)) = 0 := by
  have hR : (s • (1 : X →L[ℝ] X) - A) * resolvent A s = 1 := by
    rw [_root_.sub_mul, smul_mul_assoc, one_mul]
    exact sub_eq_iff_eq_add.mpr (smul_resolvent_eq_one_add A hs)
  exact eigenfunctional_resolvent_apply_eq_zero A ρ lam hA B hB
    (resolvent A s) hR hsl v

end LinearMap

/-! ## Assessment: the exponential-polynomial scoping and the bridge to
`IsOutputStabilizable`

This task formalised the *frequency-domain* and *finite-expansion* content of the
convolution non-cancellation statement:

* `LinearMap.eigenfunctional_resolvent_apply_eq_zero` and its resolvent
  specialisation `LinearMap.eigenfunctional_resolvent_eq_zero` — the input
  transfer `ρ (s I - A)⁻¹ B` of an uncontrollable eigenfunctional is zero
  wherever it is defined, `(s - lam) * ρ (R (B v)) = ρ (B v) = 0`;
* `LinearSystem.IsAntistableExponentialPolynomial` and
  `LinearSystem.tendsto_zero_of_isAntistableExponentialPolynomial` — Laplace /
  exponential-polynomial uniqueness: a decaying finite sum of antistable
  polynomial-exponential characters vanishes identically.

The two together give the exact frequency-domain reading of the obstruction: at
an uncontrollable antistable mode `lam`, the autonomous readout carries the
residue `e^{lam t} ρ x` and the input transfer has no pole, so no locally
integrable input can cancel the residue. This is precisely
`LinearSystem.variationOfConstants_eigenfunctional` (and its complex and
Jordan-chain companions), which already holds for **every** locally integrable
input.

### Why the restriction does not bridge to `IsOutputStabilizable`

Restricting the input to the exponential-polynomial class therefore adds **no**
strength on the residue side: the accepted eigenfunctional/Jordan-chain
non-cancellation theorems are unconditional in the input. The genuine remaining
gap is not a property of a single readout functional but a *separation* of the
autonomous antistable part of the **state** from the reachable subspace:

```lean
theorem LinearSystem.mem_outputStabilizableSubspace_of_isOutputStabilizable
    (sys : LinearSystem ℝ X U Z) (H : X →ₗ[ℝ] Z) (x : X)
    (h : IsOutputStabilizable sys H x) :
    x ∈ outputStabilizableSubspace sys.A sys.B H
```

Writing `x_u(t) = e^{tA} x + r_t` with `r_t ∈ R = ⟨A | im B⟩`
(`variationOfConstants_sub_expFlow_mem_reachableSubspace`), the total readout is
`H x_u(t) = H (e^{tA} x) + H r_t`. The missing step is the *spectral* statement
that the reachable readout `H r_t` — the convolution of the Markov kernel
`H e^{tA} B` with `u` — cannot cancel the antistable autonomous residue of the
state. The single-functional form of this statement is false
(`exists_readout_functional_of_notMem_ker_sup_reachable` and the
`V*(ker H ⊔ R)` threshold discussion above); the observability-chain functionals
`ρ ∘ H ∘ Aᵏ` separate only `V*(ker H ⊔ ⟨A | im B⟩)`, which can strictly exceed
`V*(ker H) + Xstab`. This is the documented Titchmarsh/Laplace
convolution-cancellation obligation; it is a statement about the *whole
trajectory* and is independent of whether the input is locally integrable or
exponential-polynomial.

The frequency-domain identity above shows why the exponential-polynomial
hypothesis cannot close that gap: an input may have a frequency `μ` that is an
eigenvalue of `A`, in which case the forcing integrand
`e^{-(s-t₀)A} (B u(s))` produces an `e^{lam t}` term in the reachable readout
exactly when the mode `lam` is *reachable* (some `ρ` with `ρ ∘ B ≠ 0`). When it
does, `H` detects the reachable unstable direction; the cancellation succeeds and
the state lies in `V*(ker H) + Xstab` after all (the two-dimensional examples in
the handoff notes above). When it does not, the accepted eigenfunctional residues
already give non-cancellation for all inputs. The finite-expansion class thus
splits cleanly into cases already covered, and does not add a proof of the
separation.

### Exact remaining obligation

The unrestricted-input obligation remains
`LinearSystem.mem_outputStabilizableSubspace_of_isOutputStabilizable`; the tools
it needs are the ones recorded in the handoff notes: a way to handle arbitrary
locally integrable forcing without a finite-Bohl spectral projection, the
observability-chain readout on the reachable subspace, and the PBH separation at
the threshold `V*(ker H ⊔ ⟨A | im B⟩)`. The finite-Bohl forcing-image case is
proved below by `finiteBohlWBridge`; it does not settle this broader theorem.
The closest unrestricted-input result
proved here is
`mem_outputStabilizableSubspace_of_isOutputStabilizable_of_reachable_le_ker`,
which handles every readout annihilating the reachable subspace; it is a strict
partial case and does not imply the general theorem. The new declarations above
are non-vacuous: the transfer identity holds for any real right inverse of
`s • 1 - A` (in particular the resolvent), and the uniqueness lemma applies to
every decaying antistable exponential polynomial. -/

/-! ## Finite exponential-polynomial (Bohl) input signals

This section begins the missing Bohl/input-spectral formalisation with a
mathematically explicit finite-dimensional foundation. A **Bohl signal** is a
finite sum of *Bohl modes* `t ↦ e^{t μ} • (t ^ k • v)` with complex frequency
`μ`, polynomial order `k` and vector coefficient `v`; equivalently it is the
finite-support spectral representation

`t ↦ ∑_{μ ∈ s} e^{t μ} • (∑_{k < D+1} t ^ k • a μ k)`.

The class is closed under the linear operations (zero, addition, negation,
scalar multiplication), so it is a genuine ambient function space, and antistable
members that vanish at `+∞` are identically zero
(`tendsto_zero_of_isAntistableBohlSignal`) — the accepted polynomial-exponential
vanishing theorem `LinearMap.tendsto_zero_of_sum_exp_polynomial` transported to
the class. Complex conjugation transports the class to itself, carrying the
frequencies to their conjugates (`IsExponentialPolynomial.conj`), which is what
makes the complex-conjugate pairing of real Bohl signals available.

The unrestricted **locally integrable** input predicate remains separate: nothing
here asserts that every locally integrable input is a finite exponential
polynomial, and no closure claim about that predicate is made.

The remaining variation-of-constants milestone is the residue/antiderivative
identity: for a single mode `u s = e^{s μ} • p(s)` the response
`∫_{t₀}^{t} exp ((t-s)A) B (u s) ds` should be an exponential polynomial plus the
autonomous term `exp ((t-t₀)A) x₀`. Its analytic content is that the antiderivative
of `s ↦ e^{s μ} p(s)` is again an exponential polynomial (a polynomial times
`e^{s μ}` when `μ` is not an eigenvalue, with one extra power of `s` in the
resonant/generalized-eigenmode case); this is not asserted here. -/

namespace LinearSystem

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- The elementary **Bohl mode** `t ↦ e^{t μ} • (t ^ k • v)`. -/
noncomputable def BohlModeEval (t : ℝ) (p : ℂ × ℕ × X) : X :=
  Complex.exp ((t : ℂ) * p.1) • ((t : ℂ) ^ p.2.1 • p.2.2)

@[simp]
theorem BohlModeEval_apply (t : ℝ) (p : ℂ × ℕ × X) :
    BohlModeEval t p = Complex.exp ((t : ℂ) * p.1) • ((t : ℂ) ^ p.2.1 • p.2.2) := rfl

/-- A single **Bohl mode** as a predicate. -/
def IsBohlMode (f : ℝ → X) : Prop :=
  ∃ (μ : ℂ) (k : ℕ) (v : X), ∀ t, f t = BohlModeEval t (μ, k, v)

/-- The **finite exponential-polynomial (Bohl) class**: a function `f : ℝ → X` is a
finite sum of Bohl modes, written in the finite-support spectral form
`t ↦ ∑_{μ ∈ s} e^{t μ} • (∑_{k < D+1} t ^ k • a μ k)`.

The frequency set is a genuine `Finset ℂ`, so the frequencies are distinct by
construction; the unrestricted locally integrable predicate is deliberately *not*
identified with this class. -/
def IsExponentialPolynomial (f : ℝ → X) : Prop :=
  ∃ (s : Finset ℂ) (D : ℕ) (a : ℂ → ℕ → X),
    ∀ t, f t = ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
      (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)

theorem isExponentialPolynomial_iff {f : ℝ → X} :
    IsExponentialPolynomial f ↔
      ∃ (s : Finset ℂ) (D : ℕ) (a : ℂ → ℕ → X),
        ∀ t, f t = ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k) := Iff.rfl

/-- Coefficients in a finite exponential-polynomial representation are unique:
if the represented function is zero, every polynomial coefficient at every
frequency in the support is zero. The proof shifts all frequencies by one common
real scalar into the closed right half-plane, then applies
`LinearMap.tendsto_zero_of_sum_exp_polynomial`. -/
theorem exponentialPolynomial_coefficients_eq_zero_of_eq_zero
    (s : Finset ℂ) (D : ℕ) (a : ℂ → ℕ → X)
    (hzero : ∀ t : ℝ, ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
      (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k) = 0) :
    ∀ μ ∈ s, ∀ k ≤ D, a μ k = 0 := by
  classical
  let R : ℝ := ∑ μ ∈ s, ‖μ‖
  have hR_dom : ∀ μ ∈ s, ‖μ‖ ≤ R := by
    intro μ hμ
    dsimp [R]
    exact Finset.single_le_sum (fun ν hν => norm_nonneg (ν : ℂ)) hμ
  have hμ_nonneg : ∀ μ ∈ s, 0 ≤ (μ + (R : ℂ)).re := by
    intro μ hμ
    have hRe : -‖μ‖ ≤ μ.re := (abs_le.mp (Complex.abs_re_le_norm μ)).1
    have hReR : 0 ≤ μ.re + R := by linarith [hR_dom μ hμ]
    simpa using hReR
  have hshift (t : ℝ) :
      (∑ μ ∈ s, Complex.exp ((t : ℂ) * (μ + (R : ℂ))) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)) =
      Complex.exp ((t : ℂ) * (R : ℂ)) •
        (∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)) := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro μ hμ
    rw [show (t : ℂ) * (μ + (R : ℂ)) = (t : ℂ) * (R : ℂ) + (t : ℂ) * μ by ring,
      Complex.exp_add, mul_smul]
  have hshift_zero : ∀ t : ℝ,
      ∑ μ ∈ s, Complex.exp ((t : ℂ) * (μ + (R : ℂ))) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k) = 0 := by
    intro t
    rw [hshift t, hzero t, smul_zero]
  apply LinearMap.tendsto_zero_of_sum_exp_polynomial s
    (fun μ => μ + (R : ℂ)) (fun μ hμ => hμ_nonneg μ hμ)
    (by
      intro μ hμ ν hν h
      exact add_right_cancel h)
    D a
  have hfun : (fun t : ℝ =>
      ∑ μ ∈ s, Complex.exp ((t : ℂ) * (μ + (R : ℂ))) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)) = fun _ => (0 : X) := by
    funext t
    exact hshift_zero t
  rw [hfun]
  exact tendsto_const_nhds

/-- Two finite exponential-polynomial representations with the same distinct
frequency set and degree bound have equal coefficients when they agree at every
time. This is the algebraic coefficient-comparison step used after expanding a
finite-dimensional ODE into exponential-polynomial form. -/
theorem exponentialPolynomial_coefficients_eq_of_eq
    (s : Finset ℂ) (D : ℕ) (a b : ℂ → ℕ → X)
    (heq : ∀ t : ℝ,
      (∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)) =
      ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • b μ k)) :
    ∀ μ ∈ s, ∀ k ≤ D, a μ k = b μ k := by
  have hzero : ∀ t : ℝ,
      ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • (a μ k - b μ k)) = 0 := by
    intro t
    rw [show
      (∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • (a μ k - b μ k))) =
      (∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)) -
      (∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • b μ k)) by
        simp only [smul_sub, Finset.sum_sub_distrib]]
    rw [sub_eq_zero.mpr (heq t)]
  have hcoeff := exponentialPolynomial_coefficients_eq_zero_of_eq_zero
    s D (fun μ k => a μ k - b μ k) hzero
  intro μ hμ k hk
  exact sub_eq_zero.mp (hcoeff μ hμ k hk)

/-- Derivative of a finite vector-valued polynomial, before reindexing its
coefficients into the usual degree convention. -/
lemma hasDerivAt_sum_pow_smul (a : ℕ → X) (D : ℕ) (t : ℝ) :
    HasDerivAt (fun r : ℝ =>
      ∑ k ∈ Finset.range (D + 1), (r : ℂ) ^ k • a k)
      (∑ k ∈ Finset.range (D + 1),
        (((k : ℂ) * (t : ℂ) ^ (k - 1)) • a k)) t := by
  have h := HasDerivAt.sum (u := Finset.range (D + 1))
    (A := fun k (r : ℝ) => (r : ℂ) ^ k • a k)
    (A' := fun k => ((k : ℂ) * (t : ℂ) ^ (k - 1)) • a k)
    (fun k _ => by
      have hpow := (hasDerivAt_pow k (t : ℂ)).comp_ofReal
      have hpow' : HasDerivAt (fun r : ℝ => (r : ℂ) ^ k)
          ((k : ℂ) * (t : ℂ) ^ (k - 1)) t := by
        simpa using hpow
      exact hpow'.smul_const (a k))
  convert h using 1
  ext r
  simp only [Finset.sum_apply]

/-- Reindex the polynomial derivative into ordinary nonnegative powers. The
coefficient at degree `D + 1` is padded by zero. -/
lemma sum_pow_smul_derivative_reindex (a : ℕ → X) (D : ℕ) (t : ℝ)
    (hpad : a (D + 1) = 0) :
    (∑ k ∈ Finset.range (D + 1),
      (((k : ℂ) * (t : ℂ) ^ (k - 1)) • a k)) =
    ∑ k ∈ Finset.range (D + 1),
      (t : ℂ) ^ k • ((k + 1 : ℂ) • a (k + 1)) := by
  have hraw :
      (∑ k ∈ Finset.range (D + 1),
        (((k : ℂ) * (t : ℂ) ^ (k - 1)) • a k)) =
      ∑ k ∈ Finset.range D, (((k + 1 : ℕ) : ℂ) * (t : ℂ) ^ k) • a (k + 1) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, zero_smul, pow_zero, one_mul]
    rw [add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
  calc
    _ = ∑ k ∈ Finset.range D, (((k + 1 : ℕ) : ℂ) * (t : ℂ) ^ k) • a (k + 1) := hraw
    _ = ∑ k ∈ Finset.range D,
      (t : ℂ) ^ k • ((k + 1 : ℂ) • a (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        (((k + 1 : ℕ) : ℂ) * (t : ℂ) ^ k) • a (k + 1) =
            ((t : ℂ) ^ k * ((k + 1 : ℕ) : ℂ)) • a (k + 1) := by rw [mul_comm]
        _ = (t : ℂ) ^ k • (((k + 1 : ℕ) : ℂ) • a (k + 1)) := by rw [smul_smul]
      simpa only [Nat.cast_add, Nat.cast_one]
    _ = ∑ k ∈ Finset.range (D + 1),
          (t : ℂ) ^ k • ((k + 1 : ℂ) • a (k + 1)) := by
      apply Finset.sum_subset (Finset.range_mono (Nat.le_succ D))
      intro k hk hknot
      have hlt : k < D + 1 := Finset.mem_range.mp hk
      have hnot : ¬ k < D := by simpa [Finset.mem_range] using hknot
      have hkd : k = D := by omega
      subst k
      simp [hpad]

/-- Derivative of one exponential times a vector-valued polynomial. The derivative
coefficients use a terminal-zero convention at the top degree. -/
lemma hasDerivAt_exp_mul_sum_pow_smul (a : ℕ → X) (D : ℕ) (μ : ℂ) (t : ℝ) :
    HasDerivAt (fun r : ℝ => Complex.exp ((r : ℂ) * μ) •
      (∑ k ∈ Finset.range (D + 1), (r : ℂ) ^ k • a k))
      (Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k •
          (μ • a k + if k < D then ((k + 1 : ℕ) : ℂ) • a (k + 1) else 0))) t := by
  let P : X := ∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a k
  let Q : X := ∑ k ∈ Finset.range D,
    ((((k + 1 : ℕ) : ℂ) * (t : ℂ) ^ k) • a (k + 1))
  have hcoef :
      (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k •
        (μ • a k + if k < D then ((k + 1 : ℕ) : ℂ) • a (k + 1) else 0)) =
      μ • P + Q := by
    dsimp [P, Q]
    rw [show (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k •
        (μ • a k + if k < D then ((k + 1 : ℕ) : ℂ) • a (k + 1) else 0)) =
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • (μ • a k)) +
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k •
          (if k < D then ((k + 1 : ℕ) : ℂ) • a (k + 1) else 0)) by
          simp only [smul_add, Finset.sum_add_distrib]]
    rw [show (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • (μ • a k)) =
        μ • (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a k) by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          rw [smul_smul, smul_smul, mul_comm]]
    rw [show (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k •
        (if k < D then ((k + 1 : ℕ) : ℂ) • a (k + 1) else 0)) =
        ∑ k ∈ Finset.range D, ((((k + 1 : ℕ) : ℂ) * (t : ℂ) ^ k) • a (k + 1)) by
          rw [Finset.sum_range_succ]
          have hlast : ¬ D < D := Nat.lt_irrefl D
          simp only [hlast, if_false, smul_zero, add_zero]
          apply Finset.sum_congr rfl
          intro k hk
          have hlt : k < D := Finset.mem_range.mp hk
          rw [if_pos hlt]
          simp [smul_smul, mul_comm]]
  have hExp : HasDerivAt (fun r : ℝ => Complex.exp ((r : ℂ) * μ))
      (μ * Complex.exp ((t : ℂ) * μ)) t := by
    have hmul : HasDerivAt (fun z : ℂ => z * μ) μ (t : ℂ) := by
      simpa using (hasDerivAt_id (t : ℂ)).mul_const μ
    simpa [mul_comm] using
      ((Complex.hasDerivAt_exp ((t : ℂ) * μ)).comp (t : ℂ) hmul).comp_ofReal
  have hpoly : HasDerivAt (fun r : ℝ =>
      ∑ k ∈ Finset.range (D + 1), (r : ℂ) ^ k • a k) Q t := by
    have h := HasDerivAt.fun_sum (u := Finset.range (D + 1)) (fun k hk =>
      (hasDerivAt_pow k (t : ℂ)).comp_ofReal |>.smul_const (a k))
    dsimp [Q]
    convert h using 1
    rw [Finset.sum_range_succ']
    simp [Nat.cast_succ, add_comm]
  have h := hExp.smul hpoly
  convert h using 1
  · funext r
    rfl
  · rw [hcoef]
    simp only [smul_add]
    rw [add_comm]
    congr 1
    rw [smul_smul]
    congr 1
    ring

/-- Differentiate a finite exponential-polynomial representation, preserving
its frequency support and degree bound. -/
lemma hasDerivAt_sum_exp_mul_sum_pow_smul (s : Finset ℂ) (D : ℕ)
    (a : ℂ → ℕ → X) (t : ℝ) :
    HasDerivAt (fun r : ℝ =>
      ∑ μ ∈ s, Complex.exp ((r : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (r : ℂ) ^ k • a μ k))
      (∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k •
          (μ • a μ k + if k < D then ((k + 1 : ℕ) : ℂ) • a μ (k + 1) else 0))) t := by
  have h := HasDerivAt.sum (u := s)
    (A := fun μ (r : ℝ) => Complex.exp ((r : ℂ) * μ) •
      (∑ k ∈ Finset.range (D + 1), (r : ℂ) ^ k • a μ k))
    (A' := fun μ => Complex.exp ((t : ℂ) * μ) •
      (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k •
        (μ • a μ k + if k < D then ((k + 1 : ℕ) : ℂ) • a μ (k + 1) else 0)))
    (fun μ _ => hasDerivAt_exp_mul_sum_pow_smul (a μ) D μ t)
  convert h using 1
  ext r
  simp only [Finset.sum_apply]

/-- Comparing a represented trajectory's ODE with its finite exponential-
polynomial derivative gives the usual coefficientwise ODE recurrence. At the
top degree the shifted coefficient is interpreted as zero. -/
theorem exponentialPolynomial_ode_coefficient_recurrence (s : Finset ℂ) (D : ℕ)
    (A : X →ₗ[ℂ] X) (a b : ℂ → ℕ → X)
    (hode : ∀ t : ℝ, HasDerivAt
      (fun r : ℝ =>
        ∑ μ ∈ s, Complex.exp ((r : ℂ) * μ) •
          (∑ k ∈ Finset.range (D + 1), (r : ℂ) ^ k • a μ k))
      (A (∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)) +
        (∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • b μ k))) t) :
    ∀ μ ∈ s, ∀ k ≤ D,
      A (a μ k) + b μ k =
        μ • a μ k + if k < D then ((k + 1 : ℕ) : ℂ) • a μ (k + 1) else 0 := by
  let x (t : ℝ) : X :=
    ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
      (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)
  let c (μ : ℂ) (k : ℕ) : X :=
    A (a μ k) + b μ k
  have hrepr (t : ℝ) : A (x t) +
      (∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • b μ k)) =
      ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • c μ k) := by
    dsimp [x, c]
    simp only [map_sum, map_smul, smul_add, Finset.sum_add_distrib]
  have heq : ∀ t : ℝ,
      (∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k •
          (μ • a μ k + if k < D then ((k + 1 : ℕ) : ℂ) • a μ (k + 1) else 0))) =
      ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • c μ k) := by
    intro t
    have hderiv := (hasDerivAt_sum_exp_mul_sum_pow_smul s D a t).deriv
    calc
      _ = deriv x t := hderiv.symm
      _ = A (x t) +
          (∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
            (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • b μ k)) := (hode t).deriv
      _ = _ := hrepr t
  have hcoeff := exponentialPolynomial_coefficients_eq_of_eq s D
    (fun μ k => μ • a μ k +
      if k < D then ((k + 1 : ℕ) : ℂ) • a μ (k + 1) else 0) c heq
  intro μ hμ k hk
  exact (hcoeff μ hμ k hk).symm

/-- A coefficientwise ODE recurrence survives any frequency projection. In
particular, filtering to stable or antistable frequencies produces forced
trajectories satisfying their projected ODEs pointwise. -/
theorem filtered_exponentialPolynomial_hasDerivAt_of_recurrence
    (A : X →ₗ[ℂ] X)
    (s tfilter : Finset ℂ) (D : ℕ) (a b : ℂ → ℕ → X)
    (hrec : ∀ μ ∈ s, ∀ k ≤ D,
      A (a μ k) + b μ k =
        μ • a μ k + if k < D then ((k + 1 : ℕ) : ℂ) • a μ (k + 1) else 0)
    (t : ℝ) :
    HasDerivAt
      (fun r : ℝ =>
        ∑ μ ∈ s, if μ ∈ tfilter then
          Complex.exp ((r : ℂ) * μ) •
            (∑ k ∈ Finset.range (D + 1), (r : ℂ) ^ k • a μ k)
          else 0)
      (A (∑ μ ∈ s, if μ ∈ tfilter then
          Complex.exp ((t : ℂ) * μ) •
            (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)
          else 0) +
        (∑ μ ∈ s, if μ ∈ tfilter then
          Complex.exp ((t : ℂ) * μ) •
            (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • b μ k)
          else 0)) t := by
  classical
  let a' : ℂ → ℕ → X := fun μ k => if μ ∈ tfilter then a μ k else 0
  let b' : ℂ → ℕ → X := fun μ k => if μ ∈ tfilter then b μ k else 0
  have hrec' : ∀ μ ∈ s, ∀ k ≤ D,
      A (a' μ k) + b' μ k =
        μ • a' μ k + if k < D then ((k + 1 : ℕ) : ℂ) • a' μ (k + 1) else 0 := by
    intro μ hμ k hk
    by_cases hμf : μ ∈ tfilter
    · simp [a', b', hμf, hrec μ hμ k hk]
    · simp [a', b', hμf]
  let x : ℝ → X := fun r =>
    ∑ μ ∈ s, Complex.exp ((r : ℂ) * μ) •
      (∑ k ∈ Finset.range (D + 1), (r : ℂ) ^ k • a' μ k)
  let g : ℝ → X := fun r =>
    ∑ μ ∈ s, Complex.exp ((r : ℂ) * μ) •
      (∑ k ∈ Finset.range (D + 1), (r : ℂ) ^ k • b' μ k)
  have hx : ∀ r : ℝ,
      x r = ∑ μ ∈ s, if μ ∈ tfilter then
        Complex.exp ((r : ℂ) * μ) •
          (∑ k ∈ Finset.range (D + 1), (r : ℂ) ^ k • a μ k)
        else 0 := by
    intro r
    simp [x, a']
  have hg : ∀ r : ℝ,
      g r = ∑ μ ∈ s, if μ ∈ tfilter then
        Complex.exp ((r : ℂ) * μ) •
          (∑ k ∈ Finset.range (D + 1), (r : ℂ) ^ k • b μ k)
        else 0 := by
    intro r
    simp [g, b']
  have hcalc := hasDerivAt_sum_exp_mul_sum_pow_smul s D a' t
  have hmatch :
      (∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k •
          (μ • a' μ k + if k < D then ((k + 1 : ℕ) : ℂ) • a' μ (k + 1) else 0))) =
      A (x t) + g t := by
    rw [show A (x t) + g t =
        ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k •
            (A (a' μ k) + b' μ k)) by
          simp only [x, g, map_sum, map_smul, smul_add, Finset.sum_add_distrib]]
    apply Finset.sum_congr rfl
    intro μ hμ
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    have hkD : k ≤ D := by
      have := Finset.mem_range.mp hk
      omega
    rw [hrec' μ hμ k hkD]
  have hcalc' := hcalc.congr_deriv hmatch
  have hfun :
      (fun r : ℝ =>
        ∑ μ ∈ s, if μ ∈ tfilter then
          Complex.exp ((r : ℂ) * μ) •
            (∑ k ∈ Finset.range (D + 1), (r : ℂ) ^ k • a μ k)
          else 0) = x := by
    funext r
    rw [hx r]
  have hx_t := hx t
  have hg_t := hg t
  rw [hfun, ← hx_t, ← hg_t]
  exact hcalc'

/-- The coefficients of an antistable finite exponential-polynomial trajectory
span a controlled-invariant subspace in the output kernel whenever the forcing
coefficients lie in the input image. The output map here is explicitly complex
linear; this lemma does not perform real-to-complex output complexification. -/
theorem exponentialPolynomial_coeff_span_controlledInvariant
    {U Z : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup Z] [Module ℂ Z]
    (s : Finset ℂ) (D : ℕ) (A : X →ₗ[ℂ] X) (B : U →ₗ[ℂ] X)
    (H : X →ₗ[ℂ] Z) (a b : ℂ → ℕ → X)
    (_hfreq : ∀ μ ∈ s, 0 ≤ μ.re)
    (hforce : ∀ μ ∈ s, ∀ k ≤ D, b μ k ∈ LinearMap.range B)
    (hrec : ∀ μ ∈ s, ∀ k ≤ D,
      A (a μ k) + b μ k =
        μ • a μ k + if k < D then ((k + 1 : ℕ) : ℂ) • a μ (k + 1) else 0)
    (houtput : ∀ μ ∈ s, ∀ k ≤ D, H (a μ k) = 0) :
    ∃ S : Submodule ℂ X,
      S ≤ LinearMap.ker H ∧ LinearMap.IsControlledInvariant A B S := by
  classical
  let S : Submodule ℂ X := Submodule.span ℂ
    {x | ∃ μ ∈ s, ∃ k ≤ D, x = a μ k}
  have hSker : S ≤ LinearMap.ker H := by
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨μ, hμ, k, hk, rfl⟩ := hx
    exact houtput μ hμ k hk
  have hSmap : ∀ x ∈ S, A x ∈ S ⊔ LinearMap.range B := by
    intro x hx
    dsimp [S] at hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro x hx
      obtain ⟨μ, hμ, k, hk, rfl⟩ := hx
      have hcoeff := hrec μ hμ k hk
      have ha : a μ k ∈ S := Submodule.subset_span ⟨μ, hμ, k, hk, rfl⟩
      have hshift :
          (μ • a μ k + if k < D then ((k + 1 : ℕ) : ℂ) • a μ (k + 1) else 0) ∈ S := by
        by_cases hlt : k < D
        · have hk' : k + 1 ≤ D := by omega
          have ha' : a μ (k + 1) ∈ S :=
            Submodule.subset_span ⟨μ, hμ, k + 1, hk', rfl⟩
          simpa [hlt] using S.add_mem (S.smul_mem μ ha)
            (S.smul_mem ((k + 1 : ℕ) : ℂ) ha')
        · simpa [hlt] using S.smul_mem μ ha
      have hb : b μ k ∈ S ⊔ LinearMap.range B :=
        Submodule.mem_sup.mpr ⟨0, S.zero_mem, b μ k, hforce μ hμ k hk, by simp⟩
      have hrhs :
          (μ • a μ k +
            if k < D then ((k + 1 : ℕ) : ℂ) • a μ (k + 1) else 0) ∈
              S ⊔ LinearMap.range B :=
        Submodule.mem_sup.mpr ⟨_, hshift, 0, (LinearMap.range B).zero_mem, by simp⟩
      have hAeq : A (a μ k) =
          (μ • a μ k + if k < D then ((k + 1 : ℕ) : ℂ) • a μ (k + 1) else 0) - b μ k := by
        calc
          A (a μ k) = A (a μ k) + b μ k - b μ k := by abel
          _ = (μ • a μ k +
              if k < D then ((k + 1 : ℕ) : ℂ) • a μ (k + 1) else 0) - b μ k := by
            rw [hcoeff]
      rw [hAeq]
      exact Submodule.sub_mem _ hrhs hb
    · simpa using (S ⊔ LinearMap.range B).zero_mem
    · intro x y _ _ hx hy
      simpa only [map_add] using (S ⊔ LinearMap.range B).add_mem hx hy
    · intro c x _ hx
      simpa only [map_smul] using (S ⊔ LinearMap.range B).smul_mem c hx
  refine ⟨S, hSker, ?_⟩
  rw [LinearMap.isControlledInvariant_iff, Submodule.map_le_iff_le_comap]
  exact hSmap

/-- If a finite exponential-polynomial signal takes all its values in a
finite-dimensional complex subspace, then every coefficient in its chosen
representation lies in that subspace. This lets one lift the coefficients of a
range-valued Bohl forcing through its input map. -/
theorem exponentialPolynomial_coefficients_mem_submodule
    [FiniteDimensional ℂ X] (S : Submodule ℂ X) (s : Finset ℂ) (D : ℕ)
    (a : ℂ → ℕ → X)
    (hval : ∀ t : ℝ, (∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
      (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)) ∈ S) :
    ∀ μ ∈ s, ∀ k ≤ D, a μ k ∈ S := by
  classical
  letI : IsClosed (S : Set X) := S.closed_of_finiteDimensional
  let q : X →ₗ[ℂ] X ⧸ S := S.mkQ
  have hqzero : ∀ t : ℝ,
      ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • q (a μ k)) = 0 := by
    intro t
    have hqt : q (∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)) = 0 := by
      change (Submodule.Quotient.mk _) = 0
      exact (Submodule.Quotient.mk_eq_zero S).2 (hval t)
    simpa only [map_sum, map_smul] using hqt
  have hcoeff := exponentialPolynomial_coefficients_eq_zero_of_eq_zero
    s D (fun μ k => q (a μ k)) hqzero
  intro μ hμ k hk
  exact (Submodule.Quotient.mk_eq_zero S).1 (by
    simpa only [q, Submodule.mkQ_apply] using hcoeff μ hμ k hk)

/-- Every Bohl mode is an exponential polynomial. -/
theorem IsBohlMode.isExponentialPolynomial {f : ℝ → X} (hf : IsBohlMode f) :
    IsExponentialPolynomial f := by
  obtain ⟨μ, k, v, hf⟩ := hf
  refine ⟨{μ}, k, fun ν j => if ν = μ then (if j = k then v else 0) else 0, fun t => ?_⟩
  rw [hf t, Finset.sum_singleton]
  rw [Finset.sum_eq_single k]
  · simp
  · intro j hj hjk
    simp [hjk]
  · intro hk
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self k)) hk

theorem IsExponentialPolynomial.zero : IsExponentialPolynomial (0 : ℝ → X) :=
  ⟨∅, 0, fun _ _ => 0, fun t => by simp⟩

@[simp]
theorem isExponentialPolynomial_zero : IsExponentialPolynomial (0 : ℝ → X) :=
  IsExponentialPolynomial.zero

/-- Auxiliary range comparison: a polynomial of degree `≤ D` padded to degree
`≤ max D E` agrees with the original finite sum. -/
theorem sum_range_smul_ite (D E : ℕ) (c : ℂ) (a : ℕ → X) :
    (∑ k ∈ Finset.range (max D E + 1), c ^ k • (if k ≤ D then a k else 0)) =
      ∑ k ∈ Finset.range (D + 1), c ^ k • a k := by
  symm
  have h : (∑ k ∈ Finset.range (D + 1), c ^ k • a k) =
      ∑ k ∈ Finset.range (D + 1), c ^ k • (if k ≤ D then a k else 0) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [ite_eq_left (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
  rw [h]
  apply Finset.sum_subset
  · intro k hk
    rw [Finset.mem_range] at hk ⊢
    omega
  · intro k hk hknot
    rw [Finset.mem_range, not_lt] at hknot
    rw [ite_eq_right (by omega), smul_zero]

theorem sum_range_smul_ite' (D E : ℕ) (c : ℂ) (a : ℕ → X) :
    (∑ k ∈ Finset.range (max D E + 1), c ^ k • (if k ≤ E then a k else 0)) =
      ∑ k ∈ Finset.range (E + 1), c ^ k • a k := by
  rw [max_comm D E]
  exact sum_range_smul_ite E D c a

theorem IsExponentialPolynomial.add {f g : ℝ → X}
    (hf : IsExponentialPolynomial f) (hg : IsExponentialPolynomial g) :
    IsExponentialPolynomial (f + g) := by
  obtain ⟨s, D, a, hf⟩ := hf
  obtain ⟨s', E, b, hg⟩ := hg
  refine ⟨s ∪ s', max D E, fun μ k =>
    (if μ ∈ s then (if k ≤ D then a μ k else 0) else 0) +
      (if μ ∈ s' then (if k ≤ E then b μ k else 0) else 0), fun t => ?_⟩
  rw [Pi.add_apply, hf t, hg t]
  have hsplit :
      (∑ μ ∈ s ∪ s', Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (max D E + 1), (t : ℂ) ^ k •
            ((if μ ∈ s then (if k ≤ D then a μ k else 0) else 0) +
              (if μ ∈ s' then (if k ≤ E then b μ k else 0) else 0)))) =
      (∑ μ ∈ s ∪ s', Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (max D E + 1), (t : ℂ) ^ k •
            (if μ ∈ s then (if k ≤ D then a μ k else 0) else 0))) +
      (∑ μ ∈ s ∪ s', Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (max D E + 1), (t : ℂ) ^ k •
            (if μ ∈ s' then (if k ≤ E then b μ k else 0) else 0))) := by
    simp only [smul_add, Finset.sum_add_distrib]
  rw [hsplit]
  congr 1
  · -- the `s` part
    have h1 : (∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)) =
        ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (max D E + 1), (t : ℂ) ^ k •
            (if μ ∈ s then (if k ≤ D then a μ k else 0) else 0)) := by
      apply Finset.sum_congr rfl
      intro μ hμ
      congr 1
      simp only [ite_eq_left hμ]
      exact (sum_range_smul_ite D E ((t : ℂ)) (a μ)).symm
    rw [h1]
    exact Finset.sum_subset Finset.subset_union_left
      (fun μ _ hμnot => by simp [hμnot])
  · -- the `s'` part
    have h1 : (∑ μ ∈ s', Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (E + 1), (t : ℂ) ^ k • b μ k)) =
        ∑ μ ∈ s', Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (max D E + 1), (t : ℂ) ^ k •
            (if μ ∈ s' then (if k ≤ E then b μ k else 0) else 0)) := by
      apply Finset.sum_congr rfl
      intro μ hμ
      congr 1
      simp only [ite_eq_left hμ]
      exact (sum_range_smul_ite' D E ((t : ℂ)) (b μ)).symm
    rw [h1]
    exact Finset.sum_subset Finset.subset_union_right
      (fun μ _ hμnot => by simp [hμnot])

/-- **Align two finite exponential-polynomial representations.** Any pair of
finite Bohl signals can be represented on the same frequency support and with
the same polynomial degree bound. This is useful when comparing the ODE
coefficients of a state trajectory and its forcing. -/
theorem IsExponentialPolynomial.exists_common_representation {f g : ℝ → X}
    (hf : IsExponentialPolynomial f) (hg : IsExponentialPolynomial g) :
    ∃ (s : Finset ℂ) (D : ℕ) (a b : ℂ → ℕ → X),
      (∀ t, f t = ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)) ∧
      (∀ t, g t = ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • b μ k)) := by
  obtain ⟨s, D, a, hf⟩ := hf
  obtain ⟨s', E, b, hg⟩ := hg
  refine ⟨s ∪ s', max D E,
    (fun μ k => if μ ∈ s then (if k ≤ D then a μ k else 0) else 0),
    (fun μ k => if μ ∈ s' then (if k ≤ E then b μ k else 0) else 0), ?_, ?_⟩
  · intro t
    rw [hf t]
    have h1 : (∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)) =
        ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (max D E + 1), (t : ℂ) ^ k •
            (if μ ∈ s then (if k ≤ D then a μ k else 0) else 0)) := by
      apply Finset.sum_congr rfl
      intro μ hμ
      congr 1
      simp only [ite_eq_left hμ]
      exact (sum_range_smul_ite D E ((t : ℂ)) (a μ)).symm
    rw [h1]
    exact Finset.sum_subset Finset.subset_union_left
      (fun μ _ hμnot => by simp [hμnot])
  · intro t
    rw [hg t]
    have h1 : (∑ μ ∈ s', Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (E + 1), (t : ℂ) ^ k • b μ k)) =
        ∑ μ ∈ s', Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (max D E + 1), (t : ℂ) ^ k •
            (if μ ∈ s' then (if k ≤ E then b μ k else 0) else 0)) := by
      apply Finset.sum_congr rfl
      intro μ hμ
      congr 1
      simp only [ite_eq_left hμ]
      exact (sum_range_smul_ite' D E ((t : ℂ)) (b μ)).symm
    rw [h1]
    exact Finset.sum_subset Finset.subset_union_right
      (fun μ _ hμnot => by simp [hμnot])

/-- **Coefficient recurrence for an ODE with finite-Bohl state and forcing.**
After aligning the two finite representations, the pointwise equation
`f' = A f + r` yields its coefficientwise polynomial-exponential recurrence.
The common-support result is important: independent representations of `f` and
`r` need not initially use the same frequencies or degree bound. -/
theorem IsExponentialPolynomial.exists_ode_coefficient_recurrence
    {f r : ℝ → X} (hf : IsExponentialPolynomial f) (hr : IsExponentialPolynomial r)
    (A : X →ₗ[ℂ] X)
    (hode : ∀ t, HasDerivAt f (A (f t) + r t) t) :
    ∃ (s : Finset ℂ) (D : ℕ) (a b : ℂ → ℕ → X),
      (∀ t, f t = ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)) ∧
      (∀ t, r t = ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • b μ k)) ∧
      (∀ μ ∈ s, ∀ k ≤ D,
        A (a μ k) + b μ k =
          μ • a μ k + if k < D then ((k + 1 : ℕ) : ℂ) • a μ (k + 1) else 0) := by
  obtain ⟨s, D, a, b, hfrepr, hrrepr⟩ := hf.exists_common_representation hr
  let F : ℝ → X := fun t => ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
    (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)
  let G : ℝ → X := fun t => ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
    (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • b μ k)
  have hF : f = F := funext fun t => hfrepr t
  have hG : r = G := funext fun t => hrrepr t
  have hode' : ∀ t, HasDerivAt F (A (F t) + G t) t := by
    intro t
    simpa [F, G, hF, hG] using hode t
  refine ⟨s, D, a, b, hfrepr, hrrepr, ?_⟩
  exact exponentialPolynomial_ode_coefficient_recurrence s D A a b hode'

theorem IsExponentialPolynomial.smul (c : ℂ) {f : ℝ → X}
    (hf : IsExponentialPolynomial f) : IsExponentialPolynomial (c • f) := by
  obtain ⟨s, D, a, hf⟩ := hf
  refine ⟨s, D, fun μ k => c • a μ k, fun t => ?_⟩
  rw [Pi.smul_apply, hf t, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [smul_comm c (Complex.exp ((t : ℂ) * μ))]
  congr 1
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [smul_comm]

theorem IsExponentialPolynomial.neg {f : ℝ → X} (hf : IsExponentialPolynomial f) :
    IsExponentialPolynomial (-f) := by
  have h := hf.smul (-1)
  have hfun : ((-1 : ℂ) • f) = -f := by funext t; simp
  rwa [hfun] at h

theorem IsExponentialPolynomial.sub {f g : ℝ → X}
    (hf : IsExponentialPolynomial f) (hg : IsExponentialPolynomial g) :
    IsExponentialPolynomial (f - g) := by
  have h := hf.add hg.neg
  simpa [sub_eq_add_neg] using h

/-- The **antistable** finite-support spectral class: an exponential polynomial
all of whose frequencies lie in the closed right half-plane. This is the vector
counterpart of the scalar `LinearSystem.IsAntistableExponentialPolynomial`. -/
def IsAntistableBohlSignal (f : ℝ → X) : Prop :=
  ∃ (s : Finset ℂ) (D : ℕ) (a : ℂ → ℕ → X),
    (∀ μ ∈ s, 0 ≤ μ.re) ∧
      ∀ t, f t = ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)

theorem IsAntistableBohlSignal.isExponentialPolynomial {f : ℝ → X}
    (hf : IsAntistableBohlSignal f) : IsExponentialPolynomial f := by
  obtain ⟨s, D, a, -, hf⟩ := hf
  exact ⟨s, D, a, hf⟩

/-- **Polynomial-exponential vanishing for the class.** A finite sum of
vector-valued polynomial terms times exponential characters with nonnegative
real parts that tends to `0` at `+∞` is identically zero: all polynomial
coefficients at every (antistable) frequency vanish. This transports the accepted
`LinearMap.tendsto_zero_of_sum_exp_polynomial` to the named finite-support
finite-dimensional class. -/
theorem tendsto_zero_of_isAntistableBohlSignal {f : ℝ → X}
    (hf : IsAntistableBohlSignal f) (h : Filter.Tendsto f Filter.atTop (nhds 0)) : f = 0 := by
  obtain ⟨s, D, a, hμs, hf⟩ := hf
  classical
  have hinj : ∀ i : {μ // μ ∈ s}, ∀ j : {μ // μ ∈ s}, (i : ℂ) = (j : ℂ) → i = j :=
    fun i j hij => Subtype.ext hij
  have hsum : (fun t : ℝ => f t) = fun t : ℝ =>
      ∑ μ : {μ // μ ∈ s}, Complex.exp ((t : ℂ) * (μ : ℂ)) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a (μ : ℂ) k) := by
    funext t
    rw [hf t]
    exact Finset.sum_subtype s (fun x => Iff.rfl) (fun μ =>
      Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k))
  have h' : Filter.Tendsto (fun t : ℝ =>
      ∑ μ : {μ // μ ∈ s}, Complex.exp ((t : ℂ) * (μ : ℂ)) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a (μ : ℂ) k)) Filter.atTop (nhds 0) := by
    rw [← hsum]; exact h
  have hzall : ∀ i ∈ (Finset.univ : Finset {μ // μ ∈ s}), ∀ k ≤ D, a (i : ℂ) k = 0 :=
    LinearMap.tendsto_zero_of_sum_exp_polynomial (Finset.univ : Finset {μ // μ ∈ s})
      (fun μ => (μ : ℂ)) (fun μ _ => hμs μ μ.2)
      (fun i _ j _ hij => hinj i j hij) D (fun μ k => a (μ : ℂ) k) h'
  have hz : ∀ μ : {μ // μ ∈ s}, ∀ k ≤ D, a (μ : ℂ) k = 0 :=
    fun μ k hk => hzall μ (Finset.mem_univ μ) k hk
  funext t
  rw [hf t]
  apply Finset.sum_eq_zero
  intro μ hμ
  have hinner : (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [hz ⟨μ, hμ⟩ k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)), smul_zero]
  rw [hinner, smul_zero]

/-- **Complex-conjugate transport.** Complex conjugation sends the finite-support
spectral class to itself: the conjugate function has the conjugate frequencies and
conjugate coefficients. For a real-valued Bohl signal this is the operation that
pairs the generalized eigenmodes at `μ` and `star μ`. -/
theorem IsExponentialPolynomial.conj {f : ℝ → ℂ} (hf : IsExponentialPolynomial f) :
    IsExponentialPolynomial (fun t => star (f t)) := by
  obtain ⟨s, D, a, hf⟩ := hf
  refine ⟨s.image star, D, fun ν k => star (a (star ν) k), fun t => ?_⟩
  rw [show (fun t => star (f t)) t = star (f t) from rfl, hf t, star_sum]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro μ hμ
    rw [star_smul, star_sum]
    congr 1
    · simp only [Complex.star_def]
      rw [← Complex.exp_conj]
      congr 1
      simp
    · apply Finset.sum_congr rfl
      intro k hk
      rw [star_smul]
      congr 1
      · simp only [Complex.star_def, map_pow, Complex.conj_ofReal]
      · simp only [star_star]
  · intro μ _ ν _ hμν
    exact star_injective hμν

/-- **Antilinear transport of the finite Bohl class.** A real-linear endomorphism
`M` that is anti-complex-linear, `M (c • x) = star c • M x`, sends a finite
exponential polynomial to a finite exponential polynomial: it conjugates the
frequencies and maps the coefficients. This is the anti-linear half of the
real-linear closure of the Bohl class; together with `IsExponentialPolynomial.map`
it reduces the preservation of the class under an arbitrary real-linear map to the
complex-linear/anti-linear decomposition of that map. -/
theorem IsExponentialPolynomial.map_antilinear (M : X →ₗ[ℝ] X)
    (hM : ∀ (c : ℂ) (x : X), M (c • x) = (star c) • M x)
    {f : ℝ → X} (hf : IsExponentialPolynomial f) :
    IsExponentialPolynomial (fun t ↦ M (f t)) := by
  obtain ⟨s, D, a, hf⟩ := hf
  refine ⟨s.image star, D, fun ν k => M (a (star ν) k), fun t => ?_⟩
  rw [show (fun t => M (f t)) t = M (f t) from rfl, hf t, map_sum]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro μ hμ
    rw [hM, map_sum]
    congr 1
    · simp only [Complex.star_def]
      rw [← Complex.exp_conj]
      congr 1
      simp
    · apply Finset.sum_congr rfl
      intro k hk
      rw [hM]
      congr 1
      · simp only [Complex.star_def, map_pow, Complex.conj_ofReal]
      · simp only [star_star]
  · intro μ _ ν _ hμν
    exact star_injective hμν

/-! ### Polynomial-exponential primitives: the scalar antiderivative recursion

The variation-of-constants closure of the Bohl class rests on the scalar
observation that `t ↦ e^{t μ} t ^ k` has an antiderivative which is again a
polynomial times `e^{t μ}` when `μ ≠ 0`, and a polynomial of one degree higher
when `μ = 0` (the resonant secular term `t ^ (k+1)`). The polynomial family
`primPoly μ k` below satisfies the recursion

`(primPoly μ k).derivative + C μ * primPoly μ k = X ^ k`,

so `t ↦ e^{t μ} (primPoly μ k).eval t` is a primitive of `t ↦ e^{t μ} t ^ k`.
The construction is the standard descending coefficient recurrence
`q_{k+1} = μ⁻¹ (X^{k+1} - (k+1) q_k)` for `μ ≠ 0`, and the plain monomial
antiderivative for `μ = 0`.

Source: Trentelman–Stoorvogel–Hautus, Chapter 2 (Bohl functions and their
antiderivatives); the recursive formula is the scalar case of the
resolvent/Jordan-chain antiderivative used in Section 2.6. -/

open Polynomial

/-- The scalar polynomial `q` with `q' + μ q = X ^ k` for `μ ≠ 0`, defined by the
recursion `q₀ = C μ⁻¹`, `q_{k+1} = C μ⁻¹ * (X^(k+1) - C (k+1) * q_k)`. -/
noncomputable def monoPrim (μ : ℂ) : ℕ → ℂ[X]
  | 0 => Polynomial.C μ⁻¹
  | (k+1) => Polynomial.C μ⁻¹ *
      (Polynomial.X ^ (k+1) - Polynomial.C ((k+1 : ℕ) : ℂ) * monoPrim μ k)

/-- **Scalar antiderivative recursion (non-resonant case).** For `μ ≠ 0` the
polynomial `monoPrim μ k` satisfies `q' + μ q = X ^ k`, so `e^{t μ} q(t)` is a
primitive of `e^{t μ} t ^ k`. -/
theorem derivative_monoPrim (μ : ℂ) (hμ : μ ≠ 0) (k : ℕ) :
    (monoPrim μ k).derivative + Polynomial.C μ * monoPrim μ k = Polynomial.X ^ k := by
  have hμC : Polynomial.C μ * Polynomial.C μ⁻¹ = (1 : ℂ[X]) := by
    rw [← Polynomial.C_mul, mul_inv_cancel₀ hμ, Polynomial.C_1]
  induction k with
  | zero =>
    rw [monoPrim, Polynomial.derivative_C, zero_add]
    exact hμC
  | succ k ih =>
    have hd : (monoPrim μ k).derivative =
        Polynomial.X ^ k - Polynomial.C μ * monoPrim μ k := by
      rw [← ih]; abel
    rw [monoPrim, Polynomial.derivative_mul, Polynomial.derivative_C, zero_mul, zero_add]
    rw [Polynomial.derivative_sub, Polynomial.derivative_C_mul, hd]
    rw [Polynomial.derivative_pow, Polynomial.derivative_X, mul_one]
    rw [show k + 1 - 1 = k by omega]
    ring_nf
    rw [show Polynomial.C μ⁻¹ * X * X ^ k * Polynomial.C μ =
        (Polynomial.C μ⁻¹ * Polynomial.C μ) * (X * X^k) by ring]
    rw [← Polynomial.C_mul, inv_mul_cancel₀ hμ, Polynomial.C_1, one_mul]

/-- The scalar recursion does not increase the degree beyond `k`. -/
theorem natDegree_monoPrim (μ : ℂ) (k : ℕ) : (monoPrim μ k).natDegree ≤ k := by
  induction k with
  | zero => simp [monoPrim]
  | succ k ih =>
    rw [monoPrim]
    calc (Polynomial.C μ⁻¹ *
          (Polynomial.X ^ (k + 1) - Polynomial.C ((k + 1 : ℕ) : ℂ) * monoPrim μ k)).natDegree
        ≤ (Polynomial.X ^ (k + 1) - Polynomial.C ((k + 1 : ℕ) : ℂ) * monoPrim μ k).natDegree :=
          Polynomial.natDegree_C_mul_le _ _
      _ ≤ max (Polynomial.X ^ (k + 1) : ℂ[X]).natDegree
            (Polynomial.C ((k + 1 : ℕ) : ℂ) * monoPrim μ k).natDegree :=
          Polynomial.natDegree_sub_le _ _
      _ ≤ max (k + 1) k := by
          apply max_le_max
          · rw [Polynomial.natDegree_X_pow (k+1)]
          · calc (Polynomial.C ((k + 1 : ℕ) : ℂ) * monoPrim μ k).natDegree
                ≤ (monoPrim μ k).natDegree := Polynomial.natDegree_C_mul_le _ _
              _ ≤ k := ih
      _ = k + 1 := max_eq_left (Nat.le_succ k)

/-- The unified scalar primitive: the non-resonant `monoPrim` for `μ ≠ 0` and the
secular monomial antiderivative `X ^ (k+1) / (k+1)` for the resonant frequency
`μ = 0`. It satisfies `q' + μ q = X ^ k` for **every** `μ`. -/
noncomputable def primPoly (μ : ℂ) (k : ℕ) : ℂ[X] :=
  if μ = 0 then Polynomial.C (((k + 1 : ℕ) : ℂ))⁻¹ * Polynomial.X ^ (k + 1)
  else monoPrim μ k

/-- **Scalar antiderivative recursion, resonant and non-resonant.** For every
complex frequency `μ`, `(primPoly μ k).derivative + C μ * primPoly μ k = X ^ k`.
The `μ = 0` case is exactly the secular degree increase of the antiderivative of
`t ^ k`. -/
theorem derivative_primPoly (μ : ℂ) (k : ℕ) :
    (primPoly μ k).derivative + Polynomial.C μ * primPoly μ k = Polynomial.X ^ k := by
  by_cases hμ : μ = 0
  · subst hμ
    rw [primPoly, ite_eq_left rfl, Polynomial.derivative_C_mul, Polynomial.derivative_pow,
      Polynomial.derivative_X, mul_one]
    rw [show k + 1 - 1 = k by omega, Polynomial.C_0, zero_mul, add_zero]
    rw [← mul_assoc, ← Polynomial.C_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (by omega : k + 1 ≠ 0)), Polynomial.C_1, one_mul]
  · rw [primPoly, ite_eq_right hμ]
    exact derivative_monoPrim μ hμ k

/-- Degree bound for the unified scalar primitive: at most `k+1` (one secular
degree more than `X ^ k`). -/
theorem natDegree_primPoly (μ : ℂ) (k : ℕ) : (primPoly μ k).natDegree ≤ k + 1 := by
  by_cases hμ : μ = 0
  · subst hμ
    rw [primPoly, ite_eq_left rfl]
    calc (Polynomial.C (((k + 1 : ℕ) : ℂ))⁻¹ * Polynomial.X ^ (k + 1)).natDegree
        ≤ (Polynomial.X ^ (k + 1) : ℂ[X]).natDegree := Polynomial.natDegree_C_mul_le _ _
      _ = k + 1 := Polynomial.natDegree_X_pow (k+1)
  · rw [primPoly, ite_eq_right hμ]
    exact le_trans (natDegree_monoPrim μ k) (Nat.le_succ k)

/-- **Analytic scalar antiderivative.** The function
`t ↦ e^{t μ} (primPoly μ k).eval t` has derivative `t ↦ e^{t μ} t ^ k`, uniformly
in the resonant and non-resonant cases. -/
theorem hasDerivAt_exp_mul_primPoly (μ : ℂ) (k : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * μ) * (primPoly μ k).eval (s : ℂ))
      (Complex.exp ((t : ℂ) * μ) * (t : ℂ) ^ k) t := by
  have h2 : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := Complex.ofRealCLM.hasDerivAt
  have hexp : HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * μ))
      (Complex.exp ((t : ℂ) * μ) * μ) t := by
    have h1 : HasDerivAt (fun z : ℂ => z * μ) μ (t : ℂ) := by
      simpa using (hasDerivAt_id (t : ℂ)).mul_const μ
    have h3 := (Complex.hasDerivAt_exp ((t : ℂ) * μ)).comp t (h1.comp t h2)
    simpa [Function.comp_def] using h3
  have hq : HasDerivAt (fun s : ℝ => (primPoly μ k).eval (s : ℂ))
      ((primPoly μ k).derivative.eval (t : ℂ)) t := by
    have h3 := ((primPoly μ k).hasDerivAt (t : ℂ)).comp t h2
    simpa [Function.comp_def] using h3
  refine (hexp.mul hq).congr_deriv ?_
  have hp : (primPoly μ k).derivative.eval (t : ℂ) + μ * (primPoly μ k).eval (t : ℂ) =
      (t : ℂ) ^ k := by
    have hh := congrArg (fun p : ℂ[X] => p.eval (t : ℂ)) (derivative_primPoly μ k)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_pow] at hh
    linear_combination hh
  linear_combination Complex.exp ((t : ℂ) * μ) * hp

/-- Coefficient shift that turns `t ^ k • a k` into `t ^ (k+1) • a k`. -/
def shiftCoeff (a : ℂ → ℕ → X) (μ : ℂ) : ℕ → X
  | 0 => 0
  | (j + 1) => a μ j

/-- The finite-support exponential-polynomial class is closed under multiplication by `t`. -/
theorem IsExponentialPolynomial.mul_t {f : ℝ → X} (hf : IsExponentialPolynomial f) :
    IsExponentialPolynomial (fun t => (t : ℂ) • f t) := by
  obtain ⟨s, D, a, hf⟩ := hf
  refine ⟨s, D + 1, fun μ k => shiftCoeff a μ k, fun t => ?_⟩
  change (t : ℂ) • f t = _
  rw [hf t, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [smul_comm]
  congr 1
  rw [Finset.smul_sum]
  conv_rhs => rw [Finset.sum_range_succ']
  simp only [shiftCoeff, pow_zero, one_smul, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  rw [smul_smul, pow_succ, mul_comm]

/-- The class is closed under multiplication by a single exponential character. -/
theorem IsExponentialPolynomial.mul_exp (ν : ℂ) {f : ℝ → X}
    (hf : IsExponentialPolynomial f) :
    IsExponentialPolynomial (fun t => Complex.exp ((t : ℂ) * ν) • f t) := by
  obtain ⟨s, D, a, hf⟩ := hf
  refine ⟨s.image (fun μ => μ + ν), D, fun δ k => a (δ - ν) k, fun t => ?_⟩
  change Complex.exp ((t : ℂ) * ν) • f t = _
  rw [hf t, Finset.smul_sum]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro μ hμ
    rw [smul_smul]
    congr 1
    · rw [← Complex.exp_add]
      congr 1
      ring
    · simp only [add_sub_cancel_right]
  · intro μ _ δ _ h
    exact add_right_cancel h

/-- **Analytic antiderivative of a single Bohl mode.** The derivative of
`t ↦ e^{t μ} Σ_k (primPoly μ k).eval t • a k` is `t ↦ e^{t μ} Σ_k t ^ k • a k`:
the scalar recursion is applied coefficientwise to the vector coefficients. -/
lemma hasDerivAt_exp_mul_primMode (a : ℂ → ℕ → X) (D : ℕ) (μ : ℂ) (t : ℝ) :
    HasDerivAt (fun r : ℝ => Complex.exp ((r : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (primPoly μ k).eval (r : ℂ) • a μ k))
      (Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)) t := by
  have hF : HasDerivAt (fun r : ℝ => Complex.exp ((r : ℂ) * μ))
      (Complex.exp ((t : ℂ) * μ) * μ) t := by
    have h2 : HasDerivAt (fun r : ℝ => (r : ℂ)) (1 : ℂ) t := Complex.ofRealCLM.hasDerivAt
    have h1 : HasDerivAt (fun z : ℂ => z * μ) μ (t : ℂ) := by
      simpa using (hasDerivAt_id (t : ℂ)).mul_const μ
    have h3 := (Complex.hasDerivAt_exp ((t : ℂ) * μ)).comp t (h1.comp t h2)
    simpa [Function.comp_def] using h3
  have hQ : HasDerivAt (fun r : ℝ =>
        ∑ k ∈ Finset.range (D + 1), (primPoly μ k).eval (r : ℂ) • a μ k)
      (∑ k ∈ Finset.range (D + 1), (primPoly μ k).derivative.eval (t : ℂ) • a μ k) t := by
    have h := HasDerivAt.sum (u := Finset.range (D + 1))
      (A := fun k (r : ℝ) => (primPoly μ k).eval (r : ℂ) • a μ k)
      (A' := fun k => (primPoly μ k).derivative.eval (t : ℂ) • a μ k)
      (fun k hk => by
        have h2 : HasDerivAt (fun r : ℝ => (r : ℂ)) (1 : ℂ) t := Complex.ofRealCLM.hasDerivAt
        have h3 := ((primPoly μ k).hasDerivAt (t : ℂ)).comp t h2
        have h4 : HasDerivAt (fun r : ℝ => (primPoly μ k).eval (r : ℂ))
            ((primPoly μ k).derivative.eval (t : ℂ)) t := by
          simpa [Function.comp_def] using h3
        exact h4.smul_const (a μ k))
    convert h using 1
    ext r
    rw [Finset.sum_apply]
  refine (hF.smul hQ).congr_deriv ?_
  have hpq : (∑ k ∈ Finset.range (D + 1), (primPoly μ k).derivative.eval (t : ℂ) • a μ k) +
        μ • (∑ k ∈ Finset.range (D + 1), (primPoly μ k).eval (t : ℂ) • a μ k) =
      ∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [smul_smul, ← add_smul]
    congr 1
    have hh := congrArg (fun p : ℂ[X] => p.eval (t : ℂ)) (derivative_primPoly μ k)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
      Polynomial.eval_pow] at hh
    linear_combination hh
  rw [← smul_smul, ← smul_add, hpq]

/-- **Antiderivative closure of the finite-support exponential-polynomial class.**
Every finite Bohl signal has a primitive that is again a finite Bohl signal, with
explicit coefficients: the primitive of `t ↦ e^{t μ} Σ_k t ^ k • a μ k` is
`t ↦ e^{t μ} Σ_k (primPoly μ k).eval t • a μ k`, and the resonant frequency
`μ = 0` raises the polynomial degree bound from `D` to `D+1` (the secular term).
This is the scalar recursion of `derivative_primPoly` applied coefficientwise and
summed over the finite frequency set. -/
theorem IsExponentialPolynomial.hasPrimitive {f : ℝ → X} (hf : IsExponentialPolynomial f) :
    ∃ g : ℝ → X, IsExponentialPolynomial g ∧ ∀ t, HasDerivAt g (f t) t := by
  obtain ⟨s, D, a, hf⟩ := hf
  refine ⟨fun t => ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
      (∑ k ∈ Finset.range (D + 1), (primPoly μ k).eval (t : ℂ) • a μ k), ?_, ?_⟩
  · refine ⟨s, D + 1, fun μ j => ∑ k ∈ Finset.range (D + 1),
        (primPoly μ k).coeff j • a μ k, fun t => ?_⟩
    apply Finset.sum_congr rfl
    intro μ hμ
    congr 1
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    rw [Polynomial.eval_eq_sum_range' (n := D + 2) (by
      have hk' := Finset.mem_range.mp hk
      have := natDegree_primPoly μ k
      omega)]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · intro t
    have hsum : HasDerivAt (fun r : ℝ => ∑ μ ∈ s,
        Complex.exp ((r : ℂ) * μ) •
          (∑ k ∈ Finset.range (D + 1), (primPoly μ k).eval (r : ℂ) • a μ k))
        (∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)) t := by
      have h := HasDerivAt.sum (u := s)
        (A := fun μ (r : ℝ) => Complex.exp ((r : ℂ) * μ) •
          (∑ k ∈ Finset.range (D + 1), (primPoly μ k).eval (r : ℂ) • a μ k))
        (A' := fun μ => Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k))
        (fun μ hμ => hasDerivAt_exp_mul_primMode a D μ t)
      convert h using 1
      ext r
      rw [Finset.sum_apply]
    rw [hf t]
    exact hsum

/-- **Finite sums of Bohl signals are Bohl signals.** The finite-support spectral
class is closed under finite sums; this packages the binary closure `add` for the
finite sums that arise when an exponential-polynomial signal is expanded in a
basis of generalized eigenmodes. -/
theorem IsExponentialPolynomial.finset_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → X}
    (hf : ∀ i ∈ s, IsExponentialPolynomial (f i)) :
    IsExponentialPolynomial (fun t => ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction with
  | empty =>
    have hzero : (fun t : ℝ => ∑ i ∈ (∅ : Finset ι), f i t) = (0 : ℝ → X) := by
      funext t; simp
    rw [hzero]
    exact isExponentialPolynomial_zero
  | insert a s ha ih =>
    have hsplit : (fun t => ∑ i ∈ insert a s, f i t) =
        fun t => f a t + ∑ i ∈ s, f i t := by
      funext t
      rw [Finset.sum_insert ha]
    rw [hsplit]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

/-- The class is closed under multiplication by a natural power of `t`. -/
theorem IsExponentialPolynomial.mul_pow_t {f : ℝ → X} (hf : IsExponentialPolynomial f)
    (k : ℕ) : IsExponentialPolynomial (fun t => (t : ℂ) ^ k • f t) := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    have h := ih.mul_t
    convert h using 1
    ext t
    rw [smul_smul, mul_comm, ← pow_succ]

/-- **The autonomous flow of a finite-dimensional operator is an exponential
polynomial.** For every `y`, the orbit `t ↦ exp (t • A) y` is a finite sum of
Bohl modes: the primary (generalized-eigenspace) decomposition writes `y` as a
finite sum of generalized eigenvectors, and the Jordan-chain identity
`LinearMap.exp_apply_eq_exp_mul_sum` expands each orbit as `e^{t μ}` times a
vector polynomial. This is the finite-dimensional "generalized-eigenmode secular
term" input to the variation-of-constants closure. -/
theorem expFlow_isExponentialPolynomial [FiniteDimensional ℂ X] (f : X →ₗ[ℂ] X) (y : X) :
    IsExponentialPolynomial (fun t : ℝ => NormedSpace.exp (t • f.toContinuousLinearMap) y) := by
  classical
  have hy : y ∈ ⨆ μ : ℂ, Module.End.maxGenEigenspace f μ := by
    rw [Module.End.iSup_maxGenEigenspace_eq_top]; trivial
  obtain ⟨s, hs⟩ := (Submodule.mem_iSup_iff_exists_finset
    (p := fun μ : ℂ => Module.End.maxGenEigenspace f μ)).mp hy
  obtain ⟨z, hz⟩ := (Submodule.mem_iSup_finset_iff_exists_sum
    (fun μ : ℂ => Module.End.maxGenEigenspace f μ) y).mp hs
  have hkf_exists : ∀ μ : ℂ, ∃ k, ((f - μ • (1 : X →ₗ[ℂ] X)) ^ k) ((z μ : X)) = 0 :=
    fun μ => (Module.End.mem_maxGenEigenspace f μ (z μ)).mp (z μ).2
  choose kf hkf using hkf_exists
  refine ⟨s, s.sup kf, fun μ j => ((j.factorial : ℂ)⁻¹) •
      (((f - μ • (1 : X →ₗ[ℂ] X)) ^ j) ((z μ : X))), fun t => ?_⟩
  change NormedSpace.exp (t • f.toContinuousLinearMap) y = _
  rw [← hz, map_sum]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [LinearMap.exp_apply_eq_exp_mul_sum f μ (hkf μ) t]
  congr 1
  rw [Finset.sum_subset (s₁ := Finset.range (kf μ)) (s₂ := Finset.range (s.sup kf + 1))
      (Finset.range_subset_range.mpr (by have := Finset.le_sup (f := kf) hμ; omega)) ?_]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [smul_smul, smul_smul, mul_comm]
  · intro j hj hjnot
    rw [Finset.mem_range, not_lt] at hjnot
    have hNj0 : (((f - μ • (1 : X →ₗ[ℂ] X)) ^ j) ((z μ : X))) = 0 := by
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hjnot
      rw [hd, show kf μ + d = d + kf μ by omega, pow_add, Module.End.mul_apply, hkf μ, map_zero]
    simp [hNj0]

/-- **The autonomous flow acts on the Bohl class.** If `G` is a finite Bohl
signal then so is `t ↦ exp (t • A) (G t)`. The proof expands `G` in its
spectral modes, uses `map_sum`/`map_smul` to move the flow onto each polynomial
coefficient, and reassembles the result from `expFlow_isExponentialPolynomial`,
`mul_pow_t` and `mul_exp`. This is the operator half of the resonant
variation-of-constants closure: applying the flow to a forcing mode produces the
secular generalized-eigenmode terms. -/
theorem flow_mul_isExponentialPolynomial [FiniteDimensional ℂ X] (f : X →ₗ[ℂ] X)
    {G : ℝ → X} (hG : IsExponentialPolynomial G) :
    IsExponentialPolynomial (fun t : ℝ =>
      NormedSpace.exp (t • f.toContinuousLinearMap) (G t)) := by
  obtain ⟨s, D, b, hG⟩ := hG
  have hfun : (fun t : ℝ => NormedSpace.exp (t • f.toContinuousLinearMap) (G t)) =
      fun t : ℝ => ∑ μ ∈ s, Complex.exp ((t:ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t:ℂ)^k •
          NormedSpace.exp (t • f.toContinuousLinearMap) (b μ k)) := by
    funext t
    rw [hG t, map_sum]
    apply Finset.sum_congr rfl
    intro μ hμ
    rw [map_smul]
    congr 1
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_smul]
  rw [hfun]
  apply IsExponentialPolynomial.finset_sum
  intro μ hμ
  apply IsExponentialPolynomial.mul_exp
  apply IsExponentialPolynomial.finset_sum
  intro k hk
  exact (expFlow_isExponentialPolynomial f (b μ k)).mul_pow_t k

/-! ### The Bohl ODE response: product rule and particular solution

This section completes the next Bohl foundation step. The forcing curve of the
variation-of-constants formula is `s ↦ exp (-(s - t₀) A) (B u(s))`; the analytic
core of the closure argument is the product rule for the operator exponential
against a differentiable vector curve,

`d/dt [exp (t A) H(t)] = exp (t A) (A H(t) + H'(t))`,

followed by the scalar/vector antiderivative recursion already packaged as
`IsExponentialPolynomial.hasPrimitive`. Because `A` is complex-linear while the
time `t` is real, the operator exponential is differentiated over `ℝ`: the
`ContinuousLinearMap.restrictScalars` `LinearIsometry` bridges the complex
continuous-linear-map algebra `X →L[ℂ] X` to the real one `X →L[ℝ] X`, which is
exactly the scalar bridge used by `HasDerivAt.clm_apply`.

With the product rule and `flow_mul_isExponentialPolynomial`, every finite Bohl
forcing admits a finite Bohl particular solution of `x' = A x + g`: take a Bohl
primitive `P` of `s ↦ exp (-s A) (g s)` (the `-A` flow applied to the forcing)
and set `x(t) = exp (t A) (P t)`. The resonant/generalized-eigenmode secular terms
are handled automatically by `hasPrimitive`, so no eigenvalue hypothesis is
needed.

The unrestricted locally-integrable forcing stays out of scope: the bridge that
would connect this finite Bohl response to the real `variationOfConstants` API is
recorded at the end of the section.

The product rule has already been proved in `DynamicalSystems.Linear.Trajectory`
for the shifted real flow `exp ((t - t₀) • A)` against a *constant* vector
(`hasDerivAt_expFlow_apply`) and, through the integral form, for the full
variation-of-constants curve. What is added here is the operator-times-curve
product rule that differentiates the exponential factor together with a general
differentiable vector curve. -/

/-- **Product rule for the operator exponential against a differentiable vector
curve.** For a complex continuous-linear-map generator `A` and a curve `H` with
`HasDerivAt H H' t`, the curve `s ↦ exp (s • A) (H s)` has derivative
`exp (t • A) (A (H t) + H')` at `t`.

The real-time/complex-generator scalar mismatch is bridged by restricting the
complex continuous-linear-map algebra `X →L[ℂ] X` to `ℝ` through the continuous
linear isometry `ContinuousLinearMap.restrictScalarsIsometry`, so that
`HasDerivAt.clm_apply` applies. This is the analytic core of the Bohl
variation-of-constants closure. -/
theorem hasDerivAt_exp_smul_clm_apply [CompleteSpace X] (A : X →L[ℂ] X) {H : ℝ → X}
    {H' : X} (t : ℝ) (hH : HasDerivAt H H' t) :
    HasDerivAt (fun s : ℝ ↦ NormedSpace.exp (s • A) (H s))
      (NormedSpace.exp (t • A) (A (H t) + H')) t := by
  have hc : HasDerivAt (fun s : ℝ ↦ NormedSpace.exp (s • A))
      (NormedSpace.exp (t • A) * A) t := by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) A t
  have hφ : HasFDerivAt (fun f : X →L[ℂ] X ↦ f.restrictScalars ℝ)
      (ContinuousLinearMap.restrictScalarsIsometry ℂ X X ℝ ℝ).toContinuousLinearMap
      (NormedSpace.exp (t • A)) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ X X ℝ ℝ).toContinuousLinearMap.hasFDerivAt
  have hc' : HasDerivAt (fun s : ℝ ↦ (NormedSpace.exp (s • A)).restrictScalars ℝ)
      ((NormedSpace.exp (t • A) * A).restrictScalars ℝ) t :=
    hφ.comp_hasDerivAt (f := fun s : ℝ ↦ NormedSpace.exp (s • A)) (x := t) hc
  have h := hc'.clm_apply hH
  have hderiv : ((NormedSpace.exp (t • A) * A).restrictScalars ℝ) (H t) +
      (NormedSpace.exp (t • A)).restrictScalars ℝ H' =
      NormedSpace.exp (t • A) (A (H t) + H') := by
    change (NormedSpace.exp (t • A) * A) (H t) + NormedSpace.exp (t • A) H' =
      NormedSpace.exp (t • A) (A (H t) + H')
    rw [mul_apply_eq_comp, map_add]
  rwa [hderiv] at h

/-- The operator exponential commutes with its generator. -/
theorem commute_exp_smul_clm (A : X →L[ℂ] X) (t : ℝ) :
    Commute (NormedSpace.exp (t • A)) A :=
  ((Commute.refl A).smul_left t).exp_left

/-- **Product rule in `A`-on-the-left form.** The derivative of
`s ↦ exp (s • A) (H s)` can also be written `A (exp (t • A) (H t)) + exp (t • A) H'`,
which is the form matching the state equation `x' = A x + g`. -/
theorem hasDerivAt_exp_smul_clm_apply' [CompleteSpace X] (A : X →L[ℂ] X) {H : ℝ → X}
    {H' : X} (t : ℝ) (hH : HasDerivAt H H' t) :
    HasDerivAt (fun s : ℝ ↦ NormedSpace.exp (s • A) (H s))
      (A (NormedSpace.exp (t • A) (H t)) + NormedSpace.exp (t • A) H') t := by
  have h := hasDerivAt_exp_smul_clm_apply A t hH
  have hc := (commute_exp_smul_clm A t).eq
  have happ : NormedSpace.exp (t • A) (A (H t)) =
      A (NormedSpace.exp (t • A) (H t)) := by
    rw [← mul_apply_eq_comp, hc, mul_apply_eq_comp]
  simpa [map_add, happ] using h

/-- **Finite Bohl particular solution of the linear ODE.** For a finite-dimensional
complex generator `A` and a finite exponential-polynomial (Bohl) forcing `g`
there is a finite exponential-polynomial curve `x` with `x' = A x + g` pointwise.

The construction takes a Bohl primitive `P` of the reversed forcing
`s ↦ exp (s • (-A)) (g s)` and sets `x(t) = exp (t • A) (P t)`. The reversed flow
cancels exactly at the derivative, and `hasPrimitive` supplies the secular terms
for any resonance, so no eigenvalue hypothesis is required. -/
theorem exists_isExponentialPolynomial_hasDerivAt_ode [FiniteDimensional ℂ X]
    (A : X →ₗ[ℂ] X) {g : ℝ → X} (hg : IsExponentialPolynomial g) :
    ∃ x : ℝ → X, IsExponentialPolynomial x ∧
      ∀ t, HasDerivAt x (A.toContinuousLinearMap (x t) + g t) t := by
  have hG : IsExponentialPolynomial
      (fun t : ℝ ↦ NormedSpace.exp (t • ((-A).toContinuousLinearMap)) (g t)) :=
    flow_mul_isExponentialPolynomial (-A) hg
  obtain ⟨P, hP, hPderiv⟩ := hG.hasPrimitive
  refine ⟨fun t : ℝ ↦ NormedSpace.exp (t • A.toContinuousLinearMap) (P t),
    flow_mul_isExponentialPolynomial A hP, fun t ↦ ?_⟩
  have h := hasDerivAt_exp_smul_clm_apply' A.toContinuousLinearMap
    (H := P) (H' := NormedSpace.exp (t • ((-A).toContinuousLinearMap)) (g t)) t
    (hPderiv t)
  have hneg : (t • ((-A).toContinuousLinearMap) : X →L[ℂ] X) =
      (-t) • A.toContinuousLinearMap := by
    rw [show ((-A).toContinuousLinearMap : X →L[ℂ] X) = -A.toContinuousLinearMap by simp]
    simp only [smul_neg, neg_smul]
  have hcomm : Commute (t • A.toContinuousLinearMap) (t • ((-A).toContinuousLinearMap)) := by
    rw [hneg]
    exact ((Commute.refl A.toContinuousLinearMap).smul_left t).smul_right (-t)
  have hsum : t • A.toContinuousLinearMap + t • ((-A).toContinuousLinearMap) = 0 := by
    rw [hneg, ← add_smul]
    simp
  have hmem1 : (t • A.toContinuousLinearMap) ∈
      Metric.eball (0 : X →L[ℂ] X) (NormedSpace.expSeries ℝ (X →L[ℂ] X)).radius :=
    (NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℂ] X)).symm ▸ edist_lt_top _ _
  have hmem2 : (t • ((-A).toContinuousLinearMap)) ∈
      Metric.eball (0 : X →L[ℂ] X) (NormedSpace.expSeries ℝ (X →L[ℂ] X)).radius :=
    (NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℂ] X)).symm ▸ edist_lt_top _ _
  have hcancel : NormedSpace.exp (t • A.toContinuousLinearMap) *
      NormedSpace.exp (t • ((-A).toContinuousLinearMap)) = 1 := by
    rw [← NormedSpace.exp_add_of_commute_of_mem_ball hcomm hmem1 hmem2, hsum,
      NormedSpace.exp_zero]
  have hg_t : NormedSpace.exp (t • A.toContinuousLinearMap)
      (NormedSpace.exp (t • ((-A).toContinuousLinearMap)) (g t)) = g t := by
    rw [← mul_apply_eq_comp, hcancel]
    rfl
  rwa [hg_t] at h

/-- **Applying a fixed complex continuous linear map preserves the Bohl class.** If `f`
is a finite exponential polynomial and `T` is a fixed complex continuous linear map, then
`t ↦ T (f t)` is again a finite exponential polynomial: the map acts coefficientwise on the
finite spectral expansion. The codomain `Y` is arbitrary, so this transports readouts as well
as endomorphisms; `IsExponentialPolynomial.clm` is the endomorphism special case. -/
theorem IsExponentialPolynomial.map {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    {f : ℝ → X} (T : X →L[ℂ] Y) (hf : IsExponentialPolynomial f) :
    IsExponentialPolynomial (fun t ↦ T (f t)) := by
  obtain ⟨s, D, a, hf⟩ := hf
  refine ⟨s, D, fun μ k ↦ T (a μ k), fun t ↦ ?_⟩
  change T (f t) = ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
    ∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • T (a μ k)
  rw [hf t, map_sum]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul]

/-- **Applying a fixed continuous linear map preserves the Bohl class.** If `f`
is a finite exponential polynomial and `T` is a fixed continuous linear map, then
`t ↦ T (f t)` is again a finite exponential polynomial: the map acts
coefficientwise on the finite spectral expansion. -/
theorem IsExponentialPolynomial.clm {f : ℝ → X} (T : X →L[ℂ] X)
    (hf : IsExponentialPolynomial f) :
    IsExponentialPolynomial (fun t ↦ T (f t)) :=
  hf.map T

/-! ### Real-linear closure of the finite Bohl class

The finite-support spectral class `IsExponentialPolynomial` is a *complex* class,
but the finite-Bohl synthesis layer frequently applies an arbitrary
real-linear map to a Bohl signal: a real state-feedback gain `F`, the
real restriction `A.restrictScalars ℝ` of a complex generator, or the
real shadow of a coordinate change. The closure under complex-linear maps is
`IsExponentialPolynomial.map` and the closure under an *anti*-complex-linear
endomorphism is `IsExponentialPolynomial.map_antilinear`. This section supplies
the missing general real-linear closure.

Every real-linear map `T : X →ₗ[ℝ] Y` between complex vector spaces decomposes
as

`T = T_cl + T_al`, with `T_cl x = ½ (T x - I (T (I x)))` complex-linear and
`T_al x = ½ (T x + I (T (I x)))` anti-complex-linear. The construction is
explicit and uses only the complex module structure: the complex-linear part is
upgraded from real-linearity to complex-linearity by the two identities
`T_cl (I x) = I (T_cl x)` and `T_cl (c x) = c (T_cl x)`, the latter reducing an
arbitrary complex scalar to its real and imaginary parts
(`Complex.re_add_im`; the pinned Mathlib 4.34.0-rc2 does not export a
`Complex.induction_on` principle, so the explicit real/imaginary decomposition is
used in its place). The anti-linear part is handled by the general anti-linear
closure `IsExponentialPolynomial.map_antilinear'`, of which the accepted
endomorphism lemma `IsExponentialPolynomial.map_antilinear` is the special case
`Y = X`.

Continuity enters only through the conversion of the complex-linear part to a
continuous linear map via `LinearMap.toContinuousLinearMap`, which needs the
finite-dimensionality of the domain `X`; the codomain is not required to be
finite-dimensional by the proof. The endomorphism specialization
`IsExponentialPolynomial.map_realLinear_self` reuses the accepted
`IsExponentialPolynomial.map` and `IsExponentialPolynomial.map_antilinear`
directly. -/

section RealLinearClosure

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- Multiplication by `I`, viewed as a real-linear endomorphism of a complex
vector space. -/
noncomputable def complexIMul (M : Type*) [AddCommGroup M] [Module ℂ M] : M →ₗ[ℝ] M where
  toFun x := Complex.I • x
  map_add' x y := smul_add Complex.I x y
  map_smul' r x := (smul_comm r Complex.I x).symm

@[simp] lemma complexIMul_apply {M : Type*} [AddCommGroup M] [Module ℂ M] (x : M) :
    complexIMul M x = Complex.I • x := rfl

/-- `I • (I • z) = -z`, the real-linear endomorphism `x ↦ I • x` squares to the
negative identity. -/
lemma I_smul_I_smul {M : Type*} [AddCommGroup M] [Module ℂ M] (z : M) :
    Complex.I • (Complex.I • z) = -z := by
  rw [← mul_smul, Complex.I_mul_I, neg_one_smul]

/-- Real scalars of a complex module are extracted out of a real-linear map. -/
lemma realLinearMap_coe_smul (T : X →ₗ[ℝ] Y) (r : ℝ) (z : X) :
    T ((r : ℂ) • z) = (r : ℂ) • T z := by
  rw [Complex.coe_smul, T.map_smul, Complex.coe_smul]

/-- Decomposition of an arbitrary complex scalar as `a + b I` with `a, b : ℝ`. -/
lemma complex_smul_decomp (c : ℂ) (x : X) :
    c • x = (c.re : ℂ) • x + (c.im : ℂ) • (Complex.I • x) := by
  conv_lhs => rw [← Complex.re_add_im c]
  rw [add_smul, mul_smul]

/-- The conjugate scalar decomposition `\bar c • y = a • y + b • (-I • y)`. -/
lemma star_smul_decomp (c : ℂ) (y : Y) :
    (star c) • y = (c.re : ℂ) • y + (c.im : ℂ) • (-Complex.I • y) := by
  conv_lhs => rw [← Complex.re_add_im (star c)]
  rw [add_smul, mul_smul]
  rw [show (star c).re = c.re by simp]
  rw [show (star c).im = -c.im by simp]
  module

/-- Upgrade an ℝ-linear map `f` commuting with multiplication by `I`,
`f (I • x) = I • f x`, to a ℂ-linear map with the same underlying function. -/
noncomputable def complexLinearMapOfReal (f : X →ₗ[ℝ] Y)
    (hI : ∀ x, f (Complex.I • x) = Complex.I • f x) : X →ₗ[ℂ] Y where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    rw [complex_smul_decomp c x, f.map_add, realLinearMap_coe_smul, realLinearMap_coe_smul, hI]
    exact (complex_smul_decomp c (f x)).symm

/-- An ℝ-linear map `f` with `f (I • x) = - I • f x` is anti-complex-linear:
`f (c • x) = \bar c • f x`. This is the scalar decomposition transported through
the anti-linear `I`-rule. -/
lemma antilinear_of_real (f : X →ₗ[ℝ] Y)
    (hI : ∀ x, f (Complex.I • x) = -Complex.I • f x) (c : ℂ) (x : X) :
    f (c • x) = (star c) • f x := by
  rw [complex_smul_decomp c x, f.map_add, realLinearMap_coe_smul, realLinearMap_coe_smul, hI]
  exact (star_smul_decomp c (f x)).symm

/-- The **complex-linear part** `x ↦ ½ (T x - I (T (I x)))` of a real-linear map,
as a real-linear map. -/
noncomputable def realLinearComplexPart (T : X →ₗ[ℝ] Y) : X →ₗ[ℝ] Y :=
  (2 : ℝ)⁻¹ • (T - (complexIMul Y).comp (T.comp (complexIMul X)))

@[simp] theorem realLinearComplexPart_apply (T : X →ₗ[ℝ] Y) (x : X) :
    realLinearComplexPart T x = (2 : ℂ)⁻¹ • (T x - Complex.I • T (Complex.I • x)) := by
  rw [realLinearComplexPart]
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.comp_apply, complexIMul_apply]
  rw [← Complex.coe_smul, Complex.ofReal_inv]
  norm_num

/-- The complex-linear part commutes with multiplication by `I`. -/
theorem realLinearComplexPart_I (T : X →ₗ[ℝ] Y) (x : X) :
    realLinearComplexPart T (Complex.I • x) = Complex.I • realLinearComplexPart T x := by
  rw [realLinearComplexPart_apply, realLinearComplexPart_apply]
  simp only [I_smul_I_smul]
  rw [map_neg]
  rw [smul_comm Complex.I (2 : ℂ)⁻¹ (T x - Complex.I • T (Complex.I • x))]
  simp only [smul_sub, I_smul_I_smul]
  module

/-- The **complex-linear part** of a real-linear map, upgraded to a
complex-linear map by `complexLinearMapOfReal`. -/
noncomputable def complexLinearPart (T : X →ₗ[ℝ] Y) : X →ₗ[ℂ] Y :=
  complexLinearMapOfReal (realLinearComplexPart T) (realLinearComplexPart_I T)

@[simp] theorem complexLinearPart_apply (T : X →ₗ[ℝ] Y) (x : X) :
    complexLinearPart T x = realLinearComplexPart T x := rfl

/-- The **anti-complex-linear part** `x ↦ ½ (T x + I (T (I x)))` of a real-linear
map, as a real-linear map. -/
noncomputable def realLinearAntilinearPart (T : X →ₗ[ℝ] Y) : X →ₗ[ℝ] Y :=
  (2 : ℝ)⁻¹ • (T + (complexIMul Y).comp (T.comp (complexIMul X)))

@[simp] theorem realLinearAntilinearPart_apply (T : X →ₗ[ℝ] Y) (x : X) :
    realLinearAntilinearPart T x = (2 : ℂ)⁻¹ • (T x + Complex.I • T (Complex.I • x)) := by
  rw [realLinearAntilinearPart]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply, complexIMul_apply]
  rw [← Complex.coe_smul, Complex.ofReal_inv]
  norm_num

/-- The anti-linear part satisfies the anti-linear `I`-rule. -/
theorem realLinearAntilinearPart_I (T : X →ₗ[ℝ] Y) (x : X) :
    realLinearAntilinearPart T (Complex.I • x) =
      -Complex.I • realLinearAntilinearPart T x := by
  rw [realLinearAntilinearPart_apply, realLinearAntilinearPart_apply]
  simp only [I_smul_I_smul]
  rw [map_neg]
  rw [neg_smul]
  rw [smul_comm Complex.I (2 : ℂ)⁻¹ (T x + Complex.I • T (Complex.I • x))]
  simp only [smul_add, I_smul_I_smul, smul_neg]
  module

/-- The anti-complex-linear part is anti-linear: `T_al (c • x) = \bar c • T_al x`. -/
theorem realLinearAntilinearPart_antilinear (T : X →ₗ[ℝ] Y) (c : ℂ) (x : X) :
    realLinearAntilinearPart T (c • x) = (star c) • realLinearAntilinearPart T x :=
  antilinear_of_real (realLinearAntilinearPart T) (realLinearAntilinearPart_I T) c x

/-- **The complex-linear/anti-linear decomposition** of a real-linear map:
`T x = T_cl x + T_al x` for every `x`. -/
theorem complexLinearPart_add_antilinearPart (T : X →ₗ[ℝ] Y) (x : X) :
    complexLinearPart T x + realLinearAntilinearPart T x = T x := by
  rw [complexLinearPart_apply, realLinearComplexPart_apply, realLinearAntilinearPart_apply]
  module

/-- **Antilinear transport of the finite Bohl class, arbitrary codomain.** This is
the general-codomain form of the accepted endomorphism lemma
`IsExponentialPolynomial.map_antilinear`: a real-linear map `M : X →ₗ[ℝ] Y` with
`M (c • x) = \bar c • M x` conjugates the frequencies and maps the coefficients,
so it sends finite exponential polynomials to finite exponential polynomials. -/
theorem IsExponentialPolynomial.map_antilinear' {M : X →ₗ[ℝ] Y}
    (hM : ∀ (c : ℂ) (x : X), M (c • x) = (star c) • M x)
    {f : ℝ → X} (hf : IsExponentialPolynomial f) :
    IsExponentialPolynomial (fun t ↦ M (f t)) := by
  obtain ⟨s, D, a, hf⟩ := hf
  refine ⟨s.image star, D, fun ν k => M (a (star ν) k), fun t => ?_⟩
  rw [show (fun t => M (f t)) t = M (f t) from rfl, hf t, map_sum]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro μ hμ
    rw [hM, map_sum]
    congr 1
    · simp only [Complex.star_def]
      rw [← Complex.exp_conj]
      congr 1
      simp
    · apply Finset.sum_congr rfl
      intro k hk
      rw [hM]
      congr 1
      · simp only [Complex.star_def, map_pow, Complex.conj_ofReal]
      · simp only [star_star]
  · intro μ _ ν _ hμν
    exact star_injective hμν

/-- **Real-linear closure of the finite Bohl class.** A continuous real-linear map
`T : X →L[ℝ] Y` between complex normed spaces sends a finite exponential
polynomial to a finite exponential polynomial, provided the domain is
finite-dimensional so that the complex-linear part can be read as a continuous
complex-linear map.

The real-linear map is decomposed as `T = T_cl + T_al`
(`complexLinearPart_add_antilinearPart`); the complex-linear part is transported by
`IsExponentialPolynomial.map` and the anti-linear part by
`IsExponentialPolynomial.map_antilinear'`. No complex-linearity is assumed of `T`;
the scalar field and the continuity are explicit in the statement, and the
finite-dimensionality is imposed on the domain `X`, which is exactly what is
needed to read the complex-linear part as a continuous complex-linear map. The
codomain `Y` is an arbitrary complex normed space, so no hypothesis is spent on
it.

See also `IsExponentialPolynomial.map_realLinear_self`, the specialization to
`Y = X`, which uses the accepted endomorphism lemma
`IsExponentialPolynomial.map_antilinear` directly. -/
theorem IsExponentialPolynomial.map_realLinear [FiniteDimensional ℂ X]
    (T : X →L[ℝ] Y) {f : ℝ → X} (hf : IsExponentialPolynomial f) :
    IsExponentialPolynomial (fun t ↦ T (f t)) := by
  have hcl : IsExponentialPolynomial
      (fun t ↦ complexLinearPart T.toLinearMap (f t)) :=
    hf.map (LinearMap.toContinuousLinearMap (complexLinearPart T.toLinearMap))
  have hal : IsExponentialPolynomial
      (fun t ↦ realLinearAntilinearPart T.toLinearMap (f t)) :=
    hf.map_antilinear' (realLinearAntilinearPart_antilinear T.toLinearMap)
  have hsum := hcl.add hal
  convert hsum using 1
  funext t
  exact (complexLinearPart_add_antilinearPart T.toLinearMap (f t)).symm

/-- The antistable finite-Bohl class is closed under addition. The union support
combines coincident frequencies, and the degree is padded to the larger bound. -/
theorem IsAntistableBohlSignal.add {f g : ℝ → X}
    (hf : IsAntistableBohlSignal f) (hg : IsAntistableBohlSignal g) :
    IsAntistableBohlSignal (f + g) := by
  obtain ⟨s, D, a, hfreq, hf⟩ := hf
  obtain ⟨s', E, b, hfreq', hg⟩ := hg
  refine ⟨s ∪ s', max D E,
    fun μ k => (if μ ∈ s then (if k ≤ D then a μ k else 0) else 0) +
      (if μ ∈ s' then (if k ≤ E then b μ k else 0) else 0), ?_, ?_⟩
  · intro μ hμ
    rcases Finset.mem_union.mp hμ with hs | hs'
    · exact hfreq μ hs
    · exact hfreq' μ hs'
  · intro t
    rw [Pi.add_apply, hf t, hg t]
    have hsplit :
        (∑ μ ∈ s ∪ s', Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (max D E + 1), (t : ℂ) ^ k •
            ((if μ ∈ s then (if k ≤ D then a μ k else 0) else 0) +
              (if μ ∈ s' then (if k ≤ E then b μ k else 0) else 0)))) =
        (∑ μ ∈ s ∪ s', Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (max D E + 1), (t : ℂ) ^ k •
            (if μ ∈ s then (if k ≤ D then a μ k else 0) else 0))) +
        (∑ μ ∈ s ∪ s', Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (max D E + 1), (t : ℂ) ^ k •
            (if μ ∈ s' then (if k ≤ E then b μ k else 0) else 0))) := by
      simp only [smul_add, Finset.sum_add_distrib]
    rw [hsplit]
    congr 1
    · have h1 :
        (∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
            (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)) =
          ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
            (∑ k ∈ Finset.range (max D E + 1), (t : ℂ) ^ k •
              (if μ ∈ s then (if k ≤ D then a μ k else 0) else 0)) := by
        apply Finset.sum_congr rfl
        intro μ hμ
        congr 1
        simp only [ite_eq_left hμ]
        exact (sum_range_smul_ite D E (t : ℂ) (a μ)).symm
      rw [h1]
      exact Finset.sum_subset Finset.subset_union_left
        (fun μ _ hμnot => by simp [hμnot])
    · have h1 :
        (∑ μ ∈ s', Complex.exp ((t : ℂ) * μ) •
            (∑ k ∈ Finset.range (E + 1), (t : ℂ) ^ k • b μ k)) =
          ∑ μ ∈ s', Complex.exp ((t : ℂ) * μ) •
            (∑ k ∈ Finset.range (max D E + 1), (t : ℂ) ^ k •
              (if μ ∈ s' then (if k ≤ E then b μ k else 0) else 0)) := by
        apply Finset.sum_congr rfl
        intro μ hμ
        congr 1
        simp only [ite_eq_left hμ]
        exact (sum_range_smul_ite' D E (t : ℂ) (b μ)).symm
      rw [h1]
      exact Finset.sum_subset Finset.subset_union_right
        (fun μ _ hμnot => by simp [hμnot])

/-- A complex-linear map preserves both the finite-Bohl representation and its
closed-right-half-plane support. -/
theorem IsAntistableBohlSignal.map {f : ℝ → X} (T : X →ₗ[ℂ] Y)
    (hf : IsAntistableBohlSignal f) :
    IsAntistableBohlSignal (fun t ↦ T (f t)) := by
  obtain ⟨s, D, a, hfreq, hf⟩ := hf
  refine ⟨s, D, fun μ k => T (a μ k), hfreq, fun t => ?_⟩
  change T (f t) = _
  rw [hf t, map_sum]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [map_smul]

/-- An antilinear map preserves antistability because complex conjugation leaves
the real part of every frequency unchanged. -/
theorem IsAntistableBohlSignal.map_antilinear' {M : X →ₗ[ℝ] Y}
    (hM : ∀ (c : ℂ) (x : X), M (c • x) = (star c) • M x)
    {f : ℝ → X} (hf : IsAntistableBohlSignal f) :
    IsAntistableBohlSignal (fun t ↦ M (f t)) := by
  obtain ⟨s, D, a, hfreq, hf⟩ := hf
  refine ⟨s.image star, D, fun ν k => M (a (star ν) k), ?_, ?_⟩
  · intro ν hν
    obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hν
    simpa [Complex.conj_re] using hfreq μ hμ
  · intro t
    change M (f t) = _
    rw [hf t, map_sum]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro μ hμ
      rw [hM, map_sum]
      congr 1
      · simp only [Complex.star_def]
        rw [← Complex.exp_conj]
        congr 1
        simp
      · apply Finset.sum_congr rfl
        intro k hk
        rw [hM]
        congr 1
        · simp only [Complex.star_def, map_pow, Complex.conj_ofReal]
        · simp only [star_star]
    · intro μ _ ν _ hμν
      exact star_injective hμν

/-- **Real-linear transport of antistable finite Bohl signals.** Decomposing the
map into its complex-linear and antilinear parts preserves the support half-plane:
the first keeps each frequency, while the second conjugates frequencies, which
does not change their real parts. -/
theorem IsAntistableBohlSignal.map_realLinear [FiniteDimensional ℂ X]
    (T : X →L[ℝ] Y) {f : ℝ → X} (hf : IsAntistableBohlSignal f) :
    IsAntistableBohlSignal (fun t ↦ T (f t)) := by
  have hcl : IsAntistableBohlSignal
      (fun t ↦ complexLinearPart T.toLinearMap (f t)) :=
    hf.map (complexLinearPart T.toLinearMap)
  have hal : IsAntistableBohlSignal
      (fun t ↦ realLinearAntilinearPart T.toLinearMap (f t)) :=
    hf.map_antilinear' (realLinearAntilinearPart_antilinear T.toLinearMap)
  have hsum := hcl.add hal
  convert hsum using 1
  funext t
  exact (complexLinearPart_add_antilinearPart T.toLinearMap (f t)).symm

/-- **A decaying real-linear readout of an antistable Bohl signal vanishes.**
The output map need not be complex-linear: scalarize each output by a separating
real continuous functional, embed that scalar in `ℂ`, and apply antistable
polynomial-exponential uniqueness. This is the output-side step needed before
turning the antistable part of a real-system trajectory into an unobservable
state component. -/
theorem tendsto_zero_of_antistable_realLinear_readout
    [FiniteDimensional ℂ X]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (H : X →L[ℝ] Z) {b : ℝ → X}
    (hb : IsAntistableBohlSignal b)
    (hlim : Filter.Tendsto (fun t => H (b t)) Filter.atTop (nhds 0)) :
    ∀ t, H (b t) = 0 := by
  intro t
  by_contra hne
  have hn : ‖H (b t)‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  obtain ⟨ℓ, hnorm, hℓ⟩ := exists_dual_vector ℝ (H (b t)) hn
  let S : Z →L[ℝ] ℂ := Complex.ofRealCLM.comp ℓ
  let T : X →L[ℝ] ℂ := S.comp H
  have hbT : IsAntistableBohlSignal (fun s => T (b s)) :=
    hb.map_realLinear T
  have hlimT : Filter.Tendsto (fun s => T (b s)) Filter.atTop (nhds 0) := by
    change Filter.Tendsto (fun s => S (H (b s))) Filter.atTop (nhds 0)
    simpa [Function.comp_def] using (S.continuous.tendsto 0).comp hlim
  have hz := tendsto_zero_of_isAntistableBohlSignal hbT hlimT
  have hzt := congrFun hz t
  have hval : ℓ (H (b t)) = 0 := by
    apply (Complex.ofReal_eq_zero).mp
    simpa [T, S, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply] using hzt
  rw [hℓ] at hval
  exact hn (norm_eq_zero.mp (by simpa using hval))

/-- **Real-linear closure, endomorphism form.** The specialization of
`IsExponentialPolynomial.map_realLinear` to `T : X →L[ℝ] X`, proved directly from
the accepted lemmas `IsExponentialPolynomial.map` and
`IsExponentialPolynomial.map_antilinear` (the latter used in place of the general
anti-linear closure). -/
theorem IsExponentialPolynomial.map_realLinear_self [FiniteDimensional ℂ X]
    (T : X →L[ℝ] X) {f : ℝ → X} (hf : IsExponentialPolynomial f) :
    IsExponentialPolynomial (fun t ↦ T (f t)) := by
  have hcl : IsExponentialPolynomial
      (fun t ↦ complexLinearPart T.toLinearMap (f t)) :=
    hf.map (LinearMap.toContinuousLinearMap (complexLinearPart T.toLinearMap))
  have hal : IsExponentialPolynomial
      (fun t ↦ realLinearAntilinearPart T.toLinearMap (f t)) :=
    hf.map_antilinear (realLinearAntilinearPart T.toLinearMap)
      (realLinearAntilinearPart_antilinear T.toLinearMap)
  have hsum := hcl.add hal
  convert hsum using 1
  funext t
  exact (complexLinearPart_add_antilinearPart T.toLinearMap (f t)).symm

end RealLinearClosure

/-- Constant curves are finite Bohl signals (the zero-frequency, degree-zero
mode). -/
theorem isExponentialPolynomial_const (c : X) :
    IsExponentialPolynomial (fun _ : ℝ ↦ c) := by
  refine ⟨{0}, 0, fun _ k ↦ if k = 0 then c else 0, fun t ↦ ?_⟩
  rw [Finset.sum_singleton]
  simp

/-- **The variation-of-constants integrand is a finite Bohl signal.** For finite
Bohl `g` the reversed-flow forcing `s ↦ exp ((t₀ - s) • A) (g s)` is a finite
exponential polynomial. It is the `-A` flow applied to `g`, followed by the fixed
operator `exp (t₀ • A)`; both operations preserve the Bohl class. This is the
algebraic form of the bridge from the finite Bohl response to the real
`variationOfConstants` forcing `s ↦ exp (-(s - t₀) • A) (B u(s))`; the remaining
analytic bridge is recorded below. -/
theorem IsExponentialPolynomial.forcing [FiniteDimensional ℂ X] (A : X →L[ℂ] X)
    (t₀ : ℝ) {g : ℝ → X} (hg : IsExponentialPolynomial g) :
    IsExponentialPolynomial
      (fun s : ℝ ↦ NormedSpace.exp ((t₀ - s) • A) (g s)) := by
  have h1 : IsExponentialPolynomial
      (fun s : ℝ ↦ NormedSpace.exp (s • (-A)) (g s)) :=
    flow_mul_isExponentialPolynomial (-A) hg
  have hshift : (fun s : ℝ ↦ NormedSpace.exp ((t₀ - s) • A) (g s)) =
      fun s : ℝ ↦ NormedSpace.exp (t₀ • A)
        (NormedSpace.exp (s • (-A)) (g s)) := by
    funext s
    have hmem1 : (t₀ • A) ∈
        Metric.eball (0 : X →L[ℂ] X) (NormedSpace.expSeries ℝ (X →L[ℂ] X)).radius :=
      (NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℂ] X)).symm ▸ edist_lt_top _ _
    have hmem2 : (s • (-A)) ∈
        Metric.eball (0 : X →L[ℂ] X) (NormedSpace.expSeries ℝ (X →L[ℂ] X)).radius :=
      (NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℂ] X)).symm ▸ edist_lt_top _ _
    have hcomm : Commute (t₀ • A) (s • (-A)) := by
      rw [show s • (-A) = -(s • A) by rw [smul_neg]]
      exact (((Commute.refl A).smul_left t₀).smul_right s).neg_right
    rw [← mul_apply_eq_comp, ← NormedSpace.exp_add_of_commute_of_mem_ball hcomm hmem1 hmem2]
    congr 1
    rw [sub_smul, smul_neg, sub_eq_add_neg]
  rw [hshift]
  exact IsExponentialPolynomial.clm _ h1

/-- **Bohl solution with prescribed initial value.** For every initial time `t₀`
and initial state `x₀` the linear ODE `x' = A x + g` with finite Bohl forcing `g`
admits a finite Bohl solution taking the value `x₀` at `t₀`.

The construction shifts the finite Bohl primitive `P` of `s ↦ exp (s • (-A)) (g s)`
by the constant needed to make `x(t₀) = x₀`, then multiplies by `exp (t • A)`.
This is the finite-dimensional Bohl counterpart of the variation-of-constants
formula `x(t) = exp ((t - t₀) A) (x₀ + ∫ exp ((t₀ - s) A) g(s) ds)`, with the
Bochner integral replaced by the explicit finite Bohl primitive. -/
theorem exists_isExponentialPolynomial_hasDerivAt_ode_init [FiniteDimensional ℂ X]
    (A : X →ₗ[ℂ] X) (t₀ : ℝ) (x₀ : X) {g : ℝ → X}
    (hg : IsExponentialPolynomial g) :
    ∃ x : ℝ → X, IsExponentialPolynomial x ∧ x t₀ = x₀ ∧
      ∀ t, HasDerivAt x (A.toContinuousLinearMap (x t) + g t) t := by
  have hG : IsExponentialPolynomial
      (fun t : ℝ ↦ NormedSpace.exp (t • ((-A).toContinuousLinearMap)) (g t)) :=
    flow_mul_isExponentialPolynomial (-A) hg
  obtain ⟨P, hP, hPderiv⟩ := hG.hasPrimitive
  let Q : ℝ → X := fun t ↦ P t +
    (NormedSpace.exp ((-t₀) • A.toContinuousLinearMap) x₀ - P t₀)
  have hQ : IsExponentialPolynomial Q :=
    hP.add (isExponentialPolynomial_const _)
  refine ⟨fun t : ℝ ↦ NormedSpace.exp (t • A.toContinuousLinearMap) (Q t),
    flow_mul_isExponentialPolynomial A hQ, ?_, fun t ↦ ?_⟩
  · change NormedSpace.exp (t₀ • A.toContinuousLinearMap) (Q t₀) = x₀
    have hQt₀ : Q t₀ = NormedSpace.exp ((-t₀) • A.toContinuousLinearMap) x₀ := by
      simp [Q]
    rw [hQt₀]
    have hcomm : Commute (t₀ • A.toContinuousLinearMap)
        ((-t₀) • A.toContinuousLinearMap) :=
      ((Commute.refl A.toContinuousLinearMap).smul_left t₀).smul_right (-t₀)
    have hsum : t₀ • A.toContinuousLinearMap + (-t₀) • A.toContinuousLinearMap = 0 := by
      rw [← add_smul]; simp
    rw [← mul_apply_eq_comp, ← NormedSpace.exp_add_of_commute_of_mem_ball hcomm
      ((NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℂ] X)).symm ▸ edist_lt_top _ _)
      ((NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℂ] X)).symm ▸ edist_lt_top _ _),
      hsum, NormedSpace.exp_zero]
    rfl
  · have hQderiv : HasDerivAt Q
        (NormedSpace.exp (t • ((-A).toContinuousLinearMap)) (g t)) t := by
      have := (hPderiv t).add_const
        (NormedSpace.exp ((-t₀) • A.toContinuousLinearMap) x₀ - P t₀)
      simpa [Q] using this
    have h := hasDerivAt_exp_smul_clm_apply' A.toContinuousLinearMap
      (H := Q) (H' := NormedSpace.exp (t • ((-A).toContinuousLinearMap)) (g t)) t hQderiv
    have hneg : (t • ((-A).toContinuousLinearMap) : X →L[ℂ] X) =
        (-t) • A.toContinuousLinearMap := by
      rw [show ((-A).toContinuousLinearMap : X →L[ℂ] X) = -A.toContinuousLinearMap by simp]
      simp only [smul_neg, neg_smul]
    have hcomm : Commute (t • A.toContinuousLinearMap) (t • ((-A).toContinuousLinearMap)) := by
      rw [hneg]
      exact ((Commute.refl A.toContinuousLinearMap).smul_left t).smul_right (-t)
    have hsum : t • A.toContinuousLinearMap + t • ((-A).toContinuousLinearMap) = 0 := by
      rw [hneg, ← add_smul]
      simp
    have hcancel : NormedSpace.exp (t • A.toContinuousLinearMap) *
        NormedSpace.exp (t • ((-A).toContinuousLinearMap)) = 1 := by
      rw [← NormedSpace.exp_add_of_commute_of_mem_ball hcomm
        ((NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℂ] X)).symm ▸ edist_lt_top _ _)
        ((NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℂ] X)).symm ▸ edist_lt_top _ _),
        hsum, NormedSpace.exp_zero]
    have hg_t : NormedSpace.exp (t • A.toContinuousLinearMap)
        (NormedSpace.exp (t • ((-A).toContinuousLinearMap)) (g t)) = g t := by
      rw [← mul_apply_eq_comp, hcancel]
      rfl
    rwa [hg_t] at h

/-! ### The variation-of-constants bridge via the vector-valued FTC

The declarations above are stated for a complex generator, because the Bohl
spectral class `IsExponentialPolynomial` is complex by construction. The pinned
`variationOfConstants` API is real: it is built from the real operator exponential
`LinearSystem.expFlow` and the real forcing `LinearSystem.forcing`.

This section closes the analytic half of the bridge. The reusable vector-valued
fundamental theorem of calculus lives in `DynamicalSystems.Linear.Trajectories`:
`intervalIntegral.integral_eq_sub_of_ae_hasDerivAt` (the absolutely-continuous form,
the vector-valued analogue of `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`)
and `intervalIntegral.sub_eq_integral_of_hasDerivAt` (the continuous-derivative form).
The specialization to the shifted exponential flow `s ↦ exp ((t - s) • A) (g s)` is
proved for real scalar generators in `Trajectories` and for the complex generators
used by the Bohl class here.

Consequently the finite Bohl primitive produced by
`IsExponentialPolynomial.hasPrimitive` is identified with the Bochner interval
integral: `isExponentialPolynomial_primitive_eq_integral` below. This is exactly the
identification that lets the explicit finite Bohl particular solution
`exists_isExponentialPolynomial_hasDerivAt_ode` be read as the Bochner
variation-of-constants convolution. No unrestricted locally-integrable closure and no
Bohl input spectral theorem is claimed. -/

/-- **Finite Bohl signals are continuous.** A finite exponential polynomial is a finite sum of
continuous modes, so it is continuous; this is the regularity input to the vector-valued FTC. -/
theorem IsExponentialPolynomial.continuous {f : ℝ → X} (hf : IsExponentialPolynomial f) :
    Continuous f := by
  obtain ⟨s, D, a, hf⟩ := hf
  rw [show f = fun t : ℝ => ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
      (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k) from funext hf]
  fun_prop

/-- **Product rule for the shifted complex exponential flow.** For a complex generator `A` and a
curve `g` with `HasDerivAt g g' s`, the curve `r ↦ exp ((t - r) • A) (g r)` has derivative
`exp ((t - s) • A) (-(A (g s)) + g')` at `s`.

The real-time/complex-generator scalar mismatch is bridged by the continuous linear isometry
`ContinuousLinearMap.restrictScalarsIsometry`, exactly as for the unshifted product rule
`hasDerivAt_exp_smul_clm_apply`. -/
theorem hasDerivAt_exp_sub_smul_clm_apply [CompleteSpace X] (A : X →L[ℂ] X) {g : ℝ → X}
    {g' : X} (t s : ℝ) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun r : ℝ ↦ NormedSpace.exp ((t - r) • A) (g r))
      (NormedSpace.exp ((t - s) • A) (-(A (g s)) + g')) s := by
  have hc : HasDerivAt (fun r : ℝ ↦ NormedSpace.exp ((t - r) • A))
      (NormedSpace.exp ((t - s) • A) * (-A)) s := by
    have h1 : HasDerivAt (fun u : ℝ ↦ NormedSpace.exp (u • A))
        (NormedSpace.exp ((t - s) • A) * A) (t - s) :=
      hasDerivAt_exp_smul_const (𝕂 := ℝ) A (t - s)
    have h2 : HasDerivAt (fun r : ℝ ↦ t - r) (-1 : ℝ) s :=
      (hasDerivAt_id s).const_sub t
    have h3 := h1.scomp s h2
    have heq : (-1 : ℝ) • (NormedSpace.exp ((t - s) • A) * A) =
        NormedSpace.exp ((t - s) • A) * (-A) := by rw [neg_one_smul, mul_neg]
    simpa [Function.comp_def, heq] using h3
  have hφ : HasFDerivAt (fun f : X →L[ℂ] X ↦ f.restrictScalars ℝ)
      (ContinuousLinearMap.restrictScalarsIsometry ℂ X X ℝ ℝ).toContinuousLinearMap
      (NormedSpace.exp ((t - s) • A)) :=
    (ContinuousLinearMap.restrictScalarsIsometry ℂ X X ℝ ℝ).toContinuousLinearMap.hasFDerivAt
  have hc' : HasDerivAt (fun r : ℝ ↦ (NormedSpace.exp ((t - r) • A)).restrictScalars ℝ)
      ((NormedSpace.exp ((t - s) • A) * (-A)).restrictScalars ℝ) s :=
    hφ.comp_hasDerivAt (f := fun r : ℝ ↦ NormedSpace.exp ((t - r) • A)) (x := s) hc
  have h := hc'.clm_apply hg
  have hderiv : ((NormedSpace.exp ((t - s) • A) * (-A)).restrictScalars ℝ) (g s) +
      (NormedSpace.exp ((t - s) • A)).restrictScalars ℝ g' =
      NormedSpace.exp ((t - s) • A) (-(A (g s)) + g') := by
    change (NormedSpace.exp ((t - s) • A) * (-A)) (g s) +
      NormedSpace.exp ((t - s) • A) g' = _
    rw [mul_apply_eq_comp, neg_apply, map_add]
  rwa [hderiv] at h

/-- **Vector-valued FTC on the shifted complex exponential flow.** If `g` has derivative `g'`
everywhere and `g'` is continuous, then the interval integral of the derivative of
`r ↦ exp ((t - r) • A) (g r)` is the endpoint difference. This is the complex companion of
`integral_exp_sub_smul_apply_deriv` in `DynamicalSystems.Linear.Trajectories`. -/
theorem integral_exp_sub_smul_clm_apply_deriv [CompleteSpace X] (A : X →L[ℂ] X)
    {g g' : ℝ → X} (hg : ∀ r, HasDerivAt g (g' r) r) (hg' : Continuous g') (t t₀ : ℝ) :
    ∫ r in t₀..t, NormedSpace.exp ((t - r) • A) (-(A (g r)) + g' r) =
      g t - NormedSpace.exp ((t - t₀) • A) (g t₀) := by
  have hg_cont : Continuous g := continuous_iff_continuousAt.mpr fun r ↦ (hg r).continuousAt
  have hderiv : ∀ r, HasDerivAt (fun r : ℝ ↦ NormedSpace.exp ((t - r) • A) (g r))
      (NormedSpace.exp ((t - r) • A) (-(A (g r)) + g' r)) r :=
    fun r ↦ hasDerivAt_exp_sub_smul_clm_apply A t r (hg r)
  have hflow : Continuous (fun r : ℝ ↦ NormedSpace.exp ((t - r) • A)) :=
    ((differentiable_exp_smul_const (𝕂 := ℝ) A).comp (by fun_prop)).continuous
  have hcont : Continuous
      (fun r : ℝ ↦ NormedSpace.exp ((t - r) • A) (-(A (g r)) + g' r)) :=
    hflow.clm_apply (((A.continuous.comp hg_cont).neg).add hg')
  have h := intervalIntegral.sub_eq_integral_of_hasDerivAt hderiv hcont t₀ t
  have ht : NormedSpace.exp ((t - t) • A) (g t) = g t := by simp
  rw [ht] at h
  exact h.symm

/-- **The finite Bohl primitive is the Bochner interval integral.** Let `g` be a finite Bohl
forcing and let `P` be any curve whose pointwise derivative is the reversed-flow forcing
`s ↦ exp (s • (-A)) (g s)` (in particular the explicit primitive produced by
`IsExponentialPolynomial.hasPrimitive`). Then `P` is the Bochner primitive of that forcing:
`P t - P t₀ = ∫ s in t₀..t, exp (s • (-A)) (g s) ds`.

This identifies the explicit finite Bohl antiderivative with the Bochner integral appearing in
the variation-of-constants formula, making the two correspondences composable. -/
theorem isExponentialPolynomial_primitive_eq_integral [FiniteDimensional ℂ X] (A : X →ₗ[ℂ] X)
    {g P : ℝ → X} (hg : IsExponentialPolynomial g)
    (hP : ∀ t, HasDerivAt P (NormedSpace.exp (t • ((-A).toContinuousLinearMap)) (g t)) t)
    (t₀ t : ℝ) :
    P t - P t₀ =
      ∫ s in t₀..t, NormedSpace.exp (s • ((-A).toContinuousLinearMap)) (g s) := by
  have hf : IsExponentialPolynomial
      (fun s : ℝ ↦ NormedSpace.exp (s • ((-A).toContinuousLinearMap)) (g s)) :=
    flow_mul_isExponentialPolynomial (-A) hg
  exact intervalIntegral.sub_eq_integral_of_hasDerivAt hP hf.continuous t₀ t

/-- **Bochner primitive of the variation-of-constants integrand.** This is the
`forcing` normalization of `isExponentialPolynomial_primitive_eq_integral`: for a finite Bohl
`g`, any curve `P` with pointwise derivative `s ↦ exp ((t₀ - s) • A) (g s)` satisfies
`P t - P t₀ = ∫ s in t₀..t, exp ((t₀ - s) • A) (g s) ds`.

The integrand `s ↦ exp ((t₀ - s) • A) (g s)` is the complex counterpart of the pinned real
`LinearSystem.forcing` `s ↦ exp (-(s - t₀) • A) (B u s)`; the two agree on real generators via
the scalar transport used in `hasDerivAt_exp_sub_smul_clm_apply`. -/
theorem isExponentialPolynomial_forcing_primitive_eq_integral [FiniteDimensional ℂ X]
    (A : X →L[ℂ] X) (t₀ : ℝ) {g P : ℝ → X} (hg : IsExponentialPolynomial g)
    (hP : ∀ t, HasDerivAt P (NormedSpace.exp ((t₀ - t) • A) (g t)) t) (t : ℝ) :
    P t - P t₀ = ∫ s in t₀..t, NormedSpace.exp ((t₀ - s) • A) (g s) := by
  have hf : IsExponentialPolynomial
      (fun s : ℝ ↦ NormedSpace.exp ((t₀ - s) • A) (g s)) :=
    IsExponentialPolynomial.forcing A t₀ hg
  exact intervalIntegral.sub_eq_integral_of_hasDerivAt hP hf.continuous t₀ t

/-! ### The finite-Bohl variation-of-constants response

This is the assembly step: the explicit finite Bohl particular solution of
`exists_isExponentialPolynomial_hasDerivAt_ode_init`, whose primitive was identified with
the Bochner integral by `isExponentialPolynomial_primitive_eq_integral`, is shown to be
exactly the variation-of-constants response

`x(t) = exp ((t - t₀) • A) x₀ + ∫_{t₀}^{t} exp ((t - s) • A) g(s) ds`.

The two analytic ingredients are the accepted finite Bohl primitive/ODE construction
(the antiderivative recursion `hasPrimitive` and the product rule
`hasDerivAt_exp_sub_smul_clm_apply`) and the Bochner-integral identification of the
primitive. The convolution reindexing `exp (tA) ∘ exp (s (-A)) = exp ((t - s) A)` is the
exponential addition theorem `NormedSpace.exp_add_of_commute`, and the flow is moved
inside the interval integral by `ContinuousLinearMap.intervalIntegral_comp_comm`.

The theorem is stated for a complex generator, because the Bohl class
`IsExponentialPolynomial` is complex by construction. To read it for a real
`LinearSystem ℝ X U Y` one needs the explicit *real-transport representation hypothesis*:
a complex vector-space structure on `X` together with complex-linear maps
`Aℂ : X →ₗ[ℂ] X`, `Bℂ : U →ₗ[ℂ] X` whose real restrictions are `sys.A` and `sys.B`, and an
input whose `Bℂ`-image is a finite Bohl signal. Under that hypothesis the real
`variationOfConstants` curve is the real restriction of the response below, since
the real and complex exponential series agree on the restricted algebra. No claim is
made for arbitrary locally integrable inputs. -/

/-- **Finite-Bohl variation-of-constants response.** For a finite-dimensional complex
generator `A`, an initial time `t₀`, an initial state `x₀` and a finite Bohl forcing `g`,
there is a finite Bohl curve `x` with `x(t₀) = x₀`, pointwise derivative `A x + g`, and the
variation-of-constants integral representation
`x(t) = exp ((t - t₀) • A) x₀ + ∫_{t₀}^{t} exp ((t - s) • A) g(s) ds`.

All three components — Bohl membership, the ODE, and the Bochner-integral representation —
are produced together; the construction is the explicit Bohl solution of
`exists_isExponentialPolynomial_hasDerivAt_ode_init`. -/
theorem exists_isExponentialPolynomial_variationOfConstants_response [FiniteDimensional ℂ X]
    (A : X →ₗ[ℂ] X) (t₀ : ℝ) (x₀ : X) {g : ℝ → X} (hg : IsExponentialPolynomial g) :
    ∃ x : ℝ → X, IsExponentialPolynomial x ∧ x t₀ = x₀ ∧
      (∀ t, HasDerivAt x (A.toContinuousLinearMap (x t) + g t) t) ∧
      ∀ t, x t = NormedSpace.exp ((t - t₀) • A.toContinuousLinearMap) x₀ +
        ∫ s in t₀..t, NormedSpace.exp ((t - s) • A.toContinuousLinearMap) (g s) := by
  have hG : IsExponentialPolynomial
      (fun t : ℝ ↦ NormedSpace.exp (t • ((-A).toContinuousLinearMap)) (g t)) :=
    flow_mul_isExponentialPolynomial (-A) hg
  obtain ⟨P, hP, hPderiv⟩ := hG.hasPrimitive
  let c : X := NormedSpace.exp ((-t₀) • A.toContinuousLinearMap) x₀ - P t₀
  let Q : ℝ → X := fun t ↦ P t + c
  have hmem : ∀ x : X →L[ℂ] X,
      x ∈ Metric.eball (0 : X →L[ℂ] X) (NormedSpace.expSeries ℝ (X →L[ℂ] X)).radius :=
    fun x => (NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℂ] X)).symm ▸ edist_lt_top _ _
  have hQ : IsExponentialPolynomial Q := by
    have h := hP.add (isExponentialPolynomial_const c)
    have hfun : (P + fun _ : ℝ => c) = Q := by funext t; simp [Q]
    rwa [hfun] at h
  refine ⟨fun t : ℝ ↦ NormedSpace.exp (t • A.toContinuousLinearMap) (Q t),
    flow_mul_isExponentialPolynomial A hQ, ?_, ?_, ?_⟩
  · change NormedSpace.exp (t₀ • A.toContinuousLinearMap) (Q t₀) = x₀
    have hQt₀ : Q t₀ = NormedSpace.exp ((-t₀) • A.toContinuousLinearMap) x₀ := by
      simp [Q, c]
    have hcomm : Commute (t₀ • A.toContinuousLinearMap)
        ((-t₀) • A.toContinuousLinearMap) :=
      ((Commute.refl A.toContinuousLinearMap).smul_left t₀).smul_right (-t₀)
    rw [hQt₀, ← mul_apply_eq_comp,
      ← NormedSpace.exp_add_of_commute_of_mem_ball hcomm (hmem _) (hmem _)]
    rw [show t₀ • A.toContinuousLinearMap + (-t₀) • A.toContinuousLinearMap = 0 by
      rw [← add_smul]; simp]
    simp
  · intro t
    have hQderiv : HasDerivAt Q
        (NormedSpace.exp (t • ((-A).toContinuousLinearMap)) (g t)) t := by
      have h := (hPderiv t).add_const c
      simpa [Q] using h
    have h := hasDerivAt_exp_smul_clm_apply' A.toContinuousLinearMap
      (H := Q) (H' := NormedSpace.exp (t • ((-A).toContinuousLinearMap)) (g t)) t hQderiv
    have hneg : (t • ((-A).toContinuousLinearMap) : X →L[ℂ] X) =
        (-t) • A.toContinuousLinearMap := by
      rw [show ((-A).toContinuousLinearMap : X →L[ℂ] X) = -A.toContinuousLinearMap by simp]
      simp only [smul_neg, neg_smul]
    have hcomm : Commute (t • A.toContinuousLinearMap) (t • ((-A).toContinuousLinearMap)) := by
      rw [hneg]
      exact ((Commute.refl A.toContinuousLinearMap).smul_left t).smul_right (-t)
    have hsum : t • A.toContinuousLinearMap + t • ((-A).toContinuousLinearMap) = 0 := by
      rw [hneg, ← add_smul]; simp
    have hcancel : NormedSpace.exp (t • A.toContinuousLinearMap) *
        NormedSpace.exp (t • ((-A).toContinuousLinearMap)) = 1 := by
      rw [← NormedSpace.exp_add_of_commute_of_mem_ball hcomm (hmem _) (hmem _), hsum,
        NormedSpace.exp_zero]
    have hg_t : NormedSpace.exp (t • A.toContinuousLinearMap)
        (NormedSpace.exp (t • ((-A).toContinuousLinearMap)) (g t)) = g t := by
      rw [← mul_apply_eq_comp, hcancel]
      rfl
    rwa [hg_t] at h
  · intro t
    have hPint : P t - P t₀ =
        ∫ s in t₀..t, NormedSpace.exp (s • ((-A).toContinuousLinearMap)) (g s) :=
      isExponentialPolynomial_primitive_eq_integral A hg hPderiv t₀ t
    have hGint : IntervalIntegrable
        (fun s : ℝ ↦ NormedSpace.exp (s • ((-A).toContinuousLinearMap)) (g s))
        MeasureTheory.volume t₀ t :=
      (flow_mul_isExponentialPolynomial (-A) hg).continuous.intervalIntegrable t₀ t
    have hxc : NormedSpace.exp (t • A.toContinuousLinearMap) (Q t) =
        NormedSpace.exp (t • A.toContinuousLinearMap) (P t - P t₀) +
          NormedSpace.exp ((t - t₀) • A.toContinuousLinearMap) x₀ := by
      have hQsplit : Q t = P t - P t₀ +
          NormedSpace.exp ((-t₀) • A.toContinuousLinearMap) x₀ := by
        simp only [Q, c]; abel
      rw [hQsplit, map_add]
      congr 1
      rw [← mul_apply_eq_comp,
        ← NormedSpace.exp_add_of_commute_of_mem_ball
          (((Commute.refl A.toContinuousLinearMap).smul_left t).smul_right (-t₀))
          (hmem _) (hmem _)]
      congr 1
      rw [sub_smul, neg_smul]
      abel
    calc NormedSpace.exp (t • A.toContinuousLinearMap) (Q t)
        = NormedSpace.exp (t • A.toContinuousLinearMap) (P t - P t₀) +
            NormedSpace.exp ((t - t₀) • A.toContinuousLinearMap) x₀ := hxc
      _ = NormedSpace.exp (t • A.toContinuousLinearMap)
            (∫ s in t₀..t, NormedSpace.exp (s • ((-A).toContinuousLinearMap)) (g s)) +
            NormedSpace.exp ((t - t₀) • A.toContinuousLinearMap) x₀ := by rw [hPint]
      _ = (∫ s in t₀..t, NormedSpace.exp ((t - s) • A.toContinuousLinearMap) (g s)) +
            NormedSpace.exp ((t - t₀) • A.toContinuousLinearMap) x₀ := by
          rw [add_right_cancel_iff]
          rw [← ContinuousLinearMap.intervalIntegral_comp_comm
            (NormedSpace.exp (t • A.toContinuousLinearMap)) hGint]
          apply intervalIntegral.integral_congr
          intro s _
          dsimp only
          rw [show (s • ((-A).toContinuousLinearMap) : X →L[ℂ] X) =
              (-s) • A.toContinuousLinearMap by
            rw [show ((-A).toContinuousLinearMap : X →L[ℂ] X) =
                -A.toContinuousLinearMap by simp]
            simp only [smul_neg, neg_smul]]
          rw [← mul_apply_eq_comp,
            ← NormedSpace.exp_add_of_commute_of_mem_ball
              (((Commute.refl A.toContinuousLinearMap).smul_left t).smul_right (-s))
              (hmem _) (hmem _)]
          congr 1
          rw [sub_smul, neg_smul]
          abel
      _ = NormedSpace.exp ((t - t₀) • A.toContinuousLinearMap) x₀ +
            ∫ s in t₀..t, NormedSpace.exp ((t - s) • A.toContinuousLinearMap) (g s) := by
          rw [add_comm]

/-! ### Real/complex transport of the finite-Bohl response

The finite-Bohl response `exists_isExponentialPolynomial_variationOfConstants_response` is
stated for a complex generator on a complex normed space, while the accepted trajectory API
`LinearSystem.variationOfConstants` lives on a *real* `LinearSystem ℝ X U Y`. The bridge here
transports the complex response to the real trajectory under an explicit
*complexification/coordinate-embedding hypothesis*: the real state space carries a complex
normed-space structure, and the system maps are the `restrictScalars ℝ` shadows of complex-linear
maps `Aℂ`, `Bℂ`, `Cℂ`,

`Aℂ.restrictScalars ℝ = sys.A`, `Bℂ.restrictScalars ℝ = sys.B`,
`Cℂ.restrictScalars ℝ = sys.C`,

so the complexification preserves the state map, the input map and the readout. The input is
admissible when its `Bℂ`-image is a finite Bohl signal (the *finite-Bohl input image*
condition). Under these hypotheses the real variation-of-constants trajectory is again a finite
exponential polynomial, its readout is a finite exponential polynomial, it is differentiable
at every time with the real state equation, and it is the real restriction of the complex
response identity
`x(t) = exp ((t - t₀) Aℂ) x₀ + ∫_{t₀}^{t} exp ((t - s) Aℂ) (Bℂ u(s)) ds`.

Because the conclusion is the named Bohl class, the accepted non-cancellation theorem
`tendsto_zero_of_isAntistableBohlSignal` (an antistable polynomial-exponential readout that
tends to zero is identically zero) now applies directly to real trajectories. No claim is made
for arbitrary locally-integrable inputs: the finite-Bohl input-image hypothesis is essential,
and the full open-loop `W_g` necessity is not asserted here. -/

section RealTransport

variable {U Y : Type*}
variable [NormedAddCommGroup U] [NormedSpace ℂ U]
variable [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- **Real/complex transport of the finite-Bohl variation-of-constants response.** Let
`sys : LinearSystem ℝ X U Y` be a real system whose state map, input map and readout are the
real restrictions of complex-linear maps `Aℂ`, `Bℂ`, `Cℂ`:
`Aℂ.restrictScalars ℝ = sys.A`, `Bℂ.restrictScalars ℝ = sys.B`,
`Cℂ.restrictScalars ℝ = sys.C`. If the input `u` is locally integrable and its `Bℂ`-image is
a finite Bohl signal, then the real variation-of-constants trajectory `sys.variationOfConstants
 t₀ x₀ u`

* is a finite exponential polynomial (the finite-Bohl response transported to the real system);
* has a finite-exponential-polynomial readout `t ↦ sys.C (x(t))`, so the accepted
  non-cancellation theorem applies to real trajectories;
* is differentiable at every time with the real state equation
  `x'(t) = sys.A x(t) + sys.B u(t)`;
* satisfies the transported complex response identity
  `x(t) = exp ((t - t₀) Aℂ) x₀ + ∫_{t₀}^{t} exp ((t - s) Aℂ) (Bℂ u(s)) ds`.

The proof consumes `exists_isExponentialPolynomial_variationOfConstants_response`, identifies
the complex response with the real `variationOfConstants` curve through the unconditional
uniqueness theorem `integralSolution_unique` (the local-integrability hypothesis on `u` supplies
the real integral identity `variationOfConstants_integral`), and transports the readout with
`IsExponentialPolynomial.map`. No arbitrary locally-integrable coverage and no open-loop `W_g`
theorem are claimed. -/
theorem variationOfConstants_transport_of_complexification
    [FiniteDimensional ℂ X] [FiniteDimensional ℂ U]
    (sys : LinearSystem ℝ X U Y) (Aℂ : X →ₗ[ℂ] X) (Bℂ : U →ₗ[ℂ] X) (Cℂ : X →ₗ[ℂ] Y)
    (hA : Aℂ.restrictScalars ℝ = sys.A) (hB : Bℂ.restrictScalars ℝ = sys.B)
    (hC : Cℂ.restrictScalars ℝ = sys.C)
    (t₀ : ℝ) (x₀ : X) (u : ℝ → U) (hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume)
    (hBohl : IsExponentialPolynomial (fun t : ℝ => Bℂ (u t))) :
    IsExponentialPolynomial (sys.variationOfConstants t₀ x₀ u) ∧
    IsExponentialPolynomial (fun t : ℝ => sys.C (sys.variationOfConstants t₀ x₀ u t)) ∧
    (∀ t : ℝ, HasDerivAt (sys.variationOfConstants t₀ x₀ u)
        (sys.dynamics (sys.variationOfConstants t₀ x₀ u t) (u t)) t) ∧
    (∀ t : ℝ, sys.variationOfConstants t₀ x₀ u t =
        NormedSpace.exp ((t - t₀) • Aℂ.toContinuousLinearMap) x₀ +
        ∫ s in t₀..t, NormedSpace.exp ((t - s) • Aℂ.toContinuousLinearMap) (Bℂ (u s))) := by
  obtain ⟨x, hxb, hx0, hxderiv, hxint⟩ :=
    exists_isExponentialPolynomial_variationOfConstants_response Aℂ t₀ x₀ hBohl
  have hxc : Continuous x := hxb.continuous
  have hdyn : ∀ t : ℝ, sys.dynamics (x t) (u t) =
      Aℂ.toContinuousLinearMap (x t) + Bℂ (u t) := by
    intro t
    rw [LinearSystem.dynamics_apply, ← hA, ← hB, LinearMap.restrictScalars_apply,
      LinearMap.restrictScalars_apply]
    rfl
  have hdx : ∀ t : ℝ, HasDerivAt x (sys.dynamics (x t) (u t)) t := by
    intro t
    rw [hdyn t]
    exact hxderiv t
  have hcont : Continuous (fun s : ℝ => sys.dynamics (x s) (u s)) := by
    have h1 : Continuous (fun s : ℝ => Aℂ.toContinuousLinearMap (x s)) :=
      Aℂ.toContinuousLinearMap.continuous.comp hxc
    have h2 : Continuous (fun s : ℝ => Bℂ (u s)) := hBohl.continuous
    have hfun : (fun s : ℝ => sys.dynamics (x s) (u s)) =
        fun s : ℝ => Aℂ.toContinuousLinearMap (x s) + Bℂ (u s) := by
      funext s
      exact hdyn s
    rw [hfun]
    exact h1.add h2
  have hxint' : ∀ t : ℝ, x t = x₀ + ∫ s in t₀..t, sys.dynamics (x s) (u s) := by
    intro t
    have hF : x t - x t₀ = ∫ s in t₀..t, sys.dynamics (x s) (u s) :=
      intervalIntegral.sub_eq_integral_of_hasDerivAt (fun s => hdx s) hcont t₀ t
    rw [hx0] at hF
    rw [← hF]
    abel
  have hEq : x = sys.variationOfConstants t₀ x₀ u :=
    integralSolution_unique sys t₀ x₀ u hu hxc hx0 hxint'
      (continuous_variationOfConstants sys t₀ x₀ u hu)
      (variationOfConstants_self sys t₀ x₀ u)
      (fun t => variationOfConstants_integral sys t₀ x₀ u hu t)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hEq]; exact hxb
  · rw [← hEq]
    have hfun : (fun t : ℝ => sys.C (x t)) = fun t : ℝ => Cℂ (x t) := by
      funext t
      rw [← hC, LinearMap.restrictScalars_apply]
    rw [hfun]
    exact hxb.map Cℂ.toContinuousLinearMap
  · intro t
    rw [← hEq]
    exact hdx t
  · intro t
    rw [← hEq]
    exact hxint t

end RealTransport

/-! ### Real-basis Bohl response for an arbitrary real-linear generator

Unlike `variationOfConstants_transport_of_complexification`, the theorem below
does not require `sys.A` to be complex-linear for the chosen complex structure on
`X`. It chooses a real basis, complexifies the resulting real matrix, solves the
finite-Bohl response in those coordinates, and projects the response back to
the real state space. -/

section RealBohlResponse

open scoped Matrix

variable {X U Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℝ X]
variable [FiniteDimensional ℂ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- **A real finite-dimensional forced trajectory is finite Bohl.** If the
system's forcing image `t ↦ B (u t)` is a finite exponential polynomial, then
the variation-of-constants trajectory is one as well, even when the real-linear
state map `A` is not complex-linear for the chosen complex structure on `X`.
The proof realifies through a real basis, complexifies its matrix, takes a
finite-Bohl primitive of the rotated forcing, and projects the resulting complex
response back to `X`. -/
theorem variationOfConstants_isExponentialPolynomial_of_realLinear
    (sys : LinearSystem ℝ X U Y) (x₀ : X) (u : ℝ → U)
    (hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume)
    (hBu : IsExponentialPolynomial (fun t : ℝ => sys.continuousB (u t))) :
    IsExponentialPolynomial (sys.variationOfConstants 0 x₀ u) := by
  let n : ℕ := Module.finrank ℝ X
  let b : Module.Basis (Fin n) ℝ X := Module.finBasis ℝ X
  let L : X ≃L[ℝ] (Fin n → ℝ) := b.equivFun.toContinuousLinearEquiv
  let M : Matrix (Fin n) (Fin n) ℝ := LinearMap.toMatrix b b sys.A
  let g : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
    (Matrix.toLin' M).toContinuousLinearMap
  let h : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    Matrix.toLin' (M.map (algebraMap ℝ ℂ))
  let hC : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) := h.toContinuousLinearMap
  have hg : g = L.conjContinuousAlgEquiv sys.continuousA := by
    apply ContinuousLinearMap.ext
    intro y
    have hrepr : M *ᵥ b.repr (L.symm y) = b.repr (sys.A (L.symm y)) :=
      LinearMap.toMatrix_mulVec_repr b b sys.A (L.symm y)
    have hLy : b.repr (L.symm y) = y := by
      rw [← Module.Basis.equivFun_apply b (L.symm y)]
      exact b.equivFun.apply_symm_apply y
    rw [hLy] at hrepr
    change M *ᵥ y = L (sys.continuousA (L.symm y))
    rw [hrepr]
    rw [← Module.Basis.equivFun_apply b (sys.A (L.symm y))]
    rfl
  have hLexp : ∀ t : ℝ, ∀ v : X,
      L (sys.expFlow t v) = NormedSpace.exp (t • g) (L v) := by
    intro t v
    have key := NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (L.conjContinuousAlgEquiv)
      (L.conjContinuousAlgEquiv).continuous (t • sys.continuousA)
      ((NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _)
    have hcongr : (L.conjContinuousAlgEquiv) (t • sys.continuousA) = t • g := by
      rw [map_smul, hg.symm]
    have hk := congrArg (fun f : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => f (L v)) key
    rw [hcongr] at hk
    simpa [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply, g,
      LinearSystem.expFlow] using hk
  let rePi : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun z i => (z i).re
      map_add' := by intro z w; ext i; simp
      map_smul' := by intro r z; ext i; simp }
  let R : (Fin n → ℂ) →ₗ[ℝ] X := L.symm.toLinearMap.comp rePi
  let T : X →L[ℝ] (Fin n → ℂ) :=
    LinearMap.ofRealPi.toContinuousLinearMap.comp L.toContinuousLinearMap
  have hBuC : IsExponentialPolynomial
      (fun t : ℝ => LinearMap.ofRealPi (L (sys.continuousB (u t)))) := by
    have h := hBu.map_realLinear (Y := Fin n → ℂ) T
    convert h using 1
    funext t
    simp [T, L]
  have hforceC : IsExponentialPolynomial
      (fun s : ℝ => LinearMap.ofRealPi (L (sys.forcing 0 u s))) := by
    have hf := IsExponentialPolynomial.forcing hC 0 hBuC
    have hEq : (fun s : ℝ => LinearMap.ofRealPi (L (sys.forcing 0 u s))) =
        (fun s : ℝ => NormedSpace.exp (s • (-hC))
          (LinearMap.ofRealPi (L (sys.continuousB (u s))))) := by
      funext s
      rw [show sys.forcing 0 u s = sys.expFlow (-s) (sys.continuousB (u s)) by
        simp [LinearSystem.forcing]]
      rw [hLexp (-s), LinearMap.ofRealPi_exp M (-s)
        (L (sys.continuousB (u s)))]
      change NormedSpace.exp ((-s : ℝ) • hC) _ =
        NormedSpace.exp (s • (-hC)) _
      congr 1
      congr 1
      ext i
      simp [h, hC, smul_neg]
    rw [hEq]
    simpa [sub_eq_add_neg, neg_smul] using hf
  obtain ⟨P, hP, hPderiv⟩ := hforceC.hasPrimitive
  let q₀ : Fin n → ℂ := LinearMap.ofRealPi (L x₀)
  let Q : ℝ → (Fin n → ℂ) := fun t => P t + (q₀ - P 0)
  have hQ : IsExponentialPolynomial Q := by
    have hh := hP.add (isExponentialPolynomial_const (q₀ - P 0))
    convert hh using 1 <;> funext t <;> simp [Q]
  have hQintegral : ∀ t : ℝ,
      Q t = LinearMap.ofRealPi (L (x₀ + ∫ s in (0 : ℝ)..t, sys.forcing 0 u s)) := by
    intro t
    have hPint : P t - P 0 =
        ∫ s in (0 : ℝ)..t, LinearMap.ofRealPi (L (sys.forcing 0 u s)) :=
      intervalIntegral.sub_eq_integral_of_hasDerivAt hPderiv hforceC.continuous 0 t
    have hInt : IntervalIntegrable (sys.forcing 0 u) MeasureTheory.volume 0 t :=
      intervalIntegrable_forcing sys 0 hu 0 t
    have hMap := T.intervalIntegral_comp_comm hInt
    calc
      Q t = q₀ + (P t - P 0) := by simp [Q, q₀]; abel
      _ = q₀ + ∫ s in (0 : ℝ)..t, T (sys.forcing 0 u s) := by
        rw [show (∫ s in (0 : ℝ)..t, T (sys.forcing 0 u s)) =
          ∫ s in (0 : ℝ)..t, LinearMap.ofRealPi (L (sys.forcing 0 u s)) by
            rfl, hPint]
      _ = q₀ + T (∫ s in (0 : ℝ)..t, sys.forcing 0 u s) := by rw [← hMap]
      _ = LinearMap.ofRealPi (L (x₀ + ∫ s in (0 : ℝ)..t, sys.forcing 0 u s)) := by
        simp [q₀, T, map_add]
  let z : ℝ → (Fin n → ℂ) := fun t => NormedSpace.exp (t • hC) (Q t)
  have hz : IsExponentialPolynomial z := flow_mul_isExponentialPolynomial h hQ
  let xcoord : ℝ → X := fun t => R (z t)
  have hxcoord : xcoord = sys.variationOfConstants 0 x₀ u := by
    funext t
    change R (NormedSpace.exp (t • hC) (Q t)) = _
    rw [hQintegral t]
    have hExp (v : X) : NormedSpace.exp (t • hC) (LinearMap.ofRealPi (L v)) =
        LinearMap.ofRealPi (L (sys.expFlow t v)) := by
      rw [hLexp t v, ← LinearMap.ofRealPi_exp M t (L v)]
    rw [hExp]
    simp [R, rePi, LinearMap.ofRealPi, LinearSystem.variationOfConstants, map_add]
  rw [← hxcoord]
  exact hz.map_realLinear R.toContinuousLinearMap

end RealBohlResponse

/-! ## Finite-Bohl quotient non-cancellation

The real/complex transport of the previous section shows that, for a real system
whose input image is a finite Bohl signal, the readout of the forced trajectory is
again a finite exponential polynomial. This section turns that class membership
into the *spectral projection* step that the unrestricted locally-integrable
`W_g` necessity has been missing.

For an unrestricted locally integrable input the pinned library supplies no
spectrum-of-a-function (Laplace/Bohl) API, so the stable/antistable spectral
projection of the forced trajectory cannot be formed. The finite Bohl class,
however, carries its frequency set as an explicit `Finset ℂ`, so the projection is
elementary: collecting the frequencies with `μ.re < 0` and with `0 ≤ μ.re` splits
any finite exponential polynomial into a *stable* part, which decays at `+∞` by
the accepted scalar engine `LinearMap.tendsto_exp_mul_pow`, and an *antistable*
part. If the whole signal tends to `0`, the antistable part inherits the limit, and
the accepted polynomial-exponential vanishing theorem
`tendsto_zero_of_isAntistableBohlSignal` forces it to vanish identically.

The reachable-subspace quotient enters through the transport hypothesis
`IsExponentialPolynomial (fun t ↦ Bℂ (u t))`: the whole reachable forcing is finite
Bohl, so the readout of the forced trajectory — not merely its autonomous orbit — is
covered by the projection. The resulting statement is the strongest honest quotient
result available for the finite-Bohl class. It is a strict specialisation of the
open-loop `W_g` necessity `mem_outputStabilizableSubspace_of_isOutputStabilizable`:
an arbitrary locally integrable input has no finite frequency set, so the
projection below cannot be formed, and the Laplace/Titchmarsh convolution
non-cancellation at the threshold `V*(ker H ⊔ ⟨A | im B⟩)` remains the documented
extension problem. Nothing here asserts that unrestricted statement. -/

section FiniteBohlProjection

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- A **stable finite exponential polynomial**: a finite-support spectral sum all
of whose frequencies lie in the open left half-plane. This is the decaying
counterpart of `IsAntistableBohlSignal`. -/
def IsStableExponentialPolynomial (f : ℝ → X) : Prop :=
  ∃ (s : Finset ℂ) (D : ℕ) (a : ℂ → ℕ → X),
    (∀ μ ∈ s, μ.re < 0) ∧
      ∀ t, f t = ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)

/-- Every stable finite exponential polynomial is a finite exponential polynomial. -/
theorem IsStableExponentialPolynomial.isExponentialPolynomial {f : ℝ → X}
    (hf : IsStableExponentialPolynomial f) : IsExponentialPolynomial f := by
  obtain ⟨s, D, a, -, hrepr⟩ := hf
  exact ⟨s, D, a, hrepr⟩

/-- **Stable finite exponential polynomials decay.** A finite sum of polynomial
terms times exponential characters with strictly negative real part tends to `0`
at `+∞`. Each mode decays by the accepted scalar engine
`LinearMap.tendsto_exp_mul_pow`, and the finite sum follows from
`tendsto_finsetSum`. -/
theorem IsStableExponentialPolynomial.tendsto_zero {f : ℝ → X}
    (hf : IsStableExponentialPolynomial f) :
    Filter.Tendsto f Filter.atTop (nhds 0) := by
  obtain ⟨s, D, a, hμs, hrepr⟩ := hf
  rw [show f = (fun t : ℝ => ∑ μ ∈ s, Complex.exp ((t : ℂ) * μ) •
      (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)) from funext hrepr]
  have hterm : ∀ μ ∈ s, Filter.Tendsto
      (fun t : ℝ => Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)) Filter.atTop (nhds 0) := by
    intro μ hμ
    have hinner : Filter.Tendsto
        (fun t : ℝ => ∑ k ∈ Finset.range (D + 1), Complex.exp ((t : ℂ) * μ) •
          ((t : ℂ) ^ k • a μ k)) Filter.atTop (nhds 0) := by
      have h2 := tendsto_finsetSum (Finset.range (D + 1))
        (f := fun (k : ℕ) (t : ℝ) =>
          Complex.exp ((t : ℂ) * μ) • ((t : ℂ) ^ k • a μ k))
        (a := fun _ => (0 : X)) (by
          intro k _
          have hscalar : Filter.Tendsto
              (fun t : ℝ => Complex.exp ((t : ℂ) * μ) * (t : ℂ) ^ k)
              Filter.atTop (nhds 0) :=
            LinearMap.tendsto_exp_mul_pow μ (hμs μ hμ) k
          have hfun2 : (fun t : ℝ => Complex.exp ((t : ℂ) * μ) • ((t : ℂ) ^ k • a μ k)) =
              fun t : ℝ => (Complex.exp ((t : ℂ) * μ) * (t : ℂ) ^ k) • a μ k := by
            funext t; rw [smul_smul]
          rw [hfun2]
          simpa using hscalar.smul_const (a μ k))
      simpa using h2
    rwa [show (fun t : ℝ => Complex.exp ((t : ℂ) * μ) •
          (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k)) =
        fun t : ℝ => ∑ k ∈ Finset.range (D + 1), Complex.exp ((t : ℂ) * μ) •
          ((t : ℂ) ^ k • a μ k) from by funext t; rw [Finset.smul_sum]]
  simpa using tendsto_finsetSum s hterm

/-- **Stable/antistable splitting of a finite exponential polynomial.** Every
finite-support spectral sum decomposes as a stable part (frequencies in the open
left half-plane) plus an antistable part (frequencies in the closed right
half-plane). The split keeps the same frequency set, degree bound and coefficient
family; it is the explicit spectral projection that the unrestricted
locally-integrable input class cannot supply. -/
theorem IsExponentialPolynomial.exists_stable_add_antistable {f : ℝ → X}
    (hf : IsExponentialPolynomial f) :
    ∃ g b : ℝ → X, f = g + b ∧ IsStableExponentialPolynomial g ∧
      IsAntistableBohlSignal b := by
  obtain ⟨s, D, a, hrepr⟩ := hf
  classical
  refine ⟨fun t : ℝ => ∑ μ ∈ s.filter (fun μ => μ.re < 0),
      Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k),
    fun t : ℝ => ∑ μ ∈ s.filter (fun μ => ¬ μ.re < 0),
      Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k), ?_, ?_, ?_⟩
  · funext t
    rw [Pi.add_apply, hrepr t]
    exact (Finset.sum_filter_add_sum_filter_not s (fun μ => μ.re < 0)
      (fun μ => Complex.exp ((t : ℂ) * μ) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a μ k))).symm
  · exact ⟨s.filter (fun μ => μ.re < 0), D, a,
      fun μ hμ => (Finset.mem_filter.mp hμ).2, fun t => rfl⟩
  · exact ⟨s.filter (fun μ => ¬ μ.re < 0), D, a,
      fun μ hμ => not_lt.mp (Finset.mem_filter.mp hμ).2, fun t => rfl⟩

/-- **Forward-projection non-cancellation.** If a finite exponential polynomial
tends to `0` at `+∞`, then in *any* stable/antistable decomposition its
antistable part vanishes identically. The stable part decays by
`IsStableExponentialPolynomial.tendsto_zero`, so the antistable part inherits the
limit; the accepted polynomial-exponential vanishing theorem then kills it. This
is the abstract frequency-projection core of the finite-Bohl quotient result. -/
theorem eq_zero_of_eq_stable_add_antistable_of_tendsto_zero {f g b : ℝ → X}
    (hgb : f = g + b) (hg : IsStableExponentialPolynomial g)
    (hb : IsAntistableBohlSignal b) (hf : Filter.Tendsto f Filter.atTop (nhds 0)) :
    b = 0 := by
  have hg0 : Filter.Tendsto g Filter.atTop (nhds 0) := hg.tendsto_zero
  have hb0 : Filter.Tendsto b Filter.atTop (nhds 0) := by
    have hsub : Filter.Tendsto (fun t : ℝ => f t - g t) Filter.atTop (nhds 0) := by
      simpa using hf.sub hg0
    refine hsub.congr' (Filter.Eventually.of_forall fun t => ?_)
    rw [hgb]
    simp only [Pi.add_apply]
    abel
  exact tendsto_zero_of_isAntistableBohlSignal hb hb0

/-- **A decaying finite exponential polynomial is stable.** If a finite
exponential polynomial tends to `0` at `+∞`, then it admits a representation all
of whose frequencies lie in the open left half-plane; equivalently, its antistable
spectral projection vanishes. This is the transparent form of the
frequency-projection non-cancellation: decay cannot leave an antistable character
un cancelled. -/
theorem IsExponentialPolynomial.of_tendsto_zero {f : ℝ → X}
    (hf : IsExponentialPolynomial f) (h : Filter.Tendsto f Filter.atTop (nhds 0)) :
    IsStableExponentialPolynomial f := by
  obtain ⟨g, b, hgb, hg, hb⟩ := hf.exists_stable_add_antistable
  have hb0 : b = 0 := eq_zero_of_eq_stable_add_antistable_of_tendsto_zero hgb hg hb h
  have hf_eq_g : f = g := by rw [hgb, hb0, add_zero]
  rw [hf_eq_g]
  exact hg

/-- **Real-linear output projection of a decaying Bohl signal.** If a
finite-dimensional complex state signal is a finite exponential polynomial and
its real-linear readout tends to zero, it splits into a decaying stable state
part and an antistable state part whose readout vanishes identically. This
packages the stable/antistable frequency split with real-output scalarization. -/
theorem IsExponentialPolynomial.exists_stable_add_antistable_of_tendsto_realLinear
    [FiniteDimensional ℂ X]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : ℝ → X} (hf : IsExponentialPolynomial f) (H : X →L[ℝ] Z)
    (hlim : Filter.Tendsto (fun t => H (f t)) Filter.atTop (nhds 0)) :
    ∃ g b : ℝ → X, f = g + b ∧ IsStableExponentialPolynomial g ∧
      IsAntistableBohlSignal b ∧ Filter.Tendsto g Filter.atTop (nhds 0) ∧
      ∀ t, H (b t) = 0 := by
  obtain ⟨g, b, hgb, hg, hb⟩ := hf.exists_stable_add_antistable
  have hg0 : Filter.Tendsto g Filter.atTop (nhds 0) := hg.tendsto_zero
  have hHg0 : Filter.Tendsto (fun t => H (g t)) Filter.atTop (nhds 0) := by
    have h := (H.continuous.tendsto 0).comp hg0
    simpa [Function.comp_def] using h
  have hbdec : Filter.Tendsto (fun t => H (b t)) Filter.atTop (nhds 0) := by
    have hsplit : (fun t => H (f t)) = fun t => H (g t) + H (b t) := by
      funext t
      rw [congrFun hgb t, Pi.add_apply, map_add]
    have h' := hlim
    rw [hsplit] at h'
    simpa using h'.sub hHg0
  exact ⟨g, b, hgb, hg, hb, hg0,
    tendsto_zero_of_antistable_realLinear_readout H hb hbdec⟩

end FiniteBohlProjection

end LinearSystem

namespace LinearMap

private theorem finiteBohl_linear_ode_eq_exp
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (A : Y →L[ℝ] Y) (y : ℝ → Y)
    (hode : ∀ t, HasDerivAt y (A (y t)) t) :
    ∀ t, y t = NormedSpace.exp (t • A) (y 0) := by
  let P : ℝ → Y := fun t => NormedSpace.exp (t • (-A)) (y t)
  have hP : ∀ t, HasDerivAt P 0 t := by
    intro t
    have hexp : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • (-A)))
        (NormedSpace.exp (t • (-A)) * (-A)) t := by
      simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) t
    have h := hexp.clm_apply (hode t)
    convert h using 1 <;> simp [P, mul_apply_eq_comp]
  have hconst : ∀ t, P t = P 0 := by
    intro t
    exact is_const_of_deriv_eq_zero (fun s => (hP s).differentiableAt)
      (fun s => (hP s).deriv) t 0
  intro t
  let E : Y →L[ℝ] Y := NormedSpace.exp (t • A)
  have headd : E * NormedSpace.exp (t • (-A)) = 1 := by
    have hneg : t • (-A) = (-t) • A := by simp
    have hcomm : Commute (t • A) (t • (-A)) := by
      rw [hneg]
      exact ((Commute.refl A).smul_left t).smul_right (-t)
    have hsum : t • A + t • (-A) = 0 := by rw [hneg, ← add_smul]; simp
    have hmem1 : (t • A) ∈
        Metric.eball (0 : Y →L[ℝ] Y) (NormedSpace.expSeries ℝ (Y →L[ℝ] Y)).radius :=
      (NormedSpace.expSeries_radius_eq_top ℝ (Y →L[ℝ] Y)).symm ▸ edist_lt_top _ _
    have hmem2 : (t • (-A)) ∈
        Metric.eball (0 : Y →L[ℝ] Y) (NormedSpace.expSeries ℝ (Y →L[ℝ] Y)).radius :=
      (NormedSpace.expSeries_radius_eq_top ℝ (Y →L[ℝ] Y)).symm ▸ edist_lt_top _ _
    rw [← NormedSpace.exp_add_of_commute_of_mem_ball hcomm hmem1 hmem2, hsum,
      NormedSpace.exp_zero]
  have hcancel : E (P t) = y t := by
    change (NormedSpace.exp (t • A))
      ((NormedSpace.exp (t • (-A))) (y t)) = y t
    rw [← mul_apply_eq_comp, headd]
    simp
  calc
    y t = E (P t) := hcancel.symm
    _ = E (P 0) := congrArg E (hconst t)
    _ = NormedSpace.exp (t • A) (y 0) := by simp [E, P]

private theorem finiteBohl_quotient_ode_eq_exp
    {X U : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup U] [NormedSpace ℝ U]
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    [IsClosed (_root_.LinearMap.reachableSubspace A B : Set X)]
    [IsTopologicalRing
      ((X ⧸ _root_.LinearMap.reachableSubspace A B) →L[ℝ]
        (X ⧸ _root_.LinearMap.reachableSubspace A B))]
    (g : ℝ → X) (r : ℝ → X) (x₀ : X)
    (hg0 : g 0 = x₀)
    (hode : ∀ t, HasDerivAt g (A (g t) + r t) t)
    (hr : ∀ t, r t ∈ _root_.LinearMap.reachableSubspace A B) :
    ∀ t, (_root_.LinearMap.reachableSubspace A B).mkQ (g t) =
      NormedSpace.exp (t • (_root_.LinearMap.quotientReachableA A B).toContinuousLinearMap)
        ((_root_.LinearMap.reachableSubspace A B).mkQ x₀) := by
  let R := _root_.LinearMap.reachableSubspace A B
  let Aq : (X ⧸ R) →ₗ[ℝ] (X ⧸ R) := R.mapQ R A
    ((Submodule.map_le_iff_le_comap).mp (_root_.LinearMap.map_reachableSubspace_le A B))
  have hR : R ≤ R.comap A := fun x hx =>
    _root_.LinearMap.map_reachableSubspace_le A B ⟨x, hx, rfl⟩
  have hq : R.mkQ.comp A = Aq.comp R.mkQ := by
    ext x
    exact (congrFun (congrArg DFunLike.coe (Submodule.mapQ_mkQ R R A (h := hR))) x).symm
  have hqode : ∀ t, HasDerivAt (fun s : ℝ => R.mkQ (g s))
      (Aq (R.mkQ (g t))) t := by
    intro t
    have hd := (ContinuousLinearMap.hasFDerivAt R.mkQ.toContinuousLinearMap).comp_hasDerivAt
      t (hode t)
    have hderiv : R.mkQ (A (g t) + r t) = Aq (R.mkQ (g t)) := by
      have hr0 : R.mkQ (r t) = 0 :=
        (Submodule.Quotient.mk_eq_zero R).mpr (hr t)
      calc
        R.mkQ (A (g t) + r t) = R.mkQ (A (g t)) + R.mkQ (r t) := map_add _ _ _
        _ = R.mkQ (A (g t)) := by rw [hr0, add_zero]
        _ = Aq (R.mkQ (g t)) := congrFun (congrArg DFunLike.coe hq) (g t)
    exact hd.congr_deriv hderiv
  have hflow := finiteBohl_linear_ode_eq_exp Aq.toContinuousLinearMap
    (fun t => R.mkQ (g t)) hqode
  intro t
  simpa [Aq, _root_.LinearMap.quotientReachableA, R, hg0] using hflow t

/-- **A stable forced component starts in the stabilizable subspace.** If a
stable finite exponential-polynomial signal solves `g' = A g + r` and the
forcing lies pointwise in `range B`, then its initial state belongs to
`Xstab(A,B) = X_g(A) + R(A,B)`. Passing to the uncontrollable quotient removes
the forcing; decay then places the quotient initial state in the Hurwitz
subspace, and `comap_hurwitzSubspace_quotientReachable_eq` lifts it back. -/
theorem stable_forced_component_mem_stabilizableSubspace
    {X U : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace ℂ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup U] [NormedSpace ℝ U]
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (g r : ℝ → X) (hg : LinearSystem.IsStableExponentialPolynomial g)
    (hode : ∀ t, HasDerivAt g (A (g t) + r t) t)
    (hr : ∀ t, r t ∈ _root_.LinearMap.reachableSubspace A B) :
    g 0 ∈ _root_.LinearMap.hurwitzSubspace A ⊔ _root_.LinearMap.reachableSubspace A B := by
  let R := _root_.LinearMap.reachableSubspace A B
  haveI : IsClosed (R : Set X) := R.closed_of_finiteDimensional
  letI : IsTopologicalRing ((X ⧸ R) →L[ℝ] (X ⧸ R)) :=
    { continuous_add := continuous_add
      continuous_mul := Continuous.clm_comp continuous_fst continuous_snd
      continuous_neg := continuous_neg }
  have hflow := finiteBohl_quotient_ode_eq_exp A B g r (g 0) rfl hode hr
  let q : X →L[ℝ] X ⧸ R := R.mkQ.toContinuousLinearMap
  have hqdec : Filter.Tendsto (fun t : ℝ => q (g t)) Filter.atTop (nhds 0) := by
    have h := (q.continuous.tendsto 0).comp hg.tendsto_zero
    simpa only [Function.comp_def, map_zero] using h
  have horbit : Filter.Tendsto
      (fun t : ℝ => NormedSpace.exp
        (t • (_root_.LinearMap.quotientReachableA A B).toContinuousLinearMap)
        (R.mkQ (g 0))) Filter.atTop (nhds 0) := by
    refine hqdec.congr' (Filter.Eventually.of_forall fun t => ?_)
    exact hflow t
  have hquot : R.mkQ (g 0) ∈ _root_.LinearMap.hurwitzSubspace
      (_root_.LinearMap.quotientReachableA A B) :=
    _root_.LinearMap.orbit_decay_mem_hurwitz (_root_.LinearMap.quotientReachableA A B) horbit
  have hcomap : g 0 ∈ Submodule.comap R.mkQ
      (_root_.LinearMap.hurwitzSubspace (_root_.LinearMap.quotientReachableA A B)) :=
    Submodule.mem_comap.mpr hquot
  rw [_root_.LinearMap.comap_hurwitzSubspace_quotientReachable_eq A B] at hcomap
  simpa [R] using hcomap

/-- The range span of a differentiable forced trajectory with zero readout is
a controlled-invariant witness. The derivative remains in this span because
its quotient trajectory is identically zero. This avoids any coefficientwise
realification when the antistable trajectory is already real-valued. -/
theorem forced_curve_initial_mem_controlledInvariantSubspace
    {X U Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (b r : ℝ → X)
    (hode : ∀ t, HasDerivAt b (A (b t) + r t) t)
    (hr : ∀ t, r t ∈ LinearMap.range B)
    (hH : ∀ t, H (b t) = 0) :
    b 0 ∈ LinearMap.controlledInvariantSubspace A B (LinearMap.ker H) := by
  let V : Submodule ℝ X := Submodule.span ℝ (Set.range b)
  haveI : IsClosed (V : Set X) := V.closed_of_finiteDimensional
  have hbV (t : ℝ) : b t ∈ V := Submodule.subset_span ⟨t, rfl⟩
  have hqzero (t : ℝ) : V.mkQ (b t) = 0 :=
    (Submodule.Quotient.mk_eq_zero V).mpr (hbV t)
  have hderivV (t : ℝ) : A (b t) + r t ∈ V := by
    have hd := (ContinuousLinearMap.hasFDerivAt V.mkQ.toContinuousLinearMap).comp_hasDerivAt
      t (hode t)
    have hz : HasDerivAt (fun s : ℝ => V.mkQ (b s)) (0 : X ⧸ V) t := by
      simpa only [hqzero] using (hasDerivAt_const (x := t) (c := (0 : X ⧸ V)))
    have hq : V.mkQ (A (b t) + r t) = 0 := (hd.deriv).symm.trans hz.deriv
    exact (Submodule.Quotient.mk_eq_zero V).mp hq
  have hVker : V ≤ LinearMap.ker H := by
    apply Submodule.span_le.mpr
    rintro x ⟨t, rfl⟩
    exact LinearMap.mem_ker.mpr (hH t)
  have hVmap : ∀ x ∈ V, A x ∈ V ⊔ LinearMap.range B := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨t, rfl⟩
      have hAeq : A (b t) = (A (b t) + r t) - r t := by abel
      rw [hAeq]
      have hv : A (b t) + r t ∈ V ⊔ LinearMap.range B :=
        (le_sup_left : V ≤ V ⊔ LinearMap.range B) (hderivV t)
      have hr' : r t ∈ V ⊔ LinearMap.range B :=
        (le_sup_right : LinearMap.range B ≤ V ⊔ LinearMap.range B) (hr t)
      exact (V ⊔ LinearMap.range B).sub_mem hv hr'
    · simpa using (V ⊔ LinearMap.range B).zero_mem
    · intro x y _ _ hx hy
      simpa only [map_add] using (V ⊔ LinearMap.range B).add_mem hx hy
    · intro c x _ hx
      simpa only [map_smul] using (V ⊔ LinearMap.range B).smul_mem c hx
  have hVctrl : LinearMap.IsControlledInvariant A B V := by
    rw [LinearMap.isControlledInvariant_iff, Submodule.map_le_iff_le_comap]
    exact hVmap
  exact LinearMap.le_controlledInvariantSubspace hVker hVctrl (hbV 0)

end LinearMap

namespace LinearSystem

open Filter
open scoped Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-! ### Stable/antistable decomposition of a decaying forced state

The preceding analytic facts combine without any complex-linearity assumption
on the real state map: a finite-Bohl forcing image makes the whole state
trajectory finite Bohl, and a decaying real-linear readout kills the
antistable state's readout. The remaining `W_g` proof is algebraic: show the
stable initial component lies in `Xstab` and the antistable initial component
lies in `V*(ker H)`. -/

section FiniteBohlStateProjection

variable {X U Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℂ X]
variable [FiniteDimensional ℝ X] [FiniteDimensional ℂ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- A finite-Bohl forcing image upgrades the variation-of-constants ODE from
almost-everywhere to pointwise, even when the input itself is only locally
integrable. -/
theorem variationOfConstants_hasDerivAt_of_finiteBohl_forcing
    (sys : LinearSystem ℝ X U Z) (x₀ : X) (u : ℝ → U)
    (hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume)
    (hBu : IsExponentialPolynomial (fun t : ℝ => sys.continuousB (u t)))
    (t : ℝ) :
    HasDerivAt (sys.variationOfConstants 0 x₀ u)
      (sys.A (sys.variationOfConstants 0 x₀ u t) + sys.B (u t)) t := by
  let x := sys.variationOfConstants 0 x₀ u
  let F : ℝ → X := fun s => sys.continuousA (x s) + sys.continuousB (u s)
  have hx : Continuous x := sys.continuous_variationOfConstants 0 x₀ u hu
  have hF : Continuous F := (sys.continuousA.continuous.comp hx).add hBu.continuous
  have heq (s : ℝ) : x s = x₀ + ∫ r in (0 : ℝ)..s, F r := by
    simpa only [x, F, dynamics, continuousA_apply, continuousB_apply] using
      (sys.variationOfConstants_integral 0 x₀ u hu s)
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hF.intervalIntegrable 0 t)
    hF.aestronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt
  have hd' := (hasDerivAt_const (x := t) (c := x₀)).add hd
  have hderiv : (0 : X) + F t =
      sys.A (sys.variationOfConstants 0 x₀ u t) + sys.B (u t) := by
    simp [F, x, continuousA_apply, continuousB_apply]
  rw [hderiv] at hd'
  exact hd'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => heq s)

private theorem stable_sub_bohl {f g : ℝ → X}
    (hf : IsStableExponentialPolynomial f) (hg : IsStableExponentialPolynomial g) :
    IsStableExponentialPolynomial (f - g) := by
  have hneg : IsStableExponentialPolynomial (-g) := by
    apply hg.isExponentialPolynomial.neg |>.of_tendsto_zero
    change Filter.Tendsto (fun t => -g t) Filter.atTop (nhds 0)
    simpa using hg.tendsto_zero.neg
  have hsum : IsExponentialPolynomial (f + -g) :=
    hf.isExponentialPolynomial.add hneg.isExponentialPolynomial
  have hlim : Filter.Tendsto (f - g) Filter.atTop (nhds 0) := by
    change Filter.Tendsto (fun t => f t - g t) Filter.atTop (nhds 0)
    simpa using hf.tendsto_zero.sub hg.tendsto_zero
  have hfun : f - g = f + -g := by funext t; exact sub_eq_add_neg _ _
  rw [hfun]
  exact hsum.of_tendsto_zero (by simpa [hfun] using hlim)

private theorem antistable_neg_bohl {f : ℝ → X} (hf : IsAntistableBohlSignal f) :
    IsAntistableBohlSignal (-f) := by
  obtain ⟨s, D, a, hfreq, hrepr⟩ := hf
  refine ⟨s, D, fun μ k => -a μ k, hfreq, fun t => ?_⟩
  rw [Pi.neg_apply, hrepr t]
  simp only [Finset.sum_neg_distrib, smul_neg]

private theorem antistable_sub_bohl {f g : ℝ → X}
    (hf : IsAntistableBohlSignal f) (hg : IsAntistableBohlSignal g) :
    IsAntistableBohlSignal (f - g) := by
  have h := hf.add (antistable_neg_bohl hg)
  simpa [sub_eq_add_neg] using h

private theorem hasDerivAt_deriv_exponentialPolynomial {f : ℝ → X}
    (hf : IsExponentialPolynomial f) (t : ℝ) : HasDerivAt f (deriv f t) t := by
  obtain ⟨s, D, a, hrepr⟩ := hf
  have h := hasDerivAt_sum_exp_mul_sum_pow_smul s D a t
  have h' := h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => hrepr r)
  exact h'.congr_deriv h'.deriv.symm

private theorem stable_deriv_bohl {f : ℝ → X} (hf : IsStableExponentialPolynomial f) :
    IsStableExponentialPolynomial (fun t => deriv f t) := by
  obtain ⟨s, D, a, hfreq, hrepr⟩ := hf
  let d : ℂ → ℕ → X := fun μ k =>
    μ • a μ k + if k < D then ((k + 1 : ℕ) : ℂ) • a μ (k + 1) else 0
  refine ⟨s, D, d, hfreq, fun t => ?_⟩
  have h := hasDerivAt_sum_exp_mul_sum_pow_smul s D a t
  have h' := h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => hrepr r)
  simpa [d] using h'.deriv

private theorem antistable_deriv_bohl {f : ℝ → X} (hf : IsAntistableBohlSignal f) :
    IsAntistableBohlSignal (fun t => deriv f t) := by
  obtain ⟨s, D, a, hfreq, hrepr⟩ := hf
  let d : ℂ → ℕ → X := fun μ k =>
    μ • a μ k + if k < D then ((k + 1 : ℕ) : ℂ) • a μ (k + 1) else 0
  refine ⟨s, D, d, hfreq, fun t => ?_⟩
  have h := hasDerivAt_sum_exp_mul_sum_pow_smul s D a t
  have h' := h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun r => hrepr r)
  simpa [d] using h'.deriv

/-- For a real-linear forced ODE, the stable and antistable state components
have range-valued ODE residuals separately whenever the full forcing takes
values in a complex subspace. Quotienting by that subspace and using
stable/antistable non-cancellation avoids complexifying the generator. -/
theorem stable_antistable_ode_residuals_mem_submodule
    (A : X →L[ℝ] X) (S : Submodule ℂ X)
    {f r g b : ℝ → X}
    (hfb : f = g + b)
    (hg : IsStableExponentialPolynomial g)
    (hb : IsAntistableBohlSignal b)
    (hode : ∀ t, HasDerivAt f (A (f t) + r t) t)
    (hrange : ∀ t, r t ∈ S) :
    (∀ t, deriv g t - A (g t) ∈ S) ∧
      (∀ t, deriv b t - A (b t) ∈ S) ∧
      (∀ t, HasDerivAt g (A (g t) + (deriv g t - A (g t))) t) ∧
      (∀ t, HasDerivAt b (A (b t) + (deriv b t - A (b t))) t) := by
  classical
  haveI : IsClosed (S : Set X) := S.closed_of_finiteDimensional
  let q : X →L[ℂ] X ⧸ S := S.mkQ.toContinuousLinearMap
  let rg : ℝ → X := fun t => deriv g t - A (g t)
  let rb : ℝ → X := fun t => deriv b t - A (b t)
  have hAg : IsStableExponentialPolynomial (fun t => A (g t)) := by
    have hEP : IsExponentialPolynomial (fun t => A (g t)) :=
      hg.isExponentialPolynomial.map_realLinear A
    have hlim : Filter.Tendsto (fun t => A (g t)) Filter.atTop (nhds 0) := by
      simpa only [Function.comp_def, map_zero] using
        (A.continuous.tendsto 0).comp hg.tendsto_zero
    exact hEP.of_tendsto_zero hlim
  have hAb : IsAntistableBohlSignal (fun t => A (b t)) := hb.map_realLinear A
  have hrg : IsStableExponentialPolynomial rg := by
    change IsStableExponentialPolynomial ((fun t => deriv g t) - (fun t => A (g t)))
    exact stable_sub_bohl (stable_deriv_bohl hg) hAg
  have hrb : IsAntistableBohlSignal rb := by
    change IsAntistableBohlSignal ((fun t => deriv b t) - (fun t => A (b t)))
    exact antistable_sub_bohl (antistable_deriv_bohl hb) hAb
  have hodeSplit : ∀ t, deriv f t = deriv g t + deriv b t := by
    intro t
    have hg' := hasDerivAt_deriv_exponentialPolynomial hg.isExponentialPolynomial t
    have hb' := hasDerivAt_deriv_exponentialPolynomial hb.isExponentialPolynomial t
    have hsum := hg'.add hb'
    have hsum' := hsum.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => congrFun hfb s)
    exact hsum'.deriv
  have hforceDecomp : r = rg + rb := by
    funext t
    have hcoeff : deriv g t + deriv b t = A (g t) + A (b t) + r t := by
      have h := (hode t).deriv
      rw [congrFun hfb t] at h
      change deriv f t = A (g t + b t) + r t at h
      rw [map_add] at h
      rw [hodeSplit t] at h
      exact h
    have hcoeff' : r t + (A (g t) + A (b t)) = deriv g t + deriv b t := by
      rw [hcoeff]
      abel
    have hsub : r t = deriv g t + deriv b t - (A (g t) + A (b t)) :=
      (eq_sub_iff_add_eq).2 hcoeff'
    dsimp [rg, rb]
    rw [hsub]
    abel
  have hqSum : (fun t => q (rg t)) + (fun t => q (rb t)) = 0 := by
    funext t
    calc
      q (rg t) + q (rb t) = q (rg t + rb t) := by rw [map_add]
      _ = q (r t) := by
        congr 1
        calc
          rg t + rb t = (rg + rb) t := rfl
          _ = r t := congrFun hforceDecomp.symm t
      _ = 0 := (Submodule.Quotient.mk_eq_zero S).2 (hrange t)
  have hqg : IsStableExponentialPolynomial (fun t => q (rg t)) := by
    have hEP := hrg.isExponentialPolynomial.map q
    have hlim : Filter.Tendsto (fun t => q (rg t)) Filter.atTop (nhds 0) := by
      have h := (q.continuous.tendsto 0).comp hrg.tendsto_zero
      simpa only [Function.comp_def, map_zero] using h
    exact hEP.of_tendsto_zero hlim
  have hqb : IsAntistableBohlSignal (fun t => q (rb t)) := hrb.map q.toLinearMap
  have hqb0 : (fun t => q (rb t)) = 0 :=
    eq_zero_of_eq_stable_add_antistable_of_tendsto_zero
      hqSum.symm hqg hqb tendsto_const_nhds
  have hqg0 : (fun t => q (rg t)) = 0 := by
    funext t
    have hs := congrFun hqSum t
    have hb0 := congrFun hqb0 t
    have hs' : q (rg t) + q (rb t) = 0 := by simpa using hs
    have hb0' : q (rb t) = 0 := by simpa using hb0
    rw [hb0', add_zero] at hs'
    exact hs'
  have hr_mem : ∀ t, rg t ∈ S ∧ rb t ∈ S := by
    intro t
    exact ⟨(Submodule.Quotient.mk_eq_zero S).mp (congrFun hqg0 t),
      (Submodule.Quotient.mk_eq_zero S).mp (congrFun hqb0 t)⟩
  have hderivG (t : ℝ) : HasDerivAt g (deriv g t) t :=
    hasDerivAt_deriv_exponentialPolynomial hg.isExponentialPolynomial t
  have hderivB (t : ℝ) : HasDerivAt b (deriv b t) t :=
    hasDerivAt_deriv_exponentialPolynomial hb.isExponentialPolynomial t
  refine ⟨fun t => (hr_mem t).1, fun t => (hr_mem t).2, ?_, ?_⟩
  · intro t
    have heq : deriv g t = A (g t) + rg t := by
      dsimp [rg]
      abel
    exact (hderivG t).congr_deriv heq
  · intro t
    have heq : deriv b t = A (b t) + rb t := by
      dsimp [rb]
      abel
    exact (hderivB t).congr_deriv heq

/-- The two projected forced ODEs are sufficient for the finite-Bohl `W_g`
necessity conclusion: the stable initial component is stabilizable, while the
zero-readout antistable component lies in a controlled invariant subspace. -/
theorem mem_outputStabilizableSubspace_of_projected_forced_state
    (sys : LinearSystem ℝ X U Z) (H : X →ₗ[ℝ] Z) (x₀ : X)
    (g b r_g r_b : ℝ → X)
    (hsplit : x₀ = g 0 + b 0)
    (hg : IsStableExponentialPolynomial g)
    (hode_g : ∀ t, HasDerivAt g (sys.A (g t) + r_g t) t)
    (hr_g : ∀ t, r_g t ∈ _root_.LinearMap.reachableSubspace sys.A sys.B)
    (hode_b : ∀ t, HasDerivAt b (sys.A (b t) + r_b t) t)
    (hr_b : ∀ t, r_b t ∈ _root_.LinearMap.range sys.B)
    (hHb : ∀ t, H (b t) = 0) :
    x₀ ∈ outputStabilizableSubspace sys.A sys.B H := by
  have hgmem : g 0 ∈ _root_.LinearMap.stabilizableSubspace sys.A sys.B := by
    exact _root_.LinearMap.stable_forced_component_mem_stabilizableSubspace
      sys.A sys.B g r_g hg hode_g hr_g
  have hbmem : b 0 ∈ _root_.LinearMap.controlledInvariantSubspace
      sys.A sys.B (_root_.LinearMap.ker H) :=
    _root_.LinearMap.forced_curve_initial_mem_controlledInvariantSubspace
      sys.A sys.B H b r_b hode_b hr_b hHb
  rw [outputStabilizableSubspace, hsplit, add_comm]
  exact Submodule.add_mem_sup hbmem hgmem

/-- **State-level finite-Bohl projection under real-linear readout.** If the
system's forcing image is a finite exponential polynomial and the controlled
readout tends to zero, the forced state trajectory decomposes into a stable
finite-Bohl component and an antistable component whose readout is pointwise
zero. No complex-linear extension of `sys.A` or `H` is assumed. -/
theorem finiteBohl_state_stable_antistable_decomposition
    (sys : LinearSystem ℝ X U Z) (H : X →ₗ[ℝ] Z) (x₀ : X) (u : ℝ → U)
    (hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume)
    (hBu : IsExponentialPolynomial (fun t : ℝ => sys.continuousB (u t)))
    (hdec : Filter.Tendsto
      (fun t : ℝ => H (sys.variationOfConstants 0 x₀ u t)) Filter.atTop (nhds 0)) :
    ∃ g b : ℝ → X,
      sys.variationOfConstants 0 x₀ u = g + b ∧
      IsStableExponentialPolynomial g ∧ IsAntistableBohlSignal b ∧
      Filter.Tendsto g Filter.atTop (nhds 0) ∧ ∀ t, H (b t) = 0 := by
  have htraj : IsExponentialPolynomial (sys.variationOfConstants 0 x₀ u) :=
    variationOfConstants_isExponentialPolynomial_of_realLinear (sys := sys) x₀ u hu hBu
  exact htraj.exists_stable_add_antistable_of_tendsto_realLinear
    H.toContinuousLinearMap hdec

end FiniteBohlStateProjection

section FiniteBohlReadout

variable {U Y : Type*}
variable [NormedAddCommGroup U] [NormedSpace ℂ U]
variable [NormedAddCommGroup Y] [NormedSpace ℂ Y]

/-- **Finite-Bohl stable/antistable decomposition of the forced readout.** Under
the explicit complexification hypotheses of `variationOfConstants_transport_of_
complexification` (finite-dimensional complex state and input spaces, complex-linear
`Aℂ`, `Bℂ`, `Cℂ` whose real restrictions are `sys.A`, `sys.B`, `sys.C`), a locally
integrable input whose `Bℂ`-image is a finite Bohl signal produces a forced readout
that splits into a stable part and an antistable part.

This is the transported real finite-Bohl trajectory theorem fed into the spectral
projection `IsExponentialPolynomial.exists_stable_add_antistable`: the readout is a
finite exponential polynomial by the transport theorem, and its frequency set is
split by the sign of the real part. -/
theorem finiteBohl_readout_stable_antistable_decomposition
    [FiniteDimensional ℂ X] [FiniteDimensional ℂ U]
    (sys : LinearSystem ℝ X U Y) (Aℂ : X →ₗ[ℂ] X) (Bℂ : U →ₗ[ℂ] X) (Cℂ : X →ₗ[ℂ] Y)
    (hA : Aℂ.restrictScalars ℝ = sys.A) (hB : Bℂ.restrictScalars ℝ = sys.B)
    (hC : Cℂ.restrictScalars ℝ = sys.C)
    (t₀ : ℝ) (x₀ : X) (u : ℝ → U)
    (hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume)
    (hBohl : IsExponentialPolynomial (fun t : ℝ => Bℂ (u t))) :
    ∃ g b : ℝ → Y,
      (fun t : ℝ => sys.C (sys.variationOfConstants t₀ x₀ u t)) = g + b ∧
      IsStableExponentialPolynomial g ∧ IsAntistableBohlSignal b := by
  have hreadout : IsExponentialPolynomial
      (fun t : ℝ => sys.C (sys.variationOfConstants t₀ x₀ u t)) :=
    (variationOfConstants_transport_of_complexification sys Aℂ Bℂ Cℂ hA hB hC
      t₀ x₀ u hu hBohl).2.1
  exact hreadout.exists_stable_add_antistable

/-- **Finite-Bohl quotient non-cancellation.** Let `sys : LinearSystem ℝ X U Y` be a
real system whose state map, input map and readout are the real restrictions of
complex-linear maps `Aℂ`, `Bℂ`, `Cℂ`, with `[FiniteDimensional ℂ X]` and
`[FiniteDimensional ℂ U]`. If the input `u` is locally integrable and its
`Bℂ`-image is a finite Bohl signal, then the forced readout is a finite exponential
polynomial, and whenever it tends to `0` at `+∞` its antistable quotient component
vanishes: there is a stable part `g` and an antistable part `b` with
`C x_u = g + b`, `g` stable, `b` antistable, and `b = 0`.

The reachable-subspace quotient is carried by the finite-Bohl input-image hypothesis:
the whole reachable forcing `t ↦ exp((t-t₀)Aℂ)(Bℂ u(t))` is a finite exponential
polynomial, so the projection sees the forced trajectory and not only its autonomous
orbit. This is the strongest statement for the finite-Bohl class; the unrestricted
locally-integrable `W_g` necessity is deliberately not claimed. -/
theorem finiteBohl_readout_antistable_eq_zero_of_tendsto_zero
    [FiniteDimensional ℂ X] [FiniteDimensional ℂ U]
    (sys : LinearSystem ℝ X U Y) (Aℂ : X →ₗ[ℂ] X) (Bℂ : U →ₗ[ℂ] X) (Cℂ : X →ₗ[ℂ] Y)
    (hA : Aℂ.restrictScalars ℝ = sys.A) (hB : Bℂ.restrictScalars ℝ = sys.B)
    (hC : Cℂ.restrictScalars ℝ = sys.C)
    (t₀ : ℝ) (x₀ : X) (u : ℝ → U)
    (hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume)
    (hBohl : IsExponentialPolynomial (fun t : ℝ => Bℂ (u t)))
    (hdec : Filter.Tendsto
      (fun t : ℝ => sys.C (sys.variationOfConstants t₀ x₀ u t)) Filter.atTop (nhds 0)) :
    ∃ g b : ℝ → Y,
      (fun t : ℝ => sys.C (sys.variationOfConstants t₀ x₀ u t)) = g + b ∧
      IsStableExponentialPolynomial g ∧ IsAntistableBohlSignal b ∧ b = 0 := by
  obtain ⟨g, b, hgb, hg, hb⟩ :=
    finiteBohl_readout_stable_antistable_decomposition sys Aℂ Bℂ Cℂ hA hB hC
      t₀ x₀ u hu hBohl
  exact ⟨g, b, hgb, hg, hb,
    eq_zero_of_eq_stable_add_antistable_of_tendsto_zero hgb hg hb hdec⟩

/-- **The decaying finite-Bohl readout is stable.** The stable reformulation of
`finiteBohl_readout_antistable_eq_zero_of_tendsto_zero`: under the same
transport, finite-Bohl and finite-dimensional hypotheses, a decaying forced
readout admits a representation with all frequencies in the open left half-plane.
This is the compact form in which the finite-Bohl non-cancellation composes with
the accepted quotient/readout APIs. -/
theorem finiteBohl_readout_isStable_of_tendsto_zero
    [FiniteDimensional ℂ X] [FiniteDimensional ℂ U]
    (sys : LinearSystem ℝ X U Y) (Aℂ : X →ₗ[ℂ] X) (Bℂ : U →ₗ[ℂ] X) (Cℂ : X →ₗ[ℂ] Y)
    (hA : Aℂ.restrictScalars ℝ = sys.A) (hB : Bℂ.restrictScalars ℝ = sys.B)
    (hC : Cℂ.restrictScalars ℝ = sys.C)
    (t₀ : ℝ) (x₀ : X) (u : ℝ → U)
    (hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume)
    (hBohl : IsExponentialPolynomial (fun t : ℝ => Bℂ (u t)))
    (hdec : Filter.Tendsto
      (fun t : ℝ => sys.C (sys.variationOfConstants t₀ x₀ u t)) Filter.atTop (nhds 0)) :
    IsStableExponentialPolynomial
      (fun t : ℝ => sys.C (sys.variationOfConstants t₀ x₀ u t)) := by
  have hreadout : IsExponentialPolynomial
      (fun t : ℝ => sys.C (sys.variationOfConstants t₀ x₀ u t)) :=
    (variationOfConstants_transport_of_complexification sys Aℂ Bℂ Cℂ hA hB hC
      t₀ x₀ u hu hBohl).2.1
  exact hreadout.of_tendsto_zero hdec

end FiniteBohlReadout

/-! ## The finite-Bohl forcing-image version of Theorem 4.37

Trentelman–Stoorvogel–Hautus, Theorem 4.37 (PDF page 115 / printed page 99)
states the output-stabilizable set `W_g(ker H)` for **Bohl inputs**:

`W_g(ker H) = {x | ∃ Bohl input u, H x_u(·, x) is stable} = V*(ker H) + Xstab(A, B)`.

The predicate `LinearSystem.IsOutputStabilizable` of this file quantifies over an
*arbitrary* locally integrable input. The predicate `IsBohlOutputStabilizable`
below is a finite-Bohl forcing-image variant, kept deliberately distinct: the
input is required to be locally integrable and its `Bℂ`-image to be a finite exponential
polynomial, the representation hypothesis consumed by the finite-Bohl state
projection. The complex-linear input map
`Bℂ : U →ₗ[ℂ] X` comes with the compatibility equality
`hB : Bℂ.restrictScalars ℝ = sys.B`, so its represented Bohl signal is exactly
the actual system forcing `sys.B (u t)`. This equality is explicit because the
finite-Bohl class is a complex class. The book puts the Bohl condition on `u`
itself; in finite dimension a linear section of `B` on its range should lift a
Bohl forcing image to a Bohl input with the same forcing, but that equivalence is
not formalized here. The state and input use the real scalar structures induced
by their complex normed spaces; no complex-linear extension of the real state
map `A` is needed for the necessity proof.

The two directions of the forcing-image characterization are recorded as
separately named propositions (`FiniteBohlWBridge`, `FiniteBohlSynthesis`) and
proved below. This keeps the restricted statement distinct from the unrestricted
`mem_outputStabilizableSubspace_of_isOutputStabilizable`, which is *not* claimed.
Identifying the forcing-image class
with the book's Bohl-input set still requires the finite-dimensional lifting
lemma described above. -/

section FiniteBohlWg

variable {X U Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℂ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- **The finite-Bohl forcing-image open-loop predicate.** A state `x` lies in
the encoded forcing-image variant of `W_g(ker H)` when there is a locally integrable input `u` whose
`Bℂ`-image is a finite exponential polynomial and whose controlled output of the
variation-of-constants trajectory decays: `t ↦ H (x_u(t, x)) → 0`.

This is a finite-Bohl forcing-image restriction of
`LinearSystem.IsOutputStabilizable`; the
complexification map `Bℂ : U →ₗ[ℂ] X` records the representation hypothesis of
the accepted transport layer. Source: Trentelman–Stoorvogel–Hautus, equation
(4.28) together with Definition 2.5 (Bohl functions). -/
def IsBohlOutputStabilizable (sys : LinearSystem ℝ X U Z) (Bℂ : U →ₗ[ℂ] X)
    (hB : Bℂ.restrictScalars ℝ = sys.B) (H : X →ₗ[ℝ] Z) (x : X) : Prop :=
  ∃ u : ℝ → U, MeasureTheory.LocallyIntegrable u MeasureTheory.volume ∧
    IsExponentialPolynomial (fun t : ℝ => Bℂ (u t)) ∧
    Filter.Tendsto (fun t : ℝ => H (sys.variationOfConstants 0 x u t))
      Filter.atTop (nhds 0)

/-- The finite-Bohl predicate is a restriction of the arbitrary-locally-integrable
predicate `IsOutputStabilizable`: forgetting the finite-Bohl input hypothesis
keeps the same locally integrable witness and the same decay. This is the formal
record that the book's Theorem 4.37 statement is *weaker* than the unrestricted
extension. -/
theorem IsBohlOutputStabilizable.isOutputStabilizable {sys : LinearSystem ℝ X U Z}
    {Bℂ : U →ₗ[ℂ] X} {hB : Bℂ.restrictScalars ℝ = sys.B}
    {H : X →ₗ[ℝ] Z} {x : X}
    (h : IsBohlOutputStabilizable sys Bℂ hB H x) : IsOutputStabilizable sys H x :=
  ⟨h.choose, h.choose_spec.1, h.choose_spec.2.2⟩

/-- **The finite-Bohl forcing-image set is closed under addition.** If `u`
stabilizes `x` and `v` stabilizes `y`, then `u + v` stabilizes `x + y`; the
`Bℂ`-image of `u + v` is the finite sum of the two finite Bohl signals, hence a
finite Bohl signal. This proves additivity of the encoded forcing-image class. -/
theorem IsBohlOutputStabilizable.add {sys : LinearSystem ℝ X U Z} {Bℂ : U →ₗ[ℂ] X}
    {hB : Bℂ.restrictScalars ℝ = sys.B} {H : X →ₗ[ℝ] Z} {x y : X}
    (hx : IsBohlOutputStabilizable sys Bℂ hB H x)
    (hy : IsBohlOutputStabilizable sys Bℂ hB H y) :
    IsBohlOutputStabilizable sys Bℂ hB H (x + y) := by
  obtain ⟨u, hu, hBu, hux⟩ := hx
  obtain ⟨v, hv, hBv, hvy⟩ := hy
  refine ⟨u + v, hu.add hv, ?_, ?_⟩
  · have hfun : (fun t : ℝ => Bℂ ((u + v) t)) =
        fun t : ℝ => Bℂ (u t) + Bℂ (v t) := by
      funext t
      rw [Pi.add_apply, map_add]
    rw [hfun]
    exact hBu.add hBv
  · have htraj : ∀ t : ℝ, sys.variationOfConstants 0 (x + y) (u + v) t =
        sys.variationOfConstants 0 x u t + sys.variationOfConstants 0 y v t := by
      intro t
      rw [variationOfConstants_eq, variationOfConstants_eq, variationOfConstants_eq]
      have hfor : (∫ s in (0 : ℝ)..t, sys.forcing 0 (u + v) s) =
          (∫ s in (0 : ℝ)..t, sys.forcing 0 u s) +
            (∫ s in (0 : ℝ)..t, sys.forcing 0 v s) := by
        rw [show sys.forcing 0 (u + v) = sys.forcing 0 u + sys.forcing 0 v from
          forcing_add sys u v]
        exact intervalIntegral.integral_add
          (intervalIntegrable_forcing sys 0 hu 0 t)
          (intervalIntegrable_forcing sys 0 hv 0 t)
      rw [hfor]
      have harg : x + y + ((∫ s in (0 : ℝ)..t, sys.forcing 0 u s) +
          (∫ s in (0 : ℝ)..t, sys.forcing 0 v s)) =
          (x + ∫ s in (0 : ℝ)..t, sys.forcing 0 u s) +
            (y + ∫ s in (0 : ℝ)..t, sys.forcing 0 v s) := by abel
      rw [harg, map_add]
    have hfun : (fun t : ℝ => H (sys.variationOfConstants 0 (x + y) (u + v) t)) =
        fun t : ℝ => H (sys.variationOfConstants 0 x u t) +
          H (sys.variationOfConstants 0 y v t) := by
      funext t
      rw [htraj t, map_add]
    rw [hfun]
    simpa using hux.add hvy

/-- **The finite-Bohl-forcing-image `W_g` bridge (necessity direction).** This
names the necessity direction of the forcing-image variant of the book's
Theorem 4.37: a finite Bohl forcing image whose controlled output decays keeps the state inside
`W_g(ker H) = V*(ker H) + Xstab(A, B)`. It is the finite-Bohl spectral projection
form of `mem_outputStabilizableSubspace_of_isOutputStabilizable`, isolated as a
named proposition so it is not confused with the unrestricted locally-integrable
statement. It is proved by `finiteBohlWBridge` below. The argument `hB` fixes the complex input map
to the system's actual input map. -/
def FiniteBohlWBridge (sys : LinearSystem ℝ X U Z) (Bℂ : U →ₗ[ℂ] X)
    (hB : Bℂ.restrictScalars ℝ = sys.B) (H : X →ₗ[ℝ] Z) : Prop :=
  ∀ x : X, IsBohlOutputStabilizable sys Bℂ hB H x →
    x ∈ outputStabilizableSubspace sys.A sys.B H

/-- The finite-Bohl forcing-image necessity direction of Theorem 4.37.
The state response is split into stable and antistable Bohl parts. Their ODE
residuals are separately in `range Bℂ` by quotient non-cancellation; the
stable part starts in `Xstab`, and the zero-readout antistable part generates
a controlled-invariant subspace of `ker H`. -/
theorem finiteBohlWBridge [FiniteDimensional ℂ X]
    (sys : LinearSystem ℝ X U Z) (Bℂ : U →ₗ[ℂ] X)
    (hB : Bℂ.restrictScalars ℝ = sys.B) (H : X →ₗ[ℝ] Z) :
    FiniteBohlWBridge sys Bℂ hB H := by
  intro x hx
  obtain ⟨u, hu, hBu, hdec⟩ := hx
  have hBpoint (v : U) : Bℂ v = sys.B v := by
    have h := congrFun (congrArg DFunLike.coe hB) v
    exact h
  have hBu' : IsExponentialPolynomial (fun t : ℝ => sys.continuousB (u t)) := by
    convert hBu using 1
    funext t
    rw [continuousB_apply]
    exact (hBpoint (u t)).symm
  have hdecomp : ∃ g b : ℝ → X,
      sys.variationOfConstants 0 x u = g + b ∧
      IsStableExponentialPolynomial g ∧ IsAntistableBohlSignal b ∧
      Filter.Tendsto g Filter.atTop (nhds 0) ∧ ∀ t, H (b t) = 0 :=
    finiteBohl_state_stable_antistable_decomposition (X := X) (U := U) (Z := Z)
      sys H x u hu hBu' hdec
  obtain ⟨g, b, hsplit, hg, hb, _, hHb⟩ := hdecomp
  have hode : ∀ t, HasDerivAt (sys.variationOfConstants 0 x u)
      (sys.continuousA (sys.variationOfConstants 0 x u t) + sys.B (u t)) t := by
    intro t
    simpa only [continuousA_apply] using
      variationOfConstants_hasDerivAt_of_finiteBohl_forcing sys x u hu hBu' t
  have hrange : ∀ t, sys.B (u t) ∈ LinearMap.range Bℂ := by
    intro t
    exact ⟨u t, hBpoint (u t)⟩
  have hres := stable_antistable_ode_residuals_mem_submodule
    sys.continuousA (LinearMap.range Bℂ) hsplit hg hb hode hrange
  let rg : ℝ → X := fun t => deriv g t - sys.A (g t)
  let rb : ℝ → X := fun t => deriv b t - sys.A (b t)
  have hrangeReal (z : X) (hz : z ∈ LinearMap.range Bℂ) : z ∈ LinearMap.range sys.B := by
    obtain ⟨v, hv⟩ := hz
    exact ⟨v, (hBpoint v).symm.trans hv⟩
  have hrg : ∀ t, rg t ∈ LinearMap.reachableSubspace sys.A sys.B := by
    intro t
    exact LinearMap.range_le_reachableSubspace sys.A sys.B
      (hrangeReal _ (hres.1 t))
  have hrb : ∀ t, rb t ∈ LinearMap.range sys.B := by
    intro t
    exact hrangeReal _ (hres.2.1 t)
  have hodeg : ∀ t, HasDerivAt g (sys.A (g t) + rg t) t := by
    intro t
    simpa only [continuousA_apply] using hres.2.2.1 t
  have hodeb : ∀ t, HasDerivAt b (sys.A (b t) + rb t) t := by
    intro t
    simpa only [continuousA_apply] using hres.2.2.2 t
  have hstart : x = g 0 + b 0 := by
    have hzero : sys.variationOfConstants 0 x u 0 = x := by
      simp [variationOfConstants]
    calc
      x = sys.variationOfConstants 0 x u 0 := hzero.symm
      _ = g 0 + b 0 := congrFun hsplit 0
  exact mem_outputStabilizableSubspace_of_projected_forced_state
    sys H x g b rg rb hstart hg hodeg hrg hodeb hrb hHb

/-- **The finite-Bohl synthesis direction.** Every state in
`W_g(ker H) = V*(ker H) + Xstab(A, B)` admits a *finite Bohl* stabilizing input:
the state feedback `F` of
`exists_feedback_tendsto_readout_of_mem_outputStabilizableSubspace`, read as an
open-loop input along its own closed-loop orbit, is finite Bohl. This is the
constructive direction of the book's Theorem 4.37, proved by
`finiteBohlSynthesis` below. -/
def FiniteBohlSynthesis (sys : LinearSystem ℝ X U Z) (Bℂ : U →ₗ[ℂ] X)
    (hB : Bℂ.restrictScalars ℝ = sys.B) (H : X →ₗ[ℝ] Z) : Prop :=
  ∀ x : X, x ∈ outputStabilizableSubspace sys.A sys.B H →
    IsBohlOutputStabilizable sys Bℂ hB H x

/-- **The finite-Bohl forcing-image version of Theorem 4.37.** Under the two named
finite-Bohl obligations — the spectral-projection necessity `FiniteBohlWBridge`
and the constructive synthesis `FiniteBohlSynthesis` — the finite-Bohl
output-stabilizable set is exactly `W_g(ker H) = V*(ker H) + Xstab(A, B)`.

This is a forcing-image variant of the book statement. The book's Bohl-input
form is equivalent once the finite-dimensional Bohl lifting lemma is supplied;
the same-carrier complex scalar structures and restriction equality are explicit
here. The unrestricted predicate theorem
`mem_outputStabilizableSubspace_of_isOutputStabilizable` is *not* claimed, and
neither bridge is identified with it. -/
theorem isBohlOutputStabilizable_iff_mem_outputStabilizableSubspace
    (sys : LinearSystem ℝ X U Z) (Bℂ : U →ₗ[ℂ] X)
    (hB : Bℂ.restrictScalars ℝ = sys.B) (H : X →ₗ[ℝ] Z)
    (hbridge : FiniteBohlWBridge sys Bℂ hB H)
    (hsynth : FiniteBohlSynthesis sys Bℂ hB H) (x : X) :
    IsBohlOutputStabilizable sys Bℂ hB H x ↔
      x ∈ outputStabilizableSubspace sys.A sys.B H :=
  ⟨hbridge x, hsynth x⟩

end FiniteBohlWg

/-! ## Discharging the finite-Bohl synthesis obligation

The finite-Bohl forcing-image `W_g` package of the previous section names the
constructive direction of Trentelman–Stoorvogel–Hautus Theorem 4.37 as the
obligation `FiniteBohlSynthesis`: every state of the algebraic
`W_g(ker H) = V*(ker H) + Xstab(A, B)` admits a locally integrable input whose
`Bℂ`-image is a finite Bohl signal and whose controlled readout decays.

This section discharges that obligation. The accepted real state-feedback
characterization produces, for `x ∈ W_g(ker H)`, a real gain `F` with
`t ↦ H (exp (t (A + B F)) x) → 0`. The input `u t = F (exp (t (A + B F)) x)`
then produces the same decay after the open-loop/closed-loop identification
`variationOfConstants_feedback_eq_expFlow`, and its `Bℂ`-image is finite Bohl
because `Bℂ ∘ F` is an arbitrary real-linear map and real-linear maps preserve
the finite Bohl class (`IsExponentialPolynomial.map_realLinear`), applied to the
closed-loop exponential orbit. The orbit itself is finite Bohl for an
*arbitrary* real-linear generator by
`isExponentialPolynomial_expFlow_of_realLinear`, which complexifies the real
orbit through a real basis and the coordinatewise inclusion `ofRealPi` and then
projects back with the real-linear real-part map. This is the missing real-orbit
step; it does not use any spectral hypothesis on `A`. -/

section FiniteBohlSynthesisAssembly

open scoped Matrix

variable {X U Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℂ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

set_option maxHeartbeats 800000 in
-- Heavy basis/complexification argument; the default heartbeat budget is insufficient.
/-- **The orbit of an arbitrary real-linear generator is finite Bohl.** For a
real-linear endomorphism `A` of a finite-dimensional complex normed space `X`
and any `x : X`, the exponential orbit `t ↦ exp (t A) x` is a finite sum of
polynomial-times-exponential modes.

The proof chooses a real basis `b` of `X`, writes the orbit in the real
coordinates `Fin n → ℝ`, complexifies the coordinate matrix to a complex-linear
map `h` on `Fin n → ℂ`, and observes that the coordinatewise inclusion
`ofRealPi` intertwines the real exponential with the complex one
(`LinearMap.ofRealPi_exp`). The complex orbit is finite Bohl by
`expFlow_isExponentialPolynomial`, and the real orbit is recovered by the
*real-linear* real-part projection `Fin n → ℂ → X`, so the real-linear closure
`IsExponentialPolynomial.map_realLinear` transports the class back. -/
theorem isExponentialPolynomial_expFlow_of_realLinear
    (A : X →ₗ[ℝ] X) (x : X) :
    IsExponentialPolynomial (fun t : ℝ => NormedSpace.exp (t • A.toContinuousLinearMap) x) := by
  let n : ℕ := Module.finrank ℝ X
  let b : Module.Basis (Fin n) ℝ X := Module.finBasis ℝ X
  let L : X ≃L[ℝ] (Fin n → ℝ) := b.equivFun.toContinuousLinearEquiv
  let M : Matrix (Fin n) (Fin n) ℝ := LinearMap.toMatrix b b A
  let g : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := (Matrix.toLin' M).toContinuousLinearMap
  let h : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := Matrix.toLin' (M.map (algebraMap ℝ ℂ))
  have hg : g = L.conjContinuousAlgEquiv A.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro y
    have hrepr : M *ᵥ b.repr (L.symm y) = b.repr (A (L.symm y)) :=
      LinearMap.toMatrix_mulVec_repr b b A (L.symm y)
    have hLy : b.repr (L.symm y) = y := by
      rw [← Module.Basis.equivFun_apply b (L.symm y)]
      exact b.equivFun.apply_symm_apply y
    rw [hLy] at hrepr
    change M *ᵥ y = L (A.toContinuousLinearMap (L.symm y))
    rw [hrepr]
    rw [← Module.Basis.equivFun_apply b (A (L.symm y))]
    rfl
  have hLexp : ∀ t : ℝ, L (NormedSpace.exp (t • A.toContinuousLinearMap) x)
      = NormedSpace.exp (t • g) (L x) := by
    intro t
    have key := NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (L.conjContinuousAlgEquiv)
      (L.conjContinuousAlgEquiv).continuous (t • A.toContinuousLinearMap)
      ((NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _)
    have hcongr : (L.conjContinuousAlgEquiv) (t • A.toContinuousLinearMap) = t • g := by
      rw [map_smul, hg.symm]
    have := congrArg (fun f : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => f (L x)) key
    rw [hcongr] at this
    simpa [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply, g] using this
  have hz : IsExponentialPolynomial
      (fun t : ℝ =>
        LinearMap.ofRealPi (L (NormedSpace.exp (t • A.toContinuousLinearMap) x))) := by
    have h1 : (fun t : ℝ =>
          LinearMap.ofRealPi (L (NormedSpace.exp (t • A.toContinuousLinearMap) x)))
        = fun t : ℝ =>
          NormedSpace.exp (t • h.toContinuousLinearMap) (LinearMap.ofRealPi (L x)) := by
      funext t
      rw [hLexp t, LinearMap.ofRealPi_exp M t (L x)]
    rw [h1]
    exact expFlow_isExponentialPolynomial h (LinearMap.ofRealPi (L x))
  let rePi : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun z i => (z i).re
      map_add' := by intro z w; ext i; simp
      map_smul' := by intro r z; ext i; simp }
  let R : (Fin n → ℂ) →ₗ[ℝ] X := L.symm.toLinearMap.comp rePi
  have hR : (fun t : ℝ =>
        R (LinearMap.ofRealPi (L (NormedSpace.exp (t • A.toContinuousLinearMap) x))))
      = fun t : ℝ => NormedSpace.exp (t • A.toContinuousLinearMap) x := by
    funext t
    simp [R, rePi, LinearMap.ofRealPi]
  rw [← hR]
  exact hz.map_realLinear R.toContinuousLinearMap

set_option maxHeartbeats 800000 in
-- The FTC and uniqueness assembly exceeds the default heartbeat budget.
/-- **The feedback input drives the closed-loop orbit.** For a real gain `F`, the
open-loop variation-of-constants trajectory with input
`u t = F (exp (t (A + B F)) x)` is exactly the closed-loop exponential orbit
`t ↦ exp (t (A + B F)) x`. Both curves are continuous solutions of the same
integral equation `y t = x + ∫₀ᵗ (A y s + B (F (y s))) ds`, so
`integralSolution_unique` identifies them; the integral identity is the ordinary
fundamental theorem of calculus applied to the closed-loop exponential. -/
theorem variationOfConstants_feedback_eq_expFlow
    (sys : LinearSystem ℝ X U Z) (F : X →ₗ[ℝ] U) (x : X) :
    sys.variationOfConstants 0 x
        (fun t : ℝ =>
          F (NormedSpace.exp (t • (sys.A + sys.B.comp F).toContinuousLinearMap) x)) =
      fun t : ℝ =>
        NormedSpace.exp (t • (sys.A + sys.B.comp F).toContinuousLinearMap) x := by
  let sys' : LinearSystem ℝ X U Z := ⟨sys.A + sys.B.comp F, 0, sys.C, 0⟩
  let y : ℝ → X := fun t => sys'.expFlow t x
  let u : ℝ → U := fun t => F (y t)
  have hy_deriv : ∀ t : ℝ, HasDerivAt y (sys'.A (y t)) t :=
    fun t => hasDerivAt_expFlow_apply_state sys' t x
  have hy0 : y 0 = x := by simp [y, sys', LinearSystem.expFlow_zero]
  have hy_cont : Continuous y := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hy_deriv t).continuousAt
  have hdyn : ∀ s : ℝ, sys.dynamics (y s) (u s) = sys'.A (y s) := by
    intro s
    simp [LinearSystem.dynamics_apply, sys', u]
  have hcont_dyn : Continuous (fun s : ℝ => sys.dynamics (y s) (u s)) := by
    have h : (fun s : ℝ => sys.dynamics (y s) (u s)) = fun s => sys'.A (y s) := by
      funext s; exact hdyn s
    rw [h]
    exact sys'.A.toContinuousLinearMap.continuous.comp hy_cont
  have hint : ∀ t : ℝ, y t = x + ∫ s in (0:ℝ)..t, sys.dynamics (y s) (u s) := by
    intro t
    have hderiv' : ∀ s : ℝ, HasDerivAt y (sys.dynamics (y s) (u s)) s := by
      intro s; rw [hdyn s]; exact hy_deriv s
    have hFTC := intervalIntegral.sub_eq_integral_of_hasDerivAt hderiv' hcont_dyn 0 t
    rw [hy0] at hFTC
    rw [← hFTC]; abel
  have hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume := by
    have hFu : Continuous u := F.continuous_of_finiteDimensional.comp hy_cont
    exact hFu.locallyIntegrable
  exact integralSolution_unique sys 0 x u hu
    (continuous_variationOfConstants sys 0 x u hu)
    (variationOfConstants_self sys 0 x u)
    (fun t => variationOfConstants_integral sys 0 x u hu t)
    hy_cont hy0 hint

set_option maxHeartbeats 800000 in
-- Instantiating the real-linear Bohl closure at the state space exceeds the default budget.
/-- **The finite-Bohl synthesis obligation is discharged.** Under the explicit
finite-dimensionality `[FiniteDimensional ℂ X]` of the complexified state space,
a complex-linear input map `Bℂ : U →ₗ[ℂ] X` whose real restriction equals
`sys.B` satisfies `FiniteBohlSynthesis sys Bℂ hB H`: each state of the algebraic
`W_g(ker H) = V*(ker H) + Xstab(A, B)` admits a finite-Bohl input with decaying
controlled readout.

The state-feedback characterization supplies a real gain `F` with
`t ↦ H (exp (t (A + B F)) x) → 0`. The orbit is finite Bohl by
`isExponentialPolynomial_expFlow_of_realLinear`, so its image under the
real-linear map `Bℂ ∘ F` is finite Bohl by
`IsExponentialPolynomial.map_realLinear`, and the trajectory identity
`variationOfConstants_feedback_eq_expFlow` turns the closed-loop decay into the
open-loop decay. No complexification of the gain and no spectral hypothesis on
`A` is assumed. -/
theorem finiteBohlSynthesis [FiniteDimensional ℂ X]
    (sys : LinearSystem ℝ X U Z) (Bℂ : U →ₗ[ℂ] X)
    (hB : Bℂ.restrictScalars ℝ = sys.B) (H : X →ₗ[ℝ] Z) :
    FiniteBohlSynthesis sys Bℂ hB H := by
  intro x hx
  obtain ⟨F, hdec⟩ :=
    exists_feedback_tendsto_readout_of_mem_outputStabilizableSubspace sys.A sys.B H hx
  let orb : ℝ → X :=
    fun t => NormedSpace.exp (t • (sys.A + sys.B.comp F).toContinuousLinearMap) x
  let u : ℝ → U := fun t => F (orb t)
  refine ⟨u, ?_, ?_, ?_⟩
  · have horb_cont : Continuous orb := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (hasDerivAt_expFlow_apply_state
        (⟨sys.A + sys.B.comp F, 0, sys.C, 0⟩ : LinearSystem ℝ X U Z) t x).continuousAt
    exact (F.continuous_of_finiteDimensional.comp horb_cont).locallyIntegrable
  · have hmap := (isExponentialPolynomial_expFlow_of_realLinear
        (sys.A + sys.B.comp F) x).map_realLinear
      (((Bℂ.restrictScalars ℝ).comp F).toContinuousLinearMap)
    simpa [u, orb, LinearMap.comp_apply, LinearMap.restrictScalars_apply] using hmap
  · have hv : sys.variationOfConstants 0 x u = orb := by
      change sys.variationOfConstants 0 x (fun t => F (orb t)) = orb
      exact variationOfConstants_feedback_eq_expFlow sys F x
    rw [hv]
    simpa [orb] using hdec

set_option maxHeartbeats 800000 in
-- Packaging the conditional iff against the discharged synthesis exceeds the default budget.
/-- The finite-Bohl-forcing-image `W_g` identity with synthesis supplied and an
explicit necessity argument, retained as a compositional API. -/
theorem isBohlOutputStabilizable_iff_mem_outputStabilizableSubspace'
    [FiniteDimensional ℂ X]
    (sys : LinearSystem ℝ X U Z) (Bℂ : U →ₗ[ℂ] X)
    (hB : Bℂ.restrictScalars ℝ = sys.B) (H : X →ₗ[ℝ] Z)
    (hbridge : FiniteBohlWBridge sys Bℂ hB H) (x : X) :
    IsBohlOutputStabilizable sys Bℂ hB H x ↔
      x ∈ outputStabilizableSubspace sys.A sys.B H :=
  isBohlOutputStabilizable_iff_mem_outputStabilizableSubspace sys Bℂ hB H hbridge
    (finiteBohlSynthesis sys Bℂ hB H) x

/-- **Finite-Bohl forcing-image output stabilization (Theorem 4.37 variant).**
For the coherent real/complex scalar structures and a complex-linear input map
restricting to `sys.B`, the finite-Bohl forcing-image output-stabilizable states
are exactly `V*(ker H) + Xstab(A,B)`. Unlike the book's Bohl-input statement,
this formulation constrains the forcing image; it does not assert the
unrestricted locally-integrable characterization. -/
theorem isBohlOutputStabilizable_iff_mem_outputStabilizableSubspace_complete
    [FiniteDimensional ℂ X]
    (sys : LinearSystem ℝ X U Z) (Bℂ : U →ₗ[ℂ] X)
    (hB : Bℂ.restrictScalars ℝ = sys.B) (H : X →ₗ[ℝ] Z) (x : X) :
    IsBohlOutputStabilizable sys Bℂ hB H x ↔
      x ∈ outputStabilizableSubspace sys.A sys.B H :=
  isBohlOutputStabilizable_iff_mem_outputStabilizableSubspace'
    sys Bℂ hB H (finiteBohlWBridge sys Bℂ hB H) x

end FiniteBohlSynthesisAssembly

end LinearSystem
