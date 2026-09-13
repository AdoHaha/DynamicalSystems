/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.DisturbanceDecoupling
public import DynamicalSystems.Linear.Trajectory

/-! # Dynamic measurement-feedback: algebraic foundations

This file lays the algebraic foundations of Chapter 6 of Trentelman, Stoorvogel
and Hautus, *Control Theory for Linear Systems*: the **dynamic measurement
feedback** interconnection of a plant with a finite-dimensional linear
time-invariant controller, in the presence of a feedthrough from the control
input to the measurement.

The plant `Σ = (A, B, C, D)` is an ordinary `LinearSystem` with state `X`,
control input `U` and measurement output `Y`, and it is driven by a disturbance
input `d : D` through a **state channel** `E : D →ₗ[𝕜] X`; the controlled output
is the **output channel** `H : X →ₗ[𝕜] Z`:

```
x'(t) = A x(t) + B u(t) + E d(t),
y(t)  = C x(t) + D u(t),
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
`He = outputMap` (`closedLoopSystem`). The main algebraic law below is the
composition identity `closedLoopSystem_dynamics`, which decomposes the
closed-loop right-hand side into the autonomous extended map plus the disturbance
channel.

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

## Scope and deferred obligations

This file deliberately stops at the **foundations**. The following are *not*
claimed here and remain the next milestones; they are recorded so that no
unproved strengthening is read into the present declarations:

* the full dynamic decoupling synthesis: that a `(C, A, B)`-pair between
  `im E` and `ker H` yields a controller with `T = 0` (Theorem 6.6 and
  Corollary 6.7). The algebraic core `exists_isCABPairBetween_iff` already lives
  in `DynamicalSystems.Linear.DisturbanceDecoupling`, but the passage from a
  pair to the controller above is not formalised here;
* a measurement disturbance channel `F : D →ₗ[𝕜] Y` in the readout; only the
  state disturbance `E` is modelled at this stage, and the output channel `H`
  is the controlled-output map;
* the spectrum factorization of the extended system mapping and the internal
  stability results of Sections 6.3–6.4 (`σ (Ae) = σ (A + B F) ∪ σ (A + G C)`),
  which require a stabilizability/detectability calculus that is likewise not
  claimed here;
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
* `DynamicInterconnection.closedLoopMap`, `disturbanceMap`, `outputMap`
* `DynamicInterconnection.closedLoopSystem`
* `DynamicInterconnection.IsClosedLoopDisturbanceDecoupled`

## Main results

* `DynamicInterconnection.measurement_eq_plant_readout`
* `DynamicInterconnection.measurement_eq_of_plant_readout`
* `DynamicInterconnection.closedLoopSystem_dynamics`
* `DynamicInterconnection.closedLoopSystem_dynamics_zero_disturbance`
* `DynamicInterconnection.closedLoopMap_of_D_eq_zero`
* `DynamicInterconnection.closedLoopSystem_variationOfConstants_zero`

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

end LinearSystem
