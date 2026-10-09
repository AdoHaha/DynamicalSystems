/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.FiniteRelaxedEpigraph
public import DynamicalSystems.Mathlib.MeasureTheory.IntegralTrajectoryExtension
public import DynamicalSystems.Mathlib.MeasureTheory.EquiIntegrableTrajectories

/-!
# Admissible finite relaxed Bolza pairs

Admissibility records actual measurable simplex controls, state and graph
constraints, boundary data, integrable weighted dynamics and costs, and the
integral differential equation. It does not contain a compactness certificate,
a limiting control, or an optimality assertion.

The common-interval bounded continuous path and L1 velocity are constructed
from each original moving-interval pair. Classical equi-AC then implies uniform
integrability of the constructed velocities.
-/

@[expose] public section

open Set MeasureTheory Filter
open DynamicalSystems.ClassicalEquiAC DynamicalSystems.MeasurableLift
open scoped Topology BoundedContinuousFunction

namespace OptimalControl

/-- Data of a finite-horizon Bolza problem. The control type may be a subtype
of an open Euclidean control domain; no extension of dynamics outside its
admissible graph is built into these data. -/
structure FiniteRelaxedBolzaData (E U : Type*) where
  /-- Lower endpoint of the common compact time interval. -/
  a : ℝ
  /-- Upper endpoint of the common compact time interval. -/
  b : ℝ
  /-- The common time interval is ordered. -/
  time_order : a ≤ b
  /-- Admissible time-state domain. -/
  stateDomain : Set (ℝ × E)
  /-- Original state-dependent ordinary control graph. -/
  controlGraph : Set (ℝ × E × U)
  /-- Original dynamics, used only on the admissible graph. -/
  dynamics : ℝ × E × U → E
  /-- Original running cost. -/
  runningCost : ℝ × E × U → ℝ
  /-- Admissible endpoint tuples. -/
  boundary : Set (ℝ × E × ℝ × E)
  /-- Terminal cost on endpoint tuples. -/
  terminalCost : ℝ × E × ℝ × E → ℝ

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace U]

/-- An actual admissible finite relaxed pair, with `N` measurable weights and
atoms. The integral law is imposed for every source subinterval, and the
integrability assumptions concern the actual weighted dynamics and cost.
Values of `path` outside the pair's own interval are irrelevant. -/
structure FiniteRelaxedAdmissiblePair (N : ℕ) (P : FiniteRelaxedBolzaData E U) where
  /-- Initial time of this pair. -/
  startTime : Icc P.a P.b
  /-- Final time of this pair. -/
  endTime : Icc P.a P.b
  /-- Each admissible pair has positive duration. -/
  time_lt : (startTime : ℝ) < endTime
  /-- Original trajectory, constrained only on its own interval. -/
  path : ℝ → E
  /-- Actual simplex weights and control atoms. -/
  control : ℝ → FiniteRelaxedControl N U
  /-- Measurability of all weights and atoms. -/
  measurable_control : Measurable control
  /-- Continuity on the original interval, as required for integral trajectories. -/
  continuous_path : ContinuousOn path (Icc (startTime : ℝ) (endTime : ℝ))
  /-- State-domain membership at every time, including both endpoints. -/
  state_mem : ∀ t ∈ Icc (startTime : ℝ) (endTime : ℝ), (t, path t) ∈ P.stateDomain
  /-- Simplex normalization and admissibility of every atom almost everywhere. -/
  graph_mem : ∀ᵐ t ∂volume.restrict (Icc (startTime : ℝ) (endTime : ℝ)),
    (t, path t, control t) ∈ finiteRelaxedControlGraph N P.controlGraph
  /-- Integrability of the actual weighted velocity. -/
  velocity_integrable : IntegrableOn
    (fun t ↦ finiteRelaxedVelocity N P.dynamics (t, path t, control t))
    (Icc (startTime : ℝ) (endTime : ℝ))
  /-- Finite integrability of the actual weighted running cost. -/
  cost_integrable : IntegrableOn
    (fun t ↦ finiteRelaxedRunningCost N P.runningCost (t, path t, control t))
    (Icc (startTime : ℝ) (endTime : ℝ))
  /-- Integral dynamics on every ordered source subinterval. -/
  integral_law : ∀ s ∈ Icc (startTime : ℝ) (endTime : ℝ),
    ∀ t ∈ Icc (startTime : ℝ) (endTime : ℝ), s ≤ t →
      path t - path s = ∫ z in Ioc s t,
        finiteRelaxedVelocity N P.dynamics (z, path z, control z)
  /-- Original terminal constraint. -/
  boundary_mem : ((startTime : ℝ), path startTime, (endTime : ℝ), path endTime) ∈ P.boundary

namespace FiniteRelaxedBolzaData

/-- The concrete finite relaxed velocity-cost epigraph of the problem. -/
def relaxedEpigraph (P : FiniteRelaxedBolzaData E U) (N : ℕ) : ℝ → E → Set (E × ℝ) :=
  constrainedVelocityCostSet (finiteRelaxedControlGraph N P.controlGraph)
    (finiteRelaxedVelocity N P.dynamics) (finiteRelaxedRunningCost N P.runningCost)

end FiniteRelaxedBolzaData

namespace FiniteRelaxedAdmissiblePair

variable {N : ℕ} {P : FiniteRelaxedBolzaData E U} (p : FiniteRelaxedAdmissiblePair N P)

/-- Endpoint data of an admissible pair. -/
def endpointData : ℝ × E × ℝ × E :=
  ((p.startTime : ℝ), p.path p.startTime, (p.endTime : ℝ), p.path p.endTime)

/-- Actual weighted velocity of a finite relaxed pair. -/
noncomputable def velocity : ℝ → E :=
  fun t ↦ finiteRelaxedVelocity N P.dynamics (t, p.path t, p.control t)

/-- Actual weighted running-cost density of a finite relaxed pair. -/
noncomputable def cost : ℝ → ℝ :=
  fun t ↦ finiteRelaxedRunningCost N P.runningCost (t, p.path t, p.control t)

/-- The complete original terminal-plus-running objective. -/
noncomputable def objective : ℝ :=
  P.terminalCost p.endpointData +
    ∫ t in Icc (p.startTime : ℝ) (p.endTime : ℝ), p.cost t

/-- The actual constant extension, bundled as a bounded continuous path on the
common compact interval. Boundedness follows from compactness of that interval. -/
noncomputable def extendedPath : Icc P.a P.b →ᵇ E :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun t ↦ constantExtension p.startTime p.endTime p.path t,
      (continuous_constantExtension p.time_lt.le p.continuous_path).comp
        continuous_subtype_val⟩

/-- Evaluation of the constructed common-interval path. -/
theorem extendedPath_apply (t : Icc P.a P.b) :
    p.extendedPath t = constantExtension p.startTime p.endTime p.path t := rfl

/-- The constructed path agrees with the original trajectory on its interval. -/
theorem extendedPath_eq (t : Icc P.a P.b)
    (ht : (t : ℝ) ∈ Icc (p.startTime : ℝ) (p.endTime : ℝ)) :
    p.extendedPath t = p.path t := constantExtension_eq p.path ht

/-- The initial endpoint value is preserved exactly. -/
@[simp] theorem extendedPath_start : p.extendedPath p.startTime = p.path p.startTime :=
  p.extendedPath_eq p.startTime ⟨le_rfl, p.time_lt.le⟩

/-- The final endpoint value is preserved exactly. -/
@[simp] theorem extendedPath_end : p.extendedPath p.endTime = p.path p.endTime :=
  p.extendedPath_eq p.endTime ⟨p.time_lt.le, le_rfl⟩

/-- The bundled path is constant before the original start time. -/
theorem extendedPath_left (t : Icc P.a P.b) (ht : (t : ℝ) ≤ p.startTime) :
    p.extendedPath t = p.extendedPath p.startTime := by
  rw [p.extendedPath_start, p.extendedPath_apply]
  exact constantExtension_left p.path ht

/-- The bundled path is constant after the original end time. -/
theorem extendedPath_right (t : Icc P.a P.b) (ht : (p.endTime : ℝ) ≤ t) :
    p.extendedPath t = p.extendedPath p.endTime := by
  rw [p.extendedPath_end, p.extendedPath_apply]
  exact constantExtension_right p.path p.time_lt.le ht

/-- Zero extension of the pair's actual velocity. -/
noncomputable def extendedVelocity : ℝ → E :=
  zeroExtension p.startTime p.endTime p.velocity

/-- Integrability of the extended velocity is derived from source integrability. -/
theorem extendedVelocity_integrable :
    Integrable p.extendedVelocity (volume.restrict (Icc P.a P.b)) :=
  (integrable_zeroExtension p.velocity_integrable).restrict

/-- The L1 element constructed from the actual zero-extended velocity. -/
noncomputable def extendedVelocityLp : Lp E 1 (volume.restrict (Icc P.a P.b)) :=
  MemLp.toLp p.extendedVelocity (memLp_one_iff_integrable.mpr p.extendedVelocity_integrable)

/-- The constructed L1 representative equals the actual extension almost everywhere. -/
theorem extendedVelocityLp_ae :
    (fun t ↦ p.extendedVelocityLp t) =ᵐ[volume.restrict (Icc P.a P.b)] p.extendedVelocity :=
  (memLp_one_iff_integrable.mpr p.extendedVelocity_integrable).coeFn_toLp

/-- The constructed path and L1 velocity retain the actual integral dynamics. -/
theorem extendedPath_integral_law (s t : Icc P.a P.b) (hst : (s : ℝ) ≤ t) :
    p.extendedPath t - p.extendedPath s =
      ∫ z in Ioc (s : ℝ) (t : ℝ), p.extendedVelocityLp z
        ∂volume.restrict (Icc P.a P.b) := by
  calc
    _ = ∫ z in Ioc (s : ℝ) (t : ℝ), p.extendedVelocity z
        ∂volume.restrict (Icc P.a P.b) :=
      constantExtension_integral_law p.startTime.property.1 p.endTime.property.2
        p.time_lt.le p.path p.velocity p.integral_law s t hst
    _ = _ := by
      apply setIntegral_congr_ae measurableSet_Ioc
      exact p.extendedVelocityLp_ae.symm.mono (fun z hz _ ↦ hz)

/-- Oriented-interval integral law in the form used by moving-interval compactness. -/
theorem extendedPath_intervalIntegral_law (s t : Icc P.a P.b) :
    p.extendedPath t - p.extendedPath s =
      ∫ z in (s : ℝ)..(t : ℝ), p.extendedVelocityLp z
        ∂volume.restrict (Icc P.a P.b) := by
  rcases le_total (s : ℝ) (t : ℝ) with hst | hts
  · rw [intervalIntegral.integral_of_le hst]
    exact p.extendedPath_integral_law s t hst
  · rw [intervalIntegral.integral_of_ge hts, ← p.extendedPath_integral_law t s hts]
    abel

/-- The endpoint tuple supplied to the analytic extraction is the original one. -/
theorem extended_boundary_mem :
    ((p.startTime : ℝ), p.extendedPath p.startTime,
      (p.endTime : ℝ), p.extendedPath p.endTime) ∈ P.boundary := by
  simpa only [p.extendedPath_start, p.extendedPath_end] using p.boundary_mem

end FiniteRelaxedAdmissiblePair

/-- Classical equi-AC of an actual admissible sequence gives uniform
integrability of its constructed L1 velocities, with no supplied L1 bound. -/
theorem unifIntegrable_extendedVelocityLp_of_equiAC [CompleteSpace E]
    {N : ℕ} {P : FiniteRelaxedBolzaData E U} (p : ℕ → FiniteRelaxedAdmissiblePair N P)
    (hx : EquiAbsolutelyContinuousOn (fun n ↦ (p n).path)
      (fun n ↦ ((p n).startTime : ℝ)) (fun n ↦ ((p n).endTime : ℝ))) :
    UnifIntegrable (fun n t ↦ (p n).extendedVelocityLp t) 1
      (volume.restrict (Icc P.a P.b)) := by
  have H := unifIntegrable_zeroExtension_of_equiAC P.time_order
    (fun n ↦ ((p n).startTime : ℝ)) (fun n ↦ ((p n).endTime : ℝ))
    (fun n ↦ (p n).path) (fun n ↦ (p n).velocity)
    (fun n ↦ ⟨(p n).startTime.property.1, (p n).time_lt.le, (p n).endTime.property.2⟩)
    (fun n ↦ (p n).continuous_path) (fun n ↦ (p n).velocity_integrable)
    (fun n ↦ (p n).integral_law) hx
  exact H.ae_eq (fun n ↦ (p n).extendedVelocityLp_ae.symm)

end OptimalControl
