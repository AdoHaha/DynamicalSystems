/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.ControlHorizon
public import DynamicalSystems.OptimalControl.ContinuousTime.IntegralControlPath
public import DynamicalSystems.Mathlib.Analysis.Convex.MeasureInequalityMultipliers
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Tactic.Abel

/-!
# Necessary state-constraint measures for affine convex integral control problems

Controls are measurable and take values in a compact convex subset of a real
normed space. Trajectories satisfy the Volterra equation at every horizon time.
Affine dynamics make the unconstrained dynamics domain convex. Joint convexity
of the running cost, terminal convexity and spatial constraint convexity then
give measure multipliers from actual constrained optimality.

The measure is on time times the finite constraint index. It is concentrated on
the actual contact set; abnormal multipliers are retained. No multiplier,
trajectory convexity, Lagrangian minimum or BV certificate is supplied.
This module supplies multiplier necessity, not the subsequent adjoint/PMP assembly.
-/

@[expose] public section

open Set MeasureTheory
open scoped NNReal

namespace OptimalControl

variable (E V : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Primitive affine/convex data. Affinity is a pointwise identity of the field,
not an assumption about trajectories or their attainable cost image. -/
structure ConvexStateControlProblem (n : ℕ) where
  horizon : ℝ
  horizon_pos : 0 < horizon
  initial : E
  controlSet : Set V
  controlSet_compact : IsCompact controlSet
  controlSet_convex : Convex ℝ controlSet
  dynamics : ControlTime horizon → E → V → E
  dynamics_continuous : Continuous (fun z : (ControlTime horizon × E) × V ↦
    dynamics z.1.1 z.1.2 z.2)
  dynamics_affine : ∀ t x y u v (a b : ℝ), 0 ≤ a → 0 ≤ b → a + b = 1 →
    dynamics t (a • x + b • y) (a • u + b • v) =
      a • dynamics t x u + b • dynamics t y v
  runningCost : ControlTime horizon → E → V → ℝ
  runningCost_continuous : Continuous (fun z : (ControlTime horizon × E) × V ↦
    runningCost z.1.1 z.1.2 z.2)
  runningCost_convex : ∀ t, ConvexOn ℝ univ (fun z : E × V ↦ runningCost t z.1 z.2)
  terminalCost : E → ℝ
  terminalCost_convex : ConvexOn ℝ univ terminalCost
  constraint : (ControlTime horizon × Fin n) → E → ℝ
  constraint_continuous : Continuous (fun z : (ControlTime horizon × Fin n) × E ↦
    constraint z.1 z.2)
  constraint_convex : ∀ t, ConvexOn ℝ univ (constraint t)

namespace ConvexStateControlProblem

variable {E V} [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] {n : ℕ}

abbrev Time (P : ConvexStateControlProblem E V n) := ControlTime P.horizon
abbrev Candidate (P : ConvexStateControlProblem E V n) := C(P.Time, E) × (P.Time → V)
abbrev ConstraintIndex (P : ConvexStateControlProblem E V n) := P.Time × Fin n

/-- The domain retains control constraints and actual integral dynamics but
does not yet impose state inequalities. -/
def DynamicsAdmissible (P : ConvexStateControlProblem E V n) (z : P.Candidate) : Prop :=
  Measurable z.2 ∧ (∀ t, z.2 t ∈ P.controlSet) ∧
    ∀ t, z.1 t = P.initial + P.horizon •
      ∫ s in Ioc (timeZero P.horizon P.horizon_pos.le) t,
        P.dynamics s (z.1 s) (z.2 s) ∂horizonProbability P.horizon P.horizon_pos

/-- The actual Bolza cost. The factor `horizon` undoes normalized time measure. -/
noncomputable def cost (P : ConvexStateControlProblem E V n) (z : P.Candidate) : ℝ :=
  P.terminalCost (z.1 (timeEnd P.horizon P.horizon_pos.le)) +
    P.horizon * ∫ t, P.runningCost t (z.1 t) (z.2 t)
      ∂horizonProbability P.horizon P.horizon_pos

/-- Continuous constraint residual on time times the finite constraint index. -/
def residual (P : ConvexStateControlProblem E V n) (z : P.Candidate) :
    C(P.ConstraintIndex, ℝ) :=
  ⟨fun q ↦ P.constraint q (z.1 q.1),
    P.constraint_continuous.comp (continuous_id.prodMk
      (z.1.continuous.comp continuous_fst))⟩

/-- Actual state-constrained optimality, comparing all measurable integral pairs. -/
def IsMinimum (P : ConvexStateControlProblem E V n) (z : P.Candidate) : Prop :=
  P.DynamicsAdmissible z ∧ P.residual z ≤ 0 ∧
    ∀ y, P.DynamicsAdmissible y → P.residual y ≤ 0 → P.cost z ≤ P.cost y

/-- Compact controls derive integrability of continuous field/cost compositions.
No global bound on the state-dependent vector field is needed. -/
theorem integrable_composition {F : Type*} [NormedAddCommGroup F]
    (P : ConvexStateControlProblem E V n) (z : P.Candidate) (hz : P.DynamicsAdmissible z)
    (g : P.Time → E → V → F)
    (hg : Continuous (fun q : (P.Time × E) × V ↦ g q.1.1 q.1.2 q.2)) :
    Integrable (fun t ↦ g t (z.1 t) (z.2 t))
      (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  let : CompactSpace P.controlSet := isCompact_iff_compactSpace.mp P.controlSet_compact
  let u : P.Time → P.controlSet := fun t ↦ ⟨z.2 t, hz.2.1 t⟩
  have hu : Measurable u := hz.1.subtype_mk
  have hc : Continuous (fun q : P.Time × P.controlSet ↦ g q.1 (z.1 q.1) q.2) :=
    hg.comp ((continuous_fst.prodMk (z.1.continuous.comp continuous_fst)).prodMk
      (continuous_subtype_val.comp continuous_snd))
  have hi : Integrable (fun q : P.Time × P.controlSet ↦ g q.1 (z.1 q.1) q.2)
      (Measure.map (fun t ↦ (t, u t))
        (horizonProbability P.horizon P.horizon_pos).toMeasure) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact hi.comp_measurable (measurable_id.prodMk hu)

/-- Convex combinations satisfy the original dynamics, not a supplied convexity certificate. -/
theorem convex_dynamicsAdmissible (P : ConvexStateControlProblem E V n) :
    Convex ℝ {z | P.DynamicsAdmissible z} := by
  intro x hx y hy a b ha hb hab
  refine ⟨(hx.1.const_smul a).add (hy.1.const_smul b), ?_, ?_⟩
  · intro t
    exact P.controlSet_convex (hx.2.1 t) (hy.2.1 t) ha hb hab
  · intro t
    have hxi := (P.integrable_composition x hx P.dynamics P.dynamics_continuous).integrableOn
      (s := Ioc (timeZero P.horizon P.horizon_pos.le) t)
    have hyi := (P.integrable_composition y hy P.dynamics P.dynamics_continuous).integrableOn
      (s := Ioc (timeZero P.horizon P.horizon_pos.le) t)
    change a • x.1 t + b • y.1 t = P.initial + P.horizon •
      ∫ s in Ioc (timeZero P.horizon P.horizon_pos.le) t,
        P.dynamics s (a • x.1 s + b • y.1 s) (a • x.2 s + b • y.2 s)
          ∂horizonProbability P.horizon P.horizon_pos
    simp_rw [P.dynamics_affine _ _ _ _ _ _ _ ha hb hab]
    rw [integral_add (hxi.fun_smul a) (hyi.fun_smul b), integral_smul, integral_smul,
      hx.2.2 t, hy.2.2 t]
    simp only [smul_add, smul_smul]
    rw [add_add_add_comm, ← add_smul, hab, one_smul,
      mul_comm a P.horizon, mul_comm b P.horizon]

/-- Joint running-cost convexity integrates to actual cost convexity. -/
theorem convexOn_cost (P : ConvexStateControlProblem E V n) :
    ConvexOn ℝ {z | P.DynamicsAdmissible z} P.cost := by
  refine ⟨P.convex_dynamicsAdmissible, ?_⟩
  intro x hx y hy a b ha hb hab
  have hmix := P.convex_dynamicsAdmissible hx hy ha hb hab
  have hxi := P.integrable_composition x hx P.runningCost P.runningCost_continuous
  have hyi := P.integrable_composition y hy P.runningCost P.runningCost_continuous
  have hzi := P.integrable_composition _ hmix P.runningCost P.runningCost_continuous
  have hi : (∫ t, P.runningCost t ((a • x + b • y).1 t) ((a • x + b • y).2 t)
      ∂horizonProbability P.horizon P.horizon_pos) ≤
      a * (∫ t, P.runningCost t (x.1 t) (x.2 t)
        ∂horizonProbability P.horizon P.horizon_pos) +
      b * (∫ t, P.runningCost t (y.1 t) (y.2 t)
        ∂horizonProbability P.horizon P.horizon_pos) := by
    calc
      _ ≤ ∫ t, a • P.runningCost t (x.1 t) (x.2 t) +
          b • P.runningCost t (y.1 t) (y.2 t)
          ∂horizonProbability P.horizon P.horizon_pos :=
        integral_mono hzi ((hxi.fun_smul a).add (hyi.fun_smul b)) (fun t ↦
          (P.runningCost_convex t).2 (mem_univ (x.1 t, x.2 t))
            (mem_univ (y.1 t, y.2 t)) ha hb hab)
      _ = _ := by
        rw [integral_add (hxi.fun_smul a) (hyi.fun_smul b), integral_smul, integral_smul]
        simp only [smul_eq_mul]
  have ht := P.terminalCost_convex.2
    (mem_univ (x.1 (timeEnd P.horizon P.horizon_pos.le)))
    (mem_univ (y.1 (timeEnd P.horizon P.horizon_pos.le))) ha hb hab
  change P.cost (a • x + b • y) ≤ a * P.cost x + b * P.cost y
  unfold cost
  change P.terminalCost (a • x.1 (timeEnd P.horizon P.horizon_pos.le) +
      b • y.1 (timeEnd P.horizon P.horizon_pos.le)) +
      P.horizon * (∫ t, P.runningCost t ((a • x + b • y).1 t) ((a • x + b • y).2 t)
        ∂horizonProbability P.horizon P.horizon_pos) ≤ _
  have hscaled := mul_le_mul_of_nonneg_left hi P.horizon_pos.le
  simp only [smul_eq_mul] at ht
  nlinarith

/-- Spatial convexity of each primitive state constraint gives residual convexity. -/
theorem convexOn_residual (P : ConvexStateControlProblem E V n) (q : P.ConstraintIndex) :
    ConvexOn ℝ {z | P.DynamicsAdmissible z} (fun z ↦ P.residual z q) := by
  refine ⟨P.convex_dynamicsAdmissible, ?_⟩
  intro x _ y _ a b ha hb hab
  exact (P.constraint_convex q).2 (mem_univ (x.1 q.1)) (mem_univ (y.1 q.1)) ha hb hab

/-- Actual affine-convex constrained optimality constructs nontrivial finite
state-constraint measures, complementary slackness, active-set concentration,
and a Lagrangian minimum over every unconstrained dynamics competitor. -/
theorem exists_measure_of_isMinimum (P : ConvexStateControlProblem E V n)
    (z : P.Candidate) (hz : P.IsMinimum z) :
    ∃ (α : ℝ) (μ : Measure P.ConstraintIndex), IsFiniteMeasure μ ∧ 0 ≤ α ∧
      (α ≠ 0 ∨ μ ≠ 0) ∧ (∫ q, P.residual z q ∂μ) = 0 ∧
      μ {q | P.residual z q ≠ 0} = 0 ∧
      ∀ y, P.DynamicsAdmissible y →
        α * P.cost z ≤ α * P.cost y + ∫ q, P.residual y q ∂μ :=
  ConvexProgramming.exists_continuousInequality_measure P.convex_dynamicsAdmissible
    P.cost P.residual z P.convexOn_cost P.convexOn_residual hz.1 hz.2.1
    (fun y hy hg ↦ hz.2.2 y hy hg)

/-- Strict feasibility of one actual integral control pair proves normality. -/
theorem exists_normal_measure_of_isMinimum (P : ConvexStateControlProblem E V n)
    (z : P.Candidate) (hz : P.IsMinimum z)
    (hstrict : ∃ y, P.DynamicsAdmissible y ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ q, P.residual y q ≤ -δ) :
    ∃ (α : ℝ) (μ : Measure P.ConstraintIndex), IsFiniteMeasure μ ∧ 0 < α ∧
      (∫ q, P.residual z q ∂μ) = 0 ∧ μ {q | P.residual z q ≠ 0} = 0 ∧
      ∀ y, P.DynamicsAdmissible y →
        α * P.cost z ≤ α * P.cost y + ∫ q, P.residual y q ∂μ := by
  obtain ⟨α, μ, hfin, hα, hne, hcomp, hsupport, hmin⟩ := P.exists_measure_of_isMinimum z hz
  let : IsFiniteMeasure μ := hfin
  have hp := ConvexProgramming.costMultiplier_pos_of_uniform_slater
    {y | P.DynamicsAdmissible y} P.cost P.residual z α μ hα hne hmin hstrict
  exact ⟨α, μ, hfin, hp, hcomp, hsupport, hmin⟩

section Integrator

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [SecondCountableTopology E] in
/-- Every measurable compact-set-valued control has an integrable actual velocity. -/
theorem integrable_control (P : ConvexStateControlProblem E E n) (u : P.Time → E)
    (hu : Measurable u) (hmem : ∀ t, u t ∈ P.controlSet) :
    Integrable u (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  let : CompactSpace P.controlSet := isCompact_iff_compactSpace.mp P.controlSet_compact
  let v : P.Time → P.controlSet := fun t ↦ ⟨u t, hmem t⟩
  have hv : Measurable v := hu.subtype_mk
  have hi : Integrable ((↑) : P.controlSet → E)
      (Measure.map v (horizonProbability P.horizon P.horizon_pos).toMeasure) :=
    continuous_subtype_val.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact hi.comp_measurable hv

omit [SecondCountableTopology E] in
/-- For integrator dynamics every measurable control has a constructed continuous
integral trajectory. This justifies arbitrary replacements after dualizing the
state constraints; trajectory existence is not supplied as a hypothesis. -/
theorem exists_integrator_candidate (P : ConvexStateControlProblem E E n)
    (hf : ∀ t x u, P.dynamics t x u = u) (u : P.Time → E)
    (hu : Measurable u) (hmem : ∀ t, u t ∈ P.controlSet) :
    ∃ y : P.Candidate, P.DynamicsAdmissible y ∧ y.2 = u ∧
      ∀ t, y.1 t = integralControlPath P.horizon_pos P.initial u t := by
  have hi := P.integrable_control u hu hmem
  obtain ⟨C, hC⟩ := P.controlSet_compact.isBounded.exists_norm_le
  let M : ℝ≥0 := Real.toNNReal (max C 0)
  have hM : ∀ t, ‖u t‖ ≤ M := by
    intro t
    rw [Real.coe_toNNReal _ (le_max_right C 0)]
    exact (hC (u t) (hmem t)).trans (le_max_left C 0)
  let x : C(P.Time, E) := ⟨integralControlPath P.horizon_pos P.initial u,
    (lipschitzWith_integralControlPath P.horizon_pos P.initial u hi hM).continuous⟩
  refine ⟨(x, u), ⟨hu, hmem, ?_⟩, rfl, fun _ ↦ rfl⟩
  intro t
  change integralControlPath P.horizon_pos P.initial u t = _
  simp only [hf]
  rfl

end Integrator

end ConvexStateControlProblem
end OptimalControl
