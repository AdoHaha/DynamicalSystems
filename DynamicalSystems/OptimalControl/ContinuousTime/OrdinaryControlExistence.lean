/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.Existence
public import DynamicalSystems.OptimalControl.ContinuousTime.BarycentricRecovery

/-!
# Ordinary optimal-control existence in the convex-control, affine-dynamics regime

A relaxed minimizer is constructed using actual compactness and closure.
Its conditional barycentre then supplies a measurable ordinary control with
the same entire trajectory and no larger cost. Graph-measure embedding compares
it against every ordinary admissible competitor. No realization/selection or
integrability hypothesis is left to the caller of the final existence theorem.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped BoundedContinuousFunction NNReal Topology

namespace OptimalControl

namespace BoundedContinuousProblem

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [CompactSpace U]

/-- A measurable ordinary control, actual integral dynamics, and explicit
endpoint/state constraints. All admissible competitors use this predicate. -/
def OrdinaryAdmissible (P : BoundedContinuousProblem E U) (x : P.Path) (u : P.Time → U) : Prop :=
  Measurable u ∧
    (∀ t, x t = P.initial + P.horizon • ∫ s in Ioc (timeZero P.horizon P.horizon_pos.le) t,
      P.dynamics s (x s) (u s) ∂horizonProbability P.horizon P.horizon_pos) ∧
    x (timeEnd P.horizon P.horizon_pos.le) ∈ P.target ∧ ∀ t, x t ∈ P.stateConstraint t

/-- The ordinary Bolza objective, using the same Lebesgue normalization as
the relaxed objective. -/
noncomputable def ordinaryCost (P : BoundedContinuousProblem E U) (x : P.Path) (u : P.Time → U) : ℝ :=
  P.terminalCost (x (timeEnd P.horizon P.horizon_pos.le)) +
    P.horizon * ∫ t, P.runningCost t (x t) (u t) ∂horizonProbability P.horizon P.horizon_pos

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Continuous field/cost compositions with a measurable control are
integrable. This derives ordinary integrability from primitive compact data. -/
theorem integrable_ordinary_composition {F : Type*} [NormedAddCommGroup F]
    (P : BoundedContinuousProblem E U) (x : P.Path) (u : P.Time → U) (hu : Measurable u)
    (g : P.Time → E → U → F)
    (hg : Continuous (fun z : (P.Time × E) × U => g z.1.1 z.1.2 z.2)) :
    Integrable (fun t => g t (x t) (u t)) (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  have hc : Continuous (fun z : P.Time × U => g z.1 (x z.1) z.2) :=
    hg.comp ((continuous_fst.prodMk (x.continuous.comp continuous_fst)).prodMk continuous_snd)
  have hi : Integrable (fun z : P.Time × U => g z.1 (x z.1) z.2)
      (Measure.map (fun t => (t, u t)) (horizonProbability P.horizon P.horizon_pos).toMeasure) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact hi.comp_measurable (measurable_id.prodMk hu)

omit [FiniteDimensional ℝ E] in
/-- Ordinary admissibility embeds into relaxed admissibility without changing
the state path. -/
theorem OrdinaryAdmissible.to_relaxed {P : BoundedContinuousProblem E U} {x : P.Path}
    {u : P.Time → U} (hu : P.OrdinaryAdmissible x u) :
    P.RelaxedAdmissible x (RelaxedControl.ofControl
      (horizonProbability P.horizon P.horizon_pos) u hu.1) := by
  refine ⟨?_, hu.2.2⟩
  intro t
  rw [RelaxedControl.setIntegral_ofControl _ u hu.1 measurableSet_Ioc _
    (integrable_trajectoryField P.horizon_pos P.dynamics P.dynamics_continuous x _).aestronglyMeasurable]
  exact hu.2.1 t

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- The graph embedding preserves the objective exactly. -/
theorem relaxedCost_ofControl (P : BoundedContinuousProblem E U) (x : P.Path)
    (u : P.Time → U) (hu : Measurable u) :
    P.relaxedCost x (RelaxedControl.ofControl (horizonProbability P.horizon P.horizon_pos) u hu) =
      P.ordinaryCost x u := by
  unfold relaxedCost ordinaryCost
  rw [RelaxedControl.integral_ofControl]
  exact (P.runningCost_continuous.comp
    ((continuous_fst.prodMk (x.continuous.comp continuous_fst)).prodMk continuous_snd)).aestronglyMeasurable

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {K : Set V} [CompactSpace K] [Nonempty K]

/-- Algebraic control-affinity and convexity data. These are properties of the
original dynamics/cost, not an assumed ordinary-control recovery certificate. -/
structure AffineConvexData (P : BoundedContinuousProblem E K) where
  drift : P.Time → E → E
  inputMap : P.Time → E → V →L[ℝ] E
  dynamics_eq : ∀ t x (u : K), P.dynamics t x u = drift t x + inputMap t x (u : V)
  costExtension : P.Time → E → V → ℝ
  cost_eq : ∀ t x (u : K), P.runningCost t x u = costExtension t x (u : V)
  cost_convex : ∀ t x, ConvexOn ℝ K (costExtension t x)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [CompactSpace K] [Nonempty K] in
/-- Continuity on the original control set follows from the problem's
continuous running cost, not from a new recovery-side premise. -/
theorem AffineConvexData.cost_continuousOn {P : BoundedContinuousProblem E K}
    (A : P.AffineConvexData) (t : P.Time) (x : E) : ContinuousOn (A.costExtension t x) K := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous (fun u : K => P.runningCost t x u) :=
    P.runningCost_continuous.comp
      ((continuous_const : Continuous (fun _ : K => (t, x))).prodMk continuous_id)
  convert hc using 1
  funext u
  exact (A.cost_eq t x u).symm

/-- The constructed measurable ordinary control preserves the full relaxed
trajectory and every endpoint/state constraint. -/
theorem RelaxedAdmissible.recover {P : BoundedContinuousProblem E K}
    (A : P.AffineConvexData) (hK : Convex ℝ K) {x : P.Path} {ρ : P.Relaxed}
    (hx : P.RelaxedAdmissible x ρ) : P.OrdinaryAdmissible x (ρ.recoveredControl hK) := by
  refine ⟨ρ.measurable_recoveredControl hK, ?_, hx.2⟩
  intro t
  have hfield : (fun z : P.Time × K => P.dynamics z.1 (x z.1) z.2) =
      (fun z => A.drift z.1 (x z.1) + A.inputMap z.1 (x z.1) (z.2 : V)) := by
    funext z
    exact A.dynamics_eq _ _ _
  have hfi := integrable_trajectoryField P.horizon_pos P.dynamics P.dynamics_continuous x ρ
  rw [hfield] at hfi
  have he := ρ.setIntegral_affine_eq_recovered hK (fun s => A.drift s (x s))
    (fun s => A.inputMap s (x s)) (s := Ioc (timeZero P.horizon P.horizon_pos.le) t)
      measurableSet_Ioc hfi.integrableOn
  rw [hx.1 t, hfield, he]
  simp only [A.dynamics_eq]

omit [FiniteDimensional ℝ E] in
/-- The cost comparison is derived from Jensen and disintegration; all actual
integrability conditions are discharged by the primitive problem data. -/
theorem relaxedCost_recovery_le (P : BoundedContinuousProblem E K)
    (A : P.AffineConvexData) (hK : Convex ℝ K) (x : P.Path) (ρ : P.Relaxed) :
    P.ordinaryCost x (ρ.recoveredControl hK) ≤ P.relaxedCost x ρ := by
  have hgr := P.integrable_ordinary_composition x (ρ.recoveredControl hK)
    (ρ.measurable_recoveredControl hK) P.runningCost P.runningCost_continuous
  have hgo : Integrable (fun z : P.Time × K => P.runningCost z.1 (x z.1) z.2) ρ.measure :=
    (P.runningCost_continuous.comp
      ((continuous_fst.prodMk (x.continuous.comp continuous_fst)).prodMk continuous_snd)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [A.cost_eq] at hgr hgo
  have hj := ρ.integral_convex_cost_recovered_le hK (fun t => A.costExtension t (x t))
    (fun t => A.cost_convex t (x t)) (fun t => A.cost_continuousOn t (x t)) hgr hgo
  unfold ordinaryCost relaxedCost
  simp only [A.cost_eq]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hj P.horizon_pos.le)

/-- **Existence of an optimal measurable ordinary control** for bounded
continuous finite-dimensional problems with compact convex controls,
control-affine dynamics, and continuous convex running costs. Feasibility is
supplied as one actual ordinary admissible pair. No compactness, closure,
selector, recovery, or integrability premise is left unproved. -/
theorem exists_ordinary_minimizer (P : BoundedContinuousProblem E K)
    (A : P.AffineConvexData) (hK : Convex ℝ K)
    (hfeasible : ∃ x u, P.OrdinaryAdmissible x u) :
    ∃ x u, P.OrdinaryAdmissible x u ∧
      ∀ y v, P.OrdinaryAdmissible y v → P.ordinaryCost x u ≤ P.ordinaryCost y v := by
  obtain ⟨x₀, u₀, h₀⟩ := hfeasible
  obtain ⟨x, ρ, hx, hmin⟩ := P.exists_relaxed_minimizer ⟨x₀, _, h₀.to_relaxed⟩
  refine ⟨x, ρ.recoveredControl hK, hx.recover A hK, ?_⟩
  intro y v hv
  calc
    P.ordinaryCost x (ρ.recoveredControl hK) ≤ P.relaxedCost x ρ := P.relaxedCost_recovery_le A hK x ρ
    _ ≤ P.relaxedCost y (RelaxedControl.ofControl
        (horizonProbability P.horizon P.horizon_pos) v hv.1) := hmin y _ hv.to_relaxed
    _ = P.ordinaryCost y v := P.relaxedCost_ofControl y v hv.1

end BoundedContinuousProblem
end OptimalControl
