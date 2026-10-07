/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.OrdinaryControlExistence

/-!
# Localization of linearly growing dynamics

A continuous radial retraction gives a globally bounded extension. The trajectory tube is
proved from actual integral dynamics; it is not supplied as a compactness premise.
The first result uses the explicit short-horizon condition `T * b < 1`.
-/

@[expose] public section

open Set MeasureTheory
open scoped BoundedContinuousFunction NNReal Topology

namespace OptimalControl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial retraction onto the closed ball of positive radius `R`. -/
noncomputable def radialClip (R : ℝ) (x : E) : E := (R / max R ‖x‖) • x

theorem continuous_radialClip {R : ℝ} (hR : 0 < R) : Continuous (radialClip R : E → E) := by
  unfold radialClip
  exact (continuous_const.div (continuous_const.max continuous_norm)
    (fun x ↦ ne_of_gt (lt_of_lt_of_le hR (le_max_left _ _)))).smul continuous_id

theorem radialClip_eq {R : ℝ} (hR : 0 < R) {x : E} (hx : ‖x‖ ≤ R) :
    radialClip R x = x := by
  simp [radialClip, max_eq_left hx, ne_of_gt hR]

theorem norm_radialClip_le_radius {R : ℝ} (hR : 0 < R) (x : E) :
    ‖radialClip R x‖ ≤ R := by
  rw [radialClip, norm_smul, Real.norm_of_nonneg (by positivity)]
  calc
    R / max R ‖x‖ * ‖x‖ ≤ R / max R ‖x‖ * max R ‖x‖ :=
      mul_le_mul_of_nonneg_left (le_max_right _ _) (by positivity)
    _ = R := div_mul_cancel₀ _ (ne_of_gt (lt_of_lt_of_le hR (le_max_left _ _)))

theorem norm_radialClip_le {R : ℝ} (hR : 0 < R) (x : E) :
    ‖radialClip R x‖ ≤ ‖x‖ := by
  rw [radialClip, norm_smul, Real.norm_of_nonneg (by positivity)]
  exact mul_le_of_le_one_left (norm_nonneg _) ((div_le_one
    (lt_of_lt_of_le hR (le_max_left _ _))).2 (le_max_left _ _))

variable {U : Type*} [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [CompactSpace U]
  [FiniteDimensional ℝ E]

omit [MetricSpace U] [BorelSpace U] [CompactSpace U] [FiniteDimensional ℝ E] in
/-- The actual Volterra dynamics and linear growth imply a uniform tube on a short horizon.
No regularity of the control, differentiability of the trajectory, or tube is assumed. -/
theorem IsRelaxedTrajectory.norm_le_of_linear_growth {T a b : ℝ} (hT : 0 < T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hshort : T * b < 1)
    {f : ControlTime T → E → U → E} {x₀ : E} {x : ControlTime T →ᵇ E}
    {ρ : RelaxedControl (ControlTime T) U (horizonProbability T hT)}
    (hgrowth : ∀ t y u, ‖f t y u‖ ≤ a + b * ‖y‖)
    (hx : IsRelaxedTrajectory hT f x₀ x ρ) :
    ‖x‖ ≤ (‖x₀‖ + T * a) / (1 - T * b) := by
  have hc : 0 ≤ a + b * ‖x‖ := by positivity
  have hpoint (t : ControlTime T) : ‖x t‖ ≤ ‖x₀‖ + T * (a + b * ‖x‖) := by
    rw [hx t]
    refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
    rw [norm_smul, Real.norm_of_nonneg hT.le]
    apply mul_le_mul_of_nonneg_left _ hT.le
    calc
      ‖∫ z in Ioc (timeZero T hT.le) t ×ˢ univ, f z.1 (x z.1) z.2 ∂ρ.measure‖ ≤
          (a + b * ‖x‖) * ρ.measure.real (Ioc (timeZero T hT.le) t ×ˢ univ) :=
        norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) (fun z _ ↦
          (hgrowth _ _ _).trans (add_le_add_right
            (mul_le_mul_of_nonneg_left (x.norm_coe_le_norm _) hb) _))
      _ ≤ a + b * ‖x‖ := mul_le_of_le_one_right hc measureReal_le_one
  have hsup : ‖x‖ ≤ ‖x₀‖ + T * (a + b * ‖x‖) :=
    (BoundedContinuousFunction.norm_le (by positivity)).2 hpoint
  apply (le_div_iff₀ (sub_pos.mpr hshort)).2
  nlinarith

/-- Continuous finite-horizon data with a global linear-growth estimate. The drift need not
be globally bounded in state. -/
structure LinearGrowthProblem (E U : Type*) [NormedAddCommGroup E] [MetricSpace U] where
  horizon : ℝ
  horizon_pos : 0 < horizon
  initial : E
  dynamics : ControlTime horizon → E → U → E
  dynamics_continuous : Continuous (fun z : (ControlTime horizon × E) × U ↦
    dynamics z.1.1 z.1.2 z.2)
  growthConstant : ℝ≥0
  growthRate : ℝ≥0
  dynamics_growth : ∀ t x u, ‖dynamics t x u‖ ≤ growthConstant + growthRate * ‖x‖
  runningCost : ControlTime horizon → E → U → ℝ
  runningCost_continuous : Continuous (fun z : (ControlTime horizon × E) × U ↦
    runningCost z.1.1 z.1.2 z.2)
  terminalCost : E → ℝ
  terminalCost_continuous : Continuous terminalCost
  target : Set E
  target_closed : IsClosed target
  stateConstraint : ControlTime horizon → Set E
  stateConstraint_closed : ∀ t, IsClosed (stateConstraint t)

namespace LinearGrowthProblem

variable (P : LinearGrowthProblem E U)

abbrev Time := ControlTime P.horizon
abbrev Path := P.Time →ᵇ E
abbrev Relaxed := RelaxedControl P.Time U (horizonProbability P.horizon P.horizon_pos)

/-- Actual integral dynamics with endpoint and state restrictions. -/
def RelaxedAdmissible (x : P.Path) (ρ : P.Relaxed) : Prop :=
  IsRelaxedTrajectory P.horizon_pos P.dynamics P.initial x ρ ∧
    x (timeEnd P.horizon P.horizon_pos.le) ∈ P.target ∧ ∀ t, x t ∈ P.stateConstraint t

noncomputable def relaxedCost (x : P.Path) (ρ : P.Relaxed) : ℝ :=
  P.terminalCost (x (timeEnd P.horizon P.horizon_pos.le)) +
    P.horizon * ∫ z, P.runningCost z.1 (x z.1) z.2 ∂ρ.measure

/-- A strictly positive radius, exceeding the tube estimate by one. -/
noncomputable def tubeRadius : ℝ :=
  (‖P.initial‖ + P.horizon * P.growthConstant) / (1 - P.horizon * P.growthRate) + 1

omit [NormedSpace ℝ E] [MeasurableSpace U] [BorelSpace U] [CompactSpace U]
  [FiniteDimensional ℝ E] in
theorem tubeRadius_pos (hshort : P.horizon * P.growthRate < 1) : 0 < P.tubeRadius := by
  unfold tubeRadius
  have hT := P.horizon_pos.le
  have : 0 ≤ (‖P.initial‖ + P.horizon * P.growthConstant) /
      (1 - P.horizon * P.growthRate) := div_nonneg (by positivity) (sub_pos.mpr hshort).le
  linarith

/-- The bounded extension changes only the dynamics, leaving costs and constraints intact. -/
noncomputable def localized (hshort : P.horizon * P.growthRate < 1) :
    BoundedContinuousProblem E U where
  horizon := P.horizon
  horizon_pos := P.horizon_pos
  initial := P.initial
  dynamics := fun t x u ↦ P.dynamics t (radialClip P.tubeRadius x) u
  dynamics_continuous := P.dynamics_continuous.comp
    ((continuous_fst.fst.prodMk
      ((continuous_radialClip (P.tubeRadius_pos hshort)).comp continuous_fst.snd)).prodMk
        continuous_snd)
  velocityBound := ⟨P.growthConstant + P.growthRate * P.tubeRadius, by
    have := (P.tubeRadius_pos hshort).le
    positivity⟩
  dynamics_bound := fun t x u ↦ (P.dynamics_growth _ _ _).trans
    (add_le_add_right (mul_le_mul_of_nonneg_left
      (norm_radialClip_le_radius (P.tubeRadius_pos hshort) x) P.growthRate.2) _)
  runningCost := P.runningCost
  runningCost_continuous := P.runningCost_continuous
  terminalCost := P.terminalCost
  terminalCost_continuous := P.terminalCost_continuous
  target := P.target
  target_closed := P.target_closed
  stateConstraint := P.stateConstraint
  stateConstraint_closed := P.stateConstraint_closed

omit [BorelSpace U] [CompactSpace U] [FiniteDimensional ℝ E] in
theorem trajectory_norm_le (hshort : P.horizon * P.growthRate < 1)
    {x : P.Path} {ρ : P.Relaxed}
    (hx : IsRelaxedTrajectory P.horizon_pos P.dynamics P.initial x ρ) :
    ∀ t, ‖x t‖ ≤ P.tubeRadius := by
  have h := hx.norm_le_of_linear_growth P.horizon_pos P.growthConstant.2 P.growthRate.2
    hshort P.dynamics_growth
  intro t
  have hpoint := (x.norm_coe_le_norm t).trans h
  exact hpoint.trans (le_add_of_nonneg_right zero_le_one)

omit [BorelSpace U] [CompactSpace U] [FiniteDimensional ℝ E] in
theorem localized_trajectory_norm_le (hshort : P.horizon * P.growthRate < 1)
    {x : P.Path} {ρ : P.Relaxed}
    (hx : IsRelaxedTrajectory P.horizon_pos (P.localized hshort).dynamics P.initial x ρ) :
    ∀ t, ‖x t‖ ≤ P.tubeRadius := by
  have hg : ∀ t y u, ‖(P.localized hshort).dynamics t y u‖ ≤
      P.growthConstant + P.growthRate * ‖y‖ := fun t y u ↦
    (P.dynamics_growth _ _ _).trans (add_le_add_right
      (mul_le_mul_of_nonneg_left (norm_radialClip_le (P.tubeRadius_pos hshort) y)
        P.growthRate.2) _)
  have h := hx.norm_le_of_linear_growth P.horizon_pos P.growthConstant.2 P.growthRate.2
    hshort hg
  intro t
  have hpoint := (x.norm_coe_le_norm t).trans h
  exact hpoint.trans (le_add_of_nonneg_right zero_le_one)

omit [BorelSpace U] [CompactSpace U] [FiniteDimensional ℝ E] in
theorem relaxedAdmissible_localized_iff (hshort : P.horizon * P.growthRate < 1)
    (x : P.Path) (ρ : P.Relaxed) :
    (P.localized hshort).RelaxedAdmissible x ρ ↔ P.RelaxedAdmissible x ρ := by
  constructor
  · intro hx
    have htube := P.localized_trajectory_norm_le hshort hx.1
    refine ⟨?_, hx.2⟩
    intro t
    convert hx.1 t using 1
    congr 3
    funext z
    exact (congrArg (fun y ↦ P.dynamics z.1 y z.2)
      (radialClip_eq (P.tubeRadius_pos hshort) (htube z.1))).symm
  · intro hx
    have htube := P.trajectory_norm_le hshort hx.1
    refine ⟨?_, hx.2⟩
    intro t
    convert hx.1 t using 1
    congr 3
    funext z
    exact congrArg (fun y ↦ P.dynamics z.1 y z.2)
      (radialClip_eq (P.tubeRadius_pos hshort) (htube z.1))

/-- Actual relaxed existence for linear-growth dynamics on short horizons, optimal against
every admissible competitor of the original unbounded problem. -/
theorem exists_relaxed_minimizer (hshort : P.horizon * P.growthRate < 1)
    (hfeasible : ∃ x ρ, P.RelaxedAdmissible x ρ) :
    ∃ x ρ, P.RelaxedAdmissible x ρ ∧
      ∀ y σ, P.RelaxedAdmissible y σ → P.relaxedCost x ρ ≤ P.relaxedCost y σ := by
  obtain ⟨x₀, ρ₀, h₀⟩ := hfeasible
  obtain ⟨x, ρ, hx, hmin⟩ := (P.localized hshort).exists_relaxed_minimizer
    ⟨x₀, ρ₀, (P.relaxedAdmissible_localized_iff hshort _ _).2 h₀⟩
  refine ⟨x, ρ, (P.relaxedAdmissible_localized_iff hshort _ _).1 hx, ?_⟩
  intro y σ hy
  exact hmin y σ ((P.relaxedAdmissible_localized_iff hshort _ _).2 hy)

/-- Measurable controls with actual integral dynamics and the original constraints. -/
def OrdinaryAdmissible (x : P.Path) (u : P.Time → U) : Prop :=
  Measurable u ∧
    (∀ t, x t = P.initial + P.horizon • ∫ s in Ioc (timeZero P.horizon P.horizon_pos.le) t,
      P.dynamics s (x s) (u s) ∂horizonProbability P.horizon P.horizon_pos) ∧
    x (timeEnd P.horizon P.horizon_pos.le) ∈ P.target ∧ ∀ t, x t ∈ P.stateConstraint t

noncomputable def ordinaryCost (x : P.Path) (u : P.Time → U) : ℝ :=
  P.terminalCost (x (timeEnd P.horizon P.horizon_pos.le)) +
    P.horizon * ∫ t, P.runningCost t (x t) (u t) ∂horizonProbability P.horizon P.horizon_pos

omit [FiniteDimensional ℝ E] in
theorem OrdinaryAdmissible.to_relaxed {P : LinearGrowthProblem E U} {x : P.Path}
    {u : P.Time → U} (hu : P.OrdinaryAdmissible x u) :
    P.RelaxedAdmissible x (RelaxedControl.ofControl
      (horizonProbability P.horizon P.horizon_pos) u hu.1) := by
  refine ⟨?_, hu.2.2⟩
  intro t
  rw [RelaxedControl.setIntegral_ofControl _ u hu.1 measurableSet_Ioc _
    (integrable_trajectoryField P.horizon_pos P.dynamics
      P.dynamics_continuous x _).aestronglyMeasurable]
  exact hu.2.1 t

omit [FiniteDimensional ℝ E] in
theorem ordinaryAdmissible_localized_iff (hshort : P.horizon * P.growthRate < 1)
    (x : P.Path) (u : P.Time → U) :
    (P.localized hshort).OrdinaryAdmissible x u ↔ P.OrdinaryAdmissible x u := by
  constructor
  · intro hu
    have hr := (P.relaxedAdmissible_localized_iff hshort _ _).1 hu.to_relaxed
    have htube := P.trajectory_norm_le hshort hr.1
    refine ⟨hu.1, ?_, hu.2.2⟩
    intro t
    convert hu.2.1 t using 1
    congr 3
    funext s
    exact (congrArg (fun y ↦ P.dynamics s y (u s))
      (radialClip_eq (P.tubeRadius_pos hshort) (htube s))).symm
  · intro hu
    have htube := P.trajectory_norm_le hshort hu.to_relaxed.1
    refine ⟨hu.1, ?_, hu.2.2⟩
    intro t
    convert hu.2.1 t using 1
    congr 3
    funext s
    exact congrArg (fun y ↦ P.dynamics s y (u s))
      (radialClip_eq (P.tubeRadius_pos hshort) (htube s))

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {K : Set V} [CompactSpace K] [Nonempty K]

/-- Control-affinity and convex running cost for the original, unbounded dynamics. -/
structure AffineConvexData (P : LinearGrowthProblem E K) where
  drift : P.Time → E → E
  inputMap : P.Time → E → V →L[ℝ] E
  dynamics_eq : ∀ t x (u : K), P.dynamics t x u = drift t x + inputMap t x (u : V)
  costExtension : P.Time → E → V → ℝ
  cost_eq : ∀ t x (u : K), P.runningCost t x u = costExtension t x (u : V)
  cost_convex : ∀ t x, ConvexOn ℝ K (costExtension t x)

/-- Clipping the state preserves affinity in the control. -/
noncomputable def AffineConvexData.localized {P : LinearGrowthProblem E K} (A : P.AffineConvexData)
    (hshort : P.horizon * P.growthRate < 1) :
    (P.localized hshort).AffineConvexData where
  drift := fun t x ↦ A.drift t (radialClip P.tubeRadius x)
  inputMap := fun t x ↦ A.inputMap t (radialClip P.tubeRadius x)
  dynamics_eq := fun t x u ↦ A.dynamics_eq t (radialClip P.tubeRadius x) u
  costExtension := A.costExtension
  cost_eq := A.cost_eq
  cost_convex := A.cost_convex

/-- Ordinary existence with linear-growth dynamics. The constructed control is optimal
against every ordinary competitor of the original problem, without imposing a tube on them. -/
theorem exists_ordinary_minimizer (P : LinearGrowthProblem E K)
    (A : P.AffineConvexData) (hK : Convex ℝ K)
    (hshort : P.horizon * P.growthRate < 1)
    (hfeasible : ∃ x u, P.OrdinaryAdmissible x u) :
    ∃ x u, P.OrdinaryAdmissible x u ∧
      ∀ y v, P.OrdinaryAdmissible y v → P.ordinaryCost x u ≤ P.ordinaryCost y v := by
  obtain ⟨x₀, u₀, h₀⟩ := hfeasible
  obtain ⟨x, u, hx, hmin⟩ := (P.localized hshort).exists_ordinary_minimizer
    (A.localized hshort) hK ⟨x₀, u₀, (P.ordinaryAdmissible_localized_iff hshort _ _).2 h₀⟩
  refine ⟨x, u, (P.ordinaryAdmissible_localized_iff hshort _ _).1 hx, ?_⟩
  intro y v hy
  exact hmin y v ((P.ordinaryAdmissible_localized_iff hshort _ _).2 hy)

end LinearGrowthProblem
end OptimalControl
