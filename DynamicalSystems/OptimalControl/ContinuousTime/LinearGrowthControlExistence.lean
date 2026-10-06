/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.LocalizedControlExistence
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Existence for linearly growing dynamics on arbitrary finite horizons

The scalar envelope `‖x₀‖ + ∫ (a + b * ‖x(s)‖) ds` is continuously differentiable,
although actual controls need only be measurable. Its derivative satisfies Grönwall's
inequality because the original Volterra equation bounds the trajectory by this envelope.
The fixed occupation time marginal converts the envelope integral to actual Lebesgue time.

Radial clipping on the derived tube yields a globally bounded field. Every original and
clipped admissible trajectory stays in that tube, so their admissibility predicates coincide.
The bounded-data minimizer thus solves the original problem against all competitors.
Control-affinity and convex running cost yield ordinary measurable controls by the existing
barycentric recovery theorem. Endpoints and every state constraint are preserved.

Only primitive data continuity, a global linear-growth estimate, compact controls, closed
constraints, and one feasible pair are required. No short-horizon restriction, supplied
trajectory tube, compactness certificate, or selection hypothesis occurs in the final API.
-/

@[expose] public section

open Set MeasureTheory
open scoped BoundedContinuousFunction Topology

namespace OptimalControl

variable {T : ℝ} {U : Type*} [MetricSpace U] [MeasurableSpace U] [BorelSpace U]
  [CompactSpace U]

omit [MetricSpace U] [BorelSpace U] [CompactSpace U] in
/-- Undoing the occupation time marginal and its normalization gives the actual Lebesgue
integral, including restriction to a time prefix. -/
theorem RelaxedControl.scaled_setIntegral_time (hT : 0 < T)
    (ρ : RelaxedControl (ControlTime T) U (horizonProbability T hT))
    (g : ℝ → ℝ) (hg : Continuous g) (t : ControlTime T) :
    T * (∫ z in Ioc (timeZero T hT.le) t ×ˢ univ, g (z.1 : ℝ) ∂ρ.measure) =
      ∫ s in (0 : ℝ)..(t : ℝ), g s := by
  have hm := ρ.fst_measure
  have hgsub : Continuous (fun s : ControlTime T ↦ g (s : ℝ)) :=
    hg.comp continuous_subtype_val
  have hmap := setIntegral_map (μ := ρ.measure) (g := Prod.fst)
    (f := fun s : ControlTime T ↦ g (s : ℝ)) (s := Ioc (timeZero T hT.le) t)
    measurableSet_Ioc (by rw [← Measure.fst, hm]; exact hgsub.aestronglyMeasurable)
    measurable_fst.aemeasurable
  have hpre : Prod.fst ⁻¹' Ioc (timeZero T hT.le) t =
      Ioc (timeZero T hT.le) t ×ˢ (univ : Set U) := by ext z; simp
  rw [hpre, ← Measure.fst, hm] at hmap
  rw [← hmap]
  have hscale := congrArg (fun μ : Measure (ControlTime T) ↦
      ∫ s in Ioc (timeZero T hT.le) t, g (s : ℝ) ∂μ) (scale_horizonProbability T hT)
  rw [Measure.restrict_smul, integral_smul_measure] at hscale
  simp only [ENNReal.toReal_ofReal hT.le, smul_eq_mul] at hscale
  rw [hscale]
  have hreal := (MeasurableEmbedding.subtype_coe measurableSet_Icc).setIntegral_map
    g (Ioc (0 : ℝ) (t : ℝ)) (μ := horizonVolume T)
  rw [map_horizonVolume] at hreal
  have hpreal : ((↑) : ControlTime T → ℝ) ⁻¹' Ioc (0 : ℝ) (t : ℝ) =
      Ioc (timeZero T hT.le) t := rfl
  rw [hpreal, Measure.restrict_restrict measurableSet_Ioc] at hreal
  have hinter : Ioc (0 : ℝ) (t : ℝ) ∩ Icc 0 T = Ioc (0 : ℝ) (t : ℝ) :=
    inter_eq_left.mpr (fun s hs ↦ ⟨hs.1.le, hs.2.trans t.2.2⟩)
  rw [hinter] at hreal
  rw [← hreal, intervalIntegral.integral_of_le t.2.1]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A Grönwall tube derived from actual measurable-control integral dynamics. The smooth
scalar envelope has continuous derivative even though the control itself is only measurable. -/
theorem IsRelaxedTrajectory.norm_le_gronwall_of_linear_growth {a b : ℝ} (hT : 0 < T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) {f : ControlTime T → E → U → E}
    {x₀ : E} {x : ControlTime T →ᵇ E}
    {ρ : RelaxedControl (ControlTime T) U (horizonProbability T hT)}
    (hgrowth : ∀ t y u, ‖f t y u‖ ≤ a + b * ‖y‖)
    (hx : IsRelaxedTrajectory hT f x₀ x ρ) :
    ‖x‖ ≤ gronwallBound ‖x₀‖ b a T := by
  let g : ℝ → ℝ := fun s ↦ a + b * ‖x (projIcc 0 T hT.le s)‖
  have hg : Continuous g := continuous_const.add (continuous_const.mul
    (x.continuous.comp continuous_projIcc).norm)
  have hproj (s : ControlTime T) : projIcc 0 T hT.le (s : ℝ) = s := by
    apply Subtype.ext
    simp [projIcc, min_eq_right s.2.2, max_eq_right s.2.1]
  let F : ℝ → ℝ := fun t ↦ ‖x₀‖ + ∫ s in (0 : ℝ)..t, g s
  have hFderiv (t : ℝ) : HasDerivAt F (g t) t :=
    (hg.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add _
  have hFcont : Continuous F :=
    (show Differentiable ℝ F from fun t ↦ (hFderiv t).differentiableAt).continuous
  have hpoint (t : ControlTime T) : ‖x t‖ ≤ F (t : ℝ) := by
    rw [hx t]
    refine (norm_add_le _ _).trans (add_le_add_right ?_ _)
    rw [norm_smul, Real.norm_of_nonneg hT.le]
    have hgi : Integrable (fun z : ControlTime T × U ↦ g (z.1 : ℝ)) ρ.measure :=
      (hg.comp (continuous_subtype_val.comp continuous_fst)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    calc
      T * ‖∫ z in Ioc (timeZero T hT.le) t ×ˢ univ,
          f z.1 (x z.1) z.2 ∂ρ.measure‖ ≤
          T * ∫ z in Ioc (timeZero T hT.le) t ×ˢ univ, g (z.1 : ℝ) ∂ρ.measure := by
        apply mul_le_mul_of_nonneg_left _ hT.le
        apply norm_integral_le_of_norm_le hgi.integrableOn
        exact Filter.Eventually.of_forall (fun z ↦ by
          simpa [g, hproj] using hgrowth z.1 (x z.1) z.2)
      _ = ∫ s in (0 : ℝ)..(t : ℝ), g s := ρ.scaled_setIntegral_time hT g hg t
  have hbound : ∀ t ∈ Ico (0 : ℝ) T, ‖g t‖ ≤ b * ‖F t‖ + a := by
    intro t ht
    let s : ControlTime T := ⟨t, ht.1, ht.2.le⟩
    have hnorm : ‖x s‖ ≤ ‖F t‖ := (hpoint s).trans (le_abs_self _)
    have hgval : g t = a + b * ‖x s‖ := by
      change a + b * ‖x (projIcc 0 T hT.le (s : ℝ))‖ = _
      rw [hproj]
    rw [hgval, Real.norm_of_nonneg (by positivity)]
    linarith [mul_le_mul_of_nonneg_left hnorm hb]
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le hFcont.continuousOn
    (fun t _ ↦ (hFderiv t).hasDerivWithinAt)
    (δ := ‖x₀‖) (by simp [F]) hbound
  apply (BoundedContinuousFunction.norm_le
    ((norm_nonneg (F T)).trans (by simpa using hgr T ⟨hT.le, le_rfl⟩))).2
  intro t
  calc
    ‖x t‖ ≤ ‖F (t : ℝ)‖ := (hpoint t).trans (le_abs_self _)
    _ ≤ gronwallBound ‖x₀‖ b a (t : ℝ) := by simpa using hgr t t.2
    _ ≤ gronwallBound ‖x₀‖ b a T :=
      gronwallBound_mono (norm_nonneg _) ha hb t.2.2

namespace LinearGrowthProblem

variable (P : LinearGrowthProblem E U)

/-- A strictly positive radius exceeding the derived Grönwall tube by one. -/
noncomputable def gronwallRadius : ℝ :=
  gronwallBound ‖P.initial‖ P.growthRate P.growthConstant P.horizon + 1

omit [MeasurableSpace U] [BorelSpace U] [CompactSpace U] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] in
theorem gronwallRadius_pos : 0 < P.gronwallRadius := by
  have h := gronwallBound_mono (norm_nonneg P.initial) P.growthConstant.2 P.growthRate.2
    P.horizon_pos.le
  rw [gronwallBound_x0] at h
  have hn : 0 ≤ gronwallBound ‖P.initial‖ P.growthRate P.growthConstant P.horizon :=
    (norm_nonneg _).trans h
  exact add_pos_of_nonneg_of_pos hn zero_lt_one

/-- The bounded extension changes only the dynamics, leaving costs and constraints intact. -/
noncomputable def gronwallLocalized :
    BoundedContinuousProblem E U where
  horizon := P.horizon
  horizon_pos := P.horizon_pos
  initial := P.initial
  dynamics := fun t x u ↦ P.dynamics t (radialClip P.gronwallRadius x) u
  dynamics_continuous := P.dynamics_continuous.comp
    ((continuous_fst.fst.prodMk
      ((continuous_radialClip (P.gronwallRadius_pos)).comp continuous_fst.snd)).prodMk
        continuous_snd)
  velocityBound := ⟨P.growthConstant + P.growthRate * P.gronwallRadius, by
    have := (P.gronwallRadius_pos).le
    positivity⟩
  dynamics_bound := fun t x u ↦ (P.dynamics_growth _ _ _).trans
    (add_le_add_right (mul_le_mul_of_nonneg_left
      (norm_radialClip_le_radius (P.gronwallRadius_pos) x) P.growthRate.2) _)
  runningCost := P.runningCost
  runningCost_continuous := P.runningCost_continuous
  terminalCost := P.terminalCost
  terminalCost_continuous := P.terminalCost_continuous
  target := P.target
  target_closed := P.target_closed
  stateConstraint := P.stateConstraint
  stateConstraint_closed := P.stateConstraint_closed

omit [FiniteDimensional ℝ E] in
theorem trajectory_norm_le_global
    {x : P.Path} {ρ : P.Relaxed}
    (hx : IsRelaxedTrajectory P.horizon_pos P.dynamics P.initial x ρ) :
    ∀ t, ‖x t‖ ≤ P.gronwallRadius := by
  have h := hx.norm_le_gronwall_of_linear_growth P.horizon_pos P.growthConstant.2 P.growthRate.2
    P.dynamics_growth
  intro t
  have hpoint := (x.norm_coe_le_norm t).trans h
  exact hpoint.trans (le_add_of_nonneg_right zero_le_one)

omit [FiniteDimensional ℝ E] in
theorem gronwallLocalized_trajectory_norm_le_global
    {x : P.Path} {ρ : P.Relaxed}
    (hx : IsRelaxedTrajectory P.horizon_pos (P.gronwallLocalized).dynamics P.initial x ρ) :
    ∀ t, ‖x t‖ ≤ P.gronwallRadius := by
  have hg : ∀ t y u, ‖(P.gronwallLocalized).dynamics t y u‖ ≤
      P.growthConstant + P.growthRate * ‖y‖ := fun t y u ↦
    (P.dynamics_growth _ _ _).trans (add_le_add_right
      (mul_le_mul_of_nonneg_left (norm_radialClip_le (P.gronwallRadius_pos) y)
        P.growthRate.2) _)
  have h := hx.norm_le_gronwall_of_linear_growth P.horizon_pos P.growthConstant.2 P.growthRate.2
    hg
  intro t
  have hpoint := (x.norm_coe_le_norm t).trans h
  exact hpoint.trans (le_add_of_nonneg_right zero_le_one)

omit [FiniteDimensional ℝ E] in
theorem relaxedAdmissible_gronwallLocalized_iff
    (x : P.Path) (ρ : P.Relaxed) :
    (P.gronwallLocalized).RelaxedAdmissible x ρ ↔ P.RelaxedAdmissible x ρ := by
  constructor
  · intro hx
    have htube := P.gronwallLocalized_trajectory_norm_le_global hx.1
    refine ⟨?_, hx.2⟩
    intro t
    convert hx.1 t using 1
    congr 3
    funext z
    exact (congrArg (fun y ↦ P.dynamics z.1 y z.2)
      (radialClip_eq (P.gronwallRadius_pos) (htube z.1))).symm
  · intro hx
    have htube := P.trajectory_norm_le_global hx.1
    refine ⟨?_, hx.2⟩
    intro t
    convert hx.1 t using 1
    congr 3
    funext z
    exact congrArg (fun y ↦ P.dynamics z.1 y z.2)
      (radialClip_eq (P.gronwallRadius_pos) (htube z.1))

/-- Actual relaxed existence for linear-growth dynamics on arbitrary finite horizons,
optimal against every admissible competitor of the original unbounded problem. -/
theorem exists_relaxed_minimizer_global
    (hfeasible : ∃ x ρ, P.RelaxedAdmissible x ρ) :
    ∃ x ρ, P.RelaxedAdmissible x ρ ∧
      ∀ y σ, P.RelaxedAdmissible y σ → P.relaxedCost x ρ ≤ P.relaxedCost y σ := by
  obtain ⟨x₀, ρ₀, h₀⟩ := hfeasible
  obtain ⟨x, ρ, hx, hmin⟩ := (P.gronwallLocalized).exists_relaxed_minimizer
    ⟨x₀, ρ₀, (P.relaxedAdmissible_gronwallLocalized_iff _ _).2 h₀⟩
  refine ⟨x, ρ, (P.relaxedAdmissible_gronwallLocalized_iff _ _).1 hx, ?_⟩
  intro y σ hy
  exact hmin y σ ((P.relaxedAdmissible_gronwallLocalized_iff _ _).2 hy)

omit [FiniteDimensional ℝ E] in
theorem ordinaryAdmissible_gronwallLocalized_iff
    (x : P.Path) (u : P.Time → U) :
    (P.gronwallLocalized).OrdinaryAdmissible x u ↔ P.OrdinaryAdmissible x u := by
  constructor
  · intro hu
    have hr := (P.relaxedAdmissible_gronwallLocalized_iff _ _).1 hu.to_relaxed
    have htube := P.trajectory_norm_le_global hr.1
    refine ⟨hu.1, ?_, hu.2.2⟩
    intro t
    convert hu.2.1 t using 1
    congr 3
    funext s
    exact (congrArg (fun y ↦ P.dynamics s y (u s))
      (radialClip_eq (P.gronwallRadius_pos) (htube s))).symm
  · intro hu
    have htube := P.trajectory_norm_le_global hu.to_relaxed.1
    refine ⟨hu.1, ?_, hu.2.2⟩
    intro t
    convert hu.2.1 t using 1
    congr 3
    funext s
    exact congrArg (fun y ↦ P.dynamics s y (u s))
      (radialClip_eq (P.gronwallRadius_pos) (htube s))

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {K : Set V} [CompactSpace K] [Nonempty K]

/-- Clipping the state preserves affinity in the control. -/
noncomputable def AffineConvexData.gronwallLocalized {P : LinearGrowthProblem E K}
    (A : P.AffineConvexData) :
    (P.gronwallLocalized).AffineConvexData where
  drift := fun t x ↦ A.drift t (radialClip P.gronwallRadius x)
  inputMap := fun t x ↦ A.inputMap t (radialClip P.gronwallRadius x)
  dynamics_eq := fun t x u ↦ A.dynamics_eq t (radialClip P.gronwallRadius x) u
  costExtension := A.costExtension
  cost_eq := A.cost_eq
  cost_convex := A.cost_convex

/-- Ordinary existence on arbitrary finite horizons with linear-growth dynamics.
The constructed control is optimal against every ordinary competitor of the original problem,
without imposing a tube on them. -/
theorem exists_ordinary_minimizer_global (P : LinearGrowthProblem E K)
    (A : P.AffineConvexData) (hK : Convex ℝ K)
    (hfeasible : ∃ x u, P.OrdinaryAdmissible x u) :
    ∃ x u, P.OrdinaryAdmissible x u ∧
      ∀ y v, P.OrdinaryAdmissible y v → P.ordinaryCost x u ≤ P.ordinaryCost y v := by
  obtain ⟨x₀, u₀, h₀⟩ := hfeasible
  obtain ⟨x, u, hx, hmin⟩ := (P.gronwallLocalized).exists_ordinary_minimizer
    (A.gronwallLocalized) hK ⟨x₀, u₀, (P.ordinaryAdmissible_gronwallLocalized_iff _ _).2 h₀⟩
  refine ⟨x, u, (P.ordinaryAdmissible_gronwallLocalized_iff _ _).1 hx, ?_⟩
  intro y v hy
  exact hmin y v ((P.ordinaryAdmissible_gronwallLocalized_iff _ _).2 hy)

end LinearGrowthProblem

end OptimalControl
