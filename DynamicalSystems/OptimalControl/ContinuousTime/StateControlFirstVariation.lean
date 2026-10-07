/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.StateConstraintMultipliers
public import DynamicalSystems.Mathlib.Analysis.Calculus.IntegralAffineVariation
public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Necessary first variation of actual state-constrained integral control functionals

Primitive C¹ terminal, running and constraint data differentiate the actual penalized Bolza
functional along affine candidate variations. Compact controls and continuous trajectories
derive the uniform bounds needed by differentiation under both Lebesgue and constraint
measures. Actual constrained optimality constructs the measure and proves a nonnegative
first variation against every dynamics competitor, including for abnormal multipliers.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology NNReal

namespace OptimalControl.ConvexStateControlProblem

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] {n : ℕ}

/-- Actual C¹ derivatives of the primitive problem data. The running derivative acts
jointly on state and control; the state-constraint derivative acts only on the state. -/
structure ContinuouslyDifferentiableData (P : OptimalControl.ConvexStateControlProblem E V n) where
  terminalDerivative : E → E →L[ℝ] ℝ
  terminalDerivative_continuous : Continuous terminalDerivative
  terminal_hasFDerivAt : ∀ x, HasFDerivAt P.terminalCost (terminalDerivative x) x
  runningDerivative : P.Time → E × V → (E × V) →L[ℝ] ℝ
  runningDerivative_continuous : Continuous (fun p : P.Time × (E × V) ↦
    runningDerivative p.1 p.2)
  running_hasFDerivAt : ∀ t x,
    HasFDerivAt (fun a : E × V ↦ P.runningCost t a.1 a.2) (runningDerivative t x) x
  constraintDerivative : P.ConstraintIndex → E → E →L[ℝ] ℝ
  constraintDerivative_continuous : Continuous (fun p : P.ConstraintIndex × E ↦
    constraintDerivative p.1 p.2)
  constraint_hasFDerivAt : ∀ q x, HasFDerivAt (P.constraint q) (constraintDerivative q x) x

variable (P : OptimalControl.ConvexStateControlProblem E V n)

/-- The actual affine variation of the continuous trajectory and measurable control. -/
noncomputable def candidateAffineVariation (z y : P.Candidate) (θ : ℝ) : P.Candidate :=
  z + θ • (y - z)

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
@[simp] theorem candidateAffineVariation_zero (z y : P.Candidate) :
    P.candidateAffineVariation z y 0 = z := by simp [candidateAffineVariation]

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] in
/-- On the right unit interval the affine variation is a genuine convex candidate mixture. -/
theorem candidateAffineVariation_eq_convex (z y : P.Candidate) (θ : ℝ) :
    P.candidateAffineVariation z y θ = (1 - θ) • z + θ • y := by
  unfold candidateAffineVariation
  rw [smul_sub, sub_smul, one_smul]
  abel

/-- Every right-unit-interval mixture satisfies the original integral dynamics. -/
theorem dynamicsAdmissible_candidateAffineVariation (z y : P.Candidate)
    (hz : P.DynamicsAdmissible z) (hy : P.DynamicsAdmissible y)
    {θ : ℝ} (hθ : θ ∈ Icc 0 1) :
    P.DynamicsAdmissible (P.candidateAffineVariation z y θ) := by
  rw [P.candidateAffineVariation_eq_convex]
  exact P.convex_dynamicsAdmissible hz hy (sub_nonneg.mpr hθ.2) hθ.1 (by ring)

omit [BorelSpace V] [SecondCountableTopology V] in
/-- Compact control values and continuous trajectory images derive a uniform candidate bound. -/
theorem exists_candidate_norm_bound (z : P.Candidate) (hz : P.DynamicsAdmissible z) :
    ∃ R : ℝ≥0, (∀ t, ‖z.1 t‖ ≤ R) ∧ ∀ t, ‖z.2 t‖ ≤ R := by
  obtain ⟨Cx, hCx⟩ := (isCompact_range z.1.continuous).isBounded.exists_norm_le
  obtain ⟨Cu, hCu⟩ := P.controlSet_compact.isBounded.exists_norm_le
  let R : ℝ≥0 := Real.toNNReal (max (max Cx Cu) 0)
  have hR : (R : ℝ) = max (max Cx Cu) 0 := Real.coe_toNNReal _ (le_max_right _ _)
  refine ⟨R, ?_, ?_⟩
  · intro t
    rw [hR]
    exact (hCx _ ⟨t, rfl⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
  · intro t
    rw [hR]
    exact (hCu _ (hz.2.1 t)).trans ((le_max_right _ _).trans (le_max_left _ _))

/-- The actual penalized functional for a finite positive state-constraint measure. -/
noncomputable def penalizedCost (α : ℝ) (μ : Measure P.ConstraintIndex) (z : P.Candidate) : ℝ :=
  α * P.cost z + ∫ q, P.residual z q ∂μ

/-- Explicit terminal/running/constraint first variation against a dynamics competitor. -/
noncomputable def stateControlFirstVariation (D : P.ContinuouslyDifferentiableData)
    (α : ℝ) (μ : Measure P.ConstraintIndex) (z y : P.Candidate) : ℝ :=
  α * (D.terminalDerivative (z.1 (timeEnd P.horizon P.horizon_pos.le))
      (y.1 (timeEnd P.horizon P.horizon_pos.le) - z.1 (timeEnd P.horizon P.horizon_pos.le)) +
    P.horizon * ∫ t, D.runningDerivative t (z.1 t, z.2 t)
      (y.1 t - z.1 t, y.2 t - z.2 t) ∂horizonProbability P.horizon P.horizon_pos) +
  ∫ q, D.constraintDerivative q (z.1 q.1) (y.1 q.1 - z.1 q.1) ∂μ

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ V]

/-- The running and constraint first variations are integrable, and the actual penalized
functional has the displayed derivative. No variation or domination certificate is assumed. -/
theorem hasDerivAt_penalizedCost_candidateAffineVariation
    (D : P.ContinuouslyDifferentiableData) (α : ℝ) (μ : Measure P.ConstraintIndex)
    [IsFiniteMeasure μ] (z y : P.Candidate)
    (hz : P.DynamicsAdmissible z) (hy : P.DynamicsAdmissible y) :
    Integrable (fun t ↦ D.runningDerivative t (z.1 t, z.2 t)
      (y.1 t - z.1 t, y.2 t - z.2 t))
        (horizonProbability P.horizon P.horizon_pos).toMeasure ∧
    Integrable (fun q ↦ D.constraintDerivative q (z.1 q.1) (y.1 q.1 - z.1 q.1)) μ ∧
    HasDerivAt (fun θ ↦ P.penalizedCost α μ (P.candidateAffineVariation z y θ))
      (P.stateControlFirstVariation D α μ z y) 0 := by
  obtain ⟨Rz, hzx, hzu⟩ := P.exists_candidate_norm_bound z hz
  obtain ⟨Ry, hyx, hyu⟩ := P.exists_candidate_norm_bound y hy
  let R : ℝ≥0 := Rz + Ry + Rz
  have hRzn : 0 ≤ (Rz : ℝ) := Rz.2
  have hRyn : 0 ≤ (Ry : ℝ) := Ry.2
  have hRz : (Rz : ℝ) ≤ R := by
    change (Rz : ℝ) ≤ (Rz : ℝ) + Ry + Rz
    linarith
  have hRdir : (Ry : ℝ) + Rz ≤ R := by
    change (Ry : ℝ) + Rz ≤ (Rz : ℝ) + Ry + Rz
    linarith
  have hstate (t : P.Time) : ‖z.1 t‖ ≤ R := (hzx t).trans hRz
  have hstateDir (t : P.Time) : ‖y.1 t - z.1 t‖ ≤ R :=
    (norm_sub_le _ _).trans ((add_le_add (hyx t) (hzx t)).trans hRdir)
  have hpair (t : P.Time) : ‖(z.1 t, z.2 t)‖ ≤ R := by
    exact max_le ((hzx t).trans hRz) ((hzu t).trans hRz)
  have hpairDir (t : P.Time) : ‖(y.1 t - z.1 t, y.2 t - z.2 t)‖ ≤ R :=
    max_le (hstateDir t) ((norm_sub_le _ _).trans
      ((add_le_add (hyu t) (hzu t)).trans hRdir))
  have hg : Continuous (fun p : P.Time × (E × V) ↦ P.runningCost p.1 p.2.1 p.2.2) :=
    P.runningCost_continuous.comp
      ((continuous_fst.prodMk continuous_snd.fst).prodMk continuous_snd.snd)
  have hzpair : Measurable (fun t ↦ (z.1 t, z.2 t)) := z.1.continuous.measurable.prodMk hz.1
  have hdpair : Measurable (fun t ↦ (y.1 t - z.1 t, y.2 t - z.2 t)) :=
    (y.1.continuous.measurable.sub z.1.continuous.measurable).prodMk (hy.1.sub hz.1)
  have hr := IntegralAffineVariation.hasDerivAt_integral_affine_of_bounded
    (μ := (horizonProbability P.horizon P.horizon_pos).toMeasure)
    (fun (t : P.Time) (a : E × V) ↦ P.runningCost t a.1 a.2) D.runningDerivative hg
    D.runningDerivative_continuous D.running_hasFDerivAt
    (fun t ↦ (z.1 t, z.2 t)) (fun t ↦ (y.1 t - z.1 t, y.2 t - z.2 t))
    hzpair hdpair R hpair hpairDir
  have hzc : Measurable (fun q : P.ConstraintIndex ↦ z.1 q.1) :=
    z.1.continuous.measurable.comp measurable_fst
  have hdc : Measurable (fun q : P.ConstraintIndex ↦ y.1 q.1 - z.1 q.1) :=
    (y.1.continuous.measurable.comp measurable_fst).sub hzc
  have hc := IntegralAffineVariation.hasDerivAt_integral_affine_of_bounded
    (μ := μ) P.constraint D.constraintDerivative P.constraint_continuous
    D.constraintDerivative_continuous D.constraint_hasFDerivAt
    (fun q ↦ z.1 q.1) (fun q ↦ y.1 q.1 - z.1 q.1)
    hzc hdc R (fun q ↦ hstate q.1) (fun q ↦ hstateDir q.1)
  let tEnd := timeEnd P.horizon P.horizon_pos.le
  have hterminal : HasFDerivAt P.terminalCost (D.terminalDerivative (z.1 tEnd))
      (z.1 tEnd + (0 : ℝ) • (y.1 tEnd - z.1 tEnd)) := by
    simpa using D.terminal_hasFDerivAt (z.1 tEnd)
  have ht := hterminal.comp_hasDerivAt 0
    (show HasDerivAt (fun θ : ℝ ↦ z.1 tEnd + θ • (y.1 tEnd - z.1 tEnd))
      (y.1 tEnd - z.1 tEnd) 0 by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y.1 tEnd - z.1 tEnd)).const_add (z.1 tEnd))
  refine ⟨hr.1, hc.1, ?_⟩
  convert (ht.add (hr.2.const_mul P.horizon)).const_mul α |>.add hc.2 using 1
  · funext θ
    rfl
  · rfl

/-- A derivative at a minimum over a right unit interval is nonnegative. This does not
require monotonicity of the function or an unconstrained local minimum. -/
theorem hasDerivAt_nonneg_of_unit_right_minimum {f : ℝ → ℝ} {a : ℝ}
    (hf : HasDerivAt f a 0) (hmin : ∀ θ ∈ Icc (0 : ℝ) 1, f 0 ≤ f θ) : 0 ≤ a := by
  apply ge_of_tendsto hf.tendsto_slope_zero_right
  have hlt : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ < 1 :=
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hlt] with θ hθ hθ1
  have hm := hmin θ ⟨hθ.le, hθ1.le⟩
  simpa [smul_eq_mul] using mul_nonneg (inv_nonneg.mpr hθ.le) (sub_nonneg.mpr hm)

/-- A convex differentiable function lies above its actual first-order support. The
support inequality follows from convex segment comparison and a right derivative minimum. -/
theorem convex_supporting_derivative {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : W → ℝ) (hf : ConvexOn ℝ univ f) (x y : W) (D : W →L[ℝ] ℝ)
    (hD : HasFDerivAt f D x) : f x + D (y - x) ≤ f y := by
  let h : ℝ → ℝ := fun θ ↦ (1 - θ) * f x + θ * f y - f (x + θ • (y - x))
  have hbase : HasFDerivAt f D (x + (0 : ℝ) • (y - x)) := by simpa using hD
  have ha := hbase.comp_hasDerivAt 0
    (show HasDerivAt (fun θ : ℝ ↦ x + θ • (y - x)) (y - x) 0 by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x)
  have h1 := ((hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub
    (hasDerivAt_id 0)).mul_const (f x)
  have h2 := (hasDerivAt_id (0 : ℝ)).mul_const (f y)
  have hd : HasDerivAt h (-f x + f y - D (y - x)) 0 := by
    convert (h1.add h2).sub ha using 1
    · funext θ
      rfl
    · simp
  have hmin : ∀ θ ∈ Icc (0 : ℝ) 1, h 0 ≤ h θ := by
    intro θ hθ
    have hc := hf.2 (mem_univ x) (mem_univ y) (sub_nonneg.mpr hθ.2) hθ.1
      (show (1 - θ) + θ = 1 by ring)
    have he : x + θ • (y - x) = (1 - θ) • x + θ • y := by
      rw [smul_sub, sub_smul, one_smul]
      abel
    simp only [smul_eq_mul] at hc
    simp only [h, zero_smul, add_zero, sub_zero, one_mul]
    rw [he]
    linarith
  have hn := hasDerivAt_nonneg_of_unit_right_minimum hd hmin
  linarith

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [FiniteDimensional ℝ V] in
/-- Primitive joint convexity and the actual joint derivative imply the Hamiltonian
support inequality in the control variable. No supporting inequality is supplied. -/
theorem runningCost_supporting_controlDerivative
    (D : P.ContinuouslyDifferentiableData) (t : P.Time) (x : E) (u v : V) :
    P.runningCost t x u + D.runningDerivative t (x, u) (0, v - u) ≤ P.runningCost t x v := by
  have h := convex_supporting_derivative
    (fun a : E × V ↦ P.runningCost t a.1 a.2) (P.runningCost_convex t)
    (x, u) (x, v) (D.runningDerivative t (x, u)) (D.running_hasFDerivAt t (x, u))
  simpa using h

/-- An actual penalized minimum over dynamics competitors yields the necessary first
variation against every such competitor. The derivative itself is derived from primitive
C¹ data; only genuine convex mixtures on `[0,1]` are used for minimum comparison. -/
theorem firstVariation_nonneg_of_penalized_minimum
    (D : P.ContinuouslyDifferentiableData) (α : ℝ) (μ : Measure P.ConstraintIndex)
    [IsFiniteMeasure μ] (z : P.Candidate) (hz : P.DynamicsAdmissible z)
    (hmin : ∀ a, P.DynamicsAdmissible a → P.penalizedCost α μ z ≤ P.penalizedCost α μ a)
    (y : P.Candidate) (hy : P.DynamicsAdmissible y) :
    0 ≤ P.stateControlFirstVariation D α μ z y := by
  have hd := (P.hasDerivAt_penalizedCost_candidateAffineVariation D α μ z y hz hy).2.2
  apply hasDerivAt_nonneg_of_unit_right_minimum hd
  intro θ hθ
  have hm := hmin (P.candidateAffineVariation z y θ)
    (P.dynamicsAdmissible_candidateAffineVariation z y hz hy hθ)
  simpa using hm

/-- Actual constrained optimality constructs positive finite state measures, complementary
slackness and contact concentration, and a nonnegative first variation against every original
dynamics competitor. The cost multiplier may vanish; no first-variation premise is supplied. -/
theorem exists_nonnegative_firstVariation_of_isMinimum
    (D : P.ContinuouslyDifferentiableData) (z : P.Candidate) (hz : P.IsMinimum z) :
    ∃ (α : ℝ) (μ : Measure P.ConstraintIndex), IsFiniteMeasure μ ∧ 0 ≤ α ∧
      (α ≠ 0 ∨ μ ≠ 0) ∧ (∫ q, P.residual z q ∂μ) = 0 ∧
      μ {q | P.residual z q ≠ 0} = 0 ∧
      ∀ y, P.DynamicsAdmissible y → 0 ≤ P.stateControlFirstVariation D α μ z y := by
  obtain ⟨α, μ, hfin, hα, hne, hcomp, hsupp, hlag⟩ := P.exists_measure_of_isMinimum z hz
  let : IsFiniteMeasure μ := hfin
  have hmin : ∀ a, P.DynamicsAdmissible a → P.penalizedCost α μ z ≤ P.penalizedCost α μ a := by
    intro a ha
    simpa [penalizedCost, hcomp] using hlag a ha
  exact ⟨α, μ, hfin, hα, hne, hcomp, hsupp,
    fun y hy ↦ P.firstVariation_nonneg_of_penalized_minimum D α μ z hz.1 hmin y hy⟩

end OptimalControl.ConvexStateControlProblem
