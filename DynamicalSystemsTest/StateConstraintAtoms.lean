import DynamicalSystems.OptimalControl.ContinuousTime.IntegratorStateMinimumPrinciple
import Mathlib.Tactic.NormNum

/-!
# A state obstacle forcing an interior Dirac multiplier

The measurable integrator reference has zero control up to time one half and unit control
afterward. Its state is `max (t - 1/2) 0`, its cost is negative terminal state, and its
obstacle is `x ≤ 2 * |t - 1/2|`. Actual global optimality compares every measurable integral
trajectory. Contact concentration and the common-AE Hamiltonian condition force the multiplier
measure to be `α δ_(1/2)` with `α > 0`, so the constructed BV costate has a nonzero jump.
-/

open Set MeasureTheory OptimalControl
open scoped Topology

namespace StateConstraintAtoms

@[reducible] noncomputable def obstacleProblem : ConvexStateControlProblem ℝ ℝ 1 where
  horizon := 1
  horizon_pos := by norm_num
  initial := 0
  controlSet := Icc (-1) 1
  controlSet_compact := isCompact_Icc
  controlSet_convex := convex_Icc _ _
  dynamics := fun _ _ u ↦ u
  dynamics_continuous := continuous_snd
  dynamics_affine := fun _ _ _ _ _ _ _ _ _ _ ↦ rfl
  runningCost := fun _ _ _ ↦ 0
  runningCost_continuous := continuous_const
  runningCost_convex := fun _ ↦ convexOn_const 0 convex_univ
  terminalCost := fun x ↦ -x
  terminalCost_convex := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ _
    simp only [smul_eq_mul]
    ring_nf
    exact le_rfl
  constraint := fun q x ↦ x - 2 * |(q.1 : ℝ) - 1 / 2|
  constraint_continuous := continuous_snd.sub
    (continuous_const.mul ((continuous_subtype_val.comp continuous_fst.fst).sub
      continuous_const).abs)
  constraint_convex := fun q ↦ by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b _ _ hab
    simp only [smul_eq_mul]
    have hd := congrArg (fun r : ℝ ↦ r * (2 * |(q.1 : ℝ) - 1 / 2|)) hab
    nlinarith [hd]

abbrev Time := ControlTime (1 : ℝ)

noncomputable def half : Time := ⟨1 / 2, by norm_num⟩

noncomputable def refControl (t : Time) : ℝ := if half < t then 1 else 0

noncomputable def refState : C(Time, ℝ) :=
  ⟨fun t ↦ max ((t : ℝ) - 1 / 2) 0,
    (continuous_subtype_val.sub continuous_const).max continuous_const⟩

noncomputable def reference : obstacleProblem.Candidate := (refState, refControl)

theorem measurable_refControl : Measurable refControl := by
  exact measurable_const.piecewise measurableSet_Ioi measurable_const

theorem refControl_mem (t : Time) : refControl t ∈ obstacleProblem.controlSet := by
  change (if half < t then (1 : ℝ) else 0) ∈ Icc (-1) 1
  split_ifs <;> norm_num

theorem time_mass {r s : Time} (hrs : r ≤ s) :
    (horizonProbability 1 (by norm_num)).toMeasure.real (Ioc r s) = (s : ℝ) - r := by
  simpa using scale_horizonProbability_real_Ioc 1 (by norm_num) r s hrs

theorem reference_dynamics : obstacleProblem.DynamicsAdmissible reference := by
  refine ⟨measurable_refControl, refControl_mem, ?_⟩
  intro t
  change max ((t : ℝ) - 1 / 2) 0 = 0 + (1 : ℝ) •
    ∫ s in Ioc (timeZero 1 (by norm_num)) t, refControl s ∂horizonProbability 1 (by norm_num)
  simp only [zero_add, one_smul]
  have he : refControl = (Ioi half).indicator (fun _ ↦ (1 : ℝ)) := by
    funext s
    simp [refControl, Set.indicator]
  rw [he, integral_indicator measurableSet_Ioi]
  have hi : Ioc (timeZero 1 (by norm_num)) t ∩ Ioi half = Ioc half t := by
    ext s
    simp only [mem_inter_iff, mem_Ioc, mem_Ioi]
    constructor
    · rintro ⟨⟨_, hst⟩, hhs⟩
      exact ⟨hhs, hst⟩
    · rintro ⟨hhs, hst⟩
      exact ⟨⟨lt_of_le_of_lt (by change (0 : ℝ) ≤ 1 / 2; norm_num) hhs, hst⟩, hhs⟩
  rw [Measure.restrict_restrict measurableSet_Ioi, inter_comm, hi, setIntegral_const,
    smul_eq_mul, mul_one]
  by_cases ht : half ≤ t
  · rw [time_mass ht, max_eq_left (by change 0 ≤ (t : ℝ) - 1 / 2; exact sub_nonneg.mpr ht)]
    rfl
  · have hlt : t < half := lt_of_not_ge ht
    have hempty : Ioc half t = ∅ := Ioc_eq_empty_of_le hlt.le
    rw [hempty]
    simp only [measureReal_empty]
    rw [max_eq_right (by change (t : ℝ) - 1 / 2 ≤ 0; exact sub_nonpos.mpr hlt.le)]

theorem reference_feasible : obstacleProblem.residual reference ≤ 0 := by
  intro q
  change max ((q.1 : ℝ) - 1 / 2) 0 - 2 * |(q.1 : ℝ) - 1 / 2| ≤ 0
  by_cases ht : 0 ≤ (q.1 : ℝ) - 1 / 2
  · rw [max_eq_left ht, abs_of_nonneg ht]
    linarith
  · rw [max_eq_right (le_of_not_ge ht), abs_of_nonpos (le_of_not_ge ht)]
    linarith

/-- The actual obstacle contacts the reference state at exactly the interior time. -/
theorem reference_contact (t : Time) :
    obstacleProblem.residual reference (t, 0) = 0 ↔ t = half := by
  change max ((t : ℝ) - 1 / 2) 0 - 2 * |(t : ℝ) - 1 / 2| = 0 ↔ t = half
  constructor
  · intro h
    apply Subtype.ext
    by_cases ht : 0 ≤ (t : ℝ) - 1 / 2
    · rw [max_eq_left ht, abs_of_nonneg ht] at h
      change (t : ℝ) = 1 / 2
      linarith
    · rw [max_eq_right (le_of_not_ge ht), abs_of_nonpos (le_of_not_ge ht)] at h
      change (t : ℝ) = 1 / 2
      linarith
  · rintro rfl
    norm_num [half]

/-- Every feasible competitor is bounded at the terminal time by the interior obstacle. -/
theorem competitor_terminal_bound (z : obstacleProblem.Candidate)
    (hz : obstacleProblem.DynamicsAdmissible z) (hg : obstacleProblem.residual z ≤ 0) :
    z.1 (timeEnd 1 (by norm_num)) ≤ 1 / 2 := by
  have hh := hg (half, 0)
  have hhalf : z.1 half ≤ 0 := by
    change z.1 half - 2 * |(half : ℝ) - 1 / 2| ≤ 0 at hh
    norm_num [half] at hh
    exact hh
  have hu := obstacleProblem.integrable_control z.2 hz.1 hz.2.1
  have hx (t : Time) : z.1 t = integralControlPath (T := 1) (by norm_num) 0 z.2 t := by
    have ht := hz.2.2 t
    change z.1 t = 0 + (1 : ℝ) • ∫ s in Ioc (timeZero 1 (by norm_num)) t,
      z.2 s ∂horizonProbability 1 (by norm_num) at ht
    exact ht
  have he := integralControlPath_sub (T := 1) (by norm_num) 0 z.2 hu
    (r := half) (s := timeEnd 1 (by norm_num)) (by change (1 / 2 : ℝ) ≤ 1; norm_num)
  rw [← hx, ← hx] at he
  simp only [one_smul] at he
  have hi : (∫ t in Ioc half (timeEnd 1 (by norm_num)), z.2 t
      ∂horizonProbability 1 (by norm_num)) ≤ 1 / 2 := by
    calc
      _ ≤ ∫ _ in Ioc half (timeEnd 1 (by norm_num)), (1 : ℝ)
          ∂horizonProbability 1 (by norm_num) :=
        integral_mono hu.integrableOn (integrable_const _) (fun t ↦ (hz.2.1 t).2)
      _ = 1 / 2 := by
        rw [setIntegral_const, smul_eq_mul, mul_one,
          time_mass (by change (1 / 2 : ℝ) ≤ 1; norm_num)]
        norm_num [half, timeEnd]
  linarith

/-- Actual global constrained optimality over every measurable integral competitor. -/
theorem reference_isMinimum : obstacleProblem.IsMinimum reference := by
  refine ⟨reference_dynamics, reference_feasible, ?_⟩
  intro z hz hg
  have hb := competitor_terminal_bound z hz hg
  have hr : obstacleProblem.cost reference = -(1 / 2) := by
    change -max ((1 : ℝ) - 1 / 2) 0 + 1 * ∫ _ : Time, (0 : ℝ)
      ∂horizonProbability 1 (by norm_num) = -(1 / 2)
    rw [integral_zero]
    norm_num
  have hc : obstacleProblem.cost z = -z.1 (timeEnd 1 (by norm_num)) := by
    change -z.1 (timeEnd 1 (by norm_num)) + 1 * ∫ _ : Time, (0 : ℝ)
      ∂horizonProbability 1 (by norm_num) = _
    rw [integral_zero]
    simp
  rw [hr, hc]
  linarith

noncomputable def slater : obstacleProblem.Candidate :=
  (⟨fun t ↦ -(t : ℝ), continuous_subtype_val.neg⟩, fun _ ↦ -1)

theorem slater_dynamics : obstacleProblem.DynamicsAdmissible slater := by
  refine ⟨measurable_const, ?_, ?_⟩
  · intro t
    change (-1 : ℝ) ∈ Icc (-1) 1
    norm_num
  · intro t
    change -(t : ℝ) = 0 + (1 : ℝ) • ∫ _ in Ioc (timeZero 1 (by norm_num)) t,
      (-1 : ℝ) ∂horizonProbability 1 (by norm_num)
    rw [zero_add, one_smul, setIntegral_const, smul_eq_mul,
      time_mass (r := timeZero 1 (by norm_num)) (s := t) (by exact t.2.1)]
    simp [timeZero]

/-- Strict feasibility is explicit, with a uniform half-unit margin. -/
theorem slater_gap (t : Time) : obstacleProblem.residual slater (t, 0) ≤ -(1 / 2) := by
  change -(t : ℝ) - 2 * |(t : ℝ) - 1 / 2| ≤ -(1 / 2)
  by_cases ht : 0 ≤ (t : ℝ) - 1 / 2
  · rw [abs_of_nonneg ht]
    linarith
  · rw [abs_of_nonpos (le_of_not_ge ht)]
    linarith

noncomputable def identityCovector : ℝ →L[ℝ] ℝ := ContinuousLinearMap.id ℝ ℝ

/-- Contact concentration forces every necessity measure to be a single interior Dirac. -/
theorem measure_eq_dirac {μ : Measure Time}
    (hsupp : μ {t | obstacleProblem.singleResidual reference t ≠ 0} = 0) :
    μ = μ {half} • Measure.dirac half := by
  have hset : {t | obstacleProblem.singleResidual reference t ≠ 0} = ({half} : Set Time)ᶜ := by
    ext t
    change (obstacleProblem.residual reference (t, 0) ≠ 0 ↔ t ≠ half)
    exact not_congr (reference_contact t)
  rw [hset] at hsupp
  have hae : ∀ᵐ t ∂μ, t ∈ ({half} : Set Time) := by
    exact ae_iff.mpr hsupp
  calc
    μ = μ.restrict {half} := (Measure.restrict_eq_self_of_ae_mem hae).symm
    _ = μ {half} • Measure.dirac half := Measure.restrict_singleton μ half

theorem prefix_measure_ne_zero :
    (horizonProbability 1 (by norm_num)).toMeasure (Iio half) ≠ 0 := by
  let quarter : Time := ⟨1 / 4, by norm_num⟩
  have hm := time_mass (r := timeZero 1 (by norm_num)) (s := quarter)
    (by change (0 : ℝ) ≤ 1 / 4; norm_num)
  have hn : (horizonProbability 1 (by norm_num)).toMeasure
      (Ioc (timeZero 1 (by norm_num)) quarter) ≠ 0 := by
    intro hz
    rw [measureReal_def, hz, ENNReal.toReal_zero] at hm
    norm_num [quarter, timeZero] at hm
  intro hz
  apply hn
  apply measure_mono_null _ hz
  intro t ht
  exact ht.2.trans_lt (by change (1 / 4 : ℝ) < 1 / 2; norm_num)

/-- The common-AE minimum forces the Dirac mass to equal the cost multiplier. -/
theorem forced_atom_mass {α : ℝ} {μ : Measure Time} [IsFiniteMeasure μ]
    (hα : 0 ≤ α) (hne : α ≠ 0 ∨ μ ≠ 0)
    (hsupp : μ {t | obstacleProblem.singleResidual reference t ≠ 0} = 0)
    (hmin : ∀ᵐ t ∂(horizonProbability 1 (by norm_num)).toMeasure,
      ∀ v ∈ obstacleProblem.controlSet,
        obstacleProblem.integratorHamiltonian α μ (-identityCovector)
          (fun _ ↦ identityCovector) t (refControl t) ≤
        obstacleProblem.integratorHamiltonian α μ (-identityCovector)
          (fun _ ↦ identityCovector) t v) :
    μ.real {half} = α ∧ 0 < α := by
  have hdirac := measure_eq_dirac hsupp
  have htail (t : Time) (ht : t < half) :
      (∫ s in Ioi t, identityCovector ∂μ) = μ.real {half} • identityCovector := by
    rw [hdirac, Measure.restrict_smul, integral_smul_measure]
    simp [ht, measureReal_def]
  obtain ⟨t, ht, htm⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae prefix_measure_ne_zero
    (hmin.filter_mono ae_restrict_le)
  change t < half at ht
  have hu : refControl t = 0 := by simp [refControl, not_lt_of_ge ht.le]
  have hp := htm (1 : ℝ) (by change (1 : ℝ) ∈ Icc (-1) 1; norm_num)
  have hn := htm (-1 : ℝ) (by change (-1 : ℝ) ∈ Icc (-1) 1; norm_num)
  change α * 0 + (α • -identityCovector + ∫ s in Ioi t, identityCovector ∂μ)
      (refControl t) ≤ α * 0 +
        (α • -identityCovector + ∫ s in Ioi t, identityCovector ∂μ) 1 at hp
  change α * 0 + (α • -identityCovector + ∫ s in Ioi t, identityCovector ∂μ)
      (refControl t) ≤ α * 0 +
        (α • -identityCovector + ∫ s in Ioi t, identityCovector ∂μ) (-1) at hn
  rw [hu, htail t ht] at hp hn
  simp [identityCovector] at hp hn
  have heq : μ.real {half} = α := by linarith
  refine ⟨heq, ?_⟩
  by_contra hneg
  have ha0 : α = 0 := le_antisymm (le_of_not_gt hneg) hα
  have hm0 : μ {half} = 0 := by
    apply (ENNReal.toReal_eq_zero_iff (μ {half})).mp
      (show (μ {half}).toReal = 0 from by simpa [measureReal_def, ha0] using heq)
      |>.resolve_right (ne_of_lt (measure_lt_top _ _))
  have hmu0 : μ = 0 := by rw [hdirac, hm0, zero_smul]
  exact hne.elim (fun h ↦ h ha0) (fun h ↦ h hmu0)

/-- Actual constrained optimality forces a positive singular multiplier and a nonzero jump.
The multiplier is obtained from the necessity theorem, never supplied as a certificate. -/
theorem exists_forced_interior_atom :
    ∃ (α : ℝ) (μ : Measure Time), IsFiniteMeasure μ ∧ 0 < α ∧
      μ = ENNReal.ofReal α • Measure.dirac half ∧
      BoundedVariationOn (obstacleProblem.integratorCostate α μ (-identityCovector)
        (fun _ ↦ identityCovector)) univ ∧
      (obstacleProblem.integratorCostate α μ (-identityCovector)
        (fun _ ↦ identityCovector) half -
        Function.leftLim (obstacleProblem.integratorCostate α μ (-identityCovector)
          (fun _ ↦ identityCovector)) half = -(α • identityCovector)) ∧
      obstacleProblem.integratorCostate α μ (-identityCovector)
        (fun _ ↦ identityCovector) half ≠
        Function.leftLim (obstacleProblem.integratorCostate α μ (-identityCovector)
          (fun _ ↦ identityCovector)) half := by
  let c : Time → ℝ := fun t ↦ -(2 * |(t : ℝ) - 1 / 2|)
  have hc : Continuous c :=
    (continuous_const.mul (continuous_subtype_val.sub continuous_const).abs).neg
  obtain ⟨α, μ, hfin, hα, hne, hcomp, hsupp, hmin⟩ :=
    obstacleProblem.exists_integrator_state_minimum_principle
      (fun _ _ _ ↦ rfl) (-identityCovector) (by ext x; rfl)
      (fun _ _ _ ↦ rfl) (fun _ ↦ identityCovector) continuous_const c hc
      (fun t x ↦ by simp [c, identityCovector, sub_eq_add_neg])
      reference reference_isMinimum
  let : IsFiniteMeasure μ := hfin
  have hforced := forced_atom_mass hα hne hsupp hmin
  have hm : μ {half} = ENNReal.ofReal α := by
    rw [← hforced.1, measureReal_def, ENNReal.ofReal_toReal (ne_of_lt (measure_lt_top _ _))]
  have hd : μ = ENNReal.ofReal α • Measure.dirac half := by
    rw [measure_eq_dirac hsupp, hm]
  have hj := obstacleProblem.integratorCostate_jump α μ (-identityCovector)
    (fun _ ↦ identityCovector) continuous_const half (by norm_num [half])
  rw [hforced.1] at hj
  refine ⟨α, μ, hfin, hforced.2, hd,
    obstacleProblem.integratorCostate_boundedVariation α μ (-identityCovector)
      (fun _ ↦ identityCovector) continuous_const, hj, ?_⟩
  intro he
  have hz : -(α • identityCovector) = 0 := by simpa [he] using hj.symm
  have hval := congrArg (fun q : ℝ →L[ℝ] ℝ ↦ q 1) hz
  simp [identityCovector] at hval
  linarith [hforced.2]

#print axioms reference_isMinimum
#print axioms forced_atom_mass
#print axioms exists_forced_interior_atom

end StateConstraintAtoms
