/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.PenaltyTermsContinuity
public import DynamicalSystems.OptimalControl.ContinuousTime.RelaxedControlDistanceSemicontinuity
public import DynamicalSystems.OptimalControl.ContinuousTime.VelocityEpsilonOptimality
public import DynamicalSystems.OptimalControl.ContinuousTime.WeakPrimitiveContinuity

/-!
# Existence of a minimiser of the penalty `F_K` on the velocity tube

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemma 11.3.4: on the tube
`B(ε)` of (11.3.2) the penalty functional `F_K` of (11.3.6) attains its minimum.  The proof is the
direct method on the product `E × WeakSpace(L²) × RelaxedControl`:

* the velocity defect `‖v − v₀‖²` is weakly lower semicontinuous (convex);
* the running cost, the Volterra residual and the endpoint term are continuous on the weakly
  compact `L²` energy ball (weak-to-uniform continuity of the primitive, `WeakPrimitiveContinuity`;
  joint continuity of the slice integral, `RelaxedSliceIntegralContinuity`);
* the control-distance term is weak-* lower semicontinuous
  (`RelaxedControlDistanceSemicontinuity`);
* the tube is compact: weak compactness of the translated energy ball (`WeakL2Compactness`),
  compactness of the relaxed controls, and closedness of the state constraint.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012),
Lemma 11.3.4, (11.3.2) and (11.3.6).  Names are concept names.
-/

@[expose] public section

open Set MeasureTheory Filter Metric
open scoped Topology BoundedContinuousFunction ENNReal

namespace OptimalControl.BoundedState

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]
  {P : Problem E V W}

/-! ## The velocity carrier as an `L²` datum -/

/-- The primitive evaluation of the `L²` class of the velocity is the interval integral. -/
theorem VelocityTrajectory.primitiveValue_toLp (γ : VelocityTrajectory P) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) P.horizon) :
    primitiveValue P.horizon t γ.toLp = ∫ s in (0 : ℝ)..t, γ.velocity s := by
  have h1 : primitiveValue P.horizon t γ.toLp =
      ∫ x in Ioc (0 : ℝ) t, γ.velocity x ∂(horizonMeasure P.horizon) := by
    rw [primitiveValue, setIntegralCLM_apply]
    exact integral_congr_ae (ae_restrict_of_ae γ.coeFn_toLp)
  rw [h1, intervalIntegral.integral_of_le ht.1, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.2 (Ioc_subset_Ioc_right ht.2)]

/-- The state path of a velocity trajectory is the primitive of its `L²` velocity class. -/
theorem VelocityTrajectory.toBoundedPath_eq_primitiveBoundedPath (γ : VelocityTrajectory P) :
    toBoundedPath γ = primitiveBoundedPath P.horizon γ.initial γ.toLp := by
  ext t
  simp [VelocityTrajectory.value, γ.primitiveValue_toLp t.2]

/-- Every `L²` velocity class with an initial value is a velocity trajectory. -/
noncomputable def VelocityTrajectory.ofLp (P : Problem E V W) (i : E)
    (v : Lp E 2 (horizonMeasure P.horizon)) : VelocityTrajectory P where
  initial := i
  velocity := v
  velocity_intervalIntegrable := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le P.horizon_pos.le]
    exact (Lp.memLp v).integrable (by norm_num)
  velocity_sq_integrable :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).1 (Lp.memLp v)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
theorem VelocityTrajectory.toLp_ofLp (i : E) (v : Lp E 2 (horizonMeasure P.horizon)) :
    (VelocityTrajectory.ofLp P i v).toLp = v :=
  Lp.toLp_coeFn v _

/-! ## The penalty as a function on `E × WeakSpace(L²) × RelaxedControl` -/

namespace Problem

variable (P)

/-- The penalty `F_K` on the product domain `(initial value) × (weak `L²` velocity) × (relaxed
control)`: the primitive path is built from `(i, v)` by `primitiveBoundedPath`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.6). -/
noncomputable def lpPenalty (K ε : ℝ) (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) : ℝ :=
  P.relaxedCost (primitiveBoundedPath P.horizon d.1 ((toWeakSpace ℝ _).symm d.2.1)) d.2.2
  + ‖(toWeakSpace ℝ _).symm d.2.1 - γ₀.toLp‖ ^ 2
  + dist d.1 γ₀.initial ^ 2
  + ε * relaxedControlDistance P d.2.2 ρ₀
  + K * ‖P.endpointConstraint
      (primitiveBoundedPath P.horizon d.1 ((toWeakSpace ℝ _).symm d.2.1)
        (timeZero P.horizon P.horizon_pos.le))
      (primitiveBoundedPath P.horizon d.1 ((toWeakSpace ℝ _).symm d.2.1)
        (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2
  + K * ∫ t, ‖P.dynamicsResidual
      (primitiveBoundedPath P.horizon d.1 ((toWeakSpace ℝ _).symm d.2.1)) d.2.2 t‖ ^ 2
    ∂(horizonProbability P.horizon P.horizon_pos).toMeasure

/-- The velocity-carrier penalty is the product-domain penalty evaluated at the data of the
trajectory.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.6). -/
theorem velocityPenalized_eq_lpPenalty (K ε : ℝ) (γ₀ γ : VelocityTrajectory P)
    (ρ₀ ρ : P.Relaxed) :
    velocityPenalized P K ε γ₀ ρ₀ γ ρ =
      lpPenalty P K ε γ₀ ρ₀ (γ.initial, toWeakSpace ℝ _ γ.toLp, ρ) := by
  have hsq : (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2) =
      ‖γ.toLp - γ₀.toLp‖ ^ 2 := by
    rw [integral_sq_velocity_sub_eq γ₀ γ, Lp_two_norm_sq_eq_integral_norm_sq]
  have hpath := γ.toBoundedPath_eq_primitiveBoundedPath
  simp only [velocityPenalized, velocityPenaltyRemainder, lpPenalty, hsq,
    LinearEquiv.symm_apply_apply, ← hpath, toBoundedPath_apply]
  ring

end Problem

/-! ## Lower semicontinuity on weakly bounded sets -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V] in
/-- A nonnegative multiple of a lower semicontinuous real function is lower semicontinuous. -/
theorem lowerSemicontinuous_const_mul_of_nonneg {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : LowerSemicontinuous f) {c : ℝ} (hc : 0 ≤ c) :
    LowerSemicontinuous fun x => c * f x := by
  intro x y hy
  rcases hc.eq_or_lt with rfl | hc
  · exact Eventually.of_forall fun x' => by simpa using hy
  · have : y / c < f x := by rw [div_lt_iff₀ hc]; linarith
    filter_upwards [hf x _ this] with x' hx'
    have h : y / c < f x' := hx'
    rw [div_lt_iff₀ hc] at h
    change y < c * f x'
    linarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V] in
/-- Lower semicontinuity is preserved by precomposition with a continuous map. -/
theorem lowerSemicontinuous_comp_continuous {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : Y → ℝ} (hf : LowerSemicontinuous f) {g : X → Y}
    (hg : Continuous g) : LowerSemicontinuous fun x => f (g x) :=
  fun x y hy => (hg.tendsto x).eventually (hf (g x) y hy)

namespace Problem

variable (P)

/-- **Lower semicontinuity of the penalty `F_K` on weakly bounded sets** (the lsc half of
Lemma 11.3.4): for `ε ≥ 0` and a continuous endpoint constraint (any real `K`), `F_K` is
lower semicontinuous on `E × (weak image of a norm ball) × RelaxedControl`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.4 and (11.3.6). -/
theorem lowerSemicontinuousOn_lpPenalty (K ε : ℝ) (hε : 0 ≤ ε)
    (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed) (R : ℝ) :
    LowerSemicontinuousOn (lpPenalty P K ε γ₀ ρ₀)
      ((univ : Set E) ×ˢ (toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) ''
        {v | ‖v‖ ≤ R}) ×ˢ (univ : Set P.Relaxed)) := by
  set S₀ : Set (Lp E 2 (horizonMeasure P.horizon)) := {v | ‖v‖ ≤ R} with hS₀
  set A : Set (E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :=
    (univ : Set E) ×ˢ (toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) '' S₀) ×ˢ
      (univ : Set P.Relaxed) with hA
  let Q := ↥((univ : Set E) ×ˢ (toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) '' S₀))
  let π : Q → P.Trajectory := fun q =>
    primitiveBoundedPath P.horizon q.1.1 ((toWeakSpace ℝ _).symm q.1.2)
  have hπ : Continuous π :=
    continuousOn_iff_continuous_domRestrict.1
      (continuousOn_primitiveBoundedPath_weakSpace_prod (T := P.horizon) S₀ fun v hv => hv)
  have hcost := continuous_relaxedCost_param P π hπ
  have hres := continuous_dynamicsResidualEnergy_param P π hπ
  have hend : Continuous fun q : Q =>
      ‖P.endpointConstraint (π q (timeZero P.horizon P.horizon_pos.le))
        (π q (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2 :=
    (Continuous.pow (Continuous.norm (hEnd.comp
      ((hπ.eval_const _).prodMk (hπ.eval_const _)))) 2)
  let H : Q × P.Relaxed → ℝ := fun q =>
    P.relaxedCost (π q.1) q.2 +
      K * ‖P.endpointConstraint (π q.1 (timeZero P.horizon P.horizon_pos.le))
        (π q.1 (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2 +
      K * ∫ t, ‖P.dynamicsResidual (π q.1) q.2 t‖ ^ 2
        ∂(horizonProbability P.horizon P.horizon_pos).toMeasure
  have hH : Continuous H :=
    (hcost.add (continuous_const.mul (hend.comp continuous_fst))).add
      (continuous_const.mul hres)
  let ι : A → Q × P.Relaxed := fun d =>
    (⟨(d.1.1, d.1.2.1), mem_univ _, d.2.2.1⟩, d.1.2.2)
  have hι : Continuous ι := by
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) ?_
    · exact (continuous_fst.comp continuous_subtype_val).prodMk
        (continuous_fst.comp (continuous_snd.comp continuous_subtype_val))
    · exact continuous_snd.comp (continuous_snd.comp continuous_subtype_val)
  have hHA : ContinuousOn (fun d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) ×
      P.Relaxed =>
      P.relaxedCost (primitiveBoundedPath P.horizon d.1 ((toWeakSpace ℝ _).symm d.2.1)) d.2.2 +
      K * ‖P.endpointConstraint
        (primitiveBoundedPath P.horizon d.1 ((toWeakSpace ℝ _).symm d.2.1)
          (timeZero P.horizon P.horizon_pos.le))
        (primitiveBoundedPath P.horizon d.1 ((toWeakSpace ℝ _).symm d.2.1)
          (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2 +
      K * ∫ t, ‖P.dynamicsResidual
        (primitiveBoundedPath P.horizon d.1 ((toWeakSpace ℝ _).symm d.2.1)) d.2.2 t‖ ^ 2
        ∂(horizonProbability P.horizon P.horizon_pos).toMeasure) A :=
    continuousOn_iff_continuous_domRestrict.2 (hH.comp hι)
  have hvel : LowerSemicontinuous fun d : E ×
      WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed =>
      ‖(toWeakSpace ℝ _).symm d.2.1 - γ₀.toLp‖ ^ 2 :=
    lowerSemicontinuous_comp_continuous
      (DynamicalSystems.WeakL2.lowerSemicontinuous_weakSpace_norm_sub_sq γ₀.toLp)
      (continuous_fst.comp continuous_snd)
  have hinit : Continuous fun d : E ×
      WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed =>
      dist d.1 γ₀.initial ^ 2 := (continuous_fst.dist continuous_const).pow 2
  have hdist : LowerSemicontinuous fun d : E ×
      WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed =>
      ε * relaxedControlDistance P d.2.2 ρ₀ :=
    lowerSemicontinuous_const_mul_of_nonneg
      (lowerSemicontinuous_comp_continuous (lowerSemicontinuous_relaxedControlDistance P ρ₀)
        (continuous_snd.comp continuous_snd)) hε
  have hsum := ((hHA.lowerSemicontinuousOn.add (hvel.lowerSemicontinuousOn A)).add
    (hinit.continuousOn.lowerSemicontinuousOn)).add (hdist.lowerSemicontinuousOn A)
  convert hsum using 1
  funext d
  simp only [lpPenalty]
  ring

end Problem

/-! ## The tube as a compact subset of the product domain and the minimiser -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V] in
/-- The energy integral of `v − v₀` is the squared `L²` norm of `v − v₀`. -/
theorem integral_norm_sub_sq_eq_norm_sq [NormedSpace ℝ E] {μ : Measure ℝ} [IsFiniteMeasure μ]
    (v v₀ : Lp E 2 μ) : ∫ a, ‖v a - v₀ a‖ ^ 2 ∂μ = ‖v - v₀‖ ^ 2 := by
  rw [Lp_two_norm_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub v v₀] with a ha
  rw [ha, Pi.sub_apply]

namespace Problem

variable (P)

/-- The velocity control tube `B(ε)` of (11.3.2) as a subset of the product domain
`E × WeakSpace(L²) × RelaxedControl`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2). -/
def lpTube (ε : ℝ) (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed) :
    Set (E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :=
  (closedBall γ₀.initial ε ×ˢ
    (toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) ''
      {v | ∫ a, ‖v a - γ₀.toLp a‖ ^ 2 ∂(horizonMeasure P.horizon) ≤ ε ^ 2}) ×ˢ
    {ρ | relaxedControlDistance P ρ ρ₀ ≤ ε}) ∩
  {d | ∀ t : P.Time, P.stateConstraint t
    (d.1 + primitiveValue P.horizon t ((toWeakSpace ℝ _).symm d.2.1)) ≤ 0}

/-- The tube is compact: closed balls, the weakly compact translated energy ball and the
compact closed sublevel set of relaxed controls, intersected with a weakly closed state
constraint.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2) and Lemma 11.3.4. -/
theorem isCompact_lpTube (ε : ℝ) (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed) :
    IsCompact (lpTube P ε γ₀ ρ₀) := by
  have hctrl : IsClosed {ρ : P.Relaxed | relaxedControlDistance P ρ ρ₀ ≤ ε} :=
    (lowerSemicontinuous_relaxedControlDistance P ρ₀).isClosed_preimage ε
  have hstate : IsClosed {d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed |
      ∀ t : P.Time, P.stateConstraint t
        (d.1 + primitiveValue P.horizon t ((toWeakSpace ℝ _).symm d.2.1)) ≤ 0} := by
    simp only [ofPred_forall]
    refine isClosed_iInter fun t => isClosed_le ?_ continuous_const
    have hc : Continuous fun d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) ×
        P.Relaxed => d.1 + primitiveValue P.horizon t ((toWeakSpace ℝ _).symm d.2.1) :=
      continuous_fst.add ((continuous_comp_weakSpace_of_finiteDimensional
        (X := Lp E 2 (horizonMeasure P.horizon)) (primitiveValue P.horizon t)).comp
        (continuous_fst.comp continuous_snd))
    exact (P.stateConstraint_continuous.comp
      (continuous_const.prodMk continuous_id)).comp hc
  exact ((isCompact_closedBall _ _).prod
    ((isCompact_toWeakSpace_image_integral_norm_sub_sq_le
      γ₀.toLp (ε ^ 2)).prod hctrl.isCompact)).inter_right hstate

/-- Membership in the velocity control tube is membership of the carrier data in `lpTube`. -/
theorem mem_lpTube_iff {ε : ℝ} (hε : 0 ≤ ε) (γ₀ γ : VelocityTrajectory P)
    (ρ₀ ρ : P.Relaxed) :
    InVelocityControlTube P γ₀ ρ₀ ε γ ρ ↔
      (γ.initial, toWeakSpace ℝ _ γ.toLp, ρ) ∈ lpTube P ε γ₀ ρ₀ := by
  have hsq : (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2) =
      ∫ a, ‖γ.toLp a - γ₀.toLp a‖ ^ 2 ∂(horizonMeasure P.horizon) := by
    rw [integral_sq_velocity_sub_eq γ₀ γ, integral_norm_sub_sq_eq_norm_sq,
      Lp_two_norm_sq_eq_integral_norm_sq]
  have hval : ∀ t : P.Time, γ.value t = γ.initial + primitiveValue P.horizon t γ.toLp := by
    intro t
    rw [γ.primitiveValue_toLp t.2]
    rfl
  simp only [InVelocityControlTube, InVelocityTube, lpTube, mem_inter_iff, mem_prod,
    mem_closedBall, mem_ofPred_eq, hsq, hval, LinearEquiv.symm_apply_apply,
    (toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon))).injective.mem_set_image]
  constructor
  · rintro ⟨⟨-, h1, h2, h3⟩, h4⟩
    exact ⟨⟨h2, h1, h4⟩, h3⟩
  · rintro ⟨⟨h2, h1, h4⟩, h3⟩
    exact ⟨⟨hε, h1, h2, h3⟩, h4⟩

end Problem

namespace Problem

variable (P)

/-- **Existence of a minimiser of the penalty `F_K` on the velocity tube** (Berkovitz & Medhin,
Lemma 11.3.4).  For `ε ≥ 0` and any `K`, a continuous endpoint constraint and a reference pair
whose path satisfies the state constraint, `F_K` attains its minimum over the tube `B(ε)` of
(11.3.2).

The endpoint constraint `T` carries no continuity field in `Problem`, so continuity is an explicit
hypothesis here.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.4, (11.3.2) and (11.3.6). -/
theorem exists_isMinOn_velocityPenalized (K ε : ℝ) (hε : 0 ≤ ε)
    (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (hstate : ∀ t : P.Time, P.stateConstraint t (γ₀.value t) ≤ 0) :
    ∃ (γ : VelocityTrajectory P) (ρ : P.Relaxed),
      InVelocityControlTube P γ₀ ρ₀ ε γ ρ ∧
      ∀ (γ' : VelocityTrajectory P) (ρ' : P.Relaxed),
        InVelocityControlTube P γ₀ ρ₀ ε γ' ρ' →
          velocityPenalized P K ε γ₀ ρ₀ γ ρ ≤ velocityPenalized P K ε γ₀ ρ₀ γ' ρ' := by
  have hne : (lpTube P ε γ₀ ρ₀).Nonempty :=
    ⟨_, (mem_lpTube_iff P hε γ₀ γ₀ ρ₀ ρ₀).1 (self_mem_InVelocityControlTube P hε hstate)⟩
  -- the tube sits in a weakly bounded set of velocity classes
  have hsub : lpTube P ε γ₀ ρ₀ ⊆ (univ : Set E) ×ˢ
      (toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) ''
        {v | ‖v‖ ≤ ‖γ₀.toLp‖ + ε}) ×ˢ (univ : Set P.Relaxed) := by
    rintro d ⟨⟨-, ⟨v, hv, hvd⟩, -⟩, -⟩
    refine ⟨mem_univ _, ⟨v, ?_, hvd⟩, mem_univ _⟩
    have h1 : ‖v - γ₀.toLp‖ ^ 2 ≤ ε ^ 2 := by
      rw [← integral_norm_sub_sq_eq_norm_sq]; exact hv
    have h2 : ‖v - γ₀.toLp‖ ≤ ε := (pow_le_pow_iff_left₀ (norm_nonneg _) hε two_ne_zero).1 h1
    have h3 : ‖v‖ ≤ ‖v - γ₀.toLp‖ + ‖γ₀.toLp‖ := by
      simpa using norm_add_le (v - γ₀.toLp) γ₀.toLp
    change ‖v‖ ≤ ‖γ₀.toLp‖ + ε
    linarith
  obtain ⟨d, hd, hmin⟩ := (lowerSemicontinuousOn_lpPenalty P K ε hε hEnd γ₀ ρ₀
    (‖γ₀.toLp‖ + ε)).mono hsub |>.exists_isMinOn hne (isCompact_lpTube P ε γ₀ ρ₀)
  set γ := VelocityTrajectory.ofLp P d.1 ((toWeakSpace ℝ _).symm d.2.1) with hγ
  have hdγ : (γ.initial, toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) γ.toLp, d.2.2) = d := by
    have hl : γ.toLp = (toWeakSpace ℝ _).symm d.2.1 := VelocityTrajectory.toLp_ofLp _ _
    have hi : γ.initial = d.1 := rfl
    rw [hl, hi]
    simp
  have hmem : InVelocityControlTube P γ₀ ρ₀ ε γ d.2.2 :=
    (mem_lpTube_iff P hε γ₀ γ ρ₀ d.2.2).2 (by rw [hdγ]; exact hd)
  refine ⟨γ, d.2.2, hmem, fun γ' ρ' hγ' => ?_⟩
  rw [velocityPenalized_eq_lpPenalty, velocityPenalized_eq_lpPenalty, hdγ]
  exact hmin ((mem_lpTube_iff P hε γ₀ γ' ρ₀ ρ').1 hγ')

end Problem

end OptimalControl.BoundedState
