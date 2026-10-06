/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.VelocityPenaltyMinimizer
public import DynamicalSystems.Mathlib.Topology.ClusterPointLimit

/-!
# Boundary positivity of the penalty `F_K`

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), Lemma 11.3.3:
for every `0 < ε ≤ ε₁` there is a penalty scale `K(ε) > 0` such that on the
boundary of the velocity-control tube `B(ε)` of (11.3.2) the penalty `F_{K(ε)}`
of (11.3.6) is strictly larger than its value at the reference pair.

The formalization follows the book's contradiction argument.  A boundary
sequence with penalty bounded by the reference value has a cluster point in the
compact tube.  Lower semicontinuity propagates the boundary gap in the running
cost, the `K`-weighted endpoint/Volterra defect forces the limit onto the
admissible graph, and optimality of the reference is contradicted.

The tube boundary is the set of tube points where one of the velocity, initial
or control inequalities of (11.3.2) is an equality.  The History `H¹` clause of
the book is not part of the velocity carrier (it is documented in
`VelocityTrajectories.lean`).

Book citations live only in docstrings; all names are concept names.
-/

@[expose] public section

open Set MeasureTheory Filter Metric
open scoped Topology BoundedContinuousFunction ENNReal

namespace OptimalControl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- A continuous function on the compact horizon that vanishes almost everywhere
for the normalized horizon measure vanishes identically.  The horizon measure is
only open-positive inside `(0, t₁)`, so the argument restricts to the interior
and extends by continuity; this is the measure-theoretic step that lets the
`K`-weighted Volterra defect force the limit of a boundary sequence to satisfy
the integral dynamics exactly.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.3 (the limit is admissible). -/
theorem Continuous.eq_zero_of_ae_eq_zero_horizonProbability {T : ℝ} (hT : 0 < T)
    {g : ControlTime T → E} (hg : Continuous g)
    (h : g =ᵐ[(horizonProbability T hT).toMeasure] 0) : g = 0 := by
  -- transport the a.e. equality to the unnormalized horizon volume
  have hae_vol : g =ᵐ[horizonVolume T] 0 := by
    rw [← scale_horizonProbability T hT]
    exact Measure.AbsolutelyContinuous.ae_eq Measure.smul_absolutelyContinuous h
  -- the projection of `g` to the ambient real line
  let G : ℝ → E := fun y => g (Set.projIcc 0 T hT.le y)
  have hGc : Continuous G := hg.comp continuous_projIcc
  -- push forward along the subtype inclusion
  have hGae : G =ᵐ[volume.restrict (Icc (0 : ℝ) T)] 0 := by
    rw [← map_horizonVolume T]
    change ∀ᵐ y ∂Measure.map Subtype.val (horizonVolume T), G y = 0
    rw [MeasureTheory.ae_map_iff measurable_subtype_coe.aemeasurable
      (isClosed_eq hGc continuous_const).measurableSet]
    filter_upwards [hae_vol] with t ht
    simpa [G, Set.projIcc_of_mem _ t.2] using ht
  -- restrict to the interior
  have hle : volume.restrict (Ioo (0 : ℝ) T) ≤ volume.restrict (Icc (0 : ℝ) T) :=
    Measure.restrict_mono_set volume Ioo_subset_Icc_self
  have hGae_int : G =ᵐ[volume.restrict (Ioo (0 : ℝ) T)] 0 :=
    hle.absolutelyContinuous.ae_eq hGae
  -- an open null set is empty
  have hnull : volume ({y : ℝ | G y ≠ 0} ∩ Ioo (0 : ℝ) T) = 0 := by
    have hsupp : MeasurableSet ({y : ℝ | G y ≠ 0}) :=
      (isOpen_ne_fun hGc continuous_const).measurableSet
    have hz := MeasureTheory.ae_iff.mp hGae_int
    simpa [Measure.restrict_apply hsupp] using hz
  have hempty : ({y : ℝ | G y ≠ 0} ∩ Ioo (0 : ℝ) T) = ∅ := by
    by_contra hne
    exact (isOpen_ne_fun hGc continuous_const).inter isOpen_Ioo |>.measure_ne_zero volume
      (nonempty_iff_ne_empty.mpr hne) hnull
  have hG_int : ∀ y ∈ Ioo (0 : ℝ) T, G y = 0 := by
    intro y hy
    by_contra hgy
    exact absurd (show y ∈ ({y : ℝ | G y ≠ 0} ∩ Ioo (0 : ℝ) T) from ⟨hgy, hy⟩)
      (by rw [hempty]; exact Set.notMem_empty y)
  -- extend by continuity to the closed interval
  have hG_closed : ∀ y ∈ Icc (0 : ℝ) T, G y = 0 := by
    have hsub : Ioo (0 : ℝ) T ⊆ {y : ℝ | G y = 0} := fun y hy => hG_int y hy
    have hclosed : IsClosed {y : ℝ | G y = 0} := isClosed_eq hGc continuous_const
    have hclosure : closure (Ioo (0 : ℝ) T) ⊆ {y : ℝ | G y = 0} :=
      closure_minimal hsub hclosed
    rw [closure_Ioo (ne_of_lt hT)] at hclosure
    exact hclosure
  ext t
  have := hG_closed (t : ℝ) t.2
  simpa [G, Set.projIcc_of_mem _ t.2] using this

end OptimalControl

namespace OptimalControl.BoundedState

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]
  {P : Problem E V W}

namespace Problem

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The relaxed-control total-variation distance is nonnegative. -/
theorem relaxedControlDistance_nonneg (P : Problem E V W) (ρ σ : P.Relaxed) :
    0 ≤ relaxedControlDistance P ρ σ := by
  rw [relaxedControlDistance]
  refine le_csSup ?_ ⟨∅, MeasurableSet.empty, by simp⟩
  refine ⟨2, ?_⟩
  rintro d ⟨A, -, rfl⟩
  have h1 : ρ.measure.real A ≤ 1 := measureReal_le_one
  have h2 : σ.measure.real A ≤ 1 := measureReal_le_one
  have h3 : 0 ≤ ρ.measure.real A := measureReal_nonneg
  have h4 : 0 ≤ σ.measure.real A := measureReal_nonneg
  rw [abs_le]
  constructor <;> linarith

/-- The primitive path attached to a product-domain datum. -/
noncomputable def lpPath (P : Problem E V W)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :
    P.Trajectory :=
  primitiveBoundedPath P.horizon d.1 ((toWeakSpace ℝ _).symm d.2.1)

/-- The `K`-independent part of the penalty `F_K`: the running cost, the velocity
and initial defects and the control distance.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.6). -/
noncomputable def lpPenaltyBase (P : Problem E V W) (ε : ℝ)
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) : ℝ :=
  P.relaxedCost (lpPath P d) d.2.2
  + ‖(toWeakSpace ℝ _).symm d.2.1 - γ₀.toLp‖ ^ 2
  + dist d.1 γ₀.initial ^ 2
  + ε * relaxedControlDistance P d.2.2 ρ₀

/-- The endpoint and Volterra defect of a product-domain datum, the two terms
carrying the penalty scale `K` in (11.3.6).

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.6). -/
noncomputable def lpConstraintDefect (P : Problem E V W)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) : ℝ :=
  ‖P.endpointConstraint (lpPath P d (timeZero P.horizon P.horizon_pos.le))
      (lpPath P d (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2
  + ∫ t, ‖P.dynamicsResidual (lpPath P d) d.2.2 t‖ ^ 2
      ∂(horizonProbability P.horizon P.horizon_pos).toMeasure

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The penalty `F_K` splits into its scale-free part and `K` times the endpoint
and Volterra defect.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.6). -/
theorem lpPenalty_eq_base_add_scale_mul_defect (P : Problem E V W) (K ε : ℝ)
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :
    lpPenalty P K ε γ₀ ρ₀ d
      = lpPenaltyBase P ε γ₀ ρ₀ d + K * lpConstraintDefect P d := by
  simp only [lpPenalty, lpPenaltyBase, lpConstraintDefect, lpPath]
  ring

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The scale-free part of `F_K` is `F_K` at scale zero. -/
theorem lpPenaltyBase_eq_lpPenalty_zero (P : Problem E V W) (ε : ℝ)
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :
    lpPenaltyBase P ε γ₀ ρ₀ d = lpPenalty P 0 ε γ₀ ρ₀ d := by
  rw [lpPenalty_eq_base_add_scale_mul_defect]
  ring

/-- The boundary of the velocity-control tube `B(ε)` of (11.3.2): a point of the
tube at which at least one of the velocity, initial-value or control-distance
inequalities is an equality.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2) and Lemma 11.3.3. -/
def lpTubeBoundary (P : Problem E V W) (ε : ℝ) (γ₀ : VelocityTrajectory P)
    (ρ₀ : P.Relaxed)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) : Prop :=
  d ∈ lpTube P ε γ₀ ρ₀ ∧
  (‖(toWeakSpace ℝ _).symm d.2.1 - γ₀.toLp‖ ^ 2 = ε ^ 2 ∨
    dist d.1 γ₀.initial = ε ∨
    relaxedControlDistance P d.2.2 ρ₀ = ε)

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The endpoint and Volterra defect is nonnegative. -/
theorem lpConstraintDefect_nonneg (P : Problem E V W)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :
    0 ≤ lpConstraintDefect P d := by
  simp only [lpConstraintDefect]
  exact add_nonneg (sq_nonneg _) (integral_nonneg fun t => sq_nonneg _)

omit [CompleteSpace E] in
/-- For fixed data the Volterra residual energy integrand is continuous in time. -/
theorem continuous_dynamicsResidualEnergy_time (P : Problem E V W) (x : P.Trajectory)
    (ρ : P.Relaxed) :
    Continuous fun t : P.Time => ‖P.dynamicsResidual x ρ t‖ ^ 2 := by
  have hg : Continuous fun z : P.Time × P.Control =>
      P.dynamics z.1 (x z.1) (z.2 : V) :=
    P.dynamics_continuous.comp (((continuous_fst.prodMk
      (x.continuous.comp continuous_fst)).prodMk
      (continuous_subtype_val.comp continuous_snd)))
  have hF : Continuous (Function.uncurry fun (_ : Unit) (z : P.Time × P.Control) =>
      P.dynamics z.1 (x z.1) (z.2 : V)) := by
    change Continuous (fun p : Unit × (P.Time × P.Control) =>
      P.dynamics p.2.1 (x p.2.1) (p.2.2 : V))
    exact hg.comp continuous_snd
  have hS := OptimalControl.RelaxedControl.continuous_sliceIntegral_joint (hT := P.horizon_pos)
    (Q := Unit) (fun (_ : Unit) (z : P.Time × P.Control) =>
      P.dynamics z.1 (x z.1) (z.2 : V)) hF
  have hcomp : Continuous fun t : P.Time =>
      ∫ z in Ioc (timeZero P.horizon P.horizon_pos.le) t ×ˢ (univ : Set P.Control),
        P.dynamics z.1 (x z.1) (z.2 : V) ∂ρ.measure :=
    hS.comp (Continuous.prodMk
      (continuous_const : Continuous fun _ : P.Time => ((), ρ)) continuous_id)
  exact Continuous.pow (Continuous.norm
    ((x.continuous.sub continuous_const).sub (continuous_const.smul hcomp))) 2

/-- The relaxed running cost is continuous on the weakly bounded parameter set. -/
theorem continuousOn_lpRelaxedCost (P : Problem E V W) (R : ℝ) :
    ContinuousOn (fun d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed =>
      P.relaxedCost (lpPath P d) d.2.2)
      ((univ : Set E) ×ˢ (toWeakSpace ℝ _ '' {v | ‖v‖ ≤ R}) ×ˢ
        (univ : Set P.Relaxed)) := by
  set S₀ : Set (Lp E 2 (horizonMeasure P.horizon)) := {v | ‖v‖ ≤ R} with hS₀
  let Q := ↥((univ : Set E) ×ˢ (toWeakSpace ℝ _ '' S₀))
  let π : Q → P.Trajectory := fun q =>
    primitiveBoundedPath P.horizon q.1.1 ((toWeakSpace ℝ _).symm q.1.2)
  have hπ : Continuous π :=
    continuousOn_iff_continuous_domRestrict.1
      (continuousOn_primitiveBoundedPath_weakSpace_prod (T := P.horizon) S₀ fun v hv => hv)
  have hcost := continuous_relaxedCost_param P π hπ
  let A : Set (E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :=
    (univ : Set E) ×ˢ (toWeakSpace ℝ _ '' S₀) ×ˢ (univ : Set P.Relaxed)
  let ι : A → Q × P.Relaxed := fun d => (⟨(d.1.1, d.1.2.1), mem_univ _, d.2.2.1⟩, d.1.2.2)
  have hι : Continuous ι := by
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) ?_
    · exact (continuous_fst.comp continuous_subtype_val).prodMk
        (continuous_fst.comp (continuous_snd.comp continuous_subtype_val))
    · exact continuous_snd.comp (continuous_snd.comp continuous_subtype_val)
  exact continuousOn_iff_continuous_domRestrict.2 (hcost.comp hι)
/-- The endpoint and Volterra defect is continuous on the weakly bounded parameter set. -/
theorem continuousOn_lpConstraintDefect (P : Problem E V W)
    (hEnd : Continuous (Function.uncurry P.endpointConstraint)) (R : ℝ) :
    ContinuousOn (fun d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed =>
      lpConstraintDefect P d)
      ((univ : Set E) ×ˢ (toWeakSpace ℝ _ '' {v | ‖v‖ ≤ R}) ×ˢ
        (univ : Set P.Relaxed)) := by
  set S₀ : Set (Lp E 2 (horizonMeasure P.horizon)) := {v | ‖v‖ ≤ R} with hS₀
  let Q := ↥((univ : Set E) ×ˢ (toWeakSpace ℝ _ '' S₀))
  let π : Q → P.Trajectory := fun q =>
    primitiveBoundedPath P.horizon q.1.1 ((toWeakSpace ℝ _).symm q.1.2)
  have hπ : Continuous π :=
    continuousOn_iff_continuous_domRestrict.1
      (continuousOn_primitiveBoundedPath_weakSpace_prod (T := P.horizon) S₀ fun v hv => hv)
  have hres := continuous_dynamicsResidualEnergy_param P π hπ
  have hend : Continuous fun q : Q =>
      ‖P.endpointConstraint (π q (timeZero P.horizon P.horizon_pos.le))
        (π q (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2 :=
    (Continuous.pow (Continuous.norm (hEnd.comp
      ((hπ.eval_const _).prodMk (hπ.eval_const _)))) 2)
  let A : Set (E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :=
    (univ : Set E) ×ˢ (toWeakSpace ℝ _ '' S₀) ×ˢ (univ : Set P.Relaxed)
  let ι : A → Q × P.Relaxed := fun d => (⟨(d.1.1, d.1.2.1), mem_univ _, d.2.2.1⟩, d.1.2.2)
  have hι : Continuous ι := by
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) ?_
    · exact (continuous_fst.comp continuous_subtype_val).prodMk
        (continuous_fst.comp (continuous_snd.comp continuous_subtype_val))
    · exact continuous_snd.comp (continuous_snd.comp continuous_subtype_val)
  have hH : Continuous fun z : Q × P.Relaxed =>
      ‖P.endpointConstraint (π z.1 (timeZero P.horizon P.horizon_pos.le))
        (π z.1 (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2
      + ∫ t, ‖P.dynamicsResidual (π z.1) z.2 t‖ ^ 2
          ∂(horizonProbability P.horizon P.horizon_pos).toMeasure :=
    (hend.comp continuous_fst).add hres
  refine continuousOn_iff_continuous_domRestrict.2 ?_
  change Continuous (fun d : ↥A => lpConstraintDefect P d.1)
  convert hH.comp hι using 1
  funext d
  rfl

/-- **Boundary positivity of the penalty `F_K`** (Berkovitz & Medhin, Lemma 11.3.3): on the
boundary of the velocity-control tube `B(ε)` the penalty `F_{K(ε)}` strictly exceeds its value at
the reference pair, for a sufficiently large scale `K(ε)`.

The statement is normalized against the reference cost `J(φ₀,ν₀)` (the book sets
`J(φ₀,ν₀) = 0` without loss of generality).  The endpoint constraint carries no continuity field
in `Problem`, so its continuity is an explicit hypothesis, exactly as for Lemma 11.3.4.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2), (11.3.6) and Lemma 11.3.3. -/
theorem exists_penalty_scale_of_boundary_positivity (P : Problem E V W) (ε : ℝ) (hε : 0 < ε)
    (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (hopt : P.IsRelaxedMinimum (toBoundedPath γ₀) ρ₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ d :
        E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed,
      lpTubeBoundary P ε γ₀ ρ₀ d →
        P.relaxedCost (toBoundedPath γ₀) ρ₀ < lpPenalty P K ε γ₀ ρ₀ d := by
  classical
  set J₀ : ℝ := P.relaxedCost (toBoundedPath γ₀) ρ₀ with hJ₀
  by_contra hcon
  rw [not_exists] at hcon
  have hbad : ∀ n : ℕ, ∃ d,
      lpTubeBoundary P ε γ₀ ρ₀ d ∧ lpPenalty P ((n : ℝ) + 1) ε γ₀ ρ₀ d ≤ J₀ := by
    intro n
    have h1 : ¬ (∀ d, lpTubeBoundary P ε γ₀ ρ₀ d →
        J₀ < lpPenalty P ((n : ℝ) + 1) ε γ₀ ρ₀ d) :=
      fun hP => hcon ((n : ℝ) + 1) ⟨by positivity, hP⟩
    simp only [not_forall, not_lt] at h1
    simpa only [exists_prop] using h1
  let x : ℕ → E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed :=
    fun n => Classical.choose (hbad n)
  have hxbnd : ∀ n : ℕ, lpTubeBoundary P ε γ₀ ρ₀ (x n) :=
    fun n => (Classical.choose_spec (hbad n)).1
  have hxle : ∀ n : ℕ, lpPenalty P ((n : ℝ) + 1) ε γ₀ ρ₀ (x n) ≤ J₀ :=
    fun n => (Classical.choose_spec (hbad n)).2
  have hxmem : ∀ n : ℕ, x n ∈ lpTube P ε γ₀ ρ₀ := fun n => (hxbnd n).1
  -- the weakly bounded parameter set
  set R : ℝ := ‖γ₀.toLp‖ + ε with hR
  set S₀ : Set (Lp E 2 (horizonMeasure P.horizon)) := {v | ‖v‖ ≤ R} with hS₀
  set A : Set (E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :=
    (univ : Set E) ×ˢ (toWeakSpace ℝ _ '' S₀) ×ˢ (univ : Set P.Relaxed) with hA
  have hSsub : lpTube P ε γ₀ ρ₀ ⊆ A := by
    rintro d ⟨⟨-, ⟨v, hv, hvd⟩, -⟩, -⟩
    refine ⟨mem_univ _, ⟨v, ?_, hvd⟩, mem_univ _⟩
    have h1 : ‖v - γ₀.toLp‖ ^ 2 ≤ ε ^ 2 := by
      rw [← integral_norm_sub_sq_eq_norm_sq]; exact hv
    have h2 : ‖v - γ₀.toLp‖ ≤ ε :=
      (pow_le_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).1 h1
    have h3 : ‖v‖ ≤ ‖v - γ₀.toLp‖ + ‖γ₀.toLp‖ := by
      simpa using norm_add_le (v - γ₀.toLp) γ₀.toLp
    change ‖v‖ ≤ R
    rw [hR]; linarith
  -- a lower bound for the scale-free penalty on the tube
  have hne : (lpTube P ε γ₀ ρ₀).Nonempty := ⟨x 0, hxmem 0⟩
  obtain ⟨dmin, hdminmem, hdmin⟩ :=
    ((lowerSemicontinuousOn_lpPenalty P 0 ε hε.le hEnd γ₀ ρ₀ R).mono hSsub).exists_isMinOn
      hne (isCompact_lpTube P ε γ₀ ρ₀)
  -- the K-weighted Volterra defect is small along the boundary sequence
  have hdefect_bound : ∀ n : ℕ, lpConstraintDefect P (x n) ≤
      (J₀ - lpPenalty P 0 ε γ₀ ρ₀ dmin) / ((n : ℝ) + 1) := by
    intro n
    have hdec := lpPenalty_eq_base_add_scale_mul_defect P ((n : ℝ) + 1) ε γ₀ ρ₀ (x n)
    have hbase := lpPenaltyBase_eq_lpPenalty_zero P ε γ₀ ρ₀ (x n)
    have hmin := hdmin (hxmem n)
    have hmin' : lpPenalty P 0 ε γ₀ ρ₀ dmin ≤ lpPenaltyBase P ε γ₀ ρ₀ (x n) := by
      rw [hbase]; exact hmin
    have hle := hxle n
    rw [hdec, hbase] at hle
    have hpos : 0 < ((n : ℝ) + 1) := by positivity
    rw [le_div_iff₀ hpos]
    nlinarith [hle, hmin']
  -- the boundary equality makes the running cost strictly smaller
  have hgap : ∀ n : ℕ, P.relaxedCost (lpPath P (x n)) (x n).2.2 ≤ J₀ - ε ^ 2 := by
    intro n
    have hb := (hxbnd n).2
    have hle := hxle n
    have hdec := lpPenalty_eq_base_add_scale_mul_defect P ((n : ℝ) + 1) ε γ₀ ρ₀ (x n)
    have hbase : lpPenaltyBase P ε γ₀ ρ₀ (x n)
        = P.relaxedCost (lpPath P (x n)) (x n).2.2
          + ‖(toWeakSpace ℝ _).symm (x n).2.1 - γ₀.toLp‖ ^ 2
          + dist (x n).1 γ₀.initial ^ 2
          + ε * relaxedControlDistance P (x n).2.2 ρ₀ := rfl
    have hKnn : 0 ≤ ((n : ℝ) + 1) := by positivity
    have hdefnn : 0 ≤ lpConstraintDefect P (x n) := lpConstraintDefect_nonneg P _
    have hinit : 0 ≤ dist (x n).1 γ₀.initial ^ 2 := sq_nonneg _
    have hctrl : 0 ≤ ε * relaxedControlDistance P (x n).2.2 ρ₀ :=
      mul_nonneg hε.le (relaxedControlDistance_nonneg P _ _)
    rw [hdec, hbase] at hle
    rcases hb with hvel | hinit' | hctrl'
    · rw [hvel] at hle
      nlinarith [hle, hinit, hctrl, mul_nonneg hKnn hdefnn]
    · rw [hinit'] at hle
      nlinarith [hle, hinit, hctrl, mul_nonneg hKnn hdefnn]
    · rw [hctrl'] at hle
      nlinarith [hle, hinit, hctrl, mul_nonneg hKnn hdefnn]
  -- the compact subtype and a cluster point of the sequence
  set S : Set (E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :=
    lpTube P ε γ₀ ρ₀ with hS
  have hScomp : IsCompact S := isCompact_lpTube P ε γ₀ ρ₀
  let y : ℕ → ↥S := fun n => ⟨x n, hxmem n⟩
  have hcount : IsCountablyCompact (univ : Set ↥S) :=
    isCountablyCompact_iff_isCountablyCompact_univ.mp hScomp.isCountablyCompact
  obtain ⟨a, -, hacl⟩ :=
    hcount.seq_clusterPt y (Eventually.of_forall fun _ => mem_univ _)
  -- lower semicontinuity transfers the running-cost gap to the cluster point
  have hJcontS : ContinuousOn (fun d => P.relaxedCost (lpPath P d) d.2.2)
      (lpTube P ε γ₀ ρ₀) := (continuousOn_lpRelaxedCost P R).mono hSsub
  have hJsub : Continuous (fun q : ↥S => P.relaxedCost (lpPath P q.1) q.1.2.2) :=
    hJcontS.domRestrict
  have hJlim : P.relaxedCost (lpPath P a.1) a.1.2.2 ≤ J₀ - ε ^ 2 :=
    DynamicalSystems.le_of_mapClusterPt_of_lowerSemicontinuous
      hJsub.lowerSemicontinuous hacl (fun n => hgap n)
  -- the K-weighted defect vanishes at the cluster point
  have hK : Tendsto (fun a : ℝ => a + 1) atTop atTop :=
    le_of_eq (Filter.map_add_atTop_eq (1 : ℝ))
  have hzero : Tendsto
      (fun n : ℕ => (J₀ - lpPenalty P 0 ε γ₀ ρ₀ dmin) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    (hK.comp tendsto_natCast_atTop_atTop).const_div_atTop _
  have hdefectlim : lpConstraintDefect P a.1 = 0 :=
    DynamicalSystems.eq_zero_of_mapClusterPt_of_continuous_of_nonneg_of_tendsto_zero
      ((continuousOn_lpConstraintDefect P hEnd R).mono hSsub).domRestrict
      (fun q => lpConstraintDefect_nonneg P q.1) hzero hacl (fun n => hdefect_bound n)
  -- unpack the defect: the endpoint equality and the integral dynamics
  have hend0 : ‖P.endpointConstraint (lpPath P a.1 (timeZero P.horizon P.horizon_pos.le))
      (lpPath P a.1 (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2 = 0 := by
    have h1 : 0 ≤ ‖P.endpointConstraint (lpPath P a.1 (timeZero P.horizon P.horizon_pos.le))
        (lpPath P a.1 (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2 := sq_nonneg _
    have h2 : 0 ≤ ∫ t, ‖P.dynamicsResidual (lpPath P a.1) a.1.2.2 t‖ ^ 2
        ∂(horizonProbability P.horizon P.horizon_pos).toMeasure :=
      integral_nonneg fun t => sq_nonneg _
    simp only [lpConstraintDefect] at hdefectlim
    linarith
  have hres0 : ∫ t, ‖P.dynamicsResidual (lpPath P a.1) a.1.2.2 t‖ ^ 2
      ∂(horizonProbability P.horizon P.horizon_pos).toMeasure = 0 := by
    have h1 : 0 ≤ ‖P.endpointConstraint (lpPath P a.1 (timeZero P.horizon P.horizon_pos.le))
        (lpPath P a.1 (timeEnd P.horizon P.horizon_pos.le))‖ ^ 2 := sq_nonneg _
    have h2 : 0 ≤ ∫ t, ‖P.dynamicsResidual (lpPath P a.1) a.1.2.2 t‖ ^ 2
        ∂(horizonProbability P.horizon P.horizon_pos).toMeasure :=
      integral_nonneg fun t => sq_nonneg _
    simp only [lpConstraintDefect] at hdefectlim
    linarith
  have hend_eq : P.endpointConstraint (lpPath P a.1 (timeZero P.horizon P.horizon_pos.le))
      (lpPath P a.1 (timeEnd P.horizon P.horizon_pos.le)) = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp hend0)
  have hres_fun : ∀ t, P.dynamicsResidual (lpPath P a.1) a.1.2.2 t = 0 := by
    have hcont := continuous_dynamicsResidualEnergy_time P (lpPath P a.1) a.1.2.2
    have hint : Integrable (fun t : P.Time =>
        ‖P.dynamicsResidual (lpPath P a.1) a.1.2.2 t‖ ^ 2)
        (horizonProbability P.horizon P.horizon_pos).toMeasure :=
      hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hae : (fun t : P.Time => ‖P.dynamicsResidual (lpPath P a.1) a.1.2.2 t‖ ^ 2)
        =ᵐ[(horizonProbability P.horizon P.horizon_pos).toMeasure] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg _) hint).mp hres0
    have hzero_fun : (fun t : P.Time => ‖P.dynamicsResidual (lpPath P a.1) a.1.2.2 t‖ ^ 2) = 0 :=
      Continuous.eq_zero_of_ae_eq_zero_horizonProbability P.horizon_pos hcont hae
    intro t
    have := congrFun hzero_fun t
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp this)
  -- the cluster point is admissible
  have hadm : P.IsRelaxedAdmissible (lpPath P a.1) a.1.2.2 := by
    refine ⟨?_, hend_eq, ?_⟩
    · intro t
      have h := hres_fun t
      rw [dynamicsResidual] at h
      rw [sub_eq_zero] at h
      rw [sub_eq_iff_eq_add] at h
      simp only [relaxedDynamics]
      simpa [add_comm] using h
    · exact a.2.2
  -- optimality of the reference contradicts the strict cost gap
  have hopt_a : J₀ ≤ P.relaxedCost (lpPath P a.1) a.1.2.2 :=
    hopt.2 (lpPath P a.1) a.1.2.2 hadm
  nlinarith [hJlim, hopt_a, sq_pos_of_pos hε]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The total-variation distance of a relaxed control from itself is zero. -/
theorem relaxedControlDistance_self (P : Problem E V W) (ρ : P.Relaxed) :
    relaxedControlDistance P ρ ρ = 0 := by
  have hset : {d : ℝ | ∃ A : Set (P.Time × P.Control), MeasurableSet A ∧
      d = |ρ.measure.real A - ρ.measure.real A|} = {0} := by
    ext d; constructor
    · rintro ⟨A, -, rfl⟩; simp
    · intro hd; exact ⟨∅, MeasurableSet.empty, by simpa using hd⟩
  rw [relaxedControlDistance, hset, csSup_singleton]

/-- At an admissible reference the penalty `F_K` takes the reference cost value. -/
theorem velocityPenalized_self (P : Problem E V W) (K ε : ℝ) (γ₀ : VelocityTrajectory P)
    (ρ₀ : P.Relaxed) (hopt : P.IsRelaxedMinimum (toBoundedPath γ₀) ρ₀) :
    velocityPenalized P K ε γ₀ ρ₀ γ₀ ρ₀ = P.relaxedCost (toBoundedPath γ₀) ρ₀ := by
  have hres : (∫ t, ‖dynamicsResidual P (toBoundedPath γ₀) ρ₀ t‖ ^ 2
      ∂(horizonProbability P.horizon P.horizon_pos).toMeasure) = 0 := by
    have h0 : ∀ t : P.Time, dynamicsResidual P (toBoundedPath γ₀) ρ₀ t = 0 := by
      intro t
      have h := hopt.1.1 t
      simp only [dynamicsResidual, Problem.relaxedDynamics] at h ⊢
      rw [h]; abel
    rw [show (fun t : P.Time => ‖dynamicsResidual P (toBoundedPath γ₀) ρ₀ t‖ ^ 2) =
        (fun _ => 0) from funext fun t => by rw [h0 t]; simp]
    simp
  have hend : P.endpointConstraint (γ₀.value (timeZero P.horizon P.horizon_pos.le))
      (γ₀.value (timeEnd P.horizon P.horizon_pos.le)) = 0 := by
    have h := hopt.1.2.1
    simpa [toBoundedPath_apply] using h
  rw [velocityPenalized, velocityPenaltyRemainder, hres, hend,
    relaxedControlDistance_self]
  simp

/-- The boundary of the velocity-control tube `B(ε)` of (11.3.2). -/
def InVelocityControlTubeBoundary (P : Problem E V W) (γ₀ : VelocityTrajectory P)
    (ρ₀ : P.Relaxed) (ε : ℝ) (γ : VelocityTrajectory P) (ρ : P.Relaxed) : Prop :=
  InVelocityControlTube P γ₀ ρ₀ ε γ ρ ∧
  ((∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2) = ε ^ 2 ∨
    dist γ.initial γ₀.initial = ε ∨
    relaxedControlDistance P ρ ρ₀ = ε)

/-- **Boundary positivity on the velocity carrier** (Berkovitz & Medhin, Lemma 11.3.3): on the
boundary of `B(ε)` the penalty `F_{K(ε)}` strictly exceeds the reference cost.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2), (11.3.6) and Lemma 11.3.3. -/
theorem exists_penalty_scale_of_velocity_boundary_positivity (P : Problem E V W) (ε : ℝ)
    (hε : 0 < ε) (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (hopt : P.IsRelaxedMinimum (toBoundedPath γ₀) ρ₀) :
    ∃ K : ℝ, 0 < K ∧ ∀ γ ρ,
      InVelocityControlTubeBoundary P γ₀ ρ₀ ε γ ρ →
        P.relaxedCost (toBoundedPath γ₀) ρ₀ < velocityPenalized P K ε γ₀ ρ₀ γ ρ := by
  obtain ⟨K, hKpos, hK⟩ :=
    exists_penalty_scale_of_boundary_positivity P ε hε hEnd γ₀ ρ₀ hopt
  refine ⟨K, hKpos, fun γ ρ hb => ?_⟩
  have hmem : (γ.initial, toWeakSpace ℝ _ γ.toLp, ρ) ∈ lpTube P ε γ₀ ρ₀ :=
    (mem_lpTube_iff P hε.le γ₀ γ ρ₀ ρ).1 hb.1
  have hbd : lpTubeBoundary P ε γ₀ ρ₀ (γ.initial, toWeakSpace ℝ _ γ.toLp, ρ) := by
    refine ⟨hmem, ?_⟩
    rcases hb.2 with hv | hi | hc
    · left
      simp only [LinearEquiv.symm_apply_apply]
      have hv' : ‖γ.toLp - γ₀.toLp‖ ^ 2 = ε ^ 2 := by
        rw [Lp_two_norm_sq_eq_integral_norm_sq]
        rw [integral_sq_velocity_sub_eq (P := P) γ₀ γ] at hv
        exact hv
      exact hv'
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hc)
  rw [velocityPenalized_eq_lpPenalty]
  exact hK _ hbd

/-- **Strict-interior minimiser of the penalty `F_{K(ε)}`** (Berkovitz & Medhin, Lemma 11.3.4):
for `0 < ε` there is a scale `K(ε) > 0` and a pair whose velocity, initial-value and
control-distance inequalities are all *strict*, which minimises `F_{K(ε)}` over the closed tube
`B(ε)` of (11.3.2).

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.4 (strict-interior part, from Lemma 11.3.3). -/
theorem exists_strict_interior_velocityPenalized_minimizer (P : Problem E V W) (ε : ℝ)
    (hε : 0 < ε) (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (hopt : P.IsRelaxedMinimum (toBoundedPath γ₀) ρ₀) :
    ∃ K : ℝ, 0 < K ∧ ∃ γ ρ,
      (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2) < ε ^ 2 ∧
      dist γ.initial γ₀.initial < ε ∧
      relaxedControlDistance P ρ ρ₀ < ε ∧
      (∀ t : P.Time, P.stateConstraint t (γ.value t) ≤ 0) ∧
      ∀ γ' ρ', InVelocityControlTube P γ₀ ρ₀ ε γ' ρ' →
        velocityPenalized P K ε γ₀ ρ₀ γ ρ ≤ velocityPenalized P K ε γ₀ ρ₀ γ' ρ' := by
  obtain ⟨K, hKpos, hK⟩ :=
    exists_penalty_scale_of_velocity_boundary_positivity P ε hε hEnd γ₀ ρ₀ hopt
  have hstate : ∀ t : P.Time, P.stateConstraint t (γ₀.value t) ≤ 0 :=
    fun t => by simpa using hopt.1.2.2 t
  obtain ⟨γ, ρ, hmem, hmin⟩ :=
    exists_isMinOn_velocityPenalized P K ε hε.le hEnd γ₀ ρ₀ hstate
  have hself := self_mem_InVelocityControlTube (P := P) (γ₀ := γ₀) (ρ₀ := ρ₀) hε.le hstate
  have hle₀ : velocityPenalized P K ε γ₀ ρ₀ γ ρ ≤ P.relaxedCost (toBoundedPath γ₀) ρ₀ := by
    rw [← velocityPenalized_self P K ε γ₀ ρ₀ hopt]
    exact hmin γ₀ ρ₀ hself
  refine ⟨K, hKpos, γ, ρ, ?_, ?_, ?_, hmem.1.2.2.2, fun γ' ρ' hγ' => hmin γ' ρ' hγ'⟩
  · by_contra hle
    rw [not_lt] at hle
    have heq : (∫ s in (0 : ℝ)..P.horizon, ‖γ.velocity s - γ₀.velocity s‖ ^ 2) = ε ^ 2 :=
      le_antisymm hmem.1.2.1 hle
    exact absurd (hK γ ρ ⟨hmem, Or.inl heq⟩) (not_lt.mpr hle₀)
  · by_contra hle
    rw [not_lt] at hle
    have heq : dist γ.initial γ₀.initial = ε := le_antisymm hmem.1.2.2.1 hle
    exact absurd (hK γ ρ ⟨hmem, Or.inr (Or.inl heq)⟩) (not_lt.mpr hle₀)
  · by_contra hle
    rw [not_lt] at hle
    have heq : relaxedControlDistance P ρ ρ₀ = ε := le_antisymm hmem.2 hle
    exact absurd (hK γ ρ ⟨hmem, Or.inr (Or.inr heq)⟩) (not_lt.mpr hle₀)

end Problem

end OptimalControl.BoundedState
