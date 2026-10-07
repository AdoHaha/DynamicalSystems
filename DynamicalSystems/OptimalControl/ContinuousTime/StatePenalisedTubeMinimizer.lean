/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.VelocityPointwiseBoundaryPositivity

/-!
# The state-penalised functional on the free tube and the limit of its minimisers

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.7)–(11.3.9) and
Lemma 11.3.5.  The state constraint `G(t, φ(t)) ≤ 0` is removed from the tube `B(ε)` of (11.3.2)
and replaced by the penalty

`H^j(φ, ν) = j ∫₀^{t₁} ω(G(t, φ(t))) dt + F(φ, ν)`,

where `ω` is a continuous profile vanishing on `(-∞, 0]` and positive on `(0, ∞)`, and `F` is the
anchored pointwise penalty `lpPenaltyPointwiseAnchored` of `VelocityPointwiseBoundaryPositivity`.
The control is frozen at the control `ρe` of a fixed `F`-minimiser `de` over the constrained tube.

* `exists_isMinOn_lpStatePenalisedAnchored` — for `j ≥ 0`, `H^j` attains its minimum on the free
  tube with frozen control (direct method: the state penalty is continuous on the weakly bounded
  parameter set because the primitive path depends continuously on `(initial, velocity)` in the
  uniform topology).
* `exists_lpStatePenalised_ultrafilter_limit` — along every ultrafilter finer than `atTop`, the
  minimisers `d_n` of `H^{j_n}` (`j_n → ∞`) converge to a datum `d*` that satisfies the state
  constraint, is an `F`-minimiser over the constrained tube, and the velocities converge **in
  norm** (the sandwich `A(d_n) → A(d*)` for the weakly lsc velocity defect `A = ‖v − v₀‖²`, then
  the Hilbert-space identity `‖v_n − v*‖² = ‖w_n‖² − 2⟪w_n,w*⟫ + ‖w*‖²`).
* `eventually_strict_lpStatePenalised_minimizer` — with boundary positivity of `F`, eventually the
  minimisers satisfy the velocity, initial and control clauses strictly.
* `exists_subseq_tendsto_lpStatePenalised_minimizer` — a subsequence converges in norm, the paths
  converge uniformly, and the limit is an `F`-minimiser satisfying `G ≤ 0`.
* `exists_anchored_tube_minimizer_of_boundary_positivity` — the hypotheses on `de` (minimiser of
  `F` over the constrained tube, `F(de) ≤ J₀`, boundary positivity) follow from relaxed
  optimality of the reference pair.

Book citations appear only in docstrings; all names are concept names.
-/

@[expose] public section

open Set MeasureTheory Filter Metric
open scoped Topology Interval BoundedContinuousFunction ENNReal

namespace OptimalControl.BoundedState

/-- A **state penalty profile** (Berkovitz & Medhin (11.3.7)): a continuous function vanishing on
`(-∞, 0]` and positive on `(0, ∞)`; the penalty `ω(G(t, φ(t)))` vanishes exactly where the state
constraint `G ≤ 0` holds.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.7). -/
structure IsStatePenaltyProfile (ω : ℝ → ℝ) : Prop where
  /-- The profile is continuous. -/
  continuous : Continuous ω
  /-- The profile vanishes on the admissible half-line. -/
  eq_zero_of_nonpos : ∀ s, s ≤ 0 → ω s = 0
  /-- The profile is positive on the violating half-line. -/
  pos_of_pos : ∀ s, 0 < s → 0 < ω s

namespace IsStatePenaltyProfile

variable {ω : ℝ → ℝ}

/-- A state penalty profile is nonnegative. -/
theorem nonneg (hω : IsStatePenaltyProfile ω) (s : ℝ) : 0 ≤ ω s := by
  rcases le_or_gt s 0 with hs | hs
  · exact (hω.eq_zero_of_nonpos s hs).ge
  · exact (hω.pos_of_pos s hs).le

end IsStatePenaltyProfile

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]
  {P : Problem E V W}

namespace Problem

/-! ## The state-violation integral on paths -/

/-- The **state-violation integral** `∫₀^{t₁} ω(G(t, x(t))) dt` of a path `x` (Berkovitz & Medhin
(11.3.7)); the path is read on the real line through the clamp `projIcc`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.7). -/
noncomputable def stateViolationIntegral (P : Problem E V W) (G : ℝ → E → ℝ) (ω : ℝ → ℝ)
    (x : P.Trajectory) : ℝ :=
  ∫ r in (0 : ℝ)..P.horizon, ω (G r (x (Set.projIcc 0 P.horizon P.horizon_pos.le r)))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The integrand of the state-violation integral is jointly continuous in the path (uniform
topology) and the time. -/
theorem continuous_stateViolationIntegrand (P : Problem E V W) {G : ℝ → E → ℝ} {ω : ℝ → ℝ}
    (hG : Continuous fun p : ℝ × E => G p.1 p.2) (hω : Continuous ω) :
    Continuous fun p : P.Trajectory × ℝ =>
      ω (G p.2 (p.1 (Set.projIcc 0 P.horizon P.horizon_pos.le p.2))) := by
  have hproj : Continuous fun r : ℝ => Set.projIcc (0 : ℝ) P.horizon P.horizon_pos.le r :=
    continuous_projIcc
  have hev : Continuous fun p : P.Trajectory × ℝ =>
      p.1 (Set.projIcc 0 P.horizon P.horizon_pos.le p.2) :=
    continuous_eval.comp (continuous_fst.prodMk (hproj.comp continuous_snd))
  exact hω.comp (hG.comp (continuous_snd.prodMk hev))

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The state-violation integral is continuous in the path for the uniform topology.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.7) and Lemma 11.3.5. -/
theorem continuous_stateViolationIntegral (P : Problem E V W) {G : ℝ → E → ℝ} {ω : ℝ → ℝ}
    (hG : Continuous fun p : ℝ × E => G p.1 p.2) (hω : Continuous ω) :
    Continuous (stateViolationIntegral P G ω) :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (x : P.Trajectory) (r : ℝ) =>
      ω (G r (x (Set.projIcc 0 P.horizon P.horizon_pos.le r))))
    (continuous_stateViolationIntegrand P hG hω) 0 P.horizon

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The state-violation integral is nonnegative. -/
theorem stateViolationIntegral_nonneg (P : Problem E V W) (G : ℝ → E → ℝ) {ω : ℝ → ℝ}
    (hω : IsStatePenaltyProfile ω) (x : P.Trajectory) :
    0 ≤ stateViolationIntegral P G ω x :=
  intervalIntegral.integral_nonneg P.horizon_pos.le fun _ _ => hω.nonneg _

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- The state-violation integral vanishes on a path satisfying the state constraint.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.7). -/
theorem stateViolationIntegral_eq_zero (P : Problem E V W) (G : ℝ → E → ℝ) {ω : ℝ → ℝ}
    (hω : IsStatePenaltyProfile ω) (x : P.Trajectory) (hx : ∀ t : P.Time, G t (x t) ≤ 0) :
    stateViolationIntegral P G ω x = 0 := by
  have h : ∀ r ∈ [[(0 : ℝ), P.horizon]],
      ω (G r (x (Set.projIcc 0 P.horizon P.horizon_pos.le r))) = 0 := by
    intro r hr
    rw [uIcc_of_le P.horizon_pos.le] at hr
    rw [Set.projIcc_of_mem P.horizon_pos.le hr]
    exact hω.eq_zero_of_nonpos _ (hx ⟨r, hr⟩)
  rw [stateViolationIntegral, intervalIntegral.integral_congr h]
  simp

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] in
/-- **A vanishing state-violation integral forces the state constraint.**  If
`∫₀^{t₁} ω(G(t, x(t))) dt ≤ 0`, then `G(t, x(t)) ≤ 0` for every `t` of the horizon: a violation at
`t₀` makes the continuous nonnegative integrand positive on a nondegenerate subinterval.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.7) and Lemma 11.3.5. -/
theorem stateConstraint_le_zero_of_stateViolationIntegral_nonpos (P : Problem E V W)
    {G : ℝ → E → ℝ} {ω : ℝ → ℝ} (hG : Continuous fun p : ℝ × E => G p.1 p.2)
    (hω : IsStatePenaltyProfile ω) (x : P.Trajectory)
    (hx : stateViolationIntegral P G ω x ≤ 0) (t : P.Time) : G t (x t) ≤ 0 := by
  by_contra hpos
  push Not at hpos
  set T := P.horizon with hT
  have hT0 : 0 < T := P.horizon_pos
  set f : ℝ → ℝ := fun r => ω (G r (x (Set.projIcc 0 P.horizon P.horizon_pos.le r))) with hf
  have hfc : Continuous f :=
    (continuous_stateViolationIntegrand P hG hω.continuous).comp
      (continuous_const.prodMk continuous_id)
  have hft : f t = ω (G t (x t)) := by
    simp only [hf, Set.projIcc_val]
  have hft0 : 0 < f t := by rw [hft]; exact hω.pos_of_pos _ hpos
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuous_iff.1 hfc (t : ℝ) (f t / 2) (by linarith)
  set a : ℝ := max 0 ((t : ℝ) - δ / 2) with ha
  set b : ℝ := min T ((t : ℝ) + δ / 2) with hb
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have htT : (t : ℝ) ≤ T := t.2.2
  have hab : a < b := by
    refine max_lt (lt_min hT0 (by linarith)) (lt_min (by linarith) (by linarith))
  have h0a : 0 ≤ a := le_max_left _ _
  have hbT : b ≤ T := min_le_left _ _
  have hpos_on : ∀ r ∈ Ioo a b, 0 < f r := by
    intro r hr
    have h1 : (t : ℝ) - δ / 2 < r := lt_of_le_of_lt (le_max_right _ _) hr.1
    have h2 : r < (t : ℝ) + δ / 2 := lt_of_lt_of_le hr.2 (min_le_right _ _)
    have hd : dist r t < δ := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have := hδf r hd
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.1]
  have hpos_ab : 0 < ∫ r in a..b, f r :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hfc.intervalIntegrable a b) hpos_on hab
  have hmono : (∫ r in a..b, f r) ≤ ∫ r in (0 : ℝ)..T, f r :=
    intervalIntegral.integral_mono_interval h0a hab.le hbT
      (Eventually.of_forall fun r => hω.nonneg _) (hfc.intervalIntegrable 0 T)
  have : stateViolationIntegral P G ω x = ∫ r in (0 : ℝ)..T, f r := rfl
  linarith

/-! ## The state penalty on the product domain -/

/-- The primitive path of a product-domain datum is continuous (weak topology on the velocity,
uniform topology on paths) on every weakly bounded parameter set.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.4 and Lemma 11.3.5. -/
theorem continuousOn_lpPath (P : Problem E V W) (R : ℝ) :
    ContinuousOn (lpPath P)
      ((univ : Set E) ×ˢ (toWeakSpace ℝ _ '' {v : Lp E 2 (horizonMeasure P.horizon) | ‖v‖ ≤ R}) ×ˢ
        (univ : Set P.Relaxed)) := by
  have h := continuousOn_primitiveBoundedPath_weakSpace_prod (T := P.horizon)
    {v : Lp E 2 (horizonMeasure P.horizon) | ‖v‖ ≤ R} fun v hv => hv
  exact h.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn
    fun d hd => ⟨mem_univ _, hd.2.1⟩

/-- The state-violation integral of the primitive path of a product-domain datum.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.7). -/
noncomputable def lpStateViolation (P : Problem E V W) (G : ℝ → E → ℝ) (ω : ℝ → ℝ)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) : ℝ :=
  stateViolationIntegral P G ω (lpPath P d)

/-- The product-domain state violation is continuous on every weakly bounded parameter set. -/
theorem continuousOn_lpStateViolation (P : Problem E V W) {G : ℝ → E → ℝ} {ω : ℝ → ℝ}
    (hG : Continuous fun p : ℝ × E => G p.1 p.2) (hω : Continuous ω) (R : ℝ) :
    ContinuousOn (lpStateViolation P G ω)
      ((univ : Set E) ×ˢ (toWeakSpace ℝ _ '' {v : Lp E 2 (horizonMeasure P.horizon) | ‖v‖ ≤ R}) ×ˢ
        (univ : Set P.Relaxed)) :=
  (continuous_stateViolationIntegral P hG hω).comp_continuousOn (continuousOn_lpPath P R)

/-- The **state-penalised anchored functional** `H^j = j ∫ ω(G(t, φ(t))) dt + F` of Berkovitz &
Medhin (11.3.8), with `F = lpPenaltyPointwiseAnchored`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.8). -/
noncomputable def lpStatePenalisedAnchored (P : Problem E V W) (G : ℝ → E → ℝ) (ω : ℝ → ℝ)
    (j K ε : ℝ) (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) : ℝ :=
  j * lpStateViolation P G ω d + lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ d

/-- The **free tube**: the tube `B(ε)` of (11.3.2) without the state clause.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2) and (11.3.8). -/
def lpFreeTube (P : Problem E V W) (ε : ℝ) (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed) :
    Set (E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :=
  closedBall γ₀.initial ε ×ˢ
    (toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) ''
      {v | ∫ a, ‖v a - γ₀.toLp a‖ ^ 2 ∂(horizonMeasure P.horizon) ≤ ε ^ 2}) ×ˢ
    {ρ | relaxedControlDistance P ρ ρ₀ ≤ ε}

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The constrained tube is the free tube cut by the state clause. -/
theorem lpTube_subset_lpFreeTube (P : Problem E V W) (ε : ℝ) (γ₀ : VelocityTrajectory P)
    (ρ₀ : P.Relaxed) : lpTube P ε γ₀ ρ₀ ⊆ lpFreeTube P ε γ₀ ρ₀ :=
  fun _ hd => hd.1

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- A free-tube datum whose path satisfies the state constraint lies in the constrained tube. -/
theorem mem_lpTube_of_mem_lpFreeTube (P : Problem E V W) {ε : ℝ} {γ₀ : VelocityTrajectory P}
    {ρ₀ : P.Relaxed} {G : ℝ → E → ℝ} (hGP : ∀ (t : P.Time) (y : E), P.stateConstraint t y = G t y)
    {d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed}
    (hd : d ∈ lpFreeTube P ε γ₀ ρ₀) (hG : ∀ t : P.Time, G t (lpPath P d t) ≤ 0) :
    d ∈ lpTube P ε γ₀ ρ₀ := by
  refine ⟨hd, fun t => ?_⟩
  rw [hGP]
  exact hG t

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The path of a constrained-tube datum satisfies `G ≤ 0`. -/
theorem stateConstraint_lpPath_of_mem_lpTube (P : Problem E V W) {ε : ℝ}
    {γ₀ : VelocityTrajectory P} {ρ₀ : P.Relaxed} {G : ℝ → E → ℝ}
    (hGP : ∀ (t : P.Time) (y : E), P.stateConstraint t y = G t y)
    {d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed}
    (hd : d ∈ lpTube P ε γ₀ ρ₀) (t : P.Time) : G t (lpPath P d t) ≤ 0 := by
  rw [← hGP]
  exact hd.2 t

/-- The free tube with frozen control `ρe` is compact (the frozen-control slice is a singleton,
so no `T1Space` assumption on relaxed controls is needed).

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2) and Lemma 11.3.4. -/
theorem isCompact_lpFreeTube_inter (P : Problem E V W) (ε : ℝ) (γ₀ : VelocityTrajectory P)
    (ρ₀ ρe : P.Relaxed) :
    IsCompact (lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = ρe}) := by
  have heq : lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = ρe} =
      closedBall γ₀.initial ε ×ˢ
        (toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) ''
          {v | ∫ a, ‖v a - γ₀.toLp a‖ ^ 2 ∂(horizonMeasure P.horizon) ≤ ε ^ 2}) ×ˢ
        ({ρ | relaxedControlDistance P ρ ρ₀ ≤ ε} ∩ {ρe}) := by
    ext ⟨a, b, c⟩
    simp only [lpFreeTube, mem_inter_iff, mem_prod, mem_ofPred_eq, mem_singleton_iff]
    tauto
  rw [heq]
  exact (isCompact_closedBall _ _).prod
    ((isCompact_toWeakSpace_image_integral_norm_sub_sq_le γ₀.toLp (ε ^ 2)).prod
      (Set.subsingleton_singleton.anti inter_subset_right).isCompact)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The free tube sits in the weakly bounded parameter set of radius `‖v₀‖ + ε`. -/
theorem lpFreeTube_subset_bounded (P : Problem E V W) {ε : ℝ} (hε : 0 ≤ ε)
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed) :
    lpFreeTube P ε γ₀ ρ₀ ⊆ (univ : Set E) ×ˢ
      (toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) ''
        {v | ‖v‖ ≤ ‖γ₀.toLp‖ + ε}) ×ˢ (univ : Set P.Relaxed) := by
  rintro d ⟨-, ⟨v, hv, hvd⟩, -⟩
  refine ⟨mem_univ _, ⟨v, ?_, hvd⟩, mem_univ _⟩
  have h1 : ‖v - γ₀.toLp‖ ^ 2 ≤ ε ^ 2 := by
    rw [← integral_norm_sub_sq_eq_norm_sq]; exact hv
  have h2 : ‖v - γ₀.toLp‖ ≤ ε :=
    (pow_le_pow_iff_left₀ (norm_nonneg _) hε two_ne_zero).1 h1
  have h3 : ‖v‖ ≤ ‖v - γ₀.toLp‖ + ‖γ₀.toLp‖ := by
    simpa using norm_add_le (v - γ₀.toLp) γ₀.toLp
  change ‖v‖ ≤ ‖γ₀.toLp‖ + ε
  linarith

/-- The state-penalised functional is lower semicontinuous on weakly bounded parameter sets for
`j ≥ 0`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.8) and Lemma 11.3.4. -/
theorem lowerSemicontinuousOn_lpStatePenalisedAnchored (P : Problem E V W) {G : ℝ → E → ℝ}
    {ω : ℝ → ℝ} (hG : Continuous fun p : ℝ × E => G p.1 p.2) (hω : Continuous ω)
    (j K ε : ℝ) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed) (R : ℝ) :
    LowerSemicontinuousOn (lpStatePenalisedAnchored P G ω j K ε γ₀ ρ₀)
      ((univ : Set E) ×ˢ (toWeakSpace ℝ _ '' {v : Lp E 2 (horizonMeasure P.horizon) | ‖v‖ ≤ R}) ×ˢ
        (univ : Set P.Relaxed)) :=
  (((continuousOn_lpStateViolation P hG hω R).const_mul j).lowerSemicontinuousOn).add
    (lowerSemicontinuousOn_lpPenaltyPointwiseAnchored P K ε hK hε hEnd γ₀ ρ₀ R)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The reference datum with the control replaced by `ρe` lies in the frozen free tube when
`ρe` is within the control radius. -/
theorem reference_mem_lpFreeTube_inter (P : Problem E V W) {ε : ℝ} (hε : 0 ≤ ε)
    (γ₀ : VelocityTrajectory P) (ρ₀ ρe : P.Relaxed) (hρe : relaxedControlDistance P ρe ρ₀ ≤ ε) :
    (γ₀.initial, toWeakSpace ℝ _ γ₀.toLp, ρe) ∈ lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = ρe} := by
  refine ⟨⟨by simpa using hε, ⟨γ₀.toLp, ?_, rfl⟩, hρe⟩, rfl⟩
  simp only [mem_ofPred_eq, sub_self, norm_zero]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
  positivity

/-- **Existence of a minimiser of the state-penalised functional on the free tube** (Berkovitz &
Medhin (11.3.8)–(11.3.9)): for `j ≥ 0` the functional `H^j` attains its minimum over the free tube
with frozen control `ρe`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.8), (11.3.9) and Lemma 11.3.4. -/
theorem exists_isMinOn_lpStatePenalisedAnchored (P : Problem E V W) {G : ℝ → E → ℝ}
    {ω : ℝ → ℝ} (hG : Continuous fun p : ℝ × E => G p.1 p.2) (hω : Continuous ω)
    (j K ε : ℝ) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    (γ₀ : VelocityTrajectory P) (ρ₀ ρe : P.Relaxed)
    (hρe : relaxedControlDistance P ρe ρ₀ ≤ ε) :
    ∃ d ∈ lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = ρe},
      IsMinOn (lpStatePenalisedAnchored P G ω j K ε γ₀ ρ₀)
        (lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = ρe}) d :=
  ((lowerSemicontinuousOn_lpStatePenalisedAnchored P hG hω j K ε hK hε hEnd γ₀ ρ₀
    (‖γ₀.toLp‖ + ε)).mono
      (inter_subset_left.trans (lpFreeTube_subset_bounded P hε γ₀ ρ₀))).exists_isMinOn
    ⟨_, reference_mem_lpFreeTube_inter P hε γ₀ ρ₀ ρe hρe⟩ (isCompact_lpFreeTube_inter P ε γ₀ ρ₀ ρe)

/-! ## The velocity defect and the remainder of the anchored penalty -/

/-- The velocity defect `‖v − v₀‖²` of a product-domain datum (the convex, weakly lower
semicontinuous part of the anchored penalty).

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.6). -/
noncomputable def lpVelocityDefect (P : Problem E V W) (γ₀ : VelocityTrajectory P)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) : ℝ :=
  ‖(toWeakSpace ℝ _).symm d.2.1 - γ₀.toLp‖ ^ 2

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- The velocity defect is weakly lower semicontinuous. -/
theorem lowerSemicontinuous_lpVelocityDefect (P : Problem E V W) (γ₀ : VelocityTrajectory P) :
    LowerSemicontinuous (lpVelocityDefect P γ₀) :=
  lowerSemicontinuous_comp_continuous
    (DynamicalSystems.WeakL2.lowerSemicontinuous_weakSpace_norm_sub_sq γ₀.toLp)
    (continuous_fst.comp continuous_snd)

/-- **The anchored penalty minus its velocity defect is lower semicontinuous** on weakly bounded
parameter sets: it is the running cost, the initial defects, the control distance, the endpoint
term and the pointwise dynamics defect, each continuous or lower semicontinuous.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.4 and Lemma 11.3.5. -/
theorem lowerSemicontinuousOn_lpPenaltyPointwiseAnchored_sub_lpVelocityDefect
    (P : Problem E V W) (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed) (R : ℝ) :
    LowerSemicontinuousOn
      (fun d => lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ d - lpVelocityDefect P γ₀ d)
      ((univ : Set E) ×ˢ (toWeakSpace ℝ _ '' {v : Lp E 2 (horizonMeasure P.horizon) | ‖v‖ ≤ R}) ×ˢ
        (univ : Set P.Relaxed)) := by
  set A : Set (E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :=
    (univ : Set E) ×ˢ (toWeakSpace ℝ _ '' {v : Lp E 2 (horizonMeasure P.horizon) | ‖v‖ ≤ R}) ×ˢ
      (univ : Set P.Relaxed) with hA
  have hcost := continuousOn_lpRelaxedCost P R
  have hend := ((continuousOn_lpEndpointSq P hEnd R).const_mul K).lowerSemicontinuousOn
  have hinit : ContinuousOn (fun d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) ×
      P.Relaxed => dist d.1 γ₀.initial ^ 2) A :=
    (continuous_fst.dist continuous_const).pow 2 |>.continuousOn
  have hdist : LowerSemicontinuousOn (fun d : E ×
      WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed =>
      ε * relaxedControlDistance P d.2.2 ρ₀) A :=
    (lowerSemicontinuous_const_mul_of_nonneg
      (lowerSemicontinuous_comp_continuous (lowerSemicontinuous_relaxedControlDistance P ρ₀)
        (continuous_snd.comp continuous_snd)) hε).lowerSemicontinuousOn A
  have hdef := lowerSemicontinuousOn_const_mul_of_nonneg
    (lowerSemicontinuousOn_lpPointwiseDefectEnergy P R) hK
  have hanchor : ContinuousOn (fun d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) ×
      P.Relaxed => K * dist d.1 P.initial ^ 2) A :=
    (((continuous_fst.dist continuous_const).pow 2).const_mul K).continuousOn
  have hsum := ((((hcost.lowerSemicontinuousOn.add hinit.lowerSemicontinuousOn).add hdist).add
    hend).add hdef).add hanchor.lowerSemicontinuousOn
  convert hsum using 1
  funext d
  simp only [lpPenaltyPointwiseAnchored, lpPenaltyPointwise, lpVelocityDefect]
  ring

omit [FiniteDimensional ℝ V] [BorelSpace V] in
/-- **Strict tube clauses off the boundary.**  A datum of the constrained tube that is not on the
boundary satisfies the velocity, initial and control clauses strictly.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2) and Lemma 11.3.4 (strict-interior part). -/
theorem lpTube_strict_of_not_lpTubeBoundary (P : Problem E V W) {ε : ℝ}
    {γ₀ : VelocityTrajectory P} {ρ₀ : P.Relaxed}
    {d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed}
    (hd : d ∈ lpTube P ε γ₀ ρ₀) (hnb : ¬ lpTubeBoundary P ε γ₀ ρ₀ d) :
    lpVelocityDefect P γ₀ d < ε ^ 2 ∧ dist d.1 γ₀.initial < ε ∧
      relaxedControlDistance P d.2.2 ρ₀ < ε := by
  have hd' := hd
  obtain ⟨⟨hb, ⟨v, hv, hvd⟩, hc⟩, -⟩ := hd'
  have hvv : (toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon))).symm d.2.1 = v := by
    rw [← hvd]; exact LinearEquiv.symm_apply_apply _ v
  have h1 : lpVelocityDefect P γ₀ d ≤ ε ^ 2 := by
    rw [lpVelocityDefect, hvv, ← integral_norm_sub_sq_eq_norm_sq]; exact hv
  have h2 : dist d.1 γ₀.initial ≤ ε := mem_closedBall.1 hb
  have h3 : relaxedControlDistance P d.2.2 ρ₀ ≤ ε := hc
  exact ⟨lt_of_le_of_ne h1 fun h => hnb ⟨hd, Or.inl h⟩,
    lt_of_le_of_ne h2 fun h => hnb ⟨hd, Or.inr (Or.inl h)⟩,
    lt_of_le_of_ne h3 fun h => hnb ⟨hd, Or.inr (Or.inr h)⟩⟩

/-! ## The limit of the state-penalised minimisers (Lemma 11.3.5) -/

/-- **Ultrafilter limit of the state-penalised minimisers** (Berkovitz & Medhin, Lemma 11.3.5).

Let `de` minimise the anchored penalty `F` over the constrained tube, and let `d n` minimise
`H^{j n} = j n ∫ ω(G) + F` over the free tube with control frozen at `de.2.2`, with
`j n → ∞`.  Along every ultrafilter `𝒰 ≤ atTop`:

* `d n → d*` in the (norm × weak × weak-*) topology;
* the path of `d*` satisfies `G ≤ 0`, so `d*` lies in the constrained tube, and `F(d*) = F(de)`
  (lower semicontinuity and `F(d n) ≤ H^{j n}(d n) ≤ H^{j n}(de) = F(de)`);
* the velocity defects converge, `A(d n) → A(d*)` (sandwich between the weakly lsc `A` and the
  lsc remainder `F − A`), hence the velocities converge **in norm** (Hilbert-space identity);
* the initial values converge and the paths converge uniformly.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.7)–(11.3.9) and Lemma 11.3.5. -/
theorem exists_lpStatePenalised_ultrafilter_limit (P : Problem E V W) {G : ℝ → E → ℝ}
    {ω : ℝ → ℝ} (hG : Continuous fun p : ℝ × E => G p.1 p.2)
    (hGP : ∀ (t : P.Time) (y : E), P.stateConstraint t y = G t y)
    (hω : IsStatePenaltyProfile ω) {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    {γ₀ : VelocityTrajectory P} {ρ₀ : P.Relaxed}
    {de : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed}
    (hde : de ∈ lpTube P ε γ₀ ρ₀)
    (hdemin : ∀ d ∈ lpTube P ε γ₀ ρ₀,
      lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ de ≤ lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ d)
    {j : ℕ → ℝ} (hj : Tendsto j atTop atTop) (hj0 : ∀ n, 0 ≤ j n)
    {d : ℕ → E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed}
    (hdmem : ∀ n, d n ∈ lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = de.2.2})
    (hdmin : ∀ n, IsMinOn (lpStatePenalisedAnchored P G ω (j n) K ε γ₀ ρ₀)
      (lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = de.2.2}) (d n))
    (𝒰 : Ultrafilter ℕ) (h𝒰 : (𝒰 : Filter ℕ) ≤ atTop) :
    ∃ ds, ds ∈ lpTube P ε γ₀ ρ₀ ∧ ds.2.2 = de.2.2 ∧
      lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ ds = lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ de ∧
      (∀ t : P.Time, G t (lpPath P ds t) ≤ 0) ∧
      Tendsto d 𝒰 (𝓝 ds) ∧
      Tendsto (fun n => (d n).1) 𝒰 (𝓝 ds.1) ∧
      Tendsto (fun n => (toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon))).symm (d n).2.1) 𝒰
        (𝓝 ((toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon))).symm ds.2.1)) ∧
      Tendsto (fun n => lpPath P (d n)) 𝒰 (𝓝 (lpPath P ds)) ∧
      Tendsto (fun n => lpVelocityDefect P γ₀ (d n)) 𝒰 (𝓝 (lpVelocityDefect P γ₀ ds)) := by
  classical
  set F := lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ with hF
  set R : ℝ := ‖γ₀.toLp‖ + ε with hR
  set A : Set (E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :=
    (univ : Set E) ×ˢ (toWeakSpace ℝ _ '' {v : Lp E 2 (horizonMeasure P.horizon) | ‖v‖ ≤ R}) ×ˢ
      (univ : Set P.Relaxed) with hA
  set S := lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = de.2.2} with hS
  have hSA : S ⊆ A := inter_subset_left.trans (lpFreeTube_subset_bounded P hε γ₀ ρ₀)
  have hSc : IsCompact S := isCompact_lpFreeTube_inter P ε γ₀ ρ₀ de.2.2
  have hdeS : de ∈ S := ⟨hde.1, rfl⟩
  have hFlsc : LowerSemicontinuousOn F A :=
    lowerSemicontinuousOn_lpPenaltyPointwiseAnchored P K ε hK hε hEnd γ₀ ρ₀ R
  have hviol_de : lpStateViolation P G ω de = 0 :=
    stateViolationIntegral_eq_zero P G hω _ (stateConstraint_lpPath_of_mem_lpTube P hGP hde)
  have hviol_nn : ∀ x, 0 ≤ lpStateViolation P G ω x :=
    fun x => stateViolationIntegral_nonneg P G hω _
  -- comparison with the feasible datum `de`
  have hcmp : ∀ n, j n * lpStateViolation P G ω (d n) + F (d n) ≤ F de := by
    intro n
    have h : lpStatePenalisedAnchored P G ω (j n) K ε γ₀ ρ₀ (d n) ≤
        lpStatePenalisedAnchored P G ω (j n) K ε γ₀ ρ₀ de := hdmin n hdeS
    simp only [lpStatePenalisedAnchored, hviol_de, mul_zero, zero_add] at h
    exact h
  have hFle : ∀ n, F (d n) ≤ F de := fun n => by
    have := mul_nonneg (hj0 n) (hviol_nn (d n))
    linarith [hcmp n]
  obtain ⟨dmin, -, hdminmin⟩ := (hFlsc.mono hSA).exists_isMinOn ⟨de, hdeS⟩ hSc
  have hviol_bd : ∀ n, j n * lpStateViolation P G ω (d n) ≤ F de - F dmin := fun n => by
    have : F dmin ≤ F (d n) := hdminmin (hdmem n)
    linarith [hcmp n]
  -- the ultrafilter limit
  obtain ⟨ds, hdsS, hle⟩ := hSc.ultrafilter_le_nhds' (𝒰.map d) (by
    rw [Ultrafilter.mem_map]; exact Filter.univ_mem' hdmem)
  have htend : Tendsto d 𝒰 (𝓝 ds) := by
    rw [Tendsto, ← Ultrafilter.coe_map]; exact hle
  have htendA : Tendsto d 𝒰 (𝓝[A] ds) :=
    tendsto_nhdsWithin_iff.2 ⟨htend, Eventually.of_forall fun n => hSA (hdmem n)⟩
  have hdsA : ds ∈ A := hSA hdsS
  -- the state constraint at the limit
  have hviolT : Tendsto (fun n => lpStateViolation P G ω (d n)) 𝒰
      (𝓝 (lpStateViolation P G ω ds)) :=
    ((continuousOn_lpStateViolation P hG hω.continuous R) ds hdsA).tendsto.comp htendA
  have hC : Tendsto (fun n => (F de - F dmin) / j n) 𝒰 (𝓝 0) :=
    (Tendsto.div_atTop tendsto_const_nhds hj).mono_left h𝒰
  have hev : ∀ᶠ n in (𝒰 : Filter ℕ),
      lpStateViolation P G ω (d n) ≤ (F de - F dmin) / j n := by
    filter_upwards [h𝒰 (hj.eventually_gt_atTop 0)] with n hn
    rw [le_div_iff₀ hn]
    linarith [hviol_bd n, mul_comm (j n) (lpStateViolation P G ω (d n))]
  have hviol_ds : lpStateViolation P G ω ds ≤ 0 := le_of_tendsto_of_tendsto hviolT hC hev
  have hGds : ∀ t : P.Time, G t (lpPath P ds t) ≤ 0 :=
    stateConstraint_le_zero_of_stateViolationIntegral_nonpos P hG hω _ hviol_ds
  have hdsT : ds ∈ lpTube P ε γ₀ ρ₀ := mem_lpTube_of_mem_lpFreeTube P hGP hdsS.1 hGds
  -- the limit is an `F`-minimiser
  have hFds_le : F ds ≤ F de := by
    by_contra hlt
    push Not at hlt
    have h1 : ∀ᶠ n in (𝒰 : Filter ℕ), F de < F (d n) :=
      htendA.eventually (hFlsc ds hdsA (F de) hlt)
    obtain ⟨n, hn⟩ := h1.exists
    linarith [hFle n]
  have hFeq : F ds = F de := le_antisymm hFds_le (hdemin ds hdsT)
  -- convergence of the velocity defect (sandwich)
  have hBlsc := lowerSemicontinuousOn_lpPenaltyPointwiseAnchored_sub_lpVelocityDefect P K ε hK
    hε hEnd γ₀ ρ₀ R
  have hAT : Tendsto (fun n => lpVelocityDefect P γ₀ (d n)) 𝒰
      (𝓝 (lpVelocityDefect P γ₀ ds)) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      exact htend.eventually (lowerSemicontinuous_lpVelocityDefect P γ₀ ds a ha)
    · intro a ha
      have hη : F ds - lpVelocityDefect P γ₀ ds - (a - lpVelocityDefect P γ₀ ds) <
          F ds - lpVelocityDefect P γ₀ ds := by linarith
      filter_upwards [htendA.eventually (hBlsc ds hdsA _ hη)] with n hn
      linarith [hFle n, hFeq]
  -- norm convergence of the velocities
  set vs := (toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon))).symm ds.2.1 with hvs
  set ws := vs - γ₀.toLp with hws
  have hinnerT : Tendsto (fun n => inner ℝ
      ((toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon))).symm (d n).2.1) ws) 𝒰
      (𝓝 (inner ℝ vs ws)) :=
    (((continuous_inner_weakSpace_right ws).comp
      (continuous_fst.comp continuous_snd)).tendsto ds).comp htend
  have hsq : Tendsto (fun n =>
      ‖(toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon))).symm (d n).2.1 - vs‖ ^ 2) 𝒰
      (𝓝 0) := by
    have hexp : ∀ n,
        ‖(toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon))).symm (d n).2.1 - vs‖ ^ 2 =
          lpVelocityDefect P γ₀ (d n) - 2 * (inner ℝ
            ((toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon))).symm (d n).2.1) ws -
              inner ℝ γ₀.toLp ws) + ‖ws‖ ^ 2 := by
      intro n
      have h1 : (toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon))).symm (d n).2.1 - vs =
          ((toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon))).symm (d n).2.1 - γ₀.toLp) -
            ws := by
        rw [hws]; abel
      rw [h1, norm_sub_sq_real, inner_sub_left]
      rfl
    have hlim := (hAT.sub ((hinnerT.sub (tendsto_const_nhds (x := inner ℝ γ₀.toLp ws))).const_mul
      2)).add
      (tendsto_const_nhds (x := ‖ws‖ ^ 2))
    have h0 : lpVelocityDefect P γ₀ ds - 2 * (inner ℝ vs ws - inner ℝ γ₀.toLp ws) +
        ‖ws‖ ^ 2 = 0 := by
      have hA0 : lpVelocityDefect P γ₀ ds = ‖ws‖ ^ 2 := rfl
      have hI0 : inner ℝ vs ws - inner ℝ γ₀.toLp ws = ‖ws‖ ^ 2 := by
        rw [← inner_sub_left, ← hws, real_inner_self_eq_norm_sq]
      rw [hA0, hI0]
      ring
    rw [h0] at hlim
    exact hlim.congr fun n => (hexp n).symm
  have hvT : Tendsto (fun n => (toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon))).symm
      (d n).2.1) 𝒰 (𝓝 vs) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using this
  have hpT : Tendsto (fun n => lpPath P (d n)) 𝒰 (𝓝 (lpPath P ds)) :=
    ((continuousOn_lpPath P R) ds hdsA).tendsto.comp htendA
  have hiT : Tendsto (fun n => (d n).1) 𝒰 (𝓝 ds.1) := (continuous_fst.tendsto ds).comp htend
  exact ⟨ds, hdsT, hdsS.2, hFeq, hGds, htend, hiT, hvT, hpT, hAT⟩

/-- **Eventual strictness of the tube clauses for the state-penalised minimisers** (Berkovitz &
Medhin, Lemma 11.3.5 and the strict-interior conclusion used in (11.3.9)): under boundary
positivity `J₀ < F` on `lpTubeBoundary` and `F(de) ≤ J₀`, eventually every minimiser `d n` of
`H^{j n}` on the frozen free tube satisfies the velocity, initial and control clauses strictly.

The proof is by contradiction: an ultrafilter `𝒰 ≤ atTop` containing the bad indices yields the
limit of `exists_lpStatePenalised_ultrafilter_limit`, which is an `F`-minimiser off the boundary;
the velocity defects and the initial values converge along `𝒰`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.3 and Lemma 11.3.5. -/
theorem eventually_strict_lpStatePenalised_minimizer (P : Problem E V W) {G : ℝ → E → ℝ}
    {ω : ℝ → ℝ} (hG : Continuous fun p : ℝ × E => G p.1 p.2)
    (hGP : ∀ (t : P.Time) (y : E), P.stateConstraint t y = G t y)
    (hω : IsStatePenaltyProfile ω) {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    {γ₀ : VelocityTrajectory P} {ρ₀ : P.Relaxed}
    {de : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed}
    (hde : de ∈ lpTube P ε γ₀ ρ₀)
    (hdemin : ∀ d ∈ lpTube P ε γ₀ ρ₀,
      lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ de ≤ lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ d)
    {J₀ : ℝ} (hdeJ : lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ de ≤ J₀)
    (hbdry : ∀ d, lpTubeBoundary P ε γ₀ ρ₀ d → J₀ < lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ d)
    {j : ℕ → ℝ} (hj : Tendsto j atTop atTop) (hj0 : ∀ n, 0 ≤ j n)
    {d : ℕ → E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed}
    (hdmem : ∀ n, d n ∈ lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = de.2.2})
    (hdmin : ∀ n, IsMinOn (lpStatePenalisedAnchored P G ω (j n) K ε γ₀ ρ₀)
      (lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = de.2.2}) (d n)) :
    ∀ᶠ n in atTop, lpVelocityDefect P γ₀ (d n) < ε ^ 2 ∧ dist (d n).1 γ₀.initial < ε ∧
      relaxedControlDistance P (d n).2.2 ρ₀ < ε := by
  by_contra hcon
  rw [not_eventually] at hcon
  have := frequently_iff_neBot.1 hcon
  set 𝒰 := Ultrafilter.of (atTop ⊓ 𝓟 {n | ¬ (lpVelocityDefect P γ₀ (d n) < ε ^ 2 ∧
    dist (d n).1 γ₀.initial < ε ∧ relaxedControlDistance P (d n).2.2 ρ₀ < ε)}) with h𝒰def
  have h𝒰 : (𝒰 : Filter ℕ) ≤ atTop := (Ultrafilter.of_le _).trans inf_le_left
  have hbad : ∀ᶠ n in (𝒰 : Filter ℕ), ¬ (lpVelocityDefect P γ₀ (d n) < ε ^ 2 ∧
      dist (d n).1 γ₀.initial < ε ∧ relaxedControlDistance P (d n).2.2 ρ₀ < ε) :=
    le_principal_iff.1 ((Ultrafilter.of_le _).trans inf_le_right)
  obtain ⟨ds, hdsT, hds2, hFeq, -, -, hiT, -, -, hAT⟩ :=
    exists_lpStatePenalised_ultrafilter_limit P hG hGP hω hK hε hEnd hde hdemin hj hj0 hdmem
      hdmin 𝒰 h𝒰
  have hnb : ¬ lpTubeBoundary P ε γ₀ ρ₀ ds := fun hb => by
    have := hbdry ds hb
    rw [hFeq] at this
    linarith
  obtain ⟨hv, hi, hc⟩ := lpTube_strict_of_not_lpTubeBoundary P hdsT hnb
  have e1 := hAT.eventually (gt_mem_nhds hv)
  have e2 := (hiT.dist tendsto_const_nhds).eventually (gt_mem_nhds hi)
  obtain ⟨n, hn1, hn2, hn3⟩ := (e1.and (e2.and hbad)).exists
  exact hn3 ⟨hn1, hn2, by rw [(hdmem n).2, ← hds2]; exact hc⟩

/-- **Convergent subsequence of the state-penalised minimisers** (Berkovitz & Medhin,
Lemma 11.3.5): there is a strictly increasing `φ` and a limit datum `d*` such that the initial
values and the velocities of `d (φ n)` converge **in norm**, the paths converge uniformly, and
`d*` is an `F`-minimiser over the constrained tube, satisfies `G ≤ 0` along its path and the strict
tube clauses.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.9) and Lemma 11.3.5. -/
theorem exists_subseq_tendsto_lpStatePenalised_minimizer (P : Problem E V W) {G : ℝ → E → ℝ}
    {ω : ℝ → ℝ} (hG : Continuous fun p : ℝ × E => G p.1 p.2)
    (hGP : ∀ (t : P.Time) (y : E), P.stateConstraint t y = G t y)
    (hω : IsStatePenaltyProfile ω) {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    {γ₀ : VelocityTrajectory P} {ρ₀ : P.Relaxed}
    {de : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed}
    (hde : de ∈ lpTube P ε γ₀ ρ₀)
    (hdemin : ∀ d ∈ lpTube P ε γ₀ ρ₀,
      lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ de ≤ lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ d)
    {J₀ : ℝ} (hdeJ : lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ de ≤ J₀)
    (hbdry : ∀ d, lpTubeBoundary P ε γ₀ ρ₀ d → J₀ < lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ d)
    {j : ℕ → ℝ} (hj : Tendsto j atTop atTop) (hj0 : ∀ n, 0 ≤ j n)
    {d : ℕ → E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed}
    (hdmem : ∀ n, d n ∈ lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = de.2.2})
    (hdmin : ∀ n, IsMinOn (lpStatePenalisedAnchored P G ω (j n) K ε γ₀ ρ₀)
      (lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = de.2.2}) (d n)) :
    ∃ ds, ds ∈ lpTube P ε γ₀ ρ₀ ∧ ds.2.2 = de.2.2 ∧
      (∀ d' ∈ lpTube P ε γ₀ ρ₀,
        lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ ds ≤ lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ d') ∧
      (∀ t : P.Time, G t (lpPath P ds t) ≤ 0) ∧
      lpVelocityDefect P γ₀ ds < ε ^ 2 ∧ dist ds.1 γ₀.initial < ε ∧
      relaxedControlDistance P ds.2.2 ρ₀ < ε ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => (d (φ n)).1) atTop (𝓝 ds.1) ∧
        Tendsto (fun n => (toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon))).symm
          (d (φ n)).2.1) atTop
          (𝓝 ((toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon))).symm ds.2.1)) ∧
        ∀ η > 0, ∀ᶠ n in atTop, ∀ t : P.Time,
          dist (lpPath P (d (φ n)) t) (lpPath P ds t) < η := by
  set 𝒰 := Ultrafilter.of (atTop : Filter ℕ) with h𝒰def
  have h𝒰 : (𝒰 : Filter ℕ) ≤ atTop := Ultrafilter.of_le _
  obtain ⟨ds, hdsT, hds2, hFeq, hGds, -, hiT, hvT, hpT, -⟩ :=
    exists_lpStatePenalised_ultrafilter_limit P hG hGP hω hK hε hEnd hde hdemin hj hj0 hdmem
      hdmin 𝒰 h𝒰
  have hnb : ¬ lpTubeBoundary P ε γ₀ ρ₀ ds := fun hb => by
    have := hbdry ds hb
    rw [hFeq] at this
    linarith
  obtain ⟨hv, hi, hc⟩ := lpTube_strict_of_not_lpTubeBoundary P hdsT hnb
  let u : ℕ → E × Lp E 2 (horizonMeasure P.horizon) × P.Trajectory := fun n =>
    ((d n).1, (toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon))).symm (d n).2.1, lpPath P (d n))
  have huT : Tendsto u 𝒰 (𝓝 (ds.1,
      (toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon))).symm ds.2.1, lpPath P ds)) :=
    hiT.prodMk_nhds (hvT.prodMk_nhds hpT)
  have hclu : MapClusterPt (ds.1,
      (toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon))).symm ds.2.1, lpPath P ds) atTop u :=
    huT.mapClusterPt.mono h𝒰
  obtain ⟨φ, hφ, hφT⟩ := hclu.tendsto_subseq
  refine ⟨ds, hdsT, hds2, fun d' hd' => by rw [hFeq]; exact hdemin d' hd', hGds, hv, hi, hc,
    φ, hφ, ?_, ?_, ?_⟩
  · have h1 := (continuous_fst.tendsto _).comp hφT
    exact h1
  · have h1 := ((continuous_fst.comp continuous_snd).tendsto _).comp hφT
    exact h1
  · intro η hη
    have hp := ((continuous_snd.comp continuous_snd).tendsto _).comp hφT
    filter_upwards [Metric.tendsto_nhds.1 hp η hη] with n hn t
    exact lt_of_le_of_lt (BoundedContinuousFunction.dist_coe_le_dist t) hn

/-- **The hypotheses on the reference minimiser follow from relaxed optimality.**  For `0 < ε` and
a relaxed optimal pair `(γ₀, ρ₀)` there is a scale `K > 0` and a minimiser `de` of the anchored
penalty `F_K` over the constrained tube with `F_K(de) ≤ J₀` (the optimal cost) and boundary
positivity `J₀ < F_K` on `lpTubeBoundary`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.3 and Lemma 11.3.4. -/
theorem exists_anchored_tube_minimizer_of_boundary_positivity (P : Problem E V W) (ε : ℝ)
    (hε : 0 < ε) (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    (γ₀ : VelocityTrajectory P) (ρ₀ : P.Relaxed)
    (hopt : P.IsRelaxedMinimum (toBoundedPath γ₀) ρ₀) :
    ∃ K : ℝ, 0 < K ∧ ∃ de ∈ lpTube P ε γ₀ ρ₀,
      (∀ d ∈ lpTube P ε γ₀ ρ₀,
        lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ de ≤ lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ d) ∧
      lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ de ≤ P.relaxedCost (toBoundedPath γ₀) ρ₀ ∧
      ∀ d, lpTubeBoundary P ε γ₀ ρ₀ d →
        P.relaxedCost (toBoundedPath γ₀) ρ₀ < lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ d := by
  obtain ⟨K, hKpos, hK⟩ :=
    exists_penalty_scale_of_pointwise_boundary_positivity P ε hε hEnd γ₀ ρ₀ hopt
  have hstate : ∀ t : P.Time, P.stateConstraint t (γ₀.value t) ≤ 0 :=
    fun t => by simpa using hopt.1.2.2 t
  have href : (γ₀.initial, toWeakSpace ℝ _ γ₀.toLp, ρ₀) ∈ lpTube P ε γ₀ ρ₀ :=
    (mem_lpTube_iff P hε.le γ₀ γ₀ ρ₀ ρ₀).1 (self_mem_InVelocityControlTube P hε.le hstate)
  obtain ⟨de, hde, hmin⟩ := ((lowerSemicontinuousOn_lpPenaltyPointwiseAnchored P K ε hKpos.le
    hε.le hEnd γ₀ ρ₀ (‖γ₀.toLp‖ + ε)).mono ((lpTube_subset_lpFreeTube P ε γ₀ ρ₀).trans
      (lpFreeTube_subset_bounded P hε.le γ₀ ρ₀))).exists_isMinOn ⟨_, href⟩
    (isCompact_lpTube P ε γ₀ ρ₀)
  refine ⟨K, hKpos, de, hde, fun d hd => hmin hd, ?_, hK⟩
  have h1 : lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ de ≤
      lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ (γ₀.initial, toWeakSpace ℝ _ γ₀.toLp, ρ₀) :=
    hmin href
  rw [← velocityPenalizedPointwiseAnchored_eq_lpPenaltyPointwiseAnchored,
    velocityPenalizedPointwiseAnchored_self P K ε γ₀ ρ₀ hopt] at h1
  exact h1

/-! ## Carrier-level statements -/

/-- The velocity trajectory carried by a product-domain datum. -/
noncomputable def lpVelocityTrajectory (P : Problem E V W)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :
    VelocityTrajectory P :=
  VelocityTrajectory.ofLp P d.1 ((toWeakSpace ℝ _).symm d.2.1)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The `L²` class of the carried velocity is the velocity of the datum. -/
theorem lpVelocityTrajectory_toLp (P : Problem E V W)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :
    (lpVelocityTrajectory P d).toLp = (toWeakSpace ℝ _).symm d.2.1 :=
  VelocityTrajectory.toLp_ofLp _ _

omit [FiniteDimensional ℝ E] [CompleteSpace E] [FiniteDimensional ℝ V] [BorelSpace V] in
/-- The carrier data of the carried velocity trajectory recover the datum. -/
theorem lpVelocityTrajectory_data (P : Problem E V W)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :
    ((lpVelocityTrajectory P d).initial,
      toWeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) (lpVelocityTrajectory P d).toLp,
      d.2.2) = d := by
  have hi : (lpVelocityTrajectory P d).initial = d.1 := rfl
  rw [lpVelocityTrajectory_toLp, hi]
  simp

/-- The state path of the carried velocity trajectory is the primitive path of the datum. -/
theorem lpVelocityTrajectory_value (P : Problem E V W)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) P.horizon) :
    (lpVelocityTrajectory P d).value t = lpPath P d ⟨t, ht⟩ := by
  have h := (lpVelocityTrajectory P d).toBoundedPath_eq_primitiveBoundedPath
  rw [lpVelocityTrajectory_toLp] at h
  have h2 := congrArg (fun x : P.Trajectory => x ⟨t, ht⟩) h
  simp only [toBoundedPath_apply] at h2
  exact h2

/-- The velocity energy of the carried trajectory is the velocity defect of the datum. -/
theorem integral_sq_velocity_sub_lpVelocityTrajectory (P : Problem E V W)
    (γ₀ : VelocityTrajectory P)
    (d : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed) :
    (∫ s in (0 : ℝ)..P.horizon, ‖(lpVelocityTrajectory P d).velocity s - γ₀.velocity s‖ ^ 2) =
      lpVelocityDefect P γ₀ d := by
  rw [integral_sq_velocity_sub_eq γ₀ _, ← Lp_two_norm_sq_eq_integral_norm_sq, lpVelocityDefect,
    lpVelocityTrajectory_toLp]

/-- **Eventual strictness on the velocity carrier** (Berkovitz & Medhin, Lemma 11.3.5): the
carried trajectories of the state-penalised minimisers eventually satisfy the velocity and
initial clauses of the tube strictly.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.3 and Lemma 11.3.5. -/
theorem eventually_strict_velocityStatePenalised_minimizer (P : Problem E V W)
    {G : ℝ → E → ℝ} {ω : ℝ → ℝ} (hG : Continuous fun p : ℝ × E => G p.1 p.2)
    (hGP : ∀ (t : P.Time) (y : E), P.stateConstraint t y = G t y)
    (hω : IsStatePenaltyProfile ω) {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    {γ₀ : VelocityTrajectory P} {ρ₀ : P.Relaxed}
    {de : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed}
    (hde : de ∈ lpTube P ε γ₀ ρ₀)
    (hdemin : ∀ d ∈ lpTube P ε γ₀ ρ₀,
      lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ de ≤ lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ d)
    {J₀ : ℝ} (hdeJ : lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ de ≤ J₀)
    (hbdry : ∀ d, lpTubeBoundary P ε γ₀ ρ₀ d → J₀ < lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ d)
    {j : ℕ → ℝ} (hj : Tendsto j atTop atTop) (hj0 : ∀ n, 0 ≤ j n)
    {d : ℕ → E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed}
    (hdmem : ∀ n, d n ∈ lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = de.2.2})
    (hdmin : ∀ n, IsMinOn (lpStatePenalisedAnchored P G ω (j n) K ε γ₀ ρ₀)
      (lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = de.2.2}) (d n)) :
    ∀ᶠ n in atTop,
      (∫ s in (0 : ℝ)..P.horizon,
        ‖(lpVelocityTrajectory P (d n)).velocity s - γ₀.velocity s‖ ^ 2) < ε ^ 2 ∧
      dist (lpVelocityTrajectory P (d n)).initial γ₀.initial < ε ∧
      relaxedControlDistance P (d n).2.2 ρ₀ < ε := by
  filter_upwards [eventually_strict_lpStatePenalised_minimizer P hG hGP hω hK hε hEnd hde hdemin
    hdeJ hbdry hj hj0 hdmem hdmin] with n hn
  rw [integral_sq_velocity_sub_lpVelocityTrajectory]
  exact hn

/-- **Convergent subsequence on the velocity carrier** (Berkovitz & Medhin, Lemma 11.3.5): the
carried trajectories `γ_{φ n}` of a subsequence of the state-penalised minimisers converge to a
velocity trajectory `γ*` — initial values and `L²` velocities in norm, state paths uniformly on
`[0, t₁]` — and `(γ*, ρe)` lies in the tube `B(ε)`, minimises the anchored penalty over `B(ε)`,
satisfies the state constraint `G ≤ 0` and all tube clauses strictly.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.9) and Lemma 11.3.5. -/
theorem exists_subseq_tendsto_velocityStatePenalised_minimizer (P : Problem E V W)
    {G : ℝ → E → ℝ} {ω : ℝ → ℝ} (hG : Continuous fun p : ℝ × E => G p.1 p.2)
    (hGP : ∀ (t : P.Time) (y : E), P.stateConstraint t y = G t y)
    (hω : IsStatePenaltyProfile ω) {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hEnd : Continuous (Function.uncurry P.endpointConstraint))
    {γ₀ : VelocityTrajectory P} {ρ₀ : P.Relaxed}
    {de : E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed}
    (hde : de ∈ lpTube P ε γ₀ ρ₀)
    (hdemin : ∀ d ∈ lpTube P ε γ₀ ρ₀,
      lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ de ≤ lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ d)
    {J₀ : ℝ} (hdeJ : lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ de ≤ J₀)
    (hbdry : ∀ d, lpTubeBoundary P ε γ₀ ρ₀ d → J₀ < lpPenaltyPointwiseAnchored P K ε γ₀ ρ₀ d)
    {j : ℕ → ℝ} (hj : Tendsto j atTop atTop) (hj0 : ∀ n, 0 ≤ j n)
    {d : ℕ → E × WeakSpace ℝ (Lp E 2 (horizonMeasure P.horizon)) × P.Relaxed}
    (hdmem : ∀ n, d n ∈ lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = de.2.2})
    (hdmin : ∀ n, IsMinOn (lpStatePenalisedAnchored P G ω (j n) K ε γ₀ ρ₀)
      (lpFreeTube P ε γ₀ ρ₀ ∩ {d | d.2.2 = de.2.2}) (d n)) :
    ∃ γs : VelocityTrajectory P,
      InVelocityControlTube P γ₀ ρ₀ ε γs de.2.2 ∧
      (∀ γ' ρ', InVelocityControlTube P γ₀ ρ₀ ε γ' ρ' →
        velocityPenalizedPointwiseAnchored P K ε γ₀ ρ₀ γs de.2.2 ≤
          velocityPenalizedPointwiseAnchored P K ε γ₀ ρ₀ γ' ρ') ∧
      (∀ t ∈ Icc (0 : ℝ) P.horizon, G t (γs.value t) ≤ 0) ∧
      (∫ s in (0 : ℝ)..P.horizon, ‖γs.velocity s - γ₀.velocity s‖ ^ 2) < ε ^ 2 ∧
      dist γs.initial γ₀.initial < ε ∧ relaxedControlDistance P de.2.2 ρ₀ < ε ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => (lpVelocityTrajectory P (d (φ n))).initial) atTop (𝓝 γs.initial) ∧
        Tendsto (fun n => (lpVelocityTrajectory P (d (φ n))).toLp) atTop (𝓝 γs.toLp) ∧
        ∀ η > 0, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) P.horizon,
          dist ((lpVelocityTrajectory P (d (φ n))).value t) (γs.value t) < η := by
  obtain ⟨ds, hdsT, hds2, hmin, hGds, hv, hi, hc, φ, hφ, hiT, hvT, hpT⟩ :=
    exists_subseq_tendsto_lpStatePenalised_minimizer P hG hGP hω hK hε hEnd hde hdemin hdeJ
      hbdry hj hj0 hdmem hdmin
  have hdata := lpVelocityTrajectory_data P ds
  have hmem : InVelocityControlTube P γ₀ ρ₀ ε (lpVelocityTrajectory P ds) ds.2.2 :=
    (mem_lpTube_iff P hε γ₀ _ ρ₀ ds.2.2).2 (by rw [hdata]; exact hdsT)
  rw [← hds2]
  refine ⟨lpVelocityTrajectory P ds, hmem, ?_, ?_, ?_, hi, hc, φ, hφ, hiT, ?_, ?_⟩
  · intro γ' ρ' h'
    rw [velocityPenalizedPointwiseAnchored_eq_lpPenaltyPointwiseAnchored,
      velocityPenalizedPointwiseAnchored_eq_lpPenaltyPointwiseAnchored, hdata]
    exact hmin _ ((mem_lpTube_iff P hε γ₀ γ' ρ₀ ρ').1 h')
  · intro t ht
    rw [lpVelocityTrajectory_value P ds ht]
    exact hGds ⟨t, ht⟩
  · rw [integral_sq_velocity_sub_lpVelocityTrajectory]
    exact hv
  · simp only [lpVelocityTrajectory_toLp]
    exact hvT
  · intro η hη
    filter_upwards [hpT η hη] with n hn t ht
    rw [lpVelocityTrajectory_value P _ ht, lpVelocityTrajectory_value P _ ht]
    exact hn ⟨t, ht⟩

end Problem

end OptimalControl.BoundedState
