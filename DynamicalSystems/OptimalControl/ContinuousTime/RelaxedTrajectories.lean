/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.ControlHorizon
public import DynamicalSystems.OptimalControl.ContinuousTime.OccupationIntegral
public import DynamicalSystems.Mathlib.Topology.LipschitzPaths

/-!
# Closed and compact graphs of actual relaxed trajectories

The defining relation is the Volterra equation at every time, with normalized
Lebesgue time marginal and its normalization undone by `T`. Bounded velocity
implies a common Lipschitz bound. Uniform-path/weak-control closure is derived
from time-restricted occupation integral continuity, then Arzelà–Ascoli proves
compactness of the trajectory graph.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped BoundedContinuousFunction NNReal Topology

namespace OptimalControl

variable {T : ℝ} {U E : Type*}
  [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [CompactSpace U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Actual integral dynamics, at every time on the compact horizon. -/
def IsRelaxedTrajectory (hT : 0 < T) (f : ControlTime T → E → U → E) (x₀ : E)
    (x : ControlTime T →ᵇ E) (ρ : RelaxedControl (ControlTime T) U (horizonProbability T hT)) : Prop :=
  ∀ t, x t = x₀ + T • ∫ z in (Ioc (timeZero T hT.le) t) ×ˢ univ,
    f z.1 (x z.1) z.2 ∂ρ.measure

omit [MetricSpace U] [BorelSpace U] [CompactSpace U] [FiniteDimensional ℝ E] in
/-- Integral dynamics imply the initial condition. -/
theorem IsRelaxedTrajectory.initial {hT : 0 < T} {f : ControlTime T → E → U → E}
    {x₀ : E} {x : ControlTime T →ᵇ E}
    {ρ : RelaxedControl (ControlTime T) U (horizonProbability T hT)}
    (hx : IsRelaxedTrajectory hT f x₀ x ρ) : x (timeZero T hT.le) = x₀ := by
  simpa using hx (timeZero T hT.le)

omit [MeasurableSpace U] [BorelSpace U] [CompactSpace U] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Joint continuity of the field evaluated on a uniformly varying path. -/
theorem continuous_trajectoryField (f : ControlTime T → E → U → E)
    (hf : Continuous (fun z : (ControlTime T × E) × U => f z.1.1 z.1.2 z.2)) :
    Continuous (fun p : (ControlTime T →ᵇ E) × (ControlTime T × U) =>
      f p.2.1 (p.1 p.2.1) p.2.2) := by
  exact hf.comp ((continuous_snd.fst.prodMk (continuous_fst.eval continuous_snd.fst)).prodMk
    continuous_snd.snd)

/-- The actual Volterra-dynamics graph is closed in uniform path × weak
occupation measure topology. No closure premise is assumed. -/
theorem isClosed_relaxedTrajectoryGraph (hT : 0 < T) (f : ControlTime T → E → U → E)
    (hf : Continuous (fun z : (ControlTime T × E) × U => f z.1.1 z.1.2 z.2)) (x₀ : E) :
    IsClosed {p : (ControlTime T →ᵇ E) ×
      RelaxedControl (ControlTime T) U (horizonProbability T hT) |
        IsRelaxedTrajectory hT f x₀ p.1 p.2} := by
  simp only [IsRelaxedTrajectory, ofPred_forall]
  apply isClosed_iInter
  intro t
  apply isClosed_eq (continuous_fst.eval_const t)
  exact continuous_const.add (continuous_const.smul
    (RelaxedControl.continuous_setIntegral_param
      (fun (x : ControlTime T →ᵇ E) (z : ControlTime T × U) => f z.1 (x z.1) z.2) (continuous_trajectoryField f hf) measurableSet_Ioc))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Integrability along a continuous trajectory follows from continuity on
the compact time/control product. -/
theorem integrable_trajectoryField (hT : 0 < T) (f : ControlTime T → E → U → E)
    (hf : Continuous (fun z : (ControlTime T × E) × U => f z.1.1 z.1.2 z.2))
    (x : ControlTime T →ᵇ E)
    (ρ : RelaxedControl (ControlTime T) U (horizonProbability T hT)) :
    Integrable (fun z : ControlTime T × U => f z.1 (x z.1) z.2) ρ.measure :=
  (hf.comp ((continuous_fst.prodMk (x.continuous.comp continuous_fst)).prodMk continuous_snd)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [FiniteDimensional ℝ E] in
/-- Bounded actual velocities imply a common Lipschitz estimate. This is the
compactness estimate, not a regularity assumption on the candidate paths. -/
theorem IsRelaxedTrajectory.lipschitzWith {hT : 0 < T} {f : ControlTime T → E → U → E}
    (hf : Continuous (fun z : (ControlTime T × E) × U => f z.1.1 z.1.2 z.2))
    {M : ℝ≥0} (hM : ∀ t x u, ‖f t x u‖ ≤ M) {x₀ : E} {x : ControlTime T →ᵇ E}
    {ρ : RelaxedControl (ControlTime T) U (horizonProbability T hT)}
    (hx : IsRelaxedTrajectory hT f x₀ x ρ) : LipschitzWith M x := by
  have hfi := integrable_trajectoryField hT f hf x ρ
  have hbound : ∀ r s : ControlTime T, r ≤ s → dist (x s) (x r) ≤ M * dist s r := by
    intro r s hrs
    let a := timeZero T hT.le
    have har : a ≤ r := r.2.1
    have hdiff : (Ioc a s ×ˢ (univ : Set U)) \ (Ioc a r ×ˢ univ) = Ioc r s ×ˢ univ := by
      ext z
      simp only [Set.mem_sdiff, mem_prod, mem_Ioc, mem_univ, and_true]
      constructor
      · rintro ⟨⟨haz, hzs⟩, hn⟩
        exact ⟨lt_of_not_ge (fun hzr => hn ⟨haz, hzr⟩), hzs⟩
      · rintro ⟨hrz, hzs⟩
        exact ⟨⟨har.trans_lt hrz, hzs⟩, fun h => (not_le_of_gt hrz) h.2⟩
    have hsub : Ioc a r ×ˢ (univ : Set U) ⊆ Ioc a s ×ˢ univ :=
      Set.prod_mono (Ioc_subset_Ioc_right hrs) Subset.rfl
    have heq := setIntegral_sdiff (measurableSet_Ioc.prod MeasurableSet.univ) hfi.integrableOn hsub
    rw [hdiff] at heq
    have hxsub : x s - x r = T • ∫ z in Ioc r s ×ˢ univ, f z.1 (x z.1) z.2 ∂ρ.measure := by
      rw [hx s, hx r, add_sub_add_left_eq_sub, ← smul_sub, ← heq]
    rw [dist_eq_norm, hxsub, norm_smul, Real.norm_of_nonneg hT.le]
    have hn : ‖∫ z in Ioc r s ×ˢ univ, f z.1 (x z.1) z.2 ∂ρ.measure‖ ≤
        M * ρ.measure.real (Ioc r s ×ˢ univ) :=
      norm_setIntegral_le_of_norm_le_const (measure_lt_top _ _) (fun z _ => hM _ _ _)
    have hm : T * ρ.measure.real (Ioc r s ×ˢ univ) = (s : ℝ) - r := by
      rw [measureReal_def, ρ.measure_prod_univ measurableSet_Ioc]
      exact scale_horizonProbability_real_Ioc T hT r s hrs
    calc
      T * ‖∫ z in Ioc r s ×ˢ univ, f z.1 (x z.1) z.2 ∂ρ.measure‖ ≤
          T * (M * ρ.measure.real (Ioc r s ×ˢ univ)) := mul_le_mul_of_nonneg_left hn hT.le
      _ = M * ((s : ℝ) - r) := by rw [mul_left_comm, hm]
      _ = M * dist s r := by rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (show (r : ℝ) ≤ s from hrs))]
  apply LipschitzWith.of_dist_le_mul
  intro r s
  rcases le_total r s with hrs | hsr
  · simpa only [dist_comm] using hbound r s hrs
  · exact hbound s r hsr

/-- Compactness of the full relaxed trajectory graph is derived from the
bounded vector field, finite dimension, and actual dynamics closure. -/
theorem isCompact_relaxedTrajectoryGraph (hT : 0 < T) (f : ControlTime T → E → U → E)
    (hf : Continuous (fun z : (ControlTime T × E) × U => f z.1.1 z.1.2 z.2))
    (M : ℝ≥0) (hM : ∀ t x u, ‖f t x u‖ ≤ M) (x₀ : E) :
    IsCompact {p : (ControlTime T →ᵇ E) ×
      RelaxedControl (ControlTime T) U (horizonProbability T hT) |
        IsRelaxedTrajectory hT f x₀ p.1 p.2} := by
  apply ((BoundedContinuousFunction.isCompact_lipschitzPaths M (timeZero T hT.le) x₀).prod
    isCompact_univ).of_isClosed_subset (isClosed_relaxedTrajectoryGraph hT f hf x₀)
  intro p hp
  exact ⟨⟨hp.lipschitzWith hf hM, hp.initial⟩, mem_univ _⟩

end OptimalControl
