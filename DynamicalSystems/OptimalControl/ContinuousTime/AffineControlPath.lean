/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module
public import DynamicalSystems.Mathlib.Analysis.ODE.AffineIntegralResponse
public import DynamicalSystems.OptimalControl.ContinuousTime.StateConstraintMultipliers

/-! # Actual affine trajectories on the normalized control horizon -/
@[expose] public section
open Set MeasureTheory
open scoped Interval Topology NNReal
namespace OptimalControl
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The subtype and real interval integrals agree exactly after undoing normalization. -/
theorem integral_horizon_prefix {T : ℝ} (hT : 0 < T)
    (g : ControlTime T → E) (t : ControlTime T) :
    T • (∫ s in Ioc (timeZero T hT.le) t, g s ∂horizonProbability T hT) =
      ∫ r in (0 : ℝ)..(t : ℝ), g (projIcc 0 T hT.le r) := by
  rw [← integral_indicator measurableSet_Ioc, integral_horizonProbability]
  let f : ℝ → E := fun r ↦ (Ioc (0 : ℝ) (t : ℝ)).indicator
    (fun r ↦ g (projIcc 0 T hT.le r)) r
  have hcomp : (Ioc (timeZero T hT.le) t).indicator g =
      fun s : ControlTime T ↦ f s := by
    funext s
    have hm : s ∈ Ioc (timeZero T hT.le) t ↔ (s : ℝ) ∈ Ioc 0 (t : ℝ) := Iff.rfl
    simp only [f, Set.indicator, hm, projIcc_of_mem hT.le s.2]
  rw [hcomp, ← (MeasurableEmbedding.subtype_coe measurableSet_Icc).integral_map f,
    map_horizonVolume]
  rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
  have hi : Ioc (0 : ℝ) (t : ℝ) ∩ Icc 0 T = Ioc 0 (t : ℝ) := by
    ext r
    simp only [mem_inter_iff, mem_Ioc, mem_Icc]
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, h.1.le, h.2.trans t.2.2⟩⟩
  rw [hi, intervalIntegral.integral_of_le t.2.1]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- A measurable bounded subtype forcing gives actual L1 forcing after clamping time. -/
theorem intervalIntegrable_horizon_extend [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {T : ℝ} (hT : 0 < T)
    {g : ControlTime T → E} (hg : Measurable g) {C : ℝ} (hC : ∀ s, ‖g s‖ ≤ C) :
    IntervalIntegrable (fun r ↦ g (projIcc 0 T hT.le r)) volume 0 T := by
  apply (intervalIntegrable_const (c := C)).mono_fun'
  · exact (hg.comp continuous_projIcc.measurable).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun r ↦ by simpa using hC (projIcc 0 T hT.le r))

namespace ConvexStateControlProblem
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {n : ℕ}

omit [CompleteSpace E] in
/-- Compact controls and continuous affine forcing derive the required L1 bound. -/
theorem intervalIntegrable_affine_forcing (P : ConvexStateControlProblem E V n)
    (B : P.Time → V →L[ℝ] E) (hB : Continuous B) (a : P.Time → E) (ha : Continuous a)
    (u : P.Time → V) (hu : Measurable u) (hmem : ∀ t, u t ∈ P.controlSet) :
    IntervalIntegrable (fun r ↦ B (projIcc 0 P.horizon P.horizon_pos.le r)
      (u (projIcc 0 P.horizon P.horizon_pos.le r)) +
      a (projIcc 0 P.horizon P.horizon_pos.le r)) volume 0 P.horizon := by
  have hc : Continuous (fun z : P.Time × V ↦ B z.1 z.2 + a z.1) :=
    ((hB.comp continuous_fst).clm_apply continuous_snd).add (ha.comp continuous_fst)
  obtain ⟨C, hC⟩ := (isCompact_univ.prod P.controlSet_compact).exists_bound_of_continuousOn
    hc.continuousOn
  apply intervalIntegrable_horizon_extend P.horizon_pos
    (g := fun t ↦ B t (u t) + a t) (C := C)
    (hc.measurable.comp (measurable_id.prodMk hu))
  intro t
  exact hC (t, u t) ⟨mem_univ t, hmem t⟩

omit [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Fixed transition data is constructed once from the primitive state coefficient. -/
theorem exists_affine_transition [FiniteDimensional ℝ E]
    (P : ConvexStateControlProblem E V n) (A : P.Time → E →L[ℝ] E) (hA : Continuous A) :
    ∃ (Aext : ℝ → E →L[ℝ] E) (Phi : ℝ → ℝ → E →L[ℝ] E),
      Continuous Aext ∧ (∀ t : P.Time, Aext t = A t) ∧ IsStateTransition Aext Phi := by
  let Aext : ℝ → E →L[ℝ] E := fun r ↦ A (projIcc 0 P.horizon P.horizon_pos.le r)
  have hAe : Continuous Aext := hA.comp continuous_projIcc
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hA.continuousOn
  let K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hb : ∀ r, ‖Aext r‖ ≤ (K : ℝ) := fun r ↦
    (hC _ (mem_univ _)).trans (le_max_left _ _)
  obtain ⟨Phi, hPhi⟩ := exists_stateTransition_of_continuous_bounded hAe hb
  refine ⟨Aext, Phi, hAe, ?_, hPhi⟩
  intro t
  simp only [Aext, projIcc_of_mem P.horizon_pos.le t.2]

/-- Every measurable compact-valued control has a constructed affine integral trajectory. -/
theorem exists_affine_candidate (P : ConvexStateControlProblem E V n)
    (A : P.Time → E →L[ℝ] E) (B : P.Time → V →L[ℝ] E) (hB : Continuous B)
    (a : P.Time → E) (ha : Continuous a)
    (hf : ∀ t x u, P.dynamics t x u = A t x + B t u + a t)
    {Aext : ℝ → E →L[ℝ] E} (hAe : Continuous Aext)
    (heA : ∀ t : P.Time, Aext t = A t)
    {Phi : ℝ → ℝ → E →L[ℝ] E} (hPhi : IsStateTransition Aext Phi)
    (u : P.Time → V) (hu : Measurable u) (hmem : ∀ t, u t ∈ P.controlSet) :
    ∃ y : P.Candidate, P.DynamicsAdmissible y ∧ y.2 = u ∧
      ∀ t, y.1 t = AffineIntegralResponse.response Phi 0 P.initial
        (fun r ↦ B (projIcc 0 P.horizon P.horizon_pos.le r)
          (u (projIcc 0 P.horizon P.horizon_pos.le r)) +
          a (projIcc 0 P.horizon P.horizon_pos.le r)) t := by
  let g : ℝ → E := fun r ↦ B (projIcc 0 P.horizon P.horizon_pos.le r)
    (u (projIcc 0 P.horizon P.horizon_pos.le r)) + a (projIcc 0 P.horizon P.horizon_pos.le r)
  have hg : IntervalIntegrable g volume 0 P.horizon :=
    P.intervalIntegrable_affine_forcing B hB a ha u hu hmem
  let x : C(P.Time, E) := ⟨fun t ↦ AffineIntegralResponse.response Phi 0 P.initial g t,
    (show ContinuousOn (AffineIntegralResponse.response Phi 0 P.initial g) (Icc 0 P.horizon) by
      simpa only [uIcc_of_le P.horizon_pos.le] using
        AffineIntegralResponse.continuousOn_response hPhi P.initial hg).domRestrict⟩
  refine ⟨(x, u), ⟨hu, hmem, ?_⟩, rfl, fun _ ↦ rfl⟩
  intro t
  rw [integral_horizon_prefix P.horizon_pos]
  change AffineIntegralResponse.response Phi 0 P.initial g t = _
  rw [AffineIntegralResponse.response_integral_eq hPhi hAe t.2.1 P.initial
    (hg.mono_set (uIcc_subset_uIcc_left (by simp [uIcc_of_le P.horizon_pos.le])))]
  congr 1
  apply intervalIntegral.integral_congr
  intro r hr
  have hrT : r ∈ Icc 0 P.horizon := by
    rw [uIcc_of_le t.2.1] at hr
    exact ⟨hr.1, hr.2.trans t.2.2⟩
  have htA := heA (⟨r, hrT⟩ : P.Time)
  simp only [hf, x, g, projIcc_of_mem P.horizon_pos.le hrT,
    htA, add_assoc]
  rfl

/-- Every actual affine trajectory equals the response constructed from its measurable control. -/
theorem affine_trajectory_eq_response (P : ConvexStateControlProblem E V n)
    (A : P.Time → E →L[ℝ] E) (B : P.Time → V →L[ℝ] E) (hB : Continuous B)
    (a : P.Time → E) (ha : Continuous a)
    (hf : ∀ t x u, P.dynamics t x u = A t x + B t u + a t)
    {Aext : ℝ → E →L[ℝ] E} (hAe : Continuous Aext)
    (heA : ∀ t : P.Time, Aext t = A t)
    {Phi : ℝ → ℝ → E →L[ℝ] E} (hPhi : IsStateTransition Aext Phi)
    (y : P.Candidate) (hy : P.DynamicsAdmissible y) (t : P.Time) :
    y.1 t = AffineIntegralResponse.response Phi 0 P.initial
      (fun r ↦ B (projIcc 0 P.horizon P.horizon_pos.le r)
        (y.2 (projIcc 0 P.horizon P.horizon_pos.le r)) +
        a (projIcc 0 P.horizon P.horizon_pos.le r)) t := by
  let g : ℝ → E := fun r ↦ B (projIcc 0 P.horizon P.horizon_pos.le r)
    (y.2 (projIcc 0 P.horizon P.horizon_pos.le r)) + a (projIcc 0 P.horizon P.horizon_pos.le r)
  let x : ℝ → E := fun r ↦ y.1 (projIcc 0 P.horizon P.horizon_pos.le r)
  have hg : IntervalIntegrable g volume 0 P.horizon :=
    P.intervalIntegrable_affine_forcing B hB a ha y.2 hy.1 hy.2.1
  have hx : Continuous x := y.1.continuous.comp continuous_projIcc
  have heq : ∀ r ∈ Icc 0 P.horizon, x r = P.initial +
      ∫ s in (0 : ℝ)..r, Aext s (x s) + g s := by
    intro r hr
    have he := hy.2.2 (⟨r, hr⟩ : P.Time)
    rw [integral_horizon_prefix P.horizon_pos] at he
    have hxval : x r = y.1 ⟨r, hr⟩ := by simp only [x, projIcc_of_mem P.horizon_pos.le hr]
    rw [hxval, he]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hsT : s ∈ Icc 0 P.horizon := by
      rw [uIcc_of_le hr.1] at hs
      exact ⟨hs.1, hs.2.trans hr.2⟩
    have hsA := heA (⟨s, hsT⟩ : P.Time)
    simp only [hf, x, g, projIcc_of_mem P.horizon_pos.le hsT, hsA, add_assoc]
  have he := AffineIntegralResponse.eq_response_of_integral_eq hPhi hAe
    P.horizon_pos.le P.initial hg hx.continuousOn heq t t.2
  simpa only [x, projIcc_of_mem P.horizon_pos.le t.2] using he

omit [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Continuous compact-control data composed with a measurable control is integrable. -/
theorem integrable_compact_control_data (P : ConvexStateControlProblem E V n)
    {F : P.Time × V → E} (hF : Continuous F) (u : P.Time → V)
    (hu : Measurable u) (hmem : ∀ t, u t ∈ P.controlSet) :
    Integrable (fun t ↦ F (t, u t)) (horizonProbability P.horizon P.horizon_pos).toMeasure := by
  let : CompactSpace P.controlSet := isCompact_iff_compactSpace.mp P.controlSet_compact
  let v : P.Time → P.Time × P.controlSet := fun t ↦ (t, ⟨u t, hmem t⟩)
  have hv : Measurable v := measurable_id.prodMk hu.subtype_mk
  have hfc : Continuous (fun q : P.Time × P.controlSet ↦ F (q.1, q.2)) :=
    hF.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hi := hfc.integrable_of_hasCompactSupport (μ := Measure.map v
    (horizonProbability P.horizon P.horizon_pos).toMeasure) (HasCompactSupport.of_compactSpace _)
  exact hi.comp_measurable hv

/-- Reference-frame formula for every actual affine trajectory, with genuine normalized prefix. -/
theorem affine_trajectory_eq_reference (P : ConvexStateControlProblem E V n)
    (A : P.Time → E →L[ℝ] E) (B : P.Time → V →L[ℝ] E) (hB : Continuous B)
    (a : P.Time → E) (ha : Continuous a)
    (hf : ∀ t x u, P.dynamics t x u = A t x + B t u + a t)
    {Aext : ℝ → E →L[ℝ] E} (hAe : Continuous Aext)
    (heA : ∀ t : P.Time, Aext t = A t)
    {Phi : ℝ → ℝ → E →L[ℝ] E} (hPhi : IsStateTransition Aext Phi)
    (y : P.Candidate) (hy : P.DynamicsAdmissible y) (t : P.Time) :
    y.1 t = Phi t 0 (P.initial + P.horizon •
      ∫ s in Iio t, Phi 0 s (B s (y.2 s) + a s)
        ∂horizonProbability P.horizon P.horizon_pos) := by
  rw [P.affine_trajectory_eq_response A B hB a ha hf hAe heA hPhi y hy t]
  have hg := P.intervalIntegrable_affine_forcing B hB a ha y.2 hy.1 hy.2.1
  rw [AffineIntegralResponse.response_eq_reference hPhi 0 t P.initial
    (hg.mono_set (uIcc_subset_uIcc_left (by simp [uIcc_of_le P.horizon_pos.le])))]
  have hpc : Continuous (fun s : P.Time ↦ Phi 0 s) :=
    hPhi.continuous.comp (continuous_const.prodMk continuous_subtype_val)
  have hi := P.integrable_compact_control_data
    (hpc.comp continuous_fst |>.clm_apply
      (((hB.comp continuous_fst).clm_apply continuous_snd).add (ha.comp continuous_fst)))
    y.2 hy.1 hy.2.1
  have hprefix := integralControlPath_prefix P.horizon_pos (0 : E)
    (fun s : P.Time ↦ Phi 0 s (B s (y.2 s) + a s)) hi t
  simp only [integralControlPath, zero_add] at hprefix
  rw [← hprefix, integral_horizon_prefix P.horizon_pos]
  congr 2
  apply intervalIntegral.integral_congr
  intro r hr
  have hrT : r ∈ Icc 0 P.horizon := by
    rw [uIcc_of_le t.2.1] at hr
    exact ⟨hr.1, hr.2.trans t.2.2⟩
  simp only [projIcc_of_mem P.horizon_pos.le hrT]

/-- Exact actual-trajectory variation, derived from affine dynamics and constructed responses. -/
theorem affine_trajectory_sub (P : ConvexStateControlProblem E V n)
    (A : P.Time → E →L[ℝ] E) (B : P.Time → V →L[ℝ] E) (hB : Continuous B)
    (a : P.Time → E) (ha : Continuous a)
    (hf : ∀ t x u, P.dynamics t x u = A t x + B t u + a t)
    {Aext : ℝ → E →L[ℝ] E} (hAe : Continuous Aext)
    (heA : ∀ t : P.Time, Aext t = A t)
    {Phi : ℝ → ℝ → E →L[ℝ] E} (hPhi : IsStateTransition Aext Phi)
    (y z : P.Candidate) (hy : P.DynamicsAdmissible y) (hz : P.DynamicsAdmissible z)
    (t : P.Time) :
    y.1 t - z.1 t = P.horizon • Phi t 0
      (∫ s in Iio t, Phi 0 s (B s (y.2 s - z.2 s))
        ∂horizonProbability P.horizon P.horizon_pos) := by
  rw [P.affine_trajectory_eq_reference A B hB a ha hf hAe heA hPhi y hy t,
    P.affine_trajectory_eq_reference A B hB a ha hf hAe heA hPhi z hz t,
    ← map_sub, add_sub_add_left_eq_sub, ← smul_sub, map_smul]
  have hpc : Continuous (fun s : P.Time ↦ Phi 0 s) :=
    hPhi.continuous.comp (continuous_const.prodMk continuous_subtype_val)
  have hc : Continuous (fun q : P.Time × V ↦ Phi 0 q.1 (B q.1 q.2 + a q.1)) :=
    (hpc.comp continuous_fst).clm_apply
      (((hB.comp continuous_fst).clm_apply continuous_snd).add (ha.comp continuous_fst))
  have hiy := P.integrable_compact_control_data hc y.2 hy.1 hy.2.1
  have hiz := P.integrable_compact_control_data hc z.2 hz.1 hz.2.1
  rw [← integral_sub hiy.integrableOn hiz.integrableOn]
  congr 2
  apply setIntegral_congr_fun measurableSet_Iio
  intro s hs
  simp only [← map_sub, add_sub_add_right_eq_sub]

/-- Primitive affine data produces a fixed transition, every comparison trajectory, and the
exact response identity for all actual pairs. -/
theorem exists_affine_response_data [FiniteDimensional ℝ E]
    (P : ConvexStateControlProblem E V n)
    (A : P.Time → E →L[ℝ] E) (hA : Continuous A)
    (B : P.Time → V →L[ℝ] E) (hB : Continuous B) (a : P.Time → E) (ha : Continuous a)
    (hf : ∀ t x u, P.dynamics t x u = A t x + B t u + a t) :
    ∃ (Aext : ℝ → E →L[ℝ] E) (Phi : ℝ → ℝ → E →L[ℝ] E),
      Continuous Aext ∧ (∀ t : P.Time, Aext t = A t) ∧ IsStateTransition Aext Phi ∧
      (∀ u : P.Time → V, Measurable u → (∀ t, u t ∈ P.controlSet) →
        ∃ y : P.Candidate, P.DynamicsAdmissible y ∧ y.2 = u) ∧
      ∀ y z : P.Candidate, P.DynamicsAdmissible y → P.DynamicsAdmissible z →
        ∀ t : P.Time, y.1 t - z.1 t = P.horizon • Phi t 0
          (∫ s in Iio t, Phi 0 s (B s (y.2 s - z.2 s))
            ∂horizonProbability P.horizon P.horizon_pos) := by
  obtain ⟨Aext, Phi, hAe, heA, hPhi⟩ := P.exists_affine_transition A hA
  refine ⟨Aext, Phi, hAe, heA, hPhi, ?_, ?_⟩
  · intro u hu hmem
    obtain ⟨y, hy, he, _⟩ := P.exists_affine_candidate A B hB a ha hf hAe heA hPhi u hu hmem
    exact ⟨y, hy, he⟩
  · intro y z hy hz t
    exact P.affine_trajectory_sub A B hB a ha hf hAe heA hPhi y z hy hz t

end ConvexStateControlProblem
end OptimalControl
