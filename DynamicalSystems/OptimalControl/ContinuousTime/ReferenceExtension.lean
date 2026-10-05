import DynamicalSystems.OptimalControl.ContinuousTime.NeedleFamily

/-!
# Extending a finite-horizon reference without changing integral optimality

The global-reference hypothesis used by the IVP family construction is a
convenience. A reference satisfying the actual classical ODE on `[0,T]`
coincides there with a global nominal solution, by uniqueness. Integral
admissibility, total cost, and integral optimality are invariant under a change
of the state curve outside the horizon. This does not enlarge a competitor
class or infer integral optimality from classical optimality.
-/

namespace NeedleIntegralModel

open Set MeasureTheory
open scoped Interval NNReal

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A classical reference on the horizon has a global nominal ODE extension
that agrees with it everywhere on the horizon, including both endpoints. -/
theorem exists_global_reference_extension
    {F : ℝ → E → E} {x : ℝ → E} {T B : ℝ} {K : ℝ≥0}
    (hLip : ∀ t, LipschitzWith K (F t))
    (hB : ∀ t, ‖F t 0‖ ≤ B) (hF : Continuous F.uncurry)
    (hx : ∀ t ∈ Icc 0 T, HasDerivAt x (F t (x t)) t) :
    ∃ y : ℝ → E, IsIntegralCurve y F ∧ y 0 = x 0 ∧ EqOn y x (Icc 0 T) := by
  obtain ⟨Φ, hΦ⟩ := global_existence hLip hB hF
  let y := Φ 0 (x 0)
  have hy : IsIntegralCurve y F := (hΦ 0 (x 0)).1
  have hy₀ : y 0 = x 0 := (hΦ 0 (x 0)).2
  have hxc : ContinuousOn x (Icc 0 T) :=
    fun t ht => (hx t ht).continuousAt.continuousWithinAt
  have hbound := needle_displacement_bound_after_spike
    (x := y) (y := x) (V := F) (tube := fun _ => univ)
    (τ := 0) (T := T) (C := 0) (ε := 0) (K := K)
    (le_refl 0) (le_refl 0) (fun t _ => (hLip t).lipschitzOnWith)
    hy.continuous.continuousOn (fun t _ => (hy t).hasDerivWithinAt)
    (by simp) hxc (fun t ht => (hx t ⟨ht.1, ht.2.le⟩).hasDerivWithinAt)
    (by simp) (by simp [hy₀])
  refine ⟨y, hy, hy₀, ?_⟩
  intro t ht
  have hnorm : ‖y t - x t‖ ≤ 0 := by simpa only [zero_mul] using hbound t ht
  exact sub_eq_zero.mp (norm_le_zero_iff.mp hnorm)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
/-- Total cost depends only on the state curve on the actual horizon. -/
theorem totalCost_eq_of_eqOn
    (prob : ContinuousOCP E U) (u : ℝ → U) {x y : ℝ → E}
    (hT : 0 ≤ prob.T) (hxy : EqOn x y (Icc 0 prob.T)) :
    continuousTotalCost prob x u = continuousTotalCost prob y u := by
  unfold continuousTotalCost
  rw [hxy (right_mem_Icc.mpr hT)]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hT] at ht
  change prob.L t (x t) (u t) = prob.L t (y t) (u t)
  rw [hxy ht]

omit [CompleteSpace E] in
/-- Integral admissibility is unchanged when the state curve changes only
outside the finite horizon. No pointwise derivative outside the horizon matters. -/
theorem IsIntegralAdmissiblePair.congr_state
    {prob : ContinuousOCP E U} {x_init : E} {x y : ℝ → E} {u : ℝ → U}
    (hx : IsIntegralAdmissiblePair prob x_init x u)
    (hT : 0 ≤ prob.T) (hxy : EqOn x y (Icc 0 prob.T)) :
    IsIntegralAdmissiblePair prob x_init y u := by
  have hfi : IntervalIntegrable (fun t => prob.f t (y t) (u t)) volume 0 prob.T := by
    apply (intervalIntegrable_congr ?_).mp hx.2.2.1
    intro t ht
    rw [uIoc_of_le hT] at ht
    change prob.f t (x t) (u t) = prob.f t (y t) (u t)
    rw [hxy ⟨ht.1.le, ht.2⟩]
  have hLi : IntervalIntegrable (fun t => prob.L t (y t) (u t)) volume 0 prob.T := by
    apply (intervalIntegrable_congr ?_).mp hx.2.2.2.2
    intro t ht
    rw [uIoc_of_le hT] at ht
    change prob.L t (x t) (u t) = prob.L t (y t) (u t)
    rw [hxy ⟨ht.1.le, ht.2⟩]
  refine ⟨(hxy (left_mem_Icc.mpr hT)).symm.trans hx.1, hx.2.1, hfi, ?_, hLi⟩
  intro t ht
  rw [← hxy ht, hx.2.2.2.1 t ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le ht.1] at hs
  change prob.f s (x s) (u s) = prob.f s (y s) (u s)
  rw [hxy ⟨hs.1, hs.2.trans ht.2⟩]

omit [CompleteSpace E] in
/-- The transfer keeps exactly the same integral competitor class. It does not
claim that classical optimality implies integral optimality. -/
theorem IsIntegralOptimalPair.congr_state
    {prob : ContinuousOCP E U} {x_init : E} {x y : ℝ → E} {u : ℝ → U}
    (hx : IsIntegralOptimalPair prob x_init x u)
    (hT : 0 ≤ prob.T) (hxy : EqOn x y (Icc 0 prob.T)) :
    IsIntegralOptimalPair prob x_init y u := by
  refine ⟨hx.1.congr_state hT hxy, ?_⟩
  intro z v hz
  rw [← totalCost_eq_of_eqOn prob u hT hxy]
  exact hx.2 z v hz

/-- Global extension of an integral-optimal reference which satisfies the
classical ODE only on the finite horizon. -/
theorem exists_global_optimal_reference_extension
    (prob : ContinuousOCP E U) (x_init : E) (x : ℝ → E) (u : ℝ → U)
    {B : ℝ} {K : ℝ≥0}
    (hT : 0 ≤ prob.T)
    (hLip : ∀ t, LipschitzWith K (fun z => prob.f t z (u t)))
    (hB : ∀ t, ‖prob.f t 0 (u t)‖ ≤ B)
    (hF : Continuous (fun q : ℝ × E => prob.f q.1 q.2 (u q.1)))
    (hx : ∀ t ∈ Icc 0 prob.T, HasDerivAt x (prob.f t (x t) (u t)) t)
    (hopt : IsIntegralOptimalPair prob x_init x u) :
    ∃ y : ℝ → E,
      IsIntegralCurve y (fun t z => prob.f t z (u t)) ∧
      EqOn y x (Icc 0 prob.T) ∧
      IsIntegralOptimalPair prob x_init y u := by
  obtain ⟨y, hy, _, heq⟩ := exists_global_reference_extension
    (F := fun t z => prob.f t z (u t)) hLip hB hF hx
  exact ⟨y, hy, heq, hopt.congr_state hT heq.symm⟩

omit [CompleteSpace E] in
/-- Continuity on the horizon follows from the actual integral dynamics and
integrability, including continuity at both endpoints. -/
theorem IsIntegralAdmissiblePair.continuousOn
    {prob : ContinuousOCP E U} {x_init : E} {x : ℝ → E} {u : ℝ → U}
    (hx : IsIntegralAdmissiblePair prob x_init x u) (hT : 0 ≤ prob.T) :
    ContinuousOn x (Icc 0 prob.T) := by
  have hc : ContinuousOn
      (fun t => x_init + ∫ s in 0..t, prob.f s (x s) (u s)) (Icc 0 prob.T) := by
    apply continuousOn_const.add
    simpa only [uIcc_of_le hT] using
      intervalIntegral.continuousOn_primitive_interval' hx.2.2.1 (a := 0) left_mem_uIcc
  exact hc.congr (fun t ht => hx.2.2.2.1 t ht)

/-- With a continuous nominal field, integral dynamics imply the actual
within-interval derivative equation; values outside the horizon are irrelevant. -/
theorem IsIntegralAdmissiblePair.hasDerivWithinAt
    {prob : ContinuousOCP E U} {x_init : E} {x : ℝ → E} {u : ℝ → U}
    (hx : IsIntegralAdmissiblePair prob x_init x u) (hT : 0 ≤ prob.T)
    (hF : Continuous (fun q : ℝ × E => prob.f q.1 q.2 (u q.1))) :
    ∀ t ∈ Icc 0 prob.T,
      HasDerivWithinAt x (prob.f t (x t) (u t)) (Icc 0 prob.T) t := by
  have hxc := hx.continuousOn hT
  have hfc : ContinuousOn (fun t => prob.f t (x t) (u t)) (Icc 0 prob.T) :=
    hF.comp_continuousOn (continuousOn_id.prodMk hxc)
  intro t ht
  have : Fact (t ∈ Icc 0 prob.T) := ⟨ht⟩
  have hi : IntervalIntegrable (fun s => prob.f s (x s) (u s)) volume 0 t :=
    hx.2.2.1.mono_set (by
      rw [uIcc_of_le hT, uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2)
  have hd : HasDerivWithinAt (fun t => ∫ s in 0..t, prob.f s (x s) (u s))
      (prob.f t (x t) (u t)) (Icc 0 prob.T) t :=
    intervalIntegral.integral_hasDerivWithinAt_right hi
      (hfc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t)
      (hfc t ht)
  exact (hd.const_add x_init).congr_of_mem (fun s hs => hx.2.2.2.1 s hs) ht

/-- An integral-optimal reference has a global nominal representative, without
assuming differentiability of the supplied state curve outside the horizon. -/
theorem exists_global_optimal_reference_of_integral
    (prob : ContinuousOCP E U) (x_init : E) (x : ℝ → E) (u : ℝ → U)
    {B : ℝ} {K : ℝ≥0}
    (hT : 0 ≤ prob.T)
    (hLip : ∀ t, LipschitzWith K (fun z => prob.f t z (u t)))
    (hB : ∀ t, ‖prob.f t 0 (u t)‖ ≤ B)
    (hF : Continuous (fun q : ℝ × E => prob.f q.1 q.2 (u q.1)))
    (hopt : IsIntegralOptimalPair prob x_init x u) :
    ∃ y : ℝ → E,
      IsIntegralCurve y (fun t z => prob.f t z (u t)) ∧
      EqOn y x (Icc 0 prob.T) ∧
      IsIntegralOptimalPair prob x_init y u := by
  obtain ⟨Φ, hΦ⟩ := global_existence hLip hB hF
  let y := Φ 0 x_init
  have hy : IsIntegralCurve y (fun t z => prob.f t z (u t)) := (hΦ 0 x_init).1
  have hy₀ : y 0 = x_init := (hΦ 0 x_init).2
  have hxright : ∀ t ∈ Ico 0 prob.T,
      HasDerivWithinAt x (prob.f t (x t) (u t)) (Ici t) t := by
    intro t ht
    apply (hopt.1.hasDerivWithinAt hT hF t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.2)] with s hs hsT
    exact ⟨ht.1.trans hs, le_of_lt hsT⟩
  have hbound := needle_displacement_bound_after_spike
    (x := y) (y := x) (V := fun t z => prob.f t z (u t)) (tube := fun _ => univ)
    (τ := 0) (T := prob.T) (C := 0) (ε := 0) (K := K)
    (le_refl 0) (le_refl 0) (fun t _ => (hLip t).lipschitzOnWith)
    hy.continuous.continuousOn (fun t _ => (hy t).hasDerivWithinAt)
    (by simp) (hopt.1.continuousOn hT) hxright (by simp)
    (by simp [hy₀, hopt.1.1])
  have heq : EqOn y x (Icc 0 prob.T) := by
    intro t ht
    have hnorm : ‖y t - x t‖ ≤ 0 := by simpa only [zero_mul] using hbound t ht
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hnorm)
  exact ⟨y, hy, heq, hopt.congr_state hT heq.symm⟩

section PMPTransfer

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- The actual project costate predicate is invariant under replacement of the
reference outside the horizon. -/
theorem costateEquation_congr_state
    (prob : ContinuousOCP X U) (u : ℝ → U) (p : ℝ → X) {x y : ℝ → X}
    (hxy : EqOn x y (Icc 0 prob.T)) :
    costateEquation prob.L prob.f prob.T x u p ↔
      costateEquation prob.L prob.f prob.T y u p := by
  constructor <;> intro h t ht <;> simpa only [hxy ht] using h t ht

/-- The terminal condition is invariant because the endpoint state agrees. -/
theorem transversalityCondition_congr_state
    (prob : ContinuousOCP X U) (p : ℝ → X) {x y : ℝ → X}
    (hT : 0 ≤ prob.T) (hxy : EqOn x y (Icc 0 prob.T)) :
    transversalityCondition prob.K prob.T x p ↔
      transversalityCondition prob.K prob.T y p := by
  simp only [transversalityCondition, hxy (right_mem_Icc.mpr hT)]

omit [CompleteSpace X] in
/-- The actual all-time Hamiltonian minimum predicate transfers to the
original reference, with the same costate. -/
theorem HamiltonianMinimizing_congr_state
    (prob : ContinuousOCP X U) (u : ℝ → U) (p : ℝ → X) {x y : ℝ → X}
    (hxy : EqOn x y (Icc 0 prob.T)) :
    HamiltonianMinimizing prob.L prob.f prob.controlSet prob.T x u p ↔
      HamiltonianMinimizing prob.L prob.f prob.controlSet prob.T y u p := by
  constructor <;> intro h t ht v hv <;> simpa only [hxy ht] using h t ht v hv

end PMPTransfer

end NeedleIntegralModel
