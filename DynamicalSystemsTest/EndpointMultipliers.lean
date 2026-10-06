import DynamicalSystems.OptimalControl.ContinuousTime.EndpointMultipliers
import DynamicalSystems.OptimalControl.ContinuousTime.LinearTerminalCost
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Regression tests for genuinely abnormal endpoint multipliers

The objective `-sqrt x` on `[0,1]`, with fixed endpoint `x=0`, has its actual minimum at zero.
Every nontrivial necessary multiplier has zero cost multiplier. The regression therefore
rules out a theorem that silently divides by the cost multiplier or forces normality.
-/

open Set OptimalControl MeasureTheory
namespace EndpointMultiplierTests

/-- No positive cost multiplier can support the square-root problem at zero. -/
theorem sqrt_cost_multiplier_eq_zero
    (q : ℝ →L[ℝ] ℝ) (α : ℝ) (hα : 0 ≤ α)
    (hmin : ∀ w ∈ Icc (0 : ℝ) 1, 0 ≤ q w - α * Real.sqrt w) : α = 0 := by
  by_contra hne
  have ha : 0 < α := lt_of_le_of_ne hα (Ne.symm hne)
  let d : ℝ := |q 1| + α + 1
  have hd : 0 < d := by dsimp [d]; positivity
  let t : ℝ := α / d
  have ht : 0 < t := div_pos ha hd
  have ht1 : t < 1 := by
    apply (div_lt_one hd).2
    dsimp [d]
    linarith [abs_nonneg (q 1)]
  have htd : t * d = α := by dsimp [t]; exact div_mul_cancel₀ _ hd.ne'
  have hqbound : q 1 < d := by dsimp [d]; linarith [le_abs_self (q 1)]
  have hqt : q 1 * t < α := by nlinarith
  have hsquare : t ^ 2 ∈ Icc (0 : ℝ) 1 := ⟨sq_nonneg t, by nlinarith⟩
  have hm := hmin (t ^ 2) hsquare
  have heq : q (t ^ 2) = t ^ 2 * q 1 := by
    simpa using q.map_smul (t ^ 2) (1 : ℝ)
  rw [heq, Real.sqrt_sq ht.le] at hm
  nlinarith

/-- The supporting theorem produces a genuinely abnormal pair for actual optimality. -/
theorem exists_strictly_abnormal_sqrt_multipliers :
    ∃ q : ℝ →L[ℝ] ℝ, q ≠ 0 ∧
      ∀ w ∈ Icc (0 : ℝ) 1, 0 ≤ q w := by
  have hJ : ConvexOn ℝ (Icc (0 : ℝ) 1) (fun w ↦ -Real.sqrt w) :=
    Real.strictConcaveOn_sqrt.concaveOn.neg.subset
      (fun _ hw ↦ hw.1) (convex_Icc _ _)
  obtain ⟨q, α, hα, hne, hlag⟩ := exists_endpoint_multipliers
    (Icc (0 : ℝ) 1) (fun w ↦ -Real.sqrt w) id 0 hJ
    (by intros; rfl) ⟨le_rfl, zero_le_one⟩ (by intros; simp_all)
  have hm : ∀ w ∈ Icc (0 : ℝ) 1, 0 ≤ q w - α * Real.sqrt w := by
    intro w hw
    simpa [id_eq, sub_eq_add_neg, mul_neg] using hlag w hw
  have hz := sqrt_cost_multiplier_eq_zero q α hα hm
  refine ⟨q, hne.resolve_right (by simp [hz]), ?_⟩
  simpa [hz] using hm

/-- The same abnormal phenomenon holds for actual measurable controls on `[0,1]`,
with endpoint `integral u = 0` and actual running objective `integral (-sqrt u)`.
The existence theorem is invoked, rather than an abnormal certificate being supplied. -/
theorem exists_strictly_abnormal_integral_sqrt_multipliers :
    ∃ q : ℝ →L[ℝ] ℝ, q ≠ 0 ∧ ∀ w ∈ Icc (0 : ℝ) 1, 0 ≤ q w := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  have hvi (v : ℝ → ℝ) (hv : Measurable v) (hm : ∀ t, v t ∈ Icc (0 : ℝ) 1) :
      Integrable v μ := by
    apply (integrable_const (1 : ℝ)).mono' hv.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro t
    simpa [Real.norm_eq_abs, abs_of_nonneg ((hm t).1)] using (hm t).2
  have hLi (v : ℝ → ℝ) (hv : Measurable v) (hm : ∀ t, v t ∈ Icc (0 : ℝ) 1) :
      Integrable (fun t ↦ -Real.sqrt (v t)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (Real.continuous_sqrt.measurable.comp hv).neg.aestronglyMeasurable
    apply Filter.Eventually.of_forall
    intro t
    change ‖-Real.sqrt (v t)‖ ≤ 1
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.sqrt_le_one).2 (hm t).2
  have hJ : ConvexOn ℝ (Icc (0 : ℝ) 1) (fun w ↦ -Real.sqrt w) :=
    Real.strictConcaveOn_sqrt.concaveOn.neg.subset
      (fun _ hw ↦ hw.1) (convex_Icc _ _)
  have hop : ∀ v : ℝ → ℝ, Measurable v → (∀ t, v t ∈ Icc (0 : ℝ) 1) →
      (∫ t, v t ∂μ) = 0 → 0 ≤ ∫ t, -Real.sqrt (v t) ∂μ := by
    intro v hv hm hz
    have hae : v =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun t ↦ (hm t).1) (hvi v hv hm)).1 hz
    have heq : (fun t ↦ -Real.sqrt (v t)) =ᵐ[μ] 0 := by
      filter_upwards [hae] with t ht
      simp [ht]
    rw [integral_congr_ae heq]
    simp
  obtain ⟨q, α, hα, hne, ha⟩ := exists_ae_hamiltonian_endpoint_multipliers
    (μ := μ) (Icc (0 : ℝ) 1) (convex_Icc _ _)
    (fun _ ↦ ContinuousLinearMap.id ℝ ℝ) (fun _ w ↦ -Real.sqrt w)
    (fun _ ↦ 0) measurable_const (fun _ ↦ ⟨le_rfl, zero_le_one⟩)
    (fun v hv hm ↦ hvi v hv hm) hLi (fun _ ↦ hJ)
    (Filter.Eventually.of_forall (fun _ ↦ Real.continuous_sqrt.neg.continuousOn))
    (by simpa using hop)
  have hμ : μ ≠ 0 := by
    intro hz
    have hx := congrArg (fun ν : Measure ℝ ↦ ν Set.univ) hz
    norm_num [μ, Measure.restrict_apply, Real.volume_Icc] at hx
  let : NeZero μ := ⟨hμ⟩
  have hm : ∀ w ∈ Icc (0 : ℝ) 1, 0 ≤ q w - α * Real.sqrt w := by
    have he := ha.exists
    obtain ⟨t, ht⟩ := he
    simpa [mul_neg, sub_eq_add_neg, add_comm] using ht
  have hz := sqrt_cost_multiplier_eq_zero q α hα hm
  refine ⟨q, hne.resolve_right (by simp [hz]), ?_⟩
  simpa [hz] using hm

/-- For the scalar integrator and nonzero terminal objective `x(1)`, actual optimality
of the constant lower-box control implies finite switching without a PMP premise. -/
theorem integrator_terminal_cost_has_ae_finite_switches :
    HasAEFiniteSwitchesOn (fun _ : ℝ ↦ WithLp.toLp 2 (fun _ : Fin 1 ↦ (-1 : ℝ))) 0 1 := by
  let u : ℝ → EuclideanSpace ℝ (Fin 1) := fun _ ↦ WithLp.toLp 2 (fun _ ↦ (-1 : ℝ))
  have hu : Measurable u := measurable_const
  have hbox : ∀ t, u t ∈ unitBox (Fin 1) := by intro t i; norm_num [u]
  have hcyclic : CyclicInput (0 : ℝ →L[ℝ] ℝ) (1 : ℝ) := by
    unfold CyclicInput
    apply top_unique
    intro x _
    have h1 : (1 : ℝ) ∈ Submodule.span ℝ
        (range (fun k : Fin (Module.finrank ℝ ℝ) ↦
          (((0 : ℝ →L[ℝ] ℝ).toLinearMap) ^ (k : ℕ)) (1 : ℝ))) :=
      Submodule.subset_span ⟨⟨0, by simp⟩, by simp⟩
    simpa using Submodule.smul_mem _ x h1
  have hqid : (ContinuousLinearMap.id ℝ ℝ) ≠ 0 := by
    intro h
    have he := congrArg (fun q : ℝ →L[ℝ] ℝ ↦ q 1) h
    norm_num at he
  apply hasAEFiniteSwitchesOn_of_linear_terminal_cost_minimizing
    (0 : ℝ →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ ℝ) (fun _ : Fin 1 ↦ 1) 0 1
    (fun _ ↦ hcyclic) hqid u hu hbox
  intro v hv hmem
  have hiu := integrable_linear_terminal_response (0 : ℝ →L[ℝ] ℝ)
    (fun _ : Fin 1 ↦ (1 : ℝ)) 1 u hu (fun t _ ↦ hbox t)
  have hiv := integrable_linear_terminal_response (0 : ℝ →L[ℝ] ℝ)
    (fun _ : Fin 1 ↦ (1 : ℝ)) 1 v hv (fun t _ ↦ hmem t)
  have hm := integral_mono hiu hiv (fun t ↦ ?_)
  · simpa [linearTerminalState] using hm
  · simp only [smul_zero, NormedSpace.exp_zero, one_apply_eq_self,
      Fin.sum_univ_one, smul_eq_mul, mul_one]
    change -1 ≤ v t 0
    exact (abs_le.mp ((hmem t) 0)).1

#print axioms exists_nonzero_supporting_covector
#print axioms OptimalControl.ae_hamiltonian_minimizing_of_integral_minimizing
#print axioms OptimalControl.exists_endpoint_multipliers
#print axioms OptimalControl.exists_ae_hamiltonian_endpoint_multipliers
#print axioms sqrt_cost_multiplier_eq_zero
#print axioms exists_strictly_abnormal_sqrt_multipliers
#print axioms exists_strictly_abnormal_integral_sqrt_multipliers
#print axioms OptimalControl.hasAEFiniteSwitchesOn_of_linear_terminal_cost_minimizing
#print axioms integrator_terminal_cost_has_ae_finite_switches

end EndpointMultiplierTests
