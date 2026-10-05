import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistenceLinear
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Regression witness for the two-time flow composition convention

For the IVP convention F(s,x,t), the first argument is the initial time and
the last is the evaluation time.  The cocycle is F(r,F(s,x,r),t)=F(s,x,t).
This scalar, smooth, nonautonomous ODE witnesses that the reversed composition
in the previously inspected NonautonomousFlow structure is a different requirement.
The explicit ODE now packages as a flow with the corrected convention and satisfies
the hypotheses of the proved global existence and uniqueness theorem.
-/

namespace NonautonomousFlowOrder

/-- Explicit time-dependent transition distinguishing the two cocycle orders. -/
noncomputable def transition (s x t : ℝ) : ℝ := (1 + t ^ 2) / (1 + s ^ 2) * (x - s) + t

/-- Nonautonomous vector field generating the explicit regression transition. -/
noncomputable def field (t x : ℝ) : ℝ := 2 * t / (1 + t ^ 2) * (x - t) + 1

theorem denominator_pos (t : ℝ) : 0 < 1 + t ^ 2 := by positivity

theorem denominator_ne (t : ℝ) : 1 + t ^ 2 ≠ 0 := ne_of_gt (denominator_pos t)

theorem diagonal (s x : ℝ) : transition s x s = x := by
  unfold transition
  rw [div_self (denominator_ne s)]
  ring

theorem cocycle (s r t x : ℝ) :
    transition r (transition s x r) t = transition s x t := by
  unfold transition
  field_simp [denominator_ne s, denominator_ne r]
  ring

theorem solves_ode (s x t : ℝ) :
    HasDerivAt (transition s x) (field t (transition s x t)) t := by
  have hp : HasDerivAt (fun r : ℝ => 1 + r ^ 2) (2 * t) t := by
    have hpow := ((hasDerivAt_id t).pow 2).const_add (1 : ℝ)
    change HasDerivAt (fun r : ℝ => 1 + r ^ 2) ((2 : ℝ) * t ^ 1 * 1) t at hpow
    simpa only [pow_one, mul_one] using hpow
  have h : HasDerivAt (transition s x)
      (2 * t / (1 + s ^ 2) * (x - s) + 1) t :=
    ((hp.div_const (1 + s ^ 2)).mul_const (x - s)).add (hasDerivAt_id t)
  have heq : field t (transition s x t) = 2 * t / (1 + s ^ 2) * (x - s) + 1 := by
    unfold field transition
    field_simp [denominator_ne s, denominator_ne t]
    ring
  rw [heq]
  exact h

theorem reversed_composition_fails :
    transition 0 (transition 1 0 2) 1 ≠ transition 0 0 2 := by
  norm_num [transition]

/-- The concrete time-dependent ODE packages directly in the corrected interface. -/
noncomputable def bundled : NonautonomousFlow ℝ ℝ where
  toFun := transition
  map_id := diagonal
  map_comp := cocycle

theorem bundled_solves (s x : ℝ) : IsIntegralCurve (bundled s x) field :=
  fun t ↦ solves_ode s x t

theorem bundled_restart (s r t x : ℝ) :
    bundled r (bundled s x r) t = bundled s x t :=
  bundled.map_comp s r t x

theorem bundled_reverse (s t x : ℝ) : bundled t (bundled s x t) s = x := by
  rw [bundled.map_comp, bundled.map_id]

theorem coefficient_bound (t : ℝ) : |2 * t / (1 + t ^ 2)| ≤ 1 := by
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ (denominator_pos t)).mpr
    nlinarith [sq_nonneg (t + 1)]
  · apply (div_le_iff₀ (denominator_pos t)).mpr
    nlinarith [sq_nonneg (t - 1)]

theorem field_lipschitz (t : ℝ) : LipschitzWith 1 (field t) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have heq : field t x - field t y = (2 * t / (1 + t ^ 2)) * (x - y) := by
    unfold field
    ring
  simp only [Real.dist_eq, heq, abs_mul, NNReal.coe_one, one_mul]
  exact mul_le_of_le_one_left (abs_nonneg (x - y)) (coefficient_bound t)

theorem field_zero_bound (t : ℝ) : ‖field t 0‖ ≤ 1 := by
  have heq : field t 0 = (1 - t ^ 2) / (1 + t ^ 2) := by
    unfold field
    field_simp [denominator_ne t]
    ring
  rw [heq, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · apply (le_div_iff₀ (denominator_pos t)).mpr
    nlinarith [sq_nonneg t]
  · apply (div_le_iff₀ (denominator_pos t)).mpr
    nlinarith [sq_nonneg t]

theorem field_continuous : Continuous field.uncurry := by
  unfold field Function.uncurry
  exact (((continuous_const.mul continuous_fst).div
    (continuous_const.add (continuous_fst.pow 2))
    (fun z ↦ denominator_ne z.1)).mul
    (continuous_snd.sub continuous_fst)).add continuous_const

/-- The repaired general existence theorem applies to this genuinely time-dependent field. -/
theorem existsUnique_bundled_solution :
    ∃! Φ : NonautonomousFlow ℝ ℝ, ∀ s x, IsIntegralCurve (Φ s x) field :=
  existsUnique_nonAutonomousFlow field_lipschitz field_zero_bound field_continuous

/-- Uniqueness identifies every global flow supplied by the existence theorem with the
explicit flow used by the regression. -/
theorem solution_eq_bundled {Φ : NonautonomousFlow ℝ ℝ}
    (hΦ : ∀ s x, IsIntegralCurve (Φ s x) field) : Φ = bundled :=
  unique_nonAutonomousFlow field_lipschitz hΦ bundled_solves

end NonautonomousFlowOrder
