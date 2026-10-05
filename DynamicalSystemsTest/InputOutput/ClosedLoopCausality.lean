import DynamicalSystems.InputOutput.ClosedLoop
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Regression for causal feedback with unique truncated state equations

Both component gains are nonzero.  The example below uses gains `2` and `3`, so their product is
larger than one: the repaired causality theorem needs algebraic prefix uniqueness, independently
of whether a particular small-gain bound applies.
-/

open Set MeasureTheory
open scoped ENNReal

namespace ClosedLoopCausality

variable {α ι : Type*}

/-- A memoryless scalar feedback connection, allowing time-dependent coefficients. -/
def scalarLoop (a b : α → ℝ) : SetRel.closedLoop α ℝ ℝ where
  topRel := (fun u x ↦ a x * u x).graph
  botRel := (fun u x ↦ b x * u x).graph

/-- Inverting the two-by-two algebraic feedback equations. -/
noncomputable def scalarState (a b : α → ℝ) (e : α → ℝ × ℝ) (x : α) : ℝ × ℝ :=
  (((e x).1 - b x * (e x).2) / (1 + a x * b x),
    (a x * (e x).1 + (e x).2) / (1 + a x * b x))

theorem scalarState_mem (a b : α → ℝ) (hab : ∀ x, 1 + a x * b x ≠ 0)
    (e : α → ℝ × ℝ) : (e, scalarState a b e) ∈ (scalarLoop a b).inputState := by
  constructor
  · change (fun x ↦ a x * (scalarState a b e x).1) =
      (fun x ↦ (scalarState a b e x).2 - (e x).2)
    funext x
    dsimp [scalarState]
    field_simp [hab x]
    ring
  · change (fun x ↦ b x * (scalarState a b e x).2) =
      (fun x ↦ (e x).1 - (scalarState a b e x).1)
    funext x
    dsimp [scalarState]
    rw [eq_sub_iff_add_eq, ← mul_div_assoc, ← add_div, div_eq_iff (hab x)]
    ring

theorem scalarLoop_isGraph (a b : α → ℝ) (hab : ∀ x, 1 + a x * b x ≠ 0) :
    (scalarLoop a b).inputState.IsGraph := by
  intro e
  refine ⟨scalarState a b e, scalarState_mem a b hab e, ?_⟩
  intro u hu
  have h₁ : (fun x ↦ a x * (u x).1) = (fun x ↦ (u x).2 - (e x).2) := hu.1
  have h₂ : (fun x ↦ b x * (u x).2) = (fun x ↦ (e x).1 - (u x).1) := hu.2
  funext x
  apply Prod.ext
  · dsimp [scalarState]
    apply (eq_div_iff (hab x)).mpr
    linear_combination b x * (congrFun h₁ x) + congrFun h₂ x
  · dsimp [scalarState]
    apply (eq_div_iff (hab x)).mpr
    linear_combination -(congrFun h₁ x) + a x * congrFun h₂ x

/-- Component truncation is multiplication by the zero-extended coefficient. -/
theorem scalarLoop_truncate (a b : α → ℝ) (S : Set α) :
    (scalarLoop a b).truncate S = scalarLoop (S.indicator a) (S.indicator b) := by
  have hcomp (c : α → ℝ) :
      {(u, y) | ∃ z, ((S.indicator u, z) ∈ (fun v x ↦ c x * v x).graph) ∧
        y = S.indicator z} = (fun u x ↦ S.indicator c x * u x).graph := by
    ext ⟨u, y⟩
    change (∃ z, (fun x ↦ c x * S.indicator u x) = z ∧ y = S.indicator z) ↔
      (fun x ↦ S.indicator c x * u x) = y
    constructor
    · rintro ⟨z, rfl, rfl⟩
      funext x
      by_cases hx : x ∈ S <;> simp [hx]
    · intro hy
      refine ⟨fun x ↦ c x * S.indicator u x, rfl, ?_⟩
      rw [← hy]
      funext x
      by_cases hx : x ∈ S <;> simp [hx]
  change SetRel.closedLoop.mk _ _ = SetRel.closedLoop.mk _ _
  congr 1
  · exact hcomp a
  · exact hcomp b

variable [MeasurableSpace α] [PseudoMetricSpace α] {μ : Measure α} {p : ℝ≥0∞}
  {s : ι → Set α}

theorem scalarLoop_locallyLpSolvable (a b : ℝ) (hab : 1 + a * b ≠ 0) :
    (scalarLoop (fun _ : α ↦ a) (fun _ ↦ b)).LocallyLpSolvable p μ := by
  intro e he
  refine ⟨scalarState (fun _ ↦ a) (fun _ ↦ b) e,
    scalarState_mem _ _ (fun _ ↦ hab) e, ?_⟩
  obtain ⟨he₁, he₂⟩ := memLpLoc_prod_iff.mp he
  rw [memLpLoc_prod_iff]
  constructor
  · convert (he₁.sub (he₂.const_smul (c := b))).const_smul
      (c := (1 + a * b)⁻¹) using 1
    funext x
    dsimp [scalarState]
    ring
  · convert ((he₁.const_smul (c := a)).add he₂).const_smul
      (c := (1 + a * b)⁻¹) using 1
    funext x
    dsimp [scalarState]
    ring

theorem scalarLoop_uniqueTruncatedStates (a b : ℝ) (hab : 1 + a * b ≠ 0) :
    (scalarLoop (fun _ : α ↦ a) (fun _ ↦ b)).HasUniqueTruncatedStates s p μ := by
  apply SetRel.closedLoop.hasUniqueTruncatedStates_of_isGraph
  intro t
  rw [scalarLoop_truncate]
  apply scalarLoop_isGraph
  intro x
  by_cases hx : x ∈ s t
  · simpa [hx] using hab
  · simp [hx]

theorem const_mul_isCausal (a : ℝ) :
    (fun u : α → ℝ ↦ fun x ↦ a * u x).IsCausal s p μ := by
  constructor
  · intro u hu
    exact hu.const_smul (c := a)
  · intro t u _
    funext x
    by_cases hx : x ∈ s t <;> simp [hx]

/-- A concrete well-posed feedback loop with component-gain product six. -/
example (hs : ∀ t, MeasurableSet (s t)) :
    (scalarLoop (fun _ : α ↦ (2 : ℝ)) (fun _ ↦ 3)).inputState.IsCausal s p μ := by
  apply SetRel.closedLoop.isCausal_inputState
  · exact SetRel.isGraph_of_graph
  · exact SetRel.isGraph_of_graph
  · exact (Function.graph_isCausal_iff_isCausal hs).mpr (const_mul_isCausal 2)
  · exact (Function.graph_isCausal_iff_isCausal hs).mpr (const_mul_isCausal 3)
  · exact scalarLoop_isGraph _ _ (by intro; norm_num)
  · exact hs
  · exact scalarLoop_locallyLpSolvable 2 3 (by norm_num)
  · exact scalarLoop_uniqueTruncatedStates 2 3 (by norm_num)

#print axioms SetRel.closedLoop.mem_inputState_truncate
#print axioms SetRel.closedLoop.isCausal_inputState
#print axioms SetRel.closedLoop.isCausal_inputOutput_of_inputState
#print axioms SetRel.closedLoop.isCausal_inputOutput
#print axioms scalarLoop_isGraph
#print axioms scalarLoop_uniqueTruncatedStates

end ClosedLoopCausality
