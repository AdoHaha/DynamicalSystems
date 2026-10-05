import DynamicalSystems.OptimalControl.ContinuousTime.NeedleSeparation
import DynamicalSystems.Mathlib.Analysis.ODE.StateTransitionExistence

/-!
# The normal Bolza adjoint from an augmented state transition

The augmented linearization of `(L,f)` is `δz' = ℓ(t) δx`,
`δx' = A(t) δx`. The backward equation first proves that the state transition
preserves a pure accumulated-cost change. Pulling back `(1, DK)` then gives a
state covector with the full inhomogeneous adjoint equation, including `ℓ`.
-/


open Set
open scoped Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The derivative in augmented state of dynamics `(L,f)` that do not depend on
the accumulated-cost coordinate. -/
def augmentedLinearCoefficient (ℓ : X →L[ℝ] ℝ) (A : X →L[ℝ] X) :
    (ℝ × X) →L[ℝ] (ℝ × X) :=
  (ℓ.comp (ContinuousLinearMap.snd ℝ ℝ X)).prod
    (A.comp (ContinuousLinearMap.snd ℝ ℝ X))

@[simp]
theorem augmentedLinearCoefficient_apply (ℓ : X →L[ℝ] ℝ) (A : X →L[ℝ] X)
    (y : ℝ × X) : augmentedLinearCoefficient ℓ A y = (ℓ y.2, A y.2) := rfl

theorem augmentedLinearCoefficient_cost_zero (ℓ : X →L[ℝ] ℝ) (A : X →L[ℝ] X) :
    augmentedLinearCoefficient ℓ A (1, 0) = 0 := by
  ext <;> simp

/-- Pure cost-coordinate preservation follows from the backward propagator law,
because the augmented linear coefficient annihilates `(1,0)`. -/
theorem augmentedTransition_preserves_cost
    (ℓ : ℝ → X →L[ℝ] ℝ) (A : ℝ → X →L[ℝ] X)
    (Φ : ℝ → ℝ → (ℝ × X) →L[ℝ] (ℝ × X))
    (hΦ : IsStateTransition (fun t => augmentedLinearCoefficient (ℓ t) (A t)) Φ)
    (T t : ℝ) : Φ T t (1, 0) = (1, 0) := by
  have hd : ∀ s, HasDerivAt (fun r => Φ T r (1, 0)) 0 s := by
    intro s
    simpa only [neg_apply, ContinuousLinearMap.comp_apply,
      augmentedLinearCoefficient_cost_zero, map_zero, neg_zero, add_zero] using
      (hΦ.backward T s).clm_apply (hasDerivAt_const s (1, (0 : X)))
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t T
  simpa [hΦ.diag T] using hc

/-- The state part of the pulled-back terminal covector solves the inhomogeneous
adjoint equation. The running-cost derivative `ℓ` is derived from cost augmentation,
not inserted into an unrelated homogeneous pullback. -/
theorem augmentedTransition_costate_derivative
    (ℓ : ℝ → X →L[ℝ] ℝ) (A : ℝ → X →L[ℝ] X)
    (Φ : ℝ → ℝ → (ℝ × X) →L[ℝ] (ℝ × X))
    (hΦ : IsStateTransition (fun t => augmentedLinearCoefficient (ℓ t) (A t)) Φ)
    (DK : X →L[ℝ] ℝ) (T t : ℝ) :
    HasDerivAt (fun s => propagatedStateCovector DK (Φ T s))
      (-(ℓ t + (propagatedStateCovector DK (Φ T t)).comp (A t))) t := by
  have hcost := augmentedTransition_preserves_cost ℓ A Φ hΦ T t
  have hd := (hΦ.terminal_covector_derivative (_root_.bolzaTerminalDifferential DK) T t).clm_comp
    (hasDerivAt_const t (ContinuousLinearMap.inr ℝ ℝ X))
  convert hd using 1
  · rfl
  · ext x
    simp only [neg_apply, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply, augmentedLinearCoefficient_apply,
      zero_apply, map_zero, add_zero]
    exact congrArg Neg.neg
      (augmented_pullback_apply DK (Φ T t) hcost (ℓ t x) (A t x)).symm

/-- At the final time the state part is exactly the terminal penalty differential. -/
theorem augmentedTransition_costate_terminal
    (ℓ : ℝ → X →L[ℝ] ℝ) (A : ℝ → X →L[ℝ] X)
    (Φ : ℝ → ℝ → (ℝ × X) →L[ℝ] (ℝ × X))
    (hΦ : IsStateTransition (fun t => augmentedLinearCoefficient (ℓ t) (A t)) Φ)
    (DK : X →L[ℝ] ℝ) (T : ℝ) :
    propagatedStateCovector DK (Φ T T) = DK := by
  ext x
  simp [propagatedStateCovector, hΦ.diag T]

/-- Local form of the pullback derivative, using only the backward equation at
the time in question and cost-coordinate preservation there. -/
theorem augmented_costate_derivative_of_backward
    (ℓ : X →L[ℝ] ℝ) (A : X →L[ℝ] X)
    (Φ : ℝ → (ℝ × X) →L[ℝ] (ℝ × X))
    (DK : X →L[ℝ] ℝ) (t : ℝ)
    (hback : HasDerivAt Φ (-(Φ t).comp (augmentedLinearCoefficient ℓ A)) t)
    (hcost : Φ t (1, 0) = (1, 0)) :
    HasDerivAt (fun s => propagatedStateCovector DK (Φ s))
      (-(ℓ + (propagatedStateCovector DK (Φ t)).comp A)) t := by
  have hd := ((hasDerivAt_const t (_root_.bolzaTerminalDifferential DK)).clm_comp hback).clm_comp
    (hasDerivAt_const t (ContinuousLinearMap.inr ℝ ℝ X))
  convert hd using 1
  · rfl
  · ext x
    simp only [neg_apply, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply, augmentedLinearCoefficient_apply,
      zero_apply, map_zero, add_zero, zero_add, map_neg]
    exact congrArg Neg.neg
      (augmented_pullback_apply DK (Φ t) hcost (ℓ x) (A x)).symm

/-- Cost-coordinate preservation on a compact interval follows from the backward
law on that interval. No uniqueness theorem or global coefficient extension is
an extra premise. -/
theorem augmentedTransitionOn_preserves_cost
    (ℓ : ℝ → X →L[ℝ] ℝ) (A : ℝ → X →L[ℝ] X)
    (Φ : ℝ → ℝ → (ℝ × X) →L[ℝ] (ℝ × X))
    (a b : ℝ)
    (hdiag : ∀ s, Φ s s = ContinuousLinearMap.id ℝ (ℝ × X))
    (hback : ∀ T s, s ∈ Icc a b → HasDerivAt (fun r => Φ T r)
      (-((Φ T s).comp (augmentedLinearCoefficient (ℓ s) (A s)))) s)
    (T t : ℝ) (hT : T ∈ Icc a b) (ht : t ∈ Icc a b) :
    Φ T t (1, 0) = (1, 0) := by
  have hd : ∀ s ∈ Icc a b, HasDerivAt (fun r => Φ T r (1, 0)) 0 s := by
    intro s hs
    simpa only [neg_apply, ContinuousLinearMap.comp_apply,
      augmentedLinearCoefficient_cost_zero, map_zero, neg_zero, add_zero] using
      (hback T s hs).clm_apply (hasDerivAt_const s (1, (0 : X)))
  have hnorm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hd s hs).hasDerivWithinAt) (fun s hs => norm_zero.le)
    (convex_Icc a b) hT ht
  have heq : Φ T t (1, 0) - Φ T T (1, 0) = 0 :=
    norm_eq_zero.mp (le_antisymm (by simpa only [zero_mul] using hnorm) (norm_nonneg _))
  simpa [hdiag T] using sub_eq_zero.mp heq

/-- The augmented coefficient depends continuously on the running-cost and
state linearizations. -/
theorem continuousOn_augmentedLinearCoefficient
    (ℓ : ℝ → X →L[ℝ] ℝ) (A : ℝ → X →L[ℝ] X) (s : Set ℝ)
    (hℓ : ContinuousOn ℓ s) (hA : ContinuousOn A s) :
    ContinuousOn (fun t => augmentedLinearCoefficient (ℓ t) (A t)) s := by
  exact (ContinuousLinearMap.prodL ℝ).continuous.comp_continuousOn
    ((hℓ.clm_comp continuousOn_const).prodMk (hA.clm_comp continuousOn_const))

/-- Continuous coefficient data on a compact interval produce the actual
augmented state transition and its full normal adjoint. The forward/backward
laws, cost-coordinate preservation, adjoint equation, and terminal value are
all conclusions. -/
theorem exists_augmented_stateTransitionOn_Icc [CompleteSpace X] [FiniteDimensional ℝ X]
    (ℓ : ℝ → X →L[ℝ] ℝ) (A : ℝ → X →L[ℝ] X)
    (a b : ℝ) (hab : a ≤ b)
    (hℓ : ContinuousOn ℓ (Icc a b)) (hA : ContinuousOn A (Icc a b))
    (DK : X →L[ℝ] ℝ) :
    ∃ Φ : ℝ → ℝ → (ℝ × X) →L[ℝ] (ℝ × X),
      (∀ s, Φ s s = ContinuousLinearMap.id ℝ (ℝ × X)) ∧
      (∀ s t, t ∈ Icc a b → HasDerivAt (fun r => Φ r s)
        ((augmentedLinearCoefficient (ℓ t) (A t)).comp (Φ t s)) t) ∧
      (∀ T s, s ∈ Icc a b → HasDerivAt (fun r => Φ T r)
        (-((Φ T s).comp (augmentedLinearCoefficient (ℓ s) (A s)))) s) ∧
      (∀ t r s, (Φ t r).comp (Φ r s) = Φ t s) ∧
      (∀ t ∈ Icc a b, Φ b t (1, 0) = (1, 0)) ∧
      (∀ t ∈ Icc a b, HasDerivAt (fun s => propagatedStateCovector DK (Φ b s))
        (-(ℓ t + (propagatedStateCovector DK (Φ b t)).comp (A t))) t) ∧
      propagatedStateCovector DK (Φ b b) = DK := by
  obtain ⟨Φ, hdiag, hforward, hback, hcomp⟩ :=
    exists_stateTransitionOn_Icc hab
      (continuousOn_augmentedLinearCoefficient ℓ A (Icc a b) hℓ hA)
  have hcost : ∀ t ∈ Icc a b, Φ b t (1, 0) = (1, 0) := by
    intro t ht
    exact augmentedTransitionOn_preserves_cost ℓ A Φ a b hdiag hback b t ⟨hab, le_rfl⟩ ht
  refine ⟨Φ, hdiag, hforward, hback, hcomp, hcost, ?_, ?_⟩
  · intro t ht
    exact augmented_costate_derivative_of_backward (ℓ t) (A t) (Φ b) DK t
      (hback b t ht) (hcost t ht)
  · ext x
    simp [propagatedStateCovector, hdiag b]

