import DynamicalSystems.Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
import Mathlib.Tactic.Linarith

/-!
# Hahn–Banach extraction and normality for a free terminal state

This module supplies the actual geometric Hahn–Banach step for the normal,
free-terminal-state Mayer problem.  The input consists of a convex set of first-order
endpoint variations and its disjointness from the open terminal-cost descent halfspace.
The separating covector is an **output** of `geometric_hahn_banach_open`.

Because the comparison set is the whole terminal-cost descent halfspace, the output
covector must be a positive multiple of the terminal cost differential.  The cost
coordinate therefore has a strictly positive coefficient and may be normalized to one.
No Hamiltonian inequality, costate, or nonzero multiplier is assumed.

The separation argument works in arbitrary real topological vector spaces; neither
finite dimensionality nor closedness of the variation set is needed.  A convex cone
containing zero is a special case of the hypotheses below.

The missing control-theoretic input is explicit: disjointness of the attainable
first-order variation set from strict terminal-cost descent must be proved from the
needle endpoint expansion and optimality.  It is not supplied by Hahn–Banach.
-/


open Set

section AugmentedState

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]

/-- The differential of `z + K(x)` at the reference endpoint. -/
def _root_.bolzaTerminalDifferential (DK : X →L[ℝ] ℝ) : (ℝ × X) →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ X + DK.comp (ContinuousLinearMap.snd ℝ ℝ X)

@[simp]
theorem _root_.bolzaTerminalDifferential_apply (DK : X →L[ℝ] ℝ) (y : ℝ × X) :
    _root_.bolzaTerminalDifferential DK y = y.1 + DK y.2 := rfl

/-- Free-terminal-state normality in augmented coordinates.  The extracted terminal
covector has the strictly positive cost-coordinate coefficient `α`; its normalized
form is exactly `(1, DK)`.

Disjointness is written with the scalar terminal-cost differential, not an input
covector `q` or a Hamiltonian sign hypothesis. -/
theorem exists_normal_augmented_terminal_covector
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    (DK : X →L[ℝ] ℝ) (C : Set (ℝ × X))
    (hconvex : Convex ℝ C) (hzero : (0 : ℝ × X) ∈ C)
    (hdisjoint : Disjoint {y : ℝ × X | y.1 + DK y.2 < 0} C) :
    ∃ (q : (ℝ × X) →L[ℝ] ℝ) (α : ℝ),
      q ≠ 0 ∧ 0 < α ∧ (∀ y ∈ C, 0 ≤ q y) ∧ q (1, 0) = α ∧
      α⁻¹ • q = _root_.bolzaTerminalDifferential DK := by
  exact _root_.exists_normalized_positive_multiple_separating_negative_halfspace
    (_root_.bolzaTerminalDifferential DK) (1, 0) (by simp) C hconvex hzero hdisjoint

/-- The state part of the terminal differential pulled back by an **augmented**
state-transition operator.  In a Bolza problem the augmented dynamics are `(L,f)`,
so this state covector includes the running-cost contribution. -/
def propagatedStateCovector (DK : X →L[ℝ] ℝ)
    (Φ : (ℝ × X) →L[ℝ] (ℝ × X)) : X →L[ℝ] ℝ :=
  ((_root_.bolzaTerminalDifferential DK).comp Φ).comp (ContinuousLinearMap.inr ℝ ℝ X)

/-- If the augmented transition preserves a pure change of accumulated cost, the
normalized pulled-back covector still has cost-coordinate coefficient one. -/
theorem augmented_pullback_apply
    (DK : X →L[ℝ] ℝ) (Φ : (ℝ × X) →L[ℝ] (ℝ × X))
    (hcost : Φ (1, 0) = (1, 0)) (z : ℝ) (x : X) :
    _root_.bolzaTerminalDifferential DK (Φ (z, x)) =
      z + propagatedStateCovector DK Φ x := by
  let q : (ℝ × X) →L[ℝ] ℝ := (_root_.bolzaTerminalDifferential DK).comp Φ
  have he : q (1, 0) = 1 := by
    change _root_.bolzaTerminalDifferential DK (Φ (1, 0)) = 1
    rw [hcost]
    simp
  have hsplit : (z, x) = z • (1, (0 : X)) + (0, x) := by
    ext <;> simp
  change q (z, x) = z + q (0, x)
  rw [hsplit, map_add, map_smul, he]
  simp

/-- Geometric separation implies the normal needle inequality once the augmented
propagated needle increment belongs to the first-order variation set.

This lemma does **not** construct the augmented transition, prove its differential
equation, or establish generator membership/disjointness.  Those are the remaining
control-theoretic obligations.  It does show exactly where both `ΔL` and `Δf` enter;
using the unaugmented state transition here would lose the running-cost term. -/
theorem hahnBanach_needle_inequality
    [IsTopologicalAddGroup X] [ContinuousSMul ℝ X]
    (DK : X →L[ℝ] ℝ) (C : Set (ℝ × X))
    (hconvex : Convex ℝ C) (hzero : (0 : ℝ × X) ∈ C)
    (hdisjoint : Disjoint {y : ℝ × X | y.1 + DK y.2 < 0} C)
    (Φ : (ℝ × X) →L[ℝ] (ℝ × X)) (hcost : Φ (1, 0) = (1, 0))
    (ΔL : ℝ) (Δf : X) (hgenerator : Φ (ΔL, Δf) ∈ C) :
    0 ≤ ΔL + propagatedStateCovector DK Φ Δf := by
  obtain ⟨q, α, _hqzero, hα, hnonneg, _hcoefficient, hnormalized⟩ :=
    exists_normal_augmented_terminal_covector DK C hconvex hzero hdisjoint
  have hc : 0 ≤ _root_.bolzaTerminalDifferential DK (Φ (ΔL, Δf)) := by
    rw [← hnormalized]
    simp only [smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.2 hα.le) (hnonneg _ hgenerator)
  rwa [augmented_pullback_apply DK Φ hcost ΔL Δf] at hc

end AugmentedState
