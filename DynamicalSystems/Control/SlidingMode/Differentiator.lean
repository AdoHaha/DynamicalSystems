/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.SlidingMode.SecondOrder
public import DynamicalSystems.Stability.Homogeneity

/-! # Levant's exact differentiators

This file records the exact robust differentiators of A. Levant, in the sliding-mode
coordinates of G. Bartolini, L. Fridman, A. Pisano and E. Usai (eds.), *Modern Sliding
Mode Control Theory: New Perspectives and Applications*, LNCIS 375, Springer 2008:

* Chapter 4, A. Levant and L. Alelishvili, *Discontinuous Homogeneous Control*,
  printed pp. 80–82 (PDF pp. 96–98): the arbitrary-order real-time exact robust
  differentiator.
* Chapter 14, L. Fridman, A. Levant and J. Davila, *Observation and Identification Via
  High-Order Sliding Modes*, printed pp. 293–305 (PDF pp. 309–321).

## Order-one super-twisting differentiator

For a signal `f : ℝ → ℝ` with Lipschitz derivative, `|f''| ≤ L`, the super-twisting
differentiator estimates `(f, f')` from `f` alone.  In the differentiator state
`z = (z₀, z₁) ∈ Fin 2 → ℝ` it reads

`ż₀ = -k₁ |z₀ - f|^{1/2} sign (z₀ - f) + z₁`, `ż₁ = -k₂ sign (z₀ - f)`.

The error coordinates `e = (z₀ - f, z₁ - f')` obey the perturbed super-twisting system:
the unperturbed part (`f'' = 0`) is exactly slice S7's `superTwistingVectorField`, and a
bounded second derivative enters the second channel as `![0, -f'']`.  The Moreno–Osorio
algebraic Lyapunov certificate `Q - L • !![k₁, 1; 1, 0]` (where `Q = morenoOsorioQ` from
S7) is positive definite for an appropriate gain condition, which is the algebraic
content of the robustness of the differentiator.

## Order-two differentiator

On `Fin 3 → ℝ` the unperturbed error dynamics with weights `(3, 2, 1)` is

`ė₀ = -k₀ |e₀|^{2/3} sign e₀ + e₁`, `ė₁ = -k₁ |e₀|^{1/3} sign e₀ + e₂`,
`ė₂ = -k₂ sign e₀`,

which is homogeneous of degree `-1` with respect to `secondOrderDifferentiatorWeights`.

## Main definitions

* `superTwistingDifferentiatorField`: the order-one super-twisting differentiator.
* `differentiatorError`: the error coordinates `(z₀ - f, z₁ - f')`.
* `superTwistingDifferentiatorPerturbedErrorField`: the error field with a bounded
  second-derivative perturbation.
* `morenoOsorioPerturbationMatrix`: the Moreno–Osorio perturbation matrix `L • !![k₁,1;1,0]`.
* `secondOrderDifferentiatorWeights`: the order-two weights `(3, 2, 1)`.
* `secondOrderDifferentiatorDilation`: the associated weighted dilation.
* `order2DifferentiatorVectorField`: the order-two unperturbed error field.

## Main statements

* `superTwistingDifferentiator_error_eq_superTwistingVectorField`: the unperturbed error
  dynamics is S7's `superTwistingVectorField`.
* `superTwistingDifferentiator_error_homogeneous`: the error field is homogeneous of
  degree `-1` with respect to `secondOrderSlidingWeights`.
* `morenoOsorio_robust_posDef`: the robust Moreno–Osorio dissipation matrix is positive
  definite under the corrected gain condition.
* `order2DifferentiatorVectorField_homogeneous`: the order-two field is homogeneous of
  degree `-1` with respect to `secondOrderDifferentiatorWeights`.

## Scope

Exactness here is the continuous-time, noise-free statement with a bounded second
derivative.  No claim is made about classical differentiation through `e₀ = 0`, about
general Filippov solution existence, or about noise-corrupted exactness; those need
non-smooth analysis that is out of scope. -/

open Matrix

@[expose] public section

/-! ## Order-one super-twisting differentiator -/

/-- The **super-twisting differentiator field** estimating `(f, f')` from the signal value
`f`: in the state `z = (z₀, z₁)`,
`ż₀ = -k₁ |z₀ - f|^{1/2} sign (z₀ - f) + z₁` and `ż₁ = -k₂ sign (z₀ - f)`
(Levant, Chapter 4, printed p. 80, Eq. 10 for `p = 1`; Chapter 14, printed p. 303,
Eq. 21). -/
noncomputable def superTwistingDifferentiatorField (k₁ k₂ : ℝ) (f : ℝ) (z : Fin 2 → ℝ) :
    Fin 2 → ℝ :=
  ![-k₁ * |z 0 - f| ^ (1 / 2 : ℝ) * Real.sign (z 0 - f) + z 1,
    -k₂ * Real.sign (z 0 - f)]

/-- The differentiator **error coordinates** `e = (z₀ - f, z₁ - f')` between the
differentiator state and the signal state `(f, f')`. -/
noncomputable def differentiatorError (f f' : ℝ) (z : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![z 0 - f, z 1 - f']

/-- When the signal has zero second derivative (`f'' = 0`), the differentiator error
dynamics is exactly slice S7's `superTwistingVectorField`: subtracting the drift
`![f', 0]` from the differentiator field and reading it in the error coordinates gives
the super-twisting field. -/
theorem superTwistingDifferentiator_error_eq_superTwistingVectorField
    (k₁ k₂ : ℝ) (f f' : ℝ) (z : Fin 2 → ℝ) :
    superTwistingDifferentiatorField k₁ k₂ f z - ![f', 0] =
      superTwistingVectorField k₁ k₂ (differentiatorError f f' z) := by
  ext i
  fin_cases i <;>
    simp only [superTwistingDifferentiatorField, superTwistingVectorField, differentiatorError,
      Pi.sub_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk] <;>
    ring

/-- The unperturbed differentiator error field is homogeneous of degree `-1` with respect
to the 2-sliding weights `secondOrderSlidingWeights = ![2, 1]`.  This is a direct reuse
of slice S7's `superTwistingVectorField_homogeneous`. -/
theorem superTwistingDifferentiator_error_homogeneous (k₁ k₂ : ℝ) :
    IsHomogeneousVectorField (superTwistingVectorField k₁ k₂) secondOrderSlidingWeights (-1) :=
  superTwistingVectorField_homogeneous k₁ k₂

/-- The **perturbed** differentiator error field: the super-twisting field plus the
bounded disturbance `![0, Δ]` in the second channel, with `Δ = -f''` and `|Δ| ≤ L`. -/
noncomputable def superTwistingDifferentiatorPerturbedErrorField
    (k₁ k₂ : ℝ) (Δ : ℝ) (e : Fin 2 → ℝ) : Fin 2 → ℝ :=
  superTwistingVectorField k₁ k₂ e + ![0, Δ]

/-- The **Moreno–Osorio perturbation matrix** `L • !![k₁, 1; 1, 0]`, the loss term
dominating the cross-coupling caused by a perturbation of size `L` in the second
channel. -/
noncomputable def morenoOsorioPerturbationMatrix (k₁ L : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  L • !![k₁, 1; 1, 0]

/-- The quadratic form of the robust Moreno–Osorio matrix
`Q(k₁, k₂) - L • !![k₁, 1; 1, 0]`, in the expanded shape
`k₁ k₂ x₀² + (k₁/2)(k₁ x₀ - x₁)² - L (k₁ x₀² + 2 x₀ x₁)`. -/
theorem morenoOsorio_robust_quadratic_form (k₁ k₂ L : ℝ) (x : Fin 2 → ℝ) :
    star x ⬝ᵥ ((morenoOsorioQ k₁ k₂ - morenoOsorioPerturbationMatrix k₁ L) *ᵥ x)
      = k₁ * k₂ * x 0 ^ 2 + (k₁ / 2) * (k₁ * x 0 - x 1) ^ 2
        - L * (k₁ * x 0 ^ 2 + 2 * x 0 * x 1) := by
  simp only [star_trivial, morenoOsorioQ, morenoOsorioPerturbationMatrix, smul_eq_mul, dotProduct,
    Matrix.mulVec, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply]
  ring

/-- **Robust Moreno–Osorio certificate.** With `k₁ > 0`, `L < k₂` and the corrected gain
condition `k₁² (k₂ - 3 L) > 2 L²`, the dissipation matrix
`Q(k₁, k₂) - L • !![k₁, 1; 1, 0]` is positive definite.

The reviewer's proposed condition `2 k₁ (k₂ - L)² > L²` is *not* sufficient: the
determinant of the matrix is `k₁² (k₂ - 3 L) / 2 - L²`, so `k₂ > 3 L` is unavoidable.
The condition stated here is exactly `det > 0`, which together with the positivity of the
leading entry `k₁ (k₂ - L + k₁²/2)` (a consequence of `L < k₂`) characterises positive
definiteness of the `2 × 2` matrix. -/
theorem morenoOsorio_robust_posDef {k₁ k₂ L : ℝ} (hk₁ : 0 < k₁) (hrob : L < k₂)
    (hgain : k₁ ^ 2 * (k₂ - 3 * L) > 2 * L ^ 2) :
    (morenoOsorioQ k₁ k₂ - morenoOsorioPerturbationMatrix k₁ L).PosDef := by
  set a : ℝ := k₁ * k₂ + (k₁ / 2) * k₁ ^ 2 - L * k₁ with ha_def
  set b : ℝ := -((k₁ / 2) * k₁ + L) with hb_def
  set c : ℝ := k₁ / 2 with hc_def
  have ha : 0 < a := by
    rw [ha_def]
    nlinarith [hk₁, hrob, mul_pos hk₁ hk₁]
  have hdet : 0 < a * c - b ^ 2 := by
    have heq : a * c - b ^ 2 = (k₁ ^ 2 * (k₂ - 3 * L) - 2 * L ^ 2) / 2 := by
      rw [ha_def, hb_def, hc_def]; ring
    rw [heq]; linarith
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · rw [Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [morenoOsorioQ, morenoOsorioPerturbationMatrix, Matrix.conjTranspose,
        Matrix.transpose, smul_eq_mul]
  · intro x hx
    have hq := morenoOsorio_robust_quadratic_form k₁ k₂ L x
    simp only [star_trivial] at hq ⊢
    rw [hq]
    have hqabc : k₁ * k₂ * x 0 ^ 2 + (k₁ / 2) * (k₁ * x 0 - x 1) ^ 2
          - L * (k₁ * x 0 ^ 2 + 2 * x 0 * x 1)
        = a * x 0 ^ 2 + 2 * b * (x 0 * x 1) + c * x 1 ^ 2 := by
      rw [ha_def, hb_def, hc_def]; ring
    rw [hqabc]
    have hkey : a * (a * x 0 ^ 2 + 2 * b * (x 0 * x 1) + c * x 1 ^ 2)
        = (a * x 0 + b * x 1) ^ 2 + (a * c - b ^ 2) * x 1 ^ 2 := by ring
    have hpos : 0 < a * (a * x 0 ^ 2 + 2 * b * (x 0 * x 1) + c * x 1 ^ 2) := by
      rw [hkey]
      rcases eq_or_ne (x 1) 0 with h1 | h1
      · have h0 : x 0 ≠ 0 := by
          intro h0
          exact hx (by funext i; fin_cases i <;> simp [h0, h1])
        have hzero : (a * x 0 + b * x 1) ^ 2 + (a * c - b ^ 2) * x 1 ^ 2 = (a * x 0) ^ 2 := by
          rw [h1]; ring
        rw [hzero]
        exact sq_pos_of_ne_zero (mul_ne_zero (ne_of_gt ha) h0)
      · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (mul_pos hdet (sq_pos_of_ne_zero h1))
    exact pos_of_mul_pos_right hpos ha.le

/-! ## Order-two exact differentiator -/

/-- The order-two differentiator homogeneity weights `(3, 2, 1)`: the components
`(z₀, z₁, z₂)` estimating `(f, f', f'')` scale as `λ ^ 3`, `λ ^ 2` and `λ ^ 1`. -/
def secondOrderDifferentiatorWeights : Fin 3 → ℝ := ![3, 2, 1]

/-- The order-two differentiator weighted dilation `d_λ (z₀, z₁, z₂) =
(λ³ z₀, λ² z₁, λ z₂)` of slice S4 with the weights `secondOrderDifferentiatorWeights`. -/
noncomputable def secondOrderDifferentiatorDilation (l : ℝ) : (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  weightedDilation secondOrderDifferentiatorWeights l

/-- Evaluation of the order-two differentiator dilation in the first coordinate:
`(d_λ z) 0 = λ ^ 3 * z 0`. -/
private theorem weightedDilation_diffWeights_zero (l : ℝ) (x : Fin 3 → ℝ) :
    weightedDilation secondOrderDifferentiatorWeights l x 0 = l ^ (3 : ℝ) * x 0 := by
  simp only [weightedDilation, secondOrderDifferentiatorWeights]
  norm_num

/-- Evaluation of the order-two differentiator dilation in the second coordinate:
`(d_λ z) 1 = λ ^ 2 * z 1`. -/
private theorem weightedDilation_diffWeights_one (l : ℝ) (x : Fin 3 → ℝ) :
    weightedDilation secondOrderDifferentiatorWeights l x 1 = l ^ (2 : ℝ) * x 1 := by
  simp only [weightedDilation, secondOrderDifferentiatorWeights]
  norm_num

/-- Evaluation of the order-two differentiator dilation in the third coordinate:
`(d_λ z) 2 = λ * z 2`. -/
private theorem weightedDilation_diffWeights_two (l : ℝ) (x : Fin 3 → ℝ) :
    weightedDilation secondOrderDifferentiatorWeights l x 2 = l ^ (1 : ℝ) * x 2 := by
  simp only [weightedDilation, secondOrderDifferentiatorWeights]
  norm_num

/-- `|λ³ a|^{2/3} = λ² |a|^{2/3}` for `λ > 0`. -/
private theorem abs_rpow_two_thirds_mul_cube {l a : ℝ} (hl : 0 < l) :
    |l ^ (3 : ℝ) * a| ^ (2 / 3 : ℝ) = l ^ (2 : ℝ) * |a| ^ (2 / 3 : ℝ) := by
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hl.le 3),
    Real.mul_rpow (Real.rpow_nonneg hl.le 3) (abs_nonneg a),
    show (l ^ (3 : ℝ)) ^ (2 / 3 : ℝ) = l ^ (2 : ℝ) by
      rw [← Real.rpow_mul hl.le]
      norm_num]

/-- `|λ³ a|^{1/3} = λ |a|^{1/3}` for `λ > 0`. -/
private theorem abs_rpow_one_third_mul_cube {l a : ℝ} (hl : 0 < l) :
    |l ^ (3 : ℝ) * a| ^ (1 / 3 : ℝ) = l ^ (1 : ℝ) * |a| ^ (1 / 3 : ℝ) := by
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hl.le 3),
    Real.mul_rpow (Real.rpow_nonneg hl.le 3) (abs_nonneg a),
    show (l ^ (3 : ℝ)) ^ (1 / 3 : ℝ) = l ^ (1 : ℝ) by
      rw [← Real.rpow_mul hl.le]
      norm_num]

/-- `λ ^ (-1) * (λ³ * a) = λ² * a` for `λ > 0`. -/
private theorem rpow_neg_one_mul_cube {l a : ℝ} (hl : 0 < l) :
    l ^ (-1 : ℝ) * (l ^ (3 : ℝ) * a) = l ^ (2 : ℝ) * a := by
  rw [← mul_assoc, show l ^ (-1 : ℝ) * l ^ (3 : ℝ) = l ^ (2 : ℝ) by
    rw [← Real.rpow_add hl]
    norm_num]

/-- `λ ^ (-1) * (λ² * a) = λ * a` for `λ > 0`. -/
private theorem rpow_neg_one_mul_sq {l a : ℝ} (hl : 0 < l) :
    l ^ (-1 : ℝ) * (l ^ (2 : ℝ) * a) = l ^ (1 : ℝ) * a := by
  rw [← mul_assoc, show l ^ (-1 : ℝ) * l ^ (2 : ℝ) = l ^ (1 : ℝ) by
    rw [← Real.rpow_add hl]
    norm_num]

/-- `λ ^ (-1) * (λ * a) = a` for `λ > 0`. -/
private theorem rpow_neg_one_mul_one {l a : ℝ} (hl : 0 < l) :
    l ^ (-1 : ℝ) * (l ^ (1 : ℝ) * a) = a := by
  rw [← mul_assoc, show l ^ (-1 : ℝ) * l ^ (1 : ℝ) = 1 by
    rw [← Real.rpow_add hl]
    norm_num,
    one_mul]

/-- The **order-two exact differentiator** unperturbed error field on `Fin 3 → ℝ`:
`ė₀ = -k₀ |e₀|^{2/3} sign e₀ + e₁`, `ė₁ = -k₁ |e₀|^{1/3} sign e₀ + e₂`,
`ė₂ = -k₂ sign e₀` (Levant, Chapter 4, printed p. 80, Eq. 10 for `p = 2`; Chapter 14,
printed p. 302, Eq. 19 for `r = 3`). -/
noncomputable def order2DifferentiatorVectorField (k₀ k₁ k₂ : ℝ) (e : Fin 3 → ℝ) :
    Fin 3 → ℝ :=
  ![-k₀ * |e 0| ^ (2 / 3 : ℝ) * Real.sign (e 0) + e 1,
    -k₁ * |e 0| ^ (1 / 3 : ℝ) * Real.sign (e 0) + e 2,
    -k₂ * Real.sign (e 0)]

/-- The order-two differentiator error field is homogeneous of degree `-1` with respect to
the weights `secondOrderDifferentiatorWeights = ![3, 2, 1]`: under
`d_λ (z₀, z₁, z₂) = (λ³ z₀, λ² z₁, λ z₂)` every component scales by `λ ^ (r i - 1)`. -/
theorem order2DifferentiatorVectorField_homogeneous (k₀ k₁ k₂ : ℝ) :
    IsHomogeneousVectorField (order2DifferentiatorVectorField k₀ k₁ k₂)
      secondOrderDifferentiatorWeights (-1) := by
  intro l hl x
  funext i
  fin_cases i
  · simp only [order2DifferentiatorVectorField, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Fin.reduceFinMk,
      weightedDilation_diffWeights_zero,
      weightedDilation_diffWeights_one, abs_rpow_two_thirds_mul_cube hl,
      sign_mul_of_pos_left (Real.rpow_pos_of_pos hl 3), rpow_neg_one_mul_cube hl]
    ring
  · simp only [order2DifferentiatorVectorField, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk,
      weightedDilation_diffWeights_zero, weightedDilation_diffWeights_one,
      weightedDilation_diffWeights_two, abs_rpow_one_third_mul_cube hl,
      sign_mul_of_pos_left (Real.rpow_pos_of_pos hl 3), rpow_neg_one_mul_sq hl]
    ring
  · simp only [order2DifferentiatorVectorField, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Fin.reduceFinMk,
      weightedDilation_diffWeights_zero, weightedDilation_diffWeights_two,
      sign_mul_of_pos_left (Real.rpow_pos_of_pos hl 3), rpow_neg_one_mul_one hl]
