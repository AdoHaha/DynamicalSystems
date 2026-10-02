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

## Arbitrary-order differentiator

On `Fin (p + 1) → ℝ` the unperturbed error dynamics with the Levant weights
`r i = p + 1 - i` is the direct fractional form
`ė_i = -k_i |e₀|^{(p-i)/(p+1)} sign e₀ + e_{i+1}` for `i < p` and
`ė_p = -k_p sign e₀`, which is homogeneous of degree `-1` with respect to the Levant
weighted dilation.  This is the degree under which Levant's finite-time theorem applies.

## Main definitions

* `superTwistingDifferentiatorField`: the order-one super-twisting differentiator.
* `differentiatorError`: the error coordinates `(z₀ - f, z₁ - f')`.
* `superTwistingDifferentiatorPerturbedErrorField`: the error field with a bounded
  second-derivative perturbation.
* `morenoOsorioPerturbationMatrix`: the Moreno–Osorio perturbation matrix `L • !![k₁,1;1,0]`.
* `secondOrderDifferentiatorWeights`: the order-two weights `(3, 2, 1)`.
* `secondOrderDifferentiatorDilation`: the associated weighted dilation.
* `order2DifferentiatorVectorField`: the order-two unperturbed error field.
* `levantDifferentiatorWeights`: the arbitrary-order Levant weights `p + 1 - i`.
* `levantDifferentiatorVectorField`: the arbitrary-order exact differentiator field.

## Main statements

* `superTwistingDifferentiator_error_eq_superTwistingVectorField`: the unperturbed error
  dynamics is S7's `superTwistingVectorField`.
* `superTwistingDifferentiator_error_homogeneous`: the error field is homogeneous of
  degree `-1` with respect to `secondOrderSlidingWeights`.
* `morenoOsorio_robust_posDef`: the robust Moreno–Osorio dissipation matrix is positive
  definite under the corrected gain condition.
* `order2DifferentiatorVectorField_homogeneous`: the order-two field is homogeneous of
  degree `-1` with respect to `secondOrderDifferentiatorWeights`.
* `levantDifferentiatorVectorField_homogeneous`: the arbitrary-order field is homogeneous
  of degree `-1` with respect to `levantDifferentiatorWeights`.
* `levantDifferentiator_finiteTime_of_contractive`: Levant's arbitrary-order finite-time
  bridge via `eventually_eq_zero_of_isHomogeneousFlow_of_contractive`.

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
theorem secondOrderDifferentiatorDilation_apply_zero (l : ℝ) (x : Fin 3 → ℝ) :
    secondOrderDifferentiatorDilation l x 0 = l ^ (3 : ℝ) * x 0 := by
  simp only [secondOrderDifferentiatorDilation, weightedDilation, secondOrderDifferentiatorWeights]
  norm_num

/-- Evaluation of the order-two differentiator dilation in the second coordinate:
`(d_λ z) 1 = λ ^ 2 * z 1`. -/
theorem secondOrderDifferentiatorDilation_apply_one (l : ℝ) (x : Fin 3 → ℝ) :
    secondOrderDifferentiatorDilation l x 1 = l ^ (2 : ℝ) * x 1 := by
  simp only [secondOrderDifferentiatorDilation, weightedDilation, secondOrderDifferentiatorWeights]
  norm_num

/-- Evaluation of the order-two differentiator dilation in the third coordinate:
`(d_λ z) 2 = λ * z 2`. -/
theorem secondOrderDifferentiatorDilation_apply_two (l : ℝ) (x : Fin 3 → ℝ) :
    secondOrderDifferentiatorDilation l x 2 = l * x 2 := by
  simp only [secondOrderDifferentiatorDilation, weightedDilation, secondOrderDifferentiatorWeights]
  norm_num

/-- The weighted dilation with the order-two differentiator weights is the order-two
differentiator dilation. -/
private theorem weightedDilation_secondOrderDifferentiatorWeights_eq (l : ℝ) (x : Fin 3 → ℝ) :
    weightedDilation secondOrderDifferentiatorWeights l x = secondOrderDifferentiatorDilation l x :=
  rfl

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
    |l ^ (3 : ℝ) * a| ^ (1 / 3 : ℝ) = l * |a| ^ (1 / 3 : ℝ) := by
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hl.le 3),
    Real.mul_rpow (Real.rpow_nonneg hl.le 3) (abs_nonneg a),
    show (l ^ (3 : ℝ)) ^ (1 / 3 : ℝ) = l ^ (1 : ℝ) by
      rw [← Real.rpow_mul hl.le]
      norm_num,
    Real.rpow_one]

/-- `λ ^ (-1) * (λ³ * a) = λ² * a` for `λ > 0`. -/
private theorem rpow_neg_one_mul_cube {l a : ℝ} (hl : 0 < l) :
    l ^ (-1 : ℝ) * (l ^ (3 : ℝ) * a) = l ^ (2 : ℝ) * a := by
  rw [← mul_assoc, show l ^ (-1 : ℝ) * l ^ (3 : ℝ) = l ^ (2 : ℝ) by
    rw [← Real.rpow_add hl]
    norm_num]

/-- `λ ^ (-1) * (λ² * a) = λ * a` for `λ > 0`. -/
private theorem rpow_neg_one_mul_sq {l a : ℝ} (hl : 0 < l) :
    l ^ (-1 : ℝ) * (l ^ (2 : ℝ) * a) = l * a := by
  rw [← mul_assoc, show l ^ (-1 : ℝ) * l ^ (2 : ℝ) = l ^ (1 : ℝ) by
    rw [← Real.rpow_add hl]
    norm_num, Real.rpow_one]

/-- `λ ^ (-1) * (λ * a) = a` for `λ > 0`. -/
private theorem rpow_neg_one_mul_one {l a : ℝ} (hl : 0 < l) :
    l ^ (-1 : ℝ) * (l * a) = a := by
  rw [Real.rpow_neg_one, inv_mul_cancel_left₀ (ne_of_gt hl)]

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
  simp only [weightedDilation_secondOrderDifferentiatorWeights_eq]
  funext i
  fin_cases i
  · simp only [order2DifferentiatorVectorField, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Fin.reduceFinMk,
      secondOrderDifferentiatorDilation_apply_zero,
      secondOrderDifferentiatorDilation_apply_one, abs_rpow_two_thirds_mul_cube hl,
      sign_mul_of_pos_left (Real.rpow_pos_of_pos hl 3), rpow_neg_one_mul_cube hl]
    ring
  · simp only [order2DifferentiatorVectorField, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.reduceFinMk,
      secondOrderDifferentiatorDilation_apply_zero,
      secondOrderDifferentiatorDilation_apply_one,
      secondOrderDifferentiatorDilation_apply_two, abs_rpow_one_third_mul_cube hl,
      sign_mul_of_pos_left (Real.rpow_pos_of_pos hl 3), rpow_neg_one_mul_sq hl]
    ring
  · simp only [order2DifferentiatorVectorField, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Fin.reduceFinMk,
      secondOrderDifferentiatorDilation_apply_zero,
      secondOrderDifferentiatorDilation_apply_two,
      sign_mul_of_pos_left (Real.rpow_pos_of_pos hl 3), rpow_neg_one_mul_one hl]

/-! ## Arbitrary-order Levant differentiator -/

/-- The **Levant differentiator weights** `r i = p + 1 - i` for the `(p + 1)`-dimensional
state `(e₀, …, e_p)` of an estimate of `(f, f', …, f^{(p)})`.  The weight of the `i`-th
error component is `p + 1 - i` (so component `i` scales as `λ ^ (p + 1 - i)`), which is
the value that makes the arbitrary-order differentiator field homogeneous of degree `-1`.
The book's printed `p - i` (Levant, Chapter 4, printed p. 80) is a typo. -/
def levantDifferentiatorWeights (p : ℕ) : Fin (p + 1) → ℝ :=
  fun i ↦ (p + 1 : ℝ) - (i : ℝ)

/-- The **arbitrary-order Levant exact differentiator** in direct fractional form on the
error coordinates `x = (e₀, …, e_p)`:
`f_i(x) = -k_i |x₀|^{(p-i)/(p+1)} sign x₀ + x_{i+1}` for `i < p`, while the last component
is `f_p(x) = -k_p sign x₀` (the `i = p` case of the same formula, since `|x₀|^0 = 1`).
This is Levant, Chapter 4, printed p. 80, Eq. 10 with `p` derivatives and the fractional
exponents `(p - i)/(p + 1)`; see Chapter 14, printed p. 302 for the observation use. -/
noncomputable def levantDifferentiatorVectorField (p : ℕ) (k : Fin (p + 1) → ℝ)
    (x : Fin (p + 1) → ℝ) : Fin (p + 1) → ℝ :=
  fun i ↦ -k i * |x 0| ^ (((p : ℝ) - (i : ℝ)) / ((p : ℝ) + 1)) * Real.sign (x 0) +
    if h : (i : ℕ) < p then x ⟨(i : ℕ) + 1, Nat.succ_lt_succ h⟩ else 0

/-- The `i`-th weight of `levantDifferentiatorWeights p` is `p + 1 - i`. -/
theorem levantDifferentiatorWeights_apply (p : ℕ) (i : Fin (p + 1)) :
    levantDifferentiatorWeights p i = (p + 1 : ℝ) - (i : ℝ) := rfl

/-- The order-two differentiator weights `(3, 2, 1)` are the Levant weights for `p = 2`. -/
theorem secondOrderDifferentiatorWeights_eq_levantDifferentiatorWeights :
    secondOrderDifferentiatorWeights = levantDifferentiatorWeights 2 := by
  funext i
  fin_cases i <;>
    simp only [secondOrderDifferentiatorWeights, levantDifferentiatorWeights] <;>
    norm_num

/-- Componentwise evaluation of the weighted dilation with the Levant weights:
`(d_λ x) i = λ ^ (p + 1 - i) * x i`. -/
theorem levantDifferentiatorDilation_apply (p : ℕ) (l : ℝ) (x : Fin (p + 1) → ℝ)
    (i : Fin (p + 1)) :
    weightedDilation (levantDifferentiatorWeights p) l x i =
      l ^ ((p + 1 : ℝ) - (i : ℝ)) * x i := rfl

/-- The successor coordinate of the Levant dilation: for `i < p`,
`(d_λ x) (i+1) = λ ^ (p - i) * x (i+1)`. -/
theorem levantDifferentiatorDilation_succ (p : ℕ) (l : ℝ) (x : Fin (p + 1) → ℝ)
    (i : Fin (p + 1)) (h : (i : ℕ) < p) :
    weightedDilation (levantDifferentiatorWeights p) l x ⟨(i : ℕ) + 1, Nat.succ_lt_succ h⟩ =
      l ^ ((p : ℝ) - (i : ℝ)) * x ⟨(i : ℕ) + 1, Nat.succ_lt_succ h⟩ := by
  rw [levantDifferentiatorDilation_apply]
  have he : ((p + 1 : ℝ) -
      (↑(⟨(i : ℕ) + 1, Nat.succ_lt_succ h⟩ : Fin (p + 1)) : ℝ)) =
      (p : ℝ) - (i : ℝ) := by
    push_cast
    ring
  rw [he]

/-- The fractional power of the Levant dilation: for `l > 0` and `i : Fin (p + 1)`,
`|l ^ (p + 1) * a| ^ ((p - i)/(p + 1)) = l ^ (p - i) * |a| ^ ((p - i)/(p + 1))`. -/
private theorem abs_rpow_levantDifferentiator (p : ℕ) {l : ℝ} (hl : 0 < l) (a : ℝ)
    (i : Fin (p + 1)) :
    |l ^ (p + 1 : ℝ) * a| ^ (((p : ℝ) - (i : ℝ)) / ((p : ℝ) + 1)) =
      l ^ ((p : ℝ) - (i : ℝ)) * |a| ^ (((p : ℝ) - (i : ℝ)) / ((p : ℝ) + 1)) := by
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hl.le _),
    Real.mul_rpow (Real.rpow_nonneg hl.le _) (abs_nonneg a)]
  congr 1
  rw [← Real.rpow_mul hl.le]
  congr 1
  field_simp

/-- Componentwise scaling of the Levant differentiator field under its dilation: for
`l > 0`, `d_λ` maps component `i` to `λ ^ (p - i) = λ ^ (r i - 1)` times component `i`. -/
private theorem levantDifferentiatorVectorField_scales (p : ℕ) (k : Fin (p + 1) → ℝ)
    {l : ℝ} (hl : 0 < l) (x : Fin (p + 1) → ℝ) (i : Fin (p + 1)) :
    levantDifferentiatorVectorField p k
        (weightedDilation (levantDifferentiatorWeights p) l x) i =
      l ^ ((p : ℝ) - (i : ℝ)) * levantDifferentiatorVectorField p k x i := by
  have h0 : weightedDilation (levantDifferentiatorWeights p) l x 0 = l ^ (p + 1 : ℝ) * x 0 := by
    rw [levantDifferentiatorDilation_apply]
    congr 1
    simp
  by_cases h : (i : ℕ) < p
  · simp only [levantDifferentiatorVectorField]
    rw [dite_eq_left h, dite_eq_left h]
    rw [h0, abs_rpow_levantDifferentiator p hl (x 0) i,
      sign_mul_of_pos_left (Real.rpow_pos_of_pos hl _),
      levantDifferentiatorDilation_succ p l x i h]
    ring
  · simp only [levantDifferentiatorVectorField]
    rw [dite_eq_right h, dite_eq_right h]
    rw [h0, abs_rpow_levantDifferentiator p hl (x 0) i,
      sign_mul_of_pos_left (Real.rpow_pos_of_pos hl _)]
    ring

/-- The **arbitrary-order Levant differentiator field is homogeneous of degree `-1`** with
respect to the weights `levantDifferentiatorWeights p = (p + 1, p, …, 1)`: under
`d_λ (e₀, …, e_p) = (λ^{p+1} e₀, …, λ e_p)` every component scales by `λ ^ (r i - 1)`.
This is the degree-`-1` condition under which Levant's Theorem 1/3 applies. -/
theorem levantDifferentiatorVectorField_homogeneous (p : ℕ) (k : Fin (p + 1) → ℝ) :
    IsHomogeneousVectorField (levantDifferentiatorVectorField p k)
      (levantDifferentiatorWeights p) (-1) := by
  intro l hl x
  funext i
  rw [Pi.smul_apply, smul_eq_mul]
  rw [levantDifferentiatorVectorField_scales p k hl x i]
  rw [levantDifferentiatorDilation_apply, ← mul_assoc, ← Real.rpow_add hl]
  congr 1
  ring_nf

/-- **Levant's arbitrary-order finite-time bridge (Chapter 4).** A flow on the `(p + 1)`-
dimensional error space that is homogeneous of time exponent `1` with respect to the Levant
weighted dilation, and that maps a dilation-retractable set `D ∋ x` into `d_l D` in time
`T`, reaches the origin by time `T / (1 - l)`.  This is
`eventually_eq_zero_of_isHomogeneousFlow_of_contractive` instantiated with `p = 1`, the
Levant dilation and `weightedDilation_isDilationAction`, using `Real.rpow_one`. -/
theorem levantDifferentiator_finiteTime_of_contractive (p : ℕ)
    {Φ : ℝ → (Fin (p + 1) → ℝ) → (Fin (p + 1) → ℝ)}
    (hΦ : IsHomogeneousFlow Φ (weightedDilation (levantDifferentiatorWeights p)) 1)
    (hcomp : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ y, Φ (s + t) y = Φ s (Φ t y))
    {D : Set (Fin (p + 1) → ℝ)}
    (hD : ∀ κ, 0 < κ → κ ≤ 1 → ∀ y ∈ D,
      weightedDilation (levantDifferentiatorWeights p) κ y ∈ D)
    {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {T : ℝ} (hT : 0 < T)
    (hcontract : ∀ y ∈ D,
      Φ T y ∈ weightedDilation (levantDifferentiatorWeights p) l '' D)
    {x : Fin (p + 1) → ℝ} (hx : x ∈ D)
    (hcont : ContinuousAt (Φ · x) (T / (1 - l)))
    (hfix : ∀ s, 0 ≤ s → Φ s 0 = 0)
    (hshrink : ∀ y, (∀ N : ℕ, y ∈ closure
      (weightedDilation (levantDifferentiatorWeights p) (l ^ N) '' D)) → y = 0) :
    ∀ t, T / (1 - l) ≤ t → Φ t x = 0 := by
  have key : ∀ t, T / (1 - l ^ (1 : ℝ)) ≤ t → Φ t x = 0 :=
    eventually_eq_zero_of_isHomogeneousFlow_of_contractive
      (weightedDilation_isDilationAction (levantDifferentiatorWeights p)) hΦ
      (by norm_num : (0 : ℝ) < 1) hcomp hD hl0 hl1 hT hcontract hx
      (by simpa only [Real.rpow_one] using hcont) hfix hshrink
  intro t ht
  exact key t (by simpa only [Real.rpow_one] using ht)
