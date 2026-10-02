/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Stability.Homogeneity
public import DynamicalSystems.Stability.HomogeneityFiniteTime
public import Mathlib.Basic.Real.Sign
public import Mathlib.Data.Fin.VecNotation

/-! # Second-order sliding modes: twisting and super-twisting homogeneity

This file records the second-order sliding-mode controllers of G. Bartolini,
L. Fridman, A. Pisano and E. Usai (eds.), *Modern Sliding Mode Control Theory:
New Perspectives and Applications*, LNCIS 375, Springer 2008, in the state-space
coordinates `x = (σ, σ̇) ∈ Fin 2 → ℝ` of Chapter 4, A. Levant and
L. Alelishvili, *Discontinuous Homogeneous Control*, Section 4 (printed p. 77,
PDF p. 91).

The 2-sliding homogeneity weights are `(2, 1)`, so the weighted dilation of slice
S4 acts as `d_λ (σ, σ̇) = (λ² σ, λ σ̇)`. The twisting controller, the
super-twisting vector field and the quasi-continuous controller of order two are
all homogeneous with respect to these weights: the (scalar) controllers have
degree `0` and the closed-loop vector fields have degree `-1`, exactly the
degree for which Levant's Theorem 1 applies.

## Main definitions

* `secondOrderSlidingWeights`: the 2-sliding weights `(2, 1)`.
* `secondOrderDilation`: the 2-sliding dilation `d_λ (σ, σ̇) = (λ² σ, λ σ̇)`.
* `twistingControl`: the twisting controller `-r₁ sign σ - r₂ sign σ̇`.
* `twistingVectorField`: the twisting closed loop `(σ̇, u_twist)`.
* `superTwistingVectorField`: the super-twisting closed loop.
* `quasiContinuous2Control`: the quasi-continuous controller of order two.
* `quasiContinuous2VectorField`: the quasi-continuous closed loop.

## Main statements

* `secondOrderDilation_isDilationAction`: `secondOrderDilation` is a dilation action.
* `twistingControl_homogeneous`: twisting control is 2-sliding homogeneous of degree `0`.
* `twistingVectorField_homogeneous`: twisting closed loop is homogeneous of degree `-1`.
* `superTwistingVectorField_homogeneous`: super-twisting field is homogeneous of degree `-1`.
* `quasiContinuous2Control_homogeneous`: quasi-continuous control has degree `0`.
* `quasiContinuous2VectorField_homogeneous`: quasi-continuous field has degree `-1`.
* `secondOrder_finiteTime_of_contractive`: Levant's Theorem 3 bridge, a contracting
  retractable set for a time-`1`-homogeneous flow reaches the origin in finite time.
-/

@[expose] public section

/-- The 2-sliding homogeneity weights `(2, 1)`: the components `σ` and `σ̇` scale as
`λ ^ 2` and `λ ^ 1` under the dilation. -/
def secondOrderSlidingWeights : Fin 2 → ℝ := ![2, 1]

/-- The 2-sliding dilation `d_λ (σ, σ̇) = (λ² σ, λ σ̇)` of the weighted dilation of
slice S4 with the 2-sliding weights. -/
noncomputable def secondOrderDilation (l : ℝ) : (Fin 2 → ℝ) → (Fin 2 → ℝ) :=
  weightedDilation secondOrderSlidingWeights l

/-- Twisting controller `-r₁ sign σ - r₂ sign σ̇` (Chapter 14, printed p. 102, and the
classical twisting algorithm of Chapter 4). -/
noncomputable def twistingControl (r₁ r₂ : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  -r₁ * Real.sign (x 0) - r₂ * Real.sign (x 1)

/-- Twisting closed-loop field `(σ̇, u_twist)` in the coordinates `(σ, σ̇)`. -/
noncomputable def twistingVectorField (r₁ r₂ : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![x 1, twistingControl r₁ r₂ x]

/-- Super-twisting field `(σ̇, ẇ) = (-k₁ |σ|^{1/2} sign σ + w, -k₂ sign σ)` in the
coordinates `(σ, w)` (Levant's super-twisting algorithm, Chapter 4, printed p. 80). -/
noncomputable def superTwistingVectorField (k₁ k₂ : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![-k₁ * |x 0| ^ (1 / 2 : ℝ) * Real.sign (x 0) + x 1, -k₂ * Real.sign (x 0)]

/-- Quasi-continuous 2-sliding controller (Chapter 4, printed p. 79, Eq. 2). -/
noncomputable def quasiContinuous2Control (α : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  -α * (x 1 + |x 0| ^ (1 / 2 : ℝ) * Real.sign (x 0)) / (|x 1| + |x 0| ^ (1 / 2 : ℝ))

/-- Quasi-continuous closed-loop field `(σ̇, u_qc)` in the coordinates `(σ, σ̇)`. -/
noncomputable def quasiContinuous2VectorField (α : ℝ) (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![x 1, quasiContinuous2Control α x]

/-- The 2-sliding dilation is a dilation action: `d_1 = id` and `d_{λ μ} = d_λ ∘ d_μ`
for positive exponents. -/
theorem secondOrderDilation_isDilationAction : IsDilationAction secondOrderDilation :=
  weightedDilation_isDilationAction secondOrderSlidingWeights

/-- Evaluation of the 2-sliding dilation in the first coordinate: `(d_λ x) 0 = λ ^ 2 * x 0`. -/
private theorem secondOrderDilation_apply_zero (l : ℝ) (x : Fin 2 → ℝ) :
    weightedDilation secondOrderSlidingWeights l x 0 = l ^ (2 : ℝ) * x 0 := by
  simp only [weightedDilation, secondOrderSlidingWeights]
  norm_num

/-- Evaluation of the 2-sliding dilation in the second coordinate: `(d_λ x) 1 = λ ^ 1 * x 1`. -/
private theorem secondOrderDilation_apply_one (l : ℝ) (x : Fin 2 → ℝ) :
    weightedDilation secondOrderSlidingWeights l x 1 = l ^ (1 : ℝ) * x 1 := by
  simp only [weightedDilation, secondOrderSlidingWeights]
  norm_num

/-- If `0 < a` then `sign (a * b) = sign b`: multiplication by a positive number does
not change the sign. -/
private theorem sign_mul_of_pos_left {a b : ℝ} (ha : 0 < a) : Real.sign (a * b) = Real.sign b := by
  rcases lt_trichotomy b 0 with hb | rfl | hb
  · rw [Real.sign_of_neg (mul_neg_of_pos_of_neg ha hb), Real.sign_of_neg hb]
  · simp
  · rw [Real.sign_of_pos (mul_pos ha hb), Real.sign_of_pos hb]

/-- The sign of the first coordinate of the 2-sliding dilation: `sign (λ ^ 2 σ) = sign σ`
for `λ > 0`. -/
private theorem sign_secondOrderDilation_apply_zero {l : ℝ} (hl : 0 < l) (x : Fin 2 → ℝ) :
    Real.sign (weightedDilation secondOrderSlidingWeights l x 0) = Real.sign (x 0) := by
  rw [secondOrderDilation_apply_zero, sign_mul_of_pos_left (Real.rpow_pos_of_pos hl 2)]

/-- The sign of the second coordinate of the 2-sliding dilation: `sign (λ σ̇) = sign σ̇`
for `λ > 0`. -/
private theorem sign_secondOrderDilation_apply_one {l : ℝ} (hl : 0 < l) (x : Fin 2 → ℝ) :
    Real.sign (weightedDilation secondOrderSlidingWeights l x 1) = Real.sign (x 1) := by
  rw [secondOrderDilation_apply_one, sign_mul_of_pos_left (Real.rpow_pos_of_pos hl 1)]

/-- The power `|λ ^ 2 a|^{1/2}` is `λ |a|^{1/2}` for `λ > 0`. -/
private theorem abs_rpow_half_mul_sq {l a : ℝ} (hl : 0 < l) :
    |l ^ (2 : ℝ) * a| ^ (1 / 2 : ℝ) = l * |a| ^ (1 / 2 : ℝ) := by
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hl.le 2),
    Real.mul_rpow (Real.rpow_nonneg hl.le 2) (abs_nonneg a),
    show (l ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = l by
      rw [← Real.rpow_mul hl.le]
      norm_num]

/-- The twisting controller is 2-sliding homogeneous of degree `0`, globally (including at
the origin, because `sign 0 = 0`). -/
theorem twistingControl_homogeneous (r₁ r₂ : ℝ) :
    IsHomogeneousFunction (twistingControl r₁ r₂) secondOrderSlidingWeights 0 := by
  intro l hl x
  rw [Real.rpow_zero, one_mul]
  simp only [twistingControl]
  rw [sign_secondOrderDilation_apply_zero hl, sign_secondOrderDilation_apply_one hl]

/-- `λ ^ (-1) * (λ * a) = a` for `λ > 0`. -/
private theorem rpow_neg_one_mul {l a : ℝ} (hl : 0 < l) :
    l ^ (-1 : ℝ) * (l * a) = a := by
  rw [Real.rpow_neg_one, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hl), one_mul]

/-- `λ ^ (-1) * (λ ^ 2 * a) = λ * a` for `λ > 0`. -/
private theorem rpow_neg_one_mul_rpow_two_mul {l a : ℝ} (hl : 0 < l) :
    l ^ (-1 : ℝ) * (l ^ (2 : ℝ) * a) = l * a := by
  rw [← mul_assoc,
    show l ^ (-1 : ℝ) * l ^ (2 : ℝ) = l by
      rw [← Real.rpow_add hl]
      norm_num]

/-- The twisting closed loop is 2-sliding homogeneous of degree `-1`. -/
theorem twistingVectorField_homogeneous (r₁ r₂ : ℝ) :
    IsHomogeneousVectorField (twistingVectorField r₁ r₂) secondOrderSlidingWeights (-1) := by
  intro l hl x
  have h0 : twistingVectorField r₁ r₂ (weightedDilation secondOrderSlidingWeights l x) 0 =
      (l ^ (-1 : ℝ) • weightedDilation secondOrderSlidingWeights l
        (twistingVectorField r₁ r₂ x)) 0 := by
    simp only [twistingVectorField, secondOrderDilation_apply_one,
      secondOrderDilation_apply_zero, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
    rw [Real.rpow_one, rpow_neg_one_mul_rpow_two_mul hl]
  have h1 : twistingVectorField r₁ r₂ (weightedDilation secondOrderSlidingWeights l x) 1 =
      (l ^ (-1 : ℝ) • weightedDilation secondOrderSlidingWeights l
        (twistingVectorField r₁ r₂ x)) 1 := by
    simp only [twistingVectorField, secondOrderDilation_apply_one, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [twistingControl_homogeneous r₁ r₂ l hl x, Real.rpow_zero, one_mul, Real.rpow_one,
      rpow_neg_one_mul hl]
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-- The super-twisting field is 2-sliding homogeneous of degree `-1`. -/
theorem superTwistingVectorField_homogeneous (k₁ k₂ : ℝ) :
    IsHomogeneousVectorField (superTwistingVectorField k₁ k₂) secondOrderSlidingWeights (-1) := by
  intro l hl x
  have h0 : superTwistingVectorField k₁ k₂ (weightedDilation secondOrderSlidingWeights l x) 0 =
      (l ^ (-1 : ℝ) • weightedDilation secondOrderSlidingWeights l
        (superTwistingVectorField k₁ k₂ x)) 0 := by
    simp only [superTwistingVectorField, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
      secondOrderDilation_apply_zero, secondOrderDilation_apply_one]
    rw [Real.rpow_one, abs_rpow_half_mul_sq hl,
      sign_mul_of_pos_left (Real.rpow_pos_of_pos hl 2), rpow_neg_one_mul_rpow_two_mul hl]
    ring
  have h1 : superTwistingVectorField k₁ k₂ (weightedDilation secondOrderSlidingWeights l x) 1 =
      (l ^ (-1 : ℝ) • weightedDilation secondOrderSlidingWeights l
        (superTwistingVectorField k₁ k₂ x)) 1 := by
    simp only [superTwistingVectorField, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
      Matrix.cons_val_zero, secondOrderDilation_apply_one, secondOrderDilation_apply_zero]
    rw [sign_mul_of_pos_left (Real.rpow_pos_of_pos hl 2), Real.rpow_one, rpow_neg_one_mul hl]
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-- `-α * (λ * A) / (λ * B) = -α * A / B` for `λ ≠ 0`: a common nonzero factor in the
numerator and denominator of the quasi-continuous control cancels. -/
private theorem quasi_div_scale {l A B α : ℝ} (hl : l ≠ 0) :
    -α * (l * A) / (l * B) = -α * A / B := by
  rw [show -α * (l * A) = l * (-α * A) by ring]
  rw [mul_div_mul_left _ _ hl]

/-- The quasi-continuous controller of order two is 2-sliding homogeneous of degree `0`
(globally, since `0 / 0 = 0` in Lean's field convention). -/
theorem quasiContinuous2Control_homogeneous (α : ℝ) :
    IsHomogeneousFunction (quasiContinuous2Control α) secondOrderSlidingWeights 0 := by
  intro l hl x
  rw [Real.rpow_zero, one_mul]
  have hnum : (weightedDilation secondOrderSlidingWeights l x) 1 +
        |(weightedDilation secondOrderSlidingWeights l x) 0| ^ (1 / 2 : ℝ) *
          Real.sign ((weightedDilation secondOrderSlidingWeights l x) 0) =
      l * (x 1 + |x 0| ^ (1 / 2 : ℝ) * Real.sign (x 0)) := by
    rw [secondOrderDilation_apply_one, Real.rpow_one, secondOrderDilation_apply_zero,
      abs_rpow_half_mul_sq hl, sign_mul_of_pos_left (Real.rpow_pos_of_pos hl 2)]
    ring
  have hden : |(weightedDilation secondOrderSlidingWeights l x) 1| +
        |(weightedDilation secondOrderSlidingWeights l x) 0| ^ (1 / 2 : ℝ) =
      l * (|x 1| + |x 0| ^ (1 / 2 : ℝ)) := by
    rw [secondOrderDilation_apply_one, Real.rpow_one, abs_mul, abs_of_pos hl,
      secondOrderDilation_apply_zero, abs_rpow_half_mul_sq hl]
    ring
  simp only [quasiContinuous2Control]
  rw [hnum, hden]
  exact quasi_div_scale (ne_of_gt hl)

/-- The quasi-continuous closed loop is 2-sliding homogeneous of degree `-1`. -/
theorem quasiContinuous2VectorField_homogeneous (α : ℝ) :
    IsHomogeneousVectorField (quasiContinuous2VectorField α) secondOrderSlidingWeights (-1) := by
  intro l hl x
  have h0 : quasiContinuous2VectorField α (weightedDilation secondOrderSlidingWeights l x) 0 =
      (l ^ (-1 : ℝ) • weightedDilation secondOrderSlidingWeights l
        (quasiContinuous2VectorField α x)) 0 := by
    simp only [quasiContinuous2VectorField, secondOrderDilation_apply_one,
      secondOrderDilation_apply_zero, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero]
    rw [Real.rpow_one, rpow_neg_one_mul_rpow_two_mul hl]
  have h1 : quasiContinuous2VectorField α (weightedDilation secondOrderSlidingWeights l x) 1 =
      (l ^ (-1 : ℝ) • weightedDilation secondOrderSlidingWeights l
        (quasiContinuous2VectorField α x)) 1 := by
    simp only [quasiContinuous2VectorField, secondOrderDilation_apply_one, Pi.smul_apply,
      smul_eq_mul, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [quasiContinuous2Control_homogeneous α l hl x, Real.rpow_zero, one_mul, Real.rpow_one,
      rpow_neg_one_mul hl]
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-- **Levant's Theorem 3 bridge (Chapter 4).** A flow on the 2-sliding phase space
`(σ, σ̇)` that is homogeneous of time exponent `1` with respect to the 2-sliding dilation,
and that maps a dilation-retractable set `D ∋ x` into `d_λ D` in time `T`, reaches the
origin by time `T / (1 - λ)`. This is
`eventually_eq_zero_of_isHomogeneousFlow_of_contractive` instantiated with `p = 1` and the
2-sliding dilation, using `secondOrderDilation_isDilationAction` and `Real.rpow_one`. -/
theorem secondOrder_finiteTime_of_contractive
    {Φ : ℝ → (Fin 2 → ℝ) → (Fin 2 → ℝ)}
    (hΦ : IsHomogeneousFlow Φ secondOrderDilation 1)
    (hcomp : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ y, Φ (s + t) y = Φ s (Φ t y))
    {D : Set (Fin 2 → ℝ)} (hD : ∀ κ, 0 < κ → κ ≤ 1 → ∀ y ∈ D, secondOrderDilation κ y ∈ D)
    {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {T : ℝ} (hT : 0 < T)
    (hcontract : ∀ y ∈ D, Φ T y ∈ secondOrderDilation l '' D) {x : Fin 2 → ℝ} (hx : x ∈ D)
    (hcont : ContinuousAt (Φ · x) (T / (1 - l)))
    (hfix : ∀ s, 0 ≤ s → Φ s 0 = 0)
    (hshrink : ∀ y, (∀ N : ℕ, y ∈ closure (secondOrderDilation (l ^ N) '' D)) → y = 0) :
    ∀ t, T / (1 - l) ≤ t → Φ t x = 0 := by
  have key : ∀ t, T / (1 - l ^ (1 : ℝ)) ≤ t → Φ t x = 0 :=
    eventually_eq_zero_of_isHomogeneousFlow_of_contractive
      secondOrderDilation_isDilationAction hΦ (by norm_num : (0 : ℝ) < 1) hcomp hD hl0 hl1 hT
      hcontract hx (by simpa only [Real.rpow_one] using hcont) hfix hshrink
  intro t ht
  exact key t (by simpa only [Real.rpow_one] using ht)
