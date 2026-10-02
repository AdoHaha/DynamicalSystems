/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Stability.FiniteTimeLyapunov
public import DynamicalSystems.Stability.Homogeneity
public import DynamicalSystems.Stability.HomogeneityFiniteTime
public import Mathlib.Basic.Real.Sign
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.LinearAlgebra.Matrix.PosDef

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
* `superTwistingA`: the Moreno–Osorio matrix `A = [[-k₁/2, 1/2], [-k₂, 0]]`.
* `morenoOsorioP`: the Moreno–Osorio matrix `P = [[2k₂ + k₁²/2, -k₁/2], [-k₁/2, 1]]`.
* `morenoOsorioQ`: the Moreno–Osorio matrix `Q = (k₁/2) • [[2k₂ + k₁², -k₁], [-k₁, 1]]`.
* `superTwistingZeta`: the Moreno–Osorio coordinate change `ζ(x) = (|x₀|^{1/2} sign x₀, x₁)`.
* `morenoOsorioV`: the Moreno–Osorio Lyapunov function `V(x) = ζ(x)ᵀ P ζ(x)`.

## Main statements

* `secondOrderDilation_isDilationAction`: `secondOrderDilation` is a dilation action.
* `twistingControl_homogeneous`: twisting control is 2-sliding homogeneous of degree `0`.
* `twistingVectorField_homogeneous`: twisting closed loop is homogeneous of degree `-1`.
* `superTwistingVectorField_homogeneous`: super-twisting field is homogeneous of degree `-1`.
* `quasiContinuous2Control_homogeneous`: quasi-continuous control has degree `0`.
* `quasiContinuous2VectorField_homogeneous`: quasi-continuous field has degree `-1`.
* `secondOrder_finiteTime_of_contractive`: Levant's Theorem 3 bridge, a contracting
  retractable set for a time-`1`-homogeneous flow reaches the origin in finite time.
* `morenoOsorioP_posDef` and `morenoOsorioQ_posDef`: `P` and `Q` are positive definite.
* `morenoOsorio_lyapunov_equation`: `Aᵀ P + P A = -Q`.
* `morenoOsorioV_pos_def`: `V` is positive definite and vanishes exactly at the origin.
* `superTwisting_finiteTime_of_lyapunov_decay`: a continuous trajectory with right
  derivative `z' ≤ -c z^{1/2}` reaches zero within the finite time `2 sqrt(z₀)/c`.

For the last statement the continuity of `z` on `[t₀, t₁]` is an explicit hypothesis
(`hzcont`): without it the statement is false (a trajectory may jump at the final time
or have an upward interior jump while still satisfying the right-derivative bound). -/

@[expose] public section

open Matrix

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

/-! ## Moreno–Osorio algebraic Lyapunov certificate -/

/-- The super-twisting matrix `A = [[-k₁/2, 1/2], [-k₂, 0]]` of the Moreno–Osorio
change of variables: with `ζ = (|σ|^{1/2} sign σ, w)` the super-twisting closed loop reads
`ζ' = |σ|^{-1/2} A ζ` off `σ = 0` (Moreno and Osorio, *A Lyapunov approach to second-order
sliding mode controllers and observers*, CDC 2008). -/
noncomputable def superTwistingA (k₁ k₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![-(1 / 2) * k₁, 1 / 2; -k₂, 0]

/-- The Moreno–Osorio matrix `P = [[2k₂ + k₁²/2, -k₁/2], [-k₁/2, 1]]`. It is positive
definite for `k₁, k₂ > 0` and solves the algebraic Lyapunov equation `Aᵀ P + P A = -Q`. -/
noncomputable def morenoOsorioP (k₁ k₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * k₂ + (1 / 2) * k₁ ^ 2, -(1 / 2) * k₁; -(1 / 2) * k₁, 1]

/-- The Moreno–Osorio matrix `Q = (k₁/2) • [[2k₂ + k₁², -k₁], [-k₁, 1]]`, positive
definite for `k₁, k₂ > 0`, whose associated quadratic form is the sum of squares
`k₁k₂ζ₁² + (k₁/2)(k₁ζ₁ - ζ₂)²`. -/
noncomputable def morenoOsorioQ (k₁ k₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (k₁ / 2) • !![2 * k₂ + k₁ ^ 2, -k₁; -k₁, 1]

/-- The Moreno–Osorio change of variables `ζ(x) = (|x₀|^{1/2} sign x₀, x₁)` on the
super-twisting phase space `x = (σ, w)`. -/
noncomputable def superTwistingZeta (x : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![|x 0| ^ (1 / 2 : ℝ) * Real.sign (x 0), x 1]

/-- The Moreno–Osorio Lyapunov function `V(x) = ζ(x)ᵀ P ζ(x)` for the super-twisting
algorithm. -/
noncomputable def morenoOsorioV (k₁ k₂ : ℝ) (x : Fin 2 → ℝ) : ℝ :=
  dotProduct (superTwistingZeta x) (morenoOsorioP k₁ k₂ *ᵥ superTwistingZeta x)

/-- The quadratic form of `morenoOsorioP` as a sum of squares,
`2k₂ a² + ½(k₁a - b)² + ½b²`. -/
private lemma qformP (k₁ k₂ : ℝ) (x : Fin 2 → ℝ) :
    star x ⬝ᵥ (morenoOsorioP k₁ k₂ *ᵥ x)
      = 2 * k₂ * x 0 ^ 2 + (1 / 2) * (k₁ * x 0 - x 1) ^ 2 + (1 / 2) * x 1 ^ 2 := by
  simp only [morenoOsorioP, Matrix.of_apply, dotProduct, Matrix.mulVec, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, star_trivial]
  ring

/-- The quadratic form of `morenoOsorioQ` as a sum of squares,
`k₁k₂ a² + (k₁/2)(k₁a - b)²`. -/
private lemma qformQ (k₁ k₂ : ℝ) (x : Fin 2 → ℝ) :
    star x ⬝ᵥ (morenoOsorioQ k₁ k₂ *ᵥ x)
      = k₁ * k₂ * x 0 ^ 2 + (k₁ / 2) * (k₁ * x 0 - x 1) ^ 2 := by
  simp only [morenoOsorioQ, Matrix.of_apply, Matrix.smul_apply, dotProduct, Matrix.mulVec,
    Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, star_trivial, smul_eq_mul]
  ring

/-- `|a|^{1/2} sign a` vanishes exactly at `a = 0`: the Moreno–Osorio coordinate change is
a bijection on the real line. -/
private theorem rpow_half_mul_sign_eq_zero {a : ℝ} :
    |a| ^ (1 / 2 : ℝ) * Real.sign a = 0 ↔ a = 0 := by
  constructor
  · intro h
    by_contra ha
    have h1 : 0 < |a| ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (abs_pos.mpr ha) _
    have h2 : Real.sign a ≠ 0 := by simpa only [ne_eq, Real.sign_eq_zero_iff] using ha
    exact (mul_ne_zero (ne_of_gt h1) h2) h
  · rintro rfl; simp

set_option linter.unusedVariables false in
/-- `P` is positive definite for `k₁, k₂ > 0`, by the sum-of-squares decomposition
`2k₂a² + ½(k₁a - b)² + ½b²`. The hypothesis `hk₁` is not needed for this particular
matrix (it is kept to match the reviewed signature and the companion `Q`), hence the
`nolint` below. -/
@[nolint unusedArguments]
theorem morenoOsorioP_posDef {k₁ k₂ : ℝ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) :
    (morenoOsorioP k₁ k₂).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · rw [Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [morenoOsorioP, Matrix.conjTranspose, Matrix.transpose]
  · intro x hx
    rw [qformP]
    rcases eq_or_ne (x 1) 0 with h1 | h1
    · have h0 : x 0 ≠ 0 := by
        intro h0
        exact hx (by funext i; fin_cases i <;> simp [h0, h1])
      have hpos : 0 < 2 * k₂ * x 0 ^ 2 := mul_pos (by positivity) (sq_pos_of_ne_zero h0)
      nlinarith [sq_nonneg (k₁ * x 0 - x 1), sq_nonneg (x 1)]
    · have hpos : 0 < (1 / 2) * x 1 ^ 2 := mul_pos (by norm_num) (sq_pos_of_ne_zero h1)
      nlinarith [sq_nonneg (k₁ * x 0 - x 1), mul_nonneg hk₂.le (sq_nonneg (x 0))]

/-- `Q` is positive definite for `k₁, k₂ > 0`, by the sum-of-squares decomposition
`k₁k₂a² + (k₁/2)(k₁a - b)²`. -/
theorem morenoOsorioQ_posDef {k₁ k₂ : ℝ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) :
    (morenoOsorioQ k₁ k₂).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · rw [Matrix.IsHermitian]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [morenoOsorioQ, Matrix.conjTranspose, Matrix.transpose, Matrix.smul_apply,
        smul_eq_mul]
  · intro x hx
    rw [qformQ]
    rcases eq_or_ne (x 0) 0 with h0 | h0
    · have h1 : x 1 ≠ 0 := by
        intro h1
        exact hx (by funext i; fin_cases i <;> simp [h0, h1])
      have hne : k₁ * x 0 - x 1 ≠ 0 := by rw [h0]; simpa using h1
      have hpos : 0 < (k₁ / 2) * (k₁ * x 0 - x 1) ^ 2 :=
        mul_pos (by positivity) (sq_pos_of_ne_zero hne)
      nlinarith [mul_nonneg (mul_nonneg hk₁.le hk₂.le) (sq_nonneg (x 0))]
    · have hpos : 0 < k₁ * k₂ * x 0 ^ 2 := by positivity
      nlinarith [sq_nonneg (k₁ * x 0 - x 1)]

/-- The Moreno–Osorio algebraic Lyapunov equation `Aᵀ P + P A = -Q`. -/
theorem morenoOsorio_lyapunov_equation {k₁ k₂ : ℝ} :
    (superTwistingA k₁ k₂)ᵀ * morenoOsorioP k₁ k₂
      + morenoOsorioP k₁ k₂ * superTwistingA k₁ k₂ = -morenoOsorioQ k₁ k₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [superTwistingA, morenoOsorioP, morenoOsorioQ, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.transpose_apply,
      Matrix.neg_apply, smul_eq_mul] <;> ring

set_option linter.unusedVariables false in
/-- The Moreno–Osorio Lyapunov function is positive definite: `0 ≤ V x` and `V x = 0`
if and only if `x = 0`. The proof rewrites `V` through the sum of squares
`2k₂ζ₁² + ½(k₁ζ₁ - ζ₂)² + ½ζ₂²` with `ζ = superTwistingZeta x`, and uses that the
coordinate change `ζ` vanishes exactly at the origin. The hypothesis `hk₁` is not needed
for this statement, hence the `nolint` below. -/
@[nolint unusedArguments]
theorem morenoOsorioV_pos_def {k₁ k₂ : ℝ} (hk₁ : 0 < k₁) (hk₂ : 0 < k₂) (x : Fin 2 → ℝ) :
    0 ≤ morenoOsorioV k₁ k₂ x ∧ (morenoOsorioV k₁ k₂ x = 0 ↔ x = 0) := by
  have hV : morenoOsorioV k₁ k₂ x
      = 2 * k₂ * (superTwistingZeta x 0) ^ 2
        + (1 / 2) * (k₁ * superTwistingZeta x 0 - superTwistingZeta x 1) ^ 2
        + (1 / 2) * (superTwistingZeta x 1) ^ 2 := by
    rw [morenoOsorioV, show dotProduct (superTwistingZeta x)
          (morenoOsorioP k₁ k₂ *ᵥ superTwistingZeta x)
        = star (superTwistingZeta x) ⬝ᵥ (morenoOsorioP k₁ k₂ *ᵥ superTwistingZeta x) from by
      simp only [dotProduct, star_trivial]]
    exact qformP k₁ k₂ (superTwistingZeta x)
  refine ⟨?_, ?_⟩
  · rw [hV]; positivity
  · constructor
    · intro hzero
      have hsum : 2 * k₂ * (superTwistingZeta x 0) ^ 2
          + (1 / 2) * (k₁ * superTwistingZeta x 0 - superTwistingZeta x 1) ^ 2
          + (1 / 2) * (superTwistingZeta x 1) ^ 2 = 0 := by rw [← hV]; exact hzero
      have h1 : 0 ≤ 2 * k₂ * (superTwistingZeta x 0) ^ 2 := by positivity
      have h2 : 0 ≤ (1 / 2) * (k₁ * superTwistingZeta x 0 - superTwistingZeta x 1) ^ 2 := by
        positivity
      have h3 : 0 ≤ (1 / 2) * (superTwistingZeta x 1) ^ 2 := by positivity
      have hfirst : 2 * k₂ * (superTwistingZeta x 0) ^ 2 = 0 := by linarith
      have hlast : (1 / 2) * (superTwistingZeta x 1) ^ 2 = 0 := by linarith
      have hz0 : superTwistingZeta x 0 = 0 := by
        refine sq_eq_zero_iff.mp ((mul_eq_zero.mp hfirst).resolve_left ?_)
        positivity
      have hz1 : superTwistingZeta x 1 = 0 := by
        refine sq_eq_zero_iff.mp ((mul_eq_zero.mp hlast).resolve_left ?_)
        norm_num
      have hx0 : x 0 = 0 := by
        have : |x 0| ^ (1 / 2 : ℝ) * Real.sign (x 0) = 0 := by
          simpa [superTwistingZeta] using hz0
        exact rpow_half_mul_sign_eq_zero.mp this
      have hx1 : x 1 = 0 := by simpa [superTwistingZeta] using hz1
      funext i; fin_cases i <;> simp [hx0, hx1]
    · rintro rfl
      rw [hV]
      simp [superTwistingZeta]

/-- **Bridge to the scalar finite-time comparison.** A continuous trajectory `z` on
`[t₀, t₁]` whose right derivative satisfies `z' ≤ -c z^{1/2}` reaches `0` by the settling
time `2 sqrt(z₀)/c`: if the endpoint value were positive, the barrier
`s ↦ z s^{1/2} + (c/2) s` would be non-increasing and would force `z t₁^{1/2} ≤ 0`.

This is the `α = 1/2` case of slice S2's `eq_zero_of_hasDerivWithinAt_le_neg_mul_rpow`,
restricted to the finite interval and with an arbitrary (existential) right derivative,
which is why the endpoint continuity `hzcont` is an explicit hypothesis. -/
theorem superTwisting_finiteTime_of_lyapunov_decay
    {z : ℝ → ℝ} {c : ℝ} (hc : 0 < c) {t₀ t₁ : ℝ} (ht : t₀ < t₁)
    (hzcont : ContinuousOn z (Set.Icc t₀ t₁))
    (hzpos : ∀ t ∈ Set.Icc t₀ t₁, 0 ≤ z t)
    (hdiff : ∀ t ∈ Set.Ico t₀ t₁,
      ∃ z', HasDerivWithinAt z z' (Set.Ici t) t ∧ z' ≤ -c * (z t) ^ (1 / 2 : ℝ))
    (hsettle : 2 * (z t₀) ^ (1 / 2 : ℝ) / c ≤ t₁ - t₀) :
    z t₁ = 0 := by
  by_contra hz
  have hztpos : 0 < z t₁ := lt_of_le_of_ne (hzpos t₁ ⟨ht.le, le_rfl⟩) (Ne.symm hz)
  let z' : ℝ → ℝ := fun t ↦ if h : t ∈ Set.Ico t₀ t₁ then (hdiff t h).choose else 0
  have hz'spec : ∀ t (ht' : t ∈ Set.Ico t₀ t₁),
      HasDerivWithinAt z (z' t) (Set.Ici t) t ∧ z' t ≤ -c * (z t) ^ (1 / 2 : ℝ) := by
    intro t ht'
    have hz' : z' t = (hdiff t ht').choose := by
      simp only [z', dite_eq_left ht']
    rw [hz']
    exact (hdiff t ht').choose_spec
  have hanti : ∀ ⦃a b : ℝ⦄, t₀ ≤ a → a ≤ b → b ≤ t₁ → z b ≤ z a := by
    intro a b ha hab hb
    have hcont_ab : ContinuousOn z (Set.Icc a b) := hzcont.mono (Set.Icc_subset_Icc ha hb)
    have hderiv' : ∀ x ∈ Set.Ico a b, HasDerivWithinAt z (z' x) (Set.Ici x) x :=
      fun x hx ↦ (hz'spec x ⟨le_trans ha hx.1, lt_of_lt_of_le hx.2 hb⟩).1
    have hbound : ∀ x ∈ Set.Ico a b, z' x ≤ (0 : ℝ) := by
      intro x hx
      have hx0 : t₀ ≤ x := le_trans ha hx.1
      have hxt : x < t₁ := lt_of_lt_of_le hx.2 hb
      have hzx : 0 ≤ z x := hzpos x ⟨hx0, le_of_lt hxt⟩
      have hzr : 0 ≤ z x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hzx _
      have hle := (hz'spec x ⟨hx0, hxt⟩).2
      nlinarith [hc, hzr, hle]
    exact image_le_of_deriv_right_le_deriv_boundary (f := z) (f' := z')
      (B := fun _ ↦ z a) (B' := fun _ ↦ 0) hcont_ab hderiv' (le_refl (z a)) continuousOn_const
      (fun x _ ↦ hasDerivWithinAt_const x (Set.Ici x) (z a)) hbound
      (Set.right_mem_Icc.mpr hab)
  have hFbound : z t₁ ^ (1 / 2 : ℝ) + (c / 2) * (t₁ - t₀) ≤ z t₀ ^ (1 / 2 : ℝ) := by
    let F : ℝ → ℝ := fun s ↦ z s ^ (1 / 2 : ℝ) + (c / 2) * s
    have hFcont : ContinuousOn F (Set.Icc t₀ t₁) := by
      have h1 : ContinuousOn (fun s ↦ z s ^ (1 / 2 : ℝ)) (Set.Icc t₀ t₁) :=
        hzcont.rpow_const fun _ _ ↦ Or.inr (by norm_num)
      have h2 : ContinuousOn (fun s : ℝ ↦ (c / 2) * s) (Set.Icc t₀ t₁) :=
        continuousOn_const.mul continuousOn_id
      exact h1.add h2
    have hFderiv : ∀ x ∈ Set.Ico t₀ t₁,
        HasDerivWithinAt F (z' x * (1 / 2) * z x ^ ((1 / 2 : ℝ) - 1) + c / 2)
          (Set.Ici x) x := by
      intro x hx
      have hzx : 0 < z x := lt_of_lt_of_le hztpos (hanti hx.1 (le_of_lt hx.2) le_rfl)
      have h1 : HasDerivWithinAt (fun s ↦ z s ^ (1 / 2 : ℝ))
          (z' x * (1 / 2) * z x ^ ((1 / 2 : ℝ) - 1)) (Set.Ici x) x :=
        (hz'spec x hx).1.rpow_const (Or.inl (ne_of_gt hzx))
      have h2 : HasDerivWithinAt (fun s : ℝ ↦ (c / 2) * s) (c / 2) (Set.Ici x) x := by
        simpa using (hasDerivWithinAt_id x (Set.Ici x)).const_mul (c / 2)
      exact h1.add h2
    have hbound : ∀ x ∈ Set.Ico t₀ t₁,
        z' x * (1 / 2) * z x ^ ((1 / 2 : ℝ) - 1) + c / 2 ≤ 0 := by
      intro x hx
      have hzx : 0 < z x := lt_of_lt_of_le hztpos (hanti hx.1 (le_of_lt hx.2) le_rfl)
      have hP : 0 ≤ z x ^ ((1 / 2 : ℝ) - 1) := Real.rpow_nonneg hzx.le _
      have hle := (hz'spec x hx).2
      have hstep1 : z' x * (1 / 2) ≤ (-c * z x ^ (1 / 2 : ℝ)) * (1 / 2) :=
        mul_le_mul_of_nonneg_right hle (by norm_num)
      have hstep2 : z' x * (1 / 2) * z x ^ ((1 / 2 : ℝ) - 1)
          ≤ (-c * z x ^ (1 / 2 : ℝ)) * (1 / 2) * z x ^ ((1 / 2 : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right hstep1 hP
      have haux : z x ^ (1 / 2 : ℝ) * z x ^ ((1 / 2 : ℝ) - 1) = 1 := by
        rw [← Real.rpow_add hzx, show (1 / 2 : ℝ) + ((1 / 2 : ℝ) - 1) = 0 by ring,
          Real.rpow_zero]
      have hident : (-c * z x ^ (1 / 2 : ℝ)) * (1 / 2) * z x ^ ((1 / 2 : ℝ) - 1)
          = -(c / 2) := by
        calc (-c * z x ^ (1 / 2 : ℝ)) * (1 / 2) * z x ^ ((1 / 2 : ℝ) - 1)
            = -c * (1 / 2) * (z x ^ (1 / 2 : ℝ) * z x ^ ((1 / 2 : ℝ) - 1)) := by ring
          _ = -c * (1 / 2) := by rw [haux, mul_one]
          _ = -(c / 2) := by ring
      linarith
    have hmain := image_le_of_deriv_right_le_deriv_boundary (f := F)
      (f' := fun x ↦ z' x * (1 / 2) * z x ^ ((1 / 2 : ℝ) - 1) + c / 2)
      (B := fun _ ↦ F t₀) (B' := fun _ ↦ 0) hFcont hFderiv (le_refl (F t₀)) continuousOn_const
      (fun x _ ↦ hasDerivWithinAt_const x (Set.Ici x) (F t₀)) hbound
    have hmain' : z t₁ ^ (1 / 2 : ℝ) + (c / 2) * t₁ ≤ z t₀ ^ (1 / 2 : ℝ) + (c / 2) * t₀ := by
      simpa [F] using hmain (Set.right_mem_Icc.mpr ht.le)
    linarith
  have hst : z t₀ ^ (1 / 2 : ℝ) ≤ (c / 2) * (t₁ - t₀) := by
    have h := hsettle
    rw [div_le_iff₀ hc] at h
    nlinarith
  have hnonpos : z t₁ ^ (1 / 2 : ℝ) ≤ 0 := by linarith
  have hpos : 0 < z t₁ ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hztpos _
  linarith
