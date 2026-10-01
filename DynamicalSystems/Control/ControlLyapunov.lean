/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Control Lyapunov functions and Sontag's formula

This file records the Chapter 4 control-design material of Kabziński and
Mosiołek, *Projektowanie nieliniowych układów sterowania*, for the single-input
affine system `x' = f x + g x * u` (equation 4.8 of the book).

## Main definitions

* `IsControlLyapunovFunction`: a Lyapunov function `V` such that at every nonzero
  state some control value makes the directional derivative of `V` negative
  (Definition 4.1, equation 4.6).
* `sontagControl`: the Artstein–Sontag feedback (equation 4.9).
* `robustRedesign`: the robust unit-vector redesign of the disturbance-compensating
  part of a feedback (equation 4.34).

## Main results

* `sontagControl_deriv_neg`: the Artstein–Sontag feedback makes the directional
  derivative of `V` strictly negative.
* `robustRedesign_inner_le`: the robust redesign cancels any matched disturbance
  whose norm is bounded by `delta` (equation 4.35).
-/

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A control Lyapunov function for the single-input affine system `x' = f x + g x * u`
(Definition 4.1, equation 4.6 of Kabziński–Mosiołek): at every nonzero state `x` there
is a control value `u` for which the directional derivative of `V` along
`f x + u • g x` is strictly negative. -/
def IsControlLyapunovFunction (V : E → ℝ) (f g : E → E) : Prop :=
  ∀ x, x ≠ 0 → ∃ u : ℝ, fderiv ℝ V x (f x + u • g x) < 0

/-- The Artstein–Sontag feedback for the single-input affine system `x' = f x + g x * u`,
written in terms of `a = ∇V(x) f x` and `b = ∇V(x) g x` (equation 4.9 of
Kabziński–Mosiołek).

The book prints the formula without the leading minus sign; the sign corrected here,
`u(x) = -(a + sqrt (a^2 + b^4)) / b`, is the one that makes the directional derivative
of `V` negative. -/
noncomputable def sontagControl (V : E → ℝ) (f g : E → E) (x : E) : ℝ :=
  let a := fderiv ℝ V x (f x)
  let b := fderiv ℝ V x (g x)
  if b = 0 then 0 else -(a + Real.sqrt (a ^ 2 + b ^ 4)) / b

/-- The scalar algebra behind the Artstein–Sontag feedback: for `b ≠ 0`,
`a + (-(a + sqrt (a^2 + b^4)) / b) * b < 0`. -/
private lemma sontag_algebra {a b : ℝ} (hb : b ≠ 0) :
    a + (-(a + Real.sqrt (a ^ 2 + b ^ 4)) / b) * b < 0 := by
  have hb4 : 0 < b ^ 4 := by
    have h : 0 < (b ^ 2) ^ 2 := pow_pos (sq_pos_of_ne_zero hb) 2
    nlinarith [h]
  have hpos : 0 < a ^ 2 + b ^ 4 := by nlinarith [sq_nonneg a]
  have hval : a + (-(a + Real.sqrt (a ^ 2 + b ^ 4)) / b) * b
      = -Real.sqrt (a ^ 2 + b ^ 4) := by
    field_simp
    ring
  rw [hval]
  linarith [Real.sqrt_pos_of_pos hpos]

/-- The Artstein–Sontag feedback drives the derivative of a control Lyapunov function
strictly negative (equation 4.9 of Kabziński–Mosiołek, with the sign corrected). -/
theorem sontagControl_deriv_neg {V : E → ℝ} {f g : E → E}
    (h : IsControlLyapunovFunction V f g) {x : E} (hx : x ≠ 0) :
    fderiv ℝ V x (f x + sontagControl V f g x • g x) < 0 := by
  have hlin : fderiv ℝ V x (f x + sontagControl V f g x • g x)
      = fderiv ℝ V x (f x) + sontagControl V f g x * fderiv ℝ V x (g x) := by
    rw [map_add, map_smul, smul_eq_mul]
  by_cases hb : fderiv ℝ V x (g x) = 0
  · have hsc : sontagControl V f g x = 0 := by
      simp only [sontagControl]
      rw [ite_eq_left hb]
    rw [hlin, hsc, zero_mul, add_zero]
    obtain ⟨u, hu⟩ := h x hx
    have heq : fderiv ℝ V x (f x + u • g x) = fderiv ℝ V x (f x) := by
      rw [map_add, map_smul, smul_eq_mul, hb, mul_zero, add_zero]
    rwa [heq] at hu
  · have hsc : sontagControl V f g x
        = -(fderiv ℝ V x (f x)
            + Real.sqrt ((fderiv ℝ V x (f x)) ^ 2 + (fderiv ℝ V x (g x)) ^ 4))
          / fderiv ℝ V x (g x) := by
      simp only [sontagControl]
      rw [ite_eq_right hb]
    rw [hlin, hsc]
    exact sontag_algebra hb

/-- The robust redesign of the disturbance-compensating part of a feedback
(equation 4.34 of Kabziński–Mosiołek): for a matched disturbance channel `w`, the
compensating control points opposite to `w` with magnitude `delta`, and is set to zero
when `w = 0`. -/
noncomputable def robustRedesign (delta : ℝ) (w : E) : E := by
  classical
  exact if w = 0 then 0 else -(delta / ‖w‖) • w

/-- The robust redesign cancels every matched disturbance of norm at most `delta`
(equation 4.35 of Kabziński–Mosiołek): if `‖d‖ ≤ delta` then
`⟪w, robustRedesign delta w + d⟫ ≤ 0`. -/
theorem robustRedesign_inner_le (delta : ℝ) (w d : E) (hd : ‖d‖ ≤ delta) :
    inner ℝ w (robustRedesign delta w + d) ≤ 0 := by
  classical
  by_cases hw : w = 0
  · subst hw
    rw [robustRedesign, ite_eq_left rfl, zero_add, inner_zero_left]
  · have hnormw : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hrr : robustRedesign delta w = -(delta / ‖w‖) • w := by
      simp only [robustRedesign]
      rw [ite_eq_right hw]
    rw [hrr, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
    have hself : -(delta / ‖w‖) * ‖w‖ ^ 2 = -delta * ‖w‖ := by
      field_simp [ne_of_gt hnormw]
    have hd_bound : inner ℝ w d ≤ ‖w‖ * delta :=
      (real_inner_le_norm w d).trans (mul_le_mul_of_nonneg_left hd (norm_nonneg w))
    rw [hself]
    linarith [hd_bound]
