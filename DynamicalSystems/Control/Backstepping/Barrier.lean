/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Order.IntermediateValue
public import DynamicalSystems.Stability.Barbalat
public import DynamicalSystems.Stability.Comparison

/-!
# Adaptive backstepping with logarithmic barrier Lyapunov functions

This file formalizes output-constrained adaptive backstepping with logarithmic
Barrier Lyapunov Functions (BLF) for the second-order strict-feedback plant,
following Kabziński and Mosiołek, *Projektowanie nieliniowych układów sterowania*,
Komitet Automatyki i Robotyki PAN, Monografie tom 22, Chapter 12, Sections
12.1–12.2, pages 219–226, Definition 12.1, Theorems 12.1–12.2, Wniosek 12.1,
and equations (12.1)–(12.46).

## System description

The plant is the second-order system
```
x₁' = x₂
x₂' = u + θ ᵀ ϕ
```
where `θ ∈ ℝᵖ` is an unknown constant parameter vector, `ϕ ∈ ℝᵖ` is a known
regressor and `u` is the control input. The control objective is asymptotic
tracking of a smooth reference trajectory `x₁d` while respecting the *hard*
output constraint `|x₁(t)| < Δ₁` (equation 12.8). Writing `e₁ = x₁ - x₁d` and
`k_b = Δ₁ - x_m` with `|x₁d(t)| ≤ x_m < Δ₁` (equation 12.10), the constraint is
equivalent to the error barrier `|e₁(t)| < k_b`.

## Logarithmic barrier Lyapunov function

The logarithmic BLF is (equation 12.1)
```
V₁(z) = (1/2) ln (k_b² / (k_b² - z²)).
```
It is nonnegative on `(-k_b, k_b)`, vanishes at the origin, and blows up as
`z → ±k_b`. Its trajectory derivative is (equation 12.19)
```
V̇₁ = z z' / (k_b² - z²).
```
Wniosek 12.1 (equations 12.41–12.46) provides the algebraic level-set bound
`V₁(z) ≤ V₀ → |z| ≤ k_b √(1 - e^{-2 V₀}) < k_b`, which is the rigorous substitute
for the informal forward-invariance argument of Theorem 12.1.

## Closed-loop design

The stabilizing virtual control is `α₁ = -k₁ e₁` (equation 12.17), the second
error coordinate is `e₂ = x₂ - α₁ - x₁d'` (equation 12.15), and the control law is
(equation 12.36)
```
u = -θ̂ ᵀ ϕ + x₁d'' + α₁' - k₂ e₂ - e₁ / (k_b² - e₁²).
```
The non-quadratic cross term `e₁ e₂ / (k_b² - e₁²)` produced by `V̇₁` cancels
identically against the barrier term of `u`, while the tuning-function adaptation
law `θ̂' = Γ *ᵥ (e₂ • ϕ)` (equation 12.39) cancels the parameter error. The
composite BLF is (equations 12.22 and 12.33)
```
V₂(e₁, e₂, θ̃) = V₁(e₁) + (1/2) e₂² + (1/2) (θ̃ ⬝ᵥ (Γ⁻¹ *ᵥ θ̃))
```
and satisfies the exact closed-loop identity (equation 12.40)
```
V̇₂ = -k₁ e₁² / (k_b² - e₁²) - k₂ e₂² ≤ -(k₁/k_b²) e₁² - k₂ e₂² ≤ 0.
```
Theorem 12.2 then follows from the LaSalle–Yoshizawa / Barbălat bridge.

## Main definitions

* `barrier_V1`: logarithmic BLF candidate (equation 12.1).
* `barrier_alpha1`: stabilizing virtual control `α₁ = -k₁ e₁` (equation 12.17).
* `barrier_control`: output-constrained control law `u` (equation 12.36).
* `barrier_adaptation_law`: adaptation vector field `θ̂' = Γ *ᵥ (e₂ • ϕ)`
  (equation 12.39).
* `barrier_V2`: composite BLF (equations 12.22 and 12.33).

## Main results

* `barrier_level_set_bound`, `barrier_strict_bound`: the algebraic level-set
  bound of Wniosek 12.1.
* `barrier_V1_hasDerivAt`: trajectory derivative of the logarithmic BLF.
* `barrier_cross_term_cancel`: exact cancellation of the non-quadratic cross
  term.
* `barrier_V2_hasDerivAt`, `barrier_V2_deriv_le`: closed-loop Lyapunov
  dissipation identity and bound.
* `barrier_forward_invariance`, `barrier_output_bounded`: hard constraint
  satisfaction.
* `barrier_dissipation_tendsto_zero`, `barrier_tracking_tendsto_zero`: Theorem
  12.2 asymptotic tracking.

## References

* J. Kabziński, P. Mosiołek, *Projektowanie nieliniowych układów sterowania*,
  Komitet Automatyki i Robotyki PAN, Monografie tom 22, Chapter 12.
* K. P. Tee, S. S. Ge, F. E. H. Tay, *Barrier Lyapunov functions for the control
  of output-constrained nonlinear systems*, Automatica 45 (2009).
-/

open scoped Matrix

variable {p : ℕ}

@[expose] public section

/-! ### The logarithmic barrier Lyapunov function -/

/-- Logarithmic Barrier Lyapunov Function candidate
`V₁(z) = (1/2) ln (k_b² / (k_b² - z²))`
(Kabziński–Mosiołek, equation 12.1). -/
-- The underscore in `barrier_V1` is mandated by the campaign's
-- required-declaration list, so the naming linter is disabled for this def.
@[nolint defsWithUnderscore]
noncomputable def barrier_V1 (kb z : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (kb ^ 2 / (kb ^ 2 - z ^ 2))

/-- Non-negativity of the logarithmic BLF: for `k_b > 0` and `|z| < k_b`,
`barrier_V1 k_b z ≥ 0` (Kabziński–Mosiołek, Definition 12.1). -/
theorem barrier_V1_nonneg (kb z : ℝ) (hkb : 0 < kb) (hz : |z| < kb) :
    0 ≤ barrier_V1 kb z := by
  have hzsq : z ^ 2 < kb ^ 2 := by
    rw [abs_lt] at hz
    nlinarith [hz.1, hz.2, hkb]
  have hden : 0 < kb ^ 2 - z ^ 2 := by linarith
  have hkb2 : 0 < kb ^ 2 := by positivity
  have hratio : 1 ≤ kb ^ 2 / (kb ^ 2 - z ^ 2) := by
    rw [le_div_iff₀ hden]
    nlinarith [sq_nonneg z]
  have hlog : 0 ≤ Real.log (kb ^ 2 / (kb ^ 2 - z ^ 2)) := Real.log_nonneg hratio
  dsimp only [barrier_V1]
  positivity

/-- The logarithmic BLF vanishes at the origin: `barrier_V1 k_b 0 = 0`
(Kabziński–Mosiołek, equation 12.1). -/
theorem barrier_V1_zero (kb : ℝ) (hkb : 0 < kb) :
    barrier_V1 kb 0 = 0 := by
  have hkb2 : kb ^ 2 ≠ 0 := pow_ne_zero 2 hkb.ne'
  have h : kb ^ 2 / (kb ^ 2 - 0 ^ 2) = 1 := by
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, div_self hkb2]
  rw [barrier_V1, h, Real.log_one, mul_zero]

/-- Algebraic level-set bound (Kabziński–Mosiołek, Wniosek 12.1, equation 12.41):
if `|z| < k_b` and `barrier_V1 k_b z ≤ V₀`, then
`|z| ≤ k_b * √(1 - exp (-2 * V₀))`. -/
theorem barrier_level_set_bound
    (kb z V0 : ℝ) (hkb : 0 < kb) (hz : |z| < kb)
    (hV : barrier_V1 kb z ≤ V0) :
    |z| ≤ kb * Real.sqrt (1 - Real.exp (-2 * V0)) := by
  have hzsq : z ^ 2 < kb ^ 2 := by
    rw [abs_lt] at hz
    nlinarith [hz.1, hz.2, hkb]
  have hden : 0 < kb ^ 2 - z ^ 2 := by linarith
  have hkb2 : 0 < kb ^ 2 := by positivity
  have hV0 : 0 ≤ V0 := (barrier_V1_nonneg kb z hkb hz).trans hV
  have hApos : 0 < kb ^ 2 / (kb ^ 2 - z ^ 2) := div_pos hkb2 hden
  have hlog : Real.log (kb ^ 2 / (kb ^ 2 - z ^ 2)) ≤ 2 * V0 := by
    have h := hV
    dsimp only [barrier_V1] at h
    linarith
  have hAle : kb ^ 2 / (kb ^ 2 - z ^ 2) ≤ Real.exp (2 * V0) :=
    (Real.log_le_iff_le_exp hApos).mp hlog
  have hexp_mul : Real.exp (-2 * V0) * Real.exp (2 * V0) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    rw [Real.exp_zero]
  have hkey : kb ^ 2 * Real.exp (-2 * V0) ≤ kb ^ 2 - z ^ 2 := by
    have h := (div_le_iff₀ hden).mp hAle
    have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos (-2 * V0)).le
    calc kb ^ 2 * Real.exp (-2 * V0) = Real.exp (-2 * V0) * kb ^ 2 := by ring
      _ ≤ Real.exp (-2 * V0) * (Real.exp (2 * V0) * (kb ^ 2 - z ^ 2)) := hmul
      _ = kb ^ 2 - z ^ 2 := by rw [← mul_assoc, hexp_mul, one_mul]
  have hzsq_le : z ^ 2 ≤ kb ^ 2 * (1 - Real.exp (-2 * V0)) := by
    nlinarith [hkey]
  have hnonneg : 0 ≤ 1 - Real.exp (-2 * V0) := by
    have hle1 : Real.exp (-2 * V0) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    linarith
  calc
    |z| = Real.sqrt (z ^ 2) := (Real.sqrt_sq_eq_abs z).symm
    _ ≤ Real.sqrt (kb ^ 2 * (1 - Real.exp (-2 * V0))) := Real.sqrt_le_sqrt hzsq_le
    _ = kb * Real.sqrt (1 - Real.exp (-2 * V0)) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ kb ^ 2), Real.sqrt_sq hkb.le]

/-- Strict boundary exclusion (Kabziński–Mosiołek, Wniosek 12.1, equations
12.45–12.46): for any finite level `V₀`, `barrier_V1 k_b z ≤ V₀` forces the
strict inequality `|z| < k_b`. -/
theorem barrier_strict_bound
    (kb z V0 : ℝ) (hkb : 0 < kb) (hz : |z| < kb)
    (hV : barrier_V1 kb z ≤ V0) :
    |z| < kb := by
  have hbound := barrier_level_set_bound kb z V0 hkb hz hV
  have hs : Real.sqrt (1 - Real.exp (-2 * V0)) < 1 := by
    rw [Real.sqrt_lt' one_pos]
    have : 0 < Real.exp (-2 * V0) := Real.exp_pos _
    nlinarith
  nlinarith [hbound, hs, hkb]

/-- Time derivative of the logarithmic BLF along a differentiable trajectory
`z`: `d/dt V₁(z(t)) = z(t) z'(t) / (k_b² - z(t)²)`
(Kabziński–Mosiołek, equation 12.19). -/
theorem barrier_V1_hasDerivAt
    {kb : ℝ} (hkb : 0 < kb) {z z' : ℝ → ℝ} {t : ℝ}
    (hz : |z t| < kb) (hz_deriv : HasDerivAt z (z' t) t) :
    HasDerivAt (fun s ↦ barrier_V1 kb (z s))
      ((z t * z' t) / (kb ^ 2 - (z t) ^ 2)) t := by
  have hzsq : (z t) ^ 2 < kb ^ 2 := by
    rw [abs_lt] at hz
    nlinarith [hz.1, hz.2, hkb]
  have hden : kb ^ 2 - (z t) ^ 2 ≠ 0 := by
    have : 0 < kb ^ 2 - (z t) ^ 2 := by linarith
    exact this.ne'
  have hkb2 : kb ^ 2 ≠ 0 := pow_ne_zero 2 hkb.ne'
  have hg : HasDerivAt (fun s ↦ kb ^ 2 - (z s) ^ 2) (-(2 * z t * z' t)) t := by
    have hz2 : HasDerivAt (fun s ↦ (z s) ^ 2) (2 * z t * z' t) t := by
      convert hz_deriv.pow 2 using 1
      ring
    convert (hasDerivAt_const t (kb ^ 2 : ℝ)).sub hz2 using 1
    ring
  have hquot : HasDerivAt (fun s ↦ kb ^ 2 / (kb ^ 2 - (z s) ^ 2))
      (kb ^ 2 * (2 * z t * z' t) / (kb ^ 2 - (z t) ^ 2) ^ 2) t := by
    convert (hasDerivAt_const t (kb ^ 2 : ℝ)).div hg hden using 1
    ring
  have hlog := hquot.log (by positivity : kb ^ 2 / (kb ^ 2 - (z t) ^ 2) ≠ 0)
  change HasDerivAt (fun s ↦ (1 / 2 : ℝ) * Real.log (kb ^ 2 / (kb ^ 2 - (z s) ^ 2)))
    ((z t * z' t) / (kb ^ 2 - (z t) ^ 2)) t
  convert hlog.const_mul (1 / 2 : ℝ) using 1
  field_simp

/-! ### Log barrier helpers and control design -/

/-- Virtual stabilizing control `α₁ = -k₁ e₁`
(Kabziński–Mosiołek, equation 12.17). -/
-- The underscore in `barrier_alpha1` is mandated by the campaign's
-- required-declaration list, so the naming linter is disabled for this def.
@[nolint defsWithUnderscore]
def barrier_alpha1 (k1 e1 : ℝ) : ℝ :=
  -k1 * e1

/-- Barrier backstepping feedback control law
`u = -θ̂ ⬝ᵥ ϕ + x₁d'' + α₁' - k₂ e₂ - e₁ / (k_b² - e₁²)`
(Kabziński–Mosiołek, equations 12.24 and 12.36). -/
-- The underscore in `barrier_control` is mandated by the campaign's
-- required-declaration list, so the naming linter is disabled for this def.
@[nolint defsWithUnderscore]
noncomputable def barrier_control
    (k2 kb e1 e2 : ℝ) (theta_hat phi : Fin p → ℝ) (xd'' alpha1' : ℝ) : ℝ :=
  -(theta_hat ⬝ᵥ phi) + xd'' + alpha1' - k2 * e2 - e1 / (kb ^ 2 - e1 ^ 2)

/-- Tuning function parameter adaptation law `θ̂' = Γ *ᵥ (e₂ • ϕ)`
(Kabziński–Mosiołek, equation 12.39). -/
-- The underscore in `barrier_adaptation_law` is mandated by the campaign's
-- required-declaration list, so the naming linter is disabled for this def.
@[nolint defsWithUnderscore]
def barrier_adaptation_law
    (Gamma : Matrix (Fin p) (Fin p) ℝ) (e2 : ℝ) (phi : Fin p → ℝ) : Fin p → ℝ :=
  Gamma *ᵥ (e2 • phi)

/-- Composite Barrier Lyapunov candidate for the second-order system:
`V₂(e₁, e₂, θ̃) = V₁(e₁) + (1/2) e₂² + (1/2) (θ̃ ⬝ᵥ (Γ⁻¹ *ᵥ θ̃))`
(Kabziński–Mosiołek, equations 12.22 and 12.33). -/
-- The underscore in `barrier_V2` is mandated by the campaign's
-- required-declaration list, so the naming linter is disabled for this def.
@[nolint defsWithUnderscore]
noncomputable def barrier_V2
    (Gamma_inv : Matrix (Fin p) (Fin p) ℝ) (kb e1 e2 : ℝ)
    (theta_tilde : Fin p → ℝ) : ℝ :=
  barrier_V1 kb e1 + (1 / 2 : ℝ) * e2 ^ 2 +
    (1 / 2 : ℝ) * (theta_tilde ⬝ᵥ (Gamma_inv *ᵥ theta_tilde))

/-! ### Internal calculus and algebra helpers

The calculus and algebra helpers below follow the compact private copies used by
`DynamicalSystems.Control.Backstepping.Tuning`. -/

/-- Product rule for the dot product of two vector trajectories. -/
private theorem hasDerivAt_dotProduct {ι : Type*} [Fintype ι]
    {u v : ℝ → (ι → ℝ)} {u' v' : ι → ℝ} {t : ℝ}
    (hu : ∀ i, HasDerivAt (fun s ↦ u s i) (u' i) t)
    (hv : ∀ i, HasDerivAt (fun s ↦ v s i) (v' i) t) :
    HasDerivAt (fun s ↦ (u s) ⬝ᵥ (v s)) (u' ⬝ᵥ (v t) + (u t) ⬝ᵥ v') t := by
  simp only [dotProduct]
  have h : HasDerivAt (∑ i ∈ (Finset.univ : Finset ι), fun s ↦ u s i * v s i)
      (∑ i ∈ (Finset.univ : Finset ι), (u' i * v t i + u t i * v' i)) t :=
    HasDerivAt.sum (fun i _ ↦ (hu i).mul (hv i))
  have hfun : (fun s ↦ ∑ i, u s i * v s i) =
      (∑ i ∈ (Finset.univ : Finset ι), fun s ↦ u s i * v s i) := by
    funext s
    rw [Finset.sum_apply]
  rw [hfun]
  exact h.congr_deriv Finset.sum_add_distrib

/-- Differentiating a constant matrix-vector product `s ↦ M *ᵥ u s`
coordinate-wise. -/
private theorem hasDerivAt_mulVec {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) {u : ℝ → (ι → ℝ)} {u' : ι → ℝ} {t : ℝ}
    (hu : ∀ j, HasDerivAt (fun s ↦ u s j) (u' j) t) (i : ι) :
    HasDerivAt (fun s ↦ (M *ᵥ (u s)) i) ((M *ᵥ u') i) t := by
  simp only [Matrix.mulVec, dotProduct]
  have h : HasDerivAt (∑ j ∈ (Finset.univ : Finset ι), fun s ↦ M i j * u s j)
      (∑ j ∈ (Finset.univ : Finset ι), M i j * u' j) t :=
    HasDerivAt.sum (fun j _ ↦ (hu j).const_mul (M i j))
  have hfun : (fun s ↦ ∑ x, M i x * u s x) =
      (∑ j ∈ (Finset.univ : Finset ι), fun s ↦ M i j * u s j) := by
    funext s
    rw [Finset.sum_apply]
  rw [hfun]
  exact h

/-- Derivative of a quadratic form `s ↦ (1/2) * (u s ⬝ᵥ (M *ᵥ u s))` along a
vector trajectory for a symmetric matrix `M`. -/
private theorem hasDerivAt_half_quadratic_form {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (hM_symm : Mᵀ = M)
    {u : ℝ → (ι → ℝ)} {u' : ι → ℝ} {t : ℝ}
    (hu : ∀ j, HasDerivAt (fun s ↦ u s j) (u' j) t) :
    HasDerivAt (fun s ↦ (1 / 2 : ℝ) * ((u s) ⬝ᵥ (M *ᵥ (u s)))) ((u t) ⬝ᵥ (M *ᵥ u')) t := by
  have hw : ∀ j, HasDerivAt (fun s ↦ (M *ᵥ (u s)) j) ((M *ᵥ u') j) t :=
    fun j ↦ hasDerivAt_mulVec M hu j
  have hdp := hasDerivAt_dotProduct hu hw
  have hsym : u' ⬝ᵥ (M *ᵥ (u t)) = (u t) ⬝ᵥ (M *ᵥ u') := by
    have h := Matrix.dotProduct_transpose_mulVec M u' (u t)
    rwa [hM_symm] at h
  refine (hdp.const_mul (1 / 2 : ℝ)).congr_deriv ?_
  rw [hsym]
  ring

/-- Positive semidefiniteness of a quadratic form for a positive definite real
matrix. -/
private theorem posDef_dotProduct_nonneg {M : Matrix (Fin p) (Fin p) ℝ}
    (hM : M.PosDef) (x : Fin p → ℝ) : 0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    simp
  · exact le_of_lt (by
      have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hM).2 hx
      simpa only [Pi.star_apply, star_trivial] using h)

/-- Hermitian parts of positive definite real matrices are symmetric. -/
private theorem posDef_transpose_eq {M : Matrix (Fin p) (Fin p) ℝ} (hM : M.PosDef) :
    Mᵀ = M := by
  have h := hM.1.eq
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- The logarithmic BLF is dominated by the composite candidate `barrier_V2`. -/
private theorem barrier_V1_le_V2 {Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    (hG : Gamma_inv.PosDef) (kb e1 e2 : ℝ) (theta_tilde : Fin p → ℝ) :
    barrier_V1 kb e1 ≤ barrier_V2 Gamma_inv kb e1 e2 theta_tilde := by
  have h3 := posDef_dotProduct_nonneg hG theta_tilde
  have h4 : 0 ≤ (1 / 2 : ℝ) * (theta_tilde ⬝ᵥ (Gamma_inv *ᵥ theta_tilde)) :=
    mul_nonneg (by norm_num) h3
  have h2 : 0 ≤ (1 / 2 : ℝ) * e2 ^ 2 := by positivity
  dsimp only [barrier_V2]
  linarith

/-- The composite Barrier Lyapunov candidate `barrier_V2` is nonnegative when
`Γ⁻¹` is positive definite and `|e₁| < k_b`. -/
private theorem barrier_V2_nonneg {Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    (hG : Gamma_inv.PosDef) {kb : ℝ} (hkb : 0 < kb)
    (e1 e2 : ℝ) (theta_tilde : Fin p → ℝ) (he1 : |e1| < kb) :
    0 ≤ barrier_V2 Gamma_inv kb e1 e2 theta_tilde :=
  (barrier_V1_nonneg kb e1 hkb he1).trans (barrier_V1_le_V2 hG kb e1 e2 theta_tilde)

/-- Exact parameter-adaptation cancellation: with the adaptation law
`θ̂' = Γ *ᵥ (e₂ • ϕ)` and `Γ⁻¹ * Γ = 1`, the parameter-error derivative term
`θ̃ ⬝ᵥ (Γ⁻¹ *ᵥ (-θ̂'))` equals `-(e₂ * (θ̃ ⬝ᵥ ϕ))`
(Kabziński–Mosiołek, equations 12.37 and 12.39). -/
private theorem barrier_adaptation_cancellation
    (Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ) (e2 : ℝ) (phi theta_tilde : Fin p → ℝ)
    (hGamma_inv : Gamma_inv * Gamma = 1) :
    theta_tilde ⬝ᵥ (Gamma_inv *ᵥ (-(barrier_adaptation_law Gamma e2 phi))) =
      -(e2 * (theta_tilde ⬝ᵥ phi)) := by
  rw [barrier_adaptation_law, Matrix.mulVec_neg, dotProduct_neg]
  congr 1
  simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hGamma_inv, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul]

/-- Exact non-quadratic cross-term cancellation between `V̇₁` and `e₂ ė₂`:
`e₁ e₂ / (k_b² - e₁²) + e₂ (-e₁ / (k_b² - e₁²)) = 0`
(Kabziński–Mosiołek, equation 12.40). -/
theorem barrier_cross_term_cancel (kb e1 e2 : ℝ) :
    (e1 * e2) / (kb ^ 2 - e1 ^ 2) + e2 * (-(e1 / (kb ^ 2 - e1 ^ 2))) = 0 := by
  ring

/-! ### Error dynamics and the composite Lyapunov derivative -/

/-- Closed-loop derivative of the tracking error `e₁ = x₁ - x₁d` along the plant
`x₁' = x₂`: with `α₁ = -k₁ e₁` and `e₂ = x₂ - α₁ - x₁d'`, the error derivative
`e₁' = x₂ - x₁d'` equals `-k₁ e₁ + e₂` (Kabziński–Mosiołek, equations 12.14 and
12.18). -/
theorem barrier_e1_hasDerivAt
    {k1 : ℝ} {x1 x2 x1d x1d' : ℝ → ℝ} {t : ℝ}
    (hx1 : HasDerivAt x1 (x2 t) t)
    (hx1d : HasDerivAt x1d (x1d' t) t) :
    HasDerivAt (fun s ↦ x1 s - x1d s)
      (-k1 * (x1 t - x1d t) + (x2 t - barrier_alpha1 k1 (x1 t - x1d t) - x1d' t)) t := by
  have h := hx1.sub hx1d
  refine h.congr_deriv ?_
  dsimp only [barrier_alpha1]
  ring

/-- Closed-loop derivative of the second error coordinate
`e₂ = x₂ - α₁ - x₁d'` along the plant `x₂' = u + θ ᵀ ϕ` with the barrier control
`u = barrier_control`: the feedforward terms cancel identically and
`e₂' = -e₁ / (k_b² - e₁²) - k₂ e₂ + θ̃ ⬝ᵥ ϕ`
(Kabziński–Mosiołek, equations 12.20 and 12.26). -/
theorem barrier_e2_hasDerivAt
    {k2 kb : ℝ} {theta : Fin p → ℝ}
    {x2 x1d' alpha1 alpha1' x1d'' : ℝ → ℝ}
    {theta_hat phi : ℝ → (Fin p → ℝ)} {e1 e2 : ℝ → ℝ} {t : ℝ}
    (he2 : e2 = fun s ↦ x2 s - alpha1 s - x1d' s)
    (hx2 : HasDerivAt x2
      (barrier_control k2 kb (e1 t) (e2 t) (theta_hat t) (phi t) (x1d'' t) (alpha1' t) +
        (theta ⬝ᵥ phi t)) t)
    (halpha1 : HasDerivAt alpha1 (alpha1' t) t)
    (hx1d' : HasDerivAt x1d' (x1d'' t) t) :
    HasDerivAt e2
      (-(e1 t / (kb ^ 2 - (e1 t) ^ 2)) - k2 * e2 t + ((theta - theta_hat t) ⬝ᵥ phi t)) t := by
  have he2t : e2 t = x2 t - alpha1 t - x1d' t := by rw [he2]
  rw [he2]
  have h := (hx2.sub halpha1).sub hx1d'
  refine h.congr_deriv ?_
  dsimp only [barrier_control]
  rw [he2t, sub_dotProduct]
  ring

/-- Derivative of the composite BLF along closed-loop trajectories:
`V̇₂ = -k₁ e₁² / (k_b² - e₁²) - k₂ e₂²`
(Kabziński–Mosiołek, equations 12.37 and 12.40 for `n = 2`).

The non-quadratic cross term `e₁ e₂ / (k_b² - e₁²)` from `V̇₁` cancels against the
barrier term of the control `u`, and the parameter error `e₂ (θ̃ ⬝ᵥ ϕ)` cancels
against `-θ̃ ⬝ᵥ (Γ⁻¹ *ᵥ θ̂')` via the adaptation law `θ̂' = Γ *ᵥ (e₂ • ϕ)`. -/
theorem barrier_V2_hasDerivAt
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ} {kb k1 k2 : ℝ} (hkb : 0 < kb)
    {e1 e2 : ℝ → ℝ} {theta_hat phi : ℝ → (Fin p → ℝ)} {t : ℝ}
    (he1_bound : |e1 t| < kb)
    (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    (he1 : HasDerivAt e1 (-k1 * e1 t + e2 t) t)
    (he2 : HasDerivAt e2
      (-(e1 t / (kb ^ 2 - (e1 t) ^ 2)) - k2 * e2 t + ((theta - theta_hat t) ⬝ᵥ phi t)) t)
    (htheta_hat : ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((barrier_adaptation_law Gamma (e2 t) (phi t)) j) t) :
    HasDerivAt (fun s ↦ barrier_V2 Gamma_inv kb (e1 s) (e2 s) (theta - theta_hat s))
      (-k1 * (e1 t) ^ 2 / (kb ^ 2 - (e1 t) ^ 2) - k2 * (e2 t) ^ 2) t := by
  have hdiff : ∀ j, HasDerivAt (fun s ↦ (theta - theta_hat s) j)
      (-(barrier_adaptation_law Gamma (e2 t) (phi t)) j) t := by
    intro j
    simpa only [Pi.sub_apply, Pi.neg_apply] using (htheta_hat j).const_sub (theta j)
  have h1 := barrier_V1_hasDerivAt (z' := fun s ↦ -k1 * e1 s + e2 s) hkb he1_bound he1
  have h2 := (he2.pow 2).const_mul (1 / 2 : ℝ)
  have h3 := hasDerivAt_half_quadratic_form
    (u' := -(barrier_adaptation_law Gamma (e2 t) (phi t)))
    Gamma_inv hGamma_inv_symm hdiff
  change HasDerivAt
    (fun s ↦ barrier_V1 kb (e1 s) + (1 / 2 : ℝ) * (e2 s) ^ 2 +
      (1 / 2 : ℝ) * ((theta - theta_hat s) ⬝ᵥ (Gamma_inv *ᵥ (theta - theta_hat s))))
    (-k1 * (e1 t) ^ 2 / (kb ^ 2 - (e1 t) ^ 2) - k2 * (e2 t) ^ 2) t
  refine ((h1.add h2).add h3).congr_deriv ?_
  rw [barrier_adaptation_cancellation Gamma Gamma_inv (e2 t) (phi t) (theta - theta_hat t)
    hGamma_inv]
  ring

/-- Negative semidefiniteness and dissipation bound: along closed-loop
trajectories `deriv V₂ t ≤ -(k₁ / k_b²) e₁² - k₂ e₂²`
(Kabziński–Mosiołek, equation 12.40 and Section 12.2). -/
theorem barrier_V2_deriv_le
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ} {kb k1 k2 : ℝ} (hkb : 0 < kb) (hk1 : 0 ≤ k1)
    {e1 e2 : ℝ → ℝ} {theta_hat phi : ℝ → (Fin p → ℝ)} {t : ℝ}
    (he1_bound : |e1 t| < kb)
    (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    (he1 : HasDerivAt e1 (-k1 * e1 t + e2 t) t)
    (he2 : HasDerivAt e2
      (-(e1 t / (kb ^ 2 - (e1 t) ^ 2)) - k2 * e2 t + ((theta - theta_hat t) ⬝ᵥ phi t)) t)
    (htheta_hat : ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((barrier_adaptation_law Gamma (e2 t) (phi t)) j) t) :
    deriv (fun s ↦ barrier_V2 Gamma_inv kb (e1 s) (e2 s) (theta - theta_hat s)) t ≤
      -(k1 / kb ^ 2) * (e1 t) ^ 2 - k2 * (e2 t) ^ 2 := by
  have hd := barrier_V2_hasDerivAt hkb he1_bound hGamma_inv_symm hGamma_inv he1 he2 htheta_hat
  rw [hd.deriv]
  have hzsq : (e1 t) ^ 2 < kb ^ 2 := by
    rw [abs_lt] at he1_bound
    nlinarith [he1_bound.1, he1_bound.2, hkb]
  have hden : 0 < kb ^ 2 - (e1 t) ^ 2 := by linarith
  have hkb2 : 0 < kb ^ 2 := by positivity
  have hnum : 0 ≤ k1 * (e1 t) ^ 2 := mul_nonneg hk1 (sq_nonneg _)
  have hkey : k1 * (e1 t) ^ 2 / kb ^ 2 ≤ k1 * (e1 t) ^ 2 / (kb ^ 2 - (e1 t) ^ 2) :=
    div_le_div_of_nonneg_left hnum hden (by linarith [sq_nonneg (e1 t)])
  have hneg := neg_le_neg hkey
  have heq1 : -k1 * (e1 t) ^ 2 / (kb ^ 2 - (e1 t) ^ 2) =
      -(k1 * (e1 t) ^ 2 / (kb ^ 2 - (e1 t) ^ 2)) := by ring
  have heq2 : -(k1 / kb ^ 2) * (e1 t) ^ 2 = -(k1 * (e1 t) ^ 2 / kb ^ 2) := by ring
  rw [heq1, heq2]
  linarith [hneg]

/-! ### Forward invariance, output constraint and convergence -/

/-- Theorem 12.1 / Wniosek 12.1: forward domain invariance along closed-loop
trajectories. If `|e₁(0)| < k_b` and the composite BLF is non-increasing
(`V₂(t) ≤ V₂(0)`), then `|e₁(t)| < k_b` for all `t ≥ 0`. Continuity of `e₁` is
used to rule out a boundary crossing and then the algebraic level-set bound
closes the argument. -/
theorem barrier_forward_invariance
    {Gamma_inv : Matrix (Fin p) (Fin p) ℝ} (hGamma_inv_pd : Gamma_inv.PosDef)
    {kb : ℝ} (hkb : 0 < kb)
    {e1 e2 : ℝ → ℝ} {theta_tilde : ℝ → (Fin p → ℝ)}
    (he1_cont : ContinuousOn e1 (Set.Ici 0))
    (he1_0 : |e1 0| < kb)
    (hV_le : ∀ t ≥ 0, barrier_V2 Gamma_inv kb (e1 t) (e2 t) (theta_tilde t) ≤
      barrier_V2 Gamma_inv kb (e1 0) (e2 0) (theta_tilde 0))
    {t : ℝ} (ht : 0 ≤ t) :
    |e1 t| < kb := by
  let M : ℝ := barrier_V2 Gamma_inv kb (e1 0) (e2 0) (theta_tilde 0)
  let c : ℝ := kb * Real.sqrt (1 - Real.exp (-2 * M))
  have hM0 : 0 ≤ M := by
    dsimp only [M]
    exact barrier_V2_nonneg hGamma_inv_pd hkb (e1 0) (e2 0) (theta_tilde 0) he1_0
  have hc_lt : c < kb := by
    have hs : Real.sqrt (1 - Real.exp (-2 * M)) < 1 := by
      rw [Real.sqrt_lt' one_pos]
      have : 0 < Real.exp (-2 * M) := Real.exp_pos _
      nlinarith
    dsimp only [c]
    nlinarith [hkb, hs]
  have hbound : ∀ s, 0 ≤ s → |e1 s| < kb → |e1 s| ≤ c := by
    intro s hs hs'
    have hV1_le : barrier_V1 kb (e1 s) ≤ M := by
      have hle := hV_le s hs
      have hge := barrier_V1_le_V2 hGamma_inv_pd kb (e1 s) (e2 s) (theta_tilde s)
      dsimp only [M] at hle ⊢
      exact hge.trans hle
    have h := barrier_level_set_bound kb (e1 s) M hkb hs' hV1_le
    dsimp only [c]
    exact h
  by_contra hcon
  rw [not_lt] at hcon
  have h0c : |e1 0| ≤ c := hbound 0 le_rfl he1_0
  have hc_mid : c < (c + kb) / 2 := by linarith
  have hmid_lt : (c + kb) / 2 < kb := by linarith
  have h0mid : |e1 0| < (c + kb) / 2 := lt_of_le_of_lt h0c hc_mid
  have hit : (c + kb) / 2 ≤ |e1 t| := by linarith
  have hf : ContinuousOn (fun s ↦ |e1 s|) (Set.Icc 0 t) :=
    (he1_cont.mono (fun x hx ↦ hx.1)).abs
  have hmem : (c + kb) / 2 ∈ Set.Icc (|e1 0|) (|e1 t|) := ⟨le_of_lt h0mid, hit⟩
  obtain ⟨s, hs_mem, hfs⟩ := intermediate_value_Icc ht hf hmem
  change |e1 s| = (c + kb) / 2 at hfs
  have hskb : |e1 s| < kb := by rw [hfs]; exact hmid_lt
  have hle := hbound s hs_mem.1 hskb
  rw [hfs] at hle
  linarith

/-- Hard output constraint satisfaction: if `|x₁d(t)| ≤ x_m`, `k_b = Δ₁ - x_m`
and forward invariance guarantees `|e₁(t)| < k_b`, then `|x₁(t)| < Δ₁` for all
`t ≥ 0` (Kabziński–Mosiołek, equations 12.7–12.8 and Theorem 12.2). Here the
output is `x₁ = e₁ + x₁d`. -/
theorem barrier_output_bounded
    {e1 x1d : ℝ → ℝ} {kb xm Delta1 : ℝ}
    (hDelta : Delta1 = kb + xm)
    (he1 : ∀ t ≥ 0, |e1 t| < kb)
    (hxd : ∀ t ≥ 0, |x1d t| ≤ xm)
    {t : ℝ} (ht : 0 ≤ t) :
    |e1 t + x1d t| < Delta1 := by
  rw [hDelta]
  calc
    |e1 t + x1d t| ≤ |e1 t| + |x1d t| := abs_add_le _ _
    _ < kb + xm := add_lt_add_of_lt_of_le (he1 t ht) (hxd t ht)

/-- Convergence of the dissipation rate `(k₁ / k_b²) e₁² + k₂ e₂² → 0` as
`t → ∞` via the LaSalle–Yoshizawa / Barbălat bridge
(Kabziński–Mosiołek, Theorem 3.7 and Theorem 12.2). -/
theorem barrier_dissipation_tendsto_zero
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ} {kb k1 k2 : ℝ} (hkb : 0 < kb)
    (hk1 : 0 < k1) (hk2 : 0 < k2)
    {e1 e2 : ℝ → ℝ} {theta_hat phi : ℝ → (Fin p → ℝ)}
    (hGamma_inv_pd : Gamma_inv.PosDef)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    (he1_bound : ∀ t ≥ 0, |e1 t| < kb)
    (he1 : ∀ t ≥ 0, HasDerivAt e1 (-k1 * e1 t + e2 t) t)
    (he2 : ∀ t ≥ 0, HasDerivAt e2
      (-(e1 t / (kb ^ 2 - (e1 t) ^ 2)) - k2 * e2 t + ((theta - theta_hat t) ⬝ᵥ phi t)) t)
    (htheta_hat : ∀ t ≥ 0, ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((barrier_adaptation_law Gamma (e2 t) (phi t)) j) t)
    (huc : UniformContinuousOn
      (fun t ↦ (k1 / kb ^ 2) * (e1 t) ^ 2 + k2 * (e2 t) ^ 2) (Set.Ici 0)) :
    Filter.Tendsto (fun t ↦ (k1 / kb ^ 2) * (e1 t) ^ 2 + k2 * (e2 t) ^ 2)
      Filter.atTop (nhds 0) := by
  let V : ℝ → ℝ := fun t ↦ barrier_V2 Gamma_inv kb (e1 t) (e2 t) (theta - theta_hat t)
  let w : ℝ → ℝ := fun t ↦ (k1 / kb ^ 2) * (e1 t) ^ 2 + k2 * (e2 t) ^ 2
  have hG_symm : Gamma_invᵀ = Gamma_inv := posDef_transpose_eq hGamma_inv_pd
  have hw_nonneg : ∀ t, 0 ≤ t → 0 ≤ w t := by
    intro t _
    have h1 : 0 ≤ (k1 / kb ^ 2) * (e1 t) ^ 2 :=
      mul_nonneg (div_nonneg hk1.le (by positivity)) (sq_nonneg _)
    have h2 : 0 ≤ k2 * (e2 t) ^ 2 := mul_nonneg hk2.le (sq_nonneg _)
    dsimp only [w]
    linarith
  have hBdd : BddBelow (V '' Set.Ici 0) := by
    refine ⟨0, ?_⟩
    rintro y ⟨t, ht, rfl⟩
    exact barrier_V2_nonneg hGamma_inv_pd hkb (e1 t) (e2 t) (theta - theta_hat t)
      (he1_bound t ht)
  have hderiv : ∀ t, 0 ≤ t → HasDerivAt V (deriv V t) t := by
    intro t ht
    have h := barrier_V2_hasDerivAt hkb (he1_bound t ht) hG_symm hGamma_inv
      (he1 t ht) (he2 t ht) (htheta_hat t ht)
    change HasDerivAt V (-k1 * (e1 t) ^ 2 / (kb ^ 2 - (e1 t) ^ 2) - k2 * (e2 t) ^ 2) t at h
    exact h.congr_deriv h.deriv.symm
  have hineq : ∀ t, 0 ≤ t → deriv V t ≤ -(w t) := by
    intro t ht
    have h := barrier_V2_deriv_le hkb hk1.le (he1_bound t ht) hG_symm hGamma_inv
      (he1 t ht) (he2 t ht) (htheta_hat t ht)
    change deriv V t ≤ -(k1 / kb ^ 2) * (e1 t) ^ 2 - k2 * (e2 t) ^ 2 at h
    have : -(k1 / kb ^ 2) * (e1 t) ^ 2 - k2 * (e2 t) ^ 2 = -(w t) := by
      dsimp only [w]
      ring
    rwa [this] at h
  simpa only [w] using
    Barbalat.tendsto_zero_of_hasDerivAt_le_neg_of_boundedBelow_of_uniformContinuousOn
      hBdd hw_nonneg hderiv hineq huc

/-- Theorem 12.2: asymptotic tracking convergence. The diagonal dissipation rate
`(k₁ / k_b²) e₁² + k₂ e₂²` dominates each single term, so
`e₁(t) → 0` and `e₂(t) → 0` as `t → ∞`. -/
theorem barrier_tracking_tendsto_zero
    {e1 e2 : ℝ → ℝ} {kb k1 k2 : ℝ} (hkb : 0 < kb)
    (hk1 : 0 < k1) (hk2 : 0 < k2)
    (hw : Filter.Tendsto
      (fun t ↦ (k1 / kb ^ 2) * (e1 t) ^ 2 + k2 * (e2 t) ^ 2)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto e1 Filter.atTop (nhds 0) ∧ Filter.Tendsto e2 Filter.atTop (nhds 0) := by
  have hc1 : 0 < k1 / kb ^ 2 := div_pos hk1 (by positivity)
  constructor
  · refine Barbalat.tendsto_zero_of_tendsto_zero_of_sq_le (c := k1 / kb ^ 2) hc1 hw ?_
    intro t _
    have h2 : 0 ≤ k2 * (e2 t) ^ 2 := mul_nonneg hk2.le (sq_nonneg _)
    linarith
  · refine Barbalat.tendsto_zero_of_tendsto_zero_of_sq_le (c := k2) hk2 hw ?_
    intro t _
    have h1 : 0 ≤ (k1 / kb ^ 2) * (e1 t) ^ 2 :=
      mul_nonneg (div_nonneg hk1.le (by positivity)) (sq_nonneg _)
    linarith
