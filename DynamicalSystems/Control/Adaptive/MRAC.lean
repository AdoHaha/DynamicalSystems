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
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import DynamicalSystems.Linear.LyapunovEquation
public import DynamicalSystems.Stability.Barbalat

/-!
# Model Reference Adaptive Control (MRAC) for nonlinear systems

This file formalizes the core of the classical Model Reference Adaptive Control
(MRAC) architecture for multi-input nonlinear systems with matched parametric
uncertainty, following Kabziński and Mosiołek, *Projektowanie nieliniowych
układów sterowania*, Komitet Automatyki i Robotyki PAN, Monografie tom 22,
Chapter 5, Section 5.2, pages 64–66, Theorems 5.1 and 5.2, equations
(5.39)–(5.52).

## System description

The plant is an `m`-input nonlinear system with matched parametric uncertainty
```
x' = A x + B (ξ(x)ᵀ θ + u)
```
where `θ ∈ ℝᵖ` is an unknown constant parameter vector, `ξ(x) ∈ ℝᵖˣᵐ` is a
known state-dependent regressor matrix, and `A`, `B` are known plant matrices.
The reference model is the linear Hurwitz system
```
xₘ' = Aₘ xₘ + Bₘ v
```
satisfying the matching conditions `Aₘ = A - B K₁` and `Bₘ = B K₂`.

With the control law `u = -K₁ x + K₂ v - ξ(x)ᵀ θ̂`, the tracking error
`e = x - xₘ` satisfies
```
e' = Aₘ e + B ξ(x)ᵀ θ̃,   θ̃ = θ - θ̂.
```
The adaptation law is `θ̂' = Γ ξ(x) Bᵀ P e`, where `P` solves the matrix
Lyapunov equation `Aₘᵀ P + P Aₘ = -2 Q` for `Q > 0` and `Γ > 0` is the
adaptation gain matrix.

## Main definitions

* `mrac_V`: composite quadratic Lyapunov candidate `V(e, θ̃)` (equation 5.48).
* `mrac_adaptation_law`: parameter adaptation vector field `θ̂'` (equation 5.44).

## Main results

* `mrac_error_dynamics_algebra`: reduction of the matched plant and reference
  model to the error dynamics (equations 5.46–5.47).
* `mrac_lyapunov_hasDerivAt`: the closed-loop derivative identity
  `V̇ = -eᵀ Q e` (equation 5.51).
* `mrac_dissipation_tendsto_zero`: Barbălat decay of the dissipation rate
  `eᵀ Q e → 0` (equation 5.52).
* `mrac_tracking_tendsto_zero`: asymptotic coordinate tracking `eᵢ(t) → 0`
  (Theorem 5.2).

## References

* J. Kabziński, P. Mosiołek, *Projektowanie nieliniowych układów sterowania*,
  Komitet Automatyki i Robotyki PAN, Monografie tom 22, Chapter 5, Section 5.2.
-/

open scoped Matrix

variable {n m p r : ℕ}

@[expose] public section

/-! ### Definitions -/

/-- Composite quadratic Lyapunov candidate for MRAC:
`V(e, θ̃) = (1/2) * (e ⬝ᵥ (P *ᵥ e)) + (1/2) * (θ̃ ⬝ᵥ (Γ⁻¹ *ᵥ θ̃))`
(Kabziński–Mosiołek, equation 5.48). -/
-- The underscore in `mrac_V` is mandated by the campaign's required-declaration
-- list, so the naming linter is disabled for this def.
@[nolint defsWithUnderscore]
noncomputable def mrac_V
    (P : Matrix (Fin n) (Fin n) ℝ) (Gamma_inv : Matrix (Fin p) (Fin p) ℝ)
    (e : Fin n → ℝ) (theta_tilde : Fin p → ℝ) : ℝ :=
  (1 / 2 : ℝ) * (e ⬝ᵥ (P *ᵥ e)) + (1 / 2 : ℝ) * (theta_tilde ⬝ᵥ (Gamma_inv *ᵥ theta_tilde))

/-- Adaptation vector field for the MRAC parameter estimate:
`θ̂' = Γ *ᵥ (ξ *ᵥ (Bᵀ *ᵥ (P *ᵥ e)))` (Kabziński–Mosiołek, equation 5.44). -/
-- The underscore in `mrac_adaptation_law` is mandated by the campaign's
-- required-declaration list, so the naming linter is disabled for this def.
@[nolint defsWithUnderscore]
def mrac_adaptation_law
    (Gamma : Matrix (Fin p) (Fin p) ℝ) (xi : Matrix (Fin p) (Fin m) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (e : Fin n → ℝ) : Fin p → ℝ :=
  Gamma *ᵥ (xi *ᵥ (Bᵀ *ᵥ (P *ᵥ e)))

/-! ### Internal algebraic and calculus helpers -/

/-- Algebraic reduction of the MRAC tracking error dynamics: under the matching
conditions `Aₘ = A - B * K₁` and `Bₘ = B * K₂`, the feedback control
`u = -K₁ x + K₂ v - ξᵀ θ̂` reduces the error derivative `x' - xₘ'` to
`Aₘ e + B (ξᵀ θ̃)` (Kabziński–Mosiołek, equations 5.46–5.47). -/
theorem mrac_error_dynamics_algebra
    (A Am : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Bm : Matrix (Fin n) (Fin r) ℝ) (K1 : Matrix (Fin m) (Fin n) ℝ)
    (K2 : Matrix (Fin m) (Fin r) ℝ) (xi : Matrix (Fin p) (Fin m) ℝ)
    (theta theta_hat : Fin p → ℝ) (x xm : Fin n → ℝ) (v : Fin r → ℝ)
    (hAm : Am = A - B * K1) (hBm : Bm = B * K2) :
    let u := -(K1 *ᵥ x) + K2 *ᵥ v - xiᵀ *ᵥ theta_hat
    let x_dot := A *ᵥ x + B *ᵥ (xiᵀ *ᵥ theta + u)
    let xm_dot := Am *ᵥ xm + Bm *ᵥ v
    let e := x - xm
    let theta_tilde := theta - theta_hat
    x_dot - xm_dot = Am *ᵥ e + B *ᵥ (xiᵀ *ᵥ theta_tilde) := by
  subst hAm hBm
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.mulVec_neg,
    ← Matrix.mulVec_mulVec]
  abel

/-- Transpose swap identity for the state-error coupling with parameter
uncertainty: for symmetric `P`, the scalar
`e ⬝ᵥ (P *ᵥ (B *ᵥ (ξᵀ *ᵥ θ̃)))` equals the transposed adaptation coupling
`θ̃ ⬝ᵥ (ξ *ᵥ (Bᵀ *ᵥ (P *ᵥ e)))` (Kabziński–Mosiołek, equation 5.50). -/
private theorem mrac_cancellation_algebra
    (P : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (xi : Matrix (Fin p) (Fin m) ℝ) (e : Fin n → ℝ) (theta_tilde : Fin p → ℝ)
    (hP_symm : Pᵀ = P) :
    e ⬝ᵥ (P *ᵥ (B *ᵥ (xiᵀ *ᵥ theta_tilde))) =
      theta_tilde ⬝ᵥ (xi *ᵥ (Bᵀ *ᵥ (P *ᵥ e))) := by
  have step1 : e ⬝ᵥ (P *ᵥ (B *ᵥ (xiᵀ *ᵥ theta_tilde))) =
      (B *ᵥ (xiᵀ *ᵥ theta_tilde)) ⬝ᵥ (P *ᵥ e) := by
    have h := Matrix.dotProduct_transpose_mulVec P e (B *ᵥ (xiᵀ *ᵥ theta_tilde))
    rwa [hP_symm] at h
  have step2 : (B *ᵥ (xiᵀ *ᵥ theta_tilde)) ⬝ᵥ (P *ᵥ e) =
      (xiᵀ *ᵥ theta_tilde) ⬝ᵥ (Bᵀ *ᵥ (P *ᵥ e)) := by
    rw [dotProduct_comm]
    exact (Matrix.dotProduct_transpose_mulVec B (xiᵀ *ᵥ theta_tilde) (P *ᵥ e)).symm
  have step3 : (xiᵀ *ᵥ theta_tilde) ⬝ᵥ (Bᵀ *ᵥ (P *ᵥ e)) =
      theta_tilde ⬝ᵥ (xi *ᵥ (Bᵀ *ᵥ (P *ᵥ e))) := by
    rw [dotProduct_comm]
    exact Matrix.dotProduct_transpose_mulVec xi (Bᵀ *ᵥ (P *ᵥ e)) theta_tilde
  rw [step1, step2, step3]

/-- Exact parameter-adaptation cancellation: with the adaptation law
`θ̂' = Γ *ᵥ (ξ *ᵥ (Bᵀ *ᵥ (P *ᵥ e)))` and `Γ⁻¹ * Γ = 1`, the parameter-error
derivative term `θ̃ ⬝ᵥ (Γ⁻¹ *ᵥ (-θ̂'))` cancels the cross term
(Kabziński–Mosiołek, equations 5.49–5.50). -/
private theorem mrac_adaptation_cancellation
    (P : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (xi : Matrix (Fin p) (Fin m) ℝ) (Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ)
    (e : Fin n → ℝ) (theta_tilde : Fin p → ℝ)
    (hGamma_inv : Gamma_inv * Gamma = 1) :
    theta_tilde ⬝ᵥ (Gamma_inv *ᵥ (-(mrac_adaptation_law Gamma xi B P e))) =
      - (theta_tilde ⬝ᵥ (xi *ᵥ (Bᵀ *ᵥ (P *ᵥ e)))) := by
  rw [Matrix.mulVec_neg, dotProduct_neg, mrac_adaptation_law]
  congr 1
  rw [Matrix.mulVec_mulVec, hGamma_inv, Matrix.one_mulVec]

/-- Product rule for the dot product of two vector trajectories. -/
private theorem hasDerivAt_dotProduct
    {u v : ℝ → (Fin n → ℝ)} {u' v' : Fin n → ℝ} {t : ℝ}
    (hu : ∀ i, HasDerivAt (fun s ↦ u s i) (u' i) t)
    (hv : ∀ i, HasDerivAt (fun s ↦ v s i) (v' i) t) :
    HasDerivAt (fun s ↦ (u s) ⬝ᵥ (v s)) (u' ⬝ᵥ (v t) + (u t) ⬝ᵥ v') t := by
  simp only [dotProduct]
  have h : HasDerivAt (∑ i ∈ (Finset.univ : Finset (Fin n)), fun s ↦ u s i * v s i)
      (∑ i ∈ (Finset.univ : Finset (Fin n)), (u' i * v t i + u t i * v' i)) t :=
    HasDerivAt.sum (fun i _ ↦ (hu i).mul (hv i))
  have hfun : (fun s ↦ ∑ i, u s i * v s i) =
      (∑ i ∈ (Finset.univ : Finset (Fin n)), fun s ↦ u s i * v s i) := by
    funext s
    rw [Finset.sum_apply]
  rw [hfun]
  exact h.congr_deriv Finset.sum_add_distrib

/-- Differentiating a constant matrix product `s ↦ M *ᵥ u s` coordinate-wise. -/
private theorem hasDerivAt_mulVec
    (M : Matrix (Fin n) (Fin n) ℝ) {u : ℝ → (Fin n → ℝ)} {u' : Fin n → ℝ} {t : ℝ}
    (hu : ∀ j, HasDerivAt (fun s ↦ u s j) (u' j) t) (i : Fin n) :
    HasDerivAt (fun s ↦ (M *ᵥ (u s)) i) ((M *ᵥ u') i) t := by
  simp only [Matrix.mulVec, dotProduct]
  have h : HasDerivAt (∑ j ∈ (Finset.univ : Finset (Fin n)), fun s ↦ M i j * u s j)
      (∑ j ∈ (Finset.univ : Finset (Fin n)), M i j * u' j) t :=
    HasDerivAt.sum (fun j _ ↦ (hu j).const_mul (M i j))
  have hfun : (fun s ↦ ∑ x, M i x * u s x) =
      (∑ j ∈ (Finset.univ : Finset (Fin n)), fun s ↦ M i j * u s j) := by
    funext s
    rw [Finset.sum_apply]
  rw [hfun]
  exact h

/-- Derivative of a quadratic form `s ↦ (1/2) * (u s ⬝ᵥ (M *ᵥ u s))` along a
vector trajectory for a symmetric matrix `M`. -/
private theorem hasDerivAt_half_quadratic_form
    (M : Matrix (Fin n) (Fin n) ℝ) (hM_symm : Mᵀ = M)
    {u : ℝ → (Fin n → ℝ)} {u' : Fin n → ℝ} {t : ℝ}
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

/-- Bridge from the matrix Lyapunov equation to the Lyapunov derivative: if
`Aₘᵀ * P + P * Aₘ = -(2 • Q)` and `P` is symmetric, then
`e ⬝ᵥ (P *ᵥ (Aₘ *ᵥ e)) = -(e ⬝ᵥ (Q *ᵥ e))`
(Kabziński–Mosiołek, equation 5.51). -/
private theorem mrac_lyapunov_derivative_algebra
    {Am Q P : Matrix (Fin n) (Fin n) ℝ}
    (hlyap : Amᵀ * P + P * Am = -((2 : ℝ) • Q))
    (hP_symm : Pᵀ = P) (e : Fin n → ℝ) :
    e ⬝ᵥ (P *ᵥ (Am *ᵥ e)) = -(e ⬝ᵥ (Q *ᵥ e)) := by
  have hqf := matrix_lyapunov_equation_quadratic_form (A := Am) (Q := (2 : ℝ) • Q)
    (P := P) hlyap e
  have hsym : (Am *ᵥ e) ⬝ᵥ (P *ᵥ e) = e ⬝ᵥ (P *ᵥ (Am *ᵥ e)) := by
    have h := Matrix.dotProduct_transpose_mulVec P (Am *ᵥ e) e
    rwa [hP_symm] at h
  have hsmul : e ⬝ᵥ (((2 : ℝ) • Q) *ᵥ e) = 2 * (e ⬝ᵥ (Q *ᵥ e)) := by
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [hsym, hsmul] at hqf
  linarith

/-! ### Closed-loop stability -/

/-- The composite Lyapunov function `mrac_V` satisfies the closed-loop
dissipation identity `V̇ = -e(t) ⬝ᵥ (Q *ᵥ e(t))` along trajectories of the MRAC
system (Kabziński–Mosiołek, equation 5.51). -/
theorem mrac_lyapunov_hasDerivAt
    {Am P Q : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin m) ℝ}
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ}
    {e : ℝ → (Fin n → ℝ)} {theta_hat : ℝ → (Fin p → ℝ)}
    {xi : ℝ → Matrix (Fin p) (Fin m) ℝ}
    (hlyap : Amᵀ * P + P * Am = -((2 : ℝ) • Q))
    (hP_symm : Pᵀ = P) (hGamma_inv_symm : Gamma_invᵀ = Gamma_inv)
    (hGamma_inv : Gamma_inv * Gamma = 1)
    {t : ℝ}
    (he : ∀ i, HasDerivAt (fun s ↦ e s i)
      ((Am *ᵥ e t + B *ᵥ ((xi t)ᵀ *ᵥ (theta - theta_hat t))) i) t)
    (htheta_hat : ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((mrac_adaptation_law Gamma (xi t) B P (e t)) j) t) :
    HasDerivAt (fun s ↦ mrac_V P Gamma_inv (e s) (theta - theta_hat s))
      (-(e t ⬝ᵥ (Q *ᵥ e t))) t := by
  have hdiff : ∀ j, HasDerivAt (fun s ↦ (theta - theta_hat s) j)
      (-(mrac_adaptation_law Gamma (xi t) B P (e t)) j) t := by
    intro j
    simpa only [Pi.sub_apply] using (htheta_hat j).const_sub (theta j)
  have h1 := hasDerivAt_half_quadratic_form P hP_symm he
  have h2 := hasDerivAt_half_quadratic_form Gamma_inv hGamma_inv_symm hdiff
  have hfun : (fun s ↦ mrac_V P Gamma_inv (e s) (theta - theta_hat s)) =
      (fun s ↦ (1 / 2 : ℝ) * ((e s) ⬝ᵥ (P *ᵥ (e s)))
        + (1 / 2 : ℝ) * ((theta - theta_hat s) ⬝ᵥ (Gamma_inv *ᵥ (theta - theta_hat s)))) := by
    funext s
    rfl
  rw [hfun]
  refine (h1.add h2).congr_deriv ?_
  rw [Matrix.mulVec_add, dotProduct_add]
  rw [show (fun j ↦ -(mrac_adaptation_law Gamma (xi t) B P (e t)) j) =
      -(mrac_adaptation_law Gamma (xi t) B P (e t)) from rfl]
  rw [mrac_adaptation_cancellation P B (xi t) Gamma Gamma_inv (e t)
    (theta - theta_hat t) hGamma_inv]
  rw [mrac_cancellation_algebra P B (xi t) (e t) (theta - theta_hat t) hP_symm]
  rw [mrac_lyapunov_derivative_algebra hlyap hP_symm (e t)]
  ring

/-- Positive semidefiniteness of a quadratic form for a positive definite real
matrix. -/
private theorem posDef_dotProduct_nonneg {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosDef) (x : Fin n → ℝ) : 0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  rcases eq_or_ne x 0 with hx | hx
  · subst hx
    simp
  · exact le_of_lt (by
      have h := (Matrix.posDef_iff_dotProduct_mulVec.mp hM).2 hx
      simpa only [Pi.star_apply, star_trivial] using h)

/-- The composite Lyapunov candidate is nonnegative when `P` and `Γ⁻¹` are
positive definite. -/
private theorem mrac_V_nonneg {P : Matrix (Fin n) (Fin n) ℝ}
    {Gamma_inv : Matrix (Fin p) (Fin p) ℝ} (hP : P.PosDef) (hG : Gamma_inv.PosDef)
    (e : Fin n → ℝ) (theta_tilde : Fin p → ℝ) : 0 ≤ mrac_V P Gamma_inv e theta_tilde := by
  have h1 := posDef_dotProduct_nonneg hP e
  have h2 := posDef_dotProduct_nonneg hG theta_tilde
  simp only [mrac_V]
  nlinarith [h1, h2]

/-- Hermitian parts of positive definite real matrices are symmetric. -/
private theorem posDef_transpose_eq {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosDef) :
    Mᵀ = M := by
  have h := hM.1.eq
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- Convergence of the dissipation rate `e(t) ⬝ᵥ (Q *ᵥ e(t)) → 0` as `t → ∞`
via the LaSalle–Yoshizawa / Barbălat bridge (Kabziński–Mosiołek, equation 5.52).

The argument is the standard one: `V ≥ 0` is decreasing along trajectories with
`V̇ = -eᵀ Q e ≤ 0`, hence bounded below; uniform continuity of the dissipation
rate makes Barbălat's lemma applicable. -/
theorem mrac_dissipation_tendsto_zero
    {Am P Q : Matrix (Fin n) (Fin n) ℝ} {B : Matrix (Fin n) (Fin m) ℝ}
    {Gamma Gamma_inv : Matrix (Fin p) (Fin p) ℝ}
    {theta : Fin p → ℝ}
    {e : ℝ → (Fin n → ℝ)} {theta_hat : ℝ → (Fin p → ℝ)}
    {xi : ℝ → Matrix (Fin p) (Fin m) ℝ}
    (hP_pd : P.PosDef) (hGamma_inv_pd : Gamma_inv.PosDef)
    (hQ_pd : Q.PosDef)
    (hlyap : Amᵀ * P + P * Am = -((2 : ℝ) • Q))
    (hGamma_inv : Gamma_inv * Gamma = 1)
    (he : ∀ t ≥ 0, ∀ i, HasDerivAt (fun s ↦ e s i)
      ((Am *ᵥ e t + B *ᵥ ((xi t)ᵀ *ᵥ (theta - theta_hat t))) i) t)
    (htheta_hat : ∀ t ≥ 0, ∀ j, HasDerivAt (fun s ↦ theta_hat s j)
      ((mrac_adaptation_law Gamma (xi t) B P (e t)) j) t)
    (huc : UniformContinuousOn (fun t ↦ e t ⬝ᵥ (Q *ᵥ e t)) (Set.Ici 0)) :
    Filter.Tendsto (fun t ↦ e t ⬝ᵥ (Q *ᵥ e t)) Filter.atTop (nhds 0) := by
  let V : ℝ → ℝ := fun t ↦ mrac_V P Gamma_inv (e t) (theta - theta_hat t)
  let w : ℝ → ℝ := fun t ↦ e t ⬝ᵥ (Q *ᵥ e t)
  have hP_symm : Pᵀ = P := posDef_transpose_eq hP_pd
  have hG_symm : Gamma_invᵀ = Gamma_inv := posDef_transpose_eq hGamma_inv_pd
  have hw_nonneg : ∀ t, 0 ≤ t → 0 ≤ w t := by
    intro t _
    exact posDef_dotProduct_nonneg hQ_pd (e t)
  have hBdd : BddBelow (V '' Set.Ici 0) := by
    refine ⟨0, ?_⟩
    rintro y ⟨t, _ht, rfl⟩
    exact mrac_V_nonneg hP_pd hGamma_inv_pd (e t) (theta - theta_hat t)
  have hVderiv : ∀ t, 0 ≤ t → HasDerivAt V (-(w t)) t := by
    intro t ht
    simpa only [V, w] using
      mrac_lyapunov_hasDerivAt hlyap hP_symm hG_symm hGamma_inv (he t ht) (htheta_hat t ht)
  have hderiv : ∀ t, 0 ≤ t → HasDerivAt V (deriv V t) t := by
    intro t ht
    exact (hVderiv t ht).congr_deriv (hVderiv t ht).deriv.symm
  have hineq : ∀ t, 0 ≤ t → deriv V t ≤ -(w t) := by
    intro t ht
    exact le_of_eq (hVderiv t ht).deriv
  simpa only [w] using
    Barbalat.tendsto_zero_of_hasDerivAt_le_neg_of_boundedBelow_of_uniformContinuousOn
      hBdd hw_nonneg hderiv hineq huc

/-- Asymptotic tracking convergence of the MRAC system: if the dissipation rate
`e(t) ⬝ᵥ (Q *ᵥ e(t))` tends to zero and the quadratic form dominates each
coordinate with coercivity constant `c > 0`, then each error coordinate
`eᵢ(t) → 0` as `t → ∞` (Kabziński–Mosiołek, Theorem 5.2). -/
theorem mrac_tracking_tendsto_zero
    {Q : Matrix (Fin n) (Fin n) ℝ} {e : ℝ → (Fin n → ℝ)} {c : ℝ} (hc : 0 < c)
    (hw : Filter.Tendsto (fun t ↦ e t ⬝ᵥ (Q *ᵥ e t)) Filter.atTop (nhds 0))
    (hcoer : ∀ t, 0 ≤ t → ∀ i, c * (e t i) ^ 2 ≤ e t ⬝ᵥ (Q *ᵥ e t)) :
    ∀ i, Filter.Tendsto (fun t ↦ e t i) Filter.atTop (nhds 0) := by
  intro i
  exact Barbalat.tendsto_zero_of_tendsto_zero_of_sq_le (e := fun t ↦ e t i)
    (w := fun t ↦ e t ⬝ᵥ (Q *ᵥ e t)) hc hw (fun t ht ↦ hcoer t ht i)
