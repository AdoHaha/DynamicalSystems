/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.SlidingMode.DiscreteMatrix
public import DynamicalSystems.DiscreteTime.MatrixLyapunov
public import DynamicalSystems.DiscreteTime.UltimateBoundedness
public import DynamicalSystems.Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # LMI-based design of a discrete-time sliding surface

This file formalizes the implication from the linear-matrix-inequality (LMI)
surface-design condition of A. Argha, S. W. Su, L. Li and H. T. Nguyen,
*Advances in Discrete-Time Sliding Mode Control: Theory and Applications*,
CRC Press 2018, Chapter 2, §2.3 (printed pp. 31–40), to the discrete
quadratic-form decrease of the closed loop. As in the campaign contract, only
the **implication** "the LMI holds ⇒ the surface/closed loop decreases" is
proved here; **feasibility** of the LMI (existence of a solution to the
semidefinite program) is not attempted.

The book's Theorem 2.1 (printed p. 35, LMI (2.24)) states that the linear part
of the control law (2.12) drives the state onto the sliding surface (2.6) and
stabilizes the plant if a large block LMI in the variables `P̄ ≻ 0`, `X`, `Y`,
`ε > 0`, `η̄ > 0` is feasible, with surface matrix `S = Bᵀ P̄⁻¹` and
`P = P̄⁻¹`. Its proof repeatedly uses the Schur complement to reduce the block
LMI to the matrix inequality `Ω₁₁ < -ηI` of eq. (2.28) (printed p. 36), which is
the discrete Lyapunov condition `(P - Aᵀ P A) ≻ 0` of the unforced closed loop.
The key objects here are:

* `dsmcSurfaceLMI A P`: the strict positive-definite block (Schur) form
  `[[P, AᵀP], [PA, P]] ≻ 0`, which is the surface-design LMI reduced to its
  algebraic core;
* `dsmc_sliding_surface_lmi`: the Schur-complement reduction of that block LMI
  to `P ≻ 0` and `(P - Aᵀ P A) ≻ 0`, and hence to a strict decrease of the
  quadratic form `quadForm P` along `A` (the equivalent closed loop of
  `DynamicalSystems.Control.SlidingMode.DiscreteMatrix`);
* `dsmc_lyapunov_decrease_of_lmi`: the one-step decrease
  `(P - Aᵀ P A) ≻ 0 ⇒ quadForm P (A x) < quadForm P x`, which is the
  discrete-Lyapunov inequality already contained in
  `DynamicalSystems.DiscreteTime.MatrixLyapunov` (`quadForm_mulVec_lt`) and is
  cited here rather than reproved;
* `dsmc_reaching_with_disturbance_bound`: the disturbance-bound robustness of
  §2.3.1 (printed pp. 33–34), i.e. the compensation error `‖f(k) - ϑ(k)‖ ≤ τ F⁻`
  of (2.13) together with the ultimate bound it induces on the closed loop
  through the discrete comparison estimate
  `eventually_le_add_of_succ_le_mul_add`;
* `dsmc_lmi_geometric_decay`: the geometric decay
  `quadForm P (Aᵏ x) ≤ cᵏ quadForm P x` with `c ∈ [0, 1)` that iterates
  `dsmc_lyapunov_decrease_of_lmi` and realises the conclusion `∆V ≤ -ρV` of
  Remark 2.3 (printed p. 37).

## Implementation notes

The strict `PosDef` block Schur complement
`Matrix.posDef_fromBlocks₂₂_iff`/`₁₁_iff` used below lives in
`DynamicalSystems.Mathlib.LinearAlgebra.Matrix.SchurComplement`; it is itself
built on Mathlib's `Matrix.fromBlocks_eq_of_invertible₂₂` LDU factorization.
The discrete decrease is *not* reproved: it is `quadForm_mulVec_lt` of
`DynamicalSystems.DiscreteTime.MatrixLyapunov`. In particular no use is made of
the continuous-time `Linear.*.IsHurwitz`.

The task sketch listed a hypothesis `hP : P.PosDef` on
`dsmc_lyapunov_decrease_of_lmi`. That hypothesis is **unnecessary** for the
one-step decrease: `(P - Aᵀ P A) ≻ 0` alone yields
`quadForm P (A x) < quadForm P x` for `x ≠ 0` (e.g. `P = -1`, `A = 2`), and the
proof of `quadForm_mulVec_lt` never uses `P ≻ 0`. It has therefore been dropped,
in keeping with the campaign rule that unused hypotheses must be removed; `P ≻ 0`
is used where the book actually needs it, in the coercivity/nonnegativity of the
Lyapunov function `xᵀ P x` (Theorem 2.2, printed p. 37).

## Correction to the LMI encoding (recorded for the campaign)

The book's block LMI (2.24) (Theorem 2.1, printed p. 35) is a large
seven-block-row matrix in the free variables `P̄ ≻ 0`, `X`, `Y`, `ε`, `η̄` and the
uncertainty model `∆A = M F N` of eq. (2.2). This file formalizes the
Schur-complement **core** of that LMI, namely the equivalence between the block
condition `[[P, AᵀP], [PA, P]] ≻ 0` and `P ≻ 0 ∧ (P - Aᵀ P A) ≻ 0`; the
auxiliary variables `X`, `Y` and the uncertainty blocks `M`, `N` are *not*
encoded, so `dsmcSurfaceLMI` is strictly the algebraic reduction the book derives
in (2.29)–(2.31) (printed pp. 35–36) rather than the literal LMI (2.24). This is
the honest boundary of the slice: it proves the implication “the surface LMI (in
reduced form) holds ⇒ the equivalent closed loop decreases”, and it neither
claims nor proves feasibility of the full LMI (2.24).
-/

@[expose] public section

open Matrix
open scoped Topology

variable {n : ℕ}

/-- **Discrete Lyapunov LMI ⇒ quadratic-form decrease** (A. Argha, S. W. Su,
L. Li and H. T. Nguyen, *Advances in Discrete-Time Sliding Mode Control: Theory
and Applications*, CRC Press 2018, Theorem 2.1 and eq. (2.28), printed pp. 35–36).

If the matrix inequality `P - Aᵀ P A` is positive definite, then one step of the
linear map `A` strictly decreases the quadratic form `quadForm P x = xᵀ P x` on
every non-zero vector. This is the disturbance-free core of the book's
closed-loop stability argument, `Ω₁₁ < -ηI` in eq. (2.28): the equivalent
closed-loop matrix of the sliding surface plays the role of `A`.

The statement is exactly the discrete Lyapunov decrease of
`DynamicalSystems.DiscreteTime.MatrixLyapunov`, which is cited here
(`quadForm_mulVec_lt` with `Q = P` and `M = A`) rather than reproved. No
continuous-time `IsHurwitz` hypothesis is involved. As recorded in the module
docstring, the positive definiteness of `P` is not needed for this one-step
inequality. -/
theorem dsmc_lyapunov_decrease_of_lmi {A P : Matrix (Fin n) (Fin n) ℝ}
    (hLMI : (P - Aᵀ * P * A).PosDef) {x : Fin n → ℝ} (hx : x ≠ 0) :
    quadForm P (A *ᵥ x) < quadForm P x :=
  quadForm_mulVec_lt hLMI hx

/-- The strict positive-definite block (Schur) **sliding-surface LMI** in the
state matrix `A` and the Lyapunov matrix `P`:
`[[P, AᵀP], [PA, P]] ≻ 0`. It is the algebraic core of the block LMI (2.24) of
A. Argha, S. W. Su, L. Li and H. T. Nguyen, *Advances in Discrete-Time Sliding
Mode Control: Theory and Applications*, CRC Press 2018, Theorem 2.1,
printed p. 35, with the surface parameterization `S = Bᵀ P̄⁻¹` and `P = P̄⁻¹`
(printed p. 35). By the strict Schur complement
`Matrix.posDef_fromBlocks₂₂_iff` it is equivalent to `P ≻ 0` together with
`P - Aᵀ P A ≻ 0`; the latter is the matrix-inequality form `Ω₁₁ < -ηI` of
eq. (2.28), printed p. 36. -/
def dsmcSurfaceLMI (A P : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (fromBlocks P (Aᵀ * P) (P * A) P).PosDef

/-- **The sliding-surface LMI implies the decrease** (A. Argha, S. W. Su, L. Li
and H. T. Nguyen, *Advances in Discrete-Time Sliding Mode Control: Theory and
Applications*, CRC Press 2018, Theorem 2.1, LMI (2.24), printed p. 35, and its
Schur-complement reduction (2.29)–(2.31) to eq. (2.28), printed pp. 35–36).

If the block LMI `[[P, AᵀP], [PA, P]] ≻ 0` is satisfied, then `P` is positive
definite and the Schur complement `P - Aᵀ P A` is positive definite; consequently
the quadratic form `quadForm P` strictly decreases along one step of `A` on every
non-zero vector. The Schur-complement step is provided by
`Matrix.posDef_fromBlocks₂₂_iff` of
`DynamicalSystems.Mathlib.LinearAlgebra.Matrix.SchurComplement`, and the decrease
by `dsmc_lyapunov_decrease_of_lmi`. This is the book's "the surface LMI holds ⇒
the closed loop is stabilized / the surface is attractive" implication, stated
without any claim about feasibility of the LMI.

In the book's application `A` is the equivalent closed-loop matrix
`dsmcEquivalentClosedLoop A₀ B C = A₀ - B (C B)⁻¹ C A₀` of
`DynamicalSystems.Control.SlidingMode.DiscreteMatrix` for the plant `(A₀, B)` and
surface matrix `C`; the corresponding surface `{x | C x = 0}` is then invariant
(`dsmcEquivalentClosedLoop_slidingVariable`). -/
theorem dsmc_sliding_surface_lmi {A P : Matrix (Fin n) (Fin n) ℝ}
    (hLMI : dsmcSurfaceLMI A P) :
    P.PosDef ∧ (P - Aᵀ * P * A).PosDef ∧
      (∀ x : Fin n → ℝ, x ≠ 0 → quadForm P (A *ᵥ x) < quadForm P x) := by
  unfold dsmcSurfaceLMI at hLMI
  have hPsub : (fromBlocks P (Aᵀ * P) (P * A) P).submatrix Sum.inr Sum.inr = P := by
    ext i j
    simp [fromBlocks_apply₂₂]
  have hP : P.PosDef := hPsub ▸ hLMI.submatrix Sum.inr_injective
  have hherm : Pᵀ = P := hP.isHermitian.eq
  have hunit : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.isUnit
  have hblock : (fromBlocks P (Aᵀ * P) (Aᵀ * P)ᵀ P).PosDef := by
    convert hLMI using 2
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, hherm]
  have hinst : Invertible P := hP.isUnit.invertible
  have hschur : (P - (Aᵀ * P) * ⅟P * (Aᵀ * P)ᵀ).PosDef :=
    (Matrix.posDef_fromBlocks₂₂_iff P (Aᵀ * P) P).mp hblock |>.2
  have hS : (Aᵀ * P) * ⅟P * (Aᵀ * P)ᵀ = Aᵀ * P * A := by
    rw [invOf_eq_nonsing_inv, Matrix.transpose_mul, Matrix.transpose_transpose, hherm]
    rw [Matrix.mul_assoc Aᵀ P P⁻¹, Matrix.mul_nonsing_inv P hunit, Matrix.mul_one,
      Matrix.mul_assoc Aᵀ P A]
  have hPsd : (P - Aᵀ * P * A).PosDef := by
    rw [← hS]
    exact hschur
  exact ⟨hP, hPsd, fun x hx ↦ dsmc_lyapunov_decrease_of_lmi hPsd hx⟩

/-- **Geometric decay from the Lyapunov LMI** (A. Argha, S. W. Su, L. Li and
H. T. Nguyen, *Advances in Discrete-Time Sliding Mode Control: Theory and
Applications*, CRC Press 2018, Theorem 2.1 and Remark 2.3, printed pp. 35–37).

A positive-definite `P` with `(P - Aᵀ P A) ≻ 0` yields a uniform contraction
factor `c ∈ [0, 1)` for the quadratic form: `quadForm P (A x) ≤ c quadForm P x`
for every `x`. Iterating, `quadForm P (Aᵏ x) ≤ cᵏ quadForm P x`, i.e. the
quadratic Lyapunov function decays geometrically (the conclusion
`∆V ≤ -ρV` of Remark 2.3, printed p. 37). This is the trajectory-level form of
the decrease of `dsmc_lyapunov_decrease_of_lmi`; it feeds
`quadForm_pow_mulVec_le` of `DynamicalSystems.DiscreteTime.MatrixLyapunov` with
the uniform factor supplied by `exists_factor`. The `Nonempty (Fin n)` hypothesis
is the non-degeneracy needed by the compactness argument of `exists_factor`. -/
theorem dsmc_lmi_geometric_decay {A P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosDef)
    (hLMI : (P - Aᵀ * P * A).PosDef) (hne : Nonempty (Fin n)) :
    ∃ c, 0 ≤ c ∧ c < 1 ∧
      ∀ (k : ℕ) (x : Fin n → ℝ), quadForm P ((A ^ k) *ᵥ x) ≤ c ^ k * quadForm P x := by
  obtain ⟨c, hc0, hc1, hstep⟩ := exists_factor hP hP hLMI hne
  exact ⟨c, hc0, hc1, fun k x ↦ quadForm_pow_mulVec_le hc0 hstep k x⟩

/-- **Existence form of the surface LMI.** If *some* positive-definite `P`
satisfies the block LMI `dsmcSurfaceLMI A P`, then there exists a `P` that is
positive definite, whose Schur complement `P - Aᵀ P A` is positive definite, and
whose quadratic form strictly decreases along `A` on non-zero vectors. This is the
`∃`-form of the implication of `dsmc_sliding_surface_lmi` (Theorem 2.1, printed
p. 35); as required by the campaign scope, feasibility of the LMI (existence of a
solution to the semidefinite program) is *assumed*, not proved. -/
theorem dsmc_sliding_surface_lmi_exists {A : Matrix (Fin n) (Fin n) ℝ}
    (h : ∃ P, dsmcSurfaceLMI A P) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, P.PosDef ∧ (P - Aᵀ * P * A).PosDef ∧
      (∀ x : Fin n → ℝ, x ≠ 0 → quadForm P (A *ᵥ x) < quadForm P x) := by
  obtain ⟨P, hP⟩ := h
  exact ⟨P, dsmc_sliding_surface_lmi hP⟩

/-- **The surface LMI on the equivalent closed loop.** Let `A_cl =
dsmcEquivalentClosedLoop A B C = A - B (C B)⁻¹ C A` be the equivalent closed loop
of the plant `(A, B)` with sliding-surface matrix `C`
(`DynamicalSystems.Control.SlidingMode.DiscreteMatrix`). If the block surface LMI
holds for `A_cl`, then (i) the surface `{x | C x = 0}` is invariant under `A_cl`
(eq. (2.7)/(2.23), printed pp. 31 and 34), and (ii) the quadratic form `quadForm P`
strictly decreases along `A_cl`. This is the form of Theorem 2.1 (printed p. 35) in
which the book's surface matrix `S = Bᵀ P̄⁻¹` is instantiated by `C`; the
invertibility hypothesis `IsUnit (C * B).det` makes `A_cl` well defined. -/
theorem dsmc_sliding_surface_lmi_closedLoop {n m : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    {B : Matrix (Fin n) (Fin m) ℝ} {C : Matrix (Fin m) (Fin n) ℝ}
    (hB : IsUnit (C * B).det) {P : Matrix (Fin n) (Fin n) ℝ}
    (hLMI : dsmcSurfaceLMI (dsmcEquivalentClosedLoop A B C) P) :
    (∀ x : Fin n → ℝ, dsmcSlidingVariable C (dsmcEquivalentClosedLoop A B C *ᵥ x) = 0) ∧
      (∀ x : Fin n → ℝ, x ≠ 0 →
        quadForm P (dsmcEquivalentClosedLoop A B C *ᵥ x) < quadForm P x) := by
  refine ⟨fun x ↦ dsmcEquivalentClosedLoop_slidingVariable A B C hB x, ?_⟩
  exact (dsmc_sliding_surface_lmi hLMI).2.2

/-! ## Disturbance-bound robustness of the `C1`/`C2` controllers

The book models the matched disturbance `f(k)` through its lower and upper bounds
`fᵢᵘ`, `fᵢˡ` (eq. (2.9), printed p. 31) and the associated mean value and
boundary-layer-thickness vectors

`fᵢ⁺ = (fᵢᵘ + fᵢˡ)/2`, `fᵢ⁻ = (fᵢᵘ - fᵢˡ)/2`  (eqs. (2.10)–(2.11)),

i.e. `F⁺ = (Fᵘ + Fˡ)/2` and `F⁻ = (Fᵘ - Fˡ)/2` componentwise. The two
variable-structure discontinuous compensations of §2.3.1 are

* `C1`, eq. (2.17)–(2.18), printed p. 33: the whole boundary layer
  `ϑ₁ = F⁺ + diag(F⁻) sgn(f̂ - F⁺)`;
* `C2`, eq. (2.20)–(2.21), printed p. 34: half of it,
  `ϑ₂ = F⁺ + (1/2) diag(F⁻) sgn(f̂ - F⁺)`.

The compensation error is required to satisfy the bound (2.13), printed p. 31,
`‖f(k) - ϑ(k)‖ ≤ τ F⁻`, with `τ = 2` for `C1` and `τ = 3/2` for `C2` in the
worst case (and `τ = 1`, `1/2` when the signum predicts the position of `f(k)`
perfectly); see the discussion after eq. (2.41), printed p. 38. That additive
bound is what enters the comparison estimate `ΔV ≤ -η̂V/λmax(M) + γ` of
Theorem 2.2 (eq. (2.41)), and hence the ultimate bound (2.32) via
`eventually_le_add_of_succ_le_mul_add`. -/

/-- The componentwise **disturbance-compensation bound** (2.13) of
A. Argha, S. W. Su, L. Li and H. T. Nguyen, *Advances in Discrete-Time Sliding
Mode Control: Theory and Applications*, CRC Press 2018, printed p. 31: every
entry of the compensation error is at most `τ` times the corresponding
boundary-layer thickness `fᵢ⁻`. -/
def dsmcDisturbanceBound {m : ℕ} (τ : ℝ) (Fminus f ϑ : Fin m → ℝ) : Prop :=
  ∀ i, |f i - ϑ i| ≤ τ * Fminus i

/-- **`C1` compensation error is bounded by `2 F⁻`.** If the exogenous disturbance
stays inside the band `[F⁺ - F⁻, F⁺ + F⁻]` of eqs. (2.9)–(2.11) (printed p. 31)
and the signum in the `C1` compensation `ϑ₁ = F⁺ + diag(F⁻) sgn(f̂ - F⁺)`
(eq. (2.17), printed p. 33) takes values in `[-1, 1]`, then the compensation error
satisfies (2.13) with `τ = 2`,

`|fᵢ(k) - ϑ₁ᵢ(k)| ≤ 2 fᵢ⁻` for all `i`.

This is the worst-case bound quoted after eq. (2.41), printed p. 38 (`τ₁ = 2`). -/
theorem dsmc_disturbance_bound_C1 {m : ℕ} {Fplus Fminus f s : Fin m → ℝ}
    (hs : ∀ i, |s i| ≤ 1) (hF : ∀ i, 0 ≤ Fminus i)
    (hf : ∀ i, |f i - Fplus i| ≤ Fminus i) :
    dsmcDisturbanceBound 2 Fminus f (fun i ↦ Fplus i + Fminus i * s i) := by
  intro i
  have h1 : |Fminus i * s i| ≤ Fminus i := by
    rw [abs_mul, abs_of_nonneg (hF i)]
    calc
      Fminus i * |s i| ≤ Fminus i * 1 := mul_le_mul_of_nonneg_left (hs i) (hF i)
      _ = Fminus i := mul_one _
  calc
    |f i - (Fplus i + Fminus i * s i)|
        = |(f i - Fplus i) - Fminus i * s i| := by ring_nf
    _ ≤ |f i - Fplus i| + |Fminus i * s i| := abs_sub _ _
    _ ≤ Fminus i + Fminus i := add_le_add (hf i) h1
    _ = 2 * Fminus i := by ring

/-- **`C2` compensation error is bounded by `3/2 F⁻`.** If the exogenous
disturbance stays inside the band `[F⁺ - F⁻, F⁺ + F⁻]` and the signum in the `C2`
compensation `ϑ₂ = F⁺ + (1/2) diag(F⁻) sgn(f̂ - F⁺)` (eq. (2.20), printed p. 34)
takes values in `[-1, 1]`, then the compensation error satisfies (2.13) with
`τ = 3/2`,

`|fᵢ(k) - ϑ₂ᵢ(k)| ≤ (3/2) fᵢ⁻` for all `i`.

This is the worst-case bound quoted after eq. (2.41), printed p. 38 (`τ₂ = 1.5`). -/
theorem dsmc_disturbance_bound_C2 {m : ℕ} {Fplus Fminus f s : Fin m → ℝ}
    (hs : ∀ i, |s i| ≤ 1) (hF : ∀ i, 0 ≤ Fminus i)
    (hf : ∀ i, |f i - Fplus i| ≤ Fminus i) :
    dsmcDisturbanceBound (3 / 2) Fminus f (fun i ↦ Fplus i + (1 / 2) * Fminus i * s i) := by
  intro i
  have hFi : 0 ≤ Fminus i := hF i
  have h1 : |(1 / 2 : ℝ) * Fminus i * s i| ≤ (1 / 2) * Fminus i := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2),
      abs_of_nonneg hFi]
    calc
      (1 / 2) * Fminus i * |s i| ≤ (1 / 2) * Fminus i * 1 :=
        mul_le_mul_of_nonneg_left (hs i) (by positivity)
      _ = (1 / 2) * Fminus i := mul_one _
  calc
    |f i - (Fplus i + (1 / 2) * Fminus i * s i)|
        = |(f i - Fplus i) - (1 / 2) * Fminus i * s i| := by ring_nf
    _ ≤ |f i - Fplus i| + |(1 / 2) * Fminus i * s i| := abs_sub _ _
    _ ≤ Fminus i + (1 / 2) * Fminus i := add_le_add (hf i) h1
    _ = (3 / 2) * Fminus i := by ring

/-- **Componentwise disturbance bound ⇒ norm bound** (eq. (2.13), printed p. 31).
If the compensation error satisfies the componentwise bound
`|fᵢ - ϑᵢ| ≤ τ fᵢ⁻` with `τ ≥ 0` and `fᵢ⁻ ≥ 0`, then its sup-norm is bounded by
`τ ‖F⁻‖`. This is the step that turns the `C1`/`C2` estimates
`dsmc_disturbance_bound_C1`/`dsmc_disturbance_bound_C2` into the scalar additive
constant of the comparison estimate. -/
theorem dsmc_disturbance_bound_norm {m : ℕ} {τ : ℝ} {Fminus f ϑ : Fin m → ℝ}
    (hcomp : dsmcDisturbanceBound τ Fminus f ϑ) (hτ : 0 ≤ τ) (hF : ∀ i, 0 ≤ Fminus i) :
    ‖f - ϑ‖ ≤ τ * ‖Fminus‖ := by
  rw [pi_norm_le_iff_of_nonneg (mul_nonneg hτ (norm_nonneg _))]
  intro i
  calc
    ‖(f - ϑ) i‖ = |f i - ϑ i| := by simp
    _ ≤ τ * Fminus i := hcomp i
    _ ≤ τ * ‖Fminus‖ := by
      refine mul_le_mul_of_nonneg_left ?_ hτ
      rw [← Real.norm_of_nonneg (hF i)]
      exact norm_le_pi_norm Fminus i

/-- **Reaching with a disturbance bound: the ultimate bound of Theorem 2.2.**
In the presence of the matched disturbance `f(k)`, if the closed-loop Lyapunov
energy `V` obeys the one-step comparison

`V(k + 1) ≤ a V(k) + c ‖f(k) - ϑ(k)‖²`

with `0 ≤ a < 1`, `c ≥ 0`, and the compensation `ϑ` satisfies the bound (2.13)
`|fᵢ - ϑᵢ| ≤ τ fᵢ⁻` (printed p. 31), then for every `ε > 0` the energy is
eventually below the ultimate level `c (τ ‖F⁻‖)² / (1 - a)` up to `ε`:

`∀ᶠ k, V(k) ≤ c (τ ‖F⁻‖)² / (1 - a) + ε`.

This is A. Argha, S. W. Su, L. Li and H. T. Nguyen, *Advances in Discrete-Time
Sliding Mode Control: Theory and Applications*, CRC Press 2018, Theorem 2.2,
eq. (2.41) and the state bound (2.32), printed pp. 37–38, with the additive
constant `γ = τ² f + 2 BᵀPB ‖F⁻‖²` of (2.41) absorbed into `c = f + 2 BᵀPB`. The
passage from the energy to the state norm is the coercivity estimate (2.40); here
it is kept in the energy variable `V` (the statement is honest about not
transporting the bound through `λmin`/`λmax`). The comparison is supplied by
`eventually_le_add_of_succ_le_mul_add` of
`DynamicalSystems.DiscreteTime.UltimateBoundedness` (Lemma 2.4, printed p. 34). -/
theorem dsmc_reaching_with_disturbance_bound {m : ℕ} {v : ℕ → ℝ} {a c τ : ℝ}
    {Fminus : Fin m → ℝ} {f ϑ : ℕ → Fin m → ℝ}
    (hcomp : ∀ k, dsmcDisturbanceBound τ Fminus (f k) (ϑ k))
    (hτ : 0 ≤ τ) (hF : ∀ i, 0 ≤ Fminus i) (ha0 : 0 ≤ a) (ha1 : a < 1) (hc : 0 ≤ c)
    (hv : ∀ k, 0 ≤ v k) (hrec : ∀ k, v (k + 1) ≤ a * v k + c * ‖f k - ϑ k‖ ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in Filter.atTop, v k ≤ c * (τ * ‖Fminus‖) ^ 2 / (1 - a) + ε := by
  have hnorm : ∀ k, ‖f k - ϑ k‖ ≤ τ * ‖Fminus‖ :=
    fun k ↦ dsmc_disturbance_bound_norm (hcomp k) hτ hF
  have hrec' : ∀ k, v (k + 1) ≤ a * v k + c * (τ * ‖Fminus‖) ^ 2 := by
    intro k
    have hsq : ‖f k - ϑ k‖ ^ 2 ≤ (τ * ‖Fminus‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hnorm k) 2
    have hc' : c * ‖f k - ϑ k‖ ^ 2 ≤ c * (τ * ‖Fminus‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hc
    linarith [hrec k]
  exact eventually_le_add_of_succ_le_mul_add ha0 ha1 hv hrec' hε
