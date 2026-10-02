/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.SlidingMode.DiscreteMatrix
public import Mathlib.LinearAlgebra.Matrix.Vec

/-! # Two-dimensional (Fornasini–Marchesini) discrete-time systems

This file formalizes the two-dimensional (2D) first Fornasini–Marchesini (FM)
model that opens the discrete sliding-mode control treatment of A. Argha,
S. W. Su, L. Li and H. T. Nguyen, *Advances in Discrete-Time Sliding Mode
Control: Theory and Applications*, CRC Press 2018, Chapter 8, §8.2–8.3
(printed pp. 163–167; printed page = PDF page − 24).

The plant is the *second-order recursive* local model

`x(i + 1, j + 1) = A₁ x(i + 1, j) + A₂ x(i, j + 1) + A₀ x(i, j) + B u(i, j)`,

eq. (8.1), printed p. 163, where `x(i, j) : Fin n → ℝ` is the local state,
`u(i, j) : Fin m → ℝ` the local input and `A₁, A₂, A₀ : Matrix (Fin n) (Fin n) ℝ`,
`B : Matrix (Fin n) (Fin m) ℝ` are constant. `dsmcTwoDModel` is the predicate
that a doubly-indexed trajectory satisfies this recursion, and
`dsmcTwoDModel_step` is its unfolding at a single grid point.

Section 8.2.1 (printed pp. 163–165) converts the FM model to a *one-dimensional*
form by stacking the states and inputs of a row `i` into vectors `X(i)`, `U(i)`
along the finite spatial direction `j = 1, …, v`, eq. (8.3), printed p. 163. The
2D recursion becomes the first-order *descriptor* model

`J X(i + 1) = K X(i) + L U(i) + V(i)`,

eq. (8.4), printed p. 163, with the block bi-diagonal Toeplitz matrices

`J = I_v ⊗ I_n + (subdiagonal) ⊗ (−A₁)`,
`K = I_v ⊗ A₂ + (subdiagonal) ⊗ A₀`,
`L = I_v ⊗ B`,

eqs. (8.5), printed pp. 163–164, and the boundary vector `V(i)` carrying
`A₁ x(i + 1, 0) + A₀ x(i, 0)` (the `j = 0` boundary), eq. (8.3), printed p. 163.
This file encodes the stacks as `v × n` (resp. `v × m`) matrices, so that the
Mathlib vectorization `Matrix.vec` and Kronecker product `⊗ₖ` express the block
matrices exactly. `dsmcTwoD_to_oneD` is the resulting reduction: it rewrites the
2D recursion into the single 1D descriptor iteration (8.4).

## Main definitions

* `dsmcTwoDModel`: the first FM 2D recursion (8.1), printed p. 163.
* `dsmcStackState`, `dsmcStackInput`, `dsmcBoundary`: the stacking vectors
  `X(i)`, `U(i)`, `V(i)` of (8.3), printed p. 163.
* `dsmcTwoDJ`, `dsmcTwoDK`, `dsmcTwoDL`: the block Toeplitz matrices `J`, `K`,
  `L` of (8.5), printed pp. 163–164.

## Main results

* `dsmcTwoDModel_step`: the recursion unfolded at one grid point.
* `dsmcTwoDModel_add`, `dsmcTwoDModel_zero`: the superposition (linearity)
  properties of the recursion.
* `dsmcTwoD_stacked_recursion`: the stacked matrix identity underlying (8.4).
* `dsmcTwoD_to_oneD`: the 2D-to-1D descriptor reduction (8.4), printed p. 163.

## Implementation notes

The stacking is done over a finite spatial horizon `v` (the book's `v`),
`X(i) ∈ ℝ^{v·n}`, in agreement with Remark 8.1 (printed p. 164): the variable `j`
is assumed to range over a finite set. The descriptor reduction is stated
against the *given* boundary data, i.e. the boundary vector `V(i)` is built from
the trajectory values at `j = 0`; no additional existence/uniqueness of a 2D
solution from boundary conditions is claimed here.

The standard form `X(i + 1) = K̂ X(i) + L̂ U(i) + R̂ V(i)` of (8.9), printed
p. 165, is *not* formalized: it requires inverting the block bi-diagonal matrix
`J` and the explicit formula (8.8), printed p. 165. The descriptor form (8.4) is
the algebraic content of §8.2.1 and is what this file proves.

The scalar/matrix reaching-law and Lyapunov machinery of the campaign is not
duplicated: the DSMC design of §8.3 (printed pp. 165–167) acts on the stacked 1D
model and is provided by `DynamicalSystems.Control.SlidingMode.DiscreteMatrix`
and `DynamicalSystems.Control.SlidingMode.LMI`.
-/

@[expose] public section

open Matrix
open scoped Kronecker

variable {n m v : ℕ}

/-- The **first Fornasini–Marchesini 2D discrete model** (8.1), printed p. 163:
the local state `x(i, j) : Fin n → ℝ` evolves by the second-order recursion

`x(i + 1, j + 1) = A₁ x(i + 1, j) + A₂ x(i, j + 1) + A₀ x(i, j) + B u(i, j)`.

`h : dsmcTwoDModel A₁ A₂ A₀ B u x` says the doubly-indexed trajectory `x`
solves this recursion for all `i, j : ℕ` with input history `u`. -/
def dsmcTwoDModel (A1 A2 A0 : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (u : ℕ → ℕ → Fin m → ℝ) (x : ℕ → ℕ → Fin n → ℝ) : Prop :=
  ∀ i j, x (i + 1) (j + 1) = A1 *ᵥ x (i + 1) j + A2 *ᵥ x i (j + 1) + A0 *ᵥ x i j
    + B *ᵥ u i j

/-- **Unfolding of the 2D FM model** (8.1), printed p. 163, at the grid point
`(i, j)`: the recursion holds pointwise. This is the well-definedness/`simp`
form of `dsmcTwoDModel`. -/
theorem dsmcTwoDModel_step (A1 A2 A0 : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {u : ℕ → ℕ → Fin m → ℝ} {x : ℕ → ℕ → Fin n → ℝ}
    (h : dsmcTwoDModel A1 A2 A0 B u x) (i j : ℕ) :
    x (i + 1) (j + 1) = A1 *ᵥ x (i + 1) j + A2 *ᵥ x i (j + 1) + A0 *ᵥ x i j
      + B *ᵥ u i j :=
  h i j

/-- **Linearity (superposition) of the 2D FM model** (8.1), printed p. 163. The
recursion is affine-linear in `(x, u)`: the state/input sum of two solutions is a
solution for the summed input. This is the 2D counterpart of the linearity used
implicitly in the stacking argument of §8.2.1 (printed pp. 163–165). -/
theorem dsmcTwoDModel_add (A1 A2 A0 : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {u₁ u₂ : ℕ → ℕ → Fin m → ℝ}
    {x₁ x₂ : ℕ → ℕ → Fin n → ℝ}
    (h₁ : dsmcTwoDModel A1 A2 A0 B u₁ x₁) (h₂ : dsmcTwoDModel A1 A2 A0 B u₂ x₂) :
    dsmcTwoDModel A1 A2 A0 B (fun i j ↦ u₁ i j + u₂ i j)
      (fun i j ↦ x₁ i j + x₂ i j) := by
  intro i j
  change x₁ (i + 1) (j + 1) + x₂ (i + 1) (j + 1) =
    A1 *ᵥ (x₁ (i + 1) j + x₂ (i + 1) j) + A2 *ᵥ (x₁ i (j + 1) + x₂ i (j + 1))
      + A0 *ᵥ (x₁ i j + x₂ i j) + B *ᵥ (u₁ i j + u₂ i j)
  rw [h₁ i j, h₂ i j, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add,
    Matrix.mulVec_add]
  abel

/-- **The zero solution of the 2D FM model** (8.1), printed p. 163: the zero
trajectory with zero input satisfies the recursion. -/
theorem dsmcTwoDModel_zero (A1 A2 A0 : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) :
    dsmcTwoDModel A1 A2 A0 B (fun _ _ ↦ 0) (fun _ _ ↦ 0) := by
  intro i j
  simp only [Matrix.mulVec_zero]
  abel

/-- The `j`-shift (subdiagonal) matrix on `Fin v`: `S p q = 1` exactly when
`p = q + 1`. It is the elementary block of the block bi-diagonal Toeplitz
matrices `J`, `K` of (8.5), printed pp. 163–164. -/
def dsmcShift (v : ℕ) : Matrix (Fin v) (Fin v) ℝ :=
  Matrix.of fun p q ↦ if (p : ℕ) = (q : ℕ) + 1 then 1 else 0

/-- The predecessor index of `p : Fin v`, as a `Fin v` (with the convention
`pred 0 = 0`, so that it is only meaningful for `p ≠ 0`). It is the spatial
`j`-index paired with the subdiagonal block of `dsmcShift` in (8.5), printed
pp. 163–164. -/
def dsmcPred {v : ℕ} (p : Fin v) : Fin v := ⟨(p : ℕ) - 1, by omega⟩

/-- Evaluation of `dsmcPred`, the subdiagonal index of (8.5), printed
pp. 163–164 (a `simp` lemma). -/
@[simp] theorem dsmcPred_val {v : ℕ} (p : Fin v) : (dsmcPred p : ℕ) = (p : ℕ) - 1 := rfl

/-- On the first block row (`p = 0`) the shift matrix annihilates the stacked
vector: `(S X) 0 = 0`. This is the boundary row of (8.4), printed p. 163. -/
theorem dsmcShift_mul_apply_zero (X : Matrix (Fin v) (Fin n) ℝ) (p : Fin v)
    (hp : (p : ℕ) = 0) (a : Fin n) : (dsmcShift v * X) p a = 0 := by
  rw [dsmcShift, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro q _
  simp only [Matrix.of_apply]
  rw [ite_eq_right]
  · simp
  · omega

/-- On a non-boundary block row (`p ≠ 0`) the shift matrix returns the previous
row of the stacked vector: `(S X) p = X (pred p)`. This is the subdiagonal block
`−A₁` / `A₀` of (8.5), printed pp. 163–164. -/
theorem dsmcShift_mul_apply (X : Matrix (Fin v) (Fin n) ℝ) (p : Fin v)
    (hp : (p : ℕ) ≠ 0) (a : Fin n) :
    (dsmcShift v * X) p a = X (dsmcPred p) a := by
  rw [dsmcShift, Matrix.mul_apply]
  rw [Finset.sum_eq_single (dsmcPred p)]
  · simp only [Matrix.of_apply]
    have h : (p : ℕ) = ((dsmcPred p : Fin v) : ℕ) + 1 := by rw [dsmcPred_val]; omega
    rw [ite_eq_left h]; simp
  · intro q _ hq
    simp only [Matrix.of_apply]
    rw [ite_eq_right]
    · simp
    · intro h
      exact hq (Fin.ext (by rw [dsmcPred_val]; omega))
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The `(p, a)` entry of `X * Mᵀ` is the `a`-th component of `M` applied to the
`p`-th row of `X`: this identifies the matrix product `X Mᵀ` used in the stacked
recursion (8.4), printed p. 163, with `Matrix.mulVec`. -/
theorem dsmcMulTranspose_apply {r c d : ℕ} (X : Matrix (Fin r) (Fin c) ℝ)
    (M : Matrix (Fin d) (Fin c) ℝ) (p : Fin r) (a : Fin d) :
    (X * Mᵀ) p a = (M *ᵥ X p) a := by
  rw [Matrix.mul_apply, Matrix.mulVec_apply, Matrix.row, dotProduct]
  exact Finset.sum_congr rfl fun b _ ↦ mul_comm _ _

/-- The **stacked 1D state vector** `X(i) = (x(i, 1), …, x(i, v))` of (8.3),
printed p. 163, represented as a `v × n` matrix whose `p`-th row is
`x(i, p + 1)`. -/
def dsmcStackState (v : ℕ) (x : ℕ → ℕ → Fin n → ℝ) (i : ℕ) : Matrix (Fin v) (Fin n) ℝ :=
  Matrix.of fun p a ↦ x i ((p : ℕ) + 1) a

/-- The **stacked 1D input vector** `U(i) = (u(i, 0), …, u(i, v − 1))` of (8.3),
printed p. 163, represented as a `v × m` matrix whose `p`-th row is `u(i, p)`. -/
def dsmcStackInput (v : ℕ) (u : ℕ → ℕ → Fin m → ℝ) (i : ℕ) : Matrix (Fin v) (Fin m) ℝ :=
  Matrix.of fun p c ↦ u i (p : ℕ) c

/-- The **boundary vector** `V(i)` of (8.3), printed p. 163: its first block row
is `A₁ x(i + 1, 0) + A₀ x(i, 0)` (the `j = 0` boundary, eq. (8.6), printed
p. 164) and all other block rows vanish. -/
def dsmcBoundary (v : ℕ) (A1 A0 : Matrix (Fin n) (Fin n) ℝ) (x : ℕ → ℕ → Fin n → ℝ)
    (i : ℕ) : Matrix (Fin v) (Fin n) ℝ :=
  Matrix.of fun p a ↦ if (p : ℕ) = 0 then (A1 *ᵥ x (i + 1) 0 + A0 *ᵥ x i 0) a else 0

/-- The `(p, a)` entry of the stacked state, eq. (8.3), printed p. 163 (a `simp`
lemma). -/
@[simp] theorem dsmcStackState_eq (x : ℕ → ℕ → Fin n → ℝ) (i : ℕ) (p : Fin v) :
    dsmcStackState v x i p = x i ((p : ℕ) + 1) := rfl

/-- The `p`-th block row of the stacked input, eq. (8.3), printed p. 163 (a
`simp` lemma). -/
@[simp] theorem dsmcStackInput_eq (u : ℕ → ℕ → Fin m → ℝ) (i : ℕ) (p : Fin v) :
    dsmcStackInput v u i p = u i (p : ℕ) := rfl

/-- The `(p, a)` entry of the boundary vector `V(i)`, eq. (8.3), printed p. 163
(a `simp` lemma). -/
@[simp] theorem dsmcBoundary_apply (A1 A0 : Matrix (Fin n) (Fin n) ℝ)
    (x : ℕ → ℕ → Fin n → ℝ) (i : ℕ) (p : Fin v) (a : Fin n) :
    dsmcBoundary v A1 A0 x i p a =
      if (p : ℕ) = 0 then (A1 *ᵥ x (i + 1) 0 + A0 *ᵥ x i 0) a else 0 := rfl

/-- The **block matrix `J`** of (8.5), printed pp. 163–164, represented through
the Kronecker product in the row-processing index order:
`J = I_n ⊗ I_v − A₁ ⊗ S`, where `S = dsmcShift` is the block subdiagonal. Its
`(p, q)` block is `δ_{pq} I_n − [p = q + 1] A₁`, as in the book. -/
def dsmcTwoDJ (v : ℕ) (A1 : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n × Fin v) (Fin n × Fin v) ℝ :=
  (1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ (1 : Matrix (Fin v) (Fin v) ℝ) - A1 ⊗ₖ dsmcShift v

/-- The **block matrix `K`** of (8.5), printed p. 164, represented as
`K = A₂ ⊗ I_v + A₀ ⊗ S`. Its `(p, q)` block is `δ_{pq} A₂ + [p = q + 1] A₀`. -/
def dsmcTwoDK (v : ℕ) (A2 A0 : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n × Fin v) (Fin n × Fin v) ℝ :=
  A2 ⊗ₖ (1 : Matrix (Fin v) (Fin v) ℝ) + A0 ⊗ₖ dsmcShift v

/-- The **block matrix `L`** of (8.5), printed p. 164, represented as
`L = B ⊗ I_v` (block diagonal with blocks `B`). -/
def dsmcTwoDL (v : ℕ) (B : Matrix (Fin n) (Fin m) ℝ) :
    Matrix (Fin n × Fin v) (Fin m × Fin v) ℝ :=
  B ⊗ₖ (1 : Matrix (Fin v) (Fin v) ℝ)

/-- **The stacked matrix recursion** underlying (8.4), printed p. 163, in the
un-vectorized `v × n` matrix form:

`X(i + 1) − S X(i + 1) A₁ᵀ = X(i) A₂ᵀ + S X(i) A₀ᵀ + U(i) Bᵀ + V(i)`.

Row `p = 0` of this identity is the `j = 0` recursion of (8.1) with the boundary
term; row `p ≠ 0` is the `j = p` recursion of (8.1). Applying `Matrix.vec`
turns it into the descriptor model (8.4). -/
theorem dsmcTwoD_stacked_recursion (A1 A2 A0 : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {u : ℕ → ℕ → Fin m → ℝ} {x : ℕ → ℕ → Fin n → ℝ}
    (h : dsmcTwoDModel A1 A2 A0 B u x) (v i : ℕ) :
    dsmcStackState v x (i + 1) - dsmcShift v * dsmcStackState v x (i + 1) * A1ᵀ
      = dsmcStackState v x i * A2ᵀ + dsmcShift v * dsmcStackState v x i * A0ᵀ
        + dsmcStackInput v u i * Bᵀ + dsmcBoundary v A1 A0 x i := by
  ext p a
  rw [Matrix.sub_apply, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply,
    dsmcMulTranspose_apply, dsmcMulTranspose_apply, dsmcMulTranspose_apply,
    dsmcMulTranspose_apply]
  by_cases hp : (p : ℕ) = 0
  · have hSX : (dsmcShift v * dsmcStackState v x (i + 1)) p = 0 :=
      funext fun b ↦ dsmcShift_mul_apply_zero _ p hp b
    have hSY : (dsmcShift v * dsmcStackState v x i) p = 0 :=
      funext fun b ↦ dsmcShift_mul_apply_zero _ p hp b
    rw [hSX, hSY, Matrix.mulVec_zero, Matrix.mulVec_zero]
    rw [dsmcBoundary_apply, ite_eq_left hp]
    simp only [Pi.zero_apply, sub_zero, add_zero, dsmcStackState_eq, dsmcStackInput_eq, hp]
    rw [h i 0]
    simp only [Pi.add_apply]
    abel
  · have hSX : (dsmcShift v * dsmcStackState v x (i + 1)) p
        = dsmcStackState v x (i + 1) (dsmcPred p) :=
      funext fun b ↦ dsmcShift_mul_apply _ p hp b
    have hSY : (dsmcShift v * dsmcStackState v x i) p
        = dsmcStackState v x i (dsmcPred p) :=
      funext fun b ↦ dsmcShift_mul_apply _ p hp b
    have hp1 : 1 ≤ (p : ℕ) := by omega
    rw [hSX, hSY]
    simp only [dsmcBoundary_apply, dsmcStackState_eq, dsmcStackInput_eq, dsmcPred_val,
      ite_eq_right hp, Nat.sub_add_cancel hp1]
    rw [h i (p : ℕ)]
    simp only [Pi.add_apply]
    abel

/-- **The 2D → 1D reduction (8.4), printed p. 163.** A trajectory of the first
Fornasini–Marchesini model (8.1) yields a solution of the 1D *descriptor* model

`J X(i + 1) = K X(i) + L U(i) + V(i)`,

with `X`, `U`, `V` the stacking vectors of (8.3) and `J`, `K`, `L` the block
bi-diagonal Toeplitz matrices of (8.5). This is the "new 1D form of the 2D first
FM model" of §8.2.1 and the stage for the 1D DSMC design of §8.3 (printed
pp. 163–167): it converts the second-order 2D recursion into a first-order
iteration on the fixed-dimension stacked vector `X(i)`. -/
theorem dsmcTwoD_to_oneD (A1 A2 A0 : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) {u : ℕ → ℕ → Fin m → ℝ} {x : ℕ → ℕ → Fin n → ℝ}
    (h : dsmcTwoDModel A1 A2 A0 B u x) (v i : ℕ) :
    dsmcTwoDJ v A1 *ᵥ vec (dsmcStackState v x (i + 1))
      = dsmcTwoDK v A2 A0 *ᵥ vec (dsmcStackState v x i)
        + dsmcTwoDL v B *ᵥ vec (dsmcStackInput v u i)
        + vec (dsmcBoundary v A1 A0 x i) := by
  have Hv := congrArg Matrix.vec (dsmcTwoD_stacked_recursion A1 A2 A0 B h v i)
  simpa only [dsmcTwoDJ, dsmcTwoDK, dsmcTwoDL, Matrix.sub_mulVec, Matrix.add_mulVec,
    kronecker_mulVec_vec, Matrix.one_mul, Matrix.mul_one, Matrix.transpose_one,
    Matrix.vec_sub, Matrix.vec_add] using Hv
