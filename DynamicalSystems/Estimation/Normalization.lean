/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Real.Sqrt

/-! # Data normalization scalar core

This file formalizes the scalar core of the data normalization of the robust
parameter estimation scheme of I. D. Landau, R. Lozano, M'Saad and A. Karimi,
*Adaptive Control: Algorithms, Analysis and Applications*, 2nd ed., Springer 2011,
Chapter 10 (Sect. 10.6, Theorems 10.4 and 10.5, eqs. 10.110 and 10.119).

Input-output data are divided by the normalizing signal
`m = √(1 + ‖φ‖²)`, so that the normalized regressor `φ / m` is bounded by `1` in
Euclidean norm. This boundedness is what keeps the normalized unmodeled response
`w̄ = w / m` bounded even when the raw regressor `φ` grows without bound.

## Main definitions

* `normalizer phi`: the normalizing signal `√(1 + ∑ k, phi k ^ 2)`.

## Main results

* `normalizer_pos`: the normalizer is positive.
* `normalized_regressor_norm_le_one`: the normalized regressor has squared norm at
  most `1`, i.e. `∑ k, (phi k / normalizer phi) ^ 2 ≤ 1`.
-/

@[expose] public section

/-- The normalizing signal `m = √(1 + ‖φ‖²)` of book eq. 10.119 (with the
constant `1` replacing the `max[‖φ‖², 1]` of the dynamic normalization, which is
the static form for Assumption B). -/
noncomputable def normalizer {n : ℕ} (phi : Fin n → ℝ) : ℝ :=
  Real.sqrt (1 + ∑ k, phi k ^ 2)

/-- The normalizer is positive, since `1 + ∑ k, phi k ^ 2 ≥ 1 > 0`. -/
theorem normalizer_pos {n : ℕ} (phi : Fin n → ℝ) : 0 < normalizer phi := by
  rw [normalizer, Real.sqrt_pos]
  have hsum : 0 ≤ ∑ k, phi k ^ 2 := Finset.sum_nonneg fun k _ ↦ sq_nonneg (phi k)
  linarith

/-- The normalized regressor has squared norm at most `1` (book eqs. 10.118 and
10.119): `∑ k, (phi k / normalizer phi) ^ 2 ≤ 1`. Multiplying through by
`normalizer phi ^ 2 = 1 + ∑ k, phi k ^ 2 > 0` reduces the claim to
`∑ k, phi k ^ 2 ≤ 1 + ∑ k, phi k ^ 2`. -/
theorem normalized_regressor_norm_le_one {n : ℕ} (phi : Fin n → ℝ) :
    ∑ k, (phi k / normalizer phi) ^ 2 ≤ 1 := by
  have hsum : 0 ≤ ∑ k, phi k ^ 2 := Finset.sum_nonneg fun k _ ↦ sq_nonneg (phi k)
  have hden : 0 < 1 + ∑ k, phi k ^ 2 := by linarith
  have hsqrt_sq : normalizer phi ^ 2 = 1 + ∑ k, phi k ^ 2 := by
    rw [normalizer, Real.sq_sqrt (by linarith : 0 ≤ 1 + ∑ k, phi k ^ 2)]
  have hterm : ∀ k, (phi k / normalizer phi) ^ 2 = phi k ^ 2 / (1 + ∑ k, phi k ^ 2) := by
    intro k
    rw [div_pow, hsqrt_sq]
  calc
    ∑ k, (phi k / normalizer phi) ^ 2
        = ∑ k, phi k ^ 2 / (1 + ∑ k, phi k ^ 2) := by
          exact Finset.sum_congr rfl fun k _ ↦ hterm k
    _ = (∑ k, phi k ^ 2) / (1 + ∑ k, phi k ^ 2) := by rw [Finset.sum_div]
    _ ≤ 1 := by
          rw [div_le_one hden]
          linarith
