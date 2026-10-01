/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic

/-! # Causal discrete convolution and ℓ¹ BIBO bounds

This file records the elementary causal-convolution estimates that justify the
plant-level stability bounds of I. D. Landau, R. Lozano, M'Saad and A. Karimi,
*Adaptive Control: Algorithms, Analysis and Applications*, 2nd ed., Springer 2011,
equations (11.28)–(11.31) on printed page 366.

A causal discrete filter with impulse response `h` acts on an input sequence `v` by
the causal convolution

`(h ⋆ v)(t) = ∑_{k=0}^{t} h(k) · v(t - k)`,

written in Lean as `causalConv h v t`. Summing only over `k ∈ Finset.range (t + 1)`
guarantees `k ≤ t`, so the index `t - k` is always in range and no saturation bug
can arise. The filter is BIBO stable exactly when the impulse response is absolutely
summable, and then `|(h ⋆ v)(t)|` is bounded by `‖h‖₁` times the running maximum of
`|v|`. This is the abstract, polynomial-free form in which Landau states the plant
stability hypotheses (11.29)–(11.31).

## Main definitions

* `causalConv h v t`: the causal discrete convolution of `h` and `v` at time `t`.

## Main results

* `abs_causalConv_le_sum_abs_mul_sup`: pointwise triangle-inequality bound.
* `causalConv_l1_bound`: the ℓ¹ BIBO stability bound.
* `affine_filter_bound`: the affine plant-output bound (eq. 11.29).
* `running_sup_bound_chain`: chaining a running-maximum bound through a filter
  (eqs. 11.29)–(11.31).
-/

@[expose] public section

/-- Causal discrete convolution of an impulse response `h` and an input sequence
`v`: `(h ⋆ v)(t) = ∑_{k=0}^{t} h(k) · v(t - k)`. -/
def causalConv (h v : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (t + 1), h k * v (t - k)

/-- The causal convolution is bounded by the partial ℓ¹ norm of the impulse response
times the running supremum of the absolute input, by the triangle inequality and
`Finset.le_sup'`. -/
theorem abs_causalConv_le_sum_abs_mul_sup (h v : ℕ → ℝ) (t : ℕ) :
    |causalConv h v t| ≤ (∑ k ∈ Finset.range (t + 1), |h k|) *
      (Finset.range (t + 1)).sup' (by simp) (fun j ↦ |v j|) := by
  calc
    |causalConv h v t|
        = |∑ k ∈ Finset.range (t + 1), h k * v (t - k)| := rfl
    _ ≤ ∑ k ∈ Finset.range (t + 1), |h k * v (t - k)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ Finset.range (t + 1), |h k| * |v (t - k)| := by
          apply Finset.sum_congr rfl
          intro k _
          rw [abs_mul]
    _ ≤ ∑ k ∈ Finset.range (t + 1), |h k| *
          (Finset.range (t + 1)).sup' (by simp) (fun j ↦ |v j|) := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_left
            (Finset.le_sup' (fun j ↦ |v j|)
              (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.sub_le t k))))
            (abs_nonneg (h k))
    _ = (∑ k ∈ Finset.range (t + 1), |h k|) *
          (Finset.range (t + 1)).sup' (by simp) (fun j ↦ |v j|) := by
          rw [Finset.sum_mul]

/-- **ℓ¹ BIBO stability bound.** If the impulse response has partial ℓ¹ norms bounded
by `H`, then the causal convolution is bounded by `H` times the running supremum of
`|v|`; this is the elementary content of the plant stability hypothesis (11.29). -/
theorem causalConv_l1_bound {h v : ℕ → ℝ} {H : ℝ} (hH : 0 ≤ H)
    (hsum : ∀ t, (∑ k ∈ Finset.range (t + 1), |h k|) ≤ H) (t : ℕ) :
    |causalConv h v t| ≤ H * (Finset.range (t + 1)).sup' (by simp) (fun j ↦ |v j|) := by
  have hsup : 0 ≤ (Finset.range (t + 1)).sup' (by simp) (fun j ↦ |v j|) := by
    have hmem : 0 ∈ Finset.range (t + 1) := Finset.mem_range.mpr (Nat.succ_pos t)
    exact (abs_nonneg (v 0)).trans (Finset.le_sup' (fun j ↦ |v j|) hmem)
  calc
    |causalConv h v t| ≤ (∑ k ∈ Finset.range (t + 1), |h k|) *
        (Finset.range (t + 1)).sup' (by simp) (fun j ↦ |v j|) :=
          abs_causalConv_le_sum_abs_mul_sup h v t
    _ ≤ H * (Finset.range (t + 1)).sup' (by simp) (fun j ↦ |v j|) :=
          mul_le_mul (hsum t) le_rfl hsup hH

/-- **Affine plant filter bound (Landau eq. 11.29).** If `y = y* + (h ⋆ v)` with a
bounded reference `|y*(t)| ≤ My` and a stable filter `∑ |h| ≤ H`, then
`|y(t)| ≤ My + H · sup_{j ≤ t} |v(j)|`. -/
theorem affine_filter_bound {y yStar h v : ℕ → ℝ} {My H : ℝ} (hMy : 0 ≤ My) (hH : 0 ≤ H)
    (hy : ∀ t, y t = yStar t + causalConv h v t)
    (hyStar : ∀ t, |yStar t| ≤ My)
    (hsum : ∀ t, (∑ k ∈ Finset.range (t + 1), |h k|) ≤ H) (t : ℕ) :
    |y t| ≤ My + H * (Finset.range (t + 1)).sup' (by simp) (fun j ↦ |v j|) := by
  rw [hy t, ← abs_of_nonneg hMy]
  calc
    |yStar t + causalConv h v t| ≤ |yStar t| + |causalConv h v t| := abs_add_le _ _
    _ ≤ |My| + H * (Finset.range (t + 1)).sup' (by simp) (fun j ↦ |v j|) :=
          add_le_add (by rw [abs_of_nonneg hMy]; exact hyStar t)
            (causalConv_l1_bound hH hsum t)

/-- **Running-maximum bound chaining.** If the output satisfies
`|y(t)| ≤ C1y + C2y · sup_{k ≤ t + D1} |e(k)|` and the input satisfies
`|u(t)| ≤ C1u + C2u · sup_{k ≤ t + D2} |y(k)|`, then composing the two running
maxima gives `|u(t)| ≤ (C1u + C2u·C1y) + C2u·C2y · sup_{k ≤ t + D1 + D2} |e(k)|`.
This is the scalar form of the bound chaining (11.29)–(11.31). -/
theorem running_sup_bound_chain {y u e : ℕ → ℝ} {C1y C2y C1u C2u : ℝ} (D1 D2 : ℕ)
    (hC2y : 0 ≤ C2y) (hC2u : 0 ≤ C2u)
    (hy : ∀ t, |y t| ≤ C1y + C2y * (Finset.range (t + D1 + 1)).sup' (by simp)
      (fun k ↦ |e k|))
    (hu : ∀ t, |u t| ≤ C1u + C2u * (Finset.range (t + D2 + 1)).sup' (by simp)
      (fun k ↦ |y k|)) :
    ∀ t, |u t| ≤ (C1u + C2u * C1y) +
      (C2u * C2y) * (Finset.range (t + D1 + D2 + 1)).sup' (by simp) (fun k ↦ |e k|) := by
  intro t
  have hsupY : (Finset.range (t + D2 + 1)).sup' (by simp) (fun k ↦ |y k|) ≤
      C1y + C2y * (Finset.range (t + D1 + D2 + 1)).sup' (by simp) (fun k ↦ |e k|) := by
    rw [Finset.sup'_le_iff]
    intro k hk
    have hk' : k ≤ t + D2 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hsub : Finset.range (k + D1 + 1) ⊆ Finset.range (t + D1 + D2 + 1) := by
      intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    calc
      |y k| ≤ C1y + C2y * (Finset.range (k + D1 + 1)).sup' (by simp) (fun j ↦ |e j|) :=
            hy k
      _ ≤ C1y + C2y * (Finset.range (t + D1 + D2 + 1)).sup' (by simp) (fun j ↦ |e j|) := by
            gcongr
  calc
    |u t| ≤ C1u + C2u * (Finset.range (t + D2 + 1)).sup' (by simp) (fun k ↦ |y k|) := hu t
    _ ≤ C1u + C2u *
          (C1y + C2y * (Finset.range (t + D1 + D2 + 1)).sup' (by simp) (fun k ↦ |e k|)) := by
          gcongr
    _ = (C1u + C2u * C1y) +
          (C2u * C2y) * (Finset.range (t + D1 + D2 + 1)).sup' (by simp) (fun k ↦ |e k|) := by
          ring
