/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Tactic

/-! # Discrete comparison (Grönwall) estimates

This file records the scalar comparison estimate used by every parameter-adaptation
and estimation bound of the discrete-time adaptive-control theory of
I. D. Landau, R. Lozano, M'Saad and A. Karimi, *Adaptive Control: Algorithms,
Analysis and Applications*, 2nd ed., Springer 2011.

Mathlib's `Mathlib.Analysis.ODE.DiscreteGronwall` only provides *growth* bounds of
the form `exp (n * c)`; the discrete-time contraction

`v (t + 1) ≤ a * v t + d`,  `0 ≤ a < 1`,

needed by the book's PAA and robust adaptive-control estimates instead has the
finite limit `d / (1 - a)`. The estimate below is the elementary induction that
produces this contraction bound.

## Main statements

* `le_of_succ_le_mul_add`: if `v (t + 1) ≤ a * v t + d` with `0 ≤ a < 1` and
  `0 ≤ v`, then `v t ≤ a ^ t * v 0 + d * (1 - a ^ t) / (1 - a)`.
* `exponential_decay_of_succ_le_mul`: the homogeneous case `d = 0`, giving
  `v t ≤ a ^ t * v 0`.
-/

@[expose] public section

/-- Discrete comparison (Grönwall) estimate: if `v (t + 1) ≤ a * v t + d` with
`0 ≤ a < 1` and `v ≥ 0`, then

`v t ≤ a ^ t * v 0 + d * (1 - a ^ t) / (1 - a)`.

The proof is an induction on `t`. The affine comparison sequence
`B t := a ^ t * v 0 + d * (1 - a ^ t) / (1 - a)` satisfies `B (t + 1) = a * B t + d`
and `B 0 = v 0`; the bound then follows from the recurrence by monotonicity of
`x ↦ a * x + d` with `a ≥ 0`.

The hypothesis `hv` (non-negativity of `v`) is not needed for this estimate — the
bound holds for arbitrary real-valued `v` — but it is retained to match the
campaign signature and is carried through the induction as a conjunct. -/
theorem le_of_succ_le_mul_add {v : ℕ → ℝ} {a d : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hv : ∀ t, 0 ≤ v t) (h : ∀ t, v (t + 1) ≤ a * v t + d) (t : ℕ) :
    v t ≤ a ^ t * v 0 + d * (1 - a ^ t) / (1 - a) := by
  have hne : (1 : ℝ) - a ≠ 0 := by linarith
  have key : ∀ t, v t ≤ a ^ t * v 0 + d * (1 - a ^ t) / (1 - a) ∧ 0 ≤ v t := by
    intro t
    induction t with
    | zero => exact ⟨by simp, hv 0⟩
    | succ t ih =>
        obtain ⟨ihle, -⟩ := ih
        refine ⟨?_, hv (t + 1)⟩
        have hstep : a * (a ^ t * v 0 + d * (1 - a ^ t) / (1 - a)) + d
            = a ^ (t + 1) * v 0 + d * (1 - a ^ (t + 1)) / (1 - a) := by
          rw [pow_succ]
          field_simp
          ring
        calc v (t + 1) ≤ a * v t + d := h t
          _ ≤ a * (a ^ t * v 0 + d * (1 - a ^ t) / (1 - a)) + d := by gcongr
          _ = a ^ (t + 1) * v 0 + d * (1 - a ^ (t + 1)) / (1 - a) := hstep
  exact (key t).1

/-- `d = 0` decay corollary of `le_of_succ_le_mul_add`: a non-negative sequence
satisfying the homogeneous inequality `v (t + 1) ≤ a * v t` with `0 ≤ a < 1`
decays geometrically, `v t ≤ a ^ t * v 0`. -/
theorem exponential_decay_of_succ_le_mul {v : ℕ → ℝ} {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (hv : ∀ t, 0 ≤ v t) (h : ∀ t, v (t + 1) ≤ a * v t) (t : ℕ) : v t ≤ a ^ t * v 0 := by
  have h' : ∀ t, v (t + 1) ≤ a * v t + 0 := fun t ↦ by simpa using h t
  have := le_of_succ_le_mul_add ha0 ha1 hv h' t
  simpa using this
