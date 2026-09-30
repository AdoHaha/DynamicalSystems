/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic

/-! # The projection operator of Kabziński and Mosiołek (Appendix D3)

This file formalizes the algebraic projection operator used in the adaptive-control
constructions of Kabziński and Mosiołek, *Projektowanie nieliniowych układów
sterowania*, Appendix D3. The operator clamps the right-hand side of an adaptation
law so that every trajectory of the estimate `θ̂` staying at a box boundary is kept
inside the box `[θᵐ, θᴹ]` described by (D3.1).

The formalization here is purely coordinate-wise algebra: no ODE invariance is
claimed. The dynamic statement (that a solution of the projected adaptation law
(D3.4) remains inside the box) is deferred.

## Main definitions

* `projCoord`: the scalar projection `proj θᵢᵐ θᵢᴹ yᵢ θ̂ᵢ` of (D3.3).
* `Proj`: the vector-valued projection `Proj θᵐ θᴹ y θ̂` of (D3.5).

## Main results

* `projCoord_smul` (D3.7): positive homogeneity of the scalar projection.
* `Proj_smul` (D3.8): equivariance of the vector projection under a positive
  diagonal scaling.
* `Proj_coord_nonpos` (D3.9): the coordinate-wise inequality of Theorem D3.1.
* `Proj_sum_nonpos` (D3.9): the summed inequality of Theorem D3.1.
* `Proj_sum_sq_le` (D3.13): the squared `ℓ²` bound of Theorem D3.2.
-/

@[expose] public noncomputable section

/-- The scalar projection operator `proj θᵢᵐ θᵢᴹ yᵢ θ̂ᵢ` of (D3.3). It zeroes the
adaptation derivative at a box boundary when that derivative would push the estimate
outside the box, and otherwise returns the derivative unchanged. -/
def projCoord (m M y theta : ℝ) : ℝ :=
  if (theta ≤ m ∧ y < 0) ∨ (M ≤ theta ∧ 0 < y) then 0 else y

/-- The vector projection operator `Proj θᵐ θᴹ y θ̂` of (D3.5), obtained by applying
`projCoord` coordinate-wise. -/
def Proj {i : Type*} (m M y theta : i → ℝ) : i → ℝ :=
  fun k ↦ projCoord (m k) (M k) (y k) (theta k)

/-- **D3.7**: the scalar projection is positively homogeneous in the vector `y`:
for `γ > 0`, `proj (γ · y) θ̂ = γ · proj y θ̂`. -/
theorem projCoord_smul {m M y theta gamma : ℝ} (hγ : 0 < gamma) :
    projCoord m M (gamma * y) theta = gamma * projCoord m M y theta := by
  have hmul_neg : gamma * y < 0 ↔ y < 0 := by
    rw [← neg_pos (a := gamma * y), ← mul_neg, mul_pos_iff_of_pos_left hγ, neg_pos]
  have hmul_pos : 0 < gamma * y ↔ 0 < y := mul_pos_iff_of_pos_left hγ
  have hcond : ((theta ≤ m ∧ gamma * y < 0) ∨ (M ≤ theta ∧ 0 < gamma * y)) ↔
      ((theta ≤ m ∧ y < 0) ∨ (M ≤ theta ∧ 0 < y)) := by
    simp only [hmul_neg, hmul_pos]
  simp only [projCoord]
  rw [if_congr hcond rfl rfl]
  by_cases h : (theta ≤ m ∧ y < 0) ∨ (M ≤ theta ∧ 0 < y) <;> simp [h]

set_option linter.unusedFintypeInType false in
/-- **D3.8**: the vector projection commutes with a positive diagonal scaling: for
`γ k > 0` for all `k`, `Proj (γ · y) θ̂ = γ · Proj y θ̂`. The `Fintype` hypothesis is
part of the vector-level interface of (D3.5) even though the identity is
coordinate-wise. -/
-- `[Fintype i]` is kept to match the vector-level interface of (D3.5); the identity
-- itself is proved coordinate-wise and does not need the finiteness hypothesis.
@[nolint unusedArguments]
theorem Proj_smul {i : Type*} [Fintype i] {m M y theta gamma : i → ℝ}
    (hγ : ∀ k, 0 < gamma k) :
    Proj m M (fun k ↦ gamma k * y k) theta = fun k ↦ gamma k * Proj m M y theta k := by
  funext k
  simp only [Proj]
  exact projCoord_smul (hγ k)

/-- **D3.9 (coordinate-wise, Theorem D3.1)**: if the true parameter `θ` lies in the box
`m k ≤ θ k ≤ M k` for every coordinate, then for every coordinate `k`,
`(θ k - θ̂ k) * (y k - proj y θ̂ k) ≤ 0`. -/
theorem Proj_coord_nonpos {i : Type*} {m M y theta thetaHat : i → ℝ}
    (hm : ∀ k, m k ≤ theta k) (hM : ∀ k, theta k ≤ M k) :
    ∀ k, (theta k - thetaHat k) * (y k - Proj m M y thetaHat k) ≤ 0 := by
  intro k
  simp only [Proj, projCoord]
  split_ifs with h
  · rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [sub_zero]
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (le_trans h1 (hm k))) (le_of_lt h2)
    · rw [sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_trans (hM k) h1)) (le_of_lt h2)
  · rw [sub_self, mul_zero]

/-- **D3.9 (summed, Theorem D3.1)**: summing the coordinate-wise inequality gives
`∑ k, (θ k - θ̂ k) * (y k - proj y θ̂ k) ≤ 0`. -/
theorem Proj_sum_nonpos {i : Type*} [Fintype i] {m M y theta thetaHat : i → ℝ}
    (hm : ∀ k, m k ≤ theta k) (hM : ∀ k, theta k ≤ M k) :
    ∑ k, (theta k - thetaHat k) * (y k - Proj m M y thetaHat k) ≤ 0 :=
  Finset.sum_nonpos fun k _ ↦ Proj_coord_nonpos hm hM k

/-- The coordinate-wise squared bound underlying (D3.13): the projection can only
shrink a coordinate, so `(proj y θ̂)² ≤ y²`. -/
private lemma projCoord_sq_le (m M y theta : ℝ) : projCoord m M y theta ^ 2 ≤ y ^ 2 := by
  simp only [projCoord]
  split_ifs <;> simp [sq_nonneg]

/-- **D3.13 (Theorem D3.2, squared `ℓ²` form)**: for any estimate `θ̂` and any `y`,
`∑ k, (Proj y θ̂ k)² ≤ ∑ k, (y k)²`. -/
theorem Proj_sum_sq_le {i : Type*} [Fintype i] {m M y thetaHat : i → ℝ} :
    ∑ k, (Proj m M y thetaHat k)^2 ≤ ∑ k, (y k)^2 := by
  apply Finset.sum_le_sum
  intro k _
  simp only [Proj]
  exact projCoord_sq_le (m k) (M k) (y k) (thetaHat k)
