/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace

/-! # The discrete matrix-Lyapunov quadratic-form toolkit

This file collects the generic, control-theory-independent facts about the
quadratic form `x ↦ xᵀ P x` of a real square matrix `P` that are used by the
discrete-time matrix-Lyapunov and switched-stability theory of the library.

For a real square matrix `P : Matrix (Fin m) (Fin m) ℝ` we write
`quadForm P x = x ⬝ᵥ (P *ᵥ x)`. The file provides:

* basic algebraic identities for `quadForm` (zero, transformation under a linear
  substitution, additivity in the matrix, homogeneity);
* nonnegativity and positivity for positive semi-definite / positive definite
  `P`, and the vanishing criterion `quadForm P x = 0 ↔ x = 0`;
* the strict decrease `quadForm_mulVec_lt`: if `Q - Mᵀ P M` is positive definite
  then `quadForm P (M x) < quadForm Q x`;
* geometric iteration of a decrease (`quadForm_pow_mulVec_le`);
* coercivity of a positive definite quadratic form on the unit sphere and on the
  whole space, and the existence of a uniform contraction factor `c ∈ [0, 1)`.

These lemmas are stated for `Fin m`-indexed vectors and real scalar (with
`star_trivial`). The switching-specific minimum-dwell-time theorem of
Geromel–Colaneri that consumes them lives in
`DynamicalSystems.AdaptiveControl.Switching`.
-/

@[expose] public section

open scoped Topology Matrix

variable {m : ℕ}

/-! ## The quadratic form of a matrix

The Lyapunov function of the Geromel–Colaneri theorem is `x ↦ xᵀ P x`. The lemmas
below record the elementary algebraic facts about this quadratic form that the
proof needs. -/

/-- The quadratic form `x ↦ xᵀ P x` of a real square matrix `P`. -/
def quadForm (P : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ) : ℝ := x ⬝ᵥ (P *ᵥ x)

/-- The quadratic form of the zero matrix vanishes. -/
@[simp]
theorem quadForm_zero (P : Matrix (Fin m) (Fin m) ℝ) : quadForm P (0 : Fin m → ℝ) = 0 := by
  simp only [quadForm, Matrix.mulVec_zero, dotProduct_zero]

/-- The quadratic form is continuous. -/
theorem quadForm_continuous (P : Matrix (Fin m) (Fin m) ℝ) : Continuous (quadForm P) := by
  change Continuous (fun x : Fin m → ℝ ↦ x ⬝ᵥ (P *ᵥ x))
  exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)

/-- The quadratic form of a positive semi-definite matrix is non-negative. -/
theorem quadForm_nonneg {P : Matrix (Fin m) (Fin m) ℝ} (hP : P.PosSemidef) (x : Fin m → ℝ) :
    0 ≤ quadForm P x := by
  simpa only [quadForm, star_trivial] using hP.dotProduct_mulVec_nonneg x

/-- The quadratic form of a positive definite matrix is positive on non-zero vectors. -/
theorem quadForm_pos {P : Matrix (Fin m) (Fin m) ℝ} (hP : P.PosDef) {x : Fin m → ℝ}
    (hx : x ≠ 0) : 0 < quadForm P x := by
  simpa only [quadForm, star_trivial] using hP.dotProduct_mulVec_pos hx

/-- The quadratic form of a positive definite matrix vanishes only at the origin. -/
theorem quadForm_eq_zero_iff {P : Matrix (Fin m) (Fin m) ℝ} (hP : P.PosDef) (x : Fin m → ℝ) :
    quadForm P x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact (quadForm_pos hP hx).ne' h
  · rintro rfl
    exact quadForm_zero P

/-- The quadratic form transforms under a linear substitution: applying `M` and
measuring with `P` is the same as measuring the original vector with
`Mᵀ P M`. -/
theorem quadForm_mulVec (P : Matrix (Fin m) (Fin m) ℝ) (M : Matrix (Fin m) (Fin m) ℝ)
    (x : Fin m → ℝ) : quadForm P (M *ᵥ x) = quadForm (Mᵀ * P * M) x := by
  simp only [quadForm, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_mulVec, Matrix.vecMul_transpose]

/-- The quadratic form is additive in the matrix. -/
theorem quadForm_sub (P Q : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ) :
    quadForm (P - Q) x = quadForm P x - quadForm Q x := by
  simp only [quadForm, Matrix.sub_mulVec, dotProduct_sub]

/-- If `Q - Mᵀ P M` is positive definite, then substituting `M` into the `P`-form
strictly decreases the quadratic form compared with the `Q`-form. -/
theorem quadForm_mulVec_lt {P Q : Matrix (Fin m) (Fin m) ℝ} {M : Matrix (Fin m) (Fin m) ℝ}
    (h : (Q - Mᵀ * P * M).PosDef) {x : Fin m → ℝ} (hx : x ≠ 0) :
    quadForm P (M *ᵥ x) < quadForm Q x := by
  rw [quadForm_mulVec, ← sub_pos, ← quadForm_sub]
  exact quadForm_pos h hx

/-! ## Homogeneity, iteration, and coercivity of the quadratic form -/

/-- The quadratic form is homogeneous of degree two. -/
theorem quadForm_smul (P : Matrix (Fin m) (Fin m) ℝ) (r : ℝ) (x : Fin m → ℝ) :
    quadForm P (r • x) = r ^ 2 * quadForm P x := by
  simp only [quadForm, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- Iterating a one-step quadratic-form decrease. If `quadForm P (M *ᵥ ·) ≤ c * quadForm P ·`
with `0 ≤ c`, then `quadForm P ((M ^ k) *ᵥ ·) ≤ c ^ k * quadForm P ·`. -/
theorem quadForm_pow_mulVec_le {P M : Matrix (Fin m) (Fin m) ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, quadForm P (M *ᵥ x) ≤ c * quadForm P x) (k : ℕ) (x : Fin m → ℝ) :
    quadForm P ((M ^ k) *ᵥ x) ≤ c ^ k * quadForm P x := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        quadForm P ((M ^ k.succ) *ᵥ x)
            = quadForm P (M *ᵥ ((M ^ k) *ᵥ x)) := by
              rw [pow_succ', Matrix.mulVec_mulVec]
        _ ≤ c * quadForm P ((M ^ k) *ᵥ x) := h _
        _ ≤ c * (c ^ k * quadForm P x) := by gcongr
        _ = c ^ k.succ * quadForm P x := by rw [pow_succ']; ring

/-- A positive definite matrix gives a positive lower bound for its quadratic form on the
unit sphere. This is the coercivity input obtained from compactness of the sphere. -/
theorem exists_pos_le_quadForm_sphere {P : Matrix (Fin m) (Fin m) ℝ} (hP : P.PosDef)
    (hne : Nonempty (Fin m)) : ∃ a > 0, ∀ x : Fin m → ℝ, ‖x‖ = 1 → a ≤ quadForm P x := by
  have hne' : (Metric.sphere (0 : Fin m → ℝ) 1).Nonempty := by
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin m → ℝ)
    refine ⟨(‖v‖)⁻¹ • v, ?_⟩
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  obtain ⟨x₀, hx₀, hmax⟩ :=
    (isCompact_sphere (0 : Fin m → ℝ) 1).exists_isMinOn hne' ((quadForm_continuous P).continuousOn)
  refine ⟨quadForm P x₀, ?_, fun x hx ↦ hmax ?_⟩
  · rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx₀
    exact quadForm_pos hP (norm_ne_zero_iff.mp (by rw [hx₀]; exact one_ne_zero))
  · rwa [Metric.mem_sphere, dist_eq_norm, sub_zero]

/-- Coercivity of the quadratic form of a positive definite matrix: there is `a > 0` with
`a * ‖x‖ ^ 2 ≤ quadForm P x` for all `x`. -/
theorem exists_coercive_quadForm {P : Matrix (Fin m) (Fin m) ℝ} (hP : P.PosDef)
    (hne : Nonempty (Fin m)) : ∃ a > 0, ∀ x : Fin m → ℝ, a * ‖x‖ ^ 2 ≤ quadForm P x := by
  obtain ⟨a, ha, hle⟩ := exists_pos_le_quadForm_sphere hP hne
  refine ⟨a, ha, fun x ↦ ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hunit : ‖(‖x‖)⁻¹ • x‖ = 1 := by
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
    have hsplit : x = ‖x‖ • ((‖x‖)⁻¹ • x) := by
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]
    conv_rhs => rw [hsplit]
    rw [quadForm_smul]
    calc a * ‖x‖ ^ 2 = ‖x‖ ^ 2 * a := by ring
      _ ≤ ‖x‖ ^ 2 * quadForm P ((‖x‖)⁻¹ • x) :=
          mul_le_mul_of_nonneg_left (hle _ hunit) (sq_nonneg _)


/-- A single uniform contraction factor for a transition `Q - Mᵀ P M` that is positive
definite: there is `c ∈ [0, 1)` with `quadForm P (M *ᵥ x) ≤ c * quadForm Q x`.

This is the compactness step: the ratio of the two quadratic forms is continuous on the
unit sphere and strictly below `1`; the maximum over the compact sphere is the factor. -/
theorem exists_factor {P Q M : Matrix (Fin m) (Fin m) ℝ} (hP : P.PosDef) (hQ : Q.PosDef)
    (h : (Q - Mᵀ * P * M).PosDef) (hne : Nonempty (Fin m)) :
    ∃ c, 0 ≤ c ∧ c < 1 ∧ ∀ x, quadForm P (M *ᵥ x) ≤ c * quadForm Q x := by
  have hnum : Continuous fun x : Fin m → ℝ ↦ quadForm P (M *ᵥ x) :=
    (quadForm_continuous P).comp (continuous_const.matrix_mulVec continuous_id)
  have hSne : (Metric.sphere (0 : Fin m → ℝ) 1).Nonempty := by
    obtain ⟨v, hv⟩ := exists_ne (0 : Fin m → ℝ)
    exact ⟨(‖v‖)⁻¹ • v, by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg v), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]⟩
  have hden : ∀ x ∈ Metric.sphere (0 : Fin m → ℝ) 1, quadForm Q x ≠ 0 := by
    intro x hx
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx
    exact fun hq ↦ (norm_ne_zero_iff.mp (by rw [hx]; exact one_ne_zero))
      ((quadForm_eq_zero_iff hQ x).mp hq)
  have hcont : ContinuousOn (fun x : Fin m → ℝ ↦ quadForm P (M *ᵥ x) / quadForm Q x)
      (Metric.sphere (0 : Fin m → ℝ) 1) :=
    hnum.continuousOn.div (quadForm_continuous Q).continuousOn hden
  obtain ⟨x₀, hx₀, hmax⟩ :=
    (isCompact_sphere (0 : Fin m → ℝ) 1).exists_isMaxOn hSne hcont
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx₀
  have hx₀ne : x₀ ≠ 0 := norm_ne_zero_iff.mp (by rw [hx₀]; exact one_ne_zero)
  have hqQpos : 0 < quadForm Q x₀ := quadForm_pos hQ hx₀ne
  refine ⟨quadForm P (M *ᵥ x₀) / quadForm Q x₀, div_nonneg (quadForm_nonneg hP.posSemidef _)
    hqQpos.le, ?_, fun x ↦ ?_⟩
  · rw [div_lt_one hqQpos]
    exact quadForm_mulVec_lt h hx₀ne
  · rcases eq_or_ne x 0 with rfl | hx
    · simp
    · set r : ℝ := (‖x‖)⁻¹ with hr
      have hunit : ‖r • x‖ = 1 := by
        rw [hr, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x),
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
      have hmem : r • x ∈ Metric.sphere (0 : Fin m → ℝ) 1 := by
        rwa [Metric.mem_sphere, dist_eq_norm, sub_zero]
      have hg : quadForm P (M *ᵥ (r • x)) / quadForm Q (r • x)
          = quadForm P (M *ᵥ x) / quadForm Q x := by
        rw [Matrix.mulVec_smul, quadForm_smul, quadForm_smul]
        have hr_ne : r ≠ 0 := by rw [hr]; exact inv_ne_zero (norm_ne_zero_iff.mpr hx)
        field_simp [hr_ne]
      have hle : quadForm P (M *ᵥ x) / quadForm Q x
          ≤ quadForm P (M *ᵥ x₀) / quadForm Q x₀ := by
        have h := hmax hmem
        simp only [Set.mem_ofPred_eq] at h
        rwa [hg] at h
      exact (div_le_iff₀ (quadForm_pos hQ hx)).mp hle
