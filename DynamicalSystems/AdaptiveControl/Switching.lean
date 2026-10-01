/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.DiscreteTime.Basic
public import DynamicalSystems.Stability.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Algebra.Order.Field
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace

/-! # Dwell-time switching stability (Geromel–Colaneri, Theorem 13.1)

This file formalizes the discrete-time minimum-dwell-time stability theorem of
Geromel and Colaneri, as presented in I. D. Landau, R. Lozano, M'Saad and
A. Karimi, *Adaptive Control: Algorithms, Analysis and Applications*, 2nd ed.,
Springer 2011, Theorem 13.1 (printed pp. 463–465).

For a family of matrices `A i` and positive-definite matrices `P i`, the
hypotheses are

* `Aᵢᵀ Pᵢ Aᵢ - Pᵢ < 0` (13.3), and
* `(Aᵢᵀ)^Td Pⱼ (Aᵢ)^Td - Pᵢ < 0` for `i ≠ j` (13.4).

The conclusion is that every switching signal whose switch instants are at least
`Td` apart makes the origin globally asymptotically stable for the switched linear
system `x (t + 1) = A (σ t) x t`.

## Main definitions

* `IsDwellTimeSwitching σ Td`: the switch instants of `σ` are at least `Td`
  steps apart.
* `switchedFlow A σ t x`: the trajectory of `x (t + 1) = A (σ t) x t` starting at
  `x` at time `0` (the recursive `t`-fold product, *not* a single step).

## Main results

* `asymptoticallyStable_switching_of_dwellTime`: the Geromel–Colaneri theorem.

## Implementation notes

The hypotheses (13.3) and (13.4) are stated as positive definiteness of the
*negated* matrix: `(P i - Aᵢᵀ Pᵢ Aᵢ).PosDef` and
`(P i - (Aᵢᵀ)^Td Pⱼ (Aᵢ)^Td).PosDef`. Mathlib has no `Matrix.NegDef`, so strict
negative definiteness of a matrix `M` is spelled `(-M).PosDef`.
-/

@[expose] public section

open Filter
open scoped Topology Matrix

variable {n m : ℕ}

/-- A switching signal `σ` with minimum dwell time `Td`: every switch instant is
followed by at least `Td` steps in the new mode, and the initial mode also lasts
at least `Td` steps. Thus two consecutive switch instants are `≥ Td` apart. -/
def IsDwellTimeSwitching (σ : ℕ → Fin n) (Td : ℕ) : Prop :=
  (∀ s, s < Td → σ s = σ 0) ∧
    ∀ t, σ t ≠ σ (t + 1) → ∀ s, t + 1 ≤ s → s ≤ t + Td → σ s = σ (t + 1)

/-- The trajectory of the switched linear system `x (t + 1) = A (σ t) x t`,
starting at `x` at time `0`. This is the recursive `t`-fold product
`A (σ (t - 1)) ⋯ A (σ 0)` applied to `x`, *not* the single step `t ↦ A (σ t) x`. -/
def switchedFlow (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (σ : ℕ → Fin n) :
    ℕ → (Fin m → ℝ) → (Fin m → ℝ)
  | 0, x => x
  | t + 1, x => (A (σ t)) *ᵥ switchedFlow A σ t x

/-- The zeroth iterate of `switchedFlow` is the identity. -/
@[simp]
theorem switchedFlow_zero (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (σ : ℕ → Fin n) :
    switchedFlow A σ 0 = id := by
  funext x
  rfl

/-- The successor iterate of `switchedFlow` is one step `A (σ t)` applied to the
`t`-th iterate. -/
theorem switchedFlow_succ (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (σ : ℕ → Fin n) (t : ℕ) :
    switchedFlow A σ (t + 1) = fun x ↦ (A (σ t)) *ᵥ switchedFlow A σ t x := by
  rfl

/-- Pointwise successor iterate of `switchedFlow`. -/
theorem switchedFlow_succ_apply (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (σ : ℕ → Fin n)
    (t : ℕ) (x : Fin m → ℝ) :
    switchedFlow A σ (t + 1) x = (A (σ t)) *ᵥ switchedFlow A σ t x := by
  rfl

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

/-- A single step of mode `i` strictly decreases the associated quadratic form
(inequality (13.3)). -/
theorem quadForm_step_lt {A : Fin n → Matrix (Fin m) (Fin m) ℝ}
    {P : Fin n → Matrix (Fin m) (Fin m) ℝ} (h1 : ∀ i, (P i - (A i)ᵀ * P i * A i).PosDef)
    (i : Fin n) {x : Fin m → ℝ} (hx : x ≠ 0) :
    quadForm (P i) (A i *ᵥ x) < quadForm (P i) x := by
  have := quadForm_mulVec_lt (h1 i) hx
  simpa only [quadForm_mulVec] using this

/-- A switch from mode `i` to mode `j` after `Td` steps strictly decreases the
quadratic form (inequality (13.4)). -/
theorem quadForm_switch_lt {A : Fin n → Matrix (Fin m) (Fin m) ℝ}
    {P : Fin n → Matrix (Fin m) (Fin m) ℝ} {Td : ℕ}
    (h2 : ∀ i j, i ≠ j → (P i - (A i)ᵀ ^ Td * P j * A i ^ Td).PosDef)
    {i j : Fin n} (hij : i ≠ j) {x : Fin m → ℝ} (hx : x ≠ 0) :
    quadForm (P j) ((A i ^ Td) *ᵥ x) < quadForm (P i) x := by
  have htrans : ((A i ^ Td)ᵀ * P j * A i ^ Td) = ((A i)ᵀ ^ Td) * P j * A i ^ Td := by
    rw [Matrix.transpose_pow]
  have := quadForm_mulVec_lt (P := P j) (Q := P i) (M := A i ^ Td) ?_ hx
  · simpa only [quadForm_mulVec] using this
  · rw [htrans]
    exact h2 i j hij

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
private theorem exists_pos_le_quadForm_sphere {P : Matrix (Fin m) (Fin m) ℝ} (hP : P.PosDef)
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
private theorem exists_coercive_quadForm {P : Matrix (Fin m) (Fin m) ℝ} (hP : P.PosDef)
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
private theorem exists_factor {P Q M : Matrix (Fin m) (Fin m) ℝ} (hP : P.PosDef) (hQ : Q.PosDef)
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

/-- A single uniform factor `c ∈ [0, 1)` bounding both the within-mode decrease (13.3)
and the switch decrease (13.4). -/
private theorem exists_uniform_factor {A P : Fin n → Matrix (Fin m) (Fin m) ℝ} {Td : ℕ}
    (hP : ∀ i, (P i).PosDef)
    (h1 : ∀ i, (P i - (A i)ᵀ * P i * A i).PosDef)
    (h2 : ∀ i j, i ≠ j → (P i - (A i)ᵀ ^ Td * P j * A i ^ Td).PosDef)
    (hne : Nonempty (Fin m)) (hn : Nonempty (Fin n)) :
    ∃ c, 0 ≤ c ∧ c < 1 ∧
      (∀ i x, quadForm (P i) (A i *ᵥ x) ≤ c * quadForm (P i) x) ∧
      (∀ i j, i ≠ j → ∀ x, quadForm (P j) ((A i ^ Td) *ᵥ x) ≤ c * quadForm (P i) x) := by
  have hstep : ∀ i, ∃ c, 0 ≤ c ∧ c < 1 ∧
      ∀ x, quadForm (P i) (A i *ᵥ x) ≤ c * quadForm (P i) x :=
    fun i ↦ exists_factor (hP i) (hP i) (h1 i) hne
  let cs : Fin n → ℝ := fun i ↦ Classical.choose (hstep i)
  have hcs : ∀ i, 0 ≤ cs i ∧ cs i < 1 ∧
      ∀ x, quadForm (P i) (A i *ᵥ x) ≤ cs i * quadForm (P i) x :=
    fun i ↦ Classical.choose_spec (hstep i)
  have hsw : ∀ i j, i ≠ j → ∃ c, 0 ≤ c ∧ c < 1 ∧
      ∀ x, quadForm (P j) ((A i ^ Td) *ᵥ x) ≤ c * quadForm (P i) x :=
    fun i j hij ↦ exists_factor (hP j) (hP i) (by
      simpa only [Matrix.transpose_pow] using h2 i j hij) hne
  let cw : Fin n → Fin n → ℝ :=
    fun i j ↦ if h : i = j then 0 else Classical.choose (hsw i j h)
  have hcw : ∀ i j, i ≠ j → 0 ≤ cw i j ∧ cw i j < 1 ∧
      ∀ x, quadForm (P j) ((A i ^ Td) *ᵥ x) ≤ cw i j * quadForm (P i) x := by
    intro i j hij
    simp only [cw, dite_eq_right hij]
    exact Classical.choose_spec (hsw i j hij)
  let f : Fin n ⊕ (Fin n × Fin n) → ℝ := fun idx ↦
    match idx with
    | Sum.inl i => cs i
    | Sum.inr p => if p.1 = p.2 then 0 else cw p.1 p.2
  let Hne : (Finset.univ : Finset (Fin n ⊕ (Fin n × Fin n))).Nonempty :=
    ⟨Sum.inl hn.some, Finset.mem_univ _⟩
  refine ⟨(Finset.univ : Finset (Fin n ⊕ (Fin n × Fin n))).sup' Hne f, ?_, ?_, ?_, ?_⟩
  · have hsup := Finset.le_sup' f (Finset.mem_univ (Sum.inl hn.some))
    exact (hcs hn.some).1.trans (by simpa only [f] using hsup)
  · refine (Finset.sup'_lt_iff Hne).mpr (fun idx _ ↦ ?_)
    rcases idx with i | ⟨i, j⟩
    · exact (hcs i).2.1
    · by_cases hij : i = j
      · simp only [f, ite_eq_left hij]; norm_num
      · simp only [f, ite_eq_right hij]
        exact (hcw i j hij).2.1
  · intro i x
    calc quadForm (P i) (A i *ᵥ x) ≤ cs i * quadForm (P i) x := (hcs i).2.2 x
      _ ≤ (Finset.univ.sup' Hne f) * quadForm (P i) x :=
          mul_le_mul_of_nonneg_right (Finset.le_sup' f (Finset.mem_univ (Sum.inl i)))
            (quadForm_nonneg (hP i).posSemidef x)
  · intro i j hij x
    have hfsup : cw i j ≤ Finset.univ.sup' Hne f := by
      have h := Finset.le_sup' f (Finset.mem_univ (Sum.inr (i, j)))
      simpa only [f, ite_eq_right hij] using h
    calc quadForm (P j) ((A i ^ Td) *ᵥ x) ≤ cw i j * quadForm (P i) x := (hcw i j hij).2.2 x
      _ ≤ (Finset.univ.sup' Hne f) * quadForm (P i) x :=
          mul_le_mul_of_nonneg_right hfsup (quadForm_nonneg (hP i).posSemidef x)

/-- The last switch instant at or before time `t`: the largest `s ≤ t` that is either the
initial time or a time at which the mode changes. -/
private def lastSwitch (σ : ℕ → Fin n) (t : ℕ) : ℕ :=
  Nat.findGreatest (fun s ↦ s = 0 ∨ σ s ≠ σ (s - 1)) t

private theorem lastSwitch_le (σ : ℕ → Fin n) (t : ℕ) : lastSwitch σ t ≤ t :=
  Nat.findGreatest_le t

private theorem lastSwitch_spec (σ : ℕ → Fin n) (t : ℕ) :
    lastSwitch σ t = 0 ∨ σ (lastSwitch σ t) ≠ σ (lastSwitch σ t - 1) :=
  Nat.findGreatest_spec (P := fun s ↦ s = 0 ∨ σ s ≠ σ (s - 1)) (Nat.zero_le t) (Or.inl rfl)

/-- The mode is constant between the last switch instant and `t`. -/
private theorem lastSwitch_const (σ : ℕ → Fin n) (t : ℕ) :
    ∀ u, lastSwitch σ t ≤ u → u ≤ t → σ u = σ (lastSwitch σ t) := by
  intro u hu
  induction u, hu using Nat.le_induction with
  | base => intro _; rfl
  | succ n _ ih =>
      intro hnt
      have hnot : ¬(n + 1 = 0 ∨ σ (n + 1) ≠ σ (n + 1 - 1)) := by
        intro hP
        have hle : n + 1 ≤ lastSwitch σ t := Nat.le_findGreatest (by omega) hP
        omega
      have hsame : σ (n + 1) = σ n := by
        by_contra hne
        exact hnot (Or.inr hne)
      rw [hsame]
      exact ih (by omega)

/-- At a genuine switch at time `t`, the mode that just ended was active for at least
`Td` steps: `Td ≤ t - lastSwitch σ (t - 1)`. -/
private theorem lastSwitch_switch_gap {σ : ℕ → Fin n} {Td : ℕ}
    (hσ : IsDwellTimeSwitching σ Td) {t : ℕ} (ht : 0 < t)
    (hdiff : σ t ≠ σ (t - 1)) : Td ≤ t - lastSwitch σ (t - 1) := by
  set τ := lastSwitch σ (t - 1) with hτdef
  have hτle : τ ≤ t - 1 := lastSwitch_le σ (t - 1)
  rcases eq_or_lt_of_le (Nat.zero_le τ) with hτ0 | hτpos
  · -- the initial mode is subject to the initial dwell condition
    rw [hτ0.symm, Nat.sub_zero]
    by_contra hlt
    rw [not_le] at hlt
    have h1 : σ t = σ 0 := hσ.1 t (by omega)
    have h2 : σ (t - 1) = σ 0 := hσ.1 (t - 1) (by omega)
    exact hdiff (by rw [h1, h2])
  · -- the mode started at `τ`, which is a switch instant
    have hspec : τ = 0 ∨ σ τ ≠ σ (τ - 1) := lastSwitch_spec σ (t - 1)
    have hsw : σ (τ - 1) ≠ σ τ := by
      rcases hspec with h | h
      · omega
      · exact h.symm
    have hτeq : τ - 1 + 1 = τ := by omega
    have hsw' : σ (τ - 1) ≠ σ (τ - 1 + 1) := by rwa [hτeq]
    have hconst := hσ.2 (τ - 1) hsw'
    have hconst' : ∀ s, τ ≤ s → s ≤ τ + Td - 1 → σ s = σ τ := by
      intro s hs hst
      have h := hconst s (by omega) (by omega)
      rwa [hτeq] at h
    by_contra hlt
    rw [not_le] at hlt
    have h1 : σ (t - 1) = σ τ := hconst' (t - 1) (by omega) (by omega)
    have h2 : σ t = σ τ := hconst' t (by omega) (by omega)
    exact hdiff (by rw [h1, h2])

/-- A mode held constant for `k` steps composes into the `k`-th power of its matrix. -/
private theorem switchedFlow_const_mode {A : Fin n → Matrix (Fin m) (Fin m) ℝ}
    {σ : ℕ → Fin n} {i : Fin n} {τ : ℕ} (k : ℕ) (x : Fin m → ℝ)
    (hconst : ∀ u, u ≤ k → σ (τ + u) = i) :
    switchedFlow A σ (τ + k) x = (A i) ^ k *ᵥ switchedFlow A σ τ x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, switchedFlow_succ_apply, hconst k (Nat.le_succ k)]
      rw [ih (fun u hu ↦ hconst u (Nat.le_trans hu (Nat.le_succ k)))]
      rw [Matrix.mulVec_mulVec, ← pow_succ']

/-- **Geromel–Colaneri (2006), Landau Theorem 13.1.** Assume there exist positive definite
matrices `P i` such that `Aᵢᵀ Pᵢ Aᵢ - Pᵢ < 0` for every mode and
`(Aᵢᵀ)^Td Pⱼ (Aᵢ)^Td - Pᵢ < 0` for every pair of distinct modes. Then every switching
signal whose switch instants are at least `Td` apart makes the origin globally
asymptotically stable for the switched linear system `x (t + 1) = A (σ t) x t`. -/
theorem asymptoticallyStable_switching_of_dwellTime {n m : ℕ}
    (A : Fin n → Matrix (Fin m) (Fin m) ℝ) (P : Fin n → Matrix (Fin m) (Fin m) ℝ)
    (Td : ℕ) (hTd : 1 ≤ Td) (σ : ℕ → Fin n) (hσ : IsDwellTimeSwitching σ Td)
    (hP : ∀ i, (P i).PosDef)
    (h1 : ∀ i, (P i - (A i)ᵀ * P i * A i).PosDef)
    (h2 : ∀ i j, i ≠ j → (P i - (A i)ᵀ ^ Td * P j * A i ^ Td).PosDef) :
    (𝓝 (0 : Fin m → ℝ)).IsStableOn (switchedFlow A σ) Set.univ ∧
      ∀ x, Tendsto (fun t ↦ switchedFlow A σ t x) atTop (𝓝 0) := by
  by_cases hn : n = 0
  · subst hn
    exact isEmptyElim (σ 0)
  by_cases hm : m = 0
  · subst hm
    constructor
    · intro s hs
      refine ⟨Set.univ, Filter.univ_mem, fun t _ x _ ↦ ?_⟩
      have hx : x = 0 := Subsingleton.elim x 0
      subst hx
      have hz : switchedFlow A σ t 0 = 0 := Subsingleton.elim _ _
      rw [hz]
      exact mem_of_mem_nhds hs
    · intro x
      have hconst : (fun t ↦ switchedFlow A σ t x) = fun _ ↦ (0 : Fin 0 → ℝ) := by
        funext t
        exact Subsingleton.elim _ _
      rw [hconst]
      exact tendsto_const_nhds
  have hn' : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  have hm' : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
  obtain ⟨c, hc0, hc1, hstep, hsw⟩ := exists_uniform_factor hP h1 h2 hm' hn'
  set d : ℝ := c ^ ((Td : ℝ)⁻¹) with hd
  have hd0 : 0 ≤ d := Real.rpow_nonneg hc0 _
  have hd1 : d < 1 := by
    rw [hd]
    exact (Real.rpow_lt_one_iff hc0).mpr (Or.inr (Or.inr ⟨hc1, by positivity⟩))
  have hcd : c ≤ d := by
    have h1 : (1 : ℝ) ≤ Td := by exact_mod_cast hTd
    have hz : (0 : ℝ) ≤ (Td : ℝ)⁻¹ := by positivity
    have hzy : (Td : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    calc c = c ^ (1 : ℝ) := (Real.rpow_one c).symm
      _ ≤ c ^ ((Td : ℝ)⁻¹) := Real.rpow_le_rpow_of_exponent_ge' hc0 hc1.le hz hzy
      _ = d := by rw [hd]
  have hswd : c ≤ d ^ Td := by
    rw [hd, Real.rpow_inv_natCast_pow hc0 (by omega)]
  have hbound : ∀ t (x : Fin m → ℝ),
      quadForm (P (σ t)) (switchedFlow A σ t x) ≤ d ^ t * quadForm (P (σ 0)) x := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro x
      rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp
      · have ht_eq : t = (t - 1) + 1 := (Nat.succ_pred_eq_of_pos ht).symm
        rcases eq_or_ne (σ t) (σ (t - 1)) with hsame | hdiff
        · -- the mode is unchanged
          have hrec : switchedFlow A σ t x
              = A (σ (t - 1)) *ᵥ switchedFlow A σ (t - 1) x := by
            conv_lhs => rw [ht_eq]
            rw [switchedFlow_succ_apply]
          rw [hrec, hsame]
          have hq0 : 0 ≤ quadForm (P (σ 0)) x := quadForm_nonneg (hP (σ 0)).posSemidef x
          have hpow : 0 ≤ d ^ (t - 1) := pow_nonneg hd0 _
          calc quadForm (P (σ (t - 1))) (A (σ (t - 1)) *ᵥ switchedFlow A σ (t - 1) x)
              ≤ c * quadForm (P (σ (t - 1))) (switchedFlow A σ (t - 1) x) :=
                hstep (σ (t - 1)) _
            _ ≤ c * (d ^ (t - 1) * quadForm (P (σ 0)) x) :=
                mul_le_mul_of_nonneg_left (ih (t - 1) (by omega) x) hc0
            _ = (c * d ^ (t - 1)) * quadForm (P (σ 0)) x := by ring
            _ ≤ (d * d ^ (t - 1)) * quadForm (P (σ 0)) x :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcd hpow) hq0
            _ = d ^ t * quadForm (P (σ 0)) x := by
                have hdt : d * d ^ (t - 1) = d ^ t := by
                  rw [← pow_succ']
                  congr 1
                  omega
                rw [hdt]
        · -- a genuine switch
          set τ := lastSwitch σ (t - 1) with hτdef
          set i := σ (t - 1) with hidef
          set j := σ t with hjdef
          have hij : i ≠ j := fun h ↦ hdiff (calc
            σ t = j := hjdef.symm
            _ = i := h.symm
            _ = σ (t - 1) := hidef)
          have hgap : Td ≤ t - τ := lastSwitch_switch_gap hσ ht hdiff
          have hτle : τ ≤ t - 1 := lastSwitch_le σ (t - 1)
          have hτσ : σ (lastSwitch σ (t - 1)) = σ (t - 1) :=
            (lastSwitch_const σ (t - 1) (t - 1) (lastSwitch_le σ (t - 1)) le_rfl).symm
          have hconst : ∀ u, τ ≤ u → u ≤ t - 1 → σ u = i := by
            intro u hu hut
            have h1 := lastSwitch_const σ (t - 1) u (by rw [← hτdef]; exact hu) hut
            rw [hidef, ← hτσ]
            exact h1
          have hmode : switchedFlow A σ (t - 1) x
              = (A i) ^ ((t - 1) - τ) *ᵥ switchedFlow A σ τ x := by
            have h := switchedFlow_const_mode (A := A) (i := i) (τ := τ) ((t - 1) - τ) x
              (fun u _ ↦ hconst (τ + u) (Nat.le_add_right _ _) (by omega))
            rwa [Nat.add_sub_cancel' hτle] at h
          have hrec : switchedFlow A σ t x
              = A i *ᵥ switchedFlow A σ (t - 1) x := by
            conv_lhs => rw [ht_eq]
            rw [switchedFlow_succ_apply, hidef]
          have hm_eq : (t - 1) - τ + 1 = t - τ := by omega
          have hxτ : switchedFlow A σ t x = (A i) ^ (t - τ) *ᵥ switchedFlow A σ τ x := by
            rw [hrec, hmode, ← hm_eq, pow_succ', Matrix.mulVec_mulVec]
          rw [hxτ]
          have hmTd : t - τ = Td + (t - τ - Td) := by omega
          have hpow_split : (A i) ^ (t - τ) = (A i) ^ Td * (A i) ^ (t - τ - Td) := by
            rw [← pow_add, show Td + (t - τ - Td) = t - τ by omega]
          rw [hpow_split, ← Matrix.mulVec_mulVec]
          have hq0 : 0 ≤ quadForm (P (σ 0)) x := quadForm_nonneg (hP (σ 0)).posSemidef x
          have hqτ : 0 ≤ d ^ τ := pow_nonneg hd0 _
          have hqstep : 0 ≤ quadForm (P i) (switchedFlow A σ τ x) :=
            quadForm_nonneg (hP i).posSemidef _
          have hih := ih τ (by omega) x
          have hconst_i : σ τ = i := hconst τ le_rfl (by omega)
          rw [hconst_i] at hih
          calc quadForm (P j) ((A i) ^ Td *ᵥ ((A i) ^ (t - τ - Td) *ᵥ switchedFlow A σ τ x))
              ≤ c * quadForm (P i) ((A i) ^ (t - τ - Td) *ᵥ switchedFlow A σ τ x) :=
                hsw i j hij _
            _ ≤ c * (c ^ (t - τ - Td) * quadForm (P i) (switchedFlow A σ τ x)) :=
                mul_le_mul_of_nonneg_left
                  (quadForm_pow_mulVec_le hc0 (hstep i) (t - τ - Td)
                    (switchedFlow A σ τ x)) hc0
            _ = (c * c ^ (t - τ - Td)) * quadForm (P i) (switchedFlow A σ τ x) := by ring
            _ ≤ (d ^ Td * d ^ (t - τ - Td)) * quadForm (P i) (switchedFlow A σ τ x) := by
                apply mul_le_mul_of_nonneg_right _ hqstep
                apply mul_le_mul
                · exact hswd
                · exact pow_le_pow_left₀ hc0 hcd (t - τ - Td)
                · exact pow_nonneg hc0 _
                · exact pow_nonneg hd0 _
            _ = d ^ (t - τ) * quadForm (P i) (switchedFlow A σ τ x) := by
                rw [← pow_add, show Td + (t - τ - Td) = t - τ by omega]
            _ ≤ d ^ (t - τ) * (d ^ τ * quadForm (P (σ 0)) x) :=
                mul_le_mul_of_nonneg_left hih (pow_nonneg hd0 _)
            _ = d ^ t * quadForm (P (σ 0)) x := by
                rw [← mul_assoc, ← pow_add, show t - τ + τ = t by omega]
  -- coercivity: a uniform positive lower bound for all quadratic forms
  have hcoer : ∃ a > 0, ∀ i (x : Fin m → ℝ), a * ‖x‖ ^ 2 ≤ quadForm (P i) x := by
    choose a' ha' hle' using fun i ↦ exists_coercive_quadForm (hP i) hm'
    let Hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨hn'.some, Finset.mem_univ _⟩
    let a : ℝ := Finset.univ.inf' Hne a'
    have ha : 0 < a := by
      change 0 < Finset.univ.inf' Hne a'
      rw [Finset.lt_inf'_iff]
      exact fun i _ ↦ ha' i
    refine ⟨a, ha, fun i x ↦ ?_⟩
    calc a * ‖x‖ ^ 2 ≤ a' i * ‖x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (Finset.inf'_le a' (Finset.mem_univ i)) (sq_nonneg _)
      _ ≤ quadForm (P i) x := hle' i x
  obtain ⟨a, ha, hcoer⟩ := hcoer
  have hquadcont : Continuous (quadForm (P (σ 0))) := quadForm_continuous _
  constructor
  · -- Lyapunov stability
    rw [(Metric.nhds_basis_ball (x := (0 : Fin m → ℝ))).isStableOn_iff]
    intro ε hε
    have haε : 0 < a * ε ^ 2 := mul_pos ha (pow_pos hε 2)
    have hmem : {y : Fin m → ℝ | quadForm (P (σ 0)) y < a * ε ^ 2} ∈ 𝓝 (0 : Fin m → ℝ) := by
      have hmem' : Set.Iio (a * ε ^ 2) ∈ 𝓝 (quadForm (P (σ 0)) (0 : Fin m → ℝ)) := by
        rw [quadForm_zero]
        exact isOpen_Iio.mem_nhds haε
      exact hquadcont.continuousAt.tendsto.eventually hmem'
    rw [Metric.mem_nhds_iff] at hmem
    obtain ⟨η, hη, hsub⟩ := hmem
    refine ⟨η, hη, fun t _ x hx ↦ ?_⟩
    rw [Metric.mem_ball] at hx ⊢
    have hx' : quadForm (P (σ 0)) x < a * ε ^ 2 := hsub (by rwa [Metric.mem_ball])
    have hb := hbound t x
    have hd1' : d ^ t ≤ 1 := pow_le_one₀ hd0 hd1.le
    have hb' : quadForm (P (σ t)) (switchedFlow A σ t x) ≤ quadForm (P (σ 0)) x := by
      calc quadForm (P (σ t)) (switchedFlow A σ t x) ≤ d ^ t * quadForm (P (σ 0)) x := hb
        _ ≤ 1 * quadForm (P (σ 0)) x :=
            mul_le_mul_of_nonneg_right hd1' (quadForm_nonneg (hP (σ 0)).posSemidef x)
        _ = quadForm (P (σ 0)) x := one_mul _
    have hlt : a * ‖switchedFlow A σ t x‖ ^ 2 < a * ε ^ 2 :=
      lt_of_le_of_lt (hcoer (σ t) _) (lt_of_le_of_lt hb' hx')
    have hsq : ‖switchedFlow A σ t x‖ ^ 2 < ε ^ 2 := by nlinarith [hlt, ha]
    rw [dist_eq_norm, sub_zero]
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hε.le (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
  · -- global attraction
    intro x
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hq0 : 0 ≤ quadForm (P (σ 0)) x := quadForm_nonneg (hP (σ 0)).posSemidef x
    have hsq_tend : Tendsto (fun t : ℕ ↦ ‖switchedFlow A σ t x‖ ^ 2) atTop (𝓝 0) := by
      have hdecay : Tendsto (fun t : ℕ ↦ (quadForm (P (σ 0)) x / a) * d ^ t) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one hd0 hd1).const_mul
          (quadForm (P (σ 0)) x / a)
        simpa using this
      apply squeeze_zero (fun t ↦ sq_nonneg _) (fun t ↦ ?_) hdecay
      calc
        ‖switchedFlow A σ t x‖ ^ 2
            ≤ (1 / a) * quadForm (P (σ t)) (switchedFlow A σ t x) := by
              rw [one_div, inv_mul_eq_div]
              exact (le_div_iff₀ ha).mpr (by rw [mul_comm]; exact hcoer (σ t) _)
        _ ≤ (1 / a) * (d ^ t * quadForm (P (σ 0)) x) :=
              mul_le_mul_of_nonneg_left (hbound t x) (by positivity)
        _ = (quadForm (P (σ 0)) x / a) * d ^ t := by ring
    have hnorm : Tendsto (fun t : ℕ ↦ ‖switchedFlow A σ t x‖) atTop (𝓝 0) := by
      have hcomp : Tendsto (fun t : ℕ ↦ Real.sqrt (‖switchedFlow A σ t x‖ ^ 2)) atTop (𝓝 0) := by
        have hc := (Real.continuous_sqrt.tendsto 0).comp hsq_tend
        simpa only [Function.comp_def, Real.sqrt_zero] using hc
      have heq : (fun t : ℕ ↦ Real.sqrt (‖switchedFlow A σ t x‖ ^ 2))
          = fun t ↦ ‖switchedFlow A σ t x‖ := by
        funext t
        exact Real.sqrt_sq (norm_nonneg _)
      rwa [heq] at hcomp
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hnorm ε hε
    refine ⟨N, fun nn hn ↦ ?_⟩
    rw [dist_eq_norm, sub_zero]
    simpa only [dist_eq_norm, sub_zero, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      using hN nn hn
