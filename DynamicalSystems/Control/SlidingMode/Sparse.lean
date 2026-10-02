/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.SlidingMode.LMI

/-! # Sparse / decentralized structure for discrete-time sliding-mode control

This file formalizes the *structure* and *algebra* of the sparse, distributed and
decentralized sliding-mode control network of A. Argha, S. W. Su, L. Li and
H. T. Nguyen, *Advances in Discrete-Time Sliding Mode Control: Theory and
Applications*, CRC Press 2018, Chapter 6, §6.2–6.4 (printed pp. 116–126,
PDF pp. 140–150), together with a *structured-LMI stability implication*.

The large-scale networked plant is written at network level as
`x(k + 1) = [A + ΔA(k)] x(k) + B [u(k) + f(k)]` (eq. (6.6), printed p. 117),
where `A = [A_ij]` is the block interconnection matrix, `B = diag[B_i]` is the
block-diagonal input matrix and `Γ = [γ_ij]` is a given *structure matrix* whose
entry `γ_ij ∈ {0, 1}` says whether the `i`-th local controller may use the state
of subsystem `j` (eqs. (6.3)–(6.4), printed p. 117). Different choices of `Γ`
recover the fully decentralized (`Γ = I`), fully distributed (`Γ = S(A)`) and
sparsely distributed topologies (Remark 6.2, printed p. 121), and `Γ` is always a
subset of the plant network (Remark 6.3, printed p. 121).

## Main definitions

* `dsmcSparsityMask`: the Boolean support mask `S(Y)` of a structure matrix
  (Definition 6.1, printed p. 117). Its diagonal is always `true`, matching the
  book's convention that the diagonal of a structure matrix is `1`.
* `dsmcRespectsMask`: the subspace of controllers whose gain has support
  contained in the mask, the formal version of `S(K) ⊆ Γ` (Definition 6.3,
  printed p. 117).
* `dsmcMaskedGain`: the projection of an arbitrary gain onto the mask (the
  implemented sparse controller).
* `dsmcL1Penalty`: the weighted `ℓ¹` penalty `∑_{i,j} w_ij |K_ij|` used to promote
  sparsity of the gain (the reweighted-`ℓ¹` optimisation of Chapter 7 is *not*
  treated here).
* `dsmcStructuredLMI`: the structured (decentralized) version of the surface LMI
  `dsmcSurfaceLMI` of `DynamicalSystems.Control.SlidingMode.LMI`, evaluated on the
  masked closed loop.

## Main results

* the basic algebra of `dsmcL1Penalty`: nonnegativity, vanishing on the zero
  gain, absolute homogeneity, subadditivity and monotonicity;
* `dsmcL1Penalty_maskedGain_le`: projecting a gain onto the mask cannot increase
  its penalty;
* `dsmc_sparse_structured_stability`: a gain whose *masked* closed loop satisfies
  the structured LMI still yields the strict quadratic-form decrease of the
  network Lyapunov function, obtained by bridging to the Schur-complement surface
  LMI of slice D2 (`dsmc_sliding_surface_lmi`) and hence to
  `quadForm_mulVec_lt` of `DynamicalSystems.DiscreteTime.MatrixLyapunov`.

## Implementation notes

The quadratic-form toolkit (`quadForm`, `quadForm_mulVec_lt`) is reused from
`DynamicalSystems.DiscreteTime.MatrixLyapunov`; the surface LMI `dsmcSurfaceLMI`
and its Schur-complement reduction `dsmc_sliding_surface_lmi` are reused from
`DynamicalSystems.Control.SlidingMode.LMI`. No second quadratic form, no new
stability predicate and no continuous-time `IsHurwitz` hypothesis is introduced.

## Honest boundary

This slice proves the *static/algebraic* structure and the *implication*
“a controller satisfying the structured LMI yields the quadratic decrease”. It
does **not** prove feasibility of the block LMI (6.20) of Theorem 6.1
(printed p. 123), does not encode the observer/disturbance blocks
`Q, A_t, L_t, M_i, N_i`, and defers the reweighted-`ℓ¹` network-design
optimisation of Chapter 7. The LMI is therefore used exactly as in slice D2:
as an assumed hypothesis, never as a claim of solvability.
-/

@[expose] public section

open Matrix
open scoped BigOperators

variable {N : ℕ}

/-! ## Structure masks and the controllers that respect them

Definition 6.1 (printed p. 117) attaches to a block matrix `Y = [Y_ij]` its
*structure matrix* `S(Y) = [s_ij]`, with `s_ij = 0` when `Y_ij = 0` for `i ≠ j`
and `s_ij = 1` otherwise; the diagonal entries are always `1`. We encode it as a
Boolean matrix, the *sparsity mask*. Definition 6.3 (printed p. 117) writes
`S(Y₁) ⊆ S(Y₂)` when `s²_ij - s¹_ij ≥ 0`, i.e. when the support of `Y₁` is
contained in that of `Y₂`; `dsmcRespectsMask` is the corresponding support
condition on a controller gain, and the lemmas below record that the gains
respecting a fixed mask form a subspace. -/

/-- The Boolean **structure/sparsity mask** `S(Y)` of a structure matrix `Y`:
`dsmcSparsityMask Y i j = true` exactly when the `ij` link is present, i.e. when
`i = j` or `Y i j ≠ 0`. This is Definition 6.1 of A. Argha, S. W. Su, L. Li and
H. T. Nguyen, *Advances in Discrete-Time Sliding Mode Control: Theory and
Applications*, CRC Press 2018, printed p. 117, including the book's convention
that the diagonal entries of a structure matrix are `1`. -/
noncomputable def dsmcSparsityMask (Y : Matrix (Fin N) (Fin N) ℝ) :
    Matrix (Fin N) (Fin N) Bool :=
  fun i j ↦ if i = j then true else decide (Y i j ≠ 0)

/-- Every diagonal link belongs to the structure mask, as required by
Definition 6.1 of A. Argha, S. W. Su, L. Li and H. T. Nguyen, *Advances in
Discrete-Time Sliding Mode Control: Theory and Applications*, CRC Press 2018,
printed p. 117 ("the diagonal entries in the structure matrix will be assumed to
be 1"). -/
@[simp] theorem dsmcSparsityMask_self (Y : Matrix (Fin N) (Fin N) ℝ) (i : Fin N) :
    dsmcSparsityMask Y i i = true := by
  simp only [dsmcSparsityMask, ↓reduceIte]

/-- An off-diagonal link is absent from the structure mask exactly when the
corresponding entry of the structure matrix vanishes. This is the componentwise
content of Definition 6.1 of A. Argha, S. W. Su, L. Li and H. T. Nguyen,
*Advances in Discrete-Time Sliding Mode Control: Theory and Applications*, CRC
Press 2018, printed p. 117. -/
theorem dsmcSparsityMask_eq_false_iff (Y : Matrix (Fin N) (Fin N) ℝ) {i j : Fin N} :
    dsmcSparsityMask Y i j = false ↔ i ≠ j ∧ Y i j = 0 := by
  unfold dsmcSparsityMask
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte, Bool.true_eq_false, false_iff]
    rintro ⟨h, -⟩
    exact h rfl
  · have hcond : (if i = j then true else decide (Y i j ≠ 0)) = decide (Y i j ≠ 0) := by
      simp only [hij, ↓reduceIte]
    rw [hcond, decide_eq_false_iff_not, ne_eq, not_not]
    exact ⟨fun h => ⟨hij, h⟩, fun h => h.2⟩

/-- A controller gain `K` **respects the mask** `Γ`, written `S(K) ⊆ Γ` in
A. Argha, S. W. Su, L. Li and H. T. Nguyen, *Advances in Discrete-Time Sliding
Mode Control: Theory and Applications*, CRC Press 2018, Definition 6.3,
printed p. 117, when every absent link of `Γ` carries a zero entry of `K`: the
gains respecting `Γ` are exactly the controllers allowed by the given control
network topology (eq. (6.9) and Remark 6.2, printed pp. 119–121). -/
def dsmcRespectsMask (mask : Matrix (Fin N) (Fin N) Bool)
    (K : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  ∀ i j, mask i j = false → K i j = 0

/-- The masked gains form a subspace (Definition 6.3, printed p. 117): the zero
gain respects every mask. -/
theorem dsmcRespectsMask_zero (mask : Matrix (Fin N) (Fin N) Bool) :
    dsmcRespectsMask mask (0 : Matrix (Fin N) (Fin N) ℝ) := by
  intro i j _
  rfl

/-- The masked gains form a subspace (Definition 6.3, printed p. 117): they are
closed under addition. -/
theorem dsmcRespectsMask_add {mask : Matrix (Fin N) (Fin N) Bool}
    {K L : Matrix (Fin N) (Fin N) ℝ} (hK : dsmcRespectsMask mask K)
    (hL : dsmcRespectsMask mask L) : dsmcRespectsMask mask (K + L) := by
  intro i j hj
  simp only [Matrix.add_apply, hK i j hj, hL i j hj, add_zero]

/-- The masked gains form a subspace (Definition 6.3, printed p. 117): they are
closed under scalar multiplication. -/
theorem dsmcRespectsMask_smul {mask : Matrix (Fin N) (Fin N) Bool}
    {K : Matrix (Fin N) (Fin N) ℝ} (c : ℝ) (hK : dsmcRespectsMask mask K) :
    dsmcRespectsMask mask (c • K) := by
  intro i j hj
  simp only [Matrix.smul_apply, hK i j hj, smul_eq_mul, mul_zero]

/-- The masked gains form a subspace (Definition 6.3, printed p. 117): they are
closed under negation. -/
theorem dsmcRespectsMask_neg {mask : Matrix (Fin N) (Fin N) Bool}
    {K : Matrix (Fin N) (Fin N) ℝ} (hK : dsmcRespectsMask mask K) :
    dsmcRespectsMask mask (-K) := by
  intro i j hj
  simp only [Matrix.neg_apply, hK i j hj, neg_zero]

/-- The masked gains form a subspace (Definition 6.3, printed p. 117): they are
closed under subtraction. -/
theorem dsmcRespectsMask_sub {mask : Matrix (Fin N) (Fin N) Bool}
    {K L : Matrix (Fin N) (Fin N) ℝ} (hK : dsmcRespectsMask mask K)
    (hL : dsmcRespectsMask mask L) : dsmcRespectsMask mask (K - L) := by
  intro i j hj
  simp only [Matrix.sub_apply, hK i j hj, hL i j hj, sub_zero]

/-- The **masked gain** `dsmcMaskedGain Γ K` is the sparse controller obtained
from the desired gain `K` by zeroing every entry outside the control network
`Γ`. This is the formalisation, for the linear part of the controller (6.15)
(printed p. 121), of the constraint that the local controllers may use only the
links present in `Γ` (eq. (6.8)–(6.9), printed p. 119; Remark 6.2, printed
p. 121). -/
def dsmcMaskedGain (mask : Matrix (Fin N) (Fin N) Bool)
    (K : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j ↦ if mask i j then K i j else 0

/-- Projecting a gain onto a mask produces a gain that respects the mask: it is
the sparse controller realisable over the network (eq. (6.9), printed p. 119). -/
theorem dsmcRespectsMask_maskedGain (mask : Matrix (Fin N) (Fin N) Bool)
    (K : Matrix (Fin N) (Fin N) ℝ) : dsmcRespectsMask mask (dsmcMaskedGain mask K) := by
  intro i j hj
  unfold dsmcMaskedGain
  rw [hj]
  simp only [Bool.false_eq_true, ↓reduceIte]

/-- If a gain already respects the mask then masking it changes nothing
(Definition 6.3, printed p. 117). -/
theorem dsmcMaskedGain_eq_self_of_respects {mask : Matrix (Fin N) (Fin N) Bool}
    {K : Matrix (Fin N) (Fin N) ℝ} (hK : dsmcRespectsMask mask K) :
    dsmcMaskedGain mask K = K := by
  ext i j
  unfold dsmcMaskedGain
  cases h : mask i j
  · simp only [Bool.false_eq_true, ↓reduceIte, hK i j h]
  · simp only [↓reduceIte]

/-! ## The weighted `ℓ¹` penalty and its algebra

The weighted `ℓ¹` penalty of a gain `K` with weights `w` is
`dsmcL1Penalty w K = ∑_{i,j} w_ij |K_ij|`. It is the objective relaxed by the
reweighted-`ℓ¹` network-design heuristic of Chapter 7 (the optimisation itself is
deferred by this slice). The lemmas below are its basic algebra: nonnegativity,
vanishing on the zero gain, absolute homogeneity, subadditivity (triangle
inequality) and monotonicity in the gain. -/

/-- The weighted **`ℓ¹` penalty** `∑_{i,j} w_ij |K_ij|` of a controller gain `K`
with nonnegative weights `w`. This is the convex surrogate for the number of
active control links minimised by the sparse control-network design of
A. Argha, S. W. Su, L. Li and H. T. Nguyen, *Advances in Discrete-Time Sliding
Mode Control: Theory and Applications*, CRC Press 2018, Chapter 6 (sparsity
objective, printed pp. 115–116), continued as the reweighted-`ℓ¹` iteration of
Chapter 7. -/
def dsmcL1Penalty (w K : Matrix (Fin N) (Fin N) ℝ) : ℝ :=
  ∑ i, ∑ j, w i j * |K i j|

/-- The weighted `ℓ¹` penalty is nonnegative when all weights are nonnegative
(Chapter 6 sparsity objective, printed pp. 115–116). -/
theorem dsmcL1Penalty_nonneg {w K : Matrix (Fin N) (Fin N) ℝ} (hw : ∀ i j, 0 ≤ w i j) :
    0 ≤ dsmcL1Penalty w K := by
  unfold dsmcL1Penalty
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    mul_nonneg (hw i j) (abs_nonneg _)

/-- The weighted `ℓ¹` penalty of the zero gain vanishes (Chapter 6 sparsity
objective, printed pp. 115–116). -/
@[simp] theorem dsmcL1Penalty_zero (w : Matrix (Fin N) (Fin N) ℝ) :
    dsmcL1Penalty w (0 : Matrix (Fin N) (Fin N) ℝ) = 0 := by
  simp only [dsmcL1Penalty, Matrix.zero_apply, abs_zero, mul_zero, Finset.sum_const_zero]

/-- The weighted `ℓ¹` penalty is absolutely homogeneous (Chapter 6 sparsity
objective, printed pp. 115–116). -/
theorem dsmcL1Penalty_smul (w K : Matrix (Fin N) (Fin N) ℝ) (c : ℝ) :
    dsmcL1Penalty w (c • K) = |c| * dsmcL1Penalty w K := by
  unfold dsmcL1Penalty
  simp only [Matrix.smul_apply, smul_eq_mul, abs_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The weighted `ℓ¹` penalty is subadditive (triangle inequality) (Chapter 6
sparsity objective, printed pp. 115–116). -/
theorem dsmcL1Penalty_add_le {w K L : Matrix (Fin N) (Fin N) ℝ}
    (hw : ∀ i j, 0 ≤ w i j) :
    dsmcL1Penalty w (K + L) ≤ dsmcL1Penalty w K + dsmcL1Penalty w L := by
  unfold dsmcL1Penalty
  simp only [Matrix.add_apply]
  calc ∑ i, ∑ j, w i j * |K i j + L i j|
      ≤ ∑ i, ∑ j, (w i j * |K i j| + w i j * |L i j|) := by
        apply Finset.sum_le_sum; intro i _
        apply Finset.sum_le_sum; intro j _
        calc w i j * |K i j + L i j| ≤ w i j * (|K i j| + |L i j|) :=
              mul_le_mul_of_nonneg_left (abs_add_le _ _) (hw i j)
          _ = w i j * |K i j| + w i j * |L i j| := by ring
    _ = ∑ i, ((∑ j, w i j * |K i j|) + ∑ j, w i j * |L i j|) := by
        apply Finset.sum_congr rfl; intro i _; rw [Finset.sum_add_distrib]
    _ = (∑ i, ∑ j, w i j * |K i j|) + ∑ i, ∑ j, w i j * |L i j| := by
        rw [Finset.sum_add_distrib]

/-- The weighted `ℓ¹` penalty is monotone in the gain with respect to the
entrywise absolute-value order (Chapter 6 sparsity objective, printed
pp. 115–116). -/
theorem dsmcL1Penalty_mono {w K L : Matrix (Fin N) (Fin N) ℝ} (hw : ∀ i j, 0 ≤ w i j)
    (h : ∀ i j, |K i j| ≤ |L i j|) : dsmcL1Penalty w K ≤ dsmcL1Penalty w L := by
  unfold dsmcL1Penalty
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j _
  exact mul_le_mul_of_nonneg_left (h i j) (hw i j)

/-- Masking a gain leaves only the weighted absolute values of the links present
in the mask: `dsmcL1Penalty` of the masked gain is the sum of `w_ij |K_ij|` over
the links of the control network. This connects the sparsity mask to the
weighted `ℓ¹` objective of A. Argha, S. W. Su, L. Li and H. T. Nguyen, *Advances
in Discrete-Time Sliding Mode Control: Theory and Applications*, CRC Press 2018,
Chapter 6 (printed pp. 115–116). -/
theorem dsmcL1Penalty_maskedGain (w : Matrix (Fin N) (Fin N) ℝ)
    (mask : Matrix (Fin N) (Fin N) Bool) (K : Matrix (Fin N) (Fin N) ℝ) :
    dsmcL1Penalty w (dsmcMaskedGain mask K) =
      ∑ i, ∑ j, if mask i j then w i j * |K i j| else 0 := by
  unfold dsmcL1Penalty dsmcMaskedGain
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  cases h : mask i j <;> simp only [Bool.false_eq_true, ↓reduceIte, abs_zero, mul_zero]

/-- Masking a gain cannot increase its weighted `ℓ¹` penalty (Chapter 6 sparsity
objective, printed pp. 115–116), because every masked entry is either the
original entry or zero. -/
theorem dsmcL1Penalty_maskedGain_le (w : Matrix (Fin N) (Fin N) ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (mask : Matrix (Fin N) (Fin N) Bool)
    (K : Matrix (Fin N) (Fin N) ℝ) :
    dsmcL1Penalty w (dsmcMaskedGain mask K) ≤ dsmcL1Penalty w K := by
  unfold dsmcL1Penalty
  apply Finset.sum_le_sum; intro i _
  apply Finset.sum_le_sum; intro j _
  refine mul_le_mul_of_nonneg_left ?_ (hw i j)
  unfold dsmcMaskedGain
  cases h : mask i j
  · simp only [Bool.false_eq_true, ↓reduceIte, abs_zero]
    exact abs_nonneg _
  · simp only [↓reduceIte]
    exact le_refl _

/-! ## The structured LMI and the quadratic decrease

The surface LMI of slice D2 (`dsmcSurfaceLMI`, `DynamicalSystems.Control.SlidingMode.LMI`)
reduced the design condition to the block inequality `[[P, AᵀP], [PA, P]] ≻ 0`,
equivalent to `P ≻ 0 ∧ (P - Aᵀ P A) ≻ 0`. The *structured* version below simply
evaluates that LMI at the masked closed loop `A - B (dsmcMaskedGain Γ K)`, i.e.
at the controller actually realisable over the control network `Γ`. The main
theorem shows that the structure constraint does not destroy the discrete
Lyapunov decrease: the network quadratic form `xᵀ P x` still decays strictly
along the sparse closed loop. -/

/-- The **structured (decentralized) surface LMI**: the D2 surface LMI
`dsmcSurfaceLMI` of `DynamicalSystems.Control.SlidingMode.LMI` evaluated at the
closed loop `A - B (dsmcMaskedGain Γ K)` obtained from the sparse controller
implemented over the control network `Γ`. It is the algebraic core of the
distributed/decentralized design condition of A. Argha, S. W. Su, L. Li and
H. T. Nguyen, *Advances in Discrete-Time Sliding Mode Control: Theory and
Applications*, CRC Press 2018, Theorem 6.1 and LMI (6.20), printed pp. 122–123,
after the Schur-complement reduction described in the proof (printed pp. 124–125):
the controller is restricted to the network `Γ`, and `P ≻ 0` is the common
network Lyapunov matrix. As in slice D2, only the implication from the LMI is
formalised; feasibility of the block LMI (6.20) is not claimed. -/
def dsmcStructuredLMI (Γ : Matrix (Fin N) (Fin N) Bool)
    (A B K P : Matrix (Fin N) (Fin N) ℝ) : Prop :=
  dsmcSurfaceLMI (A - B * dsmcMaskedGain Γ K) P

/-- **Sparse structured stability**: a controller whose *masked* closed loop
`A - B (dsmcMaskedGain Γ K)` satisfies the structured surface LMI still yields
the strict quadratic-form decrease of the network Lyapunov function, and the
implemented gain respects the control network `Γ`.

This is the stability implication of A. Argha, S. W. Su, L. Li and H. T. Nguyen,
*Advances in Discrete-Time Sliding Mode Control: Theory and Applications*, CRC
Press 2018, Theorem 6.1, LMI (6.20), printed pp. 122–123: the LMI is the
structured (decentralized) version of the D2 condition `Ω₁₁ < -ηI`
(eq. (2.28), printed p. 36), and its Schur complement is the discrete Lyapunov
inequality `P - A_clᵀ P A_cl ≻ 0` for the sparse closed loop `A_cl`. The
conclusion is the decrease `xᵀ P x` along `A_cl`, i.e. the network-level
decay that certifies every subsystem; it is obtained by reusing the D2 reduction
`dsmc_sliding_surface_lmi` (and hence `quadForm_mulVec_lt` of
`DynamicalSystems.DiscreteTime.MatrixLyapunov`) rather than reproving it. -/
theorem dsmc_sparse_structured_stability {Γ : Matrix (Fin N) (Fin N) Bool}
    {A B K P : Matrix (Fin N) (Fin N) ℝ} (hLMI : dsmcStructuredLMI Γ A B K P) :
    dsmcRespectsMask Γ (dsmcMaskedGain Γ K) ∧ P.PosDef ∧
      (P - (A - B * dsmcMaskedGain Γ K)ᵀ * P * (A - B * dsmcMaskedGain Γ K)).PosDef ∧
      ∀ x : Fin N → ℝ, x ≠ 0 →
        quadForm P ((A - B * dsmcMaskedGain Γ K) *ᵥ x) < quadForm P x := by
  have h := dsmc_sliding_surface_lmi hLMI
  exact ⟨dsmcRespectsMask_maskedGain Γ K, h.1, h.2.1, h.2.2⟩

/-- **Per-subsystem decrease of the structured LMI.** In the fully decentralized
interpretation of the control network, each subsystem `i` has its own local
Lyapunov matrix `P_i` and its own local closed loop `A_i - B_i K_i`; if every
local discrete Lyapunov inequality `P_i - (A_i - B_i K_i)ᵀ P_i (A_i - B_i K_i) ≻ 0`
holds — the decoupled (`Γ = I`) specialisation of the structured LMI of
A. Argha, S. W. Su, L. Li and H. T. Nguyen, *Advances in Discrete-Time Sliding
Mode Control: Theory and Applications*, CRC Press 2018, Theorem 6.1, printed
pp. 122–123 — then the local quadratic form `x_iᵀ P_i x_i` strictly decreases
along each subsystem. This is the blockwise reading of
`dsmc_sparse_structured_stability`; it is a direct specialisation of the library
decrease `quadForm_mulVec_lt` and introduces no new quadratic-form machinery. -/
theorem dsmc_sparse_structured_stability_subsystem {h n : ℕ}
    {A B K P : Fin h → Matrix (Fin n) (Fin n) ℝ}
    (hLMI : ∀ i, (P i - (A i - B i * K i)ᵀ * P i * (A i - B i * K i)).PosDef) :
    ∀ i (x : Fin n → ℝ), x ≠ 0 →
      quadForm (P i) ((A i - B i * K i) *ᵥ x) < quadForm (P i) x := by
  intro i x hx
  exact quadForm_mulVec_lt (hLMI i) hx
