/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.TimeOptimal

/-!
# Exact minimum-fuel Hamiltonian minimizers

The running cost is a positive weighted L¹ fuel cost. Over a symmetric interval,
the scalar Hamiltonian `α * |u| + c * u` has five regimes. Strict switching
inequalities give the unique values `M`, `0`, and `-M`; at `c = -α` every value
in `[0, M]` minimizes, and at `c = α` every value in `[-M, 0]` minimizes.

The finite-dimensional results prove both directions of the coordinatewise
classification over a box and connect it to the existing `HamiltonianMinimizing`
predicate for control-affine dynamics. These are applications of a Hamiltonian
minimum condition, not a claim to have derived PMP from trajectory optimality.
-/

@[expose] public section

open scoped BigOperators

namespace MinimumFuel

/-- Scalar fuel cost plus the control-dependent linear Hamiltonian term. -/
def scalarHamiltonian (α c u : ℝ) : ℝ := α * |u| + c * u

/-- A feasible scalar minimizer, including membership in the control interval. -/
def IsScalarMinimizer (α M c u : ℝ) : Prop :=
  u ∈ Set.Icc (-M) M ∧
    ∀ v ∈ Set.Icc (-M) M, scalarHamiltonian α c u ≤ scalarHamiltonian α c v

/-- Exact five-regime control law, retaining the intervals of nonunique minimizers
at the switching thresholds. -/
def SwitchingLaw (α M c u : ℝ) : Prop :=
  (c < -α ∧ u = M) ∨
    (c = -α ∧ u ∈ Set.Icc 0 M) ∨
    (-α < c ∧ c < α ∧ u = 0) ∨
    (c = α ∧ u ∈ Set.Icc (-M) 0) ∨
    (α < c ∧ u = -M)

private theorem positive_ray_bound {α c u : ℝ} (hα : 0 ≤ α) :
    (α + c) * u ≤ scalarHamiltonian α c u := by
  have h := mul_le_mul_of_nonneg_left (le_abs_self u) hα
  unfold scalarHamiltonian
  nlinarith

private theorem negative_ray_bound {α c u : ℝ} (hα : 0 ≤ α) :
    (c - α) * u ≤ scalarHamiltonian α c u := by
  have h := mul_le_mul_of_nonneg_left (neg_le_abs u) hα
  unfold scalarHamiltonian
  nlinarith

/-- Below the negative threshold the unique scalar minimizer is `M`. -/
theorem scalar_minimizer_iff_eq_upper {α M c u : ℝ}
    (hα : 0 < α) (hM : 0 ≤ M) (hc : c < -α) :
    IsScalarMinimizer α M c u ↔ u = M := by
  have hslope : α + c < 0 := by linarith
  constructor
  · rintro ⟨hu, hmin⟩
    have hm := hmin M ⟨by linarith, le_rfl⟩
    have hl := positive_ray_bound (c := c) (u := u) hα.le
    have heq : scalarHamiltonian α c M = (α + c) * M := by
      rw [scalarHamiltonian, abs_of_nonneg hM]
      ring
    rw [heq] at hm
    have hreverse : M ≤ u := (mul_le_mul_left_of_neg hslope).mp (hl.trans hm)
    exact le_antisymm hu.2 hreverse
  · intro hu
    subst u
    refine ⟨⟨by linarith, le_rfl⟩, fun v hv ↦ ?_⟩
    calc
      scalarHamiltonian α c M = (α + c) * M := by
        rw [scalarHamiltonian, abs_of_nonneg hM]
        ring
      _ ≤ (α + c) * v := (mul_le_mul_left_of_neg hslope).mpr hv.2
      _ ≤ scalarHamiltonian α c v := positive_ray_bound hα.le

/-- Above the positive threshold the unique scalar minimizer is `-M`. -/
theorem scalar_minimizer_iff_eq_lower {α M c u : ℝ}
    (hα : 0 < α) (hM : 0 ≤ M) (hc : α < c) :
    IsScalarMinimizer α M c u ↔ u = -M := by
  have hslope : 0 < c - α := by linarith
  constructor
  · rintro ⟨hu, hmin⟩
    have hm := hmin (-M) ⟨le_rfl, by linarith⟩
    have hl := negative_ray_bound (c := c) (u := u) hα.le
    have heq : scalarHamiltonian α c (-M) = (c - α) * (-M) := by
      rw [scalarHamiltonian, abs_of_nonpos (neg_nonpos.mpr hM)]
      ring
    rw [heq] at hm
    have hreverse : u ≤ -M := (mul_le_mul_iff_right₀ hslope).mp (hl.trans hm)
    exact le_antisymm hreverse hu.1
  · rintro rfl
    refine ⟨⟨le_rfl, by linarith⟩, fun v hv ↦ ?_⟩
    calc
      scalarHamiltonian α c (-M) = (c - α) * (-M) := by
        rw [scalarHamiltonian, abs_of_nonpos (neg_nonpos.mpr hM)]
        ring
      _ ≤ (c - α) * v := (mul_le_mul_iff_right₀ hslope).mpr hv.1
      _ ≤ scalarHamiltonian α c v := negative_ray_bound hα.le

/-- Strictly between the thresholds the unique scalar minimizer is zero. -/
theorem scalar_minimizer_iff_eq_zero {α M c u : ℝ}
    (hM : 0 ≤ M) (hlo : -α < c) (hhi : c < α) :
    IsScalarMinimizer α M c u ↔ u = 0 := by
  constructor
  · rintro ⟨_, hmin⟩
    have hm := hmin 0 ⟨by linarith, hM⟩
    simp only [scalarHamiltonian, abs_zero, mul_zero, add_zero] at hm
    rcases le_total 0 u with hu | hu
    · rw [abs_of_nonneg hu] at hm
      have hslope : 0 < α + c := by linarith
      have hmul : (α + c) * u ≤ (α + c) * 0 := by nlinarith
      exact le_antisymm ((mul_le_mul_iff_right₀ hslope).mp hmul) hu
    · rw [abs_of_nonpos hu] at hm
      have hslope : c - α < 0 := by linarith
      have hmul : (c - α) * u ≤ (c - α) * 0 := by nlinarith
      exact le_antisymm hu ((mul_le_mul_left_of_neg hslope).mp hmul)
  · rintro rfl
    refine ⟨⟨by linarith, hM⟩, fun v _ ↦ ?_⟩
    simp only [scalarHamiltonian, abs_zero, mul_zero, add_zero]
    rcases le_total 0 v with hv | hv
    · rw [abs_of_nonneg hv]
      have h := mul_nonneg (show 0 ≤ α + c by linarith) hv
      nlinarith
    · rw [abs_of_nonpos hv]
      have h := mul_nonneg_of_nonpos_of_nonpos (show c - α ≤ 0 by linarith) hv
      nlinarith

/-- At the negative threshold the complete minimizing set is `[0, M]`. -/
theorem scalar_minimizer_neg_threshold_iff {α M u : ℝ}
    (hα : 0 < α) (hM : 0 ≤ M) :
    IsScalarMinimizer α M (-α) u ↔ u ∈ Set.Icc 0 M := by
  constructor
  · rintro ⟨hu, hmin⟩
    have hm := hmin 0 ⟨by linarith, hM⟩
    simp only [scalarHamiltonian, abs_zero, mul_zero, add_zero] at hm
    refine ⟨?_, hu.2⟩
    by_contra hn
    have hneg : u < 0 := lt_of_not_ge hn
    rw [abs_of_neg hneg] at hm
    have hprod := mul_neg_of_pos_of_neg hα hneg
    nlinarith
  · intro hu
    refine ⟨⟨by linarith [hu.1], hu.2⟩, fun v _ ↦ ?_⟩
    have hv := positive_ray_bound (c := -α) (u := v) hα.le
    simp only [scalarHamiltonian, abs_of_nonneg hu.1]
    unfold scalarHamiltonian at hv
    nlinarith

/-- At the positive threshold the complete minimizing set is `[-M, 0]`. -/
theorem scalar_minimizer_pos_threshold_iff {α M u : ℝ}
    (hα : 0 < α) (hM : 0 ≤ M) :
    IsScalarMinimizer α M α u ↔ u ∈ Set.Icc (-M) 0 := by
  constructor
  · rintro ⟨hu, hmin⟩
    have hm := hmin 0 ⟨by linarith, hM⟩
    simp only [scalarHamiltonian, abs_zero, mul_zero, add_zero] at hm
    refine ⟨hu.1, ?_⟩
    by_contra hn
    have hpos : 0 < u := lt_of_not_ge hn
    rw [abs_of_pos hpos] at hm
    have hprod := mul_pos hα hpos
    nlinarith
  · intro hu
    refine ⟨⟨hu.1, by linarith [hu.2]⟩, fun v _ ↦ ?_⟩
    have hv := negative_ray_bound (c := α) (u := v) hα.le
    simp only [scalarHamiltonian, abs_of_nonpos hu.2]
    unfold scalarHamiltonian at hv
    nlinarith

/-- Complete scalar fuel-minimizer classification, including both thresholds. -/
theorem scalar_minimizer_iff_switchingLaw {α M c u : ℝ}
    (hα : 0 < α) (hM : 0 ≤ M) :
    IsScalarMinimizer α M c u ↔ SwitchingLaw α M c u := by
  constructor
  · intro h
    rcases lt_trichotomy c (-α) with hc | hc | hc
    · exact Or.inl ⟨hc, (scalar_minimizer_iff_eq_upper hα hM hc).mp h⟩
    · subst c
      exact Or.inr (Or.inl ⟨rfl, (scalar_minimizer_neg_threshold_iff hα hM).mp h⟩)
    · rcases lt_trichotomy c α with hd | hd | hd
      · exact Or.inr (Or.inr (Or.inl
          ⟨hc, hd, (scalar_minimizer_iff_eq_zero hM hc hd).mp h⟩))
      · subst c
        exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨rfl, (scalar_minimizer_pos_threshold_iff hα hM).mp h⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr
          ⟨hd, (scalar_minimizer_iff_eq_lower hα hM hd).mp h⟩)))
  · rintro (⟨hc, hu⟩ | ⟨rfl, hu⟩ | ⟨hlo, hhi, hu⟩ | ⟨rfl, hu⟩ | ⟨hc, hu⟩)
    · exact (scalar_minimizer_iff_eq_upper hα hM hc).mpr hu
    · exact (scalar_minimizer_neg_threshold_iff hα hM).mpr hu
    · exact (scalar_minimizer_iff_eq_zero hM hlo hhi).mpr hu
    · exact (scalar_minimizer_pos_threshold_iff hα hM).mpr hu
    · exact (scalar_minimizer_iff_eq_lower hα hM hc).mpr hu

/-- A deterministic minimizing choice. At either threshold it chooses zero;
the full minimizing set is still given by `SwitchingLaw`. -/
noncomputable def scalarSelector (α M c : ℝ) : ℝ :=
  if c < -α then M else if α < c then -M else 0

/-- The explicit selector minimizes the scalar Hamiltonian for every switching
coefficient, including threshold and zero-width cases. -/
theorem scalarSelector_minimizes {α M c : ℝ} (hα : 0 < α) (hM : 0 ≤ M) :
    IsScalarMinimizer α M c (scalarSelector α M c) := by
  unfold scalarSelector
  split_ifs with hlo hhi
  · exact (scalar_minimizer_iff_eq_upper hα hM hlo).mpr rfl
  · exact (scalar_minimizer_iff_eq_lower hα hM hhi).mpr rfl
  · by_cases heq : c = -α
    · rw [heq]
      exact (scalar_minimizer_neg_threshold_iff hα hM).mpr ⟨le_rfl, hM⟩
    · by_cases heq' : c = α
      · rw [heq']
        exact (scalar_minimizer_pos_threshold_iff hα hM).mpr ⟨by linarith, le_rfl⟩
      · exact (scalar_minimizer_iff_eq_zero hM
          (lt_of_le_of_ne (le_of_not_gt hlo) (Ne.symm heq))
          (lt_of_le_of_ne (le_of_not_gt hhi) heq')).mpr rfl

section Box

variable {ι : Type*} [Fintype ι]

/-- A symmetric control box with potentially different bounds in each coordinate. -/
def box (M : ι → ℝ) : Set (EuclideanSpace ℝ ι) :=
  {u | ∀ i, u i ∈ Set.Icc (-(M i)) (M i)}

omit [Fintype ι] in
/-- The unit specialization is the existing time-optimal control box. -/
theorem box_one_eq_unitBox : box (fun _ : ι ↦ (1 : ℝ)) = unitBox ι := by
  ext u
  simp only [box, unitBox, Set.mem_ofPred_eq, Set.mem_Icc, abs_le]

/-- Positive weighted L¹ running cost; positivity is required by classification
theorems rather than built into the data. -/
def weightedL1 (α : ι → ℝ) (u : EuclideanSpace ℝ ι) : ℝ :=
  ∑ i, α i * |u i|

/-- The control-dependent part of a fuel Hamiltonian. -/
noncomputable def boxHamiltonian (α : ι → ℝ) (c u : EuclideanSpace ℝ ι) : ℝ :=
  weightedL1 α u + inner ℝ c u

theorem boxHamiltonian_eq_sum (α : ι → ℝ) (c u : EuclideanSpace ℝ ι) :
    boxHamiltonian α c u = ∑ i, scalarHamiltonian (α i) (c i) (u i) := by
  simp [boxHamiltonian, weightedL1, scalarHamiltonian, PiLp.inner_apply,
    Finset.sum_add_distrib, mul_comm]

/-- Feasible minimization of the fuel Hamiltonian over the entire control box. -/
def IsBoxMinimizer (α M : ι → ℝ) (c u : EuclideanSpace ℝ ι) : Prop :=
  u ∈ box M ∧ ∀ v ∈ box M, boxHamiltonian α c u ≤ boxHamiltonian α c v

/-- A box Hamiltonian minimum is equivalent to independent scalar minima.
The forward direction replaces one coordinate by an arbitrary feasible scalar;
the reverse direction sums the scalar inequalities. -/
theorem box_minimizer_iff_coordinate_minimizers
    (α M : ι → ℝ) (c u : EuclideanSpace ℝ ι) :
    IsBoxMinimizer α M c u ↔ ∀ i, IsScalarMinimizer (α i) (M i) (c i) (u i) := by
  classical
  constructor
  · rintro ⟨hu, hmin⟩ i
    refine ⟨hu i, ?_⟩
    intro s hs
    let w : EuclideanSpace ℝ ι := u + (s - u i) • EuclideanSpace.single i (1 : ℝ)
    have hw : w ∈ box M := by
      intro j
      by_cases hji : j = i
      · subst j
        simpa [w] using hs
      · simpa [w, hji] using hu j
    have hvalue : boxHamiltonian α c w = boxHamiltonian α c u +
        (scalarHamiltonian (α i) (c i) s - scalarHamiltonian (α i) (c i) (u i)) := by
      rw [boxHamiltonian_eq_sum, boxHamiltonian_eq_sum]
      calc
        (∑ j, scalarHamiltonian (α j) (c j) (w j)) =
            ∑ j, (scalarHamiltonian (α j) (c j) (u j) +
              if j = i then scalarHamiltonian (α i) (c i) s -
                scalarHamiltonian (α i) (c i) (u i) else 0) := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hji : j = i
          · subst j
            simp [w]
          · simp [w, hji]
        _ = _ := by rw [Finset.sum_add_distrib]; simp
    have hle := hmin w hw
    rw [hvalue] at hle
    linarith
  · intro h
    refine ⟨fun i ↦ (h i).1, fun v hv ↦ ?_⟩
    rw [boxHamiltonian_eq_sum, boxHamiltonian_eq_sum]
    exact Finset.sum_le_sum fun i _ ↦ (h i).2 (v i) (hv i)

/-- Complete necessary and sufficient box classification, with no uniqueness
assertion at either switching threshold. Zero-width coordinates are allowed. -/
theorem box_minimizer_iff_switchingLaw (α M : ι → ℝ)
    (c u : EuclideanSpace ℝ ι) (hα : ∀ i, 0 < α i) (hM : ∀ i, 0 ≤ M i) :
    IsBoxMinimizer α M c u ↔ ∀ i, SwitchingLaw (α i) (M i) (c i) (u i) := by
  rw [box_minimizer_iff_coordinate_minimizers]
  exact forall_congr' fun i ↦ scalar_minimizer_iff_switchingLaw (hα i) (hM i)

/-- Componentwise explicit fuel-minimizing choice. -/
noncomputable def boxSelector (α M : ι → ℝ) (c : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i ↦ scalarSelector (α i) (M i) (c i))

/-- An explicit feasible box minimizer exists for every switching covector. -/
theorem boxSelector_minimizes (α M : ι → ℝ) (c : EuclideanSpace ℝ ι)
    (hα : ∀ i, 0 < α i) (hM : ∀ i, 0 ≤ M i) :
    IsBoxMinimizer α M c (boxSelector α M c) := by
  rw [box_minimizer_iff_coordinate_minimizers]
  intro i
  exact scalarSelector_minimizes (hα i) (hM i)

end Box

section ControlAffine

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The fuel Hamiltonian splits into a control-independent term and the box
Hamiltonian, with switching covector `B(t,x)ᵀ p`. No time/state differentiability
is needed for this algebraic identity. -/
theorem controlAffineHamiltonian_eq
    (a : ℝ → E → E) (B : ℝ → E → EuclideanSpace ℝ ι →L[ℝ] E)
    (ℓ : ℝ → E → ℝ) (α : ι → ℝ) (t : ℝ) (x : E)
    (u : EuclideanSpace ℝ ι) (p : E) :
    hamiltonianOf (fun t x u ↦ ℓ t x + weightedL1 α u)
      (fun t x u ↦ a t x + B t x u) t x u p =
      ℓ t x + inner ℝ p (a t x) + boxHamiltonian α ((B t x).adjoint p) u := by
  simp only [hamiltonianOf_apply, inner_add_right, boxHamiltonian,
    ContinuousLinearMap.adjoint_inner_left]
  ring

/-- A fuel Hamiltonian minimum is precisely the box objective minimum at each
time, after the terms independent of the control are cancelled. -/
theorem hamiltonianMinimizing_iff_box_minimum
    (a : ℝ → E → E) (B : ℝ → E → EuclideanSpace ℝ ι →L[ℝ] E)
    (ℓ : ℝ → E → ℝ) (α M : ι → ℝ)
    (T : ℝ) (x : ℝ → E) (u : ℝ → EuclideanSpace ℝ ι) (p : ℝ → E)
    (hu : ∀ t ∈ Set.Icc 0 T, u t ∈ box M) :
    HamiltonianMinimizing (fun t x u ↦ ℓ t x + weightedL1 α u)
      (fun t x u ↦ a t x + B t x u) (box M) T x u p ↔
      ∀ t ∈ Set.Icc 0 T, IsBoxMinimizer α M ((B t (x t)).adjoint (p t)) (u t) := by
  constructor
  · intro h t ht
    refine ⟨hu t ht, fun v hv ↦ ?_⟩
    have hle := h t ht v hv
    rw [controlAffineHamiltonian_eq, controlAffineHamiltonian_eq] at hle
    linarith
  · intro h t ht v hv
    have hle := (h t ht).2 v hv
    rw [controlAffineHamiltonian_eq, controlAffineHamiltonian_eq]
    linarith

/-- Exact necessary and sufficient fuel switching law for a feasible control
under the existing pointwise Hamiltonian minimum predicate. In particular, no
threshold interval is replaced by an unjustified unique control selection. -/
theorem hamiltonianMinimizing_iff_switchingLaw
    (a : ℝ → E → E) (B : ℝ → E → EuclideanSpace ℝ ι →L[ℝ] E)
    (ℓ : ℝ → E → ℝ) (α M : ι → ℝ)
    (T : ℝ) (x : ℝ → E) (u : ℝ → EuclideanSpace ℝ ι) (p : ℝ → E)
    (hα : ∀ i, 0 < α i) (hM : ∀ i, 0 ≤ M i)
    (hu : ∀ t ∈ Set.Icc 0 T, u t ∈ box M) :
    HamiltonianMinimizing (fun t x u ↦ ℓ t x + weightedL1 α u)
      (fun t x u ↦ a t x + B t x u) (box M) T x u p ↔
      ∀ t ∈ Set.Icc 0 T, ∀ i,
        SwitchingLaw (α i) (M i) (((B t (x t)).adjoint (p t)) i) (u t i) := by
  rw [hamiltonianMinimizing_iff_box_minimum a B ℓ α M T x u p hu]
  exact forall_congr' fun t ↦ forall_congr' fun _ ↦
    box_minimizer_iff_switchingLaw α M _ _ hα hM

end ControlAffine

end MinimumFuel
