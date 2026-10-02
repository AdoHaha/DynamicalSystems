/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import DynamicalSystems.Control.Calculus
public import DynamicalSystems.Control.SlidingMode.Basic

/-! # Continuous sliding sectors and second-order invariance

This file formalizes the continuous-time sliding sector theory of Yaodong Pan
and Katsuhisa Furuta, *Second-Order Sliding Sector for Variable Structure Control*,
Chapter 5 in G. Bartolini, L. Fridman, A. Pisano and E. Usai (eds.), *Modern Sliding
Mode Control Theory: New Perspectives and Applications*, LNCIS 375, Springer 2008
(printed pp. 97–118, PDF pp. 113–134).

Sliding sectors replace discontinuous sliding surfaces with a boundary-layer-free
state-space sector inside which the Lyapunov function (the `P`-norm) decreases and
control action can be relaxed ("lazy control"). The sector is the quadratic region
`{x | (c ⬝ᵥ x)² ≤ x ⬝ᵥ (Δ *ᵥ x)}` around the sliding hyperplane `c ⬝ᵥ x = 0`, and
the convergence condition is *sector domination*: the closed-loop Lyapunov matrix
`P * A + Aᵀ * P + R` is bounded by the sector gap `c cᵀ - Δ`, so that the deficiency
is only allowed where the state lies inside the sector (Pan & Furuta, Chapter 5,
Definition 1 & Theorem 1, printed pp. 100 and 104–105).

## Main definitions

* `slidingSector c Δ`: the `PR`-sliding sector `{x | (c ⬝ᵥ x)² ≤ x ⬝ᵥ (Δ *ᵥ x)}`
  (Chapter 5, Definition 1, printed p. 100).
* `secondOrderSlidingSector c Δ`: the second-order sector `S_2nd`, whose geometric
  extent coincides with `slidingSector c Δ` (Chapter 5, Definition 2, printed p. 100).
* `sectorDefect c Δ x`: the boundary defect `(c ⬝ᵥ x)² - x ⬝ᵥ (Δ *ᵥ x)`.
* `innerSlidingSector c Ξ`: the inner sector `{x | (c ⬝ᵥ x)² ≤ x ⬝ᵥ (Ξ *ᵥ x)}`
  (Chapter 5, Section 3.3, Eq. 39, printed p. 106).
* `outerSlidingSector c Ξ Δ`: the outer sector
  `{x | x ⬝ᵥ (Ξ *ᵥ x) < (c ⬝ᵥ x)² ∧ (c ⬝ᵥ x)² ≤ x ⬝ᵥ (Δ *ᵥ x)}`
  (Chapter 5, Section 3.3, Eq. 38, printed p. 106).
* `sectorDefectLieDeriv c Δ F x`: the Lie derivative of the defect along a field `F`.

## Main statements

* `mem_slidingSector_iff_defect_nonpos`: sector membership is non-positivity of the
  defect.
* `zero_mem_slidingSector`, `slidingManifold_subset_slidingSector`: the origin and
  the ideal sliding surface `{c ⬝ᵥ x = 0}` lie in every sector with PSD `Δ`.
* `hasDerivAt_quadratic_form`, `quadratic_form_linear_symm`,
  `hasDerivAt_quadratic_form_linear_system`: time derivative of the symmetric
  quadratic form along `x' = A *ᵥ x`.
* `quadratic_form_decrease_in_sector`: under sector domination, the `P`-norm decays
  at rate at least `R` for every state inside the sliding sector.
* `hasDerivAt_p_norm_decrease_in_sector`: the trajectory-level counterpart.
* `inner_subset_slidingSector`, `inner_union_outer_eq_slidingSector`,
  `inner_inter_outer_eq_empty`: the inner/outer partition of the second-order sector.
* `sectorDefect_lieDeriv_nonpos`: algebraic infinitesimal tangency — a nonpositive
  defect-derivative inequality gives a nonpositive Lie derivative.
* `slidingSector_invariant_of_deriv_nonpos`: path-level forward invariance of the
  sector via `monotoneOn_of_deriv_nonneg`.

## References

* Y. Pan, K. Furuta, *Second-Order Sliding Sector for Variable Structure Control*,
  Chapter 5 of the LNCIS 375 volume, printed pp. 97–118.
-/

open scoped Matrix

@[expose] public section

variable {ι : Type*} [Fintype ι]

/-! ### Definitions of PR-sliding sectors -/

/-- The continuous-time `PR`-sliding sector:
`S = {x | (c ⬝ᵥ x)² ≤ x ⬝ᵥ (Δ *ᵥ x)}`
(Pan & Furuta, Chapter 5, Definition 1, printed p. 100, Eq. 6). -/
def slidingSector (c : ι → ℝ) (Δ : Matrix ι ι ℝ) : Set (ι → ℝ) :=
  {x | (c ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ (Δ *ᵥ x)}

/-- The second-order `PR`-sliding sector `S_2nd` (Pan & Furuta, Definition 2,
printed p. 100). Its geometric extent coincides with `slidingSector c Δ`. -/
def secondOrderSlidingSector (c : ι → ℝ) (Δ : Matrix ι ι ℝ) : Set (ι → ℝ) :=
  slidingSector c Δ

/-- The internal sliding sector
`S_i = {x | (c ⬝ᵥ x)² ≤ x ⬝ᵥ (Ξ *ᵥ x)}`
where `0 ≺ Ξ ≺ Δ` (Pan & Furuta, Chapter 5, Section 3.3, Eq. 39, printed p. 106). -/
def innerSlidingSector (c : ι → ℝ) (Ξ : Matrix ι ι ℝ) : Set (ι → ℝ) :=
  {x | (c ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ (Ξ *ᵥ x)}

/-- The outer sliding sector
`S_o = {x | x ⬝ᵥ (Ξ *ᵥ x) < (c ⬝ᵥ x)² ∧ (c ⬝ᵥ x)² ≤ x ⬝ᵥ (Δ *ᵥ x)}`
(Pan & Furuta, Chapter 5, Section 3.3, Eq. 38, printed p. 106). -/
def outerSlidingSector (c : ι → ℝ) (Ξ Δ : Matrix ι ι ℝ) : Set (ι → ℝ) :=
  {x | x ⬝ᵥ (Ξ *ᵥ x) < (c ⬝ᵥ x) ^ 2 ∧ (c ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ (Δ *ᵥ x)}

/-- The sliding sector boundary defect `V(x) = (c ⬝ᵥ x)² - x ⬝ᵥ (Δ *ᵥ x)`.
The sector is its sublevel set `{x | sectorDefect c Δ x ≤ 0}`. -/
def sectorDefect (c : ι → ℝ) (Δ : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  (c ⬝ᵥ x) ^ 2 - x ⬝ᵥ (Δ *ᵥ x)

/-- The Lie derivative of the sector defect along a vector field `F`:
`L_F V(x) = 2 (c ⬝ᵥ x) (c ⬝ᵥ F x) - 2 (x ⬝ᵥ (Δ *ᵥ F x))` (for symmetric `Δ`). -/
def sectorDefectLieDeriv (c : ι → ℝ) (Δ : Matrix ι ι ℝ) (F : (ι → ℝ) → (ι → ℝ))
    (x : ι → ℝ) : ℝ :=
  2 * (c ⬝ᵥ x) * (c ⬝ᵥ F x) - 2 * (x ⬝ᵥ (Δ *ᵥ F x))

/-! ### Basic geometric and structural properties -/

/-- Membership in the sliding sector unfolds to
`(c ⬝ᵥ x)² ≤ x ⬝ᵥ (Δ *ᵥ x)` (a `simp` lemma). -/
@[simp] theorem mem_slidingSector {c : ι → ℝ} {Δ : Matrix ι ι ℝ} {x : ι → ℝ} :
    x ∈ slidingSector c Δ ↔ (c ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ (Δ *ᵥ x) := Iff.rfl

/-- Membership in the sliding sector is non-positivity of the boundary defect. -/
theorem mem_slidingSector_iff_defect_nonpos {c : ι → ℝ} {Δ : Matrix ι ι ℝ}
    {x : ι → ℝ} :
    x ∈ slidingSector c Δ ↔ sectorDefect c Δ x ≤ 0 := by
  simp only [slidingSector, sectorDefect, Set.mem_ofPred_eq, sub_nonpos]

/-- The origin `0` is always contained in the sliding sector whenever `Δ` is
positive semidefinite. -/
theorem zero_mem_slidingSector (c : ι → ℝ) {Δ : Matrix ι ι ℝ} (hΔ : Δ.PosSemidef) :
    0 ∈ slidingSector c Δ := by
  have h := hΔ.dotProduct_mulVec_nonneg (0 : ι → ℝ)
  simpa only [slidingSector, Set.mem_ofPred_eq, star_trivial, dotProduct_zero,
    Matrix.mulVec_zero, sq, mul_zero] using h

/-- Connection to S3: the ideal sliding surface `{x | c ⬝ᵥ x = 0}` is contained in
every sliding sector with positive semidefinite `Δ`. -/
theorem slidingManifold_subset_slidingSector (c : ι → ℝ) {Δ : Matrix ι ι ℝ}
    (hΔ : Δ.PosSemidef) :
    slidingManifold (fun x ↦ c ⬝ᵥ x) ⊆ slidingSector c Δ := by
  intro x hx
  simp only [slidingManifold, Set.mem_ofPred_eq] at hx
  simp only [slidingSector, Set.mem_ofPred_eq, hx, sq, mul_zero]
  have hpos := hΔ.dotProduct_mulVec_nonneg x
  simpa only [star_trivial] using hpos

/-- When `Ξ ⪯ Δ`, the inner sector is contained in the sliding sector. -/
theorem inner_subset_slidingSector {c : ι → ℝ} {Ξ Δ : Matrix ι ι ℝ}
    (hle : (Δ - Ξ).PosSemidef) :
    innerSlidingSector c Ξ ⊆ slidingSector c Δ := by
  intro x hx
  simp only [innerSlidingSector, Set.mem_ofPred_eq] at hx
  simp only [slidingSector, Set.mem_ofPred_eq]
  have hdiff := hle.dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at hdiff
  linarith

/-- The second-order sector is the exact union of the inner and outer sectors,
`S_i ∪ S_o = S_2nd`, when `Ξ ⪯ Δ` (Pan & Furuta, Chapter 5, Section 3.3). -/
theorem inner_union_outer_eq_slidingSector {c : ι → ℝ} {Ξ Δ : Matrix ι ι ℝ}
    (hle : (Δ - Ξ).PosSemidef) :
    innerSlidingSector c Ξ ∪ outerSlidingSector c Ξ Δ = slidingSector c Δ := by
  ext x
  simp only [Set.mem_union, innerSlidingSector, outerSlidingSector, slidingSector,
    Set.mem_ofPred_eq]
  have hdiff := hle.dotProduct_mulVec_nonneg x
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub] at hdiff
  constructor
  · rintro (h | ⟨_, h2⟩)
    · linarith
    · exact h2
  · intro h
    by_cases hx : (c ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ (Ξ *ᵥ x)
    · exact Or.inl hx
    · exact Or.inr ⟨not_le.mp hx, h⟩

/-- The inner and outer sectors are disjoint, `S_i ∩ S_o = ∅`
(Pan & Furuta, Chapter 5, Section 3.3). -/
theorem inner_inter_outer_eq_empty (c : ι → ℝ) (Ξ Δ : Matrix ι ι ℝ) :
    innerSlidingSector c Ξ ∩ outerSlidingSector c Ξ Δ = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, innerSlidingSector, outerSlidingSector,
    Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro h1 h2
  linarith

/-! ### Quadratic Lyapunov derivatives and `P`-norm decay -/

/-- Time derivative of the symmetric quadratic form `s ↦ (x s) ⬝ᵥ (P *ᵥ (x s))`,
along a trajectory with coordinate derivatives `x'`. -/
theorem hasDerivAt_quadratic_form
    (P : Matrix ι ι ℝ) (hP_symm : Pᵀ = P)
    {x : ℝ → (ι → ℝ)} {x' : ι → ℝ} {t : ℝ}
    (hx : ∀ j, HasDerivAt (fun s ↦ x s j) (x' j) t) :
    HasDerivAt (fun s ↦ (x s) ⬝ᵥ (P *ᵥ (x s))) (2 * ((x t) ⬝ᵥ (P *ᵥ x'))) t := by
  have h := hasDerivAt_half_quadratic_form P hP_symm hx
  have h2 := h.const_mul (2 : ℝ)
  have heq : (fun s ↦ 2 * ((1 / 2 : ℝ) * ((x s) ⬝ᵥ (P *ᵥ (x s))))) =
      (fun s ↦ (x s) ⬝ᵥ (P *ᵥ (x s))) := by
    funext s; ring
  rw [heq] at h2
  exact h2

/-- Symmetry identity connecting `2 * (x ⬝ᵥ (P *ᵥ (A *ᵥ x)))` with the matrix sum
`P * A + Aᵀ * P` for symmetric `P`. -/
theorem quadratic_form_linear_symm (P A : Matrix ι ι ℝ) (hP_symm : Pᵀ = P) (x : ι → ℝ) :
    2 * (x ⬝ᵥ (P *ᵥ (A *ᵥ x))) = x ⬝ᵥ ((P * A + Aᵀ * P) *ᵥ x) := by
  simp only [Matrix.add_mulVec, dotProduct_add]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have h1 : x ⬝ᵥ Aᵀ *ᵥ (P *ᵥ x) = (P *ᵥ x) ⬝ᵥ (A *ᵥ x) :=
    Matrix.dotProduct_transpose_mulVec A x (P *ᵥ x)
  have h2 : (A *ᵥ x) ⬝ᵥ P *ᵥ x = x ⬝ᵥ (P *ᵥ (A *ᵥ x)) := by
    have h := Matrix.dotProduct_transpose_mulVec P (A *ᵥ x) x
    rwa [hP_symm] at h
  rw [h1, dotProduct_comm (P *ᵥ x) (A *ᵥ x), h2]
  ring

/-- The orbital derivative of the quadratic form along the autonomous linear system
`x' = A *ᵥ x` is `x(t) ⬝ᵥ ((P * A + Aᵀ * P) *ᵥ x(t))`. -/
theorem hasDerivAt_quadratic_form_linear_system
    (P A : Matrix ι ι ℝ) (hP_symm : Pᵀ = P)
    {x : ℝ → (ι → ℝ)} {t : ℝ}
    (hx : ∀ j, HasDerivAt (fun s ↦ x s j) ((A *ᵥ (x t)) j) t) :
    HasDerivAt (fun s ↦ (x s) ⬝ᵥ (P *ᵥ (x s)))
      ((x t) ⬝ᵥ ((P * A + Aᵀ * P) *ᵥ (x t))) t := by
  have h := hasDerivAt_quadratic_form P hP_symm hx
  rw [quadratic_form_linear_symm P A hP_symm (x t)] at h
  exact h

/-- **Sector domination ⇒ `P`-norm decrease** (Pan & Furuta, Chapter 5, Theorem 1).
Under the sector domination condition on `P * A + Aᵀ * P + R`, the quadratic form
`x ⬝ᵥ ((P * A + Aᵀ * P) *ᵥ x)` decreases at rate at least `x ⬝ᵥ (R *ᵥ x)` for every
state `x` inside the sliding sector. The hypothesis `x ∈ slidingSector c Δ` is used
through the sector constraint; the result is not a global matrix inequality. -/
theorem quadratic_form_decrease_in_sector
    {c : ι → ℝ} {Δ P A R : Matrix ι ι ℝ}
    (h_dom : ∀ x, x ⬝ᵥ ((P * A + Aᵀ * P + R) *ᵥ x) ≤
      (c ⬝ᵥ x) ^ 2 - x ⬝ᵥ (Δ *ᵥ x))
    {x : ι → ℝ} (hx : x ∈ slidingSector c Δ) :
    x ⬝ᵥ ((P * A + Aᵀ * P) *ᵥ x) ≤ -(x ⬝ᵥ (R *ᵥ x)) := by
  simp only [slidingSector, Set.mem_ofPred_eq] at hx
  have hd := h_dom x
  have hsum : x ⬝ᵥ ((P * A + Aᵀ * P + R) *ᵥ x) =
      x ⬝ᵥ ((P * A + Aᵀ * P) *ᵥ x) + x ⬝ᵥ (R *ᵥ x) := by
    simp only [Matrix.add_mulVec, dotProduct_add]
  rw [hsum] at hd
  linarith

/-- Trajectory-level `P`-norm orbital derivative decay along `x' = A *ᵥ x` inside
the sector: there is a derivative value `d` of the quadratic form that is at most
`-(x t ⬝ᵥ (R *ᵥ x t))`. -/
theorem hasDerivAt_p_norm_decrease_in_sector
    {c : ι → ℝ} {Δ P A R : Matrix ι ι ℝ} (hP_symm : Pᵀ = P)
    (h_dom : ∀ x, x ⬝ᵥ ((P * A + Aᵀ * P + R) *ᵥ x) ≤
      (c ⬝ᵥ x) ^ 2 - x ⬝ᵥ (Δ *ᵥ x))
    {x : ℝ → (ι → ℝ)} {t : ℝ}
    (hx : ∀ j, HasDerivAt (fun s ↦ x s j) ((A *ᵥ (x t)) j) t)
    (hsec : x t ∈ slidingSector c Δ) :
    ∃ d : ℝ, HasDerivAt (fun s ↦ (x s) ⬝ᵥ (P *ᵥ (x s))) d t ∧
      d ≤ -(x t ⬝ᵥ (R *ᵥ (x t))) :=
  ⟨(x t) ⬝ᵥ ((P * A + Aᵀ * P) *ᵥ (x t)),
    hasDerivAt_quadratic_form_linear_system P A hP_symm hx,
    quadratic_form_decrease_in_sector h_dom hsec⟩

/-! ### Second-order sector invariance -/

/-- Algebraic infinitesimal tangency: along any vector field `F` whose sector-defect
derivative is nonpositive, the Lie derivative of the defect is nonpositive. The previously
present hypothesis `x ∈ outerSlidingSector c Ξ Δ` was unused (the implication needs only
the differential inequality) and has been removed together with the dead parameter `Ξ`. -/
theorem sectorDefect_lieDeriv_nonpos
    {c : ι → ℝ} {Δ : Matrix ι ι ℝ} {F : (ι → ℝ) → (ι → ℝ)} {x : ι → ℝ}
    (hinv : 2 * (c ⬝ᵥ x) * (c ⬝ᵥ F x) ≤ 2 * (x ⬝ᵥ (Δ *ᵥ F x))) :
    sectorDefectLieDeriv c Δ F x ≤ 0 := by
  simp only [sectorDefectLieDeriv]
  linarith

/-- Path-level forward invariance: if a continuous trajectory starts in
`slidingSector c Δ` and the sector defect `v(t) = sectorDefect c Δ (x t)` has
non-positive derivative on `(0, T)`, then `x t ∈ slidingSector c Δ` for all
`t ∈ [0, T]`. -/
theorem slidingSector_invariant_of_deriv_nonpos
    {c : ι → ℝ} {Δ : Matrix ι ι ℝ} {x : ℝ → (ι → ℝ)} {T : ℝ} (hT : 0 ≤ T)
    (hinit : x 0 ∈ slidingSector c Δ)
    (hcont : ContinuousOn (fun t ↦ sectorDefect c Δ (x t)) (Set.Icc 0 T))
    (hdiff : DifferentiableOn ℝ (fun t ↦ sectorDefect c Δ (x t))
      (interior (Set.Icc 0 T)))
    (hderiv : ∀ t ∈ interior (Set.Icc 0 T),
      deriv (fun s ↦ sectorDefect c Δ (x s)) t ≤ 0) :
    ∀ t ∈ Set.Icc 0 T, x t ∈ slidingSector c Δ := by
  intro t ht
  rw [mem_slidingSector_iff_defect_nonpos]
  rw [mem_slidingSector_iff_defect_nonpos] at hinit
  have hmono : MonotoneOn (fun s ↦ -sectorDefect c Δ (x s)) (Set.Icc 0 T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T)
    · exact hcont.neg
    · exact hdiff.neg
    · intro s hs
      have hneg : deriv (fun u ↦ -sectorDefect c Δ (x u)) s =
          -deriv (fun u ↦ sectorDefect c Δ (x u)) s := deriv.neg
      rw [hneg]
      have := hderiv s hs
      linarith
  have hle := hmono ⟨le_refl 0, hT⟩ ht ht.1
  simp only [neg_le_neg_iff] at hle
  linarith
