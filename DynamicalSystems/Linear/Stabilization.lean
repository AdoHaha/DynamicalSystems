/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.PolePlacement
public import DynamicalSystems.Linear.Hautus
public import DynamicalSystems.Stability.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Stabilization and detectability of real linear systems

This file builds the algebraic stabilization theory of Trentelman, Stoorvogel
and Hautus, *Control Theory for Linear Systems*, Sections 3.7, 3.10 and 3.11, on
top of the accepted pole-placement theorem (`DynamicalSystems.Linear.PolePlacement`)
and the accepted PBH/Hautus criteria (`DynamicalSystems.Linear.Hautus`).

## Hurwitz operators

For a real endomorphism `A` of a finite-dimensional real vector space the
characteristic polynomial `A.charpoly` has real coefficients. Its roots in `ℂ`
are the eigenvalues of the complexification of `A`. Following the source we call
`A` *Hurwitz* when every such complex eigenvalue has negative real part:

`LinearMap.IsHurwitz A := ∀ z : ℂ, (A.charpoly.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0`.

This is the complex-spectrum formulation required for real operators: a planar
rotation has no real eigenvalue but has the non-real pair `±i`, and the
complexified characteristic polynomial records it.

## Main results

* `LinearMap.isHurwitz_of_charpoly_eq_pow_X_add_one`: the companion target
  polynomial `(X + 1)^n` is Hurwitz, which turns pole placement into a
  stabilizing feedback.
* `LinearMap.isStabilizable_of_isControllable`: **gain existence** — a
  controllable real pair admits a state feedback `F` with `A + B.comp F`
  Hurwitz. The gain is produced by pole placement, not assumed.
* `LinearMap.isDetectable_of_isObservable`: the dual statement for output
  injection: an observable pair admits `L` with `A - L.comp C` Hurwitz. The
  proof uses the accepted duality `isObservable_iff_isControllable_dualMap`,
  pole placement on the dual, and the fact that `dualMap` is surjective with
  `charpoly (T.dualMap) = charpoly T`.
* `LinearMap.isDetectable_dual_of_isStabilizable`: the stabilizability→dual
detectability direction, with the dual injection realised by the negative
transpose of the stabilizing feedback.

## The decay bridge

The spectral predicate `IsHurwitz` is bridged to the existing dynamic stability
vocabulary by an explicit computation. Pole placement realises the target
`(X + 1)^n`, so Cayley–Hamilton gives `(T + 1)^n = 0`; the exponential is then a
finite polynomial-times-exponential sum and the flow is shown to be attractive
(`Filter.IsAttractive`) and Lyapunov stable (`Filter.IsStableOn`) at the origin.
Concretely:

* `LinearMap.exp_nilpotent_eq_sum`, `LinearMap.exp_decomp`: the finite
exponential series of a nilpotent shift.
* `LinearMap.norm_exp_nilpotent_shift_apply_le`: the uniform norm bound
  `‖exp (t A) x‖ ≤ C ‖x‖` for `t ≥ 0`, from `e^{-t} t^k / k! ≤ 1`.
* `LinearMap.tendsto_exp_nilpotent_shift_apply`,
  `LinearMap.isAttractive_exp_nilpotent_shift` and
  `LinearMap.isStableOn_exp_nilpotent_shift`: pointwise convergence, filter-level
  attractivity, and Lyapunov stability.
* `LinearMap.isAttractive_expFlow_of_charpoly_eq_pow_X_add_one` and
  `LinearMap.isStableOn_expFlow_of_charpoly_eq_pow_X_add_one`: the bridge from
  the pole-placement characteristic polynomial to decay and stability.
* `LinearMap.exists_stabilizing_feedback_attractive` and
  `LinearMap.exists_stabilizing_feedback_stable_attractive`: a controllable pair
  has a feedback whose closed loop is attractive (resp. asymptotically stable),
  with both the gain and the dynamic property derived rather than assumed.

The decay bridge above is stated for the explicit pole-placement target
`(X + 1)^n`, which is what the gain constructions realise; the *general*
spectral theorem "`IsHurwitz A` ⇒ every trajectory of `x' = A x` decays" is not
proved here (see the note at the end of this section).

## Converse criteria: unobservable and uncontrollable eigenvalues

* `LinearMap.IsUnobservableEigenvalue`: the real pair `(C, A)` has an
  unobservable eigenvalue `μ` when the complexification `ℂ ⊗[ℝ] X` contains a
  nonzero eigenvector of the complexified state map that is annihilated by the
  complexified readout (the eigenvector form of the PBH condition (3.14)).
* `LinearMap.isDetectable_converse_of_unobservableEigenvalue`: detectability
  forces `μ.re < 0` for every unobservable eigenvalue — the necessity direction
  of Theorem 3.38 / Corollary 3.30 for observers.
* `LinearMap.IsUncontrollableEigenvalue`: the dual notion for `(A, B)`, a
  nonzero complexified left eigenvector annihilating `range B`.
* `LinearMap.isStabilizable_converse_of_uncontrollableEigenvalue`:
  stabilizability forces `μ.re < 0` for every uncontrollable eigenvalue — the
  necessity direction of Theorem 3.32 (Corollary 3.30).
* `LinearMap.charpoly_dualMap_ofField`: the general-field transpose invariance
  `(T.dualMap).charpoly = T.charpoly` used to pass from the left eigenvector to
  the characteristic polynomial.

Both converses handle the complex spectrum of a real operator explicitly by
doing the eigenvector computation over the complexification and returning to
the real characteristic polynomial through `LinearMap.charpoly_baseChange`.

## Separation principle

* `LinearMap.blockOperator`: the block operator `[[T, K], [0, S]]` on
  `X × X`, equal to `(x, e) ↦ (T x + K e, S e)`.
* `LinearMap.toMatrix_blockOperator` and `LinearMap.charpoly_blockOperator`:
  in the product basis the block operator is upper block triangular and its
  characteristic polynomial is `T.charpoly * S.charpoly`, so its complex
  spectrum is `σ(T) ∪ σ(S)`.
* `LinearMap.isHurwitz_blockOperator`,
  `LinearMap.isHurwitz_separationOperator` and
  `LinearMap.exists_separation_block_hurwitz`: the assembled closed loop
  `[[A + B F, B F], [0, A - L C]]` of the observer-based controller is Hurwitz
  whenever both diagonal blocks are; a stabilizable and detectable system
  admits such gains `F` and `L`.

## Remaining obligation

The general finite-dimensional theorem that `IsHurwitz A` implies exponential
decay / attractivity / Lyapunov stability of `t ↦ exp (t A)` for *arbitrary*
Hurwitz `A` (not only the nilpotent shift `A + 1`) is not yet formalized. It
would connect `LinearMap.IsHurwitz A` directly to
`Filter.IsAttractive (l := 𝓝 0) (Φ := fun t x => exp (t • A.toContinuousLinearMap) x) atTop`
and to `(𝓝 0).IsStableOn` of the same flow. The complex half of this bridge is
now frozen in the section *The general Hurwitz-to-decay bridge: the complex
spectral case* below: `LinearMap.tendsto_exp_complex_apply` shows that over a
finite-dimensional complex normed space every orbit of a Hurwitz endomorphism
decays, by decomposing the space into generalized eigenspaces. What remains for
the real statement is the **real-coordinate reduction**: complexify
`A.baseChange ℂ`, apply the complex theorem there, and transport convergence
back along a real basis (`exp (t • A) = repr.symm ∘ exp (t • repr.conj A) ∘ repr`).
This is the next task; it is deliberately not claimed here. In addition, the
current slice proves the explicit pole-placement target bridge `(X + 1)^n`,
which is the case needed by every gain existence result here, via the finite
polynomial-times-exponential estimates (`LinearMap.norm_exp_nilpotent_shift_apply_le`,
`LinearMap.tendsto_exp_nilpotent_shift_apply`).

The eigenvalue criteria above are also only proved in the necessity direction.
`LinearMap.isStabilizable_converse_of_uncontrollableEigenvalue` and
`LinearMap.isDetectable_converse_of_unobservableEigenvalue` show that a
stabilizable (resp. detectable) pair has all uncontrollable (resp. unobservable)
eigenvalues in the open left half-plane. The *sufficiency* halves of
Trentelman–Stoorvogel–Hautus Theorems 3.32 and 3.38 — that those eigenvalue
conditions conversely imply stabilizability and detectability — are not
formalized in this slice. The expected route is the Kalman decomposition
(Theorem 3.11) together with pole placement on the controllable/observable part,
as in the source proofs; this is left as a follow-up obligation.

## Definition of stability

`IsStabilizable A B` means `∃ F, IsHurwitz (A + B.comp F)`. This is exactly the
existence of a stabilizing static state feedback. `IsDetectable C A` means
`∃ L, IsHurwitz (A - L.comp C)`, the existence of a stabilizing output
injection (Luenberger observer gain). Both are genuine existence statements:
no gain is assumed as a hypothesis.

## References

* H. L. Trentelman, A. A. Stoorvogel, M. Hautus, *Control Theory for Linear
  Systems*, Springer, 2001, Section 3.10 (Theorem 3.29 and the definition of
  stabilizability), Section 3.11 (Theorem 3.36 and Definition 3.37).
-/

@[expose] public section

open Polynomial LinearMap Filter Topology Module

namespace LinearMap

variable {X U Y : Type*}
variable [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]
variable [AddCommGroup U] [Module ℝ U]
variable [AddCommGroup Y] [Module ℝ Y] [FiniteDimensional ℝ Y]

/-! ## Hurwitz operators via the complexified characteristic polynomial -/

/-- A real endomorphism is **Hurwitz** when every complex root of its
complexified characteristic polynomial has negative real part. Equivalently,
every eigenvalue of the complexification of `A` lies in the open left
half-plane `{s : ℂ | re s < 0}`.

Source: Trentelman–Stoorvogel–Hautus, Section 3.7 (`σ(A) ⊂ ℂ⁻`) and
Definition 3.34/3.35. -/
def IsHurwitz (A : X →ₗ[ℝ] X) : Prop :=
  ∀ z : ℂ, (A.charpoly.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0

/-- The characteristic polynomial of the algebraic transpose equals that of the
original endomorphism, so being Hurwitz is invariant under duality. -/
theorem charpoly_dualMap (T : X →ₗ[ℝ] X) :
    T.dualMap.charpoly = T.charpoly := by
  classical
  let b : Module.Basis (Fin (Module.finrank ℝ X)) ℝ X := Module.finBasis ℝ X
  rw [← LinearMap.charpoly_toMatrix (f := T.dualMap) b.dualBasis,
      ← LinearMap.charpoly_toMatrix (f := T) b]
  rw [LinearMap.dualMap_def, LinearMap.toMatrix_transpose]
  exact Matrix.charpoly_transpose _

/-- Hurwitzness is invariant under the algebraic transpose. -/
theorem isHurwitz_dualMap_iff (T : X →ₗ[ℝ] X) :
    IsHurwitz T.dualMap ↔ IsHurwitz T := by
  rw [IsHurwitz, IsHurwitz, charpoly_dualMap]

/-- **Pole placement produces a Hurwitz operator.** If the characteristic
polynomial of `T` is the shifted power `(X + 1)^n`, then its only complex root
is `-1`, so `T` is Hurwitz. This is the bridge from the polynomial pole-placement
statement to the spectral stability condition; note that `n = 0` is impossible
because then `(X + 1)^0 = 1` has no root.

Source: Trentelman–Stoorvogel–Hautus, proof of Theorem 3.29 applied in the
proof of Theorem 3.32. -/
theorem isHurwitz_of_charpoly_eq_pow_X_add_one
    (T : X →ₗ[ℝ] X) (n : ℕ)
    (hT : T.charpoly = (Polynomial.X + Polynomial.C (1 : ℝ)) ^ n) :
    IsHurwitz T := by
  intro z hz
  rw [hT] at hz
  rw [Polynomial.map_pow, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at hz
  by_cases hn : n = 0
  · subst hn; norm_num at hz
  · have hz0 : z + 1 = 0 := (pow_eq_zero_iff hn).mp hz
    have hz1 : z = -1 := by linear_combination hz0
    rw [hz1]; norm_num

/-! ## Stabilizability and detectability as gain-existence statements -/

/-- The pair `(A, B)` is **stabilizable** when some static state feedback
`u = F x` makes the closed loop `A + B.comp F` Hurwitz.

Source: Trentelman–Stoorvogel–Hautus, Section 3.10, the paragraph following
Theorem 3.32. -/
def IsStabilizable (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) : Prop :=
  ∃ F : X →ₗ[ℝ] U, IsHurwitz (A + B.comp F)

/-- The pair `(C, A)` is **detectable** when some output-injection gain `L`
makes `A - L.comp C` Hurwitz, equivalently when a stable Luenberger state
observer exists.

Source: Trentelman–Stoorvogel–Hautus, Definition 3.37. -/
def IsDetectable (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) : Prop :=
  ∃ L : Y →ₗ[ℝ] X, IsHurwitz (A - L.comp C)

/-- An already-Hurwitz pair is stabilizable with the zero feedback. -/
theorem isStabilizable_of_isHurwitz (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (h : IsHurwitz A) : IsStabilizable A B :=
  ⟨0, by simpa using h⟩

omit [FiniteDimensional ℝ Y] in
/-- A pair with `A` Hurwitz is detectable with the zero injection. -/
theorem isDetectable_of_isHurwitz (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X)
    (h : IsHurwitz A) : IsDetectable C A :=
  ⟨0, by simpa using h⟩

/-- **Existence of a stabilizing state feedback from controllability.**
If `(A, B)` is controllable then there is a real state feedback `F` with
`A + B.comp F` Hurwitz. The gain is produced by the accepted multi-input
pole-placement theorem applied to the target polynomial `(X + 1)^n`, so this is
a genuine gain-existence result and assumes no gain.

Source: Trentelman–Stoorvogel–Hautus, Theorem 3.29 combined with
Theorem 3.32. -/
theorem isStabilizable_of_isControllable
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (h : IsControllable A B) :
    IsStabilizable A B := by
  set n : ℕ := Module.finrank ℝ X with hn
  set p : ℝ[X] := (Polynomial.X + Polynomial.C (1 : ℝ)) ^ n with hp
  have hpmonic : p.Monic := (Polynomial.monic_X_add_C (1 : ℝ)).pow n
  have hpdeg : p.natDegree = Module.finrank ℝ X := by
    rw [hp, Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C, mul_one]
  obtain ⟨F, hF⟩ := exists_feedback_charpoly_of_isControllable A B h p hpmonic hpdeg
  exact ⟨F, isHurwitz_of_charpoly_eq_pow_X_add_one (A + B.comp F) n hF⟩

/-! ## Duality of the algebraic transpose on hom spaces -/

omit [FiniteDimensional ℝ X] in
/-- The algebraic transpose is additive on endomorphisms. -/
theorem dualMap_add (T S : X →ₗ[ℝ] X) :
    (T + S).dualMap = T.dualMap + S.dualMap := by
  rw [LinearMap.dualMap_def, LinearMap.dualMap_def, LinearMap.dualMap_def, map_add]

omit [FiniteDimensional ℝ X] in
/-- The algebraic transpose is additive on endomorphisms. -/
theorem dualMap_sub (T S : X →ₗ[ℝ] X) :
    (T - S).dualMap = T.dualMap - S.dualMap := by
  rw [LinearMap.dualMap_def, LinearMap.dualMap_def, LinearMap.dualMap_def, map_sub]

/-- **The algebraic transpose between hom spaces is surjective.** For
finite-dimensional `X` and `Y`, every linear map `F : Dual X →ₗ Dual Y` is the
transpose `L.dualMap` of some `L : Y →ₗ X`. The witness is
`L = (evalEquiv X).symm ∘ F.dualMap ∘ evalEquiv Y`.

This is the coordinate-free form of "every matrix is the transpose of its
transpose", and is what lets a feedback on the dual pair be realised as an
output injection on the original pair. -/
theorem dualMap_surjective :
    Function.Surjective
      (LinearMap.dualMap : (Y →ₗ[ℝ] X) → (Module.Dual ℝ X →ₗ[ℝ] Module.Dual ℝ Y)) := by
  intro F
  refine ⟨(Module.evalEquiv ℝ X).symm.toLinearMap.comp
    (F.dualMap.comp (Module.evalEquiv ℝ Y).toLinearMap), ?_⟩
  ext φ x
  change φ ((Module.evalEquiv ℝ X).symm (F.dualMap ((Module.evalEquiv ℝ Y) x))) = (F φ) x
  rw [Module.apply_evalEquiv_symm_apply, LinearMap.dualMap_apply]
  rfl

/-! ## Detectability from observability -/

/-- **Existence of a stabilizing output injection from observability.**
If `(C, A)` is observable then there is `L` with `A - L.comp C` Hurwitz. The
proof dualises the pair with `isObservable_iff_isControllable_dualMap`, applies
`isStabilizable_of_isControllable` to `(A.dualMap, C.dualMap)` to obtain a dual
feedback `F`, lifts `-F` back to an output injection `L` using
`dualMap_surjective`, and transfers Hurwitzness across the transpose with
`isHurwitz_dualMap_iff`.

Source: Trentelman–Stoorvogel–Hautus, Theorem 3.38 (the equivalence
(iii) ⇒ (ii)). -/
theorem isDetectable_of_isObservable
    (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) (h : IsObservable C A) :
    IsDetectable C A := by
  have hc : IsControllable A.dualMap C.dualMap :=
    (isObservable_iff_isControllable_dualMap C A).mp h
  obtain ⟨F, hF⟩ := isStabilizable_of_isControllable A.dualMap C.dualMap hc
  obtain ⟨L, hL⟩ := dualMap_surjective (Y := Y) (X := X) (-F)
  refine ⟨L, ?_⟩
  have hdual : (A - L.comp C).dualMap = A.dualMap + C.dualMap.comp F := by
    rw [dualMap_sub, ← LinearMap.dualMap_comp_dualMap C L, hL, LinearMap.comp_neg]
    abel
  rw [← isHurwitz_dualMap_iff (A - L.comp C)]
  rw [hdual]
  exact hF

/-! ## Duality: stabilizability implies dual detectability -/

/-- Stabilizability of `(A, B)` yields detectability of the dual pair
`(B.dualMap, A.dualMap)`, with the dual injection realised by the negative
transpose of the stabilizing state feedback. This is the easy direction of the
stabilizability–detectability duality and is a genuine gain construction. -/
theorem isDetectable_dual_of_isStabilizable
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (h : IsStabilizable A B) :
    IsDetectable B.dualMap A.dualMap := by
  obtain ⟨F, hF⟩ := h
  refine ⟨-F.dualMap, ?_⟩
  have h : (A + B.comp F).dualMap = A.dualMap - (-F.dualMap).comp B.dualMap := by
    rw [dualMap_add, ← LinearMap.dualMap_comp_dualMap F B,
      LinearMap.neg_comp B.dualMap F.dualMap]
    abel
  rw [← h]
  exact (isHurwitz_dualMap_iff (A + B.comp F)).mpr hF

/-! ## The Hurwitz/exponential-decay bridge for the pole-placement target

The pole-placement construction produces a feedback with characteristic
polynomial `(X + 1)^n`. By Cayley–Hamilton this means `(A + B F + 1)^n = 0`, so
`A + B F = -1 + N` with `N` nilpotent. The exponential of `t (A + B F)` is then
the finite sum

`exp (t (A + B F)) = ∑_{k<n} (e^{-t} t^k / k!) • N^k`,

whose summands tend to zero at `+∞`. This proves that the pole-placement
stabilizer really is exponentially decaying: the analytic `IsAttractive`
predicate is derived from the algebraic construction, with no hypothesis on the
decay supplied by the caller.

The general spectral statement "Hurwitz implies exponential decay" is not used
here; the bridge is proved for the explicit target polynomial that the
stabilization theorem realises. -/

section ExponentialDecay

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- A nilpotent element has a finite exponential series. This is the algebraic
core of the decay bridge: only the first `n` terms of the exponential series
survive when `N ^ n = 0`. -/
theorem exp_nilpotent_eq_sum (N : E →L[ℝ] E) (n : ℕ) (hN : N ^ n = 0) (t : ℝ) :
    NormedSpace.exp (t • N) =
      ∑ k ∈ Finset.range n, ((k.factorial : ℝ)⁻¹) • (t • N) ^ k := by
  rw [show NormedSpace.exp (t • N) =
      ∑' (k : ℕ), ((k.factorial : ℝ)⁻¹) • (t • N) ^ k from
    congrFun (NormedSpace.exp_eq_tsum ℝ) (t • N)]
  rw [tsum_eq_sum (s := Finset.range n)]
  intro k hk
  rw [Finset.mem_range, not_lt] at hk
  have : (t • N) ^ k = t ^ k • N ^ k := by rw [smul_pow]
  rw [this, pow_eq_zero_of_le hk hN, smul_zero, smul_zero]

omit [FiniteDimensional ℝ E] in
/-- The exponential of a negative scalar multiple of the identity is the scalar
exponential times the identity, evaluated pointwise. -/
theorem exp_smul_one_apply (t : ℝ) (x : E) :
    NormedSpace.exp ((-t) • (1 : E →L[ℝ] E)) x = Real.exp (-t) • x := by
  rw [← Algebra.algebraMap_eq_smul_one]
  rw [← NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := E →L[ℝ] E) (-t)]
  rw [← Real.exp_eq_exp_ℝ, Algebra.algebraMap_eq_smul_one]
  rfl

/-- **Exponential decomposition of a nilpotent shift.** If `(A + 1) ^ n = 0`,
then `A = -1 + (A + 1)` with `N = A + 1` nilpotent, so

`exp (t A) = ∑_{k<n} (e^{-t} / k!) • (t N)^k`.

This is the explicit polynomial-times-exponential formula behind the decay. -/
theorem exp_decomp (A : E →L[ℝ] E) (n : ℕ) (hA : (A + 1) ^ n = 0) (t : ℝ) :
    NormedSpace.exp (t • A) =
      ∑ k ∈ Finset.range n, (Real.exp (-t) * ((k.factorial : ℝ)⁻¹)) •
        (t • (A + 1)) ^ k := by
  have hsplit : t • A = t • (A + 1) + (-t) • (1 : E →L[ℝ] E) := by
    rw [smul_add, add_assoc, ← add_smul, add_neg_cancel, zero_smul, add_zero]
  rw [hsplit, NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ)]
  · rw [exp_nilpotent_eq_sum (A + 1) n hA t]
    rw [show NormedSpace.exp ((-t) • (1 : E →L[ℝ] E)) = Real.exp (-t) • 1 from ?_]
    · rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_smul_comm, mul_one, smul_smul]
    · ext x
      rw [exp_smul_one_apply]
      rfl
  · exact (Algebra.commute_algebraMap_left (-t) (t • (A + 1))).symm
  · exact (NormedSpace.expSeries_radius_eq_top ℝ (E →L[ℝ] E)).symm ▸ edist_lt_top _ _
  · exact (NormedSpace.expSeries_radius_eq_top ℝ (E →L[ℝ] E)).symm ▸ edist_lt_top _ _

/-- **Uniform bound on the nilpotent-shift flow.** For `t ≥ 0` the explicit
finite-sum exponential is bounded by `C * ‖x‖`, where
`C = ∑_{k<n} ‖(A + 1)^k‖`. This is the norm estimate behind Lyapunov stability:
the factor `e^{-t} t^k / k!` is at most `1` on `[0, ∞)`. -/
theorem norm_exp_nilpotent_shift_apply_le
    (A : E →L[ℝ] E) (n : ℕ) (hA : (A + 1) ^ n = 0) (t : ℝ) (ht : 0 ≤ t) (x : E) :
    ‖NormedSpace.exp (t • A) x‖ ≤
      (∑ k ∈ Finset.range n, ‖(A + 1) ^ k‖) * ‖x‖ := by
  have hdecomp : NormedSpace.exp (t • A) x =
      ∑ k ∈ Finset.range n, ((t ^ k * Real.exp (-t)) * ((k.factorial : ℝ)⁻¹)) •
        ((A + 1) ^ k) x := by
    rw [exp_decomp A n hA t, _root_.sum_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [_root_.smul_apply, smul_pow, _root_.smul_apply,
      smul_smul]
    congr 1
    ring
  rw [hdecomp]
  calc ‖∑ k ∈ Finset.range n, ((t ^ k * Real.exp (-t)) * ((k.factorial : ℝ)⁻¹)) •
        ((A + 1) ^ k) x‖
      ≤ ∑ k ∈ Finset.range n, ‖((t ^ k * Real.exp (-t)) * ((k.factorial : ℝ)⁻¹)) •
        ((A + 1) ^ k) x‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, ‖(A + 1) ^ k‖ * ‖x‖ := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_smul, Real.norm_eq_abs]
        have hc : |(t ^ k * Real.exp (-t)) * ((k.factorial : ℝ)⁻¹)| ≤ 1 := by
          have hnn : 0 ≤ (t ^ k * Real.exp (-t)) * ((k.factorial : ℝ)⁻¹) := by positivity
          rw [abs_of_nonneg hnn]
          have hle : t ^ k / (k.factorial : ℝ) ≤ Real.exp t :=
            Real.pow_div_factorial_le_exp t ht k
          have h2 : t ^ k / (k.factorial : ℝ) * Real.exp (-t) ≤
              Real.exp t * Real.exp (-t) :=
            mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _)
          rw [← Real.exp_add] at h2
          simp only [add_neg_cancel, Real.exp_zero] at h2
          calc (t ^ k * Real.exp (-t)) * ((k.factorial : ℝ)⁻¹)
              = t ^ k / (k.factorial : ℝ) * Real.exp (-t) := by
                rw [div_eq_mul_inv]; ring
            _ ≤ 1 := h2
        calc |(t ^ k * Real.exp (-t)) * ((k.factorial : ℝ)⁻¹)| * ‖((A + 1) ^ k) x‖
            ≤ 1 * ‖((A + 1) ^ k) x‖ :=
              mul_le_mul_of_nonneg_right hc (norm_nonneg _)
          _ ≤ 1 * (‖(A + 1) ^ k‖ * ‖x‖) :=
              mul_le_mul_of_nonneg_left (ContinuousLinearMap.le_opNorm _ _) (by norm_num)
          _ = ‖(A + 1) ^ k‖ * ‖x‖ := by ring
    _ = (∑ k ∈ Finset.range n, ‖(A + 1) ^ k‖) * ‖x‖ := by
        rw [Finset.sum_mul]

/-- **Pointwise exponential decay.** If `(A + 1) ^ n = 0` then every trajectory
of `x' = A x` tends to zero: the explicit sum has finitely many summands
`(t^k e^{-t} / k!) • N^k x`, each of which vanishes at `+∞`. -/
theorem tendsto_exp_nilpotent_shift_apply
    (A : E →L[ℝ] E) (n : ℕ) (hA : (A + 1) ^ n = 0) (x : E) :
    Tendsto (fun t : ℝ => NormedSpace.exp (t • A) x) atTop (𝓝 0) := by
  have hdecomp : ∀ t, NormedSpace.exp (t • A) x =
      ∑ k ∈ Finset.range n, ((t ^ k * Real.exp (-t)) * ((k.factorial : ℝ)⁻¹)) •
        ((A + 1) ^ k) x := by
    intro t
    rw [exp_decomp A n hA t, _root_.sum_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [_root_.smul_apply, smul_pow, _root_.smul_apply,
      smul_smul]
    congr 1
    ring
  rw [show (fun t : ℝ => NormedSpace.exp (t • A) x) = fun t =>
      ∑ k ∈ Finset.range n, ((t ^ k * Real.exp (-t)) * ((k.factorial : ℝ)⁻¹)) •
        ((A + 1) ^ k) x from funext hdecomp]
  have hlim : Tendsto (fun t : ℝ =>
      ∑ k ∈ Finset.range n, ((t ^ k * Real.exp (-t)) * ((k.factorial : ℝ)⁻¹)) •
        ((A + 1) ^ k) x) atTop
      (𝓝 (∑ k ∈ Finset.range n, (0 : ℝ) • ((A + 1) ^ k) x)) := by
    apply tendsto_finsetSum
    intro k _
    have h1 : Tendsto (fun t : ℝ => t ^ k * Real.exp (-t)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k
    have := (h1.mul_const ((k.factorial : ℝ)⁻¹)).smul_const (((A + 1) ^ k) x)
    simpa [mul_assoc] using this
  simpa using hlim

/-- **Attractivity of the exponential flow.** If `(A + 1) ^ n = 0` then the
flow `Φ t x = exp (t A) x` is attractive at the origin in the sense of
`Filter.IsAttractive` from the project stability vocabulary. This connects the
spectral/pole-placement construction to the existing stability API. -/
theorem isAttractive_exp_nilpotent_shift
    (A : E →L[ℝ] E) (n : ℕ) (hA : (A + 1) ^ n = 0) :
    Filter.IsAttractive (l := 𝓝 (0 : E)) (Φ := fun (t : ℝ) (x : E) =>
      NormedSpace.exp (t • A) x) (l' := atTop) := by
  change ∀ᶠ x in 𝓝 (0 : E), Tendsto (fun t : ℝ => NormedSpace.exp (t • A) x) atTop (𝓝 0)
  exact Filter.Eventually.of_forall fun x => tendsto_exp_nilpotent_shift_apply A n hA x

/-- **Lyapunov stability of the nilpotent-shift flow.** The uniform bound
`‖exp (t A) x‖ ≤ C ‖x‖` on `[0, ∞)` from
`norm_exp_nilpotent_shift_apply_le` makes the origin stable in the sense of
`Filter.IsStableOn`: trajectories starting in a small ball stay in any
prescribed neighbourhood. Together with `isAttractive_exp_nilpotent_shift`
this gives the full asymptotic-stability package for the pole-placement target. -/
theorem isStableOn_exp_nilpotent_shift
    (A : E →L[ℝ] E) (n : ℕ) (hA : (A + 1) ^ n = 0) :
    (𝓝 (0 : E)).IsStableOn
      (fun (t : ℝ) (x : E) => NormedSpace.exp (t • A) x) (Set.Ici 0) := by
  intro s hs
  rw [Metric.mem_nhds_iff] at hs
  obtain ⟨ε, hεpos, hεs⟩ := hs
  set C : ℝ := ∑ k ∈ Finset.range n, ‖(A + 1) ^ k‖ with hC
  have hCnn : 0 ≤ C := Finset.sum_nonneg (fun k _ => norm_nonneg _)
  refine ⟨Metric.ball (0 : E) (ε / (C + 1)),
    Metric.ball_mem_nhds _ (by positivity), ?_⟩
  intro t ht x hx
  apply hεs
  rw [Metric.mem_ball, dist_zero_right] at hx ⊢
  have hbound := norm_exp_nilpotent_shift_apply_le A n hA t (Set.mem_Ici.mp ht) x
  have hC1 : 0 < C + 1 := by linarith
  calc ‖NormedSpace.exp (t • A) x‖ ≤ C * ‖x‖ := hbound
    _ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hx.le hCnn
    _ = ε * (C / (C + 1)) := by ring
    _ < ε * 1 := by
        apply mul_lt_mul_of_pos_left _ hεpos
        rw [div_lt_one hC1]
        linarith
    _ = ε := by ring

end ExponentialDecay

/-! ## From pole placement to exponential decay

The remaining step transfers the algebraic characteristic-polynomial identity
`(A + B F).charpoly = (X + 1)^n` to the nilpotency `(A + B F + 1)^n = 0` and
then applies the decay bridge above. -/

section CharpolyDecay

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

/-- Cayley–Hamilton turns the pole-placement identity `charpoly T = (X + 1)^n`
into the nilpotency `(T + 1)^n = 0` for the continuous realisation of `T`. -/
theorem toContinuousLinearMap_add_one_pow_eq_zero
    (T : X →ₗ[ℝ] X) (n : ℕ)
    (hT : T.charpoly = (Polynomial.X + Polynomial.C (1 : ℝ)) ^ n) :
    (T.toContinuousLinearMap + 1) ^ n = 0 := by
  have hAlg : (T + 1) ^ n = 0 := by
    have h := LinearMap.aeval_self_charpoly T
    rw [hT] at h
    simpa using h
  have hmap : T.toContinuousLinearMap + 1 =
      Module.End.toContinuousLinearMap X (T + 1) := by
    rw [map_add, map_one]
    rfl
  rw [hmap, ← map_pow, hAlg, map_zero]

/-- **The Hurwitz/decay bridge for the pole-placement target.** A real state map
whose characteristic polynomial is `(X + 1)^n` generates an exponentially
decaying (in particular attractive) flow. This is the analytic content of the
stabilization theorem: the feedback computed by pole placement really drives the
closed loop to the origin. -/
theorem isAttractive_expFlow_of_charpoly_eq_pow_X_add_one
    (T : X →ₗ[ℝ] X) (n : ℕ)
    (hT : T.charpoly = (Polynomial.X + Polynomial.C (1 : ℝ)) ^ n) :
    Filter.IsAttractive (l := 𝓝 (0 : X)) (Φ := fun (t : ℝ) (x : X) =>
      NormedSpace.exp (t • T.toContinuousLinearMap) x) (l' := atTop) :=
  isAttractive_exp_nilpotent_shift T.toContinuousLinearMap n
    (toContinuousLinearMap_add_one_pow_eq_zero T n hT)

/-- **Lyapunov stability for the pole-placement target.** The same
characteristic-polynomial hypothesis yields `Filter.IsStableOn` at the origin:
the explicit exponential flow is uniformly bounded on `[0, ∞)`. Combining this
with `isAttractive_expFlow_of_charpoly_eq_pow_X_add_one` gives asymptotic
stability of the closed loop, stated entirely in the project's stability
vocabulary. -/
theorem isStableOn_expFlow_of_charpoly_eq_pow_X_add_one
    (T : X →ₗ[ℝ] X) (n : ℕ)
    (hT : T.charpoly = (Polynomial.X + Polynomial.C (1 : ℝ)) ^ n) :
    (𝓝 (0 : X)).IsStableOn
      (fun (t : ℝ) (x : X) => NormedSpace.exp (t • T.toContinuousLinearMap) x)
      (Set.Ici 0) :=
  isStableOn_exp_nilpotent_shift T.toContinuousLinearMap n
    (toContinuousLinearMap_add_one_pow_eq_zero T n hT)

/-- **Certified stabilizing feedback for a controllable real system.** A
controllable real pair admits a state feedback `F` whose closed-loop flow
`t ↦ exp (t (A + B F))` is attractive at the origin in the sense of
`Filter.IsAttractive`. The gain is produced by the accepted pole-placement
theorem and the attractivity is *derived*, so neither the gain nor the decay is
assumed. -/
theorem exists_stabilizing_feedback_attractive
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (h : IsControllable A B) :
    ∃ F : X →ₗ[ℝ] U,
      Filter.IsAttractive (l := 𝓝 (0 : X)) (Φ := fun (t : ℝ) (x : X) =>
        NormedSpace.exp (t • (A + B.comp F).toContinuousLinearMap) x) (l' := atTop) := by
  set n : ℕ := Module.finrank ℝ X with hn
  set p : ℝ[X] := (Polynomial.X + Polynomial.C (1 : ℝ)) ^ n with hp
  have hpmonic : p.Monic := (Polynomial.monic_X_add_C (1 : ℝ)).pow n
  have hpdeg : p.natDegree = Module.finrank ℝ X := by
    rw [hp, Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C, mul_one]
  obtain ⟨F, hF⟩ := exists_feedback_charpoly_of_isControllable A B h p hpmonic hpdeg
  exact ⟨F, isAttractive_expFlow_of_charpoly_eq_pow_X_add_one (A + B.comp F) n hF⟩

/-- **Certified asymptotically stabilizing feedback for a controllable real
system.** A controllable real pair admits a state feedback `F` whose closed-loop
flow is both Lyapunov stable (`Filter.IsStableOn`) and attractive at the origin.
The gain comes from the accepted pole-placement theorem and both dynamic
properties are derived from the `(X + 1)^n` characteristic polynomial, so
neither the gain nor the stability is assumed. -/
theorem exists_stabilizing_feedback_stable_attractive
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (h : IsControllable A B) :
    ∃ F : X →ₗ[ℝ] U,
      (𝓝 (0 : X)).IsStableOn (fun (t : ℝ) (x : X) =>
        NormedSpace.exp (t • (A + B.comp F).toContinuousLinearMap) x) (Set.Ici 0) ∧
      Filter.IsAttractive (l := 𝓝 (0 : X)) (Φ := fun (t : ℝ) (x : X) =>
        NormedSpace.exp (t • (A + B.comp F).toContinuousLinearMap) x) (l' := atTop) := by
  set n : ℕ := Module.finrank ℝ X with hn
  set p : ℝ[X] := (Polynomial.X + Polynomial.C (1 : ℝ)) ^ n with hp
  have hpmonic : p.Monic := (Polynomial.monic_X_add_C (1 : ℝ)).pow n
  have hpdeg : p.natDegree = Module.finrank ℝ X := by
    rw [hp, Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C, mul_one]
  obtain ⟨F, hF⟩ := exists_feedback_charpoly_of_isControllable A B h p hpmonic hpdeg
  exact ⟨F, isStableOn_expFlow_of_charpoly_eq_pow_X_add_one (A + B.comp F) n hF,
    isAttractive_expFlow_of_charpoly_eq_pow_X_add_one (A + B.comp F) n hF⟩

end CharpolyDecay

/-! ## The separation-principle block operator

When an observer-based controller applies the state feedback `u = F ξ` to the
estimate, the coupled plant/error dynamics is

```
x' = (A + B F) x + B F e,
e' = (A - L C) e.
```

The coefficient operator on `X × X` is the block upper-triangular matrix
`[[A + B F, B F], [0, A - L C]]`. The results below assemble this operator and
prove that its characteristic polynomial is the product of those of the two
diagonal blocks, hence that its complex spectrum is the union
`σ(A + B F) ∪ σ(A - L C)`. In particular a stabilizing feedback together with a
stabilizing output injection yields a Hurwitz closed-loop operator: this is the
spectral content of the separation principle (Trentelman–Stoorvogel–Hautus,
Section 3.12, the displayed matrix `A_e` preceding Theorem 3.40). -/

section Separation

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]

/-- The block operator `[[T, K], [0, S]]` on `X × X`, acting by
`(x, e) ↦ (T x + K e, S e)`. With `T = A + B F`, `K = B F` and `S = A - L C`
this is the closed-loop operator of the observer-based controller. -/
noncomputable def blockOperator (T K S : X →ₗ[ℝ] X) : X × X →ₗ[ℝ] X × X :=
  T.prodMap S + (K.comp (LinearMap.snd ℝ X X)).prod 0

omit [FiniteDimensional ℝ X] in
/-- Evaluation rule for `blockOperator`. -/
theorem blockOperator_apply (T K S : X →ₗ[ℝ] X) (x e : X) :
    blockOperator T K S (x, e) = (T x + K e, S e) := by
  simp [blockOperator, LinearMap.prodMap_apply, LinearMap.prod_apply]

omit [FiniteDimensional ℝ X] in
/-- In the product basis `b.prod b`, the block operator has the block matrix
`[[T, K], [0, S]]`. This is the coordinate computation behind the spectrum
factorization. -/
theorem toMatrix_blockOperator {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ X) (T K S : X →ₗ[ℝ] X) :
    LinearMap.toMatrix (b.prod b) (b.prod b) (blockOperator T K S) =
      Matrix.fromBlocks (LinearMap.toMatrix b b T) (LinearMap.toMatrix b b K) 0
        (LinearMap.toMatrix b b S) := by
  rw [blockOperator, map_add, LinearMap.toMatrix_prodMap (v₁ := b) (v₂ := b)]
  have hc : LinearMap.toMatrix (b.prod b) (b.prod b)
      ((K.comp (LinearMap.snd ℝ X X)).prod 0) =
      Matrix.fromBlocks 0 (LinearMap.toMatrix b b K) 0 0 := by
    ext (i | i) (j | j) <;>
      simp [LinearMap.toMatrix_apply, LinearMap.prod_apply,
        Basis.prod_repr_inl, Basis.prod_repr_inr]
  rw [hc, Matrix.fromBlocks_add]
  simp

/-- **Spectrum factorization of the separation-principle block operator.** The
characteristic polynomial of `[[T, K], [0, S]]` is the product of the
characteristic polynomials of `T` and `S`. Consequently the complex spectrum of
the block operator is the union of the spectra of the diagonal blocks. -/
theorem charpoly_blockOperator (T K S : X →ₗ[ℝ] X) :
    (blockOperator T K S).charpoly = T.charpoly * S.charpoly := by
  let b : Basis (Fin (Module.finrank ℝ X)) ℝ X := Module.finBasis ℝ X
  rw [← LinearMap.charpoly_toMatrix (f := T) b,
    ← LinearMap.charpoly_toMatrix (f := S) b,
    ← LinearMap.charpoly_toMatrix (f := blockOperator T K S) (b.prod b),
    toMatrix_blockOperator b T K S]
  exact Matrix.charpoly_fromBlocks_zero₂₁
    (R := ℝ) (m := Fin (Module.finrank ℝ X)) (n := Fin (Module.finrank ℝ X))
    (M₁₁ := LinearMap.toMatrix b b T) (M₁₂ := LinearMap.toMatrix b b K)
    (M₂₂ := LinearMap.toMatrix b b S)

/-- **Hurwitzness of the separation-principle block operator.** If both diagonal
blocks are Hurwitz then so is the assembled block operator, because every complex
root of its characteristic polynomial is a root of one of the two factors. -/
theorem isHurwitz_blockOperator (T K S : X →ₗ[ℝ] X)
    (hT : IsHurwitz T) (hS : IsHurwitz S) :
    IsHurwitz (blockOperator T K S) := by
  intro z hz
  rw [charpoly_blockOperator] at hz
  rw [Polynomial.map_mul, Polynomial.eval_mul] at hz
  rcases mul_eq_zero.mp hz with h | h
  · exact hT z h
  · exact hS z h

end Separation

section SeparationPrinciple

variable {X U Y : Type*}
variable [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]
variable [AddCommGroup U] [Module ℝ U]
variable [AddCommGroup Y] [Module ℝ Y]

/-- **Separation principle: the closed loop is Hurwitz.** If `F` stabilizes the
state map (`A + B F` Hurwitz) and `L` stabilizes the observer error
(`A - L C` Hurwitz), then the assembled block operator
`[[A + B F, B F], [0, A - L C]]` of the observer-based controller is Hurwitz. -/
theorem isHurwitz_separationOperator
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (C : X →ₗ[ℝ] Y)
    (F : X →ₗ[ℝ] U) (L : Y →ₗ[ℝ] X)
    (hT : IsHurwitz (A + B.comp F)) (hS : IsHurwitz (A - L.comp C)) :
    IsHurwitz (blockOperator (A + B.comp F) (B.comp F) (A - L.comp C)) :=
  isHurwitz_blockOperator _ _ _ hT hS

/-- **Existence form of the separation principle.** A stabilizable and
detectable system admits a state-feedback gain `F` and an output-injection gain
`L` for which the assembled closed-loop block operator is Hurwitz. The gains are
produced by the stabilization and detection theorems; the block spectrum is then
derived from `charpoly_blockOperator`. -/
theorem exists_separation_block_hurwitz
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (C : X →ₗ[ℝ] Y)
    (hst : IsStabilizable A B) (hdet : IsDetectable C A) :
    ∃ (F : X →ₗ[ℝ] U) (L : Y →ₗ[ℝ] X),
      IsHurwitz (blockOperator (A + B.comp F) (B.comp F) (A - L.comp C)) := by
  obtain ⟨F, hF⟩ := hst
  obtain ⟨L, hL⟩ := hdet
  exact ⟨F, L, isHurwitz_separationOperator A B C F L hF hL⟩

end SeparationPrinciple

/-! ## Converse criteria: unobservable and uncontrollable eigenvalues

The necessity directions of Theorems 3.32 and 3.38 are curvature-free: an
unobservable eigenvalue of `(C, A)` is an eigenvalue of `A - L C` for *every*
output injection `L`, and dually an uncontrollable eigenvalue of `(A, B)` is an
eigenvalue of `A + B F` for *every* state feedback `F`. Hence a stabilizable or
detectable pair can have no such eigenvalue in the closed right half-plane.

Because the state map is real, the eigenvalues live in `ℂ` and the
eigenvectors live in the complexification `ℂ ⊗[ℝ] X`; the bridge from the
complexified eigenvector to the real characteristic polynomial is the base
change formula `LinearMap.charpoly_baseChange`. -/

section EigenvalueConverse

open scoped TensorProduct

/-- An **unobservable eigenvalue** of a real pair `(C, A)`: a complex number `λ`
with a nonzero complexified state that is a `λ`-eigenvector of the complexified
state map and lies in the kernel of the complexified readout. These are exactly
the eigenvalues excluded by the PBH observability criterion
(Trentelman–Stoorvogel–Hautus, Definition 3.12 and condition (3.14)). -/
def IsUnobservableEigenvalue (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) (μ : ℂ) : Prop :=
  ∃ v : ℂ ⊗[ℝ] X, v ≠ 0 ∧ (A.baseChange ℂ) v = μ • v ∧ (C.baseChange ℂ) v = 0

omit [FiniteDimensional ℝ Y] in
/-- **Detectability excludes unobservable eigenvalues in the closed right
half-plane.** If `(C, A)` is detectable — some output injection `L` makes
`A - L C` Hurwitz — then every unobservable eigenvalue has negative real part.
This is the necessity direction of Trentelman–Stoorvogel–Hautus Theorem 3.38:
an unobservable eigenvalue is an eigenvalue of `A - L C` for *every* output
injection `L`, so output injection cannot move it. -/
theorem isDetectable_converse_of_unobservableEigenvalue
    (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) (h : IsDetectable C A)
    {μ : ℂ} (hμ : IsUnobservableEigenvalue C A μ) : μ.re < 0 := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨v, hv, hAv, hCv⟩ := hμ
  have hbc : (A - L.comp C).baseChange ℂ v = μ • v := by
    have hsub : (A - L.comp C).baseChange ℂ =
        A.baseChange ℂ - (L.comp C).baseChange ℂ :=
      map_sub (Module.End.baseChangeHom ℝ ℂ X) A (L.comp C)
    have hmul : (L.comp C).baseChange ℂ =
        (L.baseChange ℂ).comp (C.baseChange ℂ) :=
      LinearMap.baseChange_comp C L
    rw [hsub, hmul, LinearMap.sub_apply, LinearMap.comp_apply, hCv, map_zero, sub_zero,
      hAv]
  have heig : Module.End.HasEigenvalue ((A - L.comp C).baseChange ℂ) μ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr hbc, hv⟩)
  have hroot : ((A - L.comp C).baseChange ℂ).charpoly.IsRoot μ :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp heig
  rw [LinearMap.charpoly_baseChange] at hroot
  exact hL μ hroot

end EigenvalueConverse

/-! ## Converse criterion for stabilizability

Dually, a stabilizing state feedback cannot move an uncontrollable eigenvalue.
The left eigenvector is a functional on the complexification, so the argument
goes through the dual operator and the invariance of the characteristic
polynomial under transposition. -/

section UncontrollableEigenvalue

open scoped TensorProduct

/-- An **uncontrollable eigenvalue** of the real pair `(A, B)`: a complex number
`μ` together with a nonzero complexified left eigenvector of the complexified
state map that annihilates the range of the complexified input map. This is the
eigenvector form of the PBH controllability obstruction
(Trentelman–Stoorvogel–Hautus, Definition 3.12, equivalently
`range (A - μI) ⊔ range B ≠ ⊤`). -/
def IsUncontrollableEigenvalue (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (μ : ℂ) : Prop :=
  ∃ η : (ℂ ⊗[ℝ] X) →ₗ[ℂ] ℂ,
    η ≠ 0 ∧ η.comp (A.baseChange ℂ) = μ • η ∧ η.comp (B.baseChange ℂ) = 0

/-- Over any field, the characteristic polynomial of the algebraic transpose
equals that of the original endomorphism. This is the general form of
`charpoly_dualMap` (which is the real case used for detectability). -/
theorem charpoly_dualMap_ofField {𝕜 M : Type*} [Field 𝕜] [AddCommGroup M] [Module 𝕜 M]
    [FiniteDimensional 𝕜 M] (T : M →ₗ[𝕜] M) :
    T.dualMap.charpoly = T.charpoly := by
  classical
  let b : Module.Basis (Fin (Module.finrank 𝕜 M)) 𝕜 M := Module.finBasis 𝕜 M
  rw [← LinearMap.charpoly_toMatrix (f := T.dualMap) b.dualBasis,
      ← LinearMap.charpoly_toMatrix (f := T) b]
  rw [LinearMap.dualMap_def, LinearMap.toMatrix_transpose]
  exact Matrix.charpoly_transpose _

/-- **Stabilizability excludes uncontrollable eigenvalues in the closed right
half-plane.** If `(A, B)` is stabilizable — some state feedback `F` makes
`A + B F` Hurwitz — then every uncontrollable eigenvalue has negative real part.
This is the necessity direction of Trentelman–Stoorvogel–Hautus Theorem 3.32
(their Corollary 3.30): an uncontrollable left eigenvector of `A` annihilated by
`B` is a left eigenvector of `A + B F` for *every* `F`, so no state feedback can
move the eigenvalue. -/
theorem isStabilizable_converse_of_uncontrollableEigenvalue
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) (h : IsStabilizable A B)
    {μ : ℂ} (hμ : IsUncontrollableEigenvalue A B μ) : μ.re < 0 := by
  obtain ⟨F, hF⟩ := h
  obtain ⟨η, hη, hAη, hBη⟩ := hμ
  have hT : η.comp ((A + B.comp F).baseChange ℂ) = μ • η := by
    have hbase : (A + B.comp F).baseChange ℂ =
        A.baseChange ℂ + (B.comp F).baseChange ℂ :=
      map_add (Module.End.baseChangeHom ℝ ℂ X) A (B.comp F)
    have hcomp : (B.comp F).baseChange ℂ =
        (B.baseChange ℂ).comp (F.baseChange ℂ) :=
      LinearMap.baseChange_comp F B
    rw [hbase, hcomp, LinearMap.comp_add, hAη, ← LinearMap.comp_assoc, hBη,
      LinearMap.zero_comp]
    simp
  have heig : Module.End.HasEigenvalue ((A + B.comp F).baseChange ℂ).dualMap μ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr (by
          rw [LinearMap.dualMap_apply']
          exact hT), hη⟩)
  have hroot : (((A + B.comp F).baseChange ℂ).dualMap).charpoly.IsRoot μ :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp heig
  rw [charpoly_dualMap_ofField] at hroot
  rw [LinearMap.charpoly_baseChange] at hroot
  exact hF μ hroot

end UncontrollableEigenvalue

/-! ## The general Hurwitz-to-decay bridge: the complex spectral case

The analytic heart of the general bridge: over a finite-dimensional complex
normed space, if every root of the characteristic polynomial of an endomorphism
`f` has negative real part, then every trajectory `t ↦ exp (t • f) x` tends to
zero. The proof decomposes the space into the generalized eigenspaces of `f`
(`Module.End.iSup_maxGenEigenspace_eq_top`, `Submodule.mem_iSup_iff_exists_finset`),
on each of which `f - μ` is nilpotent, so the exponential is a finite
polynomial-times-`exp (t μ)` sum (`exp_nilpotent_apply_eq_sum`), which decays
because `μ.re < 0`.

This is the hard analytic half of the general Hurwitz-to-decay bridge. The
remaining step is the *real reduction*: for a real endomorphism `A` on a
finite-dimensional real normed space, complexify `A` (e.g. transport `A` to
`Fin n → ℂ` along a real basis and apply `tendsto_exp_complex_apply`), then
transport the convergence back along the basis isomorphism using the relation
`exp (t • A) = repr.symm ∘ exp (t • repr.conj A) ∘ repr`. The requested
real theorems `LinearMap.tendsto_exp_of_isHurwitz` and
`LinearMap.isStableOn_expFlow_of_isHurwitz` are exactly that reduction; the
complex lemma below is the reusable core they build on. -/

section ComplexHurwitzDecay


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- For `a < 0` the polynomial-times-exponential function
`t ↦ t ^ j * Real.exp (a * t)` tends to zero at `+∞`. This is the scalar engine
behind the decay of each finite exponential-series term. -/
lemma tendsto_pow_mul_exp_of_neg (a : ℝ) (ha : a < 0) (j : ℕ) :
    Tendsto (fun t : ℝ => t ^ j * Real.exp (a * t)) atTop (𝓝 0) := by
  have hc : 0 < -a := neg_pos.mpr ha
  have hcomp : Tendsto (fun t : ℝ => ((-a) * t) ^ j * Real.exp (-((-a) * t))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero j).comp
      ((tendsto_const_mul_atTop_of_pos hc).mpr tendsto_id)
  have hfun : (fun t : ℝ => ((-a) * t) ^ j * Real.exp (-((-a) * t))) =
      fun t : ℝ => (-a)^j * (t ^ j * Real.exp (a * t)) := by
    funext t
    rw [mul_pow]
    have : -((-a) * t) = a * t := by ring
    rw [this]; ring_nf
  rw [hfun] at hcomp
  have h3 := hcomp.const_mul (((-a)^j)⁻¹)
  rw [mul_zero] at h3
  simpa only [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero j (ne_of_gt hc)), one_mul] using h3

/-- The complex form of the scalar decay: if `μ.re < 0`, then
`t ↦ Complex.exp (t * μ) * (t : ℂ) ^ j` tends to zero at `+∞`. -/
lemma tendsto_exp_mul_pow (μ : ℂ) (hμ : μ.re < 0) (j : ℕ) :
    Tendsto (fun t : ℝ => Complex.exp (t * μ) * (t : ℂ) ^ j) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h1 : (fun t : ℝ => ‖Complex.exp (t * μ) * (t : ℂ) ^ j‖) =ᶠ[atTop]
      fun t : ℝ => t ^ j * Real.exp (μ.re * t) := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    have hnorm : ‖(t : ℂ)‖ = |t| := RCLike.norm_ofReal t
    rw [norm_mul, Complex.norm_exp, norm_pow, hnorm, abs_of_nonneg ht]
    have hre : (t * μ).re = t * μ.re := by simp [Complex.mul_re]
    rw [hre, mul_comm t μ.re]; ring
  exact (tendsto_pow_mul_exp_of_neg μ.re hμ j).congr' h1.symm

/-- A nilpotent continuous endomorphism has a finite exponential series: if
`N ^ n = 0`, then `exp (t • N) x = ∑_{k < n} (k!)⁻¹ • ((t • N) ^ k) x`. -/
lemma exp_nilpotent_apply_eq_sum (N : E →L[ℂ] E) {x : E} {n : ℕ}
    (hN : (N ^ n) x = 0) (t : ℝ) :
    NormedSpace.exp (t • N) x =
      ∑ k ∈ Finset.range n, ((k.factorial : ℂ)⁻¹) • ((t • N) ^ k) x := by
  have hsumm : Summable (fun k : ℕ => ((k.factorial : ℂ)⁻¹) • (t • N) ^ k) :=
    NormedSpace.expSeries_summable' (t • N)
  have h1 : NormedSpace.exp (t • N) x =
      (∑' (k : ℕ), ((k.factorial : ℂ)⁻¹) • (t • N) ^ k) x := by
    rw [NormedSpace.exp_eq_tsum ℂ]
  have h2 : (∑' (k : ℕ), ((k.factorial : ℂ)⁻¹) • (t • N) ^ k) x =
      ∑' (k : ℕ), ((k.factorial : ℂ)⁻¹) • ((t • N) ^ k) x := by
    simpa [ContinuousLinearMap.apply_apply] using
      ContinuousLinearMap.map_tsum (ContinuousLinearMap.apply ℂ E x) hsumm
  rw [h1, h2]
  rw [tsum_eq_sum (s := Finset.range n)]
  intro k hk
  rw [Finset.mem_range, not_lt] at hk
  have hNk : (N ^ k) x = 0 := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk
    rw [hd, show n + d = d + n by omega, pow_add, mul_apply_eq_comp, hN, map_zero]
  rw [smul_pow, _root_.smul_apply, hNk, smul_zero, smul_zero]

/-- **Decay of a single generalized eigenspace.** If `x` is annihilated by a
power of `f - μ • 1` and `μ.re < 0`, then `t ↦ exp (t • f) x` tends to zero.
Writing `f = μ + N` with `N` nilpotent, the exponential is `exp (t μ)` times a
polynomial in `t`, which decays by `tendsto_exp_mul_pow`. -/
lemma tendsto_exp_apply_of_nilpotent (f : E →ₗ[ℂ] E) (μ : ℂ) (hμ : μ.re < 0)
    {x : E} {k : ℕ} (hk : ((f - μ • (1 : E →ₗ[ℂ] E)) ^ k) x = 0) :
    Tendsto (fun t : ℝ => NormedSpace.exp (t • f.toContinuousLinearMap) x) atTop (𝓝 0) := by
  set N : E →L[ℂ] E := f.toContinuousLinearMap - μ • (1 : E →L[ℂ] E) with hN
  have hcoe : (N : E →ₗ[ℂ] E) = f - μ • (1 : E →ₗ[ℂ] E) := by
    ext y; simp [hN]
  have hNx : (N ^ k) x = 0 := by
    change ((N ^ k : E →L[ℂ] E) : E →ₗ[ℂ] E) x = 0
    rw [ContinuousLinearMap.toLinearMap_pow, hcoe]
    exact hk
  have hexpscalar : ∀ t : ℝ, NormedSpace.exp ((t * μ) • (1 : E →L[ℂ] E)) =
      Complex.exp (t * μ) • (1 : E →L[ℂ] E) := by
    intro t
    rw [← Algebra.algebraMap_eq_smul_one (t * μ), ← NormedSpace.algebraMap_exp_comm (t * μ),
      show NormedSpace.exp (t * μ) = Complex.exp (t * μ) from
        (congrFun Complex.exp_eq_exp_ℂ (t * μ)).symm,
      Algebra.algebraMap_eq_smul_one]
  have hdecomp : (fun t : ℝ => NormedSpace.exp (t • f.toContinuousLinearMap) x) =
      fun (t : ℝ) => Complex.exp (t * μ) •
        (∑ j ∈ Finset.range k, ((j.factorial : ℂ)⁻¹) • ((t • N) ^ j) x) := by
    funext t
    have hsplit : t • f.toContinuousLinearMap =
        (t * μ) • (1 : E →L[ℂ] E) + t • N := by
      rw [hN]; module
    rw [hsplit, NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)]
    · rw [mul_apply_eq_comp, hexpscalar t, exp_nilpotent_apply_eq_sum N hNx t]
      rw [_root_.smul_apply, one_apply_eq_self, Finset.smul_sum]
    · rw [← Algebra.algebraMap_eq_smul_one (t * μ)]
      exact Algebra.commute_algebraMap_left (t * μ) (t • N)
    · exact (NormedSpace.expSeries_radius_eq_top ℂ (E →L[ℂ] E)).symm ▸ edist_lt_top _ _
    · exact (NormedSpace.expSeries_radius_eq_top ℂ (E →L[ℂ] E)).symm ▸ edist_lt_top _ _
  rw [hdecomp]
  have hterm : ∀ j ∈ Finset.range k,
      Tendsto (fun t : ℝ => Complex.exp (t * μ) •
        (((j.factorial : ℂ)⁻¹) • ((t • N) ^ j) x)) atTop (𝓝 0) := by
    intro j _
    have hscalar : Tendsto (fun t : ℝ => Complex.exp (t * μ) * (t : ℂ) ^ j) atTop (𝓝 0) :=
      tendsto_exp_mul_pow μ hμ j
    have hpow : (fun t : ℝ => Complex.exp (t * μ) •
          (((j.factorial : ℂ)⁻¹) • ((t • N) ^ j) x)) =
        fun (t : ℝ) => (Complex.exp (t * μ) * (t : ℂ) ^ j * ((j.factorial : ℂ)⁻¹)) •
          (N ^ j) x := by
      funext t
      rw [smul_pow, _root_.smul_apply, smul_smul]
      module
    rw [hpow]
    have := (hscalar.mul_const ((j.factorial : ℂ)⁻¹)).smul_const ((N ^ j) x)
    simpa [mul_assoc] using this
  have hgoal : (fun t : ℝ => Complex.exp (t * μ) •
        (∑ j ∈ Finset.range k, ((j.factorial : ℂ)⁻¹) • ((t • N) ^ j) x)) =
      fun (t : ℝ) => ∑ j ∈ Finset.range k, Complex.exp (t * μ) •
        (((j.factorial : ℂ)⁻¹) • ((t • N) ^ j) x) := by
    funext t; rw [Finset.smul_sum]
  rw [hgoal]
  simpa using tendsto_finsetSum (Finset.range k) hterm

omit [FiniteDimensional ℂ E] in
/-- A nonzero vector in the generalized eigenspace of `f` at `μ` exhibits `μ` as
an eigenvalue of `f`: `f - μ • 1` cannot be injective on a nonzero element of its
eventual kernel. -/
lemma hasEigenvalue_of_mem_maxGenEigenspace {f : E →ₗ[ℂ] E} {μ : ℂ} {x : E}
    (hx : x ∈ Module.End.maxGenEigenspace f μ) (hx0 : x ≠ 0) :
    Module.End.HasEigenvalue f μ := by
  rw [Module.End.HasEigenvalue, Module.End.HasUnifEigenvalue, Module.End.genEigenspace_one]
  intro h
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace f μ x).mp hx
  have hinj : Function.Injective (f - μ • (1 : E →ₗ[ℂ] E)) := LinearMap.ker_eq_bot.mp h
  have hker : ∀ n, ∀ y, ((f - μ • (1 : E →ₗ[ℂ] E)) ^ n) y = 0 → y = 0 := by
    intro n
    induction n with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
      intro y hy
      rw [pow_succ] at hy
      change ((f - μ • (1 : E →ₗ[ℂ] E)) ^ n) ((f - μ • (1 : E →ₗ[ℂ] E)) y) = 0 at hy
      have hay : (f - μ • (1 : E →ₗ[ℂ] E)) y = 0 := ih _ hy
      exact hinj (by rw [hay, map_zero])
  exact hx0 (hker k x hk)

/-- **The complex Hurwitz decay theorem.** Let `f` be an endomorphism of a
finite-dimensional complex normed space all of whose characteristic roots have
negative real part. Then every orbit `t ↦ exp (t • f) x` of the linear flow
tends to zero at `+∞`.

The proof decomposes the space into the generalized eigenspaces of `f`
(`Module.End.iSup_maxGenEigenspace_eq_top`), on each of which `f - μ` is
nilpotent, so `exp (t • f)` is a finite polynomial-times-`exp (t μ)` sum that
decays because `Re μ < 0`.

This is the reusable complex core of the general Hurwitz-to-decay bridge. The
real case is recovered by complexification and change of coordinates; that
reduction is deliberately *not* claimed here (see the module documentation). -/
theorem tendsto_exp_complex_apply (f : E →ₗ[ℂ] E)
    (hf : ∀ z : ℂ, f.charpoly.eval z = 0 → z.re < 0) (x : E) :
    Tendsto (fun t : ℝ => NormedSpace.exp (t • f.toContinuousLinearMap) x) atTop (𝓝 0) := by
  have htop : x ∈ ⨆ μ : ℂ, Module.End.maxGenEigenspace f μ := by
    rw [Module.End.iSup_maxGenEigenspace_eq_top]; exact Submodule.mem_top
  obtain ⟨s, hs⟩ := (Submodule.mem_iSup_iff_exists_finset
    (p := fun μ : ℂ => Module.End.maxGenEigenspace f μ)).mp htop
  obtain ⟨xμ, hxμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum
    (fun μ : ℂ => Module.End.maxGenEigenspace f μ) x).mp hs
  have hsum : x = ∑ μ ∈ s, (xμ μ : E) := hxμ.symm
  rw [hsum]
  have hmap : (fun t : ℝ => NormedSpace.exp (t • f.toContinuousLinearMap)
        (∑ μ ∈ s, (xμ μ : E))) =
      fun t => ∑ μ ∈ s, NormedSpace.exp (t • f.toContinuousLinearMap) (xμ μ : E) := by
    funext t; rw [map_sum]
  rw [hmap]
  have hfin0 := tendsto_finsetSum (x := atTop) s
      (f := fun (μ : ℂ) (t : ℝ) => NormedSpace.exp (t • f.toContinuousLinearMap) (xμ μ : E))
      (a := fun _ : ℂ => (0 : E))
      (fun μ _ => by
        by_cases hx0 : (xμ μ : E) = 0
        · rw [hx0]
          convert tendsto_const_nhds using 1
          simp
        · have heig : Module.End.HasEigenvalue f μ :=
            hasEigenvalue_of_mem_maxGenEigenspace (xμ μ).2 hx0
          have hroot : f.charpoly.eval μ = 0 :=
            Polynomial.IsRoot.def.mp ((Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).mp heig)
          have hre : μ.re < 0 := hf μ hroot
          obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace f μ (xμ μ)).mp (xμ μ).2
          exact tendsto_exp_apply_of_nilpotent f μ hre hk)
  simpa using hfin0

end ComplexHurwitzDecay

end LinearMap
