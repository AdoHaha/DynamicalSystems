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
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Dual.BaseChange
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

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
* `LinearMap.tendsto_exp_complex_apply`: the complex generalized-eigenspace
  decay theorem, and its real reduction
  `LinearMap.tendsto_exp_of_isHurwitz` with the Lyapunov-stability companion
  `LinearMap.isStableOn_expFlow_of_isHurwitz`.

The explicit-target bridge above is what the gain constructions realise. The
*general* spectral theorem "`IsHurwitz A` ⇒ every trajectory of `x' = A x`
decays" is also proved in this file, by the complex generalized-eigenspace
argument `LinearMap.tendsto_exp_complex_apply` followed by a real-coordinate
reduction (`LinearMap.tendsto_exp_of_isHurwitz`,
`LinearMap.isStableOn_expFlow_of_isHurwitz`).

## The Hurwitz (stable) subspace

* `LinearMap.hurwitzSubspace`: the finite-dimensional real stable subspace
  `X_g(A)` — the real form of the sum of the complex generalized eigenspaces of
  `A` at the eigenvalues with negative real part, transported to the state space
  through the canonical real basis and `ofRealPi`.
* `LinearMap.map_hurwitzSubspace_le`: the stable subspace is `A`-invariant.
* `LinearMap.tendsto_exp_restrict_hurwitzSubspace`: the exponential flow of `A`
  decays to zero on the stable subspace, reusing the generalized-eigenspace
  decay engine behind `exists_exponential_norm_bound_of_isHurwitz`.
* `LinearMap.hurwitzSubspace_eq_top_of_subsingleton`: in the zero-dimensional
  case the stable subspace is the whole space.
* `LinearMap.hurwitzSubspace_zero`: the zero operator has trivial stable
  subspace, since its only eigenvalue `0` is not in the open left half-plane.

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

## Completed bridges and remaining scope

The general finite-dimensional Hurwitz theorem is now formalized:
`LinearMap.tendsto_exp_of_isHurwitz` gives exponential-flow attractivity and
`LinearMap.isStableOn_expFlow_of_isHurwitz` gives Lyapunov stability. The proof
uses the complex generalized-eigenspace theorem
`LinearMap.tendsto_exp_complex_apply` and a real-coordinate reduction. The
quantitative operator-norm bound `‖exp (t A)‖ ≤ C * exp (-γ * t)` is
`LinearMap.exists_exponential_norm_bound_of_isHurwitz`, obtained from the
operator-norm convergence `LinearMap.tendsto_norm_exp_of_isHurwitz` and the
gometric step `LinearMap.norm_exp_le_mul_pow_floor`.

The degree-zero case of the Bohl exponential-polynomial independence used by the
antistable readout argument is also provided here:
`LinearMap.tendsto_inv_mul_geom_sum` computes the Cesàro average of a
unit-modulus geometric progression, and `LinearMap.tendsto_zero_of_sum_pow_smul`
shows that a finite sum of distinct unit-modulus characters with coefficients in
a complex normed space cannot tend to zero unless every coefficient vanishes.
This is the cancellation argument at the heart of the spectral readout lemma.

The polynomial-exponential reduction on top of it is now formalised as well.
`LinearMap.tendsto_zero_of_sum_pow_smul_polynomial` extends the accepted
character lemma to polynomial coefficients by inducting on the degree;
`LinearMap.tendsto_zero_of_sum_exp_polynomial_re_zero` transfers it to the
continuous characters `exp (t * μ i)` with purely imaginary modes; and
`LinearMap.tendsto_zero_of_sum_exp_polynomial` proves the general
`Re μ i ≥ 0` form by factoring out the dominant real part and inducting on the
number of modes. Thus a finite sum of vector-valued polynomial terms times
`exp (t * μ)`, with `Re μ ≥ 0`, that tends to zero at `+∞` has all coefficients
zero. The transport to the antistable readout (`H (e^{tA} x)`) remains the next
step recorded in `DynamicalSystems.Linear.DynamicFeedback`.

The PBH criteria are complete in both directions. The necessity results
`LinearMap.isStabilizable_converse_of_uncontrollableEigenvalue` and
`LinearMap.isDetectable_converse_of_unobservableEigenvalue`, together with
`LinearMap.isStabilizable_of_uncontrollableEigenvalues_hurwitz` and
`LinearMap.isDetectable_of_unobservableEigenvalues_hurwitz`, establish the
stabilizability/detectability equivalences via Kalman complements and pole
placement. Remaining follow-up scope concerns transfer functions, not these
static criteria.

## Invariant-submodule restriction and quotient spectra

The restriction/quotient spectrum bridge is formalized in
`LinearMap.charpoly_restrict_of_invariant`: for an `A`-invariant submodule `V`,
`A.charpoly = (A|_V).charpoly * (A|_{X/V}).charpoly`, where the quotient factor
is the existing Mathlib map `Submodule.mapQ V V A`. The spectrum-transfer form
`LinearMap.charpoly_restrict_dvd_of_invariant` records the divisibility
`(A|_V).charpoly ∣ A.charpoly`, and the edge cases `V = ⊤` and `V = ⊥` are
`LinearMap.charpoly_restrict_top` and `LinearMap.charpoly_restrict_bot`. Finally,
`LinearMap.isHurwitz_restrict_of_hurwitzSubspace` moves `IsHurwitz` from `A` to
its restriction on the stable subspace `hurwitzSubspace A`, which is the
invariant-submodule half of the lift into stabilizable/detectable
decompositions. No new quotient-spectrum API is introduced.

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

/-- **The exponential power series, evaluated pointwise.** For a complete normed
space `E` over a complete normed field `𝕜` and a continuous endomorphism `A`,
applying `exp (t • A)` to a vector expands as the factorial series
`∑ n, ((n !)⁻¹ : 𝕜) • ((t • A) ^ n x)`.

This is the shared transport step behind the exponential push-forward and the
nilpotent series: `NormedSpace.exp_eq_tsum` expands the exponential as an
operator-valued sum and `ContinuousLinearMap.map_tsum` moves the
evaluation-at-`x` map through it. -/
theorem exp_smul_apply_eq_tsum
    {𝕜 : Type*} [RCLike 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (A : E →L[𝕜] E) (t : 𝕜) (x : E) :
    NormedSpace.exp (t • A) x =
      ∑' n : ℕ, ((n.factorial : 𝕜)⁻¹) • (((t • A) ^ n) x) := by
  conv_lhs => rw [NormedSpace.exp_eq_tsum 𝕜]
  change ((ContinuousLinearMap.apply 𝕜 E x)
    (∑' n : ℕ, ((n.factorial : 𝕜)⁻¹) • (t • A) ^ n)) = _
  rw [ContinuousLinearMap.map_tsum]
  · apply tsum_congr
    intro n
    rw [map_smul, ContinuousLinearMap.apply_apply]
  · exact NormedSpace.expSeries_summable_of_mem_ball' (t • A)
      ((NormedSpace.expSeries_radius_eq_top 𝕜 (E →L[𝕜] E)).symm ▸ edist_lt_top _ _)

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

This section transfers the algebraic characteristic-polynomial identity
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

/-! ## The converse PBH criteria: gain existence

The necessity halves of the PBH criteria were proved above: a stabilizing
gain cannot move an uncontrollable eigenvalue, and an output injection cannot
move an unobservable eigenvalue. This section proves the *sufficiency* halves
of Trentelman–Stoorvogel–Hautus Theorem 3.32 and Theorem 3.38: if every
uncontrollable eigenvalue is already Hurwitz then a stabilizing state feedback
exists, and dually for detectability.

The construction chooses a complement `Q` of the reachable subspace `W`,
applies multi-input pole placement to the controllable restriction
`(A|_W, B|_W)`, and leaves the unreachable block untouched. The
characteristic polynomial of the closed loop is the product of the two block
characteristic polynomials (`charpoly_prodMap_of_lower_zero`), and the
hypothesis on uncontrollable eigenvalues supplies the Hurwitz property of the
unreachable block. The detectability statement is the dual construction with a
complement of the unobservable subspace. -/

section ConversePBH

open scoped TensorProduct

/-- **Characteristic polynomial of a block upper-triangular operator.** On a
product `W × Q`, the operator `(w, q) ↦ (f w + k q, g q)` has characteristic
polynomial `f.charpoly * g.charpoly`. This is the algebraic form of the
two-block Kalman decomposition used to combine the controllable and
uncontrollable parts of a system. -/
theorem charpoly_prodMap_of_lower_zero {W Q : Type*}
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    [AddCommGroup Q] [Module ℝ Q] [FiniteDimensional ℝ Q]
    (f : W →ₗ[ℝ] W) (g : Q →ₗ[ℝ] Q) (k : Q →ₗ[ℝ] W) :
    (LinearMap.prod ((f.comp (LinearMap.fst ℝ W Q)) + (k.comp (LinearMap.snd ℝ W Q)))
      (g.comp (LinearMap.snd ℝ W Q))).charpoly = f.charpoly * g.charpoly := by
  classical
  let bW : Module.Basis (Fin (Module.finrank ℝ W)) ℝ W := Module.finBasis ℝ W
  let bQ : Module.Basis (Fin (Module.finrank ℝ Q)) ℝ Q := Module.finBasis ℝ Q
  let b := bW.prod bQ
  let T : W × Q →ₗ[ℝ] W × Q := LinearMap.prod
    ((f.comp (LinearMap.fst ℝ W Q)) + (k.comp (LinearMap.snd ℝ W Q)))
    (g.comp (LinearMap.snd ℝ W Q))
  have hmat : LinearMap.toMatrix b b T = Matrix.fromBlocks (LinearMap.toMatrix bW bW f)
      (LinearMap.toMatrix bQ bW k) 0 (LinearMap.toMatrix bQ bQ g) := by
    ext i j
    rcases i with a | b' <;> rcases j with c | d
    · simp [b, T, LinearMap.toMatrix_apply, Module.Basis.prod_repr_inl]
    · simp [b, T, LinearMap.toMatrix_apply, Module.Basis.prod_repr_inl]
    · simp [b, T, LinearMap.toMatrix_apply, Module.Basis.prod_repr_inr]
    · simp [b, T, LinearMap.toMatrix_apply, Module.Basis.prod_repr_inr]
  rw [← LinearMap.charpoly_toMatrix (f := T) b, hmat, Matrix.charpoly_fromBlocks_zero₂₁,
    LinearMap.charpoly_toMatrix (f := f) bW, LinearMap.charpoly_toMatrix (f := g) bQ]


/-- **Sufficiency of the PBH stabilizability criterion.** If every
uncontrollable eigenvalue of `(A, B)` has negative real part, then there is a
state feedback `F` with `A + B.comp F` Hurwitz. The feedback is constructed, not
assumed: pole placement stabilises the controllable restriction of `(A, B)`
while the complement block is already Hurwitz by hypothesis.

Source: Trentelman–Stoorvogel–Hautus, Theorem 3.32 (the `⇐` direction). -/
theorem isStabilizable_of_uncontrollableEigenvalues_hurwitz
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (h : ∀ μ : ℂ, IsUncontrollableEigenvalue A B μ → μ.re < 0) :
    IsStabilizable A B := by
  classical
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl (reachableSubspace A B)
  let W := reachableSubspace A B
  let πW : X →ₗ[ℝ] W := W.projectionOnto Q hQ
  let πQ : X →ₗ[ℝ] Q := Q.projectionOnto W hQ.symm
  let A11 : W →ₗ[ℝ] W := reachableRestrictionA A B
  let B1 : U →ₗ[ℝ] W := reachableRestrictionB A B
  let A12 : Q →ₗ[ℝ] W := πW.comp (A.comp Q.subtype)
  let A22 : Q →ₗ[ℝ] Q := πQ.comp (A.comp Q.subtype)
  have hπWA : ∀ w : W, (W.projectionOnto Q hQ) (A (w : X)) = A11 w := by
    intro w
    have hmem : A (w : X) ∈ W := map_reachableSubspace_le A B ⟨_, w.2, rfl⟩
    rw [show (W.projectionOnto Q hQ) (A (w:X)) = ⟨A (w:X), hmem⟩ from
      Submodule.projectionOnto_apply_of_mem_left hQ hmem]
    apply Subtype.ext
    simp [A11, reachableRestrictionA, LinearMap.restrict_apply]
  have hπWB : ∀ u : U, (W.projectionOnto Q hQ) (B u) = B1 u := by
    intro u
    have hmem : B u ∈ W := range_le_reachableSubspace A B ⟨u, rfl⟩
    rw [show (W.projectionOnto Q hQ) (B u) = ⟨B u, hmem⟩ from
      Submodule.projectionOnto_apply_of_mem_left hQ hmem]
    apply Subtype.ext
    simp [B1, reachableRestrictionB, LinearMap.codRestrict_apply]
  have hπQA : ∀ w : W, (Q.projectionOnto W hQ.symm) (A (w : X)) = 0 := by
    intro w
    rw [Submodule.projectionOnto_apply_eq_zero_iff]
    exact map_reachableSubspace_le A B ⟨_, w.2, rfl⟩
  have hπWw : ∀ w : W, (W.projectionOnto Q hQ) (w : X) = w := by
    intro w
    exact Submodule.projectionOnto_apply_of_mem_left hQ w.2
  have hπWq : ∀ q : Q, (W.projectionOnto Q hQ) (q : X) = 0 := by
    intro q
    exact Submodule.projectionOnto_apply_right hQ q
  have hdecomp : ∀ x : X, ((πW x : X) + (πQ x : X)) = x := by
    intro x
    have hh := Submodule.projection_add_projection_eq_self hQ x
    simpa only [πW, πQ, Submodule.coe_projectionOnto_apply] using hh
  have hπQ_A : πQ.comp A = A22.comp πQ := by
    apply LinearMap.ext
    intro x
    change πQ (A x) = A22 (πQ x)
    calc πQ (A x)
        = πQ (A ((πW x : X) + (πQ x : X))) := by rw [hdecomp]
      _ = πQ (A (πW x : X) + A (πQ x : X)) := by rw [map_add]
      _ = πQ (A (πW x : X)) + πQ (A (πQ x : X)) := by rw [map_add]
      _ = A22 (πQ x) := by
          have hmem : A (πW x : X) ∈ W := map_reachableSubspace_le A B ⟨_, (πW x).2, rfl⟩
          have hz : πQ (A (πW x : X)) = 0 := by
            rw [Submodule.projectionOnto_apply_eq_zero_iff]; exact hmem
          rw [hz, zero_add]; rfl
  have hπQ_B : πQ.comp B = 0 := by
    apply LinearMap.ext
    intro u
    change πQ (B u) = 0
    rw [Submodule.projectionOnto_apply_eq_zero_iff]
    exact range_le_reachableSubspace A B ⟨u, rfl⟩
  have hA22 : IsHurwitz A22 := by
    intro μ hμ
    set A22c : (ℂ ⊗[ℝ] Q) →ₗ[ℂ] (ℂ ⊗[ℝ] Q) := A22.baseChange ℂ with hA22c
    have hchar : A22c.charpoly = A22.charpoly.map (algebraMap ℝ ℂ) :=
      LinearMap.charpoly_baseChange A22 ℂ
    have hroot : A22c.charpoly.IsRoot μ := by rw [hchar]; exact hμ
    have hroot' : A22c.dualMap.charpoly.IsRoot μ := by
      rw [charpoly_dualMap_ofField]; exact hroot
    have heig : Module.End.HasEigenvalue A22c.dualMap μ :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly A22c.dualMap μ).mpr hroot'
    obtain ⟨ξ, hξ⟩ := heig.exists_hasEigenvector
    have hξne : ξ ≠ 0 := hξ.2
    have hξeig : A22c.dualMap ξ = μ • ξ := Module.End.mem_eigenspace_iff.mp hξ.1
    have hξcomp : ξ.comp A22c = μ • ξ := by
      apply LinearMap.ext
      intro v
      change ξ (A22c v) = (μ • ξ) v
      have hh := congrArg (fun (f : (ℂ ⊗[ℝ] Q) →ₗ[ℂ] ℂ) => f v) hξeig
      simpa [LinearMap.dualMap_apply'] using hh
    let η : (ℂ ⊗[ℝ] X) →ₗ[ℂ] ℂ := ξ.comp (πQ.baseChange ℂ)
    have hηne : η ≠ 0 := by
      have hright : (πQ.baseChange ℂ).comp (Q.subtype.baseChange ℂ) = LinearMap.id := by
        rw [← LinearMap.baseChange_comp, Submodule.projectionOnto_comp_subtype,
          LinearMap.baseChange_id]
      have hsurj : Function.Surjective (πQ.baseChange ℂ) := by
        intro y
        exact ⟨(Q.subtype.baseChange ℂ) y, by
          have hh := congrArg (fun f : (ℂ ⊗[ℝ] Q) →ₗ[ℂ] (ℂ ⊗[ℝ] Q) => f y) hright
          simpa using hh⟩
      intro hη0
      apply hξne
      apply LinearMap.ext
      intro y
      change ξ y = 0
      obtain ⟨z, rfl⟩ := hsurj y
      have hz := congrArg (fun f : (ℂ ⊗[ℝ] X) →ₗ[ℂ] ℂ => f z) hη0
      simpa [η, LinearMap.comp_apply] using hz
    have hηA : η.comp (A.baseChange ℂ) = μ • η := by
      have hbase : (πQ.baseChange ℂ).comp (A.baseChange ℂ) =
          (A22.baseChange ℂ).comp (πQ.baseChange ℂ) := by
        have hh := congrArg (fun f : X →ₗ[ℝ] Q => f.baseChange ℂ) hπQ_A
        simpa only [LinearMap.baseChange_comp] using hh
      apply LinearMap.ext
      intro v
      change η ((A.baseChange ℂ) v) = (μ • η) v
      calc η ((A.baseChange ℂ) v)
          = ξ ((πQ.baseChange ℂ) ((A.baseChange ℂ) v)) := rfl
        _ = ξ (((πQ.baseChange ℂ).comp (A.baseChange ℂ)) v) := rfl
        _ = ξ (((A22.baseChange ℂ).comp (πQ.baseChange ℂ)) v) := by rw [hbase]
        _ = ξ ((A22.baseChange ℂ) ((πQ.baseChange ℂ) v)) := rfl
        _ = (ξ.comp (A22.baseChange ℂ)) ((πQ.baseChange ℂ) v) := rfl
        _ = (μ • ξ) ((πQ.baseChange ℂ) v) := by rw [hξcomp]
        _ = (μ • η) v := rfl
    have hηB : η.comp (B.baseChange ℂ) = 0 := by
      have hbase : (πQ.baseChange ℂ).comp (B.baseChange ℂ) = 0 := by
        have hh := congrArg (fun f : U →ₗ[ℝ] Q => f.baseChange ℂ) hπQ_B
        simpa only [LinearMap.baseChange_comp, LinearMap.baseChange_zero] using hh
      rw [show η.comp (B.baseChange ℂ) =
        ξ.comp ((πQ.baseChange ℂ).comp (B.baseChange ℂ)) by rw [LinearMap.comp_assoc]]
      rw [hbase, LinearMap.comp_zero]
    exact h μ ⟨η, hηne, hηA, hηB⟩
  obtain ⟨F1, hF1⟩ := isStabilizable_of_isControllable A11 B1
    (isControllable_reachableRestriction A B)
  refine ⟨F1.comp πW, ?_⟩
  let e := W.prodEquivOfIsCompl Q hQ
  let T' : W × Q →ₗ[ℝ] W × Q := LinearMap.prod
    ((A11 + B1.comp F1).comp (LinearMap.fst ℝ W Q) + A12.comp (LinearMap.snd ℝ W Q))
    (A22.comp (LinearMap.snd ℝ W Q))
  have hconj : e.symm.conj (A + B.comp (F1.comp πW)) = T' := by
    apply LinearMap.ext
    intro p
    obtain ⟨w, q⟩ := p
    rw [LinearEquiv.conj_apply_apply]
    rw [Submodule.prodEquivOfIsCompl_symm_apply]
    rw [LinearEquiv.symm_symm, Submodule.coe_prodEquivOfIsCompl']
    apply Prod.ext
    · apply Subtype.ext
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.prod_apply,
        Function.prod_apply, LinearMap.fst_apply, LinearMap.snd_apply, T']
      rw [show (W.projectionOnto Q hQ) ((w : X) + (q : X)) = w by
        rw [map_add, hπWw w, hπWq q, add_zero]]
      rw [map_add, map_add, map_add]
      rw [hπWA w]
      rw [show (W.projectionOnto Q hQ) (A (q:X)) = A12 q from rfl]
      rw [hπWB (F1 w)]
      abel
    · apply Subtype.ext
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.prod_apply,
        Function.prod_apply, LinearMap.fst_apply, LinearMap.snd_apply, T']
      rw [show (W.projectionOnto Q hQ) ((w : X) + (q : X)) = w by
        rw [map_add, hπWw w, hπWq q, add_zero]]
      rw [map_add, map_add, map_add]
      rw [show (Q.projectionOnto W hQ.symm) (A (w:X)) = 0 from hπQA w]
      rw [show (Q.projectionOnto W hQ.symm) (A (q:X)) = A22 q from rfl]
      rw [show (Q.projectionOnto W hQ.symm) (B (F1 w)) = 0 from by
        rw [Submodule.projectionOnto_apply_eq_zero_iff]
        exact range_le_reachableSubspace A B ⟨_, rfl⟩]
      rw [zero_add, add_zero]
  refine fun μ hμ => ?_
  have hchar : (A + B.comp (F1.comp πW)).charpoly = T'.charpoly := by
    rw [← LinearEquiv.charpoly_conj e.symm (A + B.comp (F1.comp πW)), hconj]
  have hTchar : T'.charpoly = (A11 + B1.comp F1).charpoly * A22.charpoly :=
    charpoly_prodMap_of_lower_zero _ _ _
  rw [hchar, hTchar] at hμ
  simp only [Polynomial.map_mul, Polynomial.eval_mul] at hμ
  rcases mul_eq_zero.mp hμ with h1 | h2
  · exact hF1 μ h1
  · exact hA22 μ h2


/-- **Sufficiency of the PBH detectability criterion.** If every unobservable
eigenvalue of `(C, A)` has negative real part, then there is an output injection
`L` with `A - L.comp C` Hurwitz. This is the dual of
`isStabilizable_of_uncontrollableEigenvalues_hurwitz` and likewise constructs
the gain.

Source: Trentelman–Stoorvogel–Hautus, Theorem 3.38 (the `⇐` direction). -/
theorem isDetectable_of_unobservableEigenvalues_hurwitz
    (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X)
    (h : ∀ μ : ℂ, IsUnobservableEigenvalue C A μ → μ.re < 0) :
    IsDetectable C A := by
  classical
  obtain ⟨P, hP⟩ := Submodule.exists_isCompl (unobservableSubspace C A)
  let N := unobservableSubspace C A
  let πN : X →ₗ[ℝ] N := N.projectionOnto P hP
  let πP : X →ₗ[ℝ] P := P.projectionOnto N hP.symm
  let AN : N →ₗ[ℝ] N := unobservableRestrictionA C A
  let CP : P →ₗ[ℝ] Y := C.comp P.subtype
  let AP : P →ₗ[ℝ] P := πP.comp (A.comp P.subtype)
  let ANP : P →ₗ[ℝ] N := πN.comp (A.comp P.subtype)
  have hsub : A.comp N.subtype = N.subtype.comp AN := by
    apply LinearMap.ext; intro n
    simp [AN, unobservableRestrictionA, LinearMap.restrict_apply]
  have hAN : IsHurwitz AN := by
    intro μ hμ
    set ANc : (ℂ ⊗[ℝ] N) →ₗ[ℂ] (ℂ ⊗[ℝ] N) := AN.baseChange ℂ with hANc
    have hchar : ANc.charpoly = AN.charpoly.map (algebraMap ℝ ℂ) :=
      LinearMap.charpoly_baseChange AN ℂ
    have hroot : ANc.charpoly.IsRoot μ := by rw [hchar]; exact hμ
    have heig : Module.End.HasEigenvalue ANc μ :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly ANc μ).mpr hroot
    obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
    have hvne : v ≠ 0 := hv.2
    have hveig : ANc v = μ • v := Module.End.mem_eigenspace_iff.mp hv.1
    have hleft : (πN.baseChange ℂ).comp (N.subtype.baseChange ℂ) = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, Submodule.projectionOnto_comp_subtype,
        LinearMap.baseChange_id]
    have hinj : Function.Injective (N.subtype.baseChange ℂ) :=
      Function.LeftInverse.injective (g := πN.baseChange ℂ) (fun y => by
        have hh := congrArg (fun f : (ℂ ⊗[ℝ] N) →ₗ[ℂ] (ℂ ⊗[ℝ] N) => f y) hleft
        simpa using hh)
    refine h μ ⟨(N.subtype.baseChange ℂ) v, ?_, ?_, ?_⟩
    · intro hzero; exact hvne (hinj (by rw [hzero, map_zero]))
    · have hcomp : (A.comp N.subtype).baseChange ℂ = (N.subtype.comp AN).baseChange ℂ := by
        rw [hsub]
      calc (A.baseChange ℂ) ((N.subtype.baseChange ℂ) v)
          = ((A.comp N.subtype).baseChange ℂ) v := by
              rw [LinearMap.baseChange_comp]; rfl
        _ = ((N.subtype.comp AN).baseChange ℂ) v := by rw [hcomp]
        _ = (N.subtype.baseChange ℂ) (ANc v) := by
              rw [LinearMap.baseChange_comp]; rfl
        _ = (N.subtype.baseChange ℂ) (μ • v) := by rw [hveig]
        _ = μ • ((N.subtype.baseChange ℂ) v) := by rw [map_smul]
    · have hcomp : (C.comp N.subtype).baseChange ℂ = 0 := by
        rw [unobservableRestrictionA_C_eq_zero, LinearMap.baseChange_zero]
      calc (C.baseChange ℂ) ((N.subtype.baseChange ℂ) v)
          = ((C.comp N.subtype).baseChange ℂ) v := by
              rw [LinearMap.baseChange_comp]; rfl
        _ = 0 := by rw [hcomp, LinearMap.zero_apply]
  have hπNN : ∀ n : N, (N.projectionOnto P hP) (n : X) = n := by
    intro n; exact Submodule.projectionOnto_apply_of_mem_left hP n.2
  have hπNP : ∀ p : P, (N.projectionOnto P hP) (p : X) = 0 := by
    intro p; exact Submodule.projectionOnto_apply_right hP p
  have hπPN : ∀ n : N, (P.projectionOnto N hP.symm) (n : X) = 0 := by
    intro n; exact Submodule.projectionOnto_apply_right hP.symm n
  have hπPP : ∀ p : P, (P.projectionOnto N hP.symm) (p : X) = p := by
    intro p; exact Submodule.projectionOnto_apply_of_mem_left hP.symm p.2
  have hπNA : ∀ n : N, (N.projectionOnto P hP) (A (n : X)) = AN n := by
    intro n
    have hmem : A (n : X) ∈ N := map_unobservableSubspace_le C A ⟨_, n.2, rfl⟩
    rw [show (N.projectionOnto P hP) (A (n:X)) = ⟨A (n:X), hmem⟩ from
      Submodule.projectionOnto_apply_of_mem_left hP hmem]
    apply Subtype.ext
    simp [AN, unobservableRestrictionA, LinearMap.restrict_apply]
  have hπPA : ∀ n : N, (P.projectionOnto N hP.symm) (A (n : X)) = 0 := by
    intro n
    rw [Submodule.projectionOnto_apply_eq_zero_iff]
    exact map_unobservableSubspace_le C A ⟨_, n.2, rfl⟩
  have hπP_A : (P.projectionOnto N hP.symm).comp A = AP.comp (P.projectionOnto N hP.symm) := by
    apply LinearMap.ext; intro x
    change (P.projectionOnto N hP.symm) (A x) = AP ((P.projectionOnto N hP.symm) x)
    have hdecomp : ((πN x : X) + (πP x : X)) = x := by
      have hh := Submodule.projection_add_projection_eq_self hP x
      simpa only [πN, πP, Submodule.coe_projectionOnto_apply] using hh
    calc (P.projectionOnto N hP.symm) (A x)
        = (P.projectionOnto N hP.symm) (A ((πN x : X) + (πP x : X))) := by rw [hdecomp]
      _ = (P.projectionOnto N hP.symm) (A (πN x : X) + A (πP x : X)) := by rw [map_add]
      _ = (P.projectionOnto N hP.symm) (A (πN x : X)) +
            (P.projectionOnto N hP.symm) (A (πP x : X)) := by rw [map_add]
      _ = AP ((P.projectionOnto N hP.symm) x) := by
          have hz : (P.projectionOnto N hP.symm) (A (πN x : X)) = 0 := by
            rw [Submodule.projectionOnto_apply_eq_zero_iff]
            exact map_unobservableSubspace_le C A ⟨_, (πN x).2, rfl⟩
          rw [hz, zero_add]
          rfl
  have hobs : IsObservable CP AP := by
    rw [isObservable_iff, Submodule.eq_bot_iff]
    intro p hp
    rw [mem_unobservableSubspace] at hp
    have hpow : ∀ k, (AP ^ k) p = (P.projectionOnto N hP.symm) ((A ^ k) p) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply, ih]
          have h2 := congrArg (fun f : X →ₗ[ℝ] P => f ((A ^ k) p)) hπP_A
          simpa only [LinearMap.comp_apply, pow_succ', Module.End.mul_eq_comp] using h2.symm
    have hpN : (p : X) ∈ N := by
      rw [mem_unobservableSubspace]
      intro k
      have hk : CP ((AP ^ k) p) = 0 := hp k
      have hsplit : ((πN ((A ^ k) p) : X) + (πP ((A ^ k) p) : X)) = (A ^ k) p := by
        have hh := Submodule.projection_add_projection_eq_self hP ((A ^ k) p)
        simpa only [πN, πP, Submodule.coe_projectionOnto_apply] using hh
      calc C ((A ^ k) p)
          = C ((πN ((A ^ k) p) : X) + (πP ((A ^ k) p) : X)) := by rw [hsplit]
        _ = C (πN ((A ^ k) p) : X) + C (πP ((A ^ k) p) : X) := by rw [map_add]
        _ = 0 := by
            have h1 : C (πN ((A ^ k) p) : X) = 0 :=
              C_eq_zero_of_mem_unobservableSubspace (πN ((A ^ k) p)).2
            have h2 : C (πP ((A ^ k) p) : X) = 0 := by
              rw [← hpow k]
              simpa [CP] using hk
            rw [h1, h2, add_zero]
    have hmem : (p : X) ∈ N ⊓ P := ⟨hpN, p.2⟩
    rw [hP.inf_eq_bot] at hmem
    exact Subtype.ext (by simpa using hmem)
  obtain ⟨LP, hLP⟩ := isDetectable_of_isObservable CP AP hobs
  let L : Y →ₗ[ℝ] X := P.subtype.comp LP
  refine ⟨L, ?_⟩
  let e := N.prodEquivOfIsCompl P hP
  let T' : N × P →ₗ[ℝ] N × P := LinearMap.prod
    ((AN.comp (LinearMap.fst ℝ N P)) + (ANP.comp (LinearMap.snd ℝ N P)))
    ((AP - LP.comp CP).comp (LinearMap.snd ℝ N P))
  have hconj : e.symm.conj (A - L.comp C) = T' := by
    apply LinearMap.ext
    intro pp
    obtain ⟨n, p⟩ := pp
    rw [LinearEquiv.conj_apply_apply]
    rw [Submodule.prodEquivOfIsCompl_symm_apply]
    rw [LinearEquiv.symm_symm, Submodule.coe_prodEquivOfIsCompl']
    apply Prod.ext
    · apply Subtype.ext
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
        LinearMap.prod_apply, Function.prod_apply, LinearMap.fst_apply, LinearMap.snd_apply, T']
      rw [map_sub]
      rw [show C ((n : X) + (p : X)) = C (p : X) by
        rw [map_add, C_eq_zero_of_mem_unobservableSubspace n.2, zero_add]]
      rw [map_add, map_add]
      rw [show (N.projectionOnto P hP) (A (n:X)) = AN n from hπNA n]
      rw [show (N.projectionOnto P hP) (A (p:X)) = ANP p from rfl]
      rw [show (N.projectionOnto P hP) (L (C (p:X))) = 0 from by
        change (N.projectionOnto P hP) ((LP (C (p:X))) : X) = 0
        exact hπNP (LP (C (p:X)))]
      abel
    · apply Subtype.ext
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
        LinearMap.prod_apply, Function.prod_apply, LinearMap.fst_apply, LinearMap.snd_apply, T']
      rw [map_sub]
      rw [show C ((n : X) + (p : X)) = C (p : X) by
        rw [map_add, C_eq_zero_of_mem_unobservableSubspace n.2, zero_add]]
      rw [map_add, map_add]
      rw [show (P.projectionOnto N hP.symm) (A (n:X)) = 0 from hπPA n]
      rw [show (P.projectionOnto N hP.symm) (A (p:X)) = AP p from rfl]
      rw [show (P.projectionOnto N hP.symm) (L (C (p:X))) = LP (C (p:X)) from by
        change (P.projectionOnto N hP.symm) ((LP (C (p:X))) : X) = LP (C (p:X))
        exact hπPP (LP (C (p:X)))]
      simp [CP]
  refine fun μ hμ => ?_
  have hchar : (A - L.comp C).charpoly = T'.charpoly := by
    rw [← LinearEquiv.charpoly_conj e.symm (A - L.comp C), hconj]
  have hTchar : T'.charpoly = AN.charpoly * (AP - LP.comp CP).charpoly :=
    charpoly_prodMap_of_lower_zero _ _ _
  rw [hchar, hTchar] at hμ
  simp only [Polynomial.map_mul, Polynomial.eval_mul] at hμ
  rcases mul_eq_zero.mp hμ with h1 | h2
  · exact hAN μ h1
  · exact hLP μ h2

/-- **Detectability from a Hurwitz unobservable restriction.** If the restriction
of `A` to the unobservable subspace `N = ⟨ker C | A⟩` is Hurwitz, then `(C, A)`
is detectable. The output injection is constructed exactly as in
`isDetectable_of_unobservableEigenvalues_hurwitz`: split `X = N ⊕ P`, observe
that `(C|_P, π_P A|_P)` is observable, stabilise the `P`-block, and assemble the
block-triangular closed loop `A - L C` whose two diagonal blocks are `A|_N`
(Hurwitz by hypothesis) and the stabilised `P`-block. -/
theorem isDetectable_of_isHurwitz_unobservableRestriction (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X)
    (hAN : IsHurwitz (unobservableRestrictionA C A)) : IsDetectable C A := by
  classical
  obtain ⟨P, hP⟩ := Submodule.exists_isCompl (unobservableSubspace C A)
  let N := unobservableSubspace C A
  let πN : X →ₗ[ℝ] N := N.projectionOnto P hP
  let πP : X →ₗ[ℝ] P := P.projectionOnto N hP.symm
  let AN : N →ₗ[ℝ] N := unobservableRestrictionA C A
  let CP : P →ₗ[ℝ] Y := C.comp P.subtype
  let AP : P →ₗ[ℝ] P := πP.comp (A.comp P.subtype)
  let ANP : P →ₗ[ℝ] N := πN.comp (A.comp P.subtype)
  have hAN' : IsHurwitz AN := hAN
  have hπNN : ∀ n : N, (N.projectionOnto P hP) (n : X) = n := by
    intro n; exact Submodule.projectionOnto_apply_of_mem_left hP n.2
  have hπNP : ∀ p : P, (N.projectionOnto P hP) (p : X) = 0 := by
    intro p; exact Submodule.projectionOnto_apply_right hP p
  have hπPN : ∀ n : N, (P.projectionOnto N hP.symm) (n : X) = 0 := by
    intro n; exact Submodule.projectionOnto_apply_right hP.symm n
  have hπPP : ∀ p : P, (P.projectionOnto N hP.symm) (p : X) = p := by
    intro p; exact Submodule.projectionOnto_apply_of_mem_left hP.symm p.2
  have hπNA : ∀ n : N, (N.projectionOnto P hP) (A (n : X)) = AN n := by
    intro n
    have hmem : A (n : X) ∈ N := map_unobservableSubspace_le C A ⟨_, n.2, rfl⟩
    rw [show (N.projectionOnto P hP) (A (n:X)) = ⟨A (n:X), hmem⟩ from
      Submodule.projectionOnto_apply_of_mem_left hP hmem]
    apply Subtype.ext
    simp [AN, unobservableRestrictionA, LinearMap.restrict_apply]
  have hπPA : ∀ n : N, (P.projectionOnto N hP.symm) (A (n : X)) = 0 := by
    intro n
    rw [Submodule.projectionOnto_apply_eq_zero_iff]
    exact map_unobservableSubspace_le C A ⟨_, n.2, rfl⟩
  have hπP_A : (P.projectionOnto N hP.symm).comp A = AP.comp (P.projectionOnto N hP.symm) := by
    apply LinearMap.ext; intro x
    change (P.projectionOnto N hP.symm) (A x) = AP ((P.projectionOnto N hP.symm) x)
    have hdecomp : ((πN x : X) + (πP x : X)) = x := by
      have hh := Submodule.projection_add_projection_eq_self hP x
      simpa only [πN, πP, Submodule.coe_projectionOnto_apply] using hh
    calc (P.projectionOnto N hP.symm) (A x)
        = (P.projectionOnto N hP.symm) (A ((πN x : X) + (πP x : X))) := by rw [hdecomp]
      _ = (P.projectionOnto N hP.symm) (A (πN x : X) + A (πP x : X)) := by rw [map_add]
      _ = (P.projectionOnto N hP.symm) (A (πN x : X)) +
            (P.projectionOnto N hP.symm) (A (πP x : X)) := by rw [map_add]
      _ = AP ((P.projectionOnto N hP.symm) x) := by
          have hz : (P.projectionOnto N hP.symm) (A (πN x : X)) = 0 := by
            rw [Submodule.projectionOnto_apply_eq_zero_iff]
            exact map_unobservableSubspace_le C A ⟨_, (πN x).2, rfl⟩
          rw [hz, zero_add]
          rfl
  have hobs : IsObservable CP AP := by
    rw [isObservable_iff, Submodule.eq_bot_iff]
    intro p hp
    rw [mem_unobservableSubspace] at hp
    have hpow : ∀ k, (AP ^ k) p = (P.projectionOnto N hP.symm) ((A ^ k) p) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply, ih]
          have h2 := congrArg (fun f : X →ₗ[ℝ] P => f ((A ^ k) p)) hπP_A
          simpa only [LinearMap.comp_apply, pow_succ', Module.End.mul_eq_comp] using h2.symm
    have hpN : (p : X) ∈ N := by
      rw [mem_unobservableSubspace]
      intro k
      have hk : CP ((AP ^ k) p) = 0 := hp k
      have hsplit : ((πN ((A ^ k) p) : X) + (πP ((A ^ k) p) : X)) = (A ^ k) p := by
        have hh := Submodule.projection_add_projection_eq_self hP ((A ^ k) p)
        simpa only [πN, πP, Submodule.coe_projectionOnto_apply] using hh
      calc C ((A ^ k) p)
          = C ((πN ((A ^ k) p) : X) + (πP ((A ^ k) p) : X)) := by rw [hsplit]
        _ = C (πN ((A ^ k) p) : X) + C (πP ((A ^ k) p) : X) := by rw [map_add]
        _ = 0 := by
            have h1 : C (πN ((A ^ k) p) : X) = 0 :=
              C_eq_zero_of_mem_unobservableSubspace (πN ((A ^ k) p)).2
            have h2 : C (πP ((A ^ k) p) : X) = 0 := by
              rw [← hpow k]
              simpa [CP] using hk
            rw [h1, h2, add_zero]
    have hmem : (p : X) ∈ N ⊓ P := ⟨hpN, p.2⟩
    rw [hP.inf_eq_bot] at hmem
    exact Subtype.ext (by simpa using hmem)
  obtain ⟨LP, hLP⟩ := isDetectable_of_isObservable CP AP hobs
  let L : Y →ₗ[ℝ] X := P.subtype.comp LP
  refine ⟨L, ?_⟩
  let e := N.prodEquivOfIsCompl P hP
  let T' : N × P →ₗ[ℝ] N × P := LinearMap.prod
    ((AN.comp (LinearMap.fst ℝ N P)) + (ANP.comp (LinearMap.snd ℝ N P)))
    ((AP - LP.comp CP).comp (LinearMap.snd ℝ N P))
  have hconj : e.symm.conj (A - L.comp C) = T' := by
    apply LinearMap.ext
    intro pp
    obtain ⟨n, p⟩ := pp
    rw [LinearEquiv.conj_apply_apply]
    rw [Submodule.prodEquivOfIsCompl_symm_apply]
    rw [LinearEquiv.symm_symm, Submodule.coe_prodEquivOfIsCompl']
    apply Prod.ext
    · apply Subtype.ext
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
        LinearMap.prod_apply, Function.prod_apply, LinearMap.fst_apply, LinearMap.snd_apply, T']
      rw [map_sub]
      rw [show C ((n : X) + (p : X)) = C (p : X) by
        rw [map_add, C_eq_zero_of_mem_unobservableSubspace n.2, zero_add]]
      rw [map_add, map_add]
      rw [show (N.projectionOnto P hP) (A (n:X)) = AN n from hπNA n]
      rw [show (N.projectionOnto P hP) (A (p:X)) = ANP p from rfl]
      rw [show (N.projectionOnto P hP) (L (C (p:X))) = 0 from by
        change (N.projectionOnto P hP) ((LP (C (p:X))) : X) = 0
        exact hπNP (LP (C (p:X)))]
      abel
    · apply Subtype.ext
      simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
        LinearMap.prod_apply, Function.prod_apply, LinearMap.fst_apply, LinearMap.snd_apply, T']
      rw [map_sub]
      rw [show C ((n : X) + (p : X)) = C (p : X) by
        rw [map_add, C_eq_zero_of_mem_unobservableSubspace n.2, zero_add]]
      rw [map_add, map_add]
      rw [show (P.projectionOnto N hP.symm) (A (n:X)) = 0 from hπPA n]
      rw [show (P.projectionOnto N hP.symm) (A (p:X)) = AP p from rfl]
      rw [show (P.projectionOnto N hP.symm) (L (C (p:X))) = LP (C (p:X)) from by
        change (P.projectionOnto N hP.symm) ((LP (C (p:X))) : X) = LP (C (p:X))
        exact hπPP (LP (C (p:X)))]
      simp [CP]
  refine fun μ hμ => ?_
  have hchar : (A - L.comp C).charpoly = T'.charpoly := by
    rw [← LinearEquiv.charpoly_conj e.symm (A - L.comp C), hconj]
  have hTchar : T'.charpoly = AN.charpoly * (AP - LP.comp CP).charpoly :=
    charpoly_prodMap_of_lower_zero _ _ _
  rw [hchar, hTchar] at hμ
  simp only [Polynomial.map_mul, Polynomial.eval_mul] at hμ
  rcases mul_eq_zero.mp hμ with h1 | h2
  · exact hAN' μ h1
  · exact hLP μ h2

end ConversePBH

/-! ## Hurwitz quotients of triangular product operators -/

section BlockQuotient
variable {M N : Type*}
variable [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
variable [AddCommGroup N] [Module ℝ N] [FiniteDimensional ℝ N]

/-- The heterogeneous upper-triangular block operator
`(m, n) ↦ (T m + K n, S n)` on `M × N`. -/
noncomputable def blockOperator₂ (T : M →ₗ[ℝ] M) (K : N →ₗ[ℝ] M) (S : N →ₗ[ℝ] N) :
    M × N →ₗ[ℝ] M × N :=
  LinearMap.prod ((T.comp (LinearMap.fst ℝ M N)) + (K.comp (LinearMap.snd ℝ M N)))
    (S.comp (LinearMap.snd ℝ M N))

omit [FiniteDimensional ℝ M] [FiniteDimensional ℝ N] in
theorem blockOperator₂_apply (T : M →ₗ[ℝ] M) (K : N →ₗ[ℝ] M) (S : N →ₗ[ℝ] N)
    (m : M) (n : N) :
    blockOperator₂ T K S (m, n) = (T m + K n, S n) := by
  simp [blockOperator₂]

omit [FiniteDimensional ℝ M] in
/-- The heterogeneous definition agrees with the existing square-block operator. -/
theorem blockOperator₂_self (T K S : M →ₗ[ℝ] M) :
    blockOperator₂ T K S = blockOperator T K S := by
  apply LinearMap.ext
  rintro ⟨m, n⟩
  simp [blockOperator₂_apply, blockOperator_apply]

/-- The characteristic polynomial of the heterogeneous block operator factors as
`T.charpoly * S.charpoly`. -/
theorem charpoly_blockOperator₂ (T : M →ₗ[ℝ] M) (K : N →ₗ[ℝ] M) (S : N →ₗ[ℝ] N) :
    (blockOperator₂ T K S).charpoly = T.charpoly * S.charpoly :=
  charpoly_prodMap_of_lower_zero T S K

omit [FiniteDimensional ℝ M] [FiniteDimensional ℝ N] in
/-- The product `P × Q` is invariant under `blockOperator₂ T K S` when `T` preserves `P`,
`S` preserves `Q` and `K` maps `Q` into `P`. -/
theorem prodInvariance (T : M →ₗ[ℝ] M) (K : N →ₗ[ℝ] M) (S : N →ₗ[ℝ] N)
    (P : Submodule ℝ M) (Q : Submodule ℝ N)
    (hTP : ∀ x ∈ P, T x ∈ P) (hSQ : ∀ y ∈ Q, S y ∈ Q) (hKQ : ∀ y ∈ Q, K y ∈ P) :
    ∀ z ∈ P.prod Q, blockOperator₂ T K S z ∈ P.prod Q := by
  intro z hz
  rw [Submodule.mem_prod] at hz
  obtain ⟨hz1, hz2⟩ := hz
  rw [blockOperator₂_apply, Submodule.mem_prod]
  exact ⟨P.add_mem (hTP z.1 hz1) (hKQ z.2 hz2), hSQ z.2 hz2⟩

/-- **Quotient of a block-upper-triangular map.** If `T` preserves `P`, `S` preserves
`Q`, `K` maps `Q` into `P`, and the quotient maps induced by `T` on `M ⧸ P` and by `S`
on `N ⧸ Q` are Hurwitz, then the map induced by `(m, n) ↦ (T m + K n, S n)` on
`(M × N) ⧸ (P × Q)` is Hurwitz. -/
theorem isHurwitz_mapQ_prod_of_isHurwitz
    (T : M →ₗ[ℝ] M) (K : N →ₗ[ℝ] M) (S : N →ₗ[ℝ] N)
    (P : Submodule ℝ M) (Q : Submodule ℝ N)
    (hTP : ∀ x ∈ P, T x ∈ P) (hSQ : ∀ y ∈ Q, S y ∈ Q) (hKQ : ∀ y ∈ Q, K y ∈ P)
    (hTq : IsHurwitz (Submodule.mapQ P P T (fun x hx => hTP x hx)))
    (hSq : IsHurwitz (Submodule.mapQ Q Q S (fun y hy => hSQ y hy))) :
    IsHurwitz (Submodule.mapQ (P.prod Q) (P.prod Q) (blockOperator₂ T K S)
      (prodInvariance T K S P Q hTP hSQ hKQ)) := by
  classical
  let hA : ∀ z ∈ P.prod Q, blockOperator₂ T K S z ∈ P.prod Q :=
    prodInvariance T K S P Q hTP hSQ hKQ
  let φ : (M × N) ⧸ (P.prod Q) →ₗ[ℝ] (M × N) ⧸ (P.prod Q) :=
    Submodule.mapQ (P.prod Q) (P.prod Q) (blockOperator₂ T K S) hA
  let Tq : M ⧸ P →ₗ[ℝ] M ⧸ P := Submodule.mapQ P P T (fun x hx => hTP x hx)
  let Sq : N ⧸ Q →ₗ[ℝ] N ⧸ Q := Submodule.mapQ Q Q S (fun y hy => hSQ y hy)
  let Kbar : N ⧸ Q →ₗ[ℝ] M ⧸ P := Submodule.mapQ Q P K (fun y hy => hKQ y hy)
  let f : M × N →ₗ[ℝ] (M ⧸ P) × (N ⧸ Q) :=
    (P.mkQ.comp (LinearMap.fst ℝ M N)).prod (Q.mkQ.comp (LinearMap.snd ℝ M N))
  have hf : Function.Surjective f := by
    intro p
    obtain ⟨u, v⟩ := p
    refine Submodule.Quotient.induction_on P u ?_
    intro m
    refine Submodule.Quotient.induction_on Q v ?_
    intro n
    exact ⟨(m, n), rfl⟩
  have hker : LinearMap.ker f = P.prod Q := by
    ext z
    obtain ⟨m, n⟩ := z
    rw [LinearMap.mem_ker, Submodule.mem_prod]
    change (P.mkQ m, Q.mkQ n) = 0 ↔ m ∈ P ∧ n ∈ Q
    simp [Submodule.Quotient.mk_eq_zero]
  let e : ((M × N) ⧸ (P.prod Q)) ≃ₗ[ℝ] ((M ⧸ P) × (N ⧸ Q)) :=
    (Submodule.quotEquivOfEq (P.prod Q) (LinearMap.ker f) hker.symm).trans
      (f.quotKerEquivOfSurjective hf)
  have he : ∀ z : M × N, e (Submodule.Quotient.mk z) = f z := by
    intro z
    simp only [e, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk]
  have hcomp : e.toLinearMap.comp φ = (blockOperator₂ Tq Kbar Sq).comp e.toLinearMap := by
    apply LinearMap.ext
    intro y
    refine Submodule.Quotient.induction_on (P.prod Q) y ?_
    intro z
    obtain ⟨m, n⟩ := z
    change e (Submodule.Quotient.mk (blockOperator₂ T K S (m, n))) =
      (blockOperator₂ Tq Kbar Sq) (e (Submodule.Quotient.mk (m, n)))
    rw [he (blockOperator₂ T K S (m, n)), he (m, n)]
    simp only [blockOperator₂_apply, Tq, Sq, Kbar, f, Function.prod_apply,
      LinearMap.prod_apply, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      Submodule.mapQ_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_add]
  have hconj : e.conj φ = blockOperator₂ Tq Kbar Sq := by
    rw [LinearEquiv.conj_apply, hcomp]
    apply LinearMap.ext
    intro x
    simp
  have hchar : φ.charpoly = (blockOperator₂ Tq Kbar Sq).charpoly := by
    rw [← LinearEquiv.charpoly_conj e φ, hconj]
  change IsHurwitz φ
  intro z hz
  have hz' : ((blockOperator₂ Tq Kbar Sq).charpoly.map (algebraMap ℝ ℂ)).eval z = 0 := by
    rwa [← hchar]
  rw [charpoly_blockOperator₂, Polynomial.map_mul, Polynomial.eval_mul] at hz'
  rcases mul_eq_zero.mp hz' with h | h
  · exact hTq z h
  · exact hSq z h

end BlockQuotient

section NestedBlockQuotient

variable {M N : Type*}
variable [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
variable [AddCommGroup N] [Module ℝ N] [FiniteDimensional ℝ N]

/-- Canonical linear equivalence between the subtype `↥(W.prod U)` of a product
and the product `W × U` of the subtypes. This is the "product subtype
equivalence" used to move the restriction of a block operator into the product
picture where `isHurwitz_mapQ_prod_of_isHurwitz` applies. -/
noncomputable def prodSubtypeEquiv (W : Submodule ℝ M) (U : Submodule ℝ N) :
    ↥(W.prod U) ≃ₗ[ℝ] (W × U) where
  toFun z :=
    (⟨z.1.1, (Submodule.mem_prod.mp z.2).1⟩, ⟨z.1.2, (Submodule.mem_prod.mp z.2).2⟩)
  invFun p := ⟨(p.1.1, p.2.1), Submodule.mem_prod.mpr ⟨p.1.2, p.2.2⟩⟩
  left_inv z := by ext <;> rfl
  right_inv p := by ext <;> rfl
  map_add' z w := by ext <;> rfl
  map_smul' c z := by ext <;> rfl

omit [FiniteDimensional ℝ M] [FiniteDimensional ℝ N] in
@[simp]
theorem prodSubtypeEquiv_apply (W : Submodule ℝ M) (U : Submodule ℝ N)
    (z : ↥(W.prod U)) :
    prodSubtypeEquiv W U z =
      (⟨z.1.1, (Submodule.mem_prod.mp z.2).1⟩,
        ⟨z.1.2, (Submodule.mem_prod.mp z.2).2⟩) :=
  rfl

omit [FiniteDimensional ℝ M] [FiniteDimensional ℝ N] in
@[simp]
theorem prodSubtypeEquiv_symm_apply (W : Submodule ℝ M) (U : Submodule ℝ N)
    (p : W × U) :
    (prodSubtypeEquiv W U).symm p =
      ⟨(p.1.1, p.2.1), Submodule.mem_prod.mpr ⟨p.1.2, p.2.2⟩⟩ :=
  rfl

omit [FiniteDimensional ℝ M] [FiniteDimensional ℝ N] in
/-- **Conjugacy of the restricted block operator with the block operator built
from the restricted diagonal maps.** Restricting `(m,n) ↦ (A m + B n, C n)` to
`W.prod U` and transporting along `prodSubtypeEquiv` gives the block operator
`(w,u) ↦ (A|_W w + B|_{U→W} u, C|_U u)`. -/
theorem prodSubtypeEquiv_conj_blockOperator₂
    (A : M →ₗ[ℝ] M) (B : N →ₗ[ℝ] M) (C : N →ₗ[ℝ] N)
    (W : Submodule ℝ M) (U : Submodule ℝ N)
    (hAW : ∀ x ∈ W, A x ∈ W) (hCU : ∀ y ∈ U, C y ∈ U) (hBU : ∀ y ∈ U, B y ∈ W) :
    (prodSubtypeEquiv W U).conj
        ((blockOperator₂ A B C).restrict (prodInvariance A B C W U hAW hCU hBU)) =
      blockOperator₂ (A.restrict hAW) (B.restrict hBU) (C.restrict hCU) := by
  apply LinearMap.ext
  intro p
  obtain ⟨w, u⟩ := p
  rw [LinearEquiv.conj_apply_apply]
  simp only [prodSubtypeEquiv_apply, prodSubtypeEquiv_symm_apply, blockOperator₂_apply,
    LinearMap.restrict_apply]
  rfl

omit [FiniteDimensional ℝ M] [FiniteDimensional ℝ N] in
/-- The submodule `V.prod T` (pulled back along the subtype inclusion) is
invariant under the restriction of the block operator to `W.prod U`, when
`A` preserves `V`, `C` preserves `T` and `B` maps `T` into `V`. -/
theorem prodRestrictInvariance
    (A : M →ₗ[ℝ] M) (B : N →ₗ[ℝ] M) (C : N →ₗ[ℝ] N)
    (W : Submodule ℝ M) (U : Submodule ℝ N)
    (V : Submodule ℝ M) (T : Submodule ℝ N)
    (hAW : ∀ x ∈ W, A x ∈ W) (hCU : ∀ y ∈ U, C y ∈ U) (hBU : ∀ y ∈ U, B y ∈ W)
    (hAV : ∀ x ∈ V, A x ∈ V) (hCT : ∀ y ∈ T, C y ∈ T) (hBT : ∀ y ∈ T, B y ∈ V) :
    ∀ z ∈ (V.prod T).comap (Submodule.subtype (W.prod U)),
      (blockOperator₂ A B C).restrict (prodInvariance A B C W U hAW hCU hBU) z ∈
        (V.prod T).comap (Submodule.subtype (W.prod U)) := by
  intro z hz
  rw [Submodule.mem_comap] at hz ⊢
  obtain ⟨hz1, hz2⟩ := Submodule.mem_prod.mp hz
  rw [LinearMap.restrict_apply]
  exact Submodule.mem_prod.mpr
    ⟨V.add_mem (hAV _ hz1) (hBT _ hz2), hCT _ hz2⟩

/-- **Hurwitz quotient of a nested block restriction.** Let
`(m,n) ↦ (A m + B n, C n)` be an upper-triangular block operator on `M × N`.
Let `W ≤ M`, `U ≤ N` be invariant numerator subspaces and `V ≤ W`, `T ≤ U`
invariant denominator subspaces, with `B U ≤ W` and `B T ≤ V`. If the induced
maps on `W ⧸ V` and `U ⧸ T` are Hurwitz, then the map induced by the block
operator restricted to `W.prod U` on the quotient `(W.prod U) ⧸ (V.prod T)` is
Hurwitz.

The proof transports the restriction along the product subtype equivalence
`↥(W.prod U) ≃ₗ W × U`, applies
`LinearMap.isHurwitz_mapQ_prod_of_isHurwitz` to the resulting block operator on
`W × U`, and transports Hurwitzness back along the induced quotient
conjugacy. -/
theorem isHurwitz_mapQ_prod_restrict_of_isHurwitz
    (A : M →ₗ[ℝ] M) (B : N →ₗ[ℝ] M) (C : N →ₗ[ℝ] N)
    (W : Submodule ℝ M) (U : Submodule ℝ N)
    (V : Submodule ℝ M) (T : Submodule ℝ N)
    (hVW : V ≤ W) (hTU : T ≤ U)
    (hAW : ∀ x ∈ W, A x ∈ W) (hCU : ∀ y ∈ U, C y ∈ U) (hBU : ∀ y ∈ U, B y ∈ W)
    (hAV : ∀ x ∈ V, A x ∈ V) (hCT : ∀ y ∈ T, C y ∈ T) (hBT : ∀ y ∈ T, B y ∈ V)
    (hAq : IsHurwitz (Submodule.mapQ (V.comap W.subtype) (V.comap W.subtype)
      (A.restrict hAW) (fun x hx => hAV x.1 hx)))
    (hCq : IsHurwitz (Submodule.mapQ (T.comap U.subtype) (T.comap U.subtype)
      (C.restrict hCU) (fun y hy => hCT y.1 hy))) :
    IsHurwitz (Submodule.mapQ
      ((V.prod T).comap (Submodule.subtype (W.prod U)))
      ((V.prod T).comap (Submodule.subtype (W.prod U)))
      ((blockOperator₂ A B C).restrict (prodInvariance A B C W U hAW hCU hBU))
      (prodRestrictInvariance A B C W U V T hAW hCU hBU hAV hCT hBT)) := by
  classical
  have _ := hVW
  have _ := hTU
  let A' : W →ₗ[ℝ] W := A.restrict hAW
  let B' : U →ₗ[ℝ] W := B.restrict hBU
  let C' : U →ₗ[ℝ] U := C.restrict hCU
  let V' : Submodule ℝ W := V.comap W.subtype
  let T' : Submodule ℝ U := T.comap U.subtype
  let P : Submodule ℝ ↥(W.prod U) := (V.prod T).comap (Submodule.subtype (W.prod U))
  let fr : ↥(W.prod U) →ₗ[ℝ] ↥(W.prod U) :=
    (blockOperator₂ A B C).restrict (prodInvariance A B C W U hAW hCU hBU)
  let hP : ∀ z ∈ P, fr z ∈ P :=
    prodRestrictInvariance A B C W U V T hAW hCU hBU hAV hCT hBT
  -- The product-side invariance used by `isHurwitz_mapQ_prod_of_isHurwitz`.
  have hV'T' : ∀ p ∈ V'.prod T', (blockOperator₂ A' B' C') p ∈ V'.prod T' := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Submodule.mem_prod.mp hp
    exact Submodule.mem_prod.mpr
      ⟨V'.add_mem (hAV _ hp1) (hBT _ hp2), hCT _ hp2⟩
  -- Apply the existing product quotient theorem.
  have hQuot : IsHurwitz (Submodule.mapQ (V'.prod T') (V'.prod T')
      (blockOperator₂ A' B' C') hV'T') := by
    refine isHurwitz_mapQ_prod_of_isHurwitz A' B' C' V' T'
      (fun x hx => hAV x.1 hx) (fun y hy => hCT y.1 hy) (fun y hy => hBT y.1 hy)
      ?_ ?_
    · simpa only [A', V'] using hAq
    · simpa only [C', T'] using hCq
  -- The product subtype equivalence and the induced quotient conjugacy.
  let e : ↥(W.prod U) ≃ₗ[ℝ] (W × U) := prodSubtypeEquiv W U
  have hmap : Submodule.map (e : ↥(W.prod U) →ₗ[ℝ] (W × U)) P = V'.prod T' := by
    ext p
    rw [Submodule.mem_map_equiv]
    change (e.symm p).1 ∈ V.prod T ↔ p ∈ V'.prod T'
    simp only [e, V', T', prodSubtypeEquiv_symm_apply, Submodule.mem_prod,
      Submodule.mem_comap, Submodule.subtype_apply]
  let qe : (↥(W.prod U) ⧸ P) ≃ₗ[ℝ] ((W × U) ⧸ (V'.prod T')) :=
    Submodule.Quotient.equiv P (V'.prod T') e hmap
  have hconj : qe.conj (Submodule.mapQ P P fr hP) =
      Submodule.mapQ (V'.prod T') (V'.prod T') (blockOperator₂ A' B' C') hV'T' := by
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ y =>
      simp only [LinearEquiv.conj_apply_apply, qe, Submodule.Quotient.equiv_symm,
        Submodule.Quotient.equiv_apply, Submodule.mapQ_apply, e, fr]
      rw [← prodSubtypeEquiv_conj_blockOperator₂ A B C W U hAW hCU hBU]
      rw [LinearEquiv.conj_apply_apply]
      rfl
  -- Transfer Hurwitzness across the conjugacy.
  have hchar : (Submodule.mapQ P P fr hP).charpoly =
      (Submodule.mapQ (V'.prod T') (V'.prod T') (blockOperator₂ A' B' C') hV'T').charpoly := by
    rw [← LinearEquiv.charpoly_conj qe (Submodule.mapQ P P fr hP), hconj]
  have hφ : IsHurwitz (Submodule.mapQ P P fr hP) := by
    intro z hz
    apply hQuot z
    rwa [hchar] at hz
  exact hφ

end NestedBlockQuotient

/-! ## Restriction and quotient characteristic polynomials

For an `A`-invariant submodule `V`, the characteristic polynomial of `A` factors
exactly as the product of the characteristic polynomial of the restriction
`A|_V` and that of the induced map on the quotient `X ⧸ V`. This is the
spectral bridge used to lift properties of `A` to invariant submodules and their
quotients. The quotient factor is the existing Mathlib map
`Submodule.mapQ V V A`, so no new quotient-spectrum API is introduced.

Source: Trentelman–Stoorvogel–Hautus, Chapter 2 (invariant subspaces and the
restriction/quotient constructions used in Sections 4.5–4.6 and Chapter 6). -/

section RestrictCharpoly

/-- **Exact characteristic-polynomial factorization for an invariant submodule.**
If `V` is invariant under `A`, then
`A.charpoly = (A|_V).charpoly * (A|_{X/V}).charpoly`, where `A|_{X/V}` is the
quotient map `Submodule.mapQ V V A`. The proof chooses a complement `Q` of `V`,
conjugates `A` to the block-upper-triangular operator
`(v, q) ↦ (A v + π_V A q, π_Q A q)` (whose characteristic polynomial is the
product by `charpoly_prodMap_of_lower_zero`), identifies the second block with
the quotient map through `Submodule.quotientEquivOfIsCompl`, and transports the
characteristic polynomial along both linear equivalences.

The edge cases `V = ⊥` and `V = ⊤` are covered by the universal statement; the
two companion lemmas below record them explicitly. -/
theorem charpoly_restrict_of_invariant (A : X →ₗ[ℝ] X) (V : Submodule ℝ X)
    (hV : ∀ x ∈ V, A x ∈ V) :
    A.charpoly = (A.restrict hV).charpoly *
      (Submodule.mapQ V V A (fun x hx => hV x hx)).charpoly := by
  classical
  obtain ⟨Q, hQ⟩ := Submodule.exists_isCompl V
  let πV : X →ₗ[ℝ] V := V.projectionOnto Q hQ
  let πQ : X →ₗ[ℝ] Q := Q.projectionOnto V hQ.symm
  let A11 : V →ₗ[ℝ] V := A.restrict hV
  let A12 : Q →ₗ[ℝ] V := πV.comp (A.comp Q.subtype)
  let A22 : Q →ₗ[ℝ] Q := πQ.comp (A.comp Q.subtype)
  let e := V.prodEquivOfIsCompl Q hQ
  let T : V × Q →ₗ[ℝ] V × Q := LinearMap.prod
    ((A11.comp (LinearMap.fst ℝ V Q)) + (A12.comp (LinearMap.snd ℝ V Q)))
    (A22.comp (LinearMap.snd ℝ V Q))
  have hconj : e.symm.conj A = T := by
    apply LinearMap.ext
    intro p
    obtain ⟨v, q⟩ := p
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_symm]
    simp only [T, LinearMap.prod_apply]
    rw [Submodule.coe_prodEquivOfIsCompl']
    rw [Submodule.prodEquivOfIsCompl_symm_apply]
    rw [map_add, map_add, map_add]
    congr 1
    · have h1 : V.projectionOnto Q hQ (A (v : X)) = A11 v := by
        rw [Submodule.projectionOnto_apply_of_mem_left hQ (hV v v.2)]
        rfl
      have h2 : V.projectionOnto Q hQ (A (q : X)) = A12 q := rfl
      rw [h1, h2]
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
        LinearMap.snd_apply]
    · have h1 : Q.projectionOnto V hQ.symm (A (v : X)) = 0 := by
        rw [Submodule.projectionOnto_apply_eq_zero_iff]
        exact hV v v.2
      have h2 : Q.projectionOnto V hQ.symm (A (q : X)) = A22 q := rfl
      rw [h1, h2, zero_add]
      simp only [LinearMap.comp_apply, LinearMap.snd_apply]
  have hchar1 : A.charpoly = T.charpoly := by
    rw [← hconj]
    exact (LinearEquiv.charpoly_conj e.symm A).symm
  have hTchar : T.charpoly = A11.charpoly * A22.charpoly :=
    charpoly_prodMap_of_lower_zero A11 A22 A12
  have hA11 : A11.charpoly = (A.restrict hV).charpoly := rfl
  let eQ : (X ⧸ V) ≃ₗ[ℝ] Q := Submodule.quotientEquivOfIsCompl V Q hQ
  have hsymm : ∀ z : Q, eQ.symm z = Submodule.Quotient.mk (z : X) := fun z =>
    eQ.injective (by rw [LinearEquiv.apply_symm_apply,
      Submodule.quotientEquivOfIsCompl_apply_mk_right])
  have hq : eQ.symm.conj A22 = Submodule.mapQ V V A (fun x hx => hV x hx) := by
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on (p := V) x ?_
    intro y
    change eQ.symm (A22 (eQ (Submodule.Quotient.mk y))) = _
    rw [Submodule.quotientEquivOfIsCompl_apply_mk]
    rw [Submodule.mapQ_apply]
    rw [hsymm (A22 (πQ y))]
    refine (Submodule.Quotient.eq V).mpr ?_
    have hdecomp : ((πV y : V) : X) + ((πQ y : Q) : X) = y := by
      have hh := Submodule.projection_add_projection_eq_self hQ y
      simpa only [πV, πQ, Submodule.coe_projectionOnto_apply] using hh
    have hsplit : A ((πQ y : Q) : X) =
        ((πV (A ((πQ y : Q) : X)) : V) : X) +
          ((πQ (A ((πQ y : Q) : X)) : Q) : X) := by
      have hh := Submodule.projection_add_projection_eq_self hQ (A ((πQ y : Q) : X))
      simpa only [πV, πQ, Submodule.coe_projectionOnto_apply] using hh.symm
    have hAy : A y = A ((πV y : V) : X) + A ((πQ y : Q) : X) := by
      conv_lhs => rw [← hdecomp]
      rw [map_add]
    have hmem1 : A ((πV y : V) : X) ∈ V := hV _ (πV y).2
    have hmem2 : ((πV (A ((πQ y : Q) : X)) : V) : X) ∈ V := (πV _).2
    have hA22 : ((A22 (πQ y) : Q) : X) = (πQ (A ((πQ y : Q) : X)) : Q) := rfl
    rw [hAy, hsplit]
    have hsim : (πQ (A ((πQ y : Q) : X)) : X) -
        (A ((πV y : V) : X) + (((πV (A ((πQ y : Q) : X)) : V) : X) +
          (πQ (A ((πQ y : Q) : X)) : X))) =
        - A ((πV y : V) : X) - ((πV (A ((πQ y : Q) : X)) : V) : X) := by abel
    rw [hA22, hsim]
    rw [sub_eq_add_neg]
    exact V.add_mem (V.neg_mem hmem1) (V.neg_mem hmem2)
  have hchar2 : A22.charpoly =
      (Submodule.mapQ V V A (fun x hx => hV x hx)).charpoly := by
    rw [← hq]
    exact (LinearEquiv.charpoly_conj eQ.symm A22).symm
  rw [hchar1, hTchar, hA11, hchar2]

/-- The restriction characteristic polynomial divides the ambient one. This is
the spectrum-transfer form of `charpoly_restrict_of_invariant`: every complex
root of `(A|_V).charpoly` is a root of `A.charpoly`. It is the form used to move
`IsHurwitz` from `A` to `A|_V`. -/
theorem charpoly_restrict_dvd_of_invariant (A : X →ₗ[ℝ] X) (V : Submodule ℝ X)
    (hV : ∀ x ∈ V, A x ∈ V) :
    (A.restrict hV).charpoly ∣ A.charpoly :=
  ⟨_, charpoly_restrict_of_invariant A V hV⟩

/-- **Spectrum transfer to an invariant submodule.** If `A` is Hurwitz, then so
is its restriction `A|_V` to any `A`-invariant submodule `V`. This is the
general form of `isHurwitz_restrict_of_hurwitzSubspace`: a complex root of the
restricted characteristic polynomial is a root of the ambient one by
`charpoly_restrict_dvd_of_invariant`, hence has negative real part. -/
theorem isHurwitz_restrict_of_invariant (A : X →ₗ[ℝ] X) (V : Submodule ℝ X)
    (hV : ∀ x ∈ V, A x ∈ V) (hA : IsHurwitz A) :
    IsHurwitz (A.restrict hV) := by
  intro z hz
  obtain ⟨q, hq⟩ := charpoly_restrict_dvd_of_invariant A V hV
  have hz' : (A.charpoly.map (algebraMap ℝ ℂ)).eval z = 0 := by
    rw [hq, Polynomial.map_mul, Polynomial.eval_mul, hz, zero_mul]
  exact hA z hz'

/-- Edge case `V = ⊤`: restricting to the whole space does not change the
characteristic polynomial. The restriction `A|_⊤` is conjugate to `A` along
`Submodule.topEquiv`. -/
theorem charpoly_restrict_top (A : X →ₗ[ℝ] X) :
    (A.restrict (p := ⊤) (q := ⊤) (fun _ _ => Submodule.mem_top)).charpoly = A.charpoly := by
  have hconj : (Submodule.topEquiv.symm : X ≃ₗ[ℝ] (⊤ : Submodule ℝ X)).conj A =
      (A.restrict (p := ⊤) (q := ⊤) (fun _ _ => Submodule.mem_top)) := by
    apply LinearMap.ext
    intro x
    rfl
  rw [← hconj, LinearEquiv.charpoly_conj]

omit [FiniteDimensional ℝ X] in
/-- Edge case `V = ⊥`: the restriction to the zero subspace is an endomorphism
of the zero-dimensional space, whose characteristic polynomial is `1`. -/
theorem charpoly_restrict_bot (A : X →ₗ[ℝ] X) :
    (A.restrict (p := ⊥) (q := ⊥) (fun _ hx => by
      rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero])).charpoly = 1 := by
  have h0 : (A.restrict (p := ⊥) (q := ⊥) (fun _ hx => by
      rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero])) =
      (0 : (⊥ : Submodule ℝ X) →ₗ[ℝ] (⊥ : Submodule ℝ X)) := by
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _
  rw [h0, LinearMap.charpoly_zero, finrank_bot, pow_zero]

end RestrictCharpoly

/-! ## The general Hurwitz-to-decay bridge: the complex spectral case

The analytic heart of the general bridge: over a finite-dimensional complex
normed space, if every root of the characteristic polynomial of an endomorphism
`f` has negative real part, then every trajectory `t ↦ exp (t • f) x` tends to
zero. The proof decomposes the space into the generalized eigenspaces of `f`
(`Module.End.iSup_maxGenEigenspace_eq_top`, `Submodule.mem_iSup_iff_exists_finset`),
on each of which `f - μ` is nilpotent, so the exponential is a finite
polynomial-times-`exp (t μ)` sum (`exp_nilpotent_apply_eq_sum`), which decays
because `μ.re < 0`.

This is the hard analytic half of the general Hurwitz-to-decay bridge, and it is
completed below. The real reduction complexifies `A` (transporting it to
`Fin n → ℂ` along a real basis), applies `tendsto_exp_complex_apply`, and
transports the convergence back along the basis isomorphism using the relation
`exp (t • A) = repr.symm ∘ exp (t • repr.conj A) ∘ repr`. The real theorems
`LinearMap.tendsto_exp_of_isHurwitz` and
`LinearMap.isStableOn_expFlow_of_isHurwitz` are exactly that reduction and are
proved later in this section. -/

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
  have hseries := exp_smul_apply_eq_tsum N (t : ℂ) x
  rw [show (t : ℂ) • N = t • N from rfl] at hseries
  rw [hseries]
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
real case is recovered by complexification and change of coordinates in
`LinearMap.tendsto_exp_of_isHurwitz`, proved below. -/
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

/-! ## Exponential independence of unit-modulus characters

The degree-zero case of the independence of exponential polynomials, which is
the analytic core of the Bohl leading-term argument: a finite sum of distinct
unit-modulus exponential characters with vector coefficients cannot tend to zero
at `+∞` unless every coefficient vanishes. The proof is elementary: the Cesàro
average of `n ↦ z ^ n` is `1` for `z = 1` and `0` otherwise, so averaging a
convergent sum after shifting by one character isolates each coefficient.

This is the reusable building block for the antistable readout lemma: the
remaining polynomial-exponential reduction (factoring the dominant real part and
the top power of `t`) is a separate step, but the cancellation argument that
actually forces one mode at a time is contained here. -/

/-- **Cesàro average of a unit-modulus geometric progression.** For a complex
number `z` of modulus one, the average `n⁻¹ ∑_{k<n} z^k` tends to `1` when
`z = 1` and to `0` otherwise. When `z ≠ 1` the geometric-sum formula bounds the
partial sums by `2 / ‖z - 1‖`, while for `z = 1` the average is eventually `1`. -/
lemma tendsto_inv_mul_geom_sum (z : ℂ) (hz : ‖z‖ = 1) :
    Tendsto (fun n : ℕ => (n : ℂ)⁻¹ * ∑ k ∈ Finset.range n, z ^ k) atTop
      (𝓝 (if z = 1 then 1 else 0)) := by
  by_cases h1 : z = 1
  · subst h1
    rw [ite_eq_left rfl]
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℂ) ≠ 0 := by
      rw [Nat.cast_ne_zero]; omega
    rw [show (∑ k ∈ Finset.range n, (1 : ℂ) ^ k) = (n : ℂ) by
      simp [Finset.sum_const, nsmul_eq_mul]]
    exact (inv_mul_cancel₀ hn0).symm
  · rw [ite_eq_right h1]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbd : ∀ n : ℕ, ‖(n : ℂ)⁻¹ * ∑ k ∈ Finset.range n, z ^ k‖ ≤
        (2 / ‖z - 1‖) / n := by
      intro n
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp
      · have hS : ‖∑ k ∈ Finset.range n, z ^ k‖ ≤ 2 / ‖z - 1‖ := by
          rw [geom_sum_eq h1 n, norm_div]
          apply div_le_div_of_nonneg_right _ (norm_nonneg _)
          calc ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
            _ = 2 := by rw [norm_pow, hz, one_pow]; norm_num
        calc ‖(n : ℂ)⁻¹ * ∑ k ∈ Finset.range n, z ^ k‖
            = ‖(n : ℂ)⁻¹‖ * ‖∑ k ∈ Finset.range n, z ^ k‖ := norm_mul _ _
          _ = (n : ℝ)⁻¹ * ‖∑ k ∈ Finset.range n, z ^ k‖ := by
              rw [norm_inv, Complex.norm_natCast]
          _ ≤ (n : ℝ)⁻¹ * (2 / ‖z - 1‖) :=
              mul_le_mul_of_nonneg_left hS (by positivity)
          _ = (2 / ‖z - 1‖) / n := by rw [div_eq_mul_inv]; ring
    refine squeeze_zero (g := fun n : ℕ => (2 / ‖z - 1‖) / n)
      (fun n => norm_nonneg _) (fun n => hbd n) ?_
    exact tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (2 / ‖z - 1‖)

/-- **Exponential independence of unit-modulus characters.** A finite sum of
distinct unit-modulus characters `n ↦ z i ^ n` with coefficients `a i` in a
complex normed space cannot tend to zero unless every coefficient vanishes. The
proof shifts the sum by the inverse of one character, applies the Cesàro average
`tendsto_inv_mul_geom_sum`, and reads off the corresponding coefficient. -/
lemma tendsto_zero_of_sum_pow_smul {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {ι : Type*} (s : Finset ι) (z : ι → ℂ) (hz : ∀ i ∈ s, ‖z i‖ = 1)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, z i = z j → i = j) (a : ι → W)
    (h : Tendsto (fun n : ℕ => ∑ i ∈ s, (z i) ^ n • a i) atTop (𝓝 0)) :
    ∀ i ∈ s, a i = 0 := by
  intro j hj
  have hzj : ‖z j‖ = 1 := hz j hj
  have hzj0 : z j ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hzj; exact one_ne_zero hzj.symm
  have hcoescale : ∀ (r : ℝ) (w : W), r • w = (r : ℂ) • w :=
    fun r w => RCLike.real_smul_eq_coe_smul r w
  have hnorm : Tendsto (fun n : ℕ => ‖∑ i ∈ s, (z i) ^ n • a i‖) atTop (𝓝 0) := by
    simpa using h.norm
  have hvnorm : Tendsto (fun n : ℕ =>
      ‖((z j)⁻¹) ^ n • ∑ i ∈ s, (z i) ^ n • a i‖) atTop (𝓝 0) := by
    refine hnorm.congr' ?_
    filter_upwards with n
    rw [norm_smul, norm_pow]
    have h1 : ‖(z j)⁻¹‖ = 1 := by rw [norm_inv, hzj, inv_one]
    rw [h1, one_pow, one_mul]
  have hv : Tendsto (fun n : ℕ =>
      ((z j)⁻¹) ^ n • ∑ i ∈ s, (z i) ^ n • a i) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hvnorm
  have hv' : Tendsto (fun k : ℕ => ∑ i ∈ s, ((z j)⁻¹ * z i) ^ k • a i) atTop (𝓝 0) := by
    refine hv.congr' ?_
    filter_upwards with k
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_smul, mul_pow]
  have hces := hv'.cesaro_smul
  have hrewrite : ∀ n : ℕ,
      (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n,
          ∑ i ∈ s, ((z j)⁻¹ * z i) ^ k • a i) =
        ∑ i ∈ s, ((n : ℂ)⁻¹ * ∑ k ∈ Finset.range n, ((z j)⁻¹ * z i) ^ k) • a i := by
    intro n
    calc (n : ℝ)⁻¹ • (∑ k ∈ Finset.range n,
            ∑ i ∈ s, ((z j)⁻¹ * z i) ^ k • a i)
        = ∑ k ∈ Finset.range n,
            (n : ℝ)⁻¹ • ∑ i ∈ s, ((z j)⁻¹ * z i) ^ k • a i := by rw [Finset.smul_sum]
      _ = ∑ k ∈ Finset.range n,
            ∑ i ∈ s, (n : ℝ)⁻¹ • (((z j)⁻¹ * z i) ^ k • a i) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.smul_sum]
      _ = ∑ i ∈ s,
            ∑ k ∈ Finset.range n, (n : ℝ)⁻¹ • (((z j)⁻¹ * z i) ^ k • a i) :=
            Finset.sum_comm
      _ = ∑ i ∈ s,
            ∑ k ∈ Finset.range n, ((n : ℂ)⁻¹ * ((z j)⁻¹ * z i) ^ k) • a i := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro k hk
            rw [hcoescale, Complex.ofReal_inv, Complex.ofReal_natCast, smul_smul]
      _ = ∑ i ∈ s,
            ((n : ℂ)⁻¹ * ∑ k ∈ Finset.range n, ((z j)⁻¹ * z i) ^ k) • a i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum, ← Finset.sum_smul]
  have hlim : Tendsto (fun n : ℕ =>
      ∑ i ∈ s, ((n : ℂ)⁻¹ * ∑ k ∈ Finset.range n, ((z j)⁻¹ * z i) ^ k) • a i)
      atTop (𝓝 (∑ i ∈ s, (if (z j)⁻¹ * z i = 1 then (1 : ℂ) else 0) • a i)) := by
    apply tendsto_finsetSum
    intro i hi
    have hzi : ‖z i‖ = 1 := hz i hi
    have hnorm2 : ‖(z j)⁻¹ * z i‖ = 1 := by rw [norm_mul, norm_inv, hzj, hzi]; simp
    exact (tendsto_inv_mul_geom_sum ((z j)⁻¹ * z i) hnorm2).smul_const (a i)
  have hces' : Tendsto (fun n : ℕ =>
      ∑ i ∈ s, ((n : ℂ)⁻¹ * ∑ k ∈ Finset.range n, ((z j)⁻¹ * z i) ^ k) • a i)
      atTop (𝓝 0) := by
    apply hces.congr'
    filter_upwards with n
    exact hrewrite n
  have hzero : (∑ i ∈ s, (if (z j)⁻¹ * z i = 1 then (1 : ℂ) else 0) • a i) = 0 :=
    tendsto_nhds_unique hlim hces'
  have hcollapse : (∑ i ∈ s, (if (z j)⁻¹ * z i = 1 then (1 : ℂ) else 0) • a i) = a j := by
    rw [Finset.sum_eq_single j]
    · rw [ite_eq_left (inv_mul_cancel₀ hzj0), one_smul]
    · intro i hi hij
      have hne : ¬ ((z j)⁻¹ * z i = 1) := by
        intro hc
        have hzi : z i = z j := by
          calc z i = z j * ((z j)⁻¹ * z i) := by field_simp
            _ = z j * 1 := by rw [hc]
            _ = z j := mul_one _
        exact hij (hinj i hi j hj hzi)
      rw [ite_eq_right hne, zero_smul]
    · intro hjnot; exact absurd hj hjnot
  rw [hcollapse] at hzero
  exact hzero

open scoped Matrix

/-- The coordinatewise real-to-complex inclusion `(ι → ℝ) →ₗ[ℝ] (ι → ℂ)`,
regarded as a real-linear map. It is an isometry for the sup norm and commutes
with matrix-vector multiplication, which lets the real exponential be compared
with the complexified one. -/
noncomputable def ofRealPi {ι : Type*} : (ι → ℝ) →ₗ[ℝ] (ι → ℂ) where
  toFun y := fun i => (y i : ℂ)
  map_add' := by intro a b; ext i; simp
  map_smul' := by intro c y; ext i; simp [Complex.ofReal_mul]

@[simp] lemma ofRealPi_apply {ι : Type*} (y : ι → ℝ) (i : ι) :
    ofRealPi y i = (y i : ℂ) := rfl

lemma norm_ofReal_complex (r : ℝ) : ‖(r : ℂ)‖ = ‖r‖ := by
  rw [Real.norm_eq_abs]; exact RCLike.norm_ofReal r

lemma ofRealPi_norm {ι : Type*} [Fintype ι] (y : ι → ℝ) :
    ‖ofRealPi y‖ = ‖y‖ := by
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    rw [ofRealPi_apply, norm_ofReal_complex]
    exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mp le_rfl i
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
    intro i
    calc ‖y i‖ = ‖(y i : ℂ)‖ := (norm_ofReal_complex _).symm
      _ = ‖ofRealPi y i‖ := by rw [ofRealPi_apply]
      _ ≤ ‖ofRealPi y‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mp le_rfl i

lemma ofRealPi_mulVec {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) (y : ι → ℝ) :
    ofRealPi (M *ᵥ y) = (M.map (algebraMap ℝ ℂ)) *ᵥ (ofRealPi y) := by
  ext i
  have h := RingHom.map_mulVec (algebraMap ℝ ℂ) M y i
  simpa [ofRealPi, Function.comp_def] using h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma ofRealPi_exp (M : Matrix ι ι ℝ) (t : ℝ) (y : ι → ℝ) :
    ofRealPi (NormedSpace.exp (t • (Matrix.toLin' M).toContinuousLinearMap) y) =
      NormedSpace.exp
        (t • (Matrix.toLin' (M.map (algebraMap ℝ ℂ))).toContinuousLinearMap) (ofRealPi y) := by
  have hstep : ∀ z : ι → ℝ,
      ofRealPi ((Matrix.toLin' M).toContinuousLinearMap z) =
        (Matrix.toLin' (M.map (algebraMap ℝ ℂ))).toContinuousLinearMap (ofRealPi z) := by
    intro z
    change ofRealPi (M *ᵥ z) = (M.map (algebraMap ℝ ℂ)) *ᵥ ofRealPi z
    exact ofRealPi_mulVec M z
  have hpow : ∀ n : ℕ, ∀ z : ι → ℝ,
      ofRealPi (((t • (Matrix.toLin' M).toContinuousLinearMap) ^ n) z) =
        ((t • (Matrix.toLin' (M.map (algebraMap ℝ ℂ))).toContinuousLinearMap) ^ n)
          (ofRealPi z) := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ']
      rw [mul_apply_eq_comp, _root_.smul_apply, map_smul]
      rw [hstep, ih z]
      rw [← _root_.smul_apply, ← mul_apply_eq_comp, ← pow_succ']
  have hseries : ∀ n : ℕ,
      ofRealPi (((n.factorial : ℝ)⁻¹) • (((t • (Matrix.toLin' M).toContinuousLinearMap) ^ n) y)) =
        ((n.factorial : ℂ)⁻¹) •
          (((t • (Matrix.toLin' (M.map (algebraMap ℝ ℂ))).toContinuousLinearMap) ^ n)
            (ofRealPi y)) := by
    intro n
    rw [map_smul, hpow n y, ← Complex.ofReal_natCast n.factorial, ← Complex.ofReal_inv]
    rfl
  have h1 : HasSum
      (fun n : ℕ => ofRealPi
        (((n.factorial : ℝ)⁻¹) • (((t • (Matrix.toLin' M).toContinuousLinearMap) ^ n) y)))
      (ofRealPi (NormedSpace.exp (t • (Matrix.toLin' M).toContinuousLinearMap) y)) := by
    have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ)
      (t • (Matrix.toLin' M).toContinuousLinearMap)
    have h2 := h.mapL (ContinuousLinearMap.apply ℝ (ι → ℝ) y)
    exact h2.mapL (ofRealPi.toContinuousLinearMap)
  have h2 : HasSum
      (fun n : ℕ => ((n.factorial : ℂ)⁻¹) •
        (((t • (Matrix.toLin' (M.map (algebraMap ℝ ℂ))).toContinuousLinearMap) ^ n)
          (ofRealPi y)))
      (NormedSpace.exp
        (t • (Matrix.toLin' (M.map (algebraMap ℝ ℂ))).toContinuousLinearMap) (ofRealPi y)) := by
    have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ)
      (t • (Matrix.toLin' (M.map (algebraMap ℝ ℂ))).toContinuousLinearMap)
    exact h.mapL (ContinuousLinearMap.apply ℂ (ι → ℂ) (ofRealPi y))
  have h3 : HasSum
      (fun n : ℕ => ofRealPi
        (((n.factorial : ℝ)⁻¹) • (((t • (Matrix.toLin' M).toContinuousLinearMap) ^ n) y)))
      (NormedSpace.exp
        (t • (Matrix.toLin' (M.map (algebraMap ℝ ℂ))).toContinuousLinearMap) (ofRealPi y)) :=
    h2.congr_fun (fun n => hseries n)
  exact h1.unique h3

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

/-- **The real Hurwitz decay theorem.** If every complex root of the
complexified characteristic polynomial of a real endomorphism `A` has negative
real part, then every trajectory `t ↦ exp (t A) x` of the linear flow tends to
zero at `+∞`.

This is the real reduction of `tendsto_exp_complex_apply`: choose a real basis,
complexify the coordinate matrix, apply the complex theorem there, and transport
the convergence back along the basis and the coordinatewise `ofReal` inclusion. -/
theorem tendsto_exp_of_isHurwitz (A : X →ₗ[ℝ] X) (hA : IsHurwitz A) (x : X) :
    Tendsto (fun t : ℝ => NormedSpace.exp (t • A.toContinuousLinearMap) x) atTop (𝓝 0) := by
  let n : ℕ := Module.finrank ℝ X
  let b : Basis (Fin n) ℝ X := Module.finBasis ℝ X
  let L : X ≃L[ℝ] (Fin n → ℝ) := b.equivFun.toContinuousLinearEquiv
  let M : Matrix (Fin n) (Fin n) ℝ := LinearMap.toMatrix b b A
  let g : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := (Matrix.toLin' M).toContinuousLinearMap
  let h : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
    (Matrix.toLin' (M.map (algebraMap ℝ ℂ))).toContinuousLinearMap
  have hg : g = L.conjContinuousAlgEquiv A.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro y
    have hrepr : M *ᵥ b.repr (L.symm y) = b.repr (A (L.symm y)) :=
      LinearMap.toMatrix_mulVec_repr b b A (L.symm y)
    have hLy : b.repr (L.symm y) = y := by
      rw [← Basis.equivFun_apply b (L.symm y)]
      exact b.equivFun.apply_symm_apply y
    rw [hLy] at hrepr
    change M *ᵥ y = L (A.toContinuousLinearMap (L.symm y))
    rw [hrepr]
    rw [← Basis.equivFun_apply b (A (L.symm y))]
    rfl
  have hchar : h.charpoly = A.charpoly.map (algebraMap ℝ ℂ) := by
    change (Matrix.toLin' (M.map (algebraMap ℝ ℂ))).charpoly = A.charpoly.map (algebraMap ℝ ℂ)
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map,
      ← LinearMap.charpoly_toMatrix (f := A) b]
  have hf : ∀ z : ℂ, h.charpoly.eval z = 0 → z.re < 0 := by
    intro z hz
    rw [hchar] at hz
    exact hA z hz
  have hcomplex : Tendsto (fun t : ℝ => NormedSpace.exp (t • h) (ofRealPi (L x))) atTop (𝓝 0) :=
    tendsto_exp_complex_apply (Matrix.toLin' (M.map (algebraMap ℝ ℂ))) hf (ofRealPi (L x))
  have hofreal : Tendsto (fun t : ℝ => ofRealPi (NormedSpace.exp (t • g) (L x))) atTop (𝓝 0) := by
    rw [show (fun t : ℝ => ofRealPi (NormedSpace.exp (t • g) (L x)))
        = fun t : ℝ => NormedSpace.exp (t • h) (ofRealPi (L x)) from
      funext (fun t => ofRealPi_exp M t (L x))]
    exact hcomplex
  have hmatrix : Tendsto (fun t : ℝ => NormedSpace.exp (t • g) (L x)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero] at hofreal ⊢
    refine hofreal.congr' ?_
    filter_upwards with t
    rw [ofRealPi_norm]
  have hLexp : ∀ t : ℝ, L (NormedSpace.exp (t • A.toContinuousLinearMap) x)
      = NormedSpace.exp (t • g) (L x) := by
    intro t
    have key := NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (L.conjContinuousAlgEquiv)
      (L.conjContinuousAlgEquiv).continuous (t • A.toContinuousLinearMap)
      ((NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _)
    have hcongr : (L.conjContinuousAlgEquiv) (t • A.toContinuousLinearMap) = t • g := by
      rw [map_smul, hg.symm]
    have := congrArg (fun f : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => f (L x)) key
    rw [hcongr] at this
    simpa [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply, g] using this
  have hfinal : Tendsto (fun t : ℝ => L (NormedSpace.exp (t • A.toContinuousLinearMap) x))
      atTop (𝓝 0) := by
    rw [show (fun t : ℝ => L (NormedSpace.exp (t • A.toContinuousLinearMap) x))
        = fun t : ℝ => NormedSpace.exp (t • g) (L x) from funext hLexp]
    exact hmatrix
  have hcomp := (L.symm.continuous.tendsto 0).comp hfinal
  rw [show L.symm (0 : Fin n → ℝ) = 0 from map_zero _] at hcomp
  simpa [Function.comp_def, L.symm_apply_apply] using hcomp

/-- **Lyapunov stability of a real Hurwitz flow.** A real endomorphism `A` whose
complexified characteristic polynomial has only roots in the open left
half-plane generates a flow `t ↦ exp (t A)` whose origin is stable on `[0, ∞)` in
the sense of `Filter.IsStableOn`.

The proof invokes the uniform boundedness principle on the family
`t ↦ exp (t A)` (`t ≥ 0`): the pointwise convergence of
`tendsto_exp_of_isHurwitz` yields pointwise boundedness, whence a uniform
operator-norm bound `‖exp (t A)‖ ≤ C` that gives the stability estimate. -/
theorem isStableOn_expFlow_of_isHurwitz (A : X →ₗ[ℝ] X) (hA : IsHurwitz A) :
    (𝓝 (0 : X)).IsStableOn
      (fun (t : ℝ) (x : X) => NormedSpace.exp (t • A.toContinuousLinearMap) x) (Set.Ici 0) := by
  have hpt : ∀ x : X, ∃ C, ∀ t : {t : ℝ // 0 ≤ t},
      ‖NormedSpace.exp (t.1 • A.toContinuousLinearMap) x‖ ≤ C := by
    intro x
    have hexpcont : Continuous (NormedSpace.exp : (X →L[ℝ] X) → (X →L[ℝ] X)) := by
      rw [← continuousOn_univ, ← show Metric.eball (0 : X →L[ℝ] X)
          (NormedSpace.expSeries ℝ (X →L[ℝ] X)).radius = Set.univ by
        rw [NormedSpace.expSeries_radius_eq_top]; simp]
      exact NormedSpace.continuousOn_exp (𝕂 := ℝ)
    have hcont : Continuous fun t : ℝ => NormedSpace.exp (t • A.toContinuousLinearMap) x :=
      (ContinuousLinearMap.apply ℝ X x).continuous.comp
        (hexpcont.comp (continuous_id.smul continuous_const))
    have hconv := tendsto_exp_of_isHurwitz A hA x
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hconv.eventually (Metric.ball_mem_nhds 0 one_pos))
    have hN' : ∀ t : ℝ, N ≤ t → ‖NormedSpace.exp (t • A.toContinuousLinearMap) x‖ < 1 := by
      intro t ht
      have h := hN t ht
      rwa [dist_zero_right] at h
    obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max C₁ 1, ?_⟩
    rintro ⟨t, ht⟩
    rcases lt_or_ge t N with h | h
    · exact (hC₁ t ⟨ht, h.le⟩).trans (le_max_left _ _)
    · exact (hN' t h).le.trans (le_max_right _ _)
  obtain ⟨C, hC⟩ := banach_steinhaus (g := fun t : {t : ℝ // 0 ≤ t} =>
      NormedSpace.exp (t.1 • A.toContinuousLinearMap)) hpt
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC ⟨0, le_refl 0⟩)
  have hC1 : 0 < C + 1 := by linarith
  intro s hs
  rw [Metric.mem_nhds_iff] at hs
  obtain ⟨ε, hεpos, hεs⟩ := hs
  refine ⟨Metric.ball (0 : X) (ε / (C + 1)), Metric.ball_mem_nhds _ (by positivity), ?_⟩
  intro t ht x hx
  apply hεs
  rw [Metric.mem_ball, dist_zero_right] at hx ⊢
  have hbound : ‖NormedSpace.exp (t • A.toContinuousLinearMap) x‖ ≤ C * ‖x‖ := by
    calc ‖NormedSpace.exp (t • A.toContinuousLinearMap) x‖
        = ‖(NormedSpace.exp (t • A.toContinuousLinearMap)) x‖ := rfl
      _ ≤ ‖NormedSpace.exp (t • A.toContinuousLinearMap)‖ * ‖x‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ C * ‖x‖ := mul_le_mul_of_nonneg_right (hC ⟨t, Set.mem_Ici.mp ht⟩) (norm_nonneg _)
  calc ‖NormedSpace.exp (t • A.toContinuousLinearMap) x‖ ≤ C * ‖x‖ := hbound
    _ ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left hx.le hCnn
    _ = ε * (C / (C + 1)) := by ring
    _ < ε * 1 := by
        apply mul_lt_mul_of_pos_left _ hεpos
        rw [div_lt_one hC1]; linarith
    _ = ε := by ring


/-- The operator norm of an endomorphism of a finite-dimensional real space is
controlled by its values on a basis: `‖T‖ ≤ ∑ i, ‖coord i‖ * ‖T (b i)‖`. This is
the elementary substitute for compactness of the unit ball in the finite
dimension argument that upgrades pointwise convergence to norm convergence. -/
theorem opNorm_le_sum_coord_mul {ι : Type*} [Fintype ι] (b : Basis ι ℝ X)
    (T : X →L[ℝ] X) :
    ‖T‖ ≤ ∑ i, ‖(b.coord i).toContinuousLinearMap‖ * ‖T (b i)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  · intro x
    have hx : ∑ i, (b.coord i x) • b i = x := by
      simpa only [Basis.coord_apply] using b.sum_repr x
    calc ‖T x‖ = ‖T (∑ i, (b.coord i x) • b i)‖ := by rw [hx]
      _ = ‖∑ i, (b.coord i x) • T (b i)‖ := by
            congr 1
            rw [map_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
      _ ≤ ∑ i, ‖(b.coord i x) • T (b i)‖ := norm_sum_le _ _
      _ = ∑ i, ‖b.coord i x‖ * ‖T (b i)‖ := by simp [norm_smul]
      _ ≤ ∑ i, (‖(b.coord i).toContinuousLinearMap‖ * ‖x‖) * ‖T (b i)‖ := by
            apply Finset.sum_le_sum
            intro i _
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            simpa using (b.coord i).toContinuousLinearMap.le_opNorm x
      _ = (∑ i, ‖(b.coord i).toContinuousLinearMap‖ * ‖T (b i)‖) * ‖x‖ := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => by ring

/-- **Operator-norm convergence of a Hurwitz flow.** For a real Hurwitz
endomorphism `A` the operator norms `‖exp (t A)‖` tend to zero at `+∞`, not just
each orbit. The finite-dimensional argument writes an arbitrary vector in a basis
and bounds the operator norm by the sum of the norms of the images of the basis
vectors, each of which tends to zero by `tendsto_exp_of_isHurwitz`. -/
theorem tendsto_norm_exp_of_isHurwitz (A : X →ₗ[ℝ] X) (hA : IsHurwitz A) :
    Tendsto (fun t : ℝ => ‖NormedSpace.exp (t • A.toContinuousLinearMap)‖) atTop (𝓝 0) := by
  classical
  let b : Basis (Fin (Module.finrank ℝ X)) ℝ X := Module.finBasis ℝ X
  have hterm : ∀ i, Tendsto (fun t : ℝ =>
      ‖(b.coord i).toContinuousLinearMap‖ *
        ‖NormedSpace.exp (t • A.toContinuousLinearMap) (b i)‖) atTop (𝓝 0) := by
    intro i
    have h := ((tendsto_exp_of_isHurwitz A hA (b i)).norm).const_mul
      (‖(b.coord i).toContinuousLinearMap‖)
    simpa using h
  have hsum : Tendsto (fun t : ℝ => ∑ i,
      ‖(b.coord i).toContinuousLinearMap‖ *
        ‖NormedSpace.exp (t • A.toContinuousLinearMap) (b i)‖) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun i _ => hterm i)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0)) hsum ?_ ?_
  · filter_upwards with t
    exact norm_nonneg _
  · filter_upwards with t
    exact opNorm_le_sum_coord_mul b _

/-- The natural-power formula for the exponential in a real Banach algebra,
stated with the natural scalar action so that no `NormedAlgebra ℚ` instance is
required. -/
lemma exp_nsmul_real {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    (n : ℕ) (x : 𝔸) : NormedSpace.exp (n • x) = NormedSpace.exp x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [succ_nsmul, NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ)
        ((Commute.refl x).smul_left n)
        ((NormedSpace.expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
        ((NormedSpace.expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _), ih, pow_succ]

/-- **Geometric decay from one small step.** If `T > 0` and `‖exp (T A)‖ ≤ 1/2`
while `exp (s A)` is bounded by `B` for `s ∈ [0, T]`, then the operator norm of
`exp (t A)` decays geometrically: writing `t = n T + s` with `n = ⌊t/T⌋₊` and
`s ∈ [0, T)`, the semigroup law factorises `exp (t A) = exp (T A)^n exp (s A)` and
the first factor is bounded by `(1/2)^n`. -/
theorem norm_exp_le_mul_pow_floor (A : X →ₗ[ℝ] X) {T B : ℝ} (hTpos : 0 < T)
    (hB : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ‖NormedSpace.exp (s • A.toContinuousLinearMap)‖ ≤ B)
    (hhalf : ‖NormedSpace.exp (T • A.toContinuousLinearMap)‖ ≤ (1 : ℝ) / 2)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖NormedSpace.exp (t • A.toContinuousLinearMap)‖ ≤
      B * (1 / 2 : ℝ) ^ (⌊t / T⌋₊) := by
  set n : ℕ := ⌊t / T⌋₊ with hn
  set s : ℝ := t - n * T with hs
  have hnt : (n : ℝ) ≤ t / T := by
    rw [hn]; exact Nat.floor_le (div_nonneg ht hTpos.le)
  have hnt' : t / T < (n : ℝ) + 1 := by
    rw [hn]; exact Nat.lt_floor_add_one (t / T)
  have hnT_le : (n : ℝ) * T ≤ t := by
    have := mul_le_mul_of_nonneg_right hnt hTpos.le
    rwa [div_mul_cancel₀ t hTpos.ne'] at this
  have ht_lt : t < ((n : ℝ) + 1) * T := by
    have := mul_lt_mul_of_pos_right hnt' hTpos
    rwa [div_mul_cancel₀ t hTpos.ne'] at this
  have hs0 : 0 ≤ s := by rw [hs]; linarith
  have hsT : s < T := by rw [hs]; nlinarith [ht_lt]
  have ht_eq : t = (n : ℝ) * T + s := by rw [hs]; ring
  have hcomm : Commute (((n : ℝ) * T) • A.toContinuousLinearMap)
      (s • A.toContinuousLinearMap) :=
    ((Commute.refl A.toContinuousLinearMap).smul_left ((n : ℝ) * T)).smul_right s
  have hdec : NormedSpace.exp (t • A.toContinuousLinearMap) =
      (NormedSpace.exp (T • A.toContinuousLinearMap)) ^ n *
        NormedSpace.exp (s • A.toContinuousLinearMap) := by
    have hsplit : t • A.toContinuousLinearMap =
        ((n : ℝ) * T) • A.toContinuousLinearMap + s • A.toContinuousLinearMap := by
      rw [← add_smul, ht_eq]
    rw [hsplit]
    rw [NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℝ) hcomm
      ((NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _)
      ((NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _)]
    rw [show ((n : ℝ) * T) • A.toContinuousLinearMap =
        n • (T • A.toContinuousLinearMap) by rw [mul_smul, Nat.cast_smul_eq_nsmul],
      exp_nsmul_real]
  have hPown : ‖(NormedSpace.exp (T • A.toContinuousLinearMap)) ^ n‖ ≤
      (1 / 2 : ℝ) ^ n := by
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · rw [hn0, pow_zero, pow_zero]
      exact ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun x => by simp)
    · calc ‖(NormedSpace.exp (T • A.toContinuousLinearMap)) ^ n‖
          ≤ ‖NormedSpace.exp (T • A.toContinuousLinearMap)‖ ^ n :=
            norm_pow_le' _ hnpos
        _ ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ (norm_nonneg _) hhalf n
  calc ‖NormedSpace.exp (t • A.toContinuousLinearMap)‖
      = ‖(NormedSpace.exp (T • A.toContinuousLinearMap)) ^ n *
          NormedSpace.exp (s • A.toContinuousLinearMap)‖ := by rw [hdec]
    _ ≤ ‖(NormedSpace.exp (T • A.toContinuousLinearMap)) ^ n‖ *
          ‖NormedSpace.exp (s • A.toContinuousLinearMap)‖ := norm_mul_le _ _
    _ ≤ ((1 / 2 : ℝ) ^ n) * B :=
          mul_le_mul hPown (hB s ⟨hs0, hsT.le⟩) (norm_nonneg _) (by positivity)
    _ = B * (1 / 2 : ℝ) ^ n := by ring

/-- **Quantitative exponential decay of a real Hurwitz flow.** For a real
endomorphism `A` of a finite-dimensional real normed space all of whose complex
eigenvalues lie in the open left half-plane, there are constants `C > 0` and
`γ > 0` with `‖exp (t A)‖ ≤ C * exp (-γ t)` for every `t ≥ 0`.

The proof chooses `T > 0` with `‖exp (T A)‖ ≤ 1/2` from the operator-norm
convergence `tendsto_norm_exp_of_isHurwitz`; the semigroup law then decomposes
`t = n T + s` and the geometric factor `(1/2)^n` is turned into `exp (-γ t)` with
`γ = log 2 / T`, while continuity on `[0, T]` bounds `exp (s A)` uniformly. -/
theorem exists_exponential_norm_bound_of_isHurwitz (A : X →ₗ[ℝ] X) (hA : IsHurwitz A) :
    ∃ C : ℝ, 0 < C ∧ ∃ γ : ℝ, 0 < γ ∧
      ∀ t : ℝ, 0 ≤ t →
        ‖NormedSpace.exp (t • A.toContinuousLinearMap)‖ ≤ C * Real.exp (-γ * t) := by
  have hnorm := tendsto_norm_exp_of_isHurwitz A hA
  have hhalf : ∀ᶠ t : ℝ in atTop,
      ‖NormedSpace.exp (t • A.toContinuousLinearMap)‖ ≤ (1 : ℝ) / 2 := by
    filter_upwards [hnorm.eventually
      (Metric.ball_mem_nhds (0 : ℝ) (show (0 : ℝ) < 1 / 2 by norm_num))]
      with t ht
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at ht
    exact ht.le
  obtain ⟨T, hT1, hTle⟩ := ((eventually_ge_atTop (1 : ℝ)).and hhalf).exists
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT1
  have hexpcont : Continuous (NormedSpace.exp : (X →L[ℝ] X) → (X →L[ℝ] X)) := by
    rw [← continuousOn_univ, ← show Metric.eball (0 : X →L[ℝ] X)
        (NormedSpace.expSeries ℝ (X →L[ℝ] X)).radius = Set.univ by
      rw [NormedSpace.expSeries_radius_eq_top]; simp]
    exact NormedSpace.continuousOn_exp (𝕂 := ℝ)
  have hcont : Continuous (fun t : ℝ => NormedSpace.exp (t • A.toContinuousLinearMap)) :=
    hexpcont.comp (continuous_id.smul continuous_const)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
  have hBnn : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 ⟨le_refl 0, hTpos.le⟩)
  refine ⟨2 * max B 1, mul_pos two_pos (lt_of_lt_of_le one_pos (le_max_right B 1)),
    Real.log 2 / T, div_pos (Real.log_pos (by norm_num)) hTpos, ?_⟩
  intro t ht
  have hγpos : 0 < Real.log 2 / T :=
    div_pos (Real.log_pos (by norm_num)) hTpos
  have hgeom : (1 / 2 : ℝ) ^ (⌊t / T⌋₊) ≤ 2 * Real.exp (-(Real.log 2 / T) * t) := by
    have hlt_floor : t / T < (⌊t / T⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one (t / T)
    have ht_lt : t < ((⌊t / T⌋₊ : ℝ) + 1) * T := by
      have := mul_lt_mul_of_pos_right hlt_floor hTpos
      rwa [div_mul_cancel₀ t hTpos.ne'] at this
    have hkey : (Real.log 2 / T) * t < ((⌊t / T⌋₊ : ℝ) + 1) * Real.log 2 := by
      calc (Real.log 2 / T) * t < (Real.log 2 / T) * (((⌊t / T⌋₊ : ℝ) + 1) * T) :=
            mul_lt_mul_of_pos_left ht_lt hγpos
        _ = ((⌊t / T⌋₊ : ℝ) + 1) * Real.log 2 := by
            field_simp
    have hexp_lt : Real.exp (-(((⌊t / T⌋₊ : ℝ) + 1) * Real.log 2)) <
        Real.exp (-(Real.log 2 / T) * t) := by
      apply Real.exp_lt_exp.mpr
      linarith
    have hexp_eq : Real.exp (-(((⌊t / T⌋₊ : ℝ) + 1) * Real.log 2)) =
        (1 / 2 : ℝ) ^ (⌊t / T⌋₊ + 1) := by
      rw [show -(((⌊t / T⌋₊ : ℝ) + 1) * Real.log 2) =
          ((⌊t / T⌋₊ + 1 : ℕ) : ℝ) * (-(Real.log 2)) by push_cast; ring]
      rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hexp_eq] at hexp_lt
    calc (1 / 2 : ℝ) ^ ⌊t / T⌋₊ = 2 * (1 / 2 : ℝ) ^ (⌊t / T⌋₊ + 1) := by
          rw [pow_succ]; ring
      _ ≤ 2 * Real.exp (-(Real.log 2 / T) * t) :=
          mul_le_mul_of_nonneg_left hexp_lt.le (by norm_num)
  calc ‖NormedSpace.exp (t • A.toContinuousLinearMap)‖
      ≤ B * (1 / 2 : ℝ) ^ (⌊t / T⌋₊) := norm_exp_le_mul_pow_floor A hTpos hB hTle ht
    _ ≤ max B 1 * (2 * Real.exp (-(Real.log 2 / T) * t)) :=
          mul_le_mul (le_max_left B 1) hgeom (by positivity)
            (le_trans hBnn (le_max_left B 1))
    _ = 2 * max B 1 * Real.exp (-(Real.log 2 / T) * t) := by ring

/-! ## The Hurwitz (stable) subspace of a real endomorphism

For a real endomorphism `A` of a finite-dimensional real vector space the stable
subspace `X_g(A)` (Trentelman–Stoervogel–Hautus, Definition 2.13 and the
decomposition used in Sections 4.6 and 6) is the direct sum of the generalized
eigenspaces of the complexification of `A` at the eigenvalues with negative real
part. Because that set of eigenvalues is invariant under complex conjugation, the
corresponding complex subspace is the complexification of a canonical real
subspace; we realize it by transporting along a real basis of the state space.

The construction uses the existing complex generalized-eigenspace API
(`Module.End.maxGenEigenspace`) on the coordinate space `Fin n → ℂ` and the
real-coordinate transport `ofRealPi` (used already by
`LinearMap.tendsto_exp_of_isHurwitz`). Concretely:

* `hurwitzMatrix A` is the real matrix of `A` in the canonical basis
  `Module.finBasis ℝ X`.
* `hurwitzComplexSubspace A` is the sum of the generalized eigenspaces of the
  complexified matrix at the eigenvalues with negative real part.
* `hurwitzSubspace A` pulls that complex subspace back to `X` along the real
  coordinates `x ↦ ofRealPi (b.equivFun x)`.

`LinearMap.map_hurwitzSubspace_le` proves that the stable subspace is
`A`-invariant, and `LinearMap.tendsto_exp_restrict_hurwitzSubspace` proves that
the exponential flow decays on it. The zero operator has trivial stable subspace
and the zero-dimensional case is the whole space, both made explicit below. -/

section HurwitzSubspace

open scoped Matrix

/-- The matrix of a real endomorphism `A` with respect to the canonical basis
`Module.finBasis ℝ X` of the finite-dimensional real state space. This is the
coordinate representation used to complexify `A` term by term. -/
noncomputable def hurwitzMatrix (A : X →ₗ[ℝ] X) :
    Matrix (Fin (Module.finrank ℝ X)) (Fin (Module.finrank ℝ X)) ℝ :=
  LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ X) A

/-- The complex **stable subspace** of `A`: the direct sum of the generalized
eigenspaces of the complexified coordinate operator at the eigenvalues with
negative real part. This is the coordinate form of `X_g(A)` over `ℂ`. -/
noncomputable def hurwitzComplexSubspace (A : X →ₗ[ℝ] X) :
    Submodule ℂ (Fin (Module.finrank ℝ X) → ℂ) :=
  ⨆ μ : {μ : ℂ // μ.re < 0},
    Module.End.maxGenEigenspace
      (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) μ.1

/-- The **Hurwitz (stable) subspace** of a real endomorphism `A`. A vector `x`
lies in it exactly when its real coordinates `ofRealPi (b.equivFun x)` lie in the
complex stable subspace `hurwitzComplexSubspace A`. This is the canonical real
form of `X_g(A)`, and agrees with the direct sum of the real generalized
eigenspaces for the eigenvalues with negative real part. -/
noncomputable def hurwitzSubspace (A : X →ₗ[ℝ] X) : Submodule ℝ X :=
  ((hurwitzComplexSubspace A).restrictScalars ℝ).comap
    (ofRealPi.comp (Module.finBasis ℝ X).equivFun.toLinearMap)

/-- Membership in the Hurwitz subspace, in terms of the real-coordinate
transport `ofRealPi`: `x ∈ hurwitzSubspace A` iff the complex coordinates of `x`
lie in `hurwitzComplexSubspace A`. -/
theorem mem_hurwitzSubspace {A : X →ₗ[ℝ] X} {x : X} :
    x ∈ hurwitzSubspace A ↔
      ofRealPi ((Module.finBasis ℝ X).equivFun x) ∈ hurwitzComplexSubspace A := by
  rw [hurwitzSubspace, Submodule.mem_comap, Submodule.restrictScalars_mem]
  rfl

/-- The complex stable subspace is invariant under the complexified coordinate
operator: it is a supremum of generalized eigenspaces, each of which is mapped
into itself. -/
theorem map_hurwitzComplexSubspace_le (A : X →ₗ[ℝ] X) :
    Submodule.map (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ)))
        (hurwitzComplexSubspace A) ≤ hurwitzComplexSubspace A := by
  rw [hurwitzComplexSubspace, Submodule.map_iSup]
  refine iSup_le fun μ => ?_
  rw [Submodule.map_le_iff_le_comap]
  intro y hy
  exact Submodule.mem_iSup_of_mem μ
    (Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) μ.1 hy)

/-- **The Hurwitz subspace is `A`-invariant**: `A (hurwitzSubspace A) ≤
hurwitzSubspace A`. The complexified matrix acts on the complex stable subspace
by `map_hurwitzComplexSubspace_le`; `ofRealPi` intertwines the real matrix action
with the complexified one, so the pull-back is invariant as well. -/
theorem map_hurwitzSubspace_le (A : X →ₗ[ℝ] X) :
    Submodule.map A (hurwitzSubspace A) ≤ hurwitzSubspace A := by
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  rw [Submodule.mem_comap]
  rw [mem_hurwitzSubspace] at hx ⊢
  have hcoord : (Module.finBasis ℝ X).equivFun (A x) =
      (hurwitzMatrix A) *ᵥ ((Module.finBasis ℝ X).equivFun x) := by
    rw [Basis.equivFun_apply, Basis.equivFun_apply]
    exact (LinearMap.toMatrix_mulVec_repr (Module.finBasis ℝ X) (Module.finBasis ℝ X) A x).symm
  rw [hcoord, ofRealPi_mulVec]
  rw [← Matrix.toLin'_apply]
  exact map_hurwitzComplexSubspace_le A ⟨_, hx, rfl⟩

/-- **Restriction to the Hurwitz subspace of a Hurwitz operator is Hurwitz.**
If `A` is Hurwitz then its restriction to its stable subspace
`hurwitzSubspace A` is again Hurwitz. The proof uses the spectrum-transfer
corollary `charpoly_restrict_dvd_of_invariant`: the characteristic polynomial of
the restriction divides that of `A`, so every complex root of the restricted
characteristic polynomial is a root of the ambient one and hence has negative
real part.

This is the invariant-submodule half of the bridge lifting the Hurwitz-subspace
foundation into the stabilizable/detectable decompositions: the stable subspace
inherits the stability of the ambient operator. -/
theorem isHurwitz_restrict_of_hurwitzSubspace (A : X →ₗ[ℝ] X) (hA : IsHurwitz A) :
    IsHurwitz (LinearMap.restrict A (p := hurwitzSubspace A) (q := hurwitzSubspace A)
      fun x hx => map_hurwitzSubspace_le A ⟨x, hx, rfl⟩) := by
  have hS : ∀ x ∈ hurwitzSubspace A, A x ∈ hurwitzSubspace A :=
    fun x hx => map_hurwitzSubspace_le A ⟨x, hx, rfl⟩
  change IsHurwitz (A.restrict hS)
  exact isHurwitz_restrict_of_invariant A (hurwitzSubspace A) hS hA

/-- **Decay on the complex stable subspace.** For any vector `z` in the complex
stable subspace of `A`, the complex coordinate flow `t ↦ exp (t A_ℂ) z` tends to
zero. Writing `z` as a finite sum of vectors in generalized eigenspaces for the
stable eigenvalues, each summand decays by `tendsto_exp_apply_of_nilpotent`. -/
theorem tendsto_exp_of_mem_hurwitzComplexSubspace (A : X →ₗ[ℝ] X)
    {z : Fin (Module.finrank ℝ X) → ℂ} (hz : z ∈ hurwitzComplexSubspace A) :
    Tendsto (fun t : ℝ =>
      NormedSpace.exp (t • (Matrix.toLin'
        ((hurwitzMatrix A).map (algebraMap ℝ ℂ))).toContinuousLinearMap) z)
      atTop (𝓝 0) := by
  let f : (Fin (Module.finrank ℝ X) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℝ X) → ℂ) :=
    Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))
  obtain ⟨s, hs⟩ := (Submodule.mem_iSup_iff_exists_finset
    (p := fun μ : {μ : ℂ // μ.re < 0} => Module.End.maxGenEigenspace f μ.1)).mp hz
  obtain ⟨zμ, hzμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum
    (fun μ : {μ : ℂ // μ.re < 0} => Module.End.maxGenEigenspace f μ.1) z).mp hs
  rw [hzμ.symm]
  have hmap : (fun t : ℝ => NormedSpace.exp (t • f.toContinuousLinearMap)
        (∑ μ ∈ s, (zμ μ : Fin (Module.finrank ℝ X) → ℂ))) =
      fun t => ∑ μ ∈ s, NormedSpace.exp (t • f.toContinuousLinearMap)
        (zμ μ : Fin (Module.finrank ℝ X) → ℂ) := by
    funext t; rw [map_sum]
  rw [hmap]
  have hfin := tendsto_finsetSum (x := atTop) s
    (f := fun (μ : {μ : ℂ // μ.re < 0}) (t : ℝ) =>
      NormedSpace.exp (t • f.toContinuousLinearMap) (zμ μ : Fin (Module.finrank ℝ X) → ℂ))
    (a := fun _ : {μ : ℂ // μ.re < 0} => (0 : Fin (Module.finrank ℝ X) → ℂ))
    (fun μ _ => by
      by_cases h0 : (zμ μ : Fin (Module.finrank ℝ X) → ℂ) = 0
      · rw [h0]; simp
      · obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace f μ.1 (zμ μ)).mp (zμ μ).2
        exact tendsto_exp_apply_of_nilpotent f μ.1 μ.2 hk)
  simpa using hfin

/-- **The exponential flow decays on the Hurwitz subspace.** If `x` lies in the
stable subspace of `A`, then `t ↦ exp (t A) x` tends to zero at `+∞`. This is the
restriction of the general Hurwitz decay theorem
`LinearMap.tendsto_exp_of_isHurwitz` to the stable spectral part; it is the
qualitative form of the accepted quantitative bound
`LinearMap.exists_exponential_norm_bound_of_isHurwitz` applied to that part. -/
theorem tendsto_exp_restrict_hurwitzSubspace (A : X →ₗ[ℝ] X) {x : X}
    (hx : x ∈ hurwitzSubspace A) :
    Tendsto (fun t : ℝ => NormedSpace.exp (t • A.toContinuousLinearMap) x) atTop (𝓝 0) := by
  classical
  let n : ℕ := Module.finrank ℝ X
  let b : Basis (Fin n) ℝ X := Module.finBasis ℝ X
  let L : X ≃L[ℝ] (Fin n → ℝ) := b.equivFun.toContinuousLinearEquiv
  let M : Matrix (Fin n) (Fin n) ℝ := LinearMap.toMatrix b b A
  let g : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := (Matrix.toLin' M).toContinuousLinearMap
  let h : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
    (Matrix.toLin' (M.map (algebraMap ℝ ℂ))).toContinuousLinearMap
  have hLx : L x = (Module.finBasis ℝ X).equivFun x := rfl
  have hxy : ofRealPi (L x) ∈ hurwitzComplexSubspace A := by
    rw [mem_hurwitzSubspace] at hx
    rwa [hLx]
  have hcomplex : Tendsto (fun t : ℝ => NormedSpace.exp (t • h) (ofRealPi (L x))) atTop (𝓝 0) :=
    tendsto_exp_of_mem_hurwitzComplexSubspace A hxy
  have hg : g = L.conjContinuousAlgEquiv A.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro y
    have hrepr : M *ᵥ b.repr (L.symm y) = b.repr (A (L.symm y)) :=
      LinearMap.toMatrix_mulVec_repr b b A (L.symm y)
    have hLy : b.repr (L.symm y) = y := by
      rw [← Basis.equivFun_apply b (L.symm y)]
      exact b.equivFun.apply_symm_apply y
    rw [hLy] at hrepr
    change M *ᵥ y = L (A.toContinuousLinearMap (L.symm y))
    rw [hrepr]
    rw [← Basis.equivFun_apply b (A (L.symm y))]
    rfl
  have hofreal : Tendsto (fun t : ℝ => ofRealPi (NormedSpace.exp (t • g) (L x))) atTop (𝓝 0) := by
    rw [show (fun t : ℝ => ofRealPi (NormedSpace.exp (t • g) (L x)))
        = fun t : ℝ => NormedSpace.exp (t • h) (ofRealPi (L x)) from
      funext (fun t => ofRealPi_exp M t (L x))]
    exact hcomplex
  have hmatrix : Tendsto (fun t : ℝ => NormedSpace.exp (t • g) (L x)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero] at hofreal ⊢
    refine hofreal.congr' ?_
    filter_upwards with t
    rw [ofRealPi_norm]
  have hLexp : ∀ t : ℝ, L (NormedSpace.exp (t • A.toContinuousLinearMap) x)
      = NormedSpace.exp (t • g) (L x) := by
    intro t
    have key := NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (L.conjContinuousAlgEquiv)
      (L.conjContinuousAlgEquiv).continuous (t • A.toContinuousLinearMap)
      ((NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _)
    have hcongr : (L.conjContinuousAlgEquiv) (t • A.toContinuousLinearMap) = t • g := by
      rw [map_smul, hg.symm]
    have := congrArg (fun f : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => f (L x)) key
    rw [hcongr] at this
    simpa [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply, g] using this
  have hfinal : Tendsto (fun t : ℝ => L (NormedSpace.exp (t • A.toContinuousLinearMap) x))
      atTop (𝓝 0) := by
    rw [show (fun t : ℝ => L (NormedSpace.exp (t • A.toContinuousLinearMap) x))
        = fun t : ℝ => NormedSpace.exp (t • g) (L x) from funext hLexp]
    exact hmatrix
  have hcomp := (L.symm.continuous.tendsto 0).comp hfinal
  rw [show L.symm (0 : Fin n → ℝ) = 0 from map_zero _] at hcomp
  simpa [Function.comp_def, L.symm_apply_apply] using hcomp

/-- On a zero-dimensional real space every submodule is the whole space, so the
Hurwitz subspace is `⊤` in the zero-dimensional case. -/
theorem hurwitzSubspace_eq_top_of_subsingleton [Subsingleton X] (A : X →ₗ[ℝ] X) :
    hurwitzSubspace A = ⊤ :=
  Subsingleton.elim _ _

/-- The generalized eigenspace of the zero endomorphism at a nonzero eigenvalue
is trivial: `(0 - μ • 1)^k = (-μ)^k • 1` is an invertible scalar multiple of the
identity. -/
theorem maxGenEigenspace_zero_of_ne_zero {E : Type*} [AddCommGroup E] [Module ℂ E]
    {μ : ℂ} (hμ : μ ≠ 0) :
    Module.End.maxGenEigenspace (0 : E →ₗ[ℂ] E) μ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace (0 : E →ₗ[ℂ] E) μ x).mp hx
  have hc : (0 : E →ₗ[ℂ] E) - μ • (1 : E →ₗ[ℂ] E) = (-μ) • (1 : E →ₗ[ℂ] E) := by
    ext y; simp
  have h1 : (((0 : E →ₗ[ℂ] E) - μ • (1 : E →ₗ[ℂ] E)) ^ k) =
      ((-μ : ℂ) ^ k) • (1 : E →ₗ[ℂ] E) := by
    rw [hc, smul_pow, one_pow]
  have h2 := congrArg (fun f : E →ₗ[ℂ] E => f x) h1
  rw [h2] at hk
  have hk' : ((-μ : ℂ) ^ k) • x = 0 := hk
  exact (smul_eq_zero.mp hk').resolve_left (pow_ne_zero k (neg_ne_zero.mpr hμ))

/-- The coordinatewise real-to-complex inclusion `ofRealPi` is injective. -/
theorem ofRealPi_eq_zero {ι : Type*} {y : ι → ℝ} (h : ofRealPi y = 0) : y = 0 := by
  funext i
  have := congrFun h i
  simpa [ofRealPi] using this

/-- **The zero operator has trivial stable subspace.** The only eigenvalue of the
zero operator is `0`, which is not in the open left half-plane, so
`hurwitzSubspace 0 = ⊥`; equivalently, the constant flow `exp (t • 0) x = x` does
not decay for nonzero `x`. -/
theorem hurwitzSubspace_zero : hurwitzSubspace (0 : X →ₗ[ℝ] X) = ⊥ := by
  have hsub : hurwitzComplexSubspace (0 : X →ₗ[ℝ] X) = ⊥ := by
    rw [hurwitzComplexSubspace, iSup_eq_bot]
    intro μ
    have hM : hurwitzMatrix (0 : X →ₗ[ℝ] X) = 0 := by simp [hurwitzMatrix]
    rw [hM]
    simp only [Matrix.map_zero, map_zero]
    exact maxGenEigenspace_zero_of_ne_zero (by
      intro h
      have hlt : μ.1.re < 0 := μ.2
      rw [h] at hlt
      simp at hlt)
  rw [hurwitzSubspace, hsub, Submodule.restrictScalars_bot]
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_comap] at hx
  simp only [Submodule.mem_bot, LinearMap.comp_apply] at hx
  have hy : (Module.finBasis ℝ X).equivFun x = 0 := ofRealPi_eq_zero hx
  exact (Module.finBasis ℝ X).equivFun.injective (by rw [hy, map_zero])

end HurwitzSubspace

/-! ## Stabilizable and detectable spectral subspaces

This section formalises the two spectral subspaces needed for the full geometric
external-stabilization converse of Trentelman–Stoorvogel–Hautus, Chapter 6:

* `LinearMap.stabilizableSubspace A B = X_g(A) + ⟨A | im B⟩`, the **stabilizable
  subspace** `Xstab` of Theorem 4.26: the states from which a stable trajectory
  can be produced. It is the sum of the accepted stable subspace
  `hurwitzSubspace A` and the reachable subspace `reachableSubspace A B`.
* `LinearMap.detectableSubspace C A = X_b(A) ∩ ⟨ker C | A⟩`, the **smallest
  detectability subspace** `Xdet` of Definition 5.10 / Theorem 5.15: the
  undetectable part of the state space, the intersection of the antistable
  spectral subspace `unstableSubspace A` with the unobservable subspace
  `unobservableSubspace C A`.

The three spectral objects are kept distinct: the **stable subspace**
`hurwitzSubspace A = X_g(A)` is the negative-real-part generalized eigenspace,
the **stabilizable subspace** is `X_g(A) + ⟨A | im B⟩`, and the **detectable
subspace** is `X_b(A) ∩ ⟨ker C | A⟩`. Both new subspaces are `A`-invariant.

Following the source we also record the dual pair of "complementary" dynamics
that make these subspaces useful:

* `LinearMap.isHurwitz_on_stabilizableComplement`: for a stabilizable pair the
  induced map on `X / ⟨A | im B⟩` — the uncontrollable complement — is Hurwitz
  (Theorem 4.30 (ii));
* `LinearMap.isHurwitz_on_detectableComplement`: for a detectable pair the
  restriction of `A` to the unobservable complement `⟨ker C | A⟩` is Hurwitz
  (Theorem 5.16 (ii)).

These are the geometric forms of the PBH necessity statements
`isStabilizable_converse_of_uncontrollableEigenvalue` and
`isDetectable_converse_of_unobservableEigenvalue`. No claim about Corollary 6.22
itself is made here.

Source: Trentelman–Stoorvogel–Hautus, Theorem 4.26, Theorem 4.30, Theorem 5.15
and Theorem 5.16 (PDF pages 81, 115 and 156 region, printed Sections 4.6
and 5.2). -/

section StabilizableDetectable

open scoped Matrix

/-- The complex **antistable subspace** of `A`: the sum of the generalized
eigenspaces of the complexified coordinate operator at the eigenvalues with
nonnegative real part. It is the spectral complement of `hurwitzComplexSubspace`
inside the complexified state space. -/
noncomputable def unstableComplexSubspace (A : X →ₗ[ℝ] X) :
    Submodule ℂ (Fin (Module.finrank ℝ X) → ℂ) :=
  ⨆ μ : {μ : ℂ // ¬ μ.re < 0},
    Module.End.maxGenEigenspace
      (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) μ.1

/-- The **antistable (unstable) subspace** `X_b(A)` of a real endomorphism `A`.
A vector `x` lies in it exactly when its real coordinates `ofRealPi (b.equivFun x)`
lie in the complex antistable subspace `unstableComplexSubspace A`. This is the
spectral object complementary to `hurwitzSubspace A = X_g(A)`; the precise direct
sum decomposition `X = X_g(A) ⊕ X_b(A)` is not needed by the results below and is
not claimed here. -/
noncomputable def unstableSubspace (A : X →ₗ[ℝ] X) : Submodule ℝ X :=
  ((unstableComplexSubspace A).restrictScalars ℝ).comap
    (ofRealPi.comp (Module.finBasis ℝ X).equivFun.toLinearMap)

/-- Membership in the antistable subspace, in terms of the real-coordinate
transport `ofRealPi`. -/
theorem mem_unstableSubspace {A : X →ₗ[ℝ] X} {x : X} :
    x ∈ unstableSubspace A ↔
      ofRealPi ((Module.finBasis ℝ X).equivFun x) ∈ unstableComplexSubspace A := by
  rw [unstableSubspace, Submodule.mem_comap, Submodule.restrictScalars_mem]
  rfl

/-- The complex antistable subspace is invariant under the complexified
coordinate operator: it is a supremum of generalized eigenspaces. -/
theorem map_unstableComplexSubspace_le (A : X →ₗ[ℝ] X) :
    Submodule.map (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ)))
        (unstableComplexSubspace A) ≤ unstableComplexSubspace A := by
  rw [unstableComplexSubspace, Submodule.map_iSup]
  refine iSup_le fun μ => ?_
  rw [Submodule.map_le_iff_le_comap]
  intro y hy
  exact Submodule.mem_iSup_of_mem μ
    (Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl _) μ.1 hy)

/-- **The antistable subspace is `A`-invariant**: `A (unstableSubspace A) ≤
unstableSubspace A`. The proof mirrors `map_hurwitzSubspace_le`: the complexified
matrix acts on the complex antistable subspace and `ofRealPi` intertwines the
real and complexified actions. -/
theorem map_unstableSubspace_le (A : X →ₗ[ℝ] X) :
    Submodule.map A (unstableSubspace A) ≤ unstableSubspace A := by
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  rw [Submodule.mem_comap]
  rw [mem_unstableSubspace] at hx ⊢
  have hcoord : (Module.finBasis ℝ X).equivFun (A x) =
      (hurwitzMatrix A) *ᵥ ((Module.finBasis ℝ X).equivFun x) := by
    rw [Basis.equivFun_apply, Basis.equivFun_apply]
    exact (LinearMap.toMatrix_mulVec_repr (Module.finBasis ℝ X) (Module.finBasis ℝ X) A x).symm
  rw [hcoord, ofRealPi_mulVec]
  rw [← Matrix.toLin'_apply]
  exact map_unstableComplexSubspace_le A ⟨_, hx, rfl⟩

/-- The **stabilizable subspace** `Xstab(A, B) = X_g(A) + ⟨A | im B⟩` of
Trentelman–Stoorvogel–Hautus, Theorem 4.26: the sum of the stable subspace
`hurwitzSubspace A` and the reachable subspace `reachableSubspace A B`. It is
the largest subspace each of whose states is the initial state of a stable
state trajectory. -/
noncomputable def stabilizableSubspace (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) :
    Submodule ℝ X :=
  hurwitzSubspace A ⊔ reachableSubspace A B

/-- The **detectable (undetectable) subspace** `Xdet(C, A) = X_b(A) ∩ ⟨ker C | A⟩`
of Trentelman–Stoorvogel–Hautus, Theorem 5.15: the intersection of the
antistable subspace `unstableSubspace A` with the unobservable subspace
`unobservableSubspace C A`. It is the source's smallest detectability subspace;
the source characterisation that it vanishes exactly when `(C, A)` is detectable
(Theorem 5.16) is not used or claimed below. -/
noncomputable def detectableSubspace (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) :
    Submodule ℝ X :=
  unobservableSubspace C A ⊓ unstableSubspace A

/-- The stable subspace is contained in the stabilizable subspace. -/
theorem hurwitzSubspace_le_stabilizableSubspace (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) :
    hurwitzSubspace A ≤ stabilizableSubspace A B :=
  le_sup_left

/-- The reachable subspace is contained in the stabilizable subspace. -/
theorem reachableSubspace_le_stabilizableSubspace (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) :
    reachableSubspace A B ≤ stabilizableSubspace A B :=
  le_sup_right

omit [FiniteDimensional ℝ Y] in
/-- The detectable subspace is contained in the unobservable subspace. -/
theorem detectableSubspace_le_unobservableSubspace (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) :
    detectableSubspace C A ≤ unobservableSubspace C A :=
  inf_le_left

omit [FiniteDimensional ℝ Y] in
/-- The detectable subspace is contained in the antistable subspace. -/
theorem detectableSubspace_le_unstableSubspace (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) :
    detectableSubspace C A ≤ unstableSubspace A :=
  inf_le_right

/-- **The stabilizable subspace is `A`-invariant.** It is the sum of two
`A`-invariant subspaces, the stable subspace and the reachable subspace. -/
theorem map_stabilizableSubspace_le (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) :
    Submodule.map A (stabilizableSubspace A B) ≤ stabilizableSubspace A B := by
  rw [stabilizableSubspace, Submodule.map_sup]
  exact sup_le (le_trans (map_hurwitzSubspace_le A) le_sup_left)
    (le_trans (map_reachableSubspace_le A B) le_sup_right)

omit [FiniteDimensional ℝ Y] in
/-- **The detectable subspace is `A`-invariant.** It is the intersection of two
`A`-invariant subspaces, the unobservable subspace and the antistable subspace. -/
theorem map_detectableSubspace_le (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) :
    Submodule.map A (detectableSubspace C A) ≤ detectableSubspace C A := by
  rw [detectableSubspace]
  exact le_trans (Submodule.map_inf_le A)
    (inf_le_inf (map_unobservableSubspace_le C A) (map_unstableSubspace_le A))

/-- **Spectrum transfer to the quotient of an invariant submodule.** If `A` is
Hurwitz, then the induced map `A : X ⧸ V → X ⧸ V` on the quotient by an
`A`-invariant `V` is Hurwitz. This is the quotient companion of
`isHurwitz_restrict_of_invariant`, obtained from the exact factorisation
`charpoly_restrict_of_invariant` (the quotient characteristic polynomial divides
that of `A`). -/
theorem isHurwitz_quotient_of_invariant (A : X →ₗ[ℝ] X) (V : Submodule ℝ X)
    (hV : ∀ x ∈ V, A x ∈ V) (hA : IsHurwitz A) :
    IsHurwitz (Submodule.mapQ V V A (fun x hx => hV x hx)) := by
  intro z hz
  have hfac := charpoly_restrict_of_invariant A V hV
  have hz' : (A.charpoly.map (algebraMap ℝ ℂ)).eval z = 0 := by
    rw [hfac, Polynomial.map_mul, Polynomial.eval_mul, hz, mul_zero]
  exact hA z hz'

/-- **The uncontrollable complement of a stabilizable pair is Hurwitz.** If
`(A, B)` is stabilizable then the map induced by `A` on the quotient
`X ⧸ ⟨A | im B⟩` is Hurwitz. Equivalently, every unreachable eigenvalue is
stable, which is Theorem 4.30 (ii) in geometric form.

This is the "complementary restriction" attached to `stabilizableSubspace`:
removing the reachable (hence stabilizable) directions leaves a Hurwitz map.
The proof is the PBH necessity statement realised geometrically: a stabilizing
feedback `F` does not change the induced quotient map because `B F` lands in
the reachable subspace, and the quotient characteristic polynomial divides the
Hurwitz characteristic polynomial of `A + B F`. -/
theorem isHurwitz_on_stabilizableComplement (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (h : IsStabilizable A B) :
    IsHurwitz (Submodule.mapQ (reachableSubspace A B) (reachableSubspace A B) A
      (fun x hx => map_reachableSubspace_le A B ⟨x, hx, rfl⟩)) := by
  obtain ⟨F, hF⟩ := h
  let W := reachableSubspace A B
  have hAW : ∀ x ∈ W, (A + B.comp F) x ∈ W := by
    intro x hx
    simp only [LinearMap.add_apply, LinearMap.comp_apply]
    exact W.add_mem (map_reachableSubspace_le A B ⟨x, hx, rfl⟩)
      (range_le_reachableSubspace A B ⟨F x, rfl⟩)
  have hmapQ : Submodule.mapQ W W (A + B.comp F) (fun x hx => hAW x hx) =
      Submodule.mapQ W W A (fun x hx => map_reachableSubspace_le A B ⟨x, hx, rfl⟩) := by
    apply LinearMap.ext
    intro x
    refine Submodule.Quotient.induction_on (p := W) x ?_
    intro y
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply]
    refine (Submodule.Quotient.eq W).mpr ?_
    have hB : (A + B.comp F) y - A y = B (F y) := by
      simp only [LinearMap.add_apply, LinearMap.comp_apply]
      abel
    rw [hB]
    exact range_le_reachableSubspace A B ⟨F y, rfl⟩
  rw [← hmapQ]
  exact isHurwitz_quotient_of_invariant (A + B.comp F) W (fun x hx => hAW x hx) hF

omit [FiniteDimensional ℝ Y] in
/-- **The unobservable complement of a detectable pair is Hurwitz.** If
`(C, A)` is detectable then the restriction of `A` to the unobservable subspace
`⟨ker C | A⟩` is Hurwitz, which is Theorem 5.16 (ii) in geometric form.

This is the "complementary restriction" attached to `detectableSubspace`:
the hidden (unobservable) directions carry a Hurwitz map. The proof is the PBH
necessity statement realised geometrically: an output injection `L` leaves the
unobservable subspace invariant, because `C` vanishes on it, so the restriction
of `A - L C` there is the restriction of `A` and is Hurwitz by
`isHurwitz_restrict_of_invariant`. -/
theorem isHurwitz_on_detectableComplement (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X)
    (h : IsDetectable C A) :
    IsHurwitz (A.restrict
      (fun x hx => map_unobservableSubspace_le C A ⟨x, hx, rfl⟩)) := by
  obtain ⟨L, hL⟩ := h
  let N := unobservableSubspace C A
  have hN : ∀ x ∈ N, (A - L.comp C) x ∈ N := by
    intro x hx
    simp only [LinearMap.sub_apply, LinearMap.comp_apply]
    exact N.sub_mem (map_unobservableSubspace_le C A ⟨x, hx, rfl⟩)
      (by simp [C_eq_zero_of_mem_unobservableSubspace hx])
  have hrestr : (A - L.comp C).restrict (fun x hx => hN x hx) =
      A.restrict (fun x hx => map_unobservableSubspace_le C A ⟨x, hx, rfl⟩) := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [LinearMap.restrict_apply, LinearMap.sub_apply, LinearMap.comp_apply]
    rw [C_eq_zero_of_mem_unobservableSubspace x.2, map_zero, sub_zero]
  rw [← hrestr]
  exact isHurwitz_restrict_of_invariant (A - L.comp C) N (fun x hx => hN x hx) hL

/-- In the zero-dimensional case the stabilizable subspace is the whole
(trivial) state space: the stable subspace is already `⊤`. -/
theorem stabilizableSubspace_eq_top_of_subsingleton [Subsingleton X]
    (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) :
    stabilizableSubspace A B = ⊤ := by
  rw [stabilizableSubspace, hurwitzSubspace_eq_top_of_subsingleton A]
  simp

omit [FiniteDimensional ℝ Y] in
/-- In the zero-dimensional case the detectable subspace is the whole (trivial)
state space, since every submodule of a subsingleton module is `⊤`; in
particular it is also `⊥`. -/
theorem detectableSubspace_eq_top_of_subsingleton [Subsingleton X]
    (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) :
    detectableSubspace C A = ⊤ := by
  have hN : unobservableSubspace C A = ⊤ := Subsingleton.elim _ _
  have hU : unstableSubspace A = ⊤ := Subsingleton.elim _ _
  rw [detectableSubspace, hN, hU]
  simp

/-! ## The stable/antistable direct-sum identity

The stable subspace `X_g(A)` and the antistable subspace `X_b(A)` together span
the state space. In the complexified coordinates the two index sets
`{μ | re μ < 0}` and `{μ | ¬ re μ < 0}` exhaust `ℂ`, so the supremum of the
corresponding generalized eigenspaces is everything
(`Module.End.iSup_maxGenEigenspace_eq_top`). Transporting that identity back to
the real state space requires the complex conjugation `star`: the complexified
matrix has real entries, so `star` intertwines it with itself; consequently each
of the two coordinate subspaces is `star`-invariant. The real statement follows
by writing an arbitrary vector in `H ⊔ U` and replacing the two summands by their
`star`-fixed halves, which are complexifications of real vectors. -/

open scoped Matrix

/-- A real-entry complex matrix commutes with complex conjugation. -/
theorem star_toLin (A : X →ₗ[ℝ] X) (z : Fin (Module.finrank ℝ X) → ℂ) :
    star ((Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) z) =
      (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) (star z) := by
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  ext i
  rw [Pi.star_apply, Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct, star_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hreal : star ((hurwitzMatrix A).map (algebraMap ℝ ℂ) i j) =
      (hurwitzMatrix A).map (algebraMap ℝ ℂ) i j := by
    simp [hurwitzMatrix]
  rw [star_mul, hreal, mul_comm]
  rfl

omit [FiniteDimensional ℝ X] in
/-- Complex conjugation is compatible with complex scalar multiplication. -/
theorem star_smul_pi (μ : ℂ) (w : Fin (Module.finrank ℝ X) → ℂ) :
    star (μ • w) = star μ • star w := by
  ext i
  rw [Pi.star_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, star_mul, mul_comm]
  rfl

/-- Complex conjugation intertwines `f - μ` with `f - star μ` for the
complexified real matrix `f`. -/
theorem star_of_sub_smul (A : X →ₗ[ℝ] X) (μ : ℂ)
    (w : Fin (Module.finrank ℝ X) → ℂ) :
    star (((Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ)))
        - μ • (1 : (Fin (Module.finrank ℝ X) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℝ X) → ℂ))) w)
      = ((Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ)))
        - star μ • (1 : (Fin (Module.finrank ℝ X) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℝ X) → ℂ)))
          (star w) := by
  rw [LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    Module.End.one_apply, Module.End.one_apply, star_sub, star_toLin, star_smul_pi]

/-- Powers of `f - μ` are intertwined with powers of `f - star μ` by complex
conjugation. -/
theorem star_pow_of_sub_smul (A : X →ₗ[ℝ] X) (μ : ℂ) (k : ℕ)
    (w : Fin (Module.finrank ℝ X) → ℂ) :
    star ((((Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ)))
        - μ • (1 : (Fin (Module.finrank ℝ X) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℝ X) → ℂ))) ^ k) w)
      = ((((Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ)))
        - star μ • (1 : (Fin (Module.finrank ℝ X) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℝ X) → ℂ))) ^ k)
          (star w)) := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
      simp only [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply]
      rw [star_of_sub_smul A μ
        ((((Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) -
          μ • (1 : (Fin (Module.finrank ℝ X) → ℂ) →ₗ[ℂ]
            (Fin (Module.finrank ℝ X) → ℂ))) ^ k) w), ih w]

/-- Complex conjugation transports the generalized eigenspace at `μ` to the
generalized eigenspace at `star μ`. -/
theorem star_mem_maxGenEigenspace (A : X →ₗ[ℝ] X) (μ : ℂ)
    {z : Fin (Module.finrank ℝ X) → ℂ}
    (hz : z ∈ Module.End.maxGenEigenspace
      (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) μ) :
    star z ∈ Module.End.maxGenEigenspace
      (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) (star μ) := by
  rw [Module.End.mem_maxGenEigenspace] at hz ⊢
  obtain ⟨k, hk⟩ := hz
  exact ⟨k, by rw [← star_pow_of_sub_smul A μ k z, hk, star_zero]⟩

/-- Complex conjugation preserves a supremum of generalized eigenspaces whose
index predicate is invariant under conjugation. -/
theorem star_mem_iSup_maxGenEigenspace (A : X →ₗ[ℝ] X) (p : ℂ → Prop)
    (hp : ∀ μ, p μ → p (star μ))
    {z : Fin (Module.finrank ℝ X) → ℂ}
    (hz : z ∈ ⨆ μ : {μ : ℂ // p μ},
      Module.End.maxGenEigenspace (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) μ.1) :
    star z ∈ ⨆ μ : {μ : ℂ // p μ},
      Module.End.maxGenEigenspace (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) μ.1 := by
  let g : (Fin (Module.finrank ℝ X) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℝ X) → ℂ) :=
    Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))
  obtain ⟨s, hs⟩ := (Submodule.mem_iSup_iff_exists_finset
    (p := fun μ : {μ : ℂ // p μ} => Module.End.maxGenEigenspace g μ.1)).mp hz
  obtain ⟨zμ, hzμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum
    (fun μ : {μ : ℂ // p μ} => Module.End.maxGenEigenspace g μ.1) z).mp hs
  rw [← hzμ, star_sum]
  apply Submodule.sum_mem
  intro μ hμ
  exact Submodule.mem_iSup_of_mem ⟨star μ.1, hp μ.1 μ.2⟩
    (star_mem_maxGenEigenspace A μ.1 (zμ μ).2)

/-- The complex Hurwitz subspace is invariant under complex conjugation. -/
theorem star_mem_hurwitzComplexSubspace (A : X →ₗ[ℝ] X)
    {z : Fin (Module.finrank ℝ X) → ℂ} (hz : z ∈ hurwitzComplexSubspace A) :
    star z ∈ hurwitzComplexSubspace A := by
  rw [hurwitzComplexSubspace] at hz ⊢
  exact star_mem_iSup_maxGenEigenspace A (fun μ => μ.re < 0)
    (fun μ hμ => by have h : (star μ).re = μ.re := Complex.conj_re μ; rwa [h]) hz

/-- The complex antistable subspace is invariant under complex conjugation. -/
theorem star_mem_unstableComplexSubspace (A : X →ₗ[ℝ] X)
    {z : Fin (Module.finrank ℝ X) → ℂ} (hz : z ∈ unstableComplexSubspace A) :
    star z ∈ unstableComplexSubspace A := by
  rw [unstableComplexSubspace] at hz ⊢
  exact star_mem_iSup_maxGenEigenspace A (fun μ => ¬ μ.re < 0)
    (fun μ hμ => by have h : (star μ).re = μ.re := Complex.conj_re μ; rwa [h]) hz

omit [FiniteDimensional ℝ X] in
/-- A `star`-fixed complex vector is the complexification of a real vector. -/
theorem exists_ofRealPi_of_star_eq {z : Fin (Module.finrank ℝ X) → ℂ} (h : star z = z) :
    ∃ a : Fin (Module.finrank ℝ X) → ℝ, ofRealPi a = z := by
  refine ⟨fun i => (z i).re, ?_⟩
  ext i
  have hi : star (z i) = z i := by
    have := congrFun h i
    simpa [Pi.star_apply] using this
  have him : (z i).im = 0 := Complex.conj_eq_iff_im.mp hi
  simp only [ofRealPi_apply]
  exact Complex.ext (by simp) (by simp [him])

/-- **Stable/antistable direct-sum identity.** For a real endomorphism `A` of a
finite-dimensional real state space, the stable subspace `X_g(A)` and the
antistable subspace `X_b(A)` span the whole space:
`X_g(A) ⊔ X_b(A) = ⊤`.

This is the real form of the primary decomposition of the complexification into
the generalized eigenspaces for eigenvalues with negative real part and those
with nonnegative real part, transported along the real coordinates. It is the
spectral identity underlying the stabilizable/detectable top characterisations.

Source: Trentelman–Stoorvogel–Hautus, Definition 2.13 and the spectral
decompositions of Sections 4.6 and 5.2. -/
theorem hurwitzSubspace_sup_unstableSubspace_eq_top (A : X →ₗ[ℝ] X) :
    hurwitzSubspace A ⊔ unstableSubspace A = ⊤ := by
  have hcomplex : hurwitzComplexSubspace A ⊔ unstableComplexSubspace A = ⊤ := by
    let f : (Fin (Module.finrank ℝ X) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℝ X) → ℂ) :=
      Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))
    have htop : (⨆ μ : ℂ, Module.End.maxGenEigenspace f μ) = ⊤ :=
      Module.End.iSup_maxGenEigenspace_eq_top f
    apply le_antisymm le_top
    rw [← htop]
    apply iSup_le
    intro μ
    by_cases hμ : μ.re < 0
    · refine le_sup_of_le_left ?_
      change Module.End.maxGenEigenspace f μ ≤ hurwitzComplexSubspace A
      rw [hurwitzComplexSubspace]
      exact le_iSup (fun μ' : {μ : ℂ // μ.re < 0} => Module.End.maxGenEigenspace f μ'.1) ⟨μ, hμ⟩
    · refine le_sup_of_le_right ?_
      change Module.End.maxGenEigenspace f μ ≤ unstableComplexSubspace A
      rw [unstableComplexSubspace]
      exact le_iSup (fun μ' : {μ : ℂ // ¬ μ.re < 0} => Module.End.maxGenEigenspace f μ'.1) ⟨μ, hμ⟩
  apply le_antisymm le_top
  intro x _
  set φ : X →ₗ[ℝ] (Fin (Module.finrank ℝ X) → ℂ) :=
    ofRealPi.comp (Module.finBasis ℝ X).equivFun.toLinearMap with hφ
  have hmem : φ x ∈ hurwitzComplexSubspace A ⊔ unstableComplexSubspace A := by
    rw [hcomplex]; exact Submodule.mem_top
  rw [Submodule.mem_sup] at hmem
  obtain ⟨h, hh, u, hu, hhu⟩ := hmem
  have hstar_h : star h ∈ hurwitzComplexSubspace A := star_mem_hurwitzComplexSubspace A hh
  have hstar_u : star u ∈ unstableComplexSubspace A := star_mem_unstableComplexSubspace A hu
  set h' : Fin (Module.finrank ℝ X) → ℂ := (1/2 : ℂ) • (h + star h) with hh'
  set u' : Fin (Module.finrank ℝ X) → ℂ := (1/2 : ℂ) • (u + star u) with hu'
  have hh'mem : h' ∈ hurwitzComplexSubspace A :=
    Submodule.smul_mem _ _ (Submodule.add_mem _ hh hstar_h)
  have hu'mem : u' ∈ unstableComplexSubspace A :=
    Submodule.smul_mem _ _ (Submodule.add_mem _ hu hstar_u)
  have hz_fixed : star (φ x) = φ x := by
    rw [hφ]
    ext i
    simp [ofRealPi]
  have hh'fix : star h' = h' := by
    rw [hh']
    ext i
    simp only [Pi.star_apply, Pi.smul_apply, Pi.add_apply]
    rw [smul_eq_mul, star_mul, star_add, star_star]
    rw [show star (1/2 : ℂ) = 1/2 by simp]
    ring
  have hu'fix : star u' = u' := by
    rw [hu']
    ext i
    simp only [Pi.star_apply, Pi.smul_apply, Pi.add_apply]
    rw [smul_eq_mul, star_mul, star_add, star_star]
    rw [show star (1/2 : ℂ) = 1/2 by simp]
    ring
  have hsum : h' + u' = φ x := by
    rw [hh', hu', ← smul_add]
    rw [show (h + star h) + (u + star u) = (h + u) + star (h + u) by
      rw [star_add]; abel]
    rw [hhu, hz_fixed]
    module
  obtain ⟨ah, hah⟩ := exists_ofRealPi_of_star_eq hh'fix
  obtain ⟨au, hau⟩ := exists_ofRealPi_of_star_eq hu'fix
  have hφin : ∀ a : Fin (Module.finrank ℝ X) → ℝ,
      φ ((Module.finBasis ℝ X).equivFun.symm a) = ofRealPi a := by
    intro a
    rw [hφ]
    simp only [LinearMap.comp_apply]
    congr 1
    exact (Module.finBasis ℝ X).equivFun.apply_symm_apply a
  have hh'pre : (Module.finBasis ℝ X).equivFun.symm ah ∈
      Submodule.comap φ ((hurwitzComplexSubspace A).restrictScalars ℝ) := by
    rw [Submodule.mem_comap, Submodule.restrictScalars_mem, hφin, hah]; exact hh'mem
  have hu'pre : (Module.finBasis ℝ X).equivFun.symm au ∈
      Submodule.comap φ ((unstableComplexSubspace A).restrictScalars ℝ) := by
    rw [Submodule.mem_comap, Submodule.restrictScalars_mem, hφin, hau]; exact hu'mem
  rw [hurwitzSubspace, unstableSubspace]
  rw [Submodule.mem_sup]
  refine ⟨_, hh'pre, _, hu'pre, ?_⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    rw [hφ] at hab
    simp only [LinearMap.comp_apply] at hab
    have hfun : (Module.finBasis ℝ X).equivFun a = (Module.finBasis ℝ X).equivFun b := by
      funext i
      have hi := congrFun hab i
      exact_mod_cast (by simpa [ofRealPi] using hi)
    exact (Module.finBasis ℝ X).equivFun.injective hfun
  apply hinj
  rw [map_add, hφin, hφin, hah, hau, hsum]


end StabilizableDetectable

open scoped TensorProduct

/-- Rectangular version of `ofRealPi_mulVec`. -/
lemma ofRealPi_mulVec_rect {ι κ : Type*} [Fintype ι]
    (M : Matrix κ ι ℝ) (y : ι → ℝ) :
    ofRealPi (M *ᵥ y) = (M.map (algebraMap ℝ ℂ)) *ᵥ (ofRealPi y) := by
  ext i
  have h := RingHom.map_mulVec (algebraMap ℝ ℂ) M y i
  simpa [ofRealPi, Function.comp_def] using h

/-- **Commuting-map generalized-eigenspace transport.** If a linear map `e`
intertwines `f` with `g` (`g ∘ e = e ∘ f`), then `e` maps the generalized
eigenspace of `f` at `μ` into the generalized eigenspace of `g` at `μ`. This is
the abstract form of `map_toLin'_maxGenEigenspace` and the reusable ingredient
for transporting spectral subspaces across a change of coordinates. -/
theorem map_maxGenEigenspace_le_of_comp_eq
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e : E →ₗ[ℂ] F) (f : E →ₗ[ℂ] E) (g : F →ₗ[ℂ] F) (μ : ℂ)
    (h : g.comp e = e.comp f) :
    Submodule.map e (Module.End.maxGenEigenspace f μ) ≤
      Module.End.maxGenEigenspace g μ := by
  rw [Submodule.map_le_iff_le_comap]
  intro z hz
  rw [Submodule.mem_comap] at *
  rw [Module.End.mem_maxGenEigenspace] at hz ⊢
  obtain ⟨k, hk⟩ := hz
  refine ⟨k, ?_⟩
  have hcomm : e.comp (f - μ • 1) = (g - μ • 1).comp e := by
    rw [LinearMap.comp_sub, LinearMap.sub_comp, h]
    ext v
    simp
  have hind : ∀ j, ((g - μ • (1 : (F →ₗ[ℂ] F))) ^ j) (e z) =
      e (((f - μ • (1 : (E →ₗ[ℂ] E))) ^ j) z) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply, ih,
          ← LinearMap.comp_apply, ← hcomm, LinearMap.comp_apply]
        rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply]
  rw [hind k, hk, map_zero]

/-- **Commuting-equivalence generalized-eigenspace transport.** A linear
equivalence `e` satisfying `g ∘ e = e ∘ f` identifies the generalized
eigenspace of `f` at `μ` with that of `g` at `μ`: the conjugation identity
`e '' maxGenEigenspace f μ = maxGenEigenspace g μ`. This is the exact form
needed for basis independence of the spectral subspaces. -/
theorem map_maxGenEigenspace_of_equiv
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (e : E ≃ₗ[ℂ] F) (f : E →ₗ[ℂ] E) (g : F →ₗ[ℂ] F) (μ : ℂ)
    (h : g.comp e.toLinearMap = e.toLinearMap.comp f) :
    Submodule.map e.toLinearMap (Module.End.maxGenEigenspace f μ) =
      Module.End.maxGenEigenspace g μ := by
  refine le_antisymm (map_maxGenEigenspace_le_of_comp_eq e.toLinearMap f g μ h) ?_
  have h1 : ∀ x : E, g (e x) = e (f x) := by
    intro x
    have := congrArg (fun φ : E →ₗ[ℂ] F => φ x) h
    simpa using this
  have h' : f.comp e.symm.toLinearMap = e.symm.toLinearMap.comp g := by
    ext y
    apply e.injective
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← h1 (e.symm.toLinearMap y)]
    simp
  have hsymm := map_maxGenEigenspace_le_of_comp_eq e.symm.toLinearMap g f μ h'
  intro y hy
  have hy' : e.symm y ∈ Module.End.maxGenEigenspace f μ := hsymm ⟨y, hy, rfl⟩
  exact ⟨e.symm y, hy', by simp⟩

/-- **Single-eigenvalue annihilator lemma.** The annihilator of the generalized
eigenrange `genEigenrange A ν k = range ((A - ν)^k)` is the `k`-th generalized
eigenspace of the transpose `Aᵀ = A.dualMap` at `ν`. This is the exact duality
between generalized eigenspaces and generalized eigenranges and is the reusable
input for the transpose spectral duality `(X_b(A))ᵃⁿⁿ = X_g(Aᵀ)`. -/
theorem dualAnnihilator_genEigenrange_eq_genEigenspace_dualMap
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (A : E →ₗ[ℂ] E) (ν : ℂ) (k : ℕ) :
    (Module.End.genEigenrange A ν k).dualAnnihilator =
      Module.End.genEigenspace A.dualMap ν k := by
  rw [Module.End.genEigenrange_nat, Module.End.genEigenspace_nat]
  rw [← LinearMap.ker_dualMap_eq_dualAnnihilator_range]
  congr 1
  rw [← dualMap_pow]
  congr 1
  exact dualMap_sub_smul_one A ν

/-- **Single-eigenvalue annihilator lemma, maximal form.** Over a
finite-dimensional complex space the annihilator of the `finrank`-generalized
eigenrange at `ν` is the maximal generalized eigenspace of the transpose at
`ν`. This is the form stated in the handoff for the transpose spectral
duality. -/
theorem dualAnnihilator_genEigenrange_finrank_eq_maxGenEigenspace
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (A : E →ₗ[ℂ] E) (ν : ℂ) :
    (Module.End.genEigenrange A ν (Module.finrank ℂ E)).dualAnnihilator =
      Module.End.maxGenEigenspace A.dualMap ν := by
  rw [dualAnnihilator_genEigenrange_eq_genEigenspace_dualMap]
  have hfin : Module.finrank ℂ (Module.Dual ℂ E) = Module.finrank ℂ E :=
    Subspace.dual_finrank_eq
  rw [← hfin, ← Module.End.maxGenEigenspace_eq_genEigenspace_finrank A.dualMap ν]

/-- **Per-eigenvalue dimension matching under transposition.** For a
finite-dimensional complex endomorphism `A` and any `μ`, the generalized
eigenspaces of `A` and of its algebraic transpose `A.dualMap` at `μ` have the
same complex dimension. The proof is rank–nullity for `(A - μ)^n` together with
the accepted single-eigenvalue annihilator identity: the transpose of the
`μ`-generalized eigenrange is the `μ`-generalized eigenspace of `A.dualMap`.
This is the dimension input for the transpose spectral duality. -/
theorem finrank_maxGenEigenspace_dualMap
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (A : E →ₗ[ℂ] E) (μ : ℂ) :
    Module.finrank ℂ (Module.End.maxGenEigenspace A μ) =
      Module.finrank ℂ (Module.End.maxGenEigenspace A.dualMap μ) := by
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank A μ,
    Module.End.maxGenEigenspace_eq_genEigenspace_finrank A.dualMap μ,
    Module.End.genEigenspace_nat, Module.End.genEigenspace_nat]
  have hann : (LinearMap.ker ((A - μ • 1) ^ Module.finrank ℂ E)).dualAnnihilator =
      LinearMap.range ((A.dualMap - μ • 1) ^ Module.finrank ℂ E) := by
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    congr 1
    rw [← dualMap_pow, dualMap_sub_smul_one]
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq
    (W := LinearMap.ker ((A - μ • 1) ^ Module.finrank ℂ E))
  rw [hann] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker
    ((A.dualMap - μ • 1) ^ Module.finrank ℂ E)
  have hd : Module.finrank ℂ (Module.Dual ℂ E) = Module.finrank ℂ E :=
    Subspace.dual_finrank_eq
  rw [hd]
  omega

/-- **Finite dimension of a supremum-independent finite family.** For a finite
set `s` on which a family of subspaces is supremum-independent, the dimension of
the finite supremum is the sum of the dimensions. This is the `Finset` form of
the finite-support dimension formula used to compute the dimensions of the stable
and antistable generalized-eigenspace suprema. -/
theorem finset_supIndep_finrank_sup_eq_sum {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] {ι : Type*} (s : Finset ι)
    (p : ι → Submodule ℂ E) (hs : s.SupIndep p) :
    Module.finrank ℂ ↥(s.sup p) = ∑ i ∈ s, Module.finrank ℂ ↥(p i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a t hat ih =>
      rw [Finset.sup_insert, Finset.sum_insert hat]
      have hdisj : Disjoint (p a) (t.sup p) :=
        hs (Finset.subset_insert a t) (Finset.mem_insert_self a t) hat
      have hst : t.SupIndep p := hs.subset (Finset.subset_insert a t)
      have h := Submodule.finrank_sup_add_finrank_inf_eq (p a) (t.sup p)
      rw [hdisj.eq_bot, finrank_bot, add_zero] at h
      rw [h, ih hst]

/-- **Finite-support dimension formula.** For a supremum-independent family
indexed by a finite type, the dimension of the supremum is the sum of the
dimensions. -/
theorem finrank_iSup_fintype {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] {ι : Type*} [Fintype ι]
    (p : ι → Submodule ℂ E) (hp : iSupIndep p) :
    Module.finrank ℂ ↥(⨆ i, p i) = ∑ i, Module.finrank ℂ ↥(p i) := by
  classical
  rw [show (⨆ i, p i) = Finset.univ.sup p by
    rw [Finset.sup_eq_iSup]; simp]
  rw [show (∑ i, Module.finrank ℂ ↥(p i)) = ∑ i ∈ Finset.univ, Module.finrank ℂ ↥(p i) by
    simp]
  exact finset_supIndep_finrank_sup_eq_sum Finset.univ p
    (iSupIndep.sup_indep_univ hp)

/-- **Finite-support dimension formula for an arbitrary independent family.** For a
supremum-independent family in a finite-dimensional space, only finitely many
members are nonzero (`iSupIndep.fintypeNeBotOfFiniteDimensional`), and the
dimension of the supremum is the sum of the dimensions over that finite support.
This is the named finite-support dimension formula for independent generalized
eigenspace suprema. -/
theorem finrank_iSup_of_iSupIndep {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] {ι : Type*} (p : ι → Submodule ℂ E) (hp : iSupIndep p)
    [Fintype {i : ι // p i ≠ ⊥}] :
    Module.finrank ℂ ↥(⨆ i, p i) =
      ∑ i : {i : ι // p i ≠ ⊥}, Module.finrank ℂ ↥(p i.1) := by
  classical
  have hsupeq : (⨆ i, p i) = ⨆ i : {i : ι // p i ≠ ⊥}, p i.1 := by
    apply le_antisymm
    · apply iSup_le
      intro i
      by_cases h : p i = ⊥
      · rw [h]; exact bot_le
      · exact le_iSup (fun i : {i : ι // p i ≠ ⊥} => p i.1) ⟨i, h⟩
    · apply iSup_le
      intro i
      exact le_iSup p i.1
  rw [hsupeq]
  exact finrank_iSup_fintype (fun i : {i : ι // p i ≠ ⊥} => p i.1)
    (hp.comp Subtype.val_injective)

/-- **Finite-support dimension formula, filtered form.** For a
supremum-independent family `p` on `ℂ` and a finite set `s` containing every
nontrivial member, the dimension of the supremum over a predicate `P` is the
filtered sum of the dimensions. This is the form that lets the stable and
antistable partial sums of two families with pointwise equal dimensions be
compared. -/
theorem finrank_iSup_subtype_eq_sum_filter {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] {P : ℂ → Prop} [DecidablePred P]
    (p : ℂ → Submodule ℂ E) (hp : iSupIndep p) (s : Finset ℂ)
    (hs : ∀ μ, p μ ≠ ⊥ → μ ∈ s) :
    Module.finrank ℂ ↥(⨆ μ : {μ : ℂ // P μ}, p μ.1) =
      ∑ μ ∈ s.filter P, Module.finrank ℂ ↥(p μ) := by
  have hsupeq : (⨆ μ : {μ : ℂ // P μ}, p μ.1) = (s.filter P).sup p := by
    apply le_antisymm
    · apply iSup_le
      intro μ
      by_cases h : p μ.1 = ⊥
      · rw [h]; exact bot_le
      · exact Finset.le_sup (Finset.mem_filter.mpr ⟨hs μ.1 h, μ.2⟩)
    · apply Finset.sup_le
      intro ν hν
      exact le_iSup (fun μ : {μ : ℂ // P μ} => p μ.1)
        ⟨ν, (Finset.mem_filter.mp hν).2⟩
  rw [hsupeq]
  exact finset_supIndep_finrank_sup_eq_sum (s.filter P) p (hp.supIndep' _)

/-- **Pairwise generalized-eigenspace separation.** For distinct scalars
`μ ≠ ν`, the `μ`-generalized eigenspace of `A` is contained in the
`ν`-generalized eigenrange `range ((A - ν)^n)`. On `X_μ(A)` the map
`A - ν = (A - μ) + (μ - ν)` has trivial kernel because `μ ≠ ν` makes the
generalized eigenspaces disjoint; since `X_μ(A)` is finite-dimensional, that
restricted map is surjective, so its `n`-th power is too. This is the
separation step that feeds the transpose annihilator duality. -/
theorem maxGenEigenspace_le_genEigenrange_of_ne
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (A : E →ₗ[ℂ] E) {μ ν : ℂ} (hμν : μ ≠ ν) :
    Module.End.maxGenEigenspace A μ ≤
      Module.End.genEigenrange A ν (Module.finrank ℂ E) := by
  rw [Module.End.genEigenrange_nat]
  intro x hx
  let p : Submodule ℂ E := Module.End.maxGenEigenspace A μ
  have hx' : x ∈ p := hx
  have hpA : ∀ y ∈ p, A y ∈ p :=
    fun y hy => Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl A) μ hy
  have hpν : ∀ y ∈ p, (A - ν • 1) y ∈ p :=
    fun y hy => p.sub_mem (hpA y hy) (p.smul_mem ν hy)
  have hker : LinearMap.ker ((A - ν • 1).restrict hpν) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    rw [LinearMap.mem_ker] at hy
    apply Subtype.ext
    have hy0 : (A - ν • 1) (y : E) = 0 := by
      have := congrArg Subtype.val hy
      simpa using this
    have heig : (y : E) ∈ Module.End.eigenspace A ν := by
      rw [Module.End.mem_eigenspace_iff]
      exact sub_eq_zero.mp hy0
    have hdisj := Module.End.disjoint_genEigenspace A hμν (⊤ : ℕ∞) 1
    have hbot : (y : E) ∈ (⊥ : Submodule ℂ E) := by
      rw [← hdisj.eq_bot]
      exact ⟨y.2, by simpa [Module.End.genEigenspace_one] using heig⟩
    simpa using hbot
  have hinj : Function.Injective ((A - ν • 1).restrict hpν) :=
    LinearMap.ker_eq_bot.mp hker
  have hsurj : Function.Surjective ((A - ν • 1).restrict hpν) :=
    LinearMap.injective_iff_surjective.mp hinj
  have hsurj' : Function.Surjective (((A - ν • 1).restrict hpν) ^ Module.finrank ℂ E) := by
    rw [Module.End.coe_pow]
    exact hsurj.iterate _
  obtain ⟨y, hy⟩ := hsurj' ⟨x, hx'⟩
  refine ⟨(y : E), ?_⟩
  have hcoe := congrArg Subtype.val hy
  rw [Module.End.pow_restrict] at hcoe
  simpa using hcoe

/-- **Inclusion half of the complex transpose spectral duality.** The sum of the
stable generalized eigenspaces of the transpose `A.dualMap` lies in the
annihilator of the sum of the antistable generalized eigenspaces of `A`. Each
stable eigenspace `X_ν(A.dualMap)` with `re ν < 0` is the annihilator of the
generalized eigenrange at `ν` (accepted single-eigenvalue annihilator lemma),
and pairwise separation puts every antistable `X_μ(A)` with `re μ ≥ 0` inside
that eigenrange. -/
theorem stable_le_dualAnnihilator_antistable
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (A : E →ₗ[ℂ] E) :
    (⨆ ν : {ν : ℂ // ν.re < 0}, Module.End.maxGenEigenspace A.dualMap ν.1) ≤
      (⨆ μ : {μ : ℂ // ¬ μ.re < 0},
        Module.End.maxGenEigenspace A μ.1).dualAnnihilator := by
  rw [Submodule.dualAnnihilator_iSup_eq]
  refine iSup_le fun ν => ?_
  refine le_iInf fun μ => ?_
  have hμν : μ.1 ≠ ν.1 := by
    intro h
    have hlt : μ.1.re < 0 := h ▸ ν.2
    exact μ.2 hlt
  rw [← dualAnnihilator_genEigenrange_finrank_eq_maxGenEigenspace A ν.1]
  exact Subspace.dualAnnihilator_le_dualAnnihilator_iff.mpr
    (maxGenEigenspace_le_genEigenrange_of_ne A hμν)

/-- **Complex transpose spectral duality, equality form.** The annihilator of the
sum of the antistable generalized eigenspaces of `A` is exactly the sum of the
stable generalized eigenspaces of the transpose `A.dualMap`. The inclusion
`stable_le_dualAnnihilator_antistable` gives one direction; the reverse follows
from the finite-support dimension formula. The finite-dimensional
generalized-eigenspace decomposition gives `finrank U + finrank W = finrank E` for
the antistable/stable parts of `A`, and `finrank_maxGenEigenspace_dualMap` makes
the stable part of `A.dualMap` have the same dimension as the stable part of `A`.
-/
theorem dualAnnihilator_antistable_eq_stable
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (A : E →ₗ[ℂ] E) :
    (⨆ μ : {μ : ℂ // ¬ μ.re < 0},
        Module.End.maxGenEigenspace A μ.1).dualAnnihilator =
      (⨆ ν : {ν : ℂ // ν.re < 0}, Module.End.maxGenEigenspace A.dualMap ν.1) := by
  let p : ℂ → Submodule ℂ E := fun μ => Module.End.maxGenEigenspace A μ
  let q : ℂ → Submodule ℂ (Module.Dual ℂ E) :=
    fun ν => Module.End.maxGenEigenspace A.dualMap ν
  change (⨆ μ : {μ : ℂ // ¬ μ.re < 0}, p μ.1).dualAnnihilator =
    (⨆ ν : {ν : ℂ // ν.re < 0}, q ν.1)
  have hp : iSupIndep p := Module.End.independent_maxGenEigenspace A
  have hq : iSupIndep q := Module.End.independent_maxGenEigenspace A.dualMap
  let s : Finset ℂ :=
    (iSupIndep.fintypeNeBotOfFiniteDimensional hp).elems.image Subtype.val
  have hs : ∀ μ, p μ ≠ ⊥ → μ ∈ s := fun μ hμ =>
      Finset.mem_image.mpr ⟨⟨μ, hμ⟩,
        (iSupIndep.fintypeNeBotOfFiniteDimensional hp).complete ⟨μ, hμ⟩, rfl⟩
  have hs_q : ∀ ν, q ν ≠ ⊥ → ν ∈ s := by
    intro ν hν
    apply hs ν
    intro hpbot
    apply hν
    have heq : Module.finrank ℂ (p ν) = Module.finrank ℂ (q ν) :=
      finrank_maxGenEigenspace_dualMap A ν
    have hz : Module.finrank ℂ (p ν) = 0 := by rw [hpbot]; simp
    rw [hz] at heq
    exact Submodule.finrank_eq_zero.mp heq.symm
  have hU : Module.finrank ℂ ↥(⨆ μ : {μ : ℂ // ¬ μ.re < 0}, p μ.1) =
      ∑ μ ∈ s.filter (fun μ : ℂ => ¬ μ.re < 0), Module.finrank ℂ ↥(p μ) :=
    finrank_iSup_subtype_eq_sum_filter (P := fun μ : ℂ => ¬ μ.re < 0) p hp s hs
  have hV : Module.finrank ℂ ↥(⨆ ν : {ν : ℂ // ν.re < 0}, q ν.1) =
      ∑ ν ∈ s.filter (fun ν : ℂ => ν.re < 0), Module.finrank ℂ ↥(q ν) :=
    finrank_iSup_subtype_eq_sum_filter (P := fun ν : ℂ => ν.re < 0) q hq s hs_q
  have hV' : Module.finrank ℂ ↥(⨆ ν : {ν : ℂ // ν.re < 0}, q ν.1) =
      ∑ ν ∈ s.filter (fun ν : ℂ => ν.re < 0), Module.finrank ℂ ↥(p ν) := by
    rw [hV]
    apply Finset.sum_congr rfl
    intro ν _
    exact (finrank_maxGenEigenspace_dualMap A ν).symm
  have hE : Module.finrank ℂ E = ∑ μ ∈ s, Module.finrank ℂ ↥(p μ) := by
    have h := finrank_iSup_subtype_eq_sum_filter (P := fun _ : ℂ => True) p hp s hs
    simp only [Finset.filter_true] at h
    rw [show (⨆ μ : {μ : ℂ // True}, p μ.1) = ⨆ μ : ℂ, p μ by
      rw [iSup_subtype]; simp] at h
    rw [Module.End.iSup_maxGenEigenspace_eq_top A, finrank_top] at h
    exact h
  have h2 : Module.finrank ℂ ↥(⨆ μ : {μ : ℂ // ¬ μ.re < 0}, p μ.1) +
      Module.finrank ℂ ↥(⨆ ν : {ν : ℂ // ν.re < 0}, q ν.1) = Module.finrank ℂ E := by
    rw [hU, hV', hE, add_comm]
    rw [Finset.sum_filter_add_sum_filter_not s (fun μ : ℂ => μ.re < 0)
      (fun μ => Module.finrank ℂ ↥(p μ))]
  have h1 : Module.finrank ℂ ↥(⨆ μ : {μ : ℂ // ¬ μ.re < 0}, p μ.1) +
      Module.finrank ℂ ↥((⨆ μ : {μ : ℂ // ¬ μ.re < 0}, p μ.1)).dualAnnihilator =
      Module.finrank ℂ E :=
    Subspace.finrank_add_finrank_dualAnnihilator_eq _
  have hdim : Module.finrank ℂ ↥(⨆ ν : {ν : ℂ // ν.re < 0}, q ν.1) =
      Module.finrank ℂ ↥((⨆ μ : {μ : ℂ // ¬ μ.re < 0}, p μ.1)).dualAnnihilator := by
    omega
  exact (Submodule.eq_of_le_of_finrank_eq (stable_le_dualAnnihilator_antistable A)
    hdim).symm

/-- Matrix transport of generalized eigenspaces. -/
theorem map_toLin'_maxGenEigenspace {m n : ℕ}
    (M : Matrix (Fin m) (Fin n) ℂ) (A : Matrix (Fin n) (Fin n) ℂ)
    (T : Matrix (Fin m) (Fin m) ℂ) (μ : ℂ)
    (h : M * A = T * M) :
    Submodule.map (Matrix.toLin' M)
        (Module.End.maxGenEigenspace (Matrix.toLin' A) μ) ≤
      Module.End.maxGenEigenspace (Matrix.toLin' T) μ := by
  have hMA : (Matrix.toLin' M).comp (Matrix.toLin' A) =
      (Matrix.toLin' T).comp (Matrix.toLin' M) := by
    rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul, h]
  exact map_maxGenEigenspace_le_of_comp_eq (Matrix.toLin' M) (Matrix.toLin' A)
    (Matrix.toLin' T) μ hMA.symm

/-- Coordinate naturality of a real linear map. -/
theorem ofRealPi_equivFun_toLin'_apply {Z : Type*} [AddCommGroup Z] [Module ℝ Z]
    [FiniteDimensional ℝ Z] (f : X →ₗ[ℝ] Z) (x : X) :
    (Matrix.toLin'
        ((LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ Z) f).map
          (algebraMap ℝ ℂ)))
      (ofRealPi ((Module.finBasis ℝ X).equivFun x)) =
    ofRealPi ((Module.finBasis ℝ Z).equivFun (f x)) := by
  rw [Matrix.toLin'_apply, ← ofRealPi_mulVec_rect]
  change ofRealPi ((LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ Z) f) *ᵥ
    (Module.finBasis ℝ X).repr x) = ofRealPi ((Module.finBasis ℝ Z).repr (f x))
  rw [LinearMap.toMatrix_mulVec_repr]

/-- The characteristic polynomial of the complexified coordinate operator is the
complexified characteristic polynomial of `A`. -/
theorem charpoly_hurwitzMatrix_map_eq (A : X →ₗ[ℝ] X) :
    (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))).charpoly =
      A.charpoly.map (algebraMap ℝ ℂ) := by
  change (Matrix.toLin'
    ((LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ X) A).map
      (algebraMap ℝ ℂ))).charpoly = A.charpoly.map (algebraMap ℝ ℂ)
  rw [Matrix.charpoly_toLin', Matrix.charpoly_map,
    ← LinearMap.charpoly_toMatrix (f := A) (Module.finBasis ℝ X)]

/-- A Hurwitz operator has no unstable generalized eigenspaces in coordinates. -/
theorem unstableComplexSubspace_eq_bot_of_isHurwitz (A : X →ₗ[ℝ] X)
    (hA : IsHurwitz A) : unstableComplexSubspace A = ⊥ := by
  rw [unstableComplexSubspace, iSup_eq_bot]
  intro μ
  rw [Submodule.eq_bot_iff]
  intro z hz
  by_contra hz0
  have heig := hasEigenvalue_of_mem_maxGenEigenspace hz hz0
  have hroot : (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))).charpoly.IsRoot μ.1 :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).mp heig
  rw [charpoly_hurwitzMatrix_map_eq] at hroot
  exact μ.2 (hA μ.1 hroot)

/-- `ofRealPi` is injective. -/
lemma ofRealPi_injective {ι : Type*} : Function.Injective (ofRealPi (ι := ι)) := by
  intro a b hab
  have hsub : ofRealPi (a - b) = 0 := by rw [map_sub, hab, sub_self]
  exact sub_eq_zero.mp (ofRealPi_eq_zero hsub)

/-- A Hurwitz operator has trivial unstable subspace. -/
theorem unstableSubspace_eq_bot_of_isHurwitz (A : X →ₗ[ℝ] X)
    (hA : IsHurwitz A) : unstableSubspace A = ⊥ := by
  rw [unstableSubspace, unstableComplexSubspace_eq_bot_of_isHurwitz A hA,
    Submodule.restrictScalars_bot, Submodule.comap_bot, LinearMap.ker_eq_bot]
  exact ofRealPi_injective.comp (Module.finBasis ℝ X).equivFun.injective




/-- Forward direction: a stabilizable pair has full stabilizable subspace. -/
theorem stabilizableSubspace_eq_top_of_isStabilizable (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (h : IsStabilizable A B) : stabilizableSubspace A B = ⊤ := by
  have hle : unstableSubspace A ≤ reachableSubspace A B := by
    intro x hx
    let R : Submodule ℝ X := reachableSubspace A B
    have _ : IsClosed (R : Set X) := R.closed_of_finiteDimensional
    let T : (X ⧸ R) →ₗ[ℝ] (X ⧸ R) :=
      Submodule.mapQ R R A (fun x hx => map_reachableSubspace_le A B ⟨x, hx, rfl⟩)
    have hT : IsHurwitz T := isHurwitz_on_stabilizableComplement A B h
    have hUT : unstableComplexSubspace T = ⊥ := unstableComplexSubspace_eq_bot_of_isHurwitz T hT
    let q : X →ₗ[ℝ] (X ⧸ R) := R.mkQ
    have hqA : q.comp A = T.comp q := by
      simpa only [q, T] using
        (Submodule.mapQ_mkQ (p := R) (q := R) (f := A) (h := fun x hx =>
          map_reachableSubspace_le A B ⟨x, hx, rfl⟩)).symm
    have hmat : LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ (X ⧸ R)) q *
        LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ X) A =
        LinearMap.toMatrix (Module.finBasis ℝ (X ⧸ R)) (Module.finBasis ℝ (X ⧸ R)) T *
        LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ (X ⧸ R)) q := by
      rw [← LinearMap.toMatrix_comp (v₁ := Module.finBasis ℝ X) (v₂ := Module.finBasis ℝ X)
            (v₃ := Module.finBasis ℝ (X ⧸ R)) q A,
        hqA, LinearMap.toMatrix_comp (v₁ := Module.finBasis ℝ X)
          (v₂ := Module.finBasis ℝ (X ⧸ R)) (v₃ := Module.finBasis ℝ (X ⧸ R)) T q]
    have hmatc : (LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ (X ⧸ R)) q).map
          (algebraMap ℝ ℂ) *
        (LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ X) A).map
          (algebraMap ℝ ℂ) =
        (LinearMap.toMatrix (Module.finBasis ℝ (X ⧸ R)) (Module.finBasis ℝ (X ⧸ R)) T).map
          (algebraMap ℝ ℂ) *
        (LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ (X ⧸ R)) q).map
          (algebraMap ℝ ℂ) := by
      rw [← Matrix.map_mul, ← Matrix.map_mul, hmat]
    have hmap : Submodule.map
        (Matrix.toLin' ((LinearMap.toMatrix (Module.finBasis ℝ X)
          (Module.finBasis ℝ (X ⧸ R)) q).map (algebraMap ℝ ℂ)))
        (unstableComplexSubspace A) ≤ unstableComplexSubspace T := by
      rw [unstableComplexSubspace, Submodule.map_iSup]
      refine iSup_le fun μ => ?_
      rw [unstableComplexSubspace]
      exact le_iSup_of_le μ (map_toLin'_maxGenEigenspace _ _ _ μ.1 hmatc)
    have hzx : ofRealPi ((Module.finBasis ℝ X).equivFun x) ∈ unstableComplexSubspace A := by
      rwa [mem_unstableSubspace] at hx
    have hmem : (Matrix.toLin' ((LinearMap.toMatrix (Module.finBasis ℝ X)
        (Module.finBasis ℝ (X ⧸ R)) q).map (algebraMap ℝ ℂ)))
        (ofRealPi ((Module.finBasis ℝ X).equivFun x)) ∈ unstableComplexSubspace T :=
      hmap ⟨_, hzx, rfl⟩
    rw [hUT, Submodule.mem_bot] at hmem
    have hqx : ofRealPi ((Module.finBasis ℝ (X ⧸ R)).equivFun (q x)) = 0 := by
      rw [← ofRealPi_equivFun_toLin'_apply q x]
      exact hmem
    have hz : (Module.finBasis ℝ (X ⧸ R)).equivFun (q x) = 0 := ofRealPi_eq_zero hqx
    have hq0 : q x = 0 :=
      (Module.finBasis ℝ (X ⧸ R)).equivFun.injective (by rw [hz, map_zero])
    change x ∈ R
    rw [← Submodule.ker_mkQ R]
    exact hq0
  rw [stabilizableSubspace]
  apply le_antisymm le_top
  calc ⊤ = hurwitzSubspace A ⊔ unstableSubspace A :=
        (hurwitzSubspace_sup_unstableSubspace_eq_top A).symm
    _ ≤ hurwitzSubspace A ⊔ reachableSubspace A B := sup_le_sup_left hle _



open scoped TensorProduct

/-- A left eigenvector annihilating the input map annihilates the whole
reachable subspace. -/
theorem apply_eq_zero_of_left_eigenvector_mem_reachableSubspace
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] E) (η : E →ₗ[ℂ] ℂ) (μ : ℂ)
    (hA : η.comp A = μ • η) (hB : η.comp B = 0) {x : E}
    (hx : x ∈ reachableSubspace A B) : η x = 0 := by
  have hgen : ∀ k (u : F), η ((A ^ k) (B u)) = 0 := by
    intro k u
    induction k with
    | zero => simpa using congrArg (fun f : F →ₗ[ℂ] ℂ => f u) hB
    | succ k ih =>
        have h1 : η (A ((A ^ k) (B u))) = μ * η ((A ^ k) (B u)) := by
          have := congrArg (fun f : E →ₗ[ℂ] ℂ => f ((A ^ k) (B u))) hA
          simpa [LinearMap.comp_apply, LinearMap.smul_apply] using this
        rw [pow_succ', Module.End.mul_eq_comp, LinearMap.comp_apply, h1, ih, mul_zero]
  rw [reachableSubspace] at hx
  obtain ⟨s, hs⟩ := (Submodule.mem_iSup_iff_exists_finset
    (p := fun k : ℕ => LinearMap.range ((A ^ k).comp B))).mp hx
  obtain ⟨xk, hxk⟩ := (Submodule.mem_iSup_finset_iff_exists_sum
    (fun k : ℕ => LinearMap.range ((A ^ k).comp B)) x).mp hs
  rw [← hxk, map_sum]
  apply Finset.sum_eq_zero
  intro k hk
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp (xk k).2
  rw [← hu]
  exact hgen k u



/-- A left eigenvector annihilates every generalized eigenspace at a different
eigenvalue. -/
theorem apply_eq_zero_of_left_eigenvector_mem_maxGenEigenspace
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (A : E →ₗ[ℂ] E) (η : E →ₗ[ℂ] ℂ) {μ ν : ℂ}
    (hA : η.comp A = μ • η) (hν : ν ≠ μ) {z : E}
    (hz : z ∈ Module.End.maxGenEigenspace A ν) : η z = 0 := by
  have hstep : η.comp (A - ν • 1) = (μ - ν) • η := by
    rw [Module.End.one_eq_id, LinearMap.comp_sub, hA, LinearMap.comp_smul, LinearMap.comp_id]
    ext v
    simp only [LinearMap.sub_apply, LinearMap.smul_apply]
    module
  have hpow : ∀ k, η.comp ((A - ν • 1) ^ k) = (μ - ν) ^ k • η := by
    intro k
    induction k with
    | zero => simp [Module.End.one_eq_id]
    | succ k ih =>
        rw [pow_succ, Module.End.mul_eq_comp, ← LinearMap.comp_assoc, ih,
          LinearMap.smul_comp, hstep, smul_smul, pow_succ]
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace A ν z).mp hz
  have h := congrArg (fun f : E →ₗ[ℂ] ℂ => f z) (hpow k)
  simp only [LinearMap.comp_apply, LinearMap.smul_apply] at h
  rw [hk, map_zero] at h
  rcases smul_eq_zero.mp h.symm with h0 | h0
  · exact absurd h0 (pow_ne_zero k (sub_ne_zero.mpr hν.symm))
  · exact h0


theorem baseChange_eq_basis : (Module.finBasis ℝ X).baseChange ℂ =
    Algebra.TensorProduct.basis ℂ (Module.finBasis ℝ X) := by
  ext i
  simp [Module.Basis.baseChange_apply, Algebra.TensorProduct.basis_apply]

/-- The coordinate equivalence of the base-changed basis intertwines `A.baseChange ℂ`
with the complexified coordinate matrix. -/
theorem baseChange_repr_comp (A : X →ₗ[ℝ] X) :
    ((Module.finBasis ℝ X).baseChange ℂ).equivFun.toLinearMap.comp (A.baseChange ℂ) =
      (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))).comp
        ((Module.finBasis ℝ X).baseChange ℂ).equivFun.toLinearMap := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  change ((Module.finBasis ℝ X).baseChange ℂ).repr ((A.baseChange ℂ) z) =
    (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ)))
      (((Module.finBasis ℝ X).baseChange ℂ).repr z)
  rw [baseChange_eq_basis,
    ← LinearMap.toMatrix_mulVec_repr (Algebra.TensorProduct.basis ℂ (Module.finBasis ℝ X))
      (Algebra.TensorProduct.basis ℂ (Module.finBasis ℝ X)) (A.baseChange ℂ) z,
    LinearMap.toMatrix_baseChange, Matrix.toLin'_apply]
  rfl



open scoped TensorProduct


/-- The coordinate equivalence of the base-changed basis sends `1 ⊗ x` to the
real coordinates of `x`. -/
theorem baseChange_equivFun_symm_one_tmul (x : X) :
    ((Module.finBasis ℝ X).baseChange ℂ).equivFun.symm
      (ofRealPi ((Module.finBasis ℝ X).equivFun x)) = (1 : ℂ) ⊗ₜ[ℝ] x := by
  rw [Basis.equivFun_symm_apply]
  conv_rhs => rw [← (Module.finBasis ℝ X).sum_equivFun x, TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.Basis.baseChange_apply]
  simp only [ofRealPi_apply]
  rw [TensorProduct.tmul_smul]
  rfl

/-- Reverse direction: a full stabilizable subspace makes the pair stabilizable. -/
theorem isStabilizable_of_stabilizableSubspace_eq_top (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X)
    (h : stabilizableSubspace A B = ⊤) : IsStabilizable A B := by
  apply isStabilizable_of_uncontrollableEigenvalues_hurwitz
  intro μ hμ
  by_contra hμre
  obtain ⟨η, hηne, hηA, hηB⟩ := hμ
  let Φ : (ℂ ⊗[ℝ] X) ≃ₗ[ℂ] (Fin (Module.finrank ℝ X) → ℂ) :=
    ((Module.finBasis ℝ X).baseChange ℂ).equivFun
  let Φs : (Fin (Module.finrank ℝ X) → ℂ) →ₗ[ℂ] (ℂ ⊗[ℝ] X) := Φ.symm.toLinearMap
  let ηc : (Fin (Module.finrank ℝ X) → ℂ) →ₗ[ℂ] ℂ := η.comp Φs
  have hsymm : Φs.comp (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) =
      (A.baseChange ℂ).comp Φs := by
    apply LinearMap.ext
    intro z
    simp only [LinearMap.comp_apply]
    apply Φ.injective
    rw [show Φ (Φs ((Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) z)) =
        (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) z by
      exact Φ.apply_symm_apply _]
    change (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) z =
      (Φ.toLinearMap.comp (A.baseChange ℂ)) (Φs z)
    rw [baseChange_repr_comp A, LinearMap.comp_apply]
    exact (congrArg (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ)))
      (Φ.apply_symm_apply z)).symm
  have hηc : ηc.comp (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) = μ • ηc := by
    rw [show ηc.comp (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) =
        η.comp (Φs.comp (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ)))) by
      rw [LinearMap.comp_assoc]]
    rw [hsymm, ← LinearMap.comp_assoc, hηA, LinearMap.smul_comp]
  have hker : hurwitzComplexSubspace A ≤ LinearMap.ker ηc := by
    rw [hurwitzComplexSubspace]
    refine iSup_le fun ν => ?_
    intro z hz
    rw [LinearMap.mem_ker]
    exact apply_eq_zero_of_left_eigenvector_mem_maxGenEigenspace
      (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) ηc hηc
      (fun hνμ => hμre (hνμ ▸ ν.2)) hz
  have hH : ∀ a ∈ hurwitzSubspace A, η ((1 : ℂ) ⊗ₜ[ℝ] a) = 0 := by
    intro a ha
    have hφ : ofRealPi ((Module.finBasis ℝ X).equivFun a) ∈ hurwitzComplexSubspace A := by
      rwa [mem_hurwitzSubspace] at ha
    rw [← baseChange_equivFun_symm_one_tmul a]
    exact hker hφ
  have hR : ∀ b ∈ reachableSubspace A B, η ((1 : ℂ) ⊗ₜ[ℝ] b) = 0 := by
    intro b hb
    have hmem : (1 : ℂ) ⊗ₜ[ℝ] b ∈
        reachableSubspace (A.baseChange ℂ) (B.baseChange ℂ) := by
      rw [reachableSubspace] at hb ⊢
      obtain ⟨s, hs⟩ := (Submodule.mem_iSup_iff_exists_finset
        (p := fun k : ℕ => LinearMap.range ((A ^ k).comp B))).mp hb
      obtain ⟨bk, hbk⟩ := (Submodule.mem_iSup_finset_iff_exists_sum
        (fun k : ℕ => LinearMap.range ((A ^ k).comp B)) b).mp hs
      rw [← hbk, TensorProduct.tmul_sum]
      apply Submodule.sum_mem
      intro k hk
      obtain ⟨u, hu⟩ := LinearMap.mem_range.mp (bk k).2
      rw [← hu]
      have hgen : (1 : ℂ) ⊗ₜ[ℝ] (((A ^ k) ∘ₗ B) u) =
          ((A.baseChange ℂ) ^ k) ((B.baseChange ℂ) ((1 : ℂ) ⊗ₜ[ℝ] u)) := by
        rw [← LinearMap.baseChange_pow]
        rw [show ((A ^ k).baseChange ℂ) ((B.baseChange ℂ) ((1 : ℂ) ⊗ₜ[ℝ] u)) =
            (((A ^ k).baseChange ℂ).comp (B.baseChange ℂ)) ((1 : ℂ) ⊗ₜ[ℝ] u) from rfl]
        rw [← LinearMap.baseChange_comp, LinearMap.baseChange_tmul]
      rw [hgen]
      exact Submodule.mem_iSup_of_mem k ⟨(1 : ℂ) ⊗ₜ[ℝ] u, rfl⟩
    exact apply_eq_zero_of_left_eigenvector_mem_reachableSubspace
      (A.baseChange ℂ) (B.baseChange ℂ) η μ hηA hηB hmem
  have hηzero : η = 0 := by
    apply ((Module.finBasis ℝ X).baseChange ℂ).ext
    intro j
    rw [Module.Basis.baseChange_apply]
    have hx : ((Module.finBasis ℝ X) j) ∈ hurwitzSubspace A ⊔ reachableSubspace A B := by
      rw [← stabilizableSubspace, h]; trivial
    rw [Submodule.mem_sup] at hx
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    rw [← hab, TensorProduct.tmul_add]
    change η ((1 : ℂ) ⊗ₜ[ℝ] a + (1 : ℂ) ⊗ₜ[ℝ] b) = 0
    rw [map_add, hH a ha, hR b hb, add_zero]
  exact hηne hηzero




/-- Top-characterization of stabilizability: the pair `(A, B)` is stabilizable
exactly when its stabilizable subspace is the whole state space. -/
theorem isStabilizable_iff_stabilizableSubspace_eq_top (A : X →ₗ[ℝ] X) (B : U →ₗ[ℝ] X) :
    IsStabilizable A B ↔ stabilizableSubspace A B = ⊤ :=
  ⟨stabilizableSubspace_eq_top_of_isStabilizable A B,
   isStabilizable_of_stabilizableSubspace_eq_top A B⟩



/-! ## Disjointness of the stable and antistable spectral subspaces

This section establishes that the stable subspace `X_g(A)` and the antistable
subspace `X_b(A)` are disjoint, complementing the accepted spanning identity
`hurwitzSubspace_sup_unstableSubspace_eq_top`. Together they show that the
stable/antistable decomposition is direct; this is the assertion behind the
direct sum `X = X_g(A) ⊕ X_b(A)`.

At the complexified coordinate level the two subspaces are suprema of the
generalized eigenspaces for the disjoint index sets `{re μ < 0}` and
`{re μ ≥ 0}`. Mathlib's `iSupIndep.disjoint_biSup_biSup` applies to the
independent family `Module.End.maxGenEigenspace`. Transporting along the
injective real-coordinate map gives the real statement. -/

/-- The complex stable and antistable coordinate subspaces are disjoint, being
suprema of generalized eigenspaces over the disjoint index sets `re < 0` and
`re ≥ 0`. -/
theorem disjoint_hurwitzComplexSubspace_unstableComplexSubspace (A : X →ₗ[ℝ] X) :
    Disjoint (hurwitzComplexSubspace A) (unstableComplexSubspace A) := by
  let F := Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))
  have hf : iSupIndep (Module.End.maxGenEigenspace F) :=
    Module.End.independent_maxGenEigenspace F
  have hd := hf.disjoint_biSup_biSup (s := {μ : ℂ | μ.re < 0})
    (t := {μ : ℂ | ¬ μ.re < 0}) (by
      rw [Set.disjoint_left]
      intro μ h1 h2
      exact h2 h1)
  simpa only [hurwitzComplexSubspace, unstableComplexSubspace, iSup_subtype,
    Set.mem_ofPred_eq] using hd

/-- The real stable and antistable subspaces are disjoint. Both are preimages of
the corresponding disjoint complex coordinate subspaces under the same injective
real-coordinate map, and preimage preserves infima. -/
theorem disjoint_hurwitzSubspace_unstableSubspace (A : X →ₗ[ℝ] X) :
    Disjoint (hurwitzSubspace A) (unstableSubspace A) := by
  have hc : hurwitzComplexSubspace A ⊓ unstableComplexSubspace A = ⊥ :=
    disjoint_iff.mp (disjoint_hurwitzComplexSubspace_unstableComplexSubspace A)
  rw [disjoint_iff, hurwitzSubspace, unstableSubspace, ← Submodule.comap_inf,
    ← Submodule.restrictScalars_inf, hc, Submodule.restrictScalars_bot, Submodule.comap_bot,
    LinearMap.ker_eq_bot]
  exact ofRealPi_injective.comp (Module.finBasis ℝ X).equivFun.injective

/-- The stable/antistable decomposition is direct: `X = X_g(A) ⊕ X_b(A)`. -/
theorem isCompl_hurwitzSubspace_unstableSubspace (A : X →ₗ[ℝ] X) :
    IsCompl (hurwitzSubspace A) (unstableSubspace A) :=
  ⟨disjoint_hurwitzSubspace_unstableSubspace A,
   codisjoint_iff.mpr (hurwitzSubspace_sup_unstableSubspace_eq_top A)⟩

/-- Dimension additivity of the direct stable/antistable decomposition. -/
theorem finrank_hurwitzSubspace_add_finrank_unstableSubspace (A : X →ₗ[ℝ] X) :
    Module.finrank ℝ (hurwitzSubspace A) + Module.finrank ℝ (unstableSubspace A) =
      Module.finrank ℝ X :=
  Submodule.finrank_add_eq_of_isCompl (isCompl_hurwitzSubspace_unstableSubspace A)

/-! ## Restriction transport for the spectral subspaces

The generalized eigenspaces of `A` restricted to an `A`-invariant subspace `p`
map into the generalized eigenspaces of `A`, so the stable and antistable
spectral subspaces of `A|_p` map into the corresponding spectral subspaces of
`A`. This is the forward (image) half of
`map p.subtype '' X_b(A|_p) = X_b(A) ⊓ p`. -/

/-- Coordinate-matrix transport for an arbitrary supremum of generalized
eigenspaces of `A` restricted to an invariant `p`. -/
theorem map_iSup_maxGenEigenspace_restrict_le
    (A : X →ₗ[ℝ] X) (p : Submodule ℝ X) (hp : ∀ x ∈ p, A x ∈ p) (q : ℂ → Prop) :
    Submodule.map
        (Matrix.toLin' ((LinearMap.toMatrix (Module.finBasis ℝ p) (Module.finBasis ℝ X)
          p.subtype).map (algebraMap ℝ ℂ)))
        (⨆ μ : {μ : ℂ // q μ},
          Module.End.maxGenEigenspace
            (Matrix.toLin' ((hurwitzMatrix (A.restrict hp)).map (algebraMap ℝ ℂ))) μ.1) ≤
      ⨆ μ : {μ : ℂ // q μ},
        Module.End.maxGenEigenspace
          (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) μ.1 := by
  have hsub : A.comp p.subtype = p.subtype.comp (A.restrict hp) := by
    ext x
    rfl
  have hmat : LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ X) A *
        LinearMap.toMatrix (Module.finBasis ℝ p) (Module.finBasis ℝ X) p.subtype =
      LinearMap.toMatrix (Module.finBasis ℝ p) (Module.finBasis ℝ X) p.subtype *
        LinearMap.toMatrix (Module.finBasis ℝ p) (Module.finBasis ℝ p) (A.restrict hp) := by
    rw [← LinearMap.toMatrix_comp (v₁ := Module.finBasis ℝ p) (v₂ := Module.finBasis ℝ X)
          (v₃ := Module.finBasis ℝ X) A p.subtype, hsub,
      LinearMap.toMatrix_comp (v₁ := Module.finBasis ℝ p) (v₂ := Module.finBasis ℝ p)
        (v₃ := Module.finBasis ℝ X) p.subtype (A.restrict hp)]
  have hmatc :
      (LinearMap.toMatrix (Module.finBasis ℝ p) (Module.finBasis ℝ X) p.subtype).map
          (algebraMap ℝ ℂ) *
        (LinearMap.toMatrix (Module.finBasis ℝ p) (Module.finBasis ℝ p) (A.restrict hp)).map
          (algebraMap ℝ ℂ) =
      (LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ X) A).map
          (algebraMap ℝ ℂ) *
        (LinearMap.toMatrix (Module.finBasis ℝ p) (Module.finBasis ℝ X) p.subtype).map
          (algebraMap ℝ ℂ) := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hmat]
  rw [Submodule.map_iSup]
  refine iSup_le fun ν => ?_
  exact le_iSup_of_le ν (map_toLin'_maxGenEigenspace _ _ _ ν.1 hmatc)

/-- **Forward stable transport.** The image of the stable subspace of the
restriction `A|_p` under the inclusion `p ↪ X` lies in the stable subspace of
`A`. -/
theorem map_hurwitzSubspace_restrict_le (A : X →ₗ[ℝ] X) (p : Submodule ℝ X)
    (hp : ∀ x ∈ p, A x ∈ p) :
    Submodule.map p.subtype (hurwitzSubspace (A.restrict hp)) ≤ hurwitzSubspace A := by
  rw [Submodule.map_le_iff_le_comap]
  intro y hy
  rw [Submodule.mem_comap]
  rw [mem_hurwitzSubspace] at hy ⊢
  rw [← ofRealPi_equivFun_toLin'_apply p.subtype y]
  exact map_iSup_maxGenEigenspace_restrict_le A p hp (fun μ => μ.re < 0)
    ⟨_, hy, rfl⟩

/-- **Forward antistable transport.** The image of the antistable subspace of
the restriction `A|_p` under the inclusion `p ↪ X` lies in the antistable
subspace of `A`. -/
theorem map_unstableSubspace_restrict_le (A : X →ₗ[ℝ] X) (p : Submodule ℝ X)
    (hp : ∀ x ∈ p, A x ∈ p) :
    Submodule.map p.subtype (unstableSubspace (A.restrict hp)) ≤ unstableSubspace A := by
  rw [Submodule.map_le_iff_le_comap]
  intro y hy
  rw [Submodule.mem_comap]
  rw [mem_unstableSubspace] at hy ⊢
  rw [← ofRealPi_equivFun_toLin'_apply p.subtype y]
  exact map_iSup_maxGenEigenspace_restrict_le A p hp (fun μ => ¬ μ.re < 0)
    ⟨_, hy, rfl⟩

/-! ## The converse of the Hurwitz/unstable-subspace equivalence

The accepted direction `unstableSubspace_eq_bot_of_isHurwitz` says that a
Hurwitz operator has trivial antistable subspace. The converse is needed to
deduce stability of an operator from the vanishing of its antistable part. It
follows from the fact that the complexified coordinate antistable subspace is
nonzero as soon as the complexified operator has a non-Hurwitz eigenvalue, and
from the correspondence between the real and complexified antistable subspaces
via `star`-invariance. -/

/-- A real operator has trivial antistable subspace exactly when its
complexified coordinate antistable subspace is trivial. -/
theorem unstableSubspace_eq_bot_iff_unstableComplexSubspace_eq_bot (A : X →ₗ[ℝ] X) :
    unstableSubspace A = ⊥ ↔ unstableComplexSubspace A = ⊥ := by
  constructor
  · intro h
    by_contra hc
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
    have hstar : star z ∈ unstableComplexSubspace A := star_mem_unstableComplexSubspace A hz
    have hsum : z + star z ∈ unstableComplexSubspace A :=
      Submodule.add_mem _ hz hstar
    have hdiff : (Complex.I : ℂ) • (z - star z) ∈ unstableComplexSubspace A :=
      Submodule.smul_mem _ _ (Submodule.sub_mem _ hz hstar)
    have hfix_sum : star (z + star z) = z + star z := by
      rw [star_add, star_star, add_comm]
    have hfix_diff : star ((Complex.I : ℂ) • (z - star z)) = (Complex.I : ℂ) • (z - star z) := by
      have hI : star (Complex.I : ℂ) = -(Complex.I : ℂ) :=
        (by simp only [Complex.star_def, Complex.conj_I] :
          star (Complex.I : ℂ) = -(Complex.I : ℂ))
      rw [star_smul, star_sub, star_star, hI]
      module
    have hz0' : z + star z ≠ 0 ∨ (Complex.I : ℂ) • (z - star z) ≠ 0 := by
      by_contra hcon
      simp only [not_or, not_not] at hcon
      obtain ⟨h1, h2⟩ := hcon
      apply hz0
      have hz_eq : z = -star z := add_eq_zero_iff_eq_neg.mp h1
      have hz_eq' : star z = -z := by
        have := congrArg star hz_eq
        simp only [star_neg, star_star] at this
        exact this
      have h2' : z + z = 0 := by
        have h3 : z - star z = 0 := by
          rw [smul_eq_zero] at h2
          rcases h2 with hh | hh
          · exact absurd hh Complex.I_ne_zero
          · exact hh
        rw [hz_eq'] at h3
        simpa using h3
      exact (smul_eq_zero.mp (by rw [two_smul]; exact h2')).resolve_left
        (by norm_num : (2 : ℂ) ≠ 0)
    rcases hz0' with h1 | h2
    · obtain ⟨a, ha⟩ := exists_ofRealPi_of_star_eq hfix_sum
      have hxmem : (Module.finBasis ℝ X).equivFun.symm a ∈ unstableSubspace A := by
        rw [mem_unstableSubspace, LinearEquiv.apply_symm_apply, ha]
        exact hsum
      have hx0 : (Module.finBasis ℝ X).equivFun.symm a ≠ 0 := by
        intro h0
        apply h1
        have ha0 : a = 0 := by
          rw [← (Module.finBasis ℝ X).equivFun.apply_symm_apply a, h0, map_zero]
        rw [← ha, ha0, map_zero]
      exact hx0 (by rw [h] at hxmem; exact hxmem)
    · obtain ⟨a, ha⟩ := exists_ofRealPi_of_star_eq hfix_diff
      have hxmem : (Module.finBasis ℝ X).equivFun.symm a ∈ unstableSubspace A := by
        rw [mem_unstableSubspace, LinearEquiv.apply_symm_apply, ha]
        exact hdiff
      have hx0 : (Module.finBasis ℝ X).equivFun.symm a ≠ 0 := by
        intro h0
        apply h2
        have ha0 : a = 0 := by
          rw [← (Module.finBasis ℝ X).equivFun.apply_symm_apply a, h0, map_zero]
        rw [← ha, ha0, map_zero]
      exact hx0 (by rw [h] at hxmem; exact hxmem)
  · intro h
    rw [unstableSubspace, h, Submodule.restrictScalars_bot, Submodule.comap_bot,
      LinearMap.ker_eq_bot]
    exact ofRealPi_injective.comp (Module.finBasis ℝ X).equivFun.injective

/-- An operator with trivial antistable subspace is Hurwitz. -/
theorem isHurwitz_of_unstableSubspace_eq_bot (A : X →ₗ[ℝ] X)
    (h : unstableSubspace A = ⊥) : IsHurwitz A := by
  intro μ hμ
  by_contra hμre
  have hUc : unstableComplexSubspace A ≠ ⊥ := by
    intro hbot
    have heig : Module.End.HasEigenvalue
        (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) μ :=
      (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).mpr (by
        rw [charpoly_hurwitzMatrix_map_eq]; exact hμ)
    obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
    have hv0 : v ≠ 0 := hv.2
    have hveig : v ∈ Module.End.maxGenEigenspace
        (Matrix.toLin' ((hurwitzMatrix A).map (algebraMap ℝ ℂ))) μ := by
      rw [Module.End.mem_maxGenEigenspace]
      refine ⟨1, ?_⟩
      rw [pow_one]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
        Module.End.mem_eigenspace_iff.mp hv.1, sub_self]
    have hmem : v ∈ unstableComplexSubspace A := by
      rw [unstableComplexSubspace]
      exact Submodule.mem_iSup_of_mem ⟨μ, hμre⟩ hveig
    exact hv0 (by rw [hbot] at hmem; exact hmem)
  exact hUc ((unstableSubspace_eq_bot_iff_unstableComplexSubspace_eq_bot A).mp h)

/-- **Top-characterization of detectability.** The pair `(C, A)` is detectable
exactly when its detectable (undetectable) subspace
`Xdet(C, A) = X_b(A) ∩ ⟨ker C | A⟩` is trivial.

The forward direction uses the accepted Hurwitz unobservable complement: the
restriction `A|_N` to `N = ⟨ker C | A⟩` is Hurwitz, so its antistable part
vanishes; the stable/antistable direct sum for `A|_N` and the forward stable
transport `map N.subtype (X_g(A|_N)) ≤ X_g(A)` then give `N ≤ X_g(A)`, whence
`Xdet = X_b(A) ∩ N ≤ X_b(A) ∩ X_g(A) = 0` by disjointness.

The reverse direction first uses the forward antistable transport to deduce
`X_b(A|_N) = 0` from `Xdet = 0`, then the converse Hurwitz/unstable-subspace
equivalence to obtain `IsHurwitz (A|_N)`, and finally
`isDetectable_of_isHurwitz_unobservableRestriction` to construct the output
injection.

Source: Trentelman–Stoorvogel–Hautus, Theorem 5.16 (equivalences (i) and
(iii)). -/
theorem isDetectable_iff_detectableSubspace_eq_bot (C : X →ₗ[ℝ] Y) (A : X →ₗ[ℝ] X) :
    IsDetectable C A ↔ detectableSubspace C A = ⊥ := by
  let N := unobservableSubspace C A
  let hN : ∀ x ∈ N, A x ∈ N := fun _ hx => map_unobservableSubspace_le C A ⟨_, hx, rfl⟩
  have hrestrict : unobservableRestrictionA C A = A.restrict hN := rfl
  constructor
  · intro h
    have hAN : IsHurwitz (unobservableRestrictionA C A) :=
      isHurwitz_on_detectableComplement C A h
    have hUN : unstableSubspace (unobservableRestrictionA C A) = ⊥ :=
      unstableSubspace_eq_bot_of_isHurwitz _ hAN
    have hHN : hurwitzSubspace (unobservableRestrictionA C A) = ⊤ := by
      have hsup := hurwitzSubspace_sup_unstableSubspace_eq_top (unobservableRestrictionA C A)
      rw [hUN, sup_bot_eq] at hsup
      exact hsup
    have hmap := map_hurwitzSubspace_restrict_le A N hN
    rw [← hrestrict, hHN, Submodule.map_subtype_top] at hmap
    rw [detectableSubspace]
    apply le_bot_iff.mp
    calc N ⊓ unstableSubspace A ≤ hurwitzSubspace A ⊓ unstableSubspace A :=
          inf_le_inf hmap le_rfl
      _ = ⊥ := disjoint_iff.mp (disjoint_hurwitzSubspace_unstableSubspace A)
  · intro h
    have hUN : unstableSubspace (unobservableRestrictionA C A) = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      rw [hrestrict] at hx
      have hxmap : ((N.subtype) x) ∈
          Submodule.map N.subtype (unstableSubspace (A.restrict hN)) :=
        ⟨x, hx, rfl⟩
      have hsub := map_unstableSubspace_restrict_le A N hN hxmap
      have hmem : ((N.subtype) x) ∈ detectableSubspace C A := by
        rw [detectableSubspace]
        exact ⟨x.2, hsub⟩
      rw [h] at hmem
      exact Subtype.ext (by simpa using hmem)
    have hAN : IsHurwitz (unobservableRestrictionA C A) :=
      isHurwitz_of_unstableSubspace_eq_bot _ hUN
    exact isDetectable_of_isHurwitz_unobservableRestriction C A hAN


/-! ## Basis-agnostic spectral subspaces on an arbitrary finite-dimensional real space

The definitions `hurwitzSubspace` and `unstableSubspace` in this file are stated
under the global `[NormedAddCommGroup X] [NormedSpace ℝ X]` variables, although
neither definition uses the norm: both only unfold `Module.finBasis` and the
matrix/`ofRealPi` construction. This blocks their use on the algebraic dual
`Module.Dual ℝ X`, which carries no norm and no `Module.finBasis`-compatible
normed instance, and is exactly the obstruction recorded in the handoff for the
output-injection half of Corollary 6.22.

The definitions below remove the norm from the interface: they are stated for an
arbitrary real finite-dimensional vector space `M` and an arbitrary finite basis
`b`, with no normed hypotheses. Specialising `b := Module.finBasis ℝ X` recovers
the accepted `hurwitzSubspace`/`unstableSubspace` definitionally (see
`hurwitzSubspace_eq_stableSubspaceOfBasis`), so the new API is a conservative
generalisation. Applying them to `M := Module.Dual ℝ X` with
`b := Module.finBasis ℝ (Module.Dual ℝ X)` makes the transpose stable subspace
`stableSubspaceOfBasis (Module.finBasis ℝ (Module.Dual ℝ X)) A.dualMap` a
well-typed object.

The missing step for the duality identity is recorded in the handoff: the
basis-independence of `stableSubspaceOfBasis` (equivalently, that it agrees with
the canonical complexification `⨆_{re<0} maxGenEigenspace (A.baseChange ℂ)`
under `x ↦ 1 ⊗ₜ x`) and the transpose spectral duality
`(unstableSubspace A).dualAnnihilator = stableSubspaceOfBasis … A.dualMap`.
-/

section BasisSpectralSubspace

variable {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]

/-- The complex spectral subspace of an endomorphism in an arbitrary finite
basis `b`, at the eigenvalues with real part satisfying a predicate `q`. -/
noncomputable def complexSpectralSubspaceOfBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ M) (A : M →ₗ[ℝ] M) (q : ℂ → Prop) : Submodule ℂ (ι → ℂ) :=
  ⨆ μ : {μ : ℂ // q μ},
    Module.End.maxGenEigenspace
      (Matrix.toLin' ((LinearMap.toMatrix b b A).map (algebraMap ℝ ℂ))) μ.1

/-- The **stable subspace** `X_g(A)` in an arbitrary finite basis: the pull-back
along the real coordinates of the sum of generalized eigenspaces at the
eigenvalues with negative real part. This is the norm-free form of
`hurwitzSubspace`. -/
noncomputable def stableSubspaceOfBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ M) (A : M →ₗ[ℝ] M) : Submodule ℝ M :=
  ((complexSpectralSubspaceOfBasis b A (fun μ => μ.re < 0)).restrictScalars ℝ).comap
    (ofRealPi.comp b.equivFun.toLinearMap)

/-- The **antistable subspace** `X_b(A)` in an arbitrary finite basis: the
pull-back along the real coordinates of the sum of generalized eigenspaces at
the eigenvalues with nonnegative real part. This is the norm-free form of
`unstableSubspace`. -/
noncomputable def unstableSubspaceOfBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ M) (A : M →ₗ[ℝ] M) : Submodule ℝ M :=
  ((complexSpectralSubspaceOfBasis b A (fun μ => ¬ μ.re < 0)).restrictScalars ℝ).comap
    (ofRealPi.comp b.equivFun.toLinearMap)

omit [FiniteDimensional ℝ M] in
/-- The coordinate pull-back is measurable/injective as before: membership in
`stableSubspaceOfBasis` is exactly membership of the complex coordinates in the
complex spectral subspace. -/
theorem mem_stableSubspaceOfBasis {ι : Type*} [Fintype ι] [DecidableEq ι]
    {b : Basis ι ℝ M} {A : M →ₗ[ℝ] M} {x : M} :
    x ∈ stableSubspaceOfBasis b A ↔
      ofRealPi (b.equivFun x) ∈ complexSpectralSubspaceOfBasis b A (fun μ => μ.re < 0) := by
  rw [stableSubspaceOfBasis, Submodule.mem_comap, Submodule.restrictScalars_mem]
  rfl

/-- **Conservative generalisation.** For the canonical basis `Module.finBasis`,
the basis-agnostic stable subspace is definitionally the accepted
`hurwitzSubspace`. -/
theorem stableSubspaceOfBasis_finBasis_eq_hurwitzSubspace (A : X →ₗ[ℝ] X) :
    stableSubspaceOfBasis (Module.finBasis ℝ X) A = hurwitzSubspace A := rfl

/-- **Conservative generalisation.** For the canonical basis `Module.finBasis`,
the basis-agnostic antistable subspace is definitionally the accepted
`unstableSubspace`. -/
theorem unstableSubspaceOfBasis_finBasis_eq_unstableSubspace (A : X →ₗ[ℝ] X) :
    unstableSubspaceOfBasis (Module.finBasis ℝ X) A = unstableSubspace A := rfl

/-! ### The canonical complexified spectral subspaces and basis independence

The coordinate definitions `complexSpectralSubspaceOfBasis` and
`stableSubspaceOfBasis`/`unstableSubspaceOfBasis` above compute a basis-dependent
matrix, but the generalized eigenspaces they collect are the base-changed ones.
Below we record the canonical objects inside the complexification `ℂ ⊗[ℝ] M` and
show that the coordinate pull-back along *any* basis `b` recovers exactly those
objects. Consequently the stable and antistable subspaces do not depend on the
chosen basis, which is the norm-free spectral identity needed to apply the
definitions to the algebraic dual `Module.Dual ℝ X`.

The only new input is the arbitrary-basis `baseChange` dictionary:
`b.equivFun` intertwines `A.baseChange ℂ` with the complexified coordinate matrix
`(toMatrix b b A).map (algebraMap ℝ ℂ)`. This is the general-field form of
`baseChange_repr_comp`, and it is exactly the commuting-square hypothesis of the
accepted `map_maxGenEigenspace_of_equiv`. -/

open scoped TensorProduct in
/-- The canonical complex **stable subspace** of `A` inside the complexification
`ℂ ⊗[ℝ] M`: the sum of generalized eigenspaces of the base-changed operator
`A.baseChange ℂ` at the eigenvalues with negative real part. This is the
basis-independent object computed by `complexSpectralSubspaceOfBasis`. -/
noncomputable def complexStableSubspace (A : M →ₗ[ℝ] M) : Submodule ℂ (ℂ ⊗[ℝ] M) :=
  ⨆ μ : {μ : ℂ // μ.re < 0}, Module.End.maxGenEigenspace (A.baseChange ℂ) μ.1

open scoped TensorProduct in
/-- The canonical complex **antistable subspace** of `A` inside the
complexification `ℂ ⊗[ℝ] M`: the sum of generalized eigenspaces of the
base-changed operator `A.baseChange ℂ` at the eigenvalues with nonnegative real
part. This is the basis-independent object computed by
`complexSpectralSubspaceOfBasis`. -/
noncomputable def complexUnstableSubspace (A : M →ₗ[ℝ] M) : Submodule ℂ (ℂ ⊗[ℝ] M) :=
  ⨆ μ : {μ : ℂ // ¬ μ.re < 0}, Module.End.maxGenEigenspace (A.baseChange ℂ) μ.1

omit [FiniteDimensional ℝ M] in
/-- **Arbitrary-basis `baseChange` dictionary, basis form.** The base-changed
basis `b.baseChange ℂ` is the tensor-product basis `Algebra.TensorProduct.basis`.
This is the form used to invoke `LinearMap.toMatrix_baseChange` for an arbitrary
basis rather than only `Module.finBasis`. -/
theorem baseChange_eq_basis_gen {ι : Type*}
    (b : Basis ι ℝ M) :
    b.baseChange ℂ = Algebra.TensorProduct.basis ℂ b := by
  ext i
  simp [Module.Basis.baseChange_apply, Algebra.TensorProduct.basis_apply]

omit [FiniteDimensional ℝ M] in
/-- **Arbitrary-basis `baseChange` dictionary, coordinate form.** For any finite
basis `b` of `M`, the real-coordinate equivalence `b.equivFun` intertwines the
base-changed operator `A.baseChange ℂ` with the complexified coordinate matrix
`(toMatrix b b A).map (algebraMap ℝ ℂ)`. This is the general-basis form of
`baseChange_repr_comp` and the input to basis independence. -/
theorem baseChange_repr_comp_gen {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ M) (A : M →ₗ[ℝ] M) :
    (b.baseChange ℂ).equivFun.toLinearMap.comp (A.baseChange ℂ) =
      (Matrix.toLin' ((LinearMap.toMatrix b b A).map (algebraMap ℝ ℂ))).comp
        (b.baseChange ℂ).equivFun.toLinearMap := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  change (b.baseChange ℂ).repr ((A.baseChange ℂ) z) =
    (Matrix.toLin' ((LinearMap.toMatrix b b A).map (algebraMap ℝ ℂ)))
      ((b.baseChange ℂ).repr z)
  rw [baseChange_eq_basis_gen b,
    ← LinearMap.toMatrix_mulVec_repr (Algebra.TensorProduct.basis ℂ b)
      (Algebra.TensorProduct.basis ℂ b) (A.baseChange ℂ) z,
    LinearMap.toMatrix_baseChange, Matrix.toLin'_apply]

set_option linter.style.haveILetI false in
omit [FiniteDimensional ℝ M] in
/-- **Arbitrary-basis `baseChange` dictionary, tensor form.** The inverse real
coordinates of `x` recover the pure tensor `1 ⊗ₜ x` inside the complexification.
This is the general-basis form of `baseChange_equivFun_symm_one_tmul`. -/
theorem baseChange_equivFun_symm_one_tmul_gen {ι : Type*} [Finite ι]
    (b : Basis ι ℝ M) (x : M) :
    (b.baseChange ℂ).equivFun.symm (ofRealPi (b.equivFun x)) = (1 : ℂ) ⊗ₜ[ℝ] x := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  rw [Basis.equivFun_symm_apply]
  conv_rhs => rw [← b.sum_equivFun x, TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.Basis.baseChange_apply]
  simp only [ofRealPi_apply]
  rw [TensorProduct.tmul_smul]
  rfl

omit [FiniteDimensional ℝ M] in
/-- The coordinate pull-back along `b` identifies the canonical complex stable
subspace with the basis-dependent `complexSpectralSubspaceOfBasis`. This is the
commuting-eigenspace transport `map_maxGenEigenspace_of_equiv` applied to the
arbitrary-basis `baseChange` dictionary. -/
theorem map_complexStableSubspace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ M) (A : M →ₗ[ℝ] M) :
    Submodule.map (b.baseChange ℂ).equivFun.toLinearMap (complexStableSubspace A) =
      complexSpectralSubspaceOfBasis b A (fun μ => μ.re < 0) := by
  rw [complexStableSubspace, complexSpectralSubspaceOfBasis, Submodule.map_iSup]
  apply iSup_congr
  intro μ
  exact map_maxGenEigenspace_of_equiv (b.baseChange ℂ).equivFun (A.baseChange ℂ)
    (Matrix.toLin' ((LinearMap.toMatrix b b A).map (algebraMap ℝ ℂ))) μ.1
    (baseChange_repr_comp_gen b A).symm

omit [FiniteDimensional ℝ M] in
/-- The coordinate pull-back along `b` identifies the canonical complex
antistable subspace with the basis-dependent `complexSpectralSubspaceOfBasis`. -/
theorem map_complexUnstableSubspace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ M) (A : M →ₗ[ℝ] M) :
    Submodule.map (b.baseChange ℂ).equivFun.toLinearMap (complexUnstableSubspace A) =
      complexSpectralSubspaceOfBasis b A (fun μ => ¬ μ.re < 0) := by
  rw [complexUnstableSubspace, complexSpectralSubspaceOfBasis, Submodule.map_iSup]
  apply iSup_congr
  intro μ
  exact map_maxGenEigenspace_of_equiv (b.baseChange ℂ).equivFun (A.baseChange ℂ)
    (Matrix.toLin' ((LinearMap.toMatrix b b A).map (algebraMap ℝ ℂ))) μ.1
    (baseChange_repr_comp_gen b A).symm

omit [FiniteDimensional ℝ M] in
/-- **Basis-independent characterisation of the stable subspace.** A vector `x`
lies in the stable subspace computed in the basis `b` exactly when the pure
tensor `1 ⊗ₜ x` lies in the canonical complex stable subspace. This makes no
reference to `b`, so basis independence is immediate. -/
theorem mem_stableSubspaceOfBasis_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ M) (A : M →ₗ[ℝ] M) {x : M} :
    x ∈ stableSubspaceOfBasis b A ↔ (1 : ℂ) ⊗ₜ[ℝ] x ∈ complexStableSubspace A := by
  rw [mem_stableSubspaceOfBasis, ← map_complexStableSubspace b A]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have he1 : (b.baseChange ℂ).equivFun.toLinearMap ((1 : ℂ) ⊗ₜ[ℝ] x) =
        ofRealPi (b.equivFun x) := by
      rw [← baseChange_equivFun_symm_one_tmul_gen b x]
      exact (b.baseChange ℂ).equivFun.apply_symm_apply _
    have : y = (1 : ℂ) ⊗ₜ[ℝ] x := by
      apply (b.baseChange ℂ).equivFun.injective
      change (b.baseChange ℂ).equivFun.toLinearMap y =
        (b.baseChange ℂ).equivFun.toLinearMap ((1 : ℂ) ⊗ₜ[ℝ] x)
      rw [hyx, he1]
    rwa [this] at hy
  · intro hx
    exact ⟨(1 : ℂ) ⊗ₜ[ℝ] x, hx, by
      rw [← baseChange_equivFun_symm_one_tmul_gen b x]
      exact (b.baseChange ℂ).equivFun.apply_symm_apply _⟩

omit [FiniteDimensional ℝ M] in
/-- **Basis-independent characterisation of the antistable subspace.** -/
theorem mem_unstableSubspaceOfBasis_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι ℝ M) (A : M →ₗ[ℝ] M) {x : M} :
    x ∈ unstableSubspaceOfBasis b A ↔ (1 : ℂ) ⊗ₜ[ℝ] x ∈ complexUnstableSubspace A := by
  rw [unstableSubspaceOfBasis, Submodule.mem_comap, Submodule.restrictScalars_mem,
    ← map_complexUnstableSubspace b A]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have he1 : (b.baseChange ℂ).equivFun.toLinearMap ((1 : ℂ) ⊗ₜ[ℝ] x) =
        ofRealPi (b.equivFun x) := by
      rw [← baseChange_equivFun_symm_one_tmul_gen b x]
      exact (b.baseChange ℂ).equivFun.apply_symm_apply _
    have : y = (1 : ℂ) ⊗ₜ[ℝ] x := by
      apply (b.baseChange ℂ).equivFun.injective
      change (b.baseChange ℂ).equivFun.toLinearMap y =
        (b.baseChange ℂ).equivFun.toLinearMap ((1 : ℂ) ⊗ₜ[ℝ] x)
      rw [hyx, he1]
      rfl
    rwa [this] at hy
  · intro hx
    exact ⟨(1 : ℂ) ⊗ₜ[ℝ] x, hx, by
      rw [← baseChange_equivFun_symm_one_tmul_gen b x]
      exact (b.baseChange ℂ).equivFun.apply_symm_apply _⟩

omit [FiniteDimensional ℝ M] in
/-- **Basis independence of the stable subspace.** The stable subspace
`stableSubspaceOfBasis b A` does not depend on the chosen finite basis. -/
theorem stableSubspaceOfBasis_eq_of_basis {ι ι' : Type*} [Fintype ι] [Fintype ι']
    [DecidableEq ι] [DecidableEq ι']
    (b : Basis ι ℝ M) (b' : Basis ι' ℝ M) (A : M →ₗ[ℝ] M) :
    stableSubspaceOfBasis b A = stableSubspaceOfBasis b' A := by
  ext x
  rw [mem_stableSubspaceOfBasis_iff b A, mem_stableSubspaceOfBasis_iff b' A]

omit [FiniteDimensional ℝ M] in
/-- **Basis independence of the antistable subspace.** The antistable subspace
`unstableSubspaceOfBasis b A` does not depend on the chosen finite basis. -/
theorem unstableSubspaceOfBasis_eq_of_basis {ι ι' : Type*} [Fintype ι] [Fintype ι']
    [DecidableEq ι] [DecidableEq ι']
    (b : Basis ι ℝ M) (b' : Basis ι' ℝ M) (A : M →ₗ[ℝ] M) :
    unstableSubspaceOfBasis b A = unstableSubspaceOfBasis b' A := by
  ext x
  rw [mem_unstableSubspaceOfBasis_iff b A, mem_unstableSubspaceOfBasis_iff b' A]

end BasisSpectralSubspace

/-! ## Real-coordinate transport of the antistable annihilator

The abstract complex transpose duality `dualAnnihilator_antistable_eq_stable`
identifies the annihilator of the antistable generalized-eigenspace sum of a
complex endomorphism with the stable generalized-eigenspace sum of its
transpose. This section transports that identity to the real state space: the
annihilator of the real antistable subspace `X_b(A) = unstableSubspace A` is the
stable subspace of the algebraic transpose `A.dualMap`, computed in the
canonical basis of the algebraic dual `Module.Dual ℝ X`.

The transport combines three ingredients.

* `complexUnstableSubspace_eq_baseChange_unstableSubspace`: the abstract
  complexification `complexUnstableSubspace A` is the base change of the real
  antistable subspace. The hard inclusion is
  `span_inter_range_ofRealPi_eq_of_star_mem`, which says that the complex span of
  the real points of a conjugation-stable subspace is the whole subspace.
* `dualAnnihilator_baseChange_iff`: the annihilator commutes with base change
  along `ℝ → ℂ`.
* `toDualBaseChange_one_tmul` and `map_toDualBaseChange_complexStableSubspace`:
  the ℂ-linear base-change equivalence of the dual
  `IsBaseChange.toDualBaseChange : ℂ ⊗[ℝ] Module.Dual ℝ X ≃ₗ[ℂ]
  Module.Dual ℂ (ℂ ⊗[ℝ] X)` sends `1 ⊗ φ` to the base-changed functional and
  intertwines the stable subspaces of `A.dualMap` and
  `(A.baseChange ℂ).dualMap`.

Source: Trentelman–Stoorvogel–Hautus, Theorem 5.13 and display (5.3), the
spectral form of the duality between stabilizability and detectability, with
the complexification bridge of Theorem 3.38. -/

open scoped TensorProduct in
/-- The complex span of the real points of a conjugation-stable subspace of
`ι → ℂ` is the subspace itself. Writing a vector `v` as
`v = ofRealPi (re v) + I • ofRealPi (im v)` exhibits it as a complex combination
of two real-valued vectors `(v ± star v) / 2` and `(v - star v) / (2 I)`, which
lie in `V` by conjugation stability. -/
theorem span_inter_range_ofRealPi_eq_of_star_mem {ι : Type*}
    (V : Submodule ℂ (ι → ℂ)) (hV : ∀ v ∈ V, star v ∈ V) :
    Submodule.span ℂ ((V : Set (ι → ℂ)) ∩ Set.range ofRealPi) = V := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro v ⟨hv, -⟩
    exact hv
  · intro v hv
    let re_v : ι → ℝ := fun i => (v i).re
    let im_v : ι → ℝ := fun i => (v i).im
    have hre : ofRealPi re_v ∈ V := by
      have h1 : ofRealPi re_v = (2 : ℂ)⁻¹ • (v + star v) := by
        ext i
        simp only [ofRealPi_apply, Pi.add_apply, Pi.star_apply, Pi.smul_apply, smul_eq_mul,
          re_v]
        rw [show star (v i) = (starRingEnd ℂ) (v i) from rfl]
        rw [Complex.re_eq_add_conj]
        ring
      rw [h1]
      exact V.smul_mem _ (V.add_mem hv (hV v hv))
    have him : ofRealPi im_v ∈ V := by
      have h1 : ofRealPi im_v = ((2 : ℂ) * Complex.I)⁻¹ • (v - star v) := by
        ext i
        simp only [ofRealPi_apply, Pi.sub_apply, Pi.star_apply, Pi.smul_apply, smul_eq_mul,
          im_v]
        rw [show star (v i) = (starRingEnd ℂ) (v i) from rfl]
        rw [Complex.im_eq_sub_conj]
        ring
      rw [h1]
      exact V.smul_mem _ (V.sub_mem hv (hV v hv))
    have hgen1 : ofRealPi re_v ∈ Submodule.span ℂ ((V : Set (ι → ℂ)) ∩ Set.range ofRealPi) :=
      Submodule.subset_span ⟨hre, ⟨re_v, rfl⟩⟩
    have hgen2 : ofRealPi im_v ∈ Submodule.span ℂ ((V : Set (ι → ℂ)) ∩ Set.range ofRealPi) :=
      Submodule.subset_span ⟨him, ⟨im_v, rfl⟩⟩
    have hvdecomp : v = ofRealPi re_v + Complex.I • ofRealPi im_v := by
      ext i
      simp only [ofRealPi_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, re_v, im_v]
      rw [mul_comm Complex.I]
      exact (Complex.re_add_im (v i)).symm
    rw [hvdecomp]
    exact (Submodule.span ℂ _).add_mem hgen1 ((Submodule.span ℂ _).smul_mem Complex.I hgen2)

section ComplexAntistableBaseChange

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

open scoped TensorProduct

/-- The canonical complex antistable subspace is the base change of the real
antistable subspace: `complexUnstableSubspace A = (unstableSubspace A).baseChange ℂ`.
The nontrivial inclusion uses that the coordinate image of the base change is
the complex span of the real points of `unstableComplexSubspace A`, which is
generated by those real points because the subspace is conjugation-stable. -/
theorem complexUnstableSubspace_eq_baseChange_unstableSubspace (A : X →ₗ[ℝ] X) :
    complexUnstableSubspace A = (unstableSubspace A).baseChange ℂ := by
  let b := Module.finBasis ℝ X
  let eX : ℂ ⊗[ℝ] X →ₗ[ℂ] (Fin (Module.finrank ℝ X) → ℂ) :=
    (b.baseChange ℂ).equivFun.toLinearMap
  have einj : Function.Injective eX := (b.baseChange ℂ).equivFun.injective
  let ψ : X →ₗ[ℝ] (Fin (Module.finrank ℝ X) → ℂ) :=
    ofRealPi.comp b.equivFun.toLinearMap
  have hcomp_fun : ∀ x : X, eX (TensorProduct.mk ℝ ℂ X 1 x) = ψ x := by
    intro x
    change (b.baseChange ℂ).equivFun (1 ⊗ₜ[ℝ] x) = ofRealPi (b.equivFun x)
    rw [← baseChange_equivFun_symm_one_tmul x]
    exact (b.baseChange ℂ).equivFun.apply_symm_apply _
  have hmapUnstable : Submodule.map eX (complexUnstableSubspace A) =
      unstableComplexSubspace A := by
    rw [map_complexUnstableSubspace b A]
    rfl
  have hψU : Set.image ψ (unstableSubspace A : Set X) =
      ((unstableComplexSubspace A : Submodule ℂ _) : Set _) ∩ Set.range ofRealPi := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, ⟨b.equivFun x, rfl⟩⟩
      change x ∈ unstableSubspace A at hx
      rw [mem_unstableSubspace] at hx
      exact hx
    · rintro ⟨hzV, y, hy⟩
      refine ⟨b.equivFun.symm y, ?_, ?_⟩
      · change b.equivFun.symm y ∈ unstableSubspace A
        rw [mem_unstableSubspace, b.equivFun.apply_symm_apply]
        exact hy.symm ▸ hzV
      · simp only [ψ, LinearMap.comp_apply]
        exact (congrArg ofRealPi (b.equivFun.apply_symm_apply y)).trans hy
  have hstar : ∀ v ∈ unstableComplexSubspace A, star v ∈ unstableComplexSubspace A :=
    fun v hv => star_mem_unstableComplexSubspace A hv
  have hspan : Submodule.span ℂ (Set.image ψ (unstableSubspace A : Set X)) =
      unstableComplexSubspace A := by
    rw [hψU]
    exact span_inter_range_ofRealPi_eq_of_star_mem _ hstar
  have hmapBase : Submodule.map eX ((unstableSubspace A).baseChange ℂ) =
      unstableComplexSubspace A := by
    rw [Submodule.baseChange_eq_span, Submodule.map_span]
    rw [show (↑(Submodule.map (TensorProduct.mk ℝ ℂ X 1) (unstableSubspace A)) : Set _) =
        (TensorProduct.mk ℝ ℂ X 1) '' (unstableSubspace A : Set X) from rfl]
    rw [show eX '' ((TensorProduct.mk ℝ ℂ X 1) '' (unstableSubspace A : Set X)) =
        Set.image ψ (unstableSubspace A : Set X) from ?_]
    · exact hspan
    · rw [← Set.image_comp]
      exact Set.image_congr (fun x _ => hcomp_fun x)
  have : Submodule.map eX ((unstableSubspace A).baseChange ℂ) =
      Submodule.map eX (complexUnstableSubspace A) := by
    rw [hmapBase, hmapUnstable]
  exact Submodule.map_injective_of_injective einj this.symm

end ComplexAntistableBaseChange

section DualAnnihilatorBaseChange

variable {M : Type*} [AddCommGroup M] [Module ℝ M]

open scoped TensorProduct

/-- Base change of a submodule and the algebraic dual commute: a functional
lies in the annihilator of `U` exactly when its base change lies in the
annihilator of the base-changed submodule. -/
theorem dualAnnihilator_baseChange_iff (U : Submodule ℝ M) (φ : Module.Dual ℝ M) :
    Module.Dual.baseChange ℂ φ ∈ (U.baseChange ℂ).dualAnnihilator ↔
      φ ∈ U.dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator, Submodule.mem_dualAnnihilator]
  constructor
  · intro h x hx
    have hmem : (1 : ℂ) ⊗ₜ[ℝ] x ∈ U.baseChange ℂ :=
      Submodule.tmul_mem_baseChange_of_mem 1 hx
    have h0 := h _ hmem
    rw [Module.Dual.baseChange_apply_tmul] at h0
    exact Complex.ofReal_injective (by simpa using h0)
  · intro h z hz
    have hK : U.baseChange ℂ ≤ LinearMap.ker (Module.Dual.baseChange ℂ φ) := by
      rw [Submodule.baseChange_eq_span]
      refine Submodule.span_le.mpr ?_
      rintro w ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker]
      change (Module.Dual.baseChange ℂ φ) ((1 : ℂ) ⊗ₜ[ℝ] x) = 0
      rw [Module.Dual.baseChange_apply_tmul, h x hx, zero_smul]
    exact hK hz

end DualAnnihilatorBaseChange

section DualBaseChangeTransport

variable {X : Type*} [AddCommGroup X] [Module ℝ X] [Module.Free ℝ X] [Module.Finite ℝ X]

open scoped TensorProduct

/-- The base-change equivalence of the dual sends `1 ⊗ φ` to the base-changed
functional. -/
theorem toDualBaseChange_one_tmul (φ : Module.Dual ℝ X) :
    (TensorProduct.isBaseChange ℝ X ℂ).toDualBaseChange ((1 : ℂ) ⊗ₜ[ℝ] φ) =
      Module.Dual.baseChange ℂ φ := by
  apply IsBaseChange.algHom_ext (TensorProduct.isBaseChange ℝ X ℂ)
  intro v
  rw [IsBaseChange.toDualBaseChange_tmul]
  simp [Module.Dual.baseChange_apply_tmul]

/-- Dualising commutes with base change for the algebraic transpose. -/
theorem toDualBaseChange_comp_dualMap_baseChange (A : X →ₗ[ℝ] X) :
    ((A.baseChange ℂ).dualMap).comp
        (TensorProduct.isBaseChange ℝ X ℂ).toDualBaseChange.toLinearMap =
      (TensorProduct.isBaseChange ℝ X ℂ).toDualBaseChange.toLinearMap.comp
        ((A.dualMap).baseChange ℂ) := by
  apply LinearMap.ext
  intro w
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul a φ =>
      apply IsBaseChange.algHom_ext (TensorProduct.isBaseChange ℝ X ℂ)
      intro v
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      have hL : ((A.baseChange ℂ).dualMap)
          ((TensorProduct.isBaseChange ℝ X ℂ).toDualBaseChange (a ⊗ₜ[ℝ] φ))
          (TensorProduct.mk ℝ ℂ X 1 v) = a * algebraMap ℝ ℂ (φ (A v)) := by
        rw [LinearMap.dualMap_apply]
        have h1 : (A.baseChange ℂ) (TensorProduct.mk ℝ ℂ X 1 v) =
            TensorProduct.mk ℝ ℂ X 1 (A v) := LinearMap.baseChange_tmul A v (a := (1 : ℂ))
        rw [h1, IsBaseChange.toDualBaseChange_tmul]
      have hR : (TensorProduct.isBaseChange ℝ X ℂ).toDualBaseChange
          ((A.dualMap).baseChange ℂ (a ⊗ₜ[ℝ] φ))
          (TensorProduct.mk ℝ ℂ X 1 v) = a * algebraMap ℝ ℂ (φ (A v)) := by
        rw [LinearMap.baseChange_tmul, IsBaseChange.toDualBaseChange_tmul]
        rfl
      exact hL.trans hR.symm

/-- The base-change equivalence of the dual transports the complex stable
subspace of `A.dualMap` to that of the dualised base change of `A`. -/
theorem map_toDualBaseChange_complexStableSubspace (A : X →ₗ[ℝ] X) :
    Submodule.map (TensorProduct.isBaseChange ℝ X ℂ).toDualBaseChange.toLinearMap
        (complexStableSubspace A.dualMap) =
      ⨆ ν : {ν : ℂ // ν.re < 0},
        Module.End.maxGenEigenspace ((A.baseChange ℂ).dualMap) ν.1 := by
  rw [complexStableSubspace, Submodule.map_iSup]
  apply iSup_congr
  intro ν
  exact map_maxGenEigenspace_of_equiv
    (TensorProduct.isBaseChange ℝ X ℂ).toDualBaseChange
    ((A.dualMap).baseChange ℂ) ((A.baseChange ℂ).dualMap) ν.1
    (toDualBaseChange_comp_dualMap_baseChange A)

end DualBaseChangeTransport

section DualAnnihilatorUnstableTransport

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

open scoped TensorProduct

/-- **Real-coordinate transport of the antistable annihilator.** The annihilator
of the real antistable subspace `X_b(A) = unstableSubspace A` is the stable
subspace of the algebraic transpose `A.dualMap`, computed in the canonical
basis of the algebraic dual `Module.Dual ℝ X`:

`(unstableSubspace A).dualAnnihilator =
  stableSubspaceOfBasis (Module.finBasis ℝ (Module.Dual ℝ X)) A.dualMap`.

This is the real form of the complex transpose spectral duality
`dualAnnihilator_antistable_eq_stable`, transported across the base-change
equivalence `IsBaseChange.toDualBaseChange` of the dual. It is the missing
bridge for the output-injection half of Trentelman–Stoorvogel–Hautus Corollary
6.22: `(X_b(A))ᵃⁿⁿ = X_g(Aᵀ)`. -/
theorem dualAnnihilator_unstableSubspace_eq_stableSubspace_dualMap (A : X →ₗ[ℝ] X) :
    (unstableSubspace A).dualAnnihilator =
      stableSubspaceOfBasis (Module.finBasis ℝ (Module.Dual ℝ X)) A.dualMap := by
  ext φ
  rw [Submodule.mem_dualAnnihilator, mem_stableSubspaceOfBasis_iff]
  have h1 : (∀ x ∈ unstableSubspace A, φ x = 0) ↔
      Module.Dual.baseChange ℂ φ ∈ (complexUnstableSubspace A).dualAnnihilator := by
    rw [complexUnstableSubspace_eq_baseChange_unstableSubspace A,
      ← Submodule.mem_dualAnnihilator]
    exact (dualAnnihilator_baseChange_iff (unstableSubspace A) φ).symm
  rw [h1]
  unfold complexUnstableSubspace
  rw [dualAnnihilator_antistable_eq_stable (A.baseChange ℂ)]
  rw [← toDualBaseChange_one_tmul φ, ← map_toDualBaseChange_complexStableSubspace A]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h : y = (1 : ℂ) ⊗ₜ[ℝ] φ :=
      (TensorProduct.isBaseChange ℝ X ℂ).toDualBaseChange.injective hyx
    rwa [h] at hy
  · intro h
    exact ⟨_, h, rfl⟩

end DualAnnihilatorUnstableTransport

/-! ## Polynomial-exponential reduction

The accepted character-isolation lemma `tendsto_zero_of_sum_pow_smul` handles a
finite sum of *constant* coefficients against distinct unit-modulus characters.
The Bohl/spectral readout argument needs the next layer: a finite sum of
vector-valued *polynomial* terms times a character that tends to zero must have
all coefficients zero. The reduction is done in three steps, mirroring the
source proof recorded in `DynamicalSystems.Linear.DynamicFeedback`:

* `tendsto_zero_of_sum_pow_smul_polynomial`: the discrete reduction
  `∑ i, z i ^ n • (∑ k ≤ D, n ^ k • a i k) → 0` with distinct unit-modulus
  `z i`, proved by induction on the degree `D`, isolating the top coefficient
  with the accepted character lemma and discarding the lower-order terms.
* `tendsto_zero_of_sum_exp_polynomial_re_zero`: the continuous version when all
  real parts vanish, obtained by sampling `t = n * δ` for a scaling `δ` chosen
  so that the unit-modulus characters `exp (δ * μ i)` stay distinct.

The general `Re μ i ≥ 0` case is obtained by factoring out the dominant real
part and inducting on the number of modes; see
`tendsto_zero_of_sum_exp_polynomial`. -/

/-- **A polynomial of degree `< D` divided by one extra power.** For `n ≥ 1`
and `k ≤ D`, `n ^ k / n ^ (D + 1) ≤ 1 / n`. This elementary bound removes the
lower-order terms after the top coefficient has been isolated. -/
lemma inv_pow_mul_pow_le_inv (n D k : ℕ) (hn : 0 < n) (hk : k ≤ D) :
    ((n : ℝ) ^ (D + 1))⁻¹ * (n : ℝ) ^ k ≤ (n : ℝ)⁻¹ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by
    have : (1 : ℕ) ≤ n := hn
    exact_mod_cast this
  have hle : k ≤ D + 1 := by omega
  have h1 : ((n : ℝ) ^ (D + 1))⁻¹ * (n : ℝ) ^ k = 1 / (n : ℝ) ^ (D + 1 - k) := by
    rw [mul_comm, ← div_eq_mul_inv, pow_sub₀ (n:ℝ) (by positivity) hle]
    rw [div_eq_mul_inv, one_div, mul_inv, inv_inv, mul_comm]
  rw [h1]
  have hle2 : (n : ℝ) ≤ (n : ℝ) ^ (D + 1 - k) := by
    simpa using pow_le_pow_right₀ hn1 (by omega : 1 ≤ D + 1 - k)
  simpa [one_div] using one_div_le_one_div_of_le hnpos hle2

/-- **Polynomial growth is dominated by one extra power.** For unit-modulus
characters `z i`, a polynomial in `n` of degree at most `D` divided by
`n ^ (D + 1)` tends to zero. This is the elementary step that removes the
lower-degree terms after the top coefficient has been isolated. -/
lemma tendsto_inv_pow_smul_sum_range {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {ι : Type*} (s : Finset ι) (z : ι → ℂ) (hz : ∀ i ∈ s, ‖z i‖ = 1)
    (D : ℕ) (a : ι → ℕ → W) :
    Tendsto (fun n : ℕ => ((n : ℂ) ^ (D + 1))⁻¹ •
      (∑ i ∈ s, (z i) ^ n •
        (∑ k ∈ Finset.range (D + 1), (n : ℂ) ^ k • a i k))) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  set C : ℝ := ∑ i ∈ s, ∑ k ∈ Finset.range (D + 1), ‖a i k‖ with hC
  refine squeeze_zero (g := fun n : ℕ => C / n) (fun n => by positivity) (fun n => ?_) ?_
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · calc
        ‖((n : ℂ) ^ (D + 1))⁻¹ •
            (∑ i ∈ s, (z i) ^ n •
              (∑ k ∈ Finset.range (D + 1), (n : ℂ) ^ k • a i k))‖
            ≤ ∑ i ∈ s, ‖((n : ℂ) ^ (D + 1))⁻¹ •
                ((z i) ^ n •
                  (∑ k ∈ Finset.range (D + 1), (n : ℂ) ^ k • a i k))‖ := by
              rw [Finset.smul_sum]
              exact norm_sum_le _ _
          _ ≤ ∑ i ∈ s, (n : ℝ)⁻¹ * (∑ k ∈ Finset.range (D + 1), ‖a i k‖) := by
              apply Finset.sum_le_sum
              intro i hi
              rw [smul_smul, norm_smul, norm_mul, norm_pow, hz i hi, one_pow, mul_one]
              rw [norm_inv, norm_pow, Complex.norm_natCast]
              have hX : ‖∑ k ∈ Finset.range (D + 1), (n : ℂ) ^ k • a i k‖ ≤
                  ∑ k ∈ Finset.range (D + 1), (n : ℝ) ^ k * ‖a i k‖ := by
                calc ‖∑ k ∈ Finset.range (D + 1), (n : ℂ) ^ k • a i k‖
                    ≤ ∑ k ∈ Finset.range (D + 1), ‖(n : ℂ) ^ k • a i k‖ :=
                      norm_sum_le _ _
                  _ = ∑ k ∈ Finset.range (D + 1), (n : ℝ) ^ k * ‖a i k‖ := by
                      apply Finset.sum_congr rfl
                      intro k hk
                      rw [norm_smul, norm_pow, Complex.norm_natCast]
              calc ((n : ℝ) ^ (D + 1))⁻¹ *
                    ‖∑ k ∈ Finset.range (D + 1), (n : ℂ) ^ k • a i k‖
                  ≤ ((n : ℝ) ^ (D + 1))⁻¹ *
                      (∑ k ∈ Finset.range (D + 1), (n : ℝ) ^ k * ‖a i k‖) :=
                    mul_le_mul_of_nonneg_left hX (by positivity)
                _ = ∑ k ∈ Finset.range (D + 1),
                      ((n : ℝ) ^ (D + 1))⁻¹ * ((n : ℝ) ^ k * ‖a i k‖) := by
                    rw [Finset.mul_sum]
                _ ≤ ∑ k ∈ Finset.range (D + 1), (n : ℝ)⁻¹ * ‖a i k‖ := by
                    apply Finset.sum_le_sum
                    intro k hk
                    rw [Finset.mem_range] at hk
                    rw [← mul_assoc]
                    exact mul_le_mul_of_nonneg_right
                      (inv_pow_mul_pow_le_inv n D k hn (Nat.lt_succ_iff.mp hk))
                      (norm_nonneg (a i k))
                _ = (n : ℝ)⁻¹ * (∑ k ∈ Finset.range (D + 1), ‖a i k‖) := by
                    rw [Finset.mul_sum]
          _ = (n : ℝ)⁻¹ * C := by rw [hC, Finset.mul_sum]
          _ = C / n := by rw [div_eq_inv_mul]
  · exact tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) C

/-- **Polynomial-exponential reduction, discrete form.** A finite sum of
polynomial terms against distinct unit-modulus characters cannot tend to zero
at `+∞` unless every polynomial coefficient vanishes. The proof is induction on
the degree bound `D`: dividing by `n ^ (D + 1)` isolates the top coefficient,
which the accepted character lemma `tendsto_zero_of_sum_pow_smul` forces to be
zero, and the remaining lower-degree sum is handled by the induction
hypothesis. -/
lemma tendsto_zero_of_sum_pow_smul_polynomial {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] {ι : Type*} (s : Finset ι) (z : ι → ℂ)
    (hz : ∀ i ∈ s, ‖z i‖ = 1)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, z i = z j → i = j)
    (D : ℕ) (a : ι → ℕ → W)
    (h : Tendsto (fun n : ℕ => ∑ i ∈ s, (z i) ^ n •
        (∑ k ∈ Finset.range (D + 1), (n : ℂ) ^ k • a i k)) atTop (𝓝 0)) :
    ∀ i ∈ s, ∀ k ≤ D, a i k = 0 := by
  induction D generalizing a with
  | zero =>
    intro i hi k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst hk0
    exact tendsto_zero_of_sum_pow_smul s z hz hinj (fun i => a i 0)
      (by simpa using h) i hi
  | succ D ih =>
    set b : ι → W := fun i => a i (D + 1) with hb
    set R : ℕ → W := fun n => ∑ i ∈ s, (z i) ^ n •
        (∑ k ∈ Finset.range (D + 1), (n : ℂ) ^ k • a i k) with hR
    set q : ℕ → ℂ := fun n => ((n : ℂ) ^ (D + 1))⁻¹ with hq
    have hq_zero : Tendsto q atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) ^ (D + 1)) atTop (𝓝 0) := by
        have := (tendsto_inv_atTop_zero.comp
          (tendsto_natCast_atTop_atTop (R := ℝ))).pow (D + 1)
        rwa [zero_pow (Nat.succ_ne_zero D)] at this
      refine h1.congr' ?_
      filter_upwards with n
      rw [hq, norm_inv, norm_pow, Complex.norm_natCast, inv_pow]
    have hf_eq : ∀ n : ℕ, (∑ i ∈ s, (z i) ^ n •
          (∑ k ∈ Finset.range (D + 1 + 1), (n : ℂ) ^ k • a i k)) =
        (n : ℂ) ^ (D + 1) • (∑ i ∈ s, (z i) ^ n • b i) + R n := by
      intro n
      rw [hR, hb, Finset.smul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_range_succ, smul_add, smul_smul, smul_smul, mul_comm]
      abel
    have hqf : Tendsto (fun n : ℕ => q n •
        (∑ i ∈ s, (z i) ^ n •
          (∑ k ∈ Finset.range (D + 1 + 1), (n : ℂ) ^ k • a i k))) atTop (𝓝 0) := by
      simpa using hq_zero.smul h
    have hqR : Tendsto (fun n : ℕ => q n • R n) atTop (𝓝 0) := by
      have := tendsto_inv_pow_smul_sum_range s z hz D a
      simpa [hR, hq] using this
    have hL : Tendsto (fun n : ℕ => ∑ i ∈ s, (z i) ^ n • b i) atTop (𝓝 0) := by
      have hsub : Tendsto (fun n : ℕ => q n •
          (∑ i ∈ s, (z i) ^ n •
            (∑ k ∈ Finset.range (D + 1 + 1), (n : ℂ) ^ k • a i k)) - q n • R n)
          atTop (𝓝 0) := by
        simpa using hqf.sub hqR
      refine hsub.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℂ) ≠ 0 := by
        have : (n : ℕ) ≠ 0 := by omega
        exact_mod_cast this
      have hcancel : q n * (n : ℂ) ^ (D + 1) = 1 := by
        rw [hq, inv_mul_cancel₀ (pow_ne_zero _ hn0)]
      rw [hf_eq n, smul_add, smul_smul, hcancel, one_smul]
      abel
    have hbzero : ∀ i ∈ s, b i = 0 :=
      tendsto_zero_of_sum_pow_smul s z hz hinj b hL
    have hRconv : Tendsto R atTop (𝓝 0) := by
      refine h.congr' ?_
      filter_upwards with n
      rw [hf_eq n]
      have : (∑ i ∈ s, (z i) ^ n • b i) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hbzero i hi, smul_zero]
      rw [this, smul_zero, zero_add]
    intro i hi k hk
    rcases Nat.lt_or_eq_of_le hk with hklt | hkeq
    · exact ih a hRconv i hi k (Nat.lt_succ_iff.mp hklt)
    · subst hkeq
      exact hbzero i hi

/-- **Polynomial-exponential reduction, purely imaginary modes.** If every mode
`μ i` is purely imaginary (`(μ i).re = 0`) and the modes are distinct, then a
finite sum of vector-valued polynomial terms times `exp (t * μ i)` that tends to
zero at `+∞` has all coefficients zero. The proof samples `t = n * δ` for a
scaling `δ` chosen so that the unit-modulus characters `exp (δ * μ i)` remain
distinct, reducing to the discrete form
`tendsto_zero_of_sum_pow_smul_polynomial`. -/
lemma tendsto_zero_of_sum_exp_polynomial_re_zero {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] {ι : Type*} (s : Finset ι) (μ : ι → ℂ)
    (hre : ∀ i ∈ s, (μ i).re = 0)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, μ i = μ j → i = j)
    (D : ℕ) (a : ι → ℕ → W)
    (h : Tendsto (fun t : ℝ => ∑ i ∈ s, Complex.exp (t * μ i) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a i k)) atTop (𝓝 0)) :
    ∀ i ∈ s, ∀ k ≤ D, a i k = 0 := by
  classical
  by_cases hs : s = ∅
  · intro i hi; rw [hs] at hi; simp at hi
  set B : ℝ := ∑ i ∈ s, ∑ j ∈ s, ‖μ i - μ j‖ with hB
  have hBnn : 0 ≤ B := by
    rw [hB]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  obtain ⟨M, hM⟩ := exists_nat_gt (B / (2 * Real.pi))
  have hMposR : (0 : ℝ) < M := lt_of_le_of_lt (by positivity) hM
  have hMpos : 0 < M := by exact_mod_cast hMposR
  set δ : ℝ := (M : ℝ)⁻¹ with hδ
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hδB : δ * B < 2 * Real.pi := by
    rw [hδ, inv_mul_eq_div, div_lt_iff₀ (by positivity : (0:ℝ) < (M:ℝ))]
    have h2 : B < (2 * Real.pi) * M := by
      have := (div_lt_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)).mp hM
      linarith
    linarith
  set z : ι → ℂ := fun i => Complex.exp ((δ : ℂ) * μ i) with hz
  set a' : ι → ℕ → W := fun i k => ((δ : ℂ) ^ k) • a i k with ha'
  have hz_norm : ∀ i ∈ s, ‖z i‖ = 1 := by
    intro i hi
    rw [hz, Complex.norm_exp]
    have hre0 : ((δ : ℂ) * μ i).re = 0 := by
      simp [Complex.mul_re, hre i hi]
    rw [hre0, Real.exp_zero]
  have hz_inj : ∀ i ∈ s, ∀ j ∈ s, z i = z j → i = j := by
    intro i hi j hj heq
    by_contra hij
    have hμij : μ i ≠ μ j := fun hh => hij (hinj i hi j hj hh)
    have hne : μ i - μ j ≠ 0 := sub_ne_zero.mpr hμij
    have heq' : Complex.exp ((δ : ℂ) * μ i) = Complex.exp ((δ : ℂ) * μ j) := by
      simpa [hz] using heq
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq'
    have hd : (δ : ℂ) * (μ i - μ j) = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [mul_sub, hn]; ring
    have hnorm := congrArg norm hd
    rw [norm_mul, norm_mul, Complex.norm_intCast] at hnorm
    have hnormδ : ‖(δ : ℂ)‖ = δ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hδpos)]
    have hnormI : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
      rw [show (2 * (Real.pi : ℂ) * Complex.I) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I by
        push_cast; ring]
      rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    rw [hnormδ, hnormI] at hnorm
    have hδnn : 0 ≤ δ := le_of_lt hδpos
    have hpos : 0 < ‖μ i - μ j‖ := norm_pos_iff.mpr hne
    have hle : δ * ‖μ i - μ j‖ ≤ δ * B := by
      apply mul_le_mul_of_nonneg_left _ hδnn
      rw [hB]
      calc ‖μ i - μ j‖ ≤ ∑ j' ∈ s, ‖μ i - μ j'‖ :=
            Finset.single_le_sum (s := s) (f := fun j' => ‖μ i - μ j'‖)
              (fun j' _ => norm_nonneg _) hj
        _ ≤ ∑ i' ∈ s, ∑ j' ∈ s, ‖μ i' - μ j'‖ :=
            Finset.single_le_sum (s := s)
              (f := fun i' => ∑ j' ∈ s, ‖μ i' - μ j'‖)
              (fun i' _ => Finset.sum_nonneg fun j' _ => norm_nonneg _) hi
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have hn0 : n ≠ 0 := by
        intro h0
        rw [h0] at hnorm
        simp only [Int.cast_zero, abs_zero, zero_mul] at hnorm
        nlinarith [hpos, hδpos]
      have h1 : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
      rw [← Int.cast_abs]
      exact_mod_cast h1
    have h2 : 2 * Real.pi ≤ δ * B := by
      calc 2 * Real.pi = 1 * (2 * Real.pi) := by ring
        _ ≤ |(n : ℝ)| * (2 * Real.pi) := mul_le_mul_of_nonneg_right hn1 (by positivity)
        _ = δ * ‖μ i - μ j‖ := hnorm.symm
        _ ≤ δ * B := hle
    exact absurd h2 (not_le.mpr hδB)
  have htend : Tendsto (fun n : ℕ => (n : ℝ) * δ) atTop atTop :=
    Tendsto.atTop_mul_const hδpos (tendsto_natCast_atTop_atTop (R := ℝ))
  have hcomp := h.comp htend
  have hseq : Tendsto (fun n : ℕ => ∑ i ∈ s, (z i) ^ n •
      (∑ k ∈ Finset.range (D + 1), (n : ℂ) ^ k • a' i k)) atTop (𝓝 0) := by
    refine hcomp.congr' ?_
    filter_upwards with n
    apply Finset.sum_congr rfl
    intro i hi
    rw [hz, ha']
    congr 1
    · rw [show ((((n : ℝ) * δ : ℝ) : ℂ)) = (n : ℂ) * (δ : ℂ) by push_cast; ring]
      rw [mul_assoc]
      exact Complex.exp_nat_mul _ _
    · apply Finset.sum_congr rfl
      intro k hk
      rw [show ((((n : ℝ) * δ : ℝ) : ℂ)) = (n : ℂ) * (δ : ℂ) by push_cast; ring]
      rw [mul_pow, smul_smul]
  have hmain := tendsto_zero_of_sum_pow_smul_polynomial s z hz_norm hz_inj D a' hseq
  intro i hi k hk
  have hzero := hmain i hi k hk
  rw [ha'] at hzero
  have hδk : ((δ : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (ne_of_gt hδpos))
  exact (smul_eq_zero.mp hzero).resolve_left hδk

/-- **The strictly-decaying part.** If every real part is negative, then a finite
sum of vector-valued polynomial terms times `exp (t * μ i)` tends to zero at
`+∞`: the exponential decay beats the polynomial growth term by term. This is
the part of the reduction discarded after the dominant real part is factored
out. -/
lemma tendsto_zero_of_sum_exp_polynomial_of_re_neg {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] {ι : Type*} (s : Finset ι) (μ : ι → ℂ)
    (hre : ∀ i ∈ s, (μ i).re < 0) (D : ℕ) (a : ι → ℕ → W) :
    Tendsto (fun t : ℝ => ∑ i ∈ s, Complex.exp (t * μ i) •
      (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a i k)) atTop (𝓝 0) := by
  have hterm : ∀ i ∈ s, Tendsto (fun t : ℝ => Complex.exp (t * μ i) •
      (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a i k)) atTop (𝓝 0) := by
    intro i hi
    have hinner : ∀ k ∈ Finset.range (D + 1),
        Tendsto (fun t : ℝ => Complex.exp (t * μ i) • ((t : ℂ) ^ k • a i k))
          atTop (𝓝 0) := by
      intro k hk
      have hk' := (tendsto_exp_mul_pow (μ i) (hre i hi) k).smul_const (a i k)
      simpa [smul_smul] using hk'
    simpa [Finset.smul_sum] using tendsto_finsetSum (Finset.range (D + 1)) hinner
  simpa using tendsto_finsetSum s hterm

/-- **Polynomial-exponential reduction.** A finite sum of vector-valued
polynomial terms times characters `exp (t * μ i)` with `0 ≤ (μ i).re` that tends
to zero at `+∞` must have all coefficients zero. The proof factors out the
dominant real part `R` (bounded multiplier `exp (-t R)`), discards the strictly
smaller real parts by `tendsto_zero_of_sum_exp_polynomial_of_re_neg`, applies
the purely imaginary reduction `tendsto_zero_of_sum_exp_polynomial_re_zero` to
the top group, and then inducts on the number of modes. -/
theorem tendsto_zero_of_sum_exp_polynomial {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℂ W] {ι : Type*} (s : Finset ι) (μ : ι → ℂ)
    (hμ : ∀ i ∈ s, 0 ≤ (μ i).re)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, μ i = μ j → i = j)
    (D : ℕ) (a : ι → ℕ → W)
    (h : Tendsto (fun t : ℝ => ∑ i ∈ s, Complex.exp (t * μ i) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a i k)) atTop (𝓝 0)) :
    ∀ i ∈ s, ∀ k ≤ D, a i k = 0 := by
  classical
  suffices hgen : ∀ n, ∀ (s : Finset ι), s.card = n → ∀ (μ : ι → ℂ) (D : ℕ) (a : ι → ℕ → W),
      (∀ i ∈ s, 0 ≤ (μ i).re) → (∀ i ∈ s, ∀ j ∈ s, μ i = μ j → i = j) →
      (Tendsto (fun t : ℝ => ∑ i ∈ s, Complex.exp (t * μ i) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a i k)) atTop (𝓝 0)) →
      ∀ i ∈ s, ∀ k ≤ D, a i k = 0 by
    exact hgen s.card s rfl μ D a hμ hinj h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s hcard μ D a hμ hinj h
    by_cases hs : s = ∅
    · intro i hi; rw [hs] at hi; simp at hi
    have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
    set R : ℝ := s.sup' hsne (fun i => (μ i).re) with hR
    obtain ⟨i0, hi0, hi0R⟩ := Finset.exists_mem_eq_sup' hsne (fun i => (μ i).re)
    have hReq : R = (μ i0).re := hR.trans hi0R
    have hRnn : 0 ≤ R := hReq.symm ▸ hμ i0 hi0
    have hleR : ∀ i ∈ s, (μ i).re ≤ R := by
      intro i hi
      rw [hR]
      have := Finset.le_sup' (fun i => (μ i).re) hi
      rwa [show s.sup' ⟨i, hi⟩ (fun i => (μ i).re) = s.sup' hsne (fun i => (μ i).re) from
        congrArg (fun H => s.sup' H (fun i => (μ i).re)) (Subsingleton.elim _ _)] at this
    set s0 : Finset ι := s.filter (fun i => (μ i).re = R) with hs0
    set s' : Finset ι := s.filter (fun i => (μ i).re ≠ R) with hs'
    have hs0ne : s0.Nonempty := ⟨i0, Finset.mem_filter.mpr ⟨hi0, hReq.symm⟩⟩
    have hsub : s' ⊆ s := Finset.filter_subset _ _
    have hne : s' ≠ s := by
      intro heq
      have : i0 ∈ s' := heq ▸ hi0
      rw [hs', Finset.mem_filter] at this
      exact this.2 hReq.symm
    have hcardlt : s'.card < s.card :=
      Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)
    set f : ℝ → W := fun t => ∑ i ∈ s, Complex.exp (t * μ i) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a i k) with hf
    set g : ℝ → W := fun t => ∑ i ∈ s, Complex.exp ((t : ℂ) * (μ i - (R : ℂ))) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a i k) with hg
    set g0 : ℝ → W := fun t => ∑ i ∈ s0, Complex.exp ((t : ℂ) * (μ i - (R : ℂ))) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a i k) with hg0
    set g1 : ℝ → W := fun t => ∑ i ∈ s', Complex.exp ((t : ℂ) * (μ i - (R : ℂ))) •
        (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a i k) with hg1
    have hg_eq : ∀ t, g t = Complex.exp (-((t : ℂ) * (R : ℂ))) • f t := by
      intro t
      simp only [hg, hf]
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [smul_smul]
      congr 1
      rw [← Complex.exp_add]
      congr 1
      ring
    have hg_split : ∀ t, g t = g0 t + g1 t := by
      intro t
      simp only [hg, hg0, hg1, hs0, hs']
      rw [← Finset.sum_filter_add_sum_filter_not s (fun i => (μ i).re = R)
        (fun i => Complex.exp ((t : ℂ) * (μ i - (R : ℂ))) •
          (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a i k))]
    have hg_tend : Tendsto g atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hf_norm : Tendsto (fun t : ℝ => ‖f t‖) atTop (𝓝 0) := by
        rw [hf]; simpa using h.norm
      refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hf_norm
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      rw [hg_eq t, norm_smul]
      have hc : ‖Complex.exp (-((t : ℂ) * (R : ℂ)))‖ ≤ 1 := by
        rw [Complex.norm_exp]
        rw [show (-((t : ℂ) * (R : ℂ))).re = -(t * R) by
          simp [Complex.mul_re]]
        rw [Real.exp_le_one_iff]
        nlinarith
      calc ‖Complex.exp (-((t : ℂ) * (R : ℂ)))‖ * ‖f t‖ ≤ 1 * ‖f t‖ :=
            mul_le_mul_of_nonneg_right hc (norm_nonneg _)
        _ = ‖f t‖ := one_mul _
    have hg1_tend : Tendsto g1 atTop (𝓝 0) := by
      rw [hg1]
      exact tendsto_zero_of_sum_exp_polynomial_of_re_neg s' (fun i => μ i - (R : ℂ))
        (fun i hi => by
          rw [hs', Finset.mem_filter] at hi
          have hlt : (μ i).re < R := lt_of_le_of_ne (hleR i hi.1) hi.2
          rw [Complex.sub_re, Complex.ofReal_re]
          linarith) D a
    have hg0_tend : Tendsto g0 atTop (𝓝 0) := by
      have hsub2 : Tendsto (fun t => g t - g1 t) atTop (𝓝 0) := by
        simpa using hg_tend.sub hg1_tend
      refine hsub2.congr' ?_
      filter_upwards with t
      simp [hg_split t]
    have h0zero : ∀ i ∈ s0, ∀ k ≤ D, a i k = 0 := by
      refine tendsto_zero_of_sum_exp_polynomial_re_zero s0 (fun i => μ i - (R : ℂ))
        ?_ ?_ D a ?_
      · intro i hi
        rw [hs0, Finset.mem_filter] at hi
        rw [Complex.sub_re, Complex.ofReal_re, hi.2, sub_self]
      · intro i hi j hj hij
        rw [hs0, Finset.mem_filter] at hi hj
        exact hinj i hi.1 j hj.1 (by
          have h := congrArg (fun z : ℂ => z + (R : ℂ)) hij
          simpa [sub_add_cancel] using h)
      · exact hg0_tend
    intro i hi k hk
    by_cases hiR : (μ i).re = R
    · exact h0zero i (Finset.mem_filter.mpr ⟨hi, hiR⟩) k hk
    · have hmem : i ∈ s' := Finset.mem_filter.mpr ⟨hi, hiR⟩
      have hf_eq_g1 : Tendsto (fun t : ℝ => ∑ j ∈ s', Complex.exp (t * μ j) •
          (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a j k)) atTop (𝓝 0) := by
        refine (show Tendsto f atTop (𝓝 0) from hf ▸ h).congr' ?_
        filter_upwards with t
        show f t = ∑ j ∈ s', Complex.exp (t * μ j) •
            (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a j k)
        have hsplit : f t = (∑ j ∈ s0, Complex.exp (t * μ j) •
              (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a j k)) +
              (∑ j ∈ s', Complex.exp (t * μ j) •
              (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a j k)) := by
          simp only [hf, hs0, hs']
          rw [← Finset.sum_filter_add_sum_filter_not s (fun i => (μ i).re = R)
            (fun i => Complex.exp (t * μ i) •
              (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a i k))]
        have hzero : (∑ j ∈ s0, Complex.exp (t * μ j) •
            (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a j k)) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          have hjzero : ∀ k ≤ D, a j k = 0 := h0zero j hj
          have hinner : (∑ k ∈ Finset.range (D + 1), (t : ℂ) ^ k • a j k) = 0 := by
            apply Finset.sum_eq_zero
            intro k hk'
            rw [hjzero k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk')), smul_zero]
          rw [hinner, smul_zero]
        rw [hsplit, hzero, zero_add]
      have hres := ih s'.card (by rw [← hcard]; exact hcardlt) s' rfl μ D a
        (fun i hi => hμ i (hsub hi))
        (fun i hi j hj hij => hinj i (hsub hi) j (hsub hj) hij) hf_eq_g1
      exact hres i hmem k hk

/-! ## Readout extraction on the antistable subspace

The polynomial-exponential reduction `tendsto_zero_of_sum_exp_polynomial` is now
applied to the linear-trajectory readout of a state in the antistable subspace.
The extraction theorem is the analytic core of the `hspectral` obligation: a
scalar readout that decays along the antistable orbit must annihilate every
`f`-power of the state, hence the state is unobservable. -/

section AntistableReadoutExtraction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

/-- **Exponential decomposition at a generalized eigenvector.** If `(f - μ)^k`
kills `x`, then `exp (t f) x = e^{t μ} Σ_{j<k} (t^j / j!) (f - μ)^j x`. This is
the `hdecomp` computation of `tendsto_exp_apply_of_nilpotent`, extracted as a
reusable identity. -/
lemma exp_apply_eq_exp_mul_sum (f : E →ₗ[ℂ] E) (μ : ℂ) {x : E} {k : ℕ}
    (hk : ((f - μ • (1 : E →ₗ[ℂ] E)) ^ k) x = 0) (t : ℝ) :
    NormedSpace.exp (t • f.toContinuousLinearMap) x =
      Complex.exp (t * μ) •
        (∑ j ∈ Finset.range k, ((j.factorial : ℂ)⁻¹) •
          ((t : ℂ) ^ j • (((f - μ • (1 : E →ₗ[ℂ] E)) ^ j) x))) := by
  set N : E →L[ℂ] E := f.toContinuousLinearMap - μ • (1 : E →L[ℂ] E) with hN
  have hcoe : (N : E →ₗ[ℂ] E) = f - μ • (1 : E →ₗ[ℂ] E) := by
    ext y; simp [hN]
  have hNalg : ∀ j : ℕ, (N ^ j) x = (((f - μ • (1 : E →ₗ[ℂ] E)) ^ j) x) := by
    intro j
    change ((N ^ j : E →L[ℂ] E) : E →ₗ[ℂ] E) x = _
    rw [ContinuousLinearMap.toLinearMap_pow, hcoe]
  have hNx : (N ^ k) x = 0 := by
    rw [hNalg k]; exact hk
  have hexpscalar : ∀ t : ℝ, NormedSpace.exp ((t * μ) • (1 : E →L[ℂ] E)) =
      Complex.exp (t * μ) • (1 : E →L[ℂ] E) := by
    intro t
    rw [← Algebra.algebraMap_eq_smul_one (t * μ), ← NormedSpace.algebraMap_exp_comm (t * μ),
      show NormedSpace.exp (t * μ) = Complex.exp (t * μ) from
        (congrFun Complex.exp_eq_exp_ℂ (t * μ)).symm,
      Algebra.algebraMap_eq_smul_one]
  have hsplit : t • f.toContinuousLinearMap =
      (t * μ) • (1 : E →L[ℂ] E) + t • N := by
    rw [hN]; module
  rw [hsplit, NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := ℂ)]
  · rw [mul_apply_eq_comp, hexpscalar t, exp_nilpotent_apply_eq_sum N hNx t]
    rw [_root_.smul_apply, one_apply_eq_self]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [smul_pow, _root_.smul_apply, hNalg j, RCLike.real_smul_eq_coe_smul (K := ℂ) (t ^ j)]
    norm_num
  · rw [← Algebra.algebraMap_eq_smul_one (t * μ)]
    exact Algebra.commute_algebraMap_left (t * μ) (t • N)
  · exact (NormedSpace.expSeries_radius_eq_top ℂ (E →L[ℂ] E)).symm ▸ edist_lt_top _ _
  · exact (NormedSpace.expSeries_radius_eq_top ℂ (E →L[ℂ] E)).symm ▸ edist_lt_top _ _

omit [FiniteDimensional ℂ E] in
/-- **Killing the nilpotent powers kills the whole orbit.** If a linear
functional `L` annihilates every power `(f - μ)^j x`, then it annihilates
`f^k x` for every `k`: the cyclic subspace generated by `x` under `f` is spanned
by the nilpotent powers and is `f`-invariant. -/
lemma apply_pow_eq_zero_of_kills_nilpotent (f : E →ₗ[ℂ] E) (L : E →ₗ[ℂ] ℂ)
    {μ : ℂ} {x : E} (hL : ∀ j : ℕ, L (((f - μ • (1 : E →ₗ[ℂ] E)) ^ j) x) = 0) :
    ∀ k : ℕ, L ((f ^ k) x) = 0 := by
  set N : E →ₗ[ℂ] E := f - μ • (1 : E →ₗ[ℂ] E) with hN
  set S : Submodule ℂ E := Submodule.span ℂ (Set.range (fun j : ℕ => (N ^ j) x)) with hS
  have hzS : x ∈ S := Submodule.subset_span ⟨0, by simp⟩
  have hSL : S ≤ LinearMap.ker L := by
    rw [hS, Submodule.span_le]
    rintro y ⟨j, rfl⟩
    exact LinearMap.mem_ker.mpr (hL j)
  have hfS : Submodule.map f S ≤ S := by
    rw [Submodule.map_le_iff_le_comap, hS, Submodule.span_le]
    rintro y ⟨j, rfl⟩
    change f ((N ^ j) x) ∈ S
    have hy : f ((N ^ j) x) = μ • ((N ^ j) x) + (N ^ (j + 1)) x := by
      have hfN : f = μ • (1 : E →ₗ[ℂ] E) + N := by rw [hN]; abel
      rw [hfN, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, pow_succ']
      rfl
    rw [hy]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
      (Submodule.subset_span ⟨j + 1, rfl⟩)
  have hpowS : ∀ k : ℕ, (f ^ k) x ∈ S := by
    intro k
    induction k with
    | zero => simpa using hzS
    | succ k ih =>
      have := hfS ⟨(f ^ k) x, ih, rfl⟩
      simpa [pow_succ'] using this
  intro k
  exact LinearMap.mem_ker.mp (hSL (hpowS k))

/-- **Complex antistable readout extraction.** If `z` lies in the sum of the
generalized eigenspaces of `f` at eigenvalues with nonnegative real part, and the
scalar readout `t ↦ L (exp (t • f) z)` tends to zero at `+∞`, then `L`
annihilates every `f`-power of `z`.

The proof writes `z` as a finite sum of generalized eigenvectors, expands each
orbit as `exp (t μ)` times a vector polynomial, applies the polynomial-exponential
reduction `tendsto_zero_of_sum_exp_polynomial` to the readout, and finishes with
`apply_pow_eq_zero_of_kills_nilpotent`. This is the analytic core of the
`hspectral` obligation. -/
theorem tendsto_zero_readout_forces_apply_pow_eq_zero (f : E →ₗ[ℂ] E)
    (L : E →ₗ[ℂ] ℂ) {z : E}
    (hz : z ∈ ⨆ μ : {μ : ℂ // ¬ μ.re < 0}, Module.End.maxGenEigenspace f μ.1)
    (h : Tendsto (fun t : ℝ => L (NormedSpace.exp (t • f.toContinuousLinearMap) z))
      atTop (𝓝 0)) :
    ∀ k, L ((f ^ k) z) = 0 := by
  classical
  obtain ⟨s, hs⟩ := (Submodule.mem_iSup_iff_exists_finset
    (p := fun μ : {μ : ℂ // ¬ μ.re < 0} => Module.End.maxGenEigenspace f μ.1)).mp hz
  obtain ⟨zμ, hzμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum
    (fun μ : {μ : ℂ // ¬ μ.re < 0} => Module.End.maxGenEigenspace f μ.1) z).mp hs
  have hz_eq : z = ∑ μ ∈ s, (zμ μ : E) := hzμ.symm
  have hkf_exists : ∀ μ : {μ : ℂ // ¬ μ.re < 0},
      ∃ k, ((f - μ.1 • (1 : E →ₗ[ℂ] E)) ^ k) (zμ μ) = 0 :=
    fun μ => (Module.End.mem_maxGenEigenspace f μ.1 (zμ μ)).mp (zμ μ).2
  choose kf hkf using hkf_exists
  let K : ℕ := s.sup kf
  have hKle : ∀ μ ∈ s, kf μ ≤ K := fun μ hμ => Finset.le_sup hμ
  let a : {μ : ℂ // ¬ μ.re < 0} → ℕ → ℂ := fun μ j =>
    L (((j.factorial : ℂ)⁻¹) • (((f - μ.1 • (1 : E →ₗ[ℂ] E)) ^ j) (zμ μ)))
  have hExp : Tendsto (fun t : ℝ => ∑ μ ∈ s, Complex.exp (t * μ.1) •
      (∑ k ∈ Finset.range (K + 1), (t : ℂ) ^ k • a μ k)) atTop (𝓝 0) := by
    refine h.congr' (Filter.Eventually.of_forall fun t => ?_)
    rw [hz_eq, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro μ hμ
    rw [exp_apply_eq_exp_mul_sum f μ.1 (hkf μ) t, map_smul, map_sum]
    congr 1
    have hstep : (∑ j ∈ Finset.range (kf μ), L (((j.factorial : ℂ)⁻¹) •
        ((t : ℂ) ^ j • (((f - μ.1 • (1 : E →ₗ[ℂ] E)) ^ j) (zμ μ))))) =
        ∑ j ∈ Finset.range (kf μ), (t : ℂ) ^ j • a μ j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_smul, map_smul]
      simp only [a]
      rw [map_smul, smul_smul, smul_smul, mul_comm]
    rw [hstep]
    rw [Finset.sum_subset (s₁ := Finset.range (kf μ)) (s₂ := Finset.range (K + 1))
      (Finset.range_subset_range.mpr (by have := hKle μ hμ; omega))
      (fun j hj hjnot => by
        rw [Finset.mem_range, not_lt] at hjnot
        simp only [a]
        have hNj0 : (((f - μ.1 • (1 : E →ₗ[ℂ] E)) ^ j) (zμ μ)) = 0 := by
          obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hjnot
          rw [hd, show kf μ + d = d + kf μ by omega, pow_add, Module.End.mul_apply, hkf μ,
            map_zero]
        rw [hNj0, smul_zero, map_zero, smul_zero])]
  have hres := tendsto_zero_of_sum_exp_polynomial s (fun μ : {μ : ℂ // ¬ μ.re < 0} => μ.1)
    (fun μ _ => le_of_not_gt μ.2)
    (fun μ _ ν _ hμν => Subtype.ext hμν) K a hExp
  intro k
  rw [hz_eq, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro μ hμ
  have hL : ∀ j : ℕ, L (((f - μ.1 • (1 : E →ₗ[ℂ] E)) ^ j) (zμ μ)) = 0 := by
    intro j
    by_cases hj : j ≤ K
    · have ha0 := hres μ hμ j hj
      have : (j.factorial : ℂ)⁻¹ • L (((f - μ.1 • (1 : E →ₗ[ℂ] E)) ^ j) (zμ μ)) = 0 := by
        rw [← map_smul]; exact ha0
      exact (smul_eq_zero.mp this).resolve_left
        (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)))
    · have hNj : (((f - μ.1 • (1 : E →ₗ[ℂ] E)) ^ j) (zμ μ)) = 0 := by
        obtain ⟨d, hd⟩ : ∃ d, j = kf μ + d :=
          Nat.exists_eq_add_of_le (le_trans (hKle μ hμ) (le_of_lt (lt_of_not_ge hj)))
        rw [hd, show kf μ + d = d + kf μ by omega, pow_add, Module.End.mul_apply, hkf μ,
          map_zero]
      rw [hNj, map_zero]
  exact apply_pow_eq_zero_of_kills_nilpotent f L (μ := μ.1) hL k

end AntistableReadoutExtraction

/-! ## The real antistable readout theorem

Transporting the complex extraction through the canonical real basis and the
coordinatewise inclusion `ofRealPi` discharges the `hspectral` obligation: an
antistable real state whose real readout decays is unobservable. -/

section RealAntistableReadout

variable {X Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- **Antistable readout forces unobservability (real version).** If `x` lies in
the antistable subspace `X_b(A)` and the real readout `t ↦ H (exp (t A) x)`
tends to zero at `+∞`, then `x` is unobservable: `H (A^k x) = 0` for every `k`.
This is the `hspectral` obligation. -/
theorem antistable_readout_forces_unobservable
    (A : X →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) {x : X}
    (hx : x ∈ unstableSubspace A)
    (hdec : Tendsto (fun t : ℝ => H (NormedSpace.exp (t • A.toContinuousLinearMap) x))
      atTop (𝓝 0)) :
    x ∈ unobservableSubspace H A := by
  classical
  rw [mem_unobservableSubspace]
  intro k
  refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ) fun ρ => ?_
  let n : ℕ := Module.finrank ℝ X
  let b : Basis (Fin n) ℝ X := Module.finBasis ℝ X
  let L : X ≃L[ℝ] (Fin n → ℝ) := b.equivFun.toContinuousLinearEquiv
  let M : Matrix (Fin n) (Fin n) ℝ := LinearMap.toMatrix b b A
  let g : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) := (Matrix.toLin' M).toContinuousLinearMap
  let f : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) := Matrix.toLin' (M.map (algebraMap ℝ ℂ))
  let z : Fin n → ℂ := ofRealPi (L x)
  have hz : z ∈ unstableComplexSubspace A := by
    have hh := (mem_unstableSubspace (A := A)).mp hx
    simpa [z, L, b, n] using hh
  have hg : g = L.conjContinuousAlgEquiv A.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro y
    have hrepr : M *ᵥ b.repr (L.symm y) = b.repr (A (L.symm y)) :=
      LinearMap.toMatrix_mulVec_repr b b A (L.symm y)
    have hLy : b.repr (L.symm y) = y := by
      rw [← Basis.equivFun_apply b (L.symm y)]
      exact b.equivFun.apply_symm_apply y
    rw [hLy] at hrepr
    change M *ᵥ y = L (A.toContinuousLinearMap (L.symm y))
    rw [hrepr]
    rw [← Basis.equivFun_apply b (A (L.symm y))]
    rfl
  have hLexp : ∀ t : ℝ, L (NormedSpace.exp (t • A.toContinuousLinearMap) x)
      = NormedSpace.exp (t • g) (L x) := by
    intro t
    have key := NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) (L.conjContinuousAlgEquiv)
      (L.conjContinuousAlgEquiv).continuous (t • A.toContinuousLinearMap)
      ((NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _)
    have hcongr : (L.conjContinuousAlgEquiv) (t • A.toContinuousLinearMap) = t • g := by
      rw [map_smul, hg.symm]
    have := congrArg (fun f : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => f (L x)) key
    rw [hcongr] at this
    simpa [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply, g] using this
  have hflow : ∀ t : ℝ,
      ofRealPi (L (NormedSpace.exp (t • A.toContinuousLinearMap) x)) =
        NormedSpace.exp (t • f.toContinuousLinearMap) z := by
    intro t
    rw [hLexp t, ofRealPi_exp M t (L x)]
  let Hc : (Fin n → ℝ) →ₗ[ℝ] Z := H.comp L.symm.toLinearMap
  let hρ : (Fin n → ℝ) →ₗ[ℝ] ℝ := ρ.toLinearMap.comp Hc
  let Φ : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun w => (hρ (fun i => (w i).re) : ℂ) +
        Complex.I * (hρ (fun i => (w i).im) : ℂ)
      map_add' := by
        intro u v
        have h1 : (fun i => (u i + v i).re) =
            (fun i => (u i).re) + (fun i => (v i).re) := by funext i; simp
        have h2 : (fun i => (u i + v i).im) =
            (fun i => (u i).im) + (fun i => (v i).im) := by funext i; simp
        simp only [Pi.add_apply]
        rw [h1, h2, map_add, map_add]
        push_cast
        ring
      map_smul' := by
        intro c w
        have h1 : (fun i => (c * w i).re) =
            c.re • (fun i => (w i).re) - c.im • (fun i => (w i).im) := by
          funext i; simp [Complex.mul_re]
        have h2 : (fun i => (c * w i).im) =
            c.re • (fun i => (w i).im) + c.im • (fun i => (w i).re) := by
          funext i; simp [Complex.mul_im]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [h1, h2, map_sub, map_add, map_smul, map_smul, map_smul, map_smul]
        push_cast
        apply Complex.ext <;> simp }
  have hΦ_ofRealPi : ∀ y : Fin n → ℝ, Φ (ofRealPi y) = (hρ y : ℂ) := by
    intro y
    change (hρ (fun i => (ofRealPi y i).re) : ℂ) +
        Complex.I * (hρ (fun i => (ofRealPi y i).im) : ℂ) = (hρ y : ℂ)
    have h1 : (fun i => (ofRealPi y i).re) = y := by funext i; simp
    have h2 : (fun i => (ofRealPi y i).im) = 0 := by funext i; simp
    rw [h1, h2, map_zero]
    simp
  have hΦz : Tendsto (fun t : ℝ => Φ (NormedSpace.exp (t • f.toContinuousLinearMap) z))
      atTop (𝓝 0) := by
    have hρdec : Tendsto (fun t : ℝ =>
        (hρ (L (NormedSpace.exp (t • A.toContinuousLinearMap) x)) : ℂ)) atTop (𝓝 0) := by
      have hcont := (ρ.continuous.tendsto 0).comp hdec
      rw [map_zero] at hcont
      have hcontC : Tendsto (fun t : ℝ =>
          ((ρ (H (NormedSpace.exp (t • A.toContinuousLinearMap) x)) : ℝ) : ℂ))
          atTop (𝓝 0) := by
        have h := (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hcont
        simpa [Function.comp_def] using h
      have hfun : (fun t : ℝ =>
          (hρ (L (NormedSpace.exp (t • A.toContinuousLinearMap) x)) : ℂ)) =
          fun t : ℝ =>
            ((ρ (H (NormedSpace.exp (t • A.toContinuousLinearMap) x)) : ℝ) : ℂ) :=
        funext fun t => by simp [hρ, Hc, L]
      rw [hfun]
      exact hcontC
    refine hρdec.congr' (Filter.Eventually.of_forall fun t => ?_)
    rw [← hΦ_ofRealPi (L (NormedSpace.exp (t • A.toContinuousLinearMap) x)), hflow t]
  have hpow : ∀ m : ℕ, Φ ((f ^ m) z) = 0 :=
    tendsto_zero_readout_forces_apply_pow_eq_zero f Φ hz hΦz
  have hf_ofRealPi : ∀ y : Fin n → ℝ, f (ofRealPi y) = ofRealPi (g y) := by
    intro y
    change (M.map (algebraMap ℝ ℂ)) *ᵥ (ofRealPi y) = ofRealPi (M *ᵥ y)
    exact (ofRealPi_mulVec M y).symm
  have hgL : ∀ y : X, g (L y) = L (A y) := by
    intro y
    rw [hg]
    simp [ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply]
  have hfz : ∀ m : ℕ, (f ^ m) z = ofRealPi (L ((A ^ m) x)) := by
    intro m
    induction m with
    | zero => simp [z]
    | succ m ih =>
      rw [pow_succ', Module.End.mul_apply, ih, hf_ofRealPi, hgL]
      congr 1
      rw [pow_succ', Module.End.mul_apply]
  have hfinal : ρ (H ((A ^ k) x)) = 0 := by
    have hk := hpow k
    rw [hfz k, hΦ_ofRealPi] at hk
    have hk' : hρ (L ((A ^ k) x)) = 0 := by exact_mod_cast hk
    simpa [hρ, Hc, L] using hk'
  exact hfinal

/-- **Decay of an autonomous orbit characterizes the Hurwitz subspace.** If
`t ↦ exp (t A) x` tends to zero, then the unstable component in the
Hurwitz/unstable spectral decomposition must vanish. This is the identity-readout
case of `antistable_readout_forces_unobservable`. -/
theorem orbit_decay_mem_hurwitz (A : X →ₗ[ℝ] X) {x : X}
    (hdec : Tendsto (fun t : ℝ => NormedSpace.exp (t • A.toContinuousLinearMap) x)
      atTop (𝓝 0)) :
    x ∈ hurwitzSubspace A := by
  have hxmem : x ∈ hurwitzSubspace A ⊔ unstableSubspace A := by
    rw [hurwitzSubspace_sup_unstableSubspace_eq_top]
    trivial
  obtain ⟨xg, hxg, xb, hxb, hxeq⟩ := Submodule.mem_sup.mp hxmem
  have hgdec := tendsto_exp_restrict_hurwitzSubspace A hxg
  have hbdec : Tendsto (fun t : ℝ => NormedSpace.exp (t • A.toContinuousLinearMap) xb)
      atTop (𝓝 0) := by
    have hsplit : (fun t : ℝ => NormedSpace.exp (t • A.toContinuousLinearMap) x) =
        fun t => NormedSpace.exp (t • A.toContinuousLinearMap) xg +
          NormedSpace.exp (t • A.toContinuousLinearMap) xb := by
      funext t
      rw [← hxeq, map_add]
    have h' := hdec
    rw [hsplit] at h'
    simpa using h'.sub hgdec
  have hunobs : xb ∈ unobservableSubspace (LinearMap.id : X →ₗ[ℝ] X) A :=
    antistable_readout_forces_unobservable A (LinearMap.id : X →ₗ[ℝ] X) hxb hbdec
  have hxbot := unobservableSubspace_le_ker (LinearMap.id : X →ₗ[ℝ] X) A hunobs
  have hxb0 : xb = 0 := by simpa using (mem_ker.mp hxbot)
  rw [← hxeq, hxb0, add_zero]
  exact hxg

end RealAntistableReadout

end LinearMap
