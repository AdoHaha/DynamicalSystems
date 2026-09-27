/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.ArbitraryControllerCriterion
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Charpoly.BaseChange

/-! # Rational pole stability of finite-dimensional scalar channels

The adjugate formula defines a scalar rational transfer channel. The reduced
rational-function denominator records algebraic pole cancellation, and its roots
are contained in the spectrum of the state matrix. The bridge to matrix
resolvent values is explicit at nonsingular points. A converse pole theorem
for minimal realizations is not asserted here.
-/

@[expose] public section


open Polynomial

noncomputable section

namespace RatFunc

/-- Evaluation of a reduced rational function agrees with its displayed
polynomial fraction away from the original denominator's zero set. -/
theorem eval_mk_of_eval_ne_zero (p q : Polynomial ℂ) (z : ℂ)
    (hqz : q.eval z ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) z (RatFunc.mk p q) = p.eval z / q.eval z := by
  have hq : q ≠ 0 := by
    intro h
    subst q
    simp at hqz
  rw [RatFunc.mk_eq_div, RatFunc.eval, RatFunc.num_div, RatFunc.denom_div _ hq]
  let g := gcd p q
  have hg0 : g ≠ 0 := by
    intro hg
    apply hq
    have hdiv := gcd_dvd_right p q
    change g ∣ q at hdiv
    rw [hg] at hdiv
    simpa using hdiv
  have hg : g.eval z ≠ 0 := by
    intro hz
    have hmul : g * (q / g) = q := by
      exact EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_right p q)
    apply hqz
    rw [← hmul, Polynomial.eval_mul, hz, zero_mul]
  have hqdiv : (q / g).eval z ≠ 0 := by
    intro hz
    have hmul : g * (q / g) = q := by
      exact EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_right p q)
    apply hqz
    rw [← hmul, Polynomial.eval_mul, hz, mul_zero]
  have hmulP : g * (p / g) = p := by
    exact EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_left p q)
  have hmulQ : g * (q / g) = q := by
    exact EuclideanDomain.mul_div_cancel' hg0 (gcd_dvd_right p q)
  simp only [Polynomial.eval₂_id, Polynomial.eval_mul, Polynomial.eval_C]
  have evalP : p.eval z = g.eval z * (p / g).eval z := by
    have he := congrArg (fun t : Polynomial ℂ => t.eval z) hmulP
    simpa only [Polynomial.eval_mul] using he.symm
  have evalQ : q.eval z = g.eval z * (q / g).eval z := by
    have he := congrArg (fun t : Polynomial ℂ => t.eval z) hmulQ
    simpa only [Polynomial.eval_mul] using he.symm
  rw [evalP, evalQ]
  simp only [g]
  have hqdiv0 : q / gcd p q ≠ 0 := by
    intro h
    rw [h] at hqdiv
    simp at hqdiv
  have hlc : (q / gcd p q).leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hqdiv0
  field_simp [hqdiv, hg, hlc]
  have hg' : Polynomial.eval z (gcd p q) ≠ 0 := by simpa [g] using hg
  calc
    _ = (Polynomial.eval z (p / gcd p q) * (Polynomial.eval z (q / gcd p q))⁻¹) *
          (Polynomial.eval z (gcd p q) * (Polynomial.eval z (gcd p q))⁻¹) := by
      simp [div_eq_mul_inv, mul_inv_cancel₀ hg']
    _ = _ := by ring

/-- A rational function is pole-stable when every root of its reduced denominator
lies in the open left half-plane. This is algebraic pole stability, not an
impulse-response or decay definition. -/
def IsPoleStable (f : RatFunc ℂ) : Prop :=
  ∀ z : ℂ, f.denom.IsRoot z → z.re < 0

theorem isPoleStable_of_denominator_dvd_hurwitz
    {f : RatFunc ℂ} {p : Polynomial ℂ}
    (hdiv : f.denom ∣ p)
    (hp : ∀ z : ℂ, p.IsRoot z → z.re < 0) :
    IsPoleStable f := by
  intro z hz
  exact hp z (hz.dvd hdiv)

theorem isPoleStable_mk_of_denominator_hurwitz
    (p q : Polynomial ℂ)
    (hHurwitz : ∀ z : ℂ, q.IsRoot z → z.re < 0) :
    IsPoleStable (RatFunc.mk p q) := by
  apply isPoleStable_of_denominator_dvd_hurwitz
    (p := q) (hp := hHurwitz)
  rw [RatFunc.mk_eq_div]
  exact RatFunc.denom_div_dvd p q

end RatFunc

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Polynomial numerator in the Cramer/adjugate formula for the scalar channel
`cᵀ (sI - A)⁻¹ b`. -/
def channelTransferNumerator (A : Matrix n n ℂ) (c b : n → ℂ) : Polynomial ℂ :=
  ∑ i : n, ∑ j : n,
    Polynomial.C (c i) * (Matrix.adjugate (Matrix.charmatrix A) i j) * Polynomial.C (b j)

/-- Rational state-space channel, represented by the adjugate formula over the
characteristic denominator. Any pole cancellation is handled by `RatFunc`'s
reduced denominator. -/
def channelTransferRatFunc (A : Matrix n n ℂ) (c b : n → ℂ) : RatFunc ℂ :=
  RatFunc.mk (channelTransferNumerator A c b) A.charpoly

/-- The reduced denominator of the rational channel divides the characteristic
polynomial. This is the formal pole-cancellation statement: cancellation may
shrink the denominator, but cannot create a pole outside the state spectrum. -/
theorem channelTransferRatFunc_denom_dvd_charpoly
    (A : Matrix n n ℂ) (c b : n → ℂ) :
    (channelTransferRatFunc A c b).denom ∣ A.charpoly := by
  rw [channelTransferRatFunc, RatFunc.mk_eq_div]
  exact RatFunc.denom_div_dvd _ _

/-- Hurwitz internal matrix spectrum implies pole-stability of every scalar
state-space channel formed by Cramer's rule. This only proves the forward
implication: cancellations can remove poles, so the converse need not hold. -/
theorem channelTransferRatFunc_isPoleStable
    (A : Matrix n n ℂ) (c b : n → ℂ)
    (hHurwitz : ∀ z : ℂ, A.charpoly.IsRoot z → z.re < 0) :
    RatFunc.IsPoleStable (channelTransferRatFunc A c b) := by
  exact RatFunc.isPoleStable_of_denominator_dvd_hurwitz
    (channelTransferRatFunc_denom_dvd_charpoly A c b) hHurwitz

/-- If the matrix's (complex) linear endomorphism has spectrum in the open
left half-plane, then its scalar state-space channel is pole-stable. -/
theorem channelTransferRatFunc_isPoleStable_of_spectrum
    (A : Matrix n n ℂ) (c b : n → ℂ)
    (hA : ∀ z : ℂ, z ∈ spectrum ℂ A.toLin' → z.re < 0) :
    RatFunc.IsPoleStable (channelTransferRatFunc A c b) := by
  apply channelTransferRatFunc_isPoleStable
  intro z hz
  apply hA z
  exact (Module.End.mem_spectrum_iff_isRoot_charpoly A.toLin' z).2 (by simpa using hz)

/-- Complex rational transfer of a real finite-dimensional realization, obtained
by coefficient-wise complexification of its state and channel matrices. If the
complex roots of the real characteristic polynomial all lie in the open left
half-plane, then the reduced transfer denominator has no other roots. -/
theorem realMatrix_channelTransferRatFunc_isPoleStable
    (A : Matrix n n ℝ) (c b : n → ℝ)
    (hA : ∀ z : ℂ,
      (Polynomial.map (algebraMap ℝ ℂ) A.charpoly).IsRoot z → z.re < 0) :
    RatFunc.IsPoleStable
      (channelTransferRatFunc (A.map (algebraMap ℝ ℂ))
        (fun i => (c i : ℂ)) (fun i => (b i : ℂ))) := by
  apply channelTransferRatFunc_isPoleStable
  intro z hz
  apply hA z
  simpa only [Polynomial.IsRoot.def, Matrix.charpoly_map, Polynomial.eval_map] using hz

/-- The Cramer numerator evaluated at a nonsingular point is the characteristic
determinant times the ordinary resolvent channel value. This is the pointwise
bridge between the rational realization and `cᵀ (sI-A)⁻¹ b`. -/
theorem channelTransferNumerator_eval_eq_det_mul_resolvent
    (A : Matrix n n ℂ) (c b : n → ℂ) (z : ℂ)
    (hdet : (Matrix.scalar n z - A).det ≠ 0) :
    (channelTransferNumerator A c b).eval z =
      A.charpoly.eval z *
        ∑ i : n, c i * (((Matrix.scalar n z - A)⁻¹) *ᵥ b) i := by
  let M : Matrix n n ℂ := Matrix.scalar n z - A
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr (by simpa [M] using hdet)
  have hdetchar : A.charpoly.eval z = M.det := by
    simpa [M] using Matrix.eval_charpoly A z
  have hM : (Polynomial.evalRingHom z).mapMatrix (Matrix.charmatrix A) = M := by
    ext i j
    change ((Matrix.charmatrix A) i j).eval z = M i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.charmatrix_apply_eq, M, Matrix.scalar_apply]
    · simp [M, Matrix.scalar_apply, hij]
  have hadjEval :
      (Polynomial.evalRingHom z).mapMatrix (Matrix.adjugate (Matrix.charmatrix A)) =
        M.adjugate := by
    rw [RingHom.map_adjugate, hM]
  have hadjEntry (i j : n) :
      (Matrix.adjugate (Matrix.charmatrix A) i j).eval z = M.adjugate i j := by
    have h := congrArg (fun N : Matrix n n ℂ => N i j) hadjEval
    simpa using h
  have hadj : M.adjugate = M.det • M⁻¹ := by
    calc
      M.adjugate = M.adjugate * 1 := by simp
      _ = M.adjugate * (M * M⁻¹) := by rw [Matrix.mul_nonsing_inv M hunit]
      _ = (M.adjugate * M) * M⁻¹ := by rw [Matrix.mul_assoc]
      _ = (M.det • (1 : Matrix n n ℂ)) * M⁻¹ := by rw [Matrix.adjugate_mul]
      _ = M.det • M⁻¹ := by simp
  have hnum : (channelTransferNumerator A c b).eval z =
      ∑ i : n, c i * (M.adjugate *ᵥ b) i := by
    rw [channelTransferNumerator, Polynomial.eval_finsetSum]
    simp_rw [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, hadjEntry]
    simp only [Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hnum, hadj, smul_mulVec]
  calc
    _ = ∑ i : n, M.det * (c i * ((M⁻¹) *ᵥ b) i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    _ = M.det * ∑ i : n, c i * ((M⁻¹) *ᵥ b) i := by rw [Finset.mul_sum]
    _ = A.charpoly.eval z * ∑ i : n, c i * ((M⁻¹) *ᵥ b) i := by rw [← hdetchar]

/-- At every nonsingular point, the evaluated rational state-space channel
agrees with the ordinary matrix-resolvent channel. -/
theorem channelTransferRatFunc_eval_eq_resolvent
    (A : Matrix n n ℂ) (c b : n → ℂ) (z : ℂ)
    (hdet : (Matrix.scalar n z - A).det ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) z (channelTransferRatFunc A c b) =
      ∑ i : n, c i * (((Matrix.scalar n z - A)⁻¹) *ᵥ b) i := by
  have hpoly : A.charpoly.eval z ≠ 0 := by
    rw [Matrix.eval_charpoly]
    simpa using hdet
  rw [channelTransferRatFunc, RatFunc.eval_mk_of_eval_ne_zero _ _ _ hpoly]
  rw [channelTransferNumerator_eval_eq_det_mul_resolvent A c b z hdet]
  rw [Matrix.eval_charpoly]
  field_simp [hpoly]

/-- Zero output cancels every state pole, even for an internally unstable `A`;
therefore transfer pole-stability alone cannot imply internal Hurwitz stability. -/
theorem channelTransferRatFunc_isPoleStable_of_zero_output
    (A : Matrix n n ℂ) (b : n → ℂ) :
    RatFunc.IsPoleStable (channelTransferRatFunc A (0 : n → ℂ) b) := by
  rw [RatFunc.IsPoleStable, channelTransferRatFunc]
  simp [channelTransferNumerator]

end Matrix

namespace LinearSystem

variable {X D Z : Type*}
variable [AddCommGroup X] [Module ℝ X] [FiniteDimensional ℝ X]
variable [AddCommGroup D] [Module ℝ D] [FiniteDimensional ℝ D]
variable [AddCommGroup Z] [Module ℝ Z] [FiniteDimensional ℝ Z]

/-- Complexifying the matrix of a real endomorphism preserves its
characteristic polynomial after coefficient base change. -/
theorem charpoly_complexified_realMatrix (A : X →ₗ[ℝ] X)
    (b : Module.Basis (Fin (Module.finrank ℝ X)) ℝ X) :
    ((A.toMatrix b b).map (algebraMap ℝ ℂ)).charpoly =
      A.charpoly.map (algebraMap ℝ ℂ) := by
  rw [Matrix.charpoly_map, LinearMap.charpoly_toMatrix]

/-- If the controllable–observable realization is Hurwitz, every scalar entry
of its complexified rational transfer matrix has only left-half-plane poles.
The converse is not asserted: it needs a no-cancellation theorem for the
entire MIMO transfer matrix. -/
theorem controllableObservableRealization_entry_transfer_poleStable
    (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (hHurwitz : LinearMap.IsHurwitz
      (LinearMap.controllableObservableRealization A E H 0).A)
    (i : Fin (Module.finrank ℝ Z)) (j : Fin (Module.finrank ℝ D)) :
    RatFunc.IsPoleStable (Matrix.channelTransferRatFunc
      (((LinearMap.controllableObservableRealization A E H 0).A.toMatrix
        (Module.finBasis ℝ _) (Module.finBasis ℝ _)).map (algebraMap ℝ ℂ))
      (fun k => (((LinearMap.controllableObservableRealization A E H 0).C.toMatrix
        (Module.finBasis ℝ _) (Module.finBasis ℝ _)) i k : ℂ))
      (fun k => (((LinearMap.controllableObservableRealization A E H 0).B.toMatrix
        (Module.finBasis ℝ _) (Module.finBasis ℝ _)) k j : ℂ))) := by
  let M := LinearMap.controllableObservableRealization A E H 0
  let S := (LinearMap.reachableSubspace A E) ⧸ LinearMap.reachableIntersection A E H
  let bS : Module.Basis (Fin (Module.finrank ℝ S)) ℝ S := Module.finBasis ℝ S
  let bD : Module.Basis (Fin (Module.finrank ℝ D)) ℝ D := Module.finBasis ℝ D
  let bZ : Module.Basis (Fin (Module.finrank ℝ Z)) ℝ Z := Module.finBasis ℝ Z
  let AM := M.A.toMatrix bS bS
  let BM := M.B.toMatrix bD bS
  let HM := M.C.toMatrix bS bZ
  change RatFunc.IsPoleStable (Matrix.channelTransferRatFunc (AM.map (algebraMap ℝ ℂ))
    (fun k => (HM i k : ℂ)) (fun k => (BM k j : ℂ)))
  apply Matrix.realMatrix_channelTransferRatFunc_isPoleStable
  intro z hz
  have hz' : (Polynomial.map (algebraMap ℝ ℂ) AM.charpoly).eval z = 0 := by
    simpa only [Polynomial.IsRoot.def, Matrix.charpoly_map,
      LinearMap.charpoly_toMatrix] using hz
  apply hHurwitz z
  simpa only [AM, LinearMap.charpoly_toMatrix] using hz'

end LinearSystem
