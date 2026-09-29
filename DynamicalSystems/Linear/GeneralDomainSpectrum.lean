/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.GeneralStabilityDomain

/-! # Spectral transfer for a general stability domain

Characteristic-polynomial identities transport spectral inclusion without
using the special geometry of the open left half-plane. These lemmas are the
domain-parameterized versions of the restriction, quotient, and triangular
block steps in the existing Hurwitz controller proofs.
-/

@[expose] public section

namespace LinearMap

variable {X Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [AddCommGroup Y] [Module ℝ Y] [FiniteDimensional ℝ Y]

/-- Spectral inclusion depends only on the characteristic polynomial. -/
theorem isStableIn_of_charpoly_eq (Cg : Set ℂ) {T S : X →ₗ[ℝ] X}
    (h : T.charpoly = S.charpoly) (hS : IsStableIn Cg S) : IsStableIn Cg T := by
  intro z hz
  apply hS z
  rwa [h] at hz

/-- Conjugating a state map preserves spectral inclusion. -/
theorem isStableIn_conj_iff (Cg : Set ℂ) (e : X ≃ₗ[ℝ] Y) (T : X →ₗ[ℝ] X) :
    IsStableIn Cg (e.conj T) ↔ IsStableIn Cg T := by
  rw [IsStableIn, IsStableIn, LinearEquiv.charpoly_conj]

/-- Every pole of an invariant restriction is a pole of the ambient map. -/
theorem isStableIn_restrict_of_invariant (Cg : Set ℂ)
    (A : X →ₗ[ℝ] X) (V : Submodule ℝ X)
    (hV : ∀ x ∈ V, A x ∈ V) (hA : IsStableIn Cg A) :
    IsStableIn Cg (A.restrict hV) := by
  intro z hz
  obtain ⟨q, hq⟩ := charpoly_restrict_dvd_of_invariant A V hV
  apply hA z
  rw [hq, Polynomial.map_mul, Polynomial.eval_mul, hz, zero_mul]

/-- Every pole of an invariant quotient is a pole of the ambient map. -/
theorem isStableIn_quotient_of_invariant (Cg : Set ℂ)
    (A : X →ₗ[ℝ] X) (V : Submodule ℝ X)
    (hV : ∀ x ∈ V, A x ∈ V) (hA : IsStableIn Cg A) :
    IsStableIn Cg (Submodule.mapQ V V A (fun x hx ↦ hV x hx)) := by
  intro z hz
  have hfac := charpoly_restrict_of_invariant A V hV
  apply hA z
  rw [hfac, Polynomial.map_mul, Polynomial.eval_mul, hz, mul_zero]

/-- A triangular block map has all poles in `Cg` exactly when both diagonal
blocks do. -/
theorem isStableIn_blockOperator₂_iff
    {M N : Type*}
    [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    [AddCommGroup N] [Module ℝ N] [FiniteDimensional ℝ N]
    (Cg : Set ℂ) (T : M →ₗ[ℝ] M) (K : N →ₗ[ℝ] M) (S : N →ₗ[ℝ] N) :
    IsStableIn Cg (blockOperator₂ T K S) ↔ IsStableIn Cg T ∧ IsStableIn Cg S := by
  constructor
  · intro h
    constructor
    · intro z hz
      apply h z
      rw [charpoly_blockOperator₂, Polynomial.map_mul, Polynomial.eval_mul, hz, zero_mul]
    · intro z hz
      apply h z
      rw [charpoly_blockOperator₂, Polynomial.map_mul, Polynomial.eval_mul, hz, mul_zero]
  · rintro ⟨hT, hS⟩ z hz
    rw [charpoly_blockOperator₂, Polynomial.map_mul, Polynomial.eval_mul] at hz
    rcases mul_eq_zero.mp hz with hz | hz
    · exact hT z hz
    · exact hS z hz

/-- Spectral inclusion of a triangular block operator descends to its quotient
by a product of invariant subspaces. -/
theorem isStableIn_mapQ_prod_of_isStableIn
    {M N : Type*}
    [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    [AddCommGroup N] [Module ℝ N] [FiniteDimensional ℝ N]
    (Cg : Set ℂ) (T : M →ₗ[ℝ] M) (K : N →ₗ[ℝ] M) (S : N →ₗ[ℝ] N)
    (P : Submodule ℝ M) (Q : Submodule ℝ N)
    (hTP : ∀ x ∈ P, T x ∈ P) (hSQ : ∀ y ∈ Q, S y ∈ Q)
    (hKQ : ∀ y ∈ Q, K y ∈ P)
    (hTq : IsStableIn Cg (Submodule.mapQ P P T (fun x hx ↦ hTP x hx)))
    (hSq : IsStableIn Cg (Submodule.mapQ Q Q S (fun y hy ↦ hSQ y hy))) :
    IsStableIn Cg (Submodule.mapQ (P.prod Q) (P.prod Q) (blockOperator₂ T K S)
      (prodInvariance T K S P Q hTP hSQ hKQ)) := by
  classical
  let hA : ∀ z ∈ P.prod Q, blockOperator₂ T K S z ∈ P.prod Q :=
    prodInvariance T K S P Q hTP hSQ hKQ
  let φ : (M × N) ⧸ (P.prod Q) →ₗ[ℝ] (M × N) ⧸ (P.prod Q) :=
    Submodule.mapQ (P.prod Q) (P.prod Q) (blockOperator₂ T K S) hA
  let Tq : M ⧸ P →ₗ[ℝ] M ⧸ P := Submodule.mapQ P P T (fun x hx ↦ hTP x hx)
  let Sq : N ⧸ Q →ₗ[ℝ] N ⧸ Q := Submodule.mapQ Q Q S (fun y hy ↦ hSQ y hy)
  let Kbar : N ⧸ Q →ₗ[ℝ] M ⧸ P := Submodule.mapQ Q P K (fun y hy ↦ hKQ y hy)
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
  change IsStableIn Cg φ
  intro z hz
  have hz' : ((blockOperator₂ Tq Kbar Sq).charpoly.map (algebraMap ℝ ℂ)).eval z = 0 := by
    rwa [← hchar]
  rw [charpoly_blockOperator₂, Polynomial.map_mul, Polynomial.eval_mul] at hz'
  rcases mul_eq_zero.mp hz' with h | h
  · exact hTq z h
  · exact hSq z h

/-- Spectral inclusion on a nested invariant quotient is preserved by a
conjugacy that identifies both numerator and denominator subspaces. -/
theorem isStableIn_mapQ_nested_conj
    (Cg : Set ℂ) (T : X →ₗ[ℝ] X) (U : Y →ₗ[ℝ] Y) (e : X ≃ₗ[ℝ] Y)
    (he : e.conj T = U)
    (P Q : Submodule ℝ X) (hPQ : P ≤ Q)
    (hQ : ∀ x ∈ Q, T x ∈ Q) (hP : ∀ x ∈ P, T x ∈ P)
    (P2 Q2 : Submodule ℝ Y) (_hP2Q2 : P2 ≤ Q2)
    (hQ2 : ∀ y ∈ Q2, U y ∈ Q2) (hP2 : ∀ y ∈ P2, U y ∈ P2)
    (hPmap : P.map (e : X →ₗ[ℝ] Y) = P2)
    (hQmap : Q.map (e : X →ₗ[ℝ] Y) = Q2) :
    IsStableIn Cg (Submodule.mapQ (P.comap Q.subtype) (P.comap Q.subtype)
        (T.restrict hQ) (fun x hx ↦ hP (x : X) hx)) ↔
      IsStableIn Cg (Submodule.mapQ (P2.comap Q2.subtype) (P2.comap Q2.subtype)
        (U.restrict hQ2) (fun y hy ↦ hP2 (y : Y) hy)) := by
  let TQ : Q →ₗ[ℝ] Q := T.restrict hQ
  let UQ : Q2 →ₗ[ℝ] Q2 := U.restrict hQ2
  let Pq : Submodule ℝ Q := P.comap Q.subtype
  let P2q : Submodule ℝ Q2 := P2.comap Q2.subtype
  let eQ : Q ≃ₗ[ℝ] Q2 := e.ofSubmodules Q Q2 hQmap
  have hPmap' : Pq.map (eQ : Q →ₗ[ℝ] Q2) = P2q := by
    ext y
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ((eQ x : Q2) : Y) ∈ P2
      rw [LinearEquiv.ofSubmodules_apply]
      exact hPmap ▸ Submodule.mem_map_of_mem hx
    · intro hy
      have hy' : (y : Y) ∈ P2 := hy
      rw [← hPmap, Submodule.mem_map] at hy'
      obtain ⟨x, hxP, hxeq⟩ := hy'
      refine ⟨⟨x, hPQ hxP⟩, hxP, ?_⟩
      apply Subtype.ext
      change (e : X →ₗ[ℝ] Y) x = (y : Y)
      exact hxeq
  let φ : Q ⧸ Pq →ₗ[ℝ] Q ⧸ Pq :=
    Submodule.mapQ Pq Pq TQ (fun x hx ↦ hP (x : X) hx)
  let ψ : Q2 ⧸ P2q →ₗ[ℝ] Q2 ⧸ P2q :=
    Submodule.mapQ P2q P2q UQ (fun y hy ↦ hP2 (y : Y) hy)
  let eP := Submodule.Quotient.equiv Pq P2q eQ hPmap'
  have hchar : ψ.charpoly = φ.charpoly := by
    have hconj : eP.conj φ = ψ := by
      apply LinearMap.ext
      intro x
      refine Submodule.Quotient.induction_on (p := P2q) x ?_
      intro y
      rw [LinearEquiv.conj_apply_apply]
      have hs : eP.symm (Submodule.Quotient.mk y) =
          Submodule.Quotient.mk (eQ.symm y) := by
        rw [Submodule.Quotient.equiv_symm, Submodule.Quotient.equiv_apply,
          Submodule.mapQ_apply]
        rfl
      rw [hs]
      have h1 : φ (Submodule.Quotient.mk (eQ.symm y)) =
          Submodule.Quotient.mk (TQ (eQ.symm y)) := rfl
      rw [h1]
      have h2 : eP (Submodule.Quotient.mk (TQ (eQ.symm y))) =
          Submodule.Quotient.mk (eQ (TQ (eQ.symm y))) := rfl
      rw [h2]
      have h3 : ψ (Submodule.Quotient.mk y) =
          Submodule.Quotient.mk (UQ y) := rfl
      rw [h3]
      congr 1
      apply Subtype.ext
      have hzs : ((eQ.symm y : Q) : X) = e.symm (y : Y) :=
        LinearEquiv.ofSubmodules_symm_apply e hQmap y
      change e (T ((eQ.symm y : Q) : X)) = U (y : Y)
      rw [hzs]
      rw [← LinearEquiv.conj_apply_apply, he]
    rw [← hconj, LinearEquiv.charpoly_conj]
  change IsStableIn Cg φ ↔ IsStableIn Cg ψ
  rw [IsStableIn, IsStableIn, hchar]

/-- Spectral inclusion of a nested restriction of an upper triangular block
operator follows from inclusion for the two diagonal nested quotients. -/
theorem isStableIn_mapQ_prod_restrict_of_isStableIn
    {M N : Type*}
    [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]
    [AddCommGroup N] [Module ℝ N] [FiniteDimensional ℝ N]
    (Cg : Set ℂ) (A : M →ₗ[ℝ] M) (B : N →ₗ[ℝ] M) (C : N →ₗ[ℝ] N)
    (W : Submodule ℝ M) (U : Submodule ℝ N)
    (V : Submodule ℝ M) (T : Submodule ℝ N)
    (hVW : V ≤ W) (hTU : T ≤ U)
    (hAW : ∀ x ∈ W, A x ∈ W) (hCU : ∀ y ∈ U, C y ∈ U)
    (hBU : ∀ y ∈ U, B y ∈ W)
    (hAV : ∀ x ∈ V, A x ∈ V) (hCT : ∀ y ∈ T, C y ∈ T)
    (hBT : ∀ y ∈ T, B y ∈ V)
    (hAq : IsStableIn Cg (Submodule.mapQ (V.comap W.subtype) (V.comap W.subtype)
      (A.restrict hAW) (fun x hx ↦ hAV x.1 hx)))
    (hCq : IsStableIn Cg (Submodule.mapQ (T.comap U.subtype) (T.comap U.subtype)
      (C.restrict hCU) (fun y hy ↦ hCT y.1 hy))) :
    IsStableIn Cg (Submodule.mapQ
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
  have hV'T' : ∀ p ∈ V'.prod T', (blockOperator₂ A' B' C') p ∈ V'.prod T' := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Submodule.mem_prod.mp hp
    exact Submodule.mem_prod.mpr
      ⟨V'.add_mem (hAV _ hp1) (hBT _ hp2), hCT _ hp2⟩
  have hQuot : IsStableIn Cg (Submodule.mapQ (V'.prod T') (V'.prod T')
      (blockOperator₂ A' B' C') hV'T') := by
    refine isStableIn_mapQ_prod_of_isStableIn Cg A' B' C' V' T'
      (fun x hx ↦ hAV x.1 hx) (fun y hy ↦ hCT y.1 hy)
      (fun y hy ↦ hBT y.1 hy) ?_ ?_
    · simpa only [A', V'] using hAq
    · simpa only [C', T'] using hCq
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
  have hchar : (Submodule.mapQ P P fr hP).charpoly =
      (Submodule.mapQ (V'.prod T') (V'.prod T') (blockOperator₂ A' B' C') hV'T').charpoly := by
    rw [← LinearEquiv.charpoly_conj qe (Submodule.mapQ P P fr hP), hconj]
  change IsStableIn Cg (Submodule.mapQ P P fr hP)
  intro z hz
  apply hQuot z
  rwa [hchar] at hz

end LinearMap
