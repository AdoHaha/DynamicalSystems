/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.Duality
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Prod

/-! # The four-block Kalman decomposition

This file assembles the two-block decompositions of
`DynamicalSystems.Linear.Duality` into the full four-block Kalman form by combining
the structural results of Trentelman–Stoorvogel–Hautus, *Control Theory for Linear
Systems*, Section 3.4 and Exercise 3.7. The combined four-block result is derived
here, rather than quoted as a separate theorem from that section.

For a linear system `Σ = (A, B, C, D)` on a state space `X` over a field `𝕜`,
write

* `W = LinearMap.reachableSubspace A B`, the reachable subspace;
* `N = LinearMap.unobservableSubspace C A`, the unobservable subspace;
* `I = W ⊓ N`, the intersection.

Both `W` and `N` are `A`-invariant, hence so is `I`. The file chooses

* `Rco`, a complement of `I` in `W`;
* `Nuo`, a complement of `I` in `N`;
* `Ruo`, a complement of `W ⊔ N` in `X`,

and builds the state-space equivalence

`(((I × Rco) × Nuo) × Ruo) ≃ₗ[𝕜] X`.

The Kalman block identities are then read off from the invariance of the three
subspaces `I`, `W` and `N`:

* the `A`-blocks with `(row, column)` in
  `(2,1), (3,1), (4,1), (3,2), (4,2), (2,3), (4,3)` vanish;
* the `B`-blocks in rows `3` and `4` vanish, because `im B ⊆ W`;
* the `C`-blocks in columns `1` and `3` vanish, because `I ⊆ N` and `Nuo ⊆ N`
  and `N ⊆ ker C`;
* the feedthrough `D` is untouched.

None of the chosen complements is assumed to be `A`-invariant; such complements
need not exist, and the four-block form above only requires the invariance of
`I`, `W` and `N`.

Finally, the *controllable and observable realization* is constructed by
restricting the system to `W` and then quotienting by `I = W ⊓ N`: the
restricted pair `(A|_W, B|_W)` is controllable, and the induced pair on
`W ⧸ I` is observable. Its feedthrough is `D`.

## Main definitions

* `LinearMap.reachableUnobservable`
* `LinearMap.kalmanRco`, `LinearMap.kalmanNuo`, `LinearMap.kalmanRuo`
* `LinearMap.kalmanEquiv`
* `LinearMap.controllableObservableRealization`

## Main theorems

* `LinearMap.kalmanEquiv_symm_snd_eq_zero` and companions: component
  characterisations of the equivalence;
* `LinearMap.kalman_A_*`, `LinearMap.kalman_B_*`, `LinearMap.kalman_C_*`:
  the zero blocks;
* `LinearMap.isControllable_controllableObservableRealization` and
  `LinearMap.isObservable_controllableObservableRealization`.

## References

* H. L. Trentelman, A. A. Stoorvogel, M. Hautus, *Control Theory for Linear
  Systems*, Springer, 2001, Sections 3.3–3.4.
-/

@[expose] public section

namespace Submodule

variable {𝕜 X : Type*}
variable [Field 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]

/-- If `q` is a complement of `p` *inside* `s`, i.e. `p ⊔ q = s` and
`p ⊓ q = ⊥`, then `p × q` is linearly equivalent to `s`. This is the relative
version of `Submodule.prodEquivOfIsCompl` needed for the nested complements of
the four-block Kalman decomposition. -/
noncomputable def prodEquivOfIsComplOfLe (p q s : Submodule 𝕜 X)
    (hsup : p ⊔ q = s) (hinf : p ⊓ q = ⊥) : (p × q) ≃ₗ[𝕜] s :=
  LinearEquiv.ofBijective
    { toFun := fun x ↦
        ⟨(x.1 : X) + (x.2 : X), by
          rw [← hsup]
          exact Submodule.add_mem_sup x.1.2 x.2.2⟩
      map_add' := by
        intro x y
        ext
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add]
        abel
      map_smul' := by
        intro c x
        ext
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul,
          RingHom.id_apply]
        rw [smul_add] }
    (by
      constructor
      · intro x y hxy
        have h : (x.1 : X) + (x.2 : X) = (y.1 : X) + (y.2 : X) := by
          have := congrArg Subtype.val hxy
          simpa using this
        have hmem : (x.1 : X) - (y.1 : X) ∈ p ⊓ q := by
          refine ⟨Submodule.sub_mem p x.1.2 y.1.2, ?_⟩
          have hsub : (x.1 : X) - (y.1 : X) = (y.2 : X) - (x.2 : X) := by
            rw [sub_eq_sub_iff_add_eq_add, h, add_comm]
          rw [hsub]
          exact Submodule.sub_mem q y.2.2 x.2.2
        have hzero : (x.1 : X) - (y.1 : X) = 0 := by
          have := hinf ▸ hmem
          simpa using this
        have hx1 : (x.1 : X) = (y.1 : X) := sub_eq_zero.mp hzero
        have hx2 : x.2 = y.2 := by
          refine Subtype.ext ?_
          have h' := h
          rw [← hx1] at h'
          exact add_left_cancel h'
        exact Prod.ext (Subtype.ext hx1) hx2
      · intro z
        have hz : (z : X) ∈ p ⊔ q := by
          rw [hsup]
          exact z.2
        obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hz
        exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩)

@[simp]
theorem prodEquivOfIsComplOfLe_apply_coe (p q s : Submodule 𝕜 X)
    (hsup : p ⊔ q = s) (hinf : p ⊓ q = ⊥) (x : p × q) :
    ((prodEquivOfIsComplOfLe p q s hsup hinf x : s) : X) =
      (x.1 : X) + (x.2 : X) := rfl

/-- Characterisation of the second component of the inverse of
`Submodule.prodEquivOfIsComplOfLe`: it vanishes exactly on `p`. -/
theorem prodEquivOfIsComplOfLe_symm_apply_snd_eq_zero (p q s : Submodule 𝕜 X)
    (hsup : p ⊔ q = s) (hinf : p ⊓ q = ⊥) {x : s} :
    ((prodEquivOfIsComplOfLe p q s hsup hinf).symm x).2 = 0 ↔ (x : X) ∈ p := by
  have hcoe : (((prodEquivOfIsComplOfLe p q s hsup hinf).symm x).1 : X) +
      (((prodEquivOfIsComplOfLe p q s hsup hinf).symm x).2 : X) = (x : X) := by
    have h := congrArg Subtype.val
      ((prodEquivOfIsComplOfLe p q s hsup hinf).apply_symm_apply x)
    exact h
  constructor
  · intro h
    have hx1 : (x : X) =
        (((prodEquivOfIsComplOfLe p q s hsup hinf).symm x).1 : X) := by
      rw [← hcoe, h, Submodule.coe_zero, add_zero]
    rw [hx1]
    exact ((prodEquivOfIsComplOfLe p q s hsup hinf).symm x).1.2
  · intro h
    have hmem : (((prodEquivOfIsComplOfLe p q s hsup hinf).symm x).2 : X) ∈ p ⊓ q := by
      refine ⟨?_, ((prodEquivOfIsComplOfLe p q s hsup hinf).symm x).2.2⟩
      have hsub : (((prodEquivOfIsComplOfLe p q s hsup hinf).symm x).2 : X) =
          (x : X) - (((prodEquivOfIsComplOfLe p q s hsup hinf).symm x).1 : X) := by
        rw [← hcoe]
        abel
      rw [hsub]
      exact Submodule.sub_mem p h
        ((prodEquivOfIsComplOfLe p q s hsup hinf).symm x).1.2
    have hzero : (((prodEquivOfIsComplOfLe p q s hsup hinf).symm x).2 : X) = 0 := by
      have := hinf ▸ hmem
      simpa using this
    exact Subtype.ext hzero

/-- The inverse of `Submodule.prodEquivOfIsComplOfLe` reconstructs `x` as the sum
of its two components. -/
theorem prodEquivOfIsComplOfLe_symm_apply_add (p q s : Submodule 𝕜 X)
    (hsup : p ⊔ q = s) (hinf : p ⊓ q = ⊥) (x : s) :
    (((prodEquivOfIsComplOfLe p q s hsup hinf).symm x).1 : X) +
      (((prodEquivOfIsComplOfLe p q s hsup hinf).symm x).2 : X) = (x : X) := by
  have h := congrArg Subtype.val
    ((prodEquivOfIsComplOfLe p q s hsup hinf).apply_symm_apply x)
  exact h

/-- If `x ∈ p` and `p ≤ s`, then the inverse of `Submodule.prodEquivOfIsComplOfLe`
sends `x` to the pure `p`-component. -/
theorem prodEquivOfIsComplOfLe_symm_apply_of_mem (p q s : Submodule 𝕜 X)
    (hsup : p ⊔ q = s) (hinf : p ⊓ q = ⊥) {x : s} (hx : (x : X) ∈ p) :
    (prodEquivOfIsComplOfLe p q s hsup hinf).symm x = (⟨(x : X), hx⟩, 0) := by
  have h2 : ((prodEquivOfIsComplOfLe p q s hsup hinf).symm x).2 = 0 :=
    (prodEquivOfIsComplOfLe_symm_apply_snd_eq_zero p q s hsup hinf).mpr hx
  have hcoe : (((prodEquivOfIsComplOfLe p q s hsup hinf).symm x).1 : X) +
      (((prodEquivOfIsComplOfLe p q s hsup hinf).symm x).2 : X) = (x : X) := by
    have h := congrArg Subtype.val
      ((prodEquivOfIsComplOfLe p q s hsup hinf).apply_symm_apply x)
    exact h
  refine Prod.ext ?_ h2
  refine Subtype.ext ?_
  rw [h2, Submodule.coe_zero, add_zero] at hcoe
  exact hcoe

/-- **Existence of a complement inside a subspace.** For any `p ≤ s` there is
`q ≤ s` with `p ⊔ q = s` and `p ⊓ q = ⊥`. This is the relative form of
`Submodule.exists_isCompl` used to choose the Kalman complements. -/
theorem exists_isCompl_of_le (p s : Submodule 𝕜 X) (hp : p ≤ s) :
    ∃ q : Submodule 𝕜 X, q ≤ s ∧ p ⊔ q = s ∧ p ⊓ q = ⊥ := by
  obtain ⟨q', hq'⟩ := Submodule.exists_isCompl (Submodule.comap s.subtype p)
  refine ⟨q'.map s.subtype, Submodule.map_subtype_le (p := s) q', ?_, ?_⟩
  · have hmap : (Submodule.comap s.subtype p).map s.subtype ⊔ q'.map s.subtype = s := by
      rw [← Submodule.map_sup, hq'.sup_eq_top, Submodule.map_top,
        Submodule.range_subtype]
    rw [Submodule.map_comap_subtype, inf_of_le_right hp] at hmap
    exact hmap
  · rw [Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨hxp, hxq⟩ := Submodule.mem_inf.mp hx
    have hxs : x ∈ s := hp hxp
    obtain ⟨y, hyq', hyx⟩ := hxq
    have hy : (⟨x, hxs⟩ : s) ∈ Submodule.comap s.subtype p := hxp
    have hyq : (⟨x, hxs⟩ : s) ∈ q' := by
      rw [show (⟨x, hxs⟩ : s) = y from Subtype.ext hyx.symm]
      exact hyq'
    have : (⟨x, hxs⟩ : s) ∈ Submodule.comap s.subtype p ⊓ q' := ⟨hy, hyq⟩
    rw [hq'.inf_eq_bot] at this
    have hz : (⟨x, hxs⟩ : s) = 0 := by simpa using this
    exact congrArg Subtype.val hz

/-- If `x ∈ p`, then the inverse of `Submodule.prodEquivOfIsCompl` sends `x` to
the pure `p`-component. -/
theorem prodEquivOfIsCompl_symm_apply_of_mem {p q : Submodule 𝕜 X} (h : IsCompl p q)
    {x : X} (hx : x ∈ p) :
    (prodEquivOfIsCompl p q h).symm x = (⟨x, hx⟩, 0) :=
  prodEquivOfIsCompl_symm_apply_left (p := p) (q := q) h (⟨x, hx⟩ : p)

end Submodule

namespace LinearMap

variable {𝕜 X U Y : Type*}
variable [Field 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup Y] [Module 𝕜 Y]

/-! ## Adapted subspaces and the four-block equivalence -/

/-- The intersection `W ⊓ N` of the reachable subspace `W = reachableSubspace A B`
and the unobservable subspace `N = unobservableSubspace C A`. This is the kernel
of the controllable and observable realization: it is exactly the part of the
reachable subspace that cannot be observed. -/
def reachableUnobservable (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    Submodule 𝕜 X :=
  reachableSubspace A B ⊓ unobservableSubspace C A

/-- `W ⊔ N`, the sum of the reachable and unobservable subspaces. This is the
subspace that the first three Kalman blocks span. -/
def reachableSupUnobservable (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    Submodule 𝕜 X :=
  reachableSubspace A B ⊔ unobservableSubspace C A

/-- A complement `Rco` of `I = W ⊓ N` inside the reachable subspace `W`. No
invariance of `Rco` is assumed or implied. -/
noncomputable def kalmanRco (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    Submodule 𝕜 X :=
  (Submodule.exists_isCompl_of_le (reachableUnobservable A B C)
    (reachableSubspace A B) inf_le_left).choose

/-- A complement `Nuo` of `I = W ⊓ N` inside the unobservable subspace `N`. -/
noncomputable def kalmanNuo (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    Submodule 𝕜 X :=
  (Submodule.exists_isCompl_of_le (reachableUnobservable A B C)
    (unobservableSubspace C A) inf_le_right).choose

/-- A complement `Ruo` of `W ⊔ N` in the whole state space `X`. -/
noncomputable def kalmanRuo (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    Submodule 𝕜 X :=
  (Submodule.exists_isCompl_of_le
    (reachableSubspace A B ⊔ unobservableSubspace C A) ⊤ le_top).choose

theorem kalmanRco_le (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    kalmanRco A B C ≤ reachableSubspace A B :=
  (Submodule.exists_isCompl_of_le (reachableUnobservable A B C)
    (reachableSubspace A B) inf_le_left).choose_spec.1

theorem kalmanRco_sup (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    reachableUnobservable A B C ⊔ kalmanRco A B C = reachableSubspace A B :=
  (Submodule.exists_isCompl_of_le (reachableUnobservable A B C)
    (reachableSubspace A B) inf_le_left).choose_spec.2.1

theorem kalmanRco_inf (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    reachableUnobservable A B C ⊓ kalmanRco A B C = ⊥ :=
  (Submodule.exists_isCompl_of_le (reachableUnobservable A B C)
    (reachableSubspace A B) inf_le_left).choose_spec.2.2

theorem kalmanNuo_le (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    kalmanNuo A B C ≤ unobservableSubspace C A :=
  (Submodule.exists_isCompl_of_le (reachableUnobservable A B C)
    (unobservableSubspace C A) inf_le_right).choose_spec.1

theorem kalmanNuo_sup (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    reachableUnobservable A B C ⊔ kalmanNuo A B C = unobservableSubspace C A :=
  (Submodule.exists_isCompl_of_le (reachableUnobservable A B C)
    (unobservableSubspace C A) inf_le_right).choose_spec.2.1

theorem kalmanNuo_inf (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    reachableUnobservable A B C ⊓ kalmanNuo A B C = ⊥ :=
  (Submodule.exists_isCompl_of_le (reachableUnobservable A B C)
    (unobservableSubspace C A) inf_le_right).choose_spec.2.2

theorem kalmanRuo_sup (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    (reachableSubspace A B ⊔ unobservableSubspace C A) ⊔ kalmanRuo A B C = ⊤ :=
  (Submodule.exists_isCompl_of_le
    (reachableSubspace A B ⊔ unobservableSubspace C A) ⊤ le_top).choose_spec.2.1

theorem kalmanRuo_inf (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    (reachableSubspace A B ⊔ unobservableSubspace C A) ⊓ kalmanRuo A B C = ⊥ :=
  (Submodule.exists_isCompl_of_le
    (reachableSubspace A B ⊔ unobservableSubspace C A) ⊤ le_top).choose_spec.2.2

/-- `W ⊔ Nuo = W ⊔ N`, since `N = I ⊔ Nuo` and `I ≤ W`. -/
theorem reachable_sup_kalmanNuo (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    reachableSubspace A B ⊔ kalmanNuo A B C =
      reachableSubspace A B ⊔ unobservableSubspace C A := by
  rw [← kalmanNuo_sup A B C]
  have hI : reachableSubspace A B ⊔ reachableUnobservable A B C = reachableSubspace A B :=
    sup_eq_left.mpr inf_le_left
  rw [← sup_assoc, hI]

/-- `W ⊓ Nuo = ⊥`, because `Nuo ≤ N` and `W ⊓ N = I` is disjoint from `Nuo`. -/
theorem reachable_inf_kalmanNuo (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    reachableSubspace A B ⊓ kalmanNuo A B C = ⊥ := by
  have hle : reachableSubspace A B ⊓ kalmanNuo A B C ≤
      reachableUnobservable A B C ⊓ kalmanNuo A B C :=
    le_inf (le_inf inf_le_left (le_trans inf_le_right (kalmanNuo_le A B C))) inf_le_right
  rw [kalmanNuo_inf A B C] at hle
  exact le_bot_iff.mp hle

end LinearMap

namespace LinearMap

variable {𝕜 X U Y : Type*}
variable [Field 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup Y] [Module 𝕜 Y]

/-- The two-block decomposition `W = I ⊕ Rco` of the reachable subspace. -/
noncomputable def kalmanEquivW (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    (reachableUnobservable A B C × kalmanRco A B C) ≃ₗ[𝕜] reachableSubspace A B :=
  Submodule.prodEquivOfIsComplOfLe _ _ _ (kalmanRco_sup A B C) (kalmanRco_inf A B C)

/-- The three-block decomposition `W ⊔ N = (I ⊕ Rco) ⊕ Nuo` after transporting
the `W = I ⊕ Rco` part. -/
noncomputable def kalmanEquivWNOuter (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (C : X →ₗ[𝕜] Y) :
    (reachableSubspace A B × kalmanNuo A B C) ≃ₗ[𝕜]
      reachableSupUnobservable A B C :=
  Submodule.prodEquivOfIsComplOfLe _ _ _
    (reachable_sup_kalmanNuo A B C) (reachable_inf_kalmanNuo A B C)

/-- The three-block decomposition `W ⊔ N = (I ⊕ Rco) ⊕ Nuo`. -/
noncomputable def kalmanEquivWN (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    ((reachableUnobservable A B C × kalmanRco A B C) × kalmanNuo A B C) ≃ₗ[𝕜]
      reachableSupUnobservable A B C :=
  LinearEquiv.trans
    ((kalmanEquivW A B C).prodCongr (LinearEquiv.refl 𝕜 (kalmanNuo A B C)))
    (kalmanEquivWNOuter A B C)

/-- The ambient splitting `X = (W ⊔ N) ⊕ Ruo`. -/
noncomputable def kalmanEquivOuter (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    (reachableSupUnobservable A B C × kalmanRuo A B C) ≃ₗ[𝕜] X :=
  Submodule.prodEquivOfIsCompl _ _
    (IsCompl.of_eq (kalmanRuo_inf A B C) (kalmanRuo_sup A B C))

/-- **The four-block state-space equivalence** of the Kalman decomposition,
with the four components ordered `(I, Rco, Nuo, Ruo)`:
`(((I × Rco) × Nuo) × Ruo) ≃ₗ[𝕜] X`. -/
noncomputable def kalmanEquiv (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    (((reachableUnobservable A B C × kalmanRco A B C) × kalmanNuo A B C) ×
      kalmanRuo A B C) ≃ₗ[𝕜] X :=
  LinearEquiv.trans
    ((kalmanEquivWN A B C).prodCongr (LinearEquiv.refl 𝕜 (kalmanRuo A B C)))
    (kalmanEquivOuter A B C)

/-! ### Components of the equivalence -/

/-- The four-block equivalence sends the component coordinates to their sum in `X`. -/
@[simp]
theorem kalmanEquiv_apply (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y)
    (i : reachableUnobservable A B C) (r : kalmanRco A B C)
    (n : kalmanNuo A B C) (s : kalmanRuo A B C) :
    kalmanEquiv A B C (((i, r), n), s) = ((i : X) + (r : X)) + (n : X) + (s : X) := rfl

/-- Splitting formula for `kalmanEquiv.symm` into the `W ⊔ N` part and the
`Ruo` part. -/
theorem kalmanEquiv_symm_apply (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y)
    (y : X) :
    (kalmanEquiv A B C).symm y =
      ((kalmanEquivWN A B C).symm ((kalmanEquivOuter A B C).symm y).1,
        ((kalmanEquivOuter A B C).symm y).2) := by
  rw [kalmanEquiv, LinearEquiv.symm_trans_apply, LinearEquiv.prodCongr_symm]
  rfl

/-- Splitting formula for `kalmanEquivWN.symm` into the `W` part and the `Nuo`
part. -/
theorem kalmanEquivWN_symm_apply (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y)
    (w : reachableSupUnobservable A B C) :
    (kalmanEquivWN A B C).symm w =
      ((kalmanEquivW A B C).symm ((kalmanEquivWNOuter A B C).symm w).1,
        ((kalmanEquivWNOuter A B C).symm w).2) := by
  rw [kalmanEquivWN, LinearEquiv.symm_trans_apply, LinearEquiv.prodCongr_symm]
  rfl

/-- The `Ruo`-component of `kalmanEquiv.symm y` vanishes exactly when `y` lies in
`W ⊔ N`. This is the block identity for the last row of the four-block form. -/
theorem kalmanEquiv_symm_snd_eq_zero (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y)
    {y : X} :
    ((kalmanEquiv A B C).symm y).2 = 0 ↔ y ∈ reachableSupUnobservable A B C := by
  rw [kalmanEquiv_symm_apply]
  rw [kalmanEquivOuter]
  exact Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero
    (reachableSupUnobservable A B C) (kalmanRuo A B C)
    (IsCompl.of_eq (kalmanRuo_inf A B C) (kalmanRuo_sup A B C))

/-- The `Nuo`-component of `kalmanEquiv.symm y` vanishes exactly when `y` lies in
`W` (for `y ∈ W ⊔ N`). This is the block identity for the third row. -/
theorem kalmanEquiv_symm_fst_snd_eq_zero (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (C : X →ₗ[𝕜] Y) {y : X}
    (hy : y ∈ reachableSupUnobservable A B C) :
    ((kalmanEquiv A B C).symm y).1.2 = 0 ↔ y ∈ reachableSubspace A B := by
  rw [kalmanEquiv_symm_apply]
  have houter : (kalmanEquivOuter A B C).symm y = (⟨y, hy⟩, 0) :=
    Submodule.prodEquivOfIsCompl_symm_apply_of_mem _ hy
  rw [houter, kalmanEquivWN_symm_apply]
  exact Submodule.prodEquivOfIsComplOfLe_symm_apply_snd_eq_zero _ _ _ _ _

/-- The `Rco`-component of `kalmanEquiv.symm y` vanishes exactly when `y` lies in
`I = W ⊓ N` (for `y ∈ W`). This is the block identity for the second row. -/
theorem kalmanEquiv_symm_fst_fst_snd_eq_zero (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (C : X →ₗ[𝕜] Y) {y : X} (hy : y ∈ reachableSubspace A B) :
    ((kalmanEquiv A B C).symm y).1.1.2 = 0 ↔ y ∈ reachableUnobservable A B C := by
  have hyWN : y ∈ reachableSupUnobservable A B C :=
    Submodule.mem_sup_left hy
  rw [kalmanEquiv_symm_apply]
  have houter : (kalmanEquivOuter A B C).symm y = (⟨y, hyWN⟩, 0) :=
    Submodule.prodEquivOfIsCompl_symm_apply_of_mem _ hyWN
  rw [houter, kalmanEquivWN_symm_apply]
  have hinner : (kalmanEquivWNOuter A B C).symm ⟨y, hyWN⟩ = (⟨y, hy⟩, 0) :=
    Submodule.prodEquivOfIsComplOfLe_symm_apply_of_mem _ _ _ _ _ hy
  rw [hinner]
  exact Submodule.prodEquivOfIsComplOfLe_symm_apply_snd_eq_zero _ _ _ _ _

end LinearMap

namespace LinearMap

variable {𝕜 X U Y : Type*}
variable [Field 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup Y] [Module 𝕜 Y]

/-! ### The zero blocks of `A`, `B` and `C`

The block `(row, column)` of a linear map with respect to the four-component
decomposition is obtained by restricting to the `column` component and
projecting to the `row` component. By the component characterisations above,
a component vanishes exactly when the image lies in the corresponding
invariant subspace. -/

/-- `I = W ⊓ N` is `A`-invariant, as the intersection of the two invariant
subspaces `W` and `N`. -/
theorem map_reachableUnobservable_le (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    Submodule.map A (reachableUnobservable A B C) ≤ reachableUnobservable A B C := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hW : A x ∈ reachableSubspace A B :=
    map_reachableSubspace_le A B (Submodule.mem_map.mpr ⟨x, hx.1, rfl⟩)
  have hN : A x ∈ unobservableSubspace C A :=
    map_unobservableSubspace_le C A (Submodule.mem_map.mpr ⟨x, hx.2, rfl⟩)
  exact ⟨hW, hN⟩

/-- **`A₂₁ = 0`.** On the first component `I`, the `Rco`-component of `A`
vanishes, because `I` is `A`-invariant. -/
theorem kalman_A_21 (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) {x : X}
    (hx : x ∈ reachableUnobservable A B C) :
    ((kalmanEquiv A B C).symm (A x)).1.1.2 = 0 := by
  have hAI : A x ∈ reachableUnobservable A B C :=
    map_reachableUnobservable_le A B C (Submodule.mem_map.mpr ⟨x, hx, rfl⟩)
  have hAW : A x ∈ reachableSubspace A B := (Submodule.mem_inf.mp hAI).1
  exact (kalmanEquiv_symm_fst_fst_snd_eq_zero A B C hAW).mpr hAI

/-- **`A₃₁ = 0`.** On the first component `I ⊆ W`, the `Nuo`-component of `A`
vanishes, because `W` is `A`-invariant. -/
theorem kalman_A_31 (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) {x : X}
    (hx : x ∈ reachableUnobservable A B C) :
    ((kalmanEquiv A B C).symm (A x)).1.2 = 0 := by
  have hxW : x ∈ reachableSubspace A B := (Submodule.mem_inf.mp hx).1
  have hAW : A x ∈ reachableSubspace A B :=
    map_reachableSubspace_le A B (Submodule.mem_map.mpr ⟨x, hxW, rfl⟩)
  exact (kalmanEquiv_symm_fst_snd_eq_zero A B C (Submodule.mem_sup_left hAW)).mpr hAW

/-- **`A₄₁ = 0`.** On the first component `I ⊆ W ⊆ W ⊔ N`, the `Ruo`-component
of `A` vanishes. -/
theorem kalman_A_41 (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) {x : X}
    (hx : x ∈ reachableUnobservable A B C) :
    ((kalmanEquiv A B C).symm (A x)).2 = 0 := by
  have hxW : x ∈ reachableSubspace A B := (Submodule.mem_inf.mp hx).1
  have hAW : A x ∈ reachableSubspace A B :=
    map_reachableSubspace_le A B (Submodule.mem_map.mpr ⟨x, hxW, rfl⟩)
  exact (kalmanEquiv_symm_snd_eq_zero A B C).mpr (Submodule.mem_sup_left hAW)

/-- **`A₃₂ = 0`.** On the second component `Rco ⊆ W`, the `Nuo`-component of
`A` vanishes, because `W` is `A`-invariant. -/
theorem kalman_A_32 (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) {x : X}
    (hx : x ∈ kalmanRco A B C) :
    ((kalmanEquiv A B C).symm (A x)).1.2 = 0 := by
  have hxW : x ∈ reachableSubspace A B := kalmanRco_le A B C hx
  have hAW : A x ∈ reachableSubspace A B :=
    map_reachableSubspace_le A B (Submodule.mem_map.mpr ⟨x, hxW, rfl⟩)
  exact (kalmanEquiv_symm_fst_snd_eq_zero A B C (Submodule.mem_sup_left hAW)).mpr hAW

/-- **`A₄₂ = 0`.** On the second component `Rco ⊆ W`, the `Ruo`-component of
`A` vanishes. -/
theorem kalman_A_42 (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) {x : X}
    (hx : x ∈ kalmanRco A B C) :
    ((kalmanEquiv A B C).symm (A x)).2 = 0 := by
  have hxW : x ∈ reachableSubspace A B := kalmanRco_le A B C hx
  have hAW : A x ∈ reachableSubspace A B :=
    map_reachableSubspace_le A B (Submodule.mem_map.mpr ⟨x, hxW, rfl⟩)
  exact (kalmanEquiv_symm_snd_eq_zero A B C).mpr (Submodule.mem_sup_left hAW)

/-- For a state in the unobservable subspace `N`, the `Rco`-component of
`kalmanEquiv.symm y` vanishes. This is the key additional case needed for the
third column, where `A` maps `Nuo` into `N` rather than into `W`. -/
theorem kalmanEquiv_symm_fst_fst_snd_eq_zero_of_mem_unobservable
    (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) {y : X}
    (hy : y ∈ unobservableSubspace C A) :
    ((kalmanEquiv A B C).symm y).1.1.2 = 0 := by
  have hyWN : y ∈ reachableSupUnobservable A B C := Submodule.mem_sup_right hy
  rw [kalmanEquiv_symm_apply]
  have houter : (kalmanEquivOuter A B C).symm y = (⟨y, hyWN⟩, 0) :=
    Submodule.prodEquivOfIsCompl_symm_apply_of_mem _ hyWN
  rw [houter, kalmanEquivWN_symm_apply]
  set w := (kalmanEquivWNOuter A B C).symm ⟨y, hyWN⟩ with hw
  have hwI : (w.1 : X) ∈ reachableUnobservable A B C := by
    refine ⟨w.1.2, ?_⟩
    have hadd : (w.1 : X) + (w.2 : X) = y := by
      have h := Submodule.prodEquivOfIsComplOfLe_symm_apply_add
        (reachableSubspace A B) (kalmanNuo A B C) (reachableSupUnobservable A B C)
        (reachable_sup_kalmanNuo A B C) (reachable_inf_kalmanNuo A B C) ⟨y, hyWN⟩
      simpa [w, kalmanEquivWNOuter] using h
    have hw2N : (w.2 : X) ∈ unobservableSubspace C A := kalmanNuo_le A B C w.2.2
    have : (w.1 : X) = y - (w.2 : X) := by
      rw [← hadd]
      abel
    rw [this]
    exact Submodule.sub_mem _ hy hw2N
  exact (Submodule.prodEquivOfIsComplOfLe_symm_apply_snd_eq_zero
    (reachableUnobservable A B C) (kalmanRco A B C) (reachableSubspace A B)
    (kalmanRco_sup A B C) (kalmanRco_inf A B C)).mpr hwI

/-- **`A₂₃ = 0`.** On the third component `Nuo ⊆ N`, the `Rco`-component of `A`
vanishes, because `A` maps `N` into `N` and `Rco ⊓ N = ⊥`. -/
theorem kalman_A_23 (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) {x : X}
    (hx : x ∈ kalmanNuo A B C) :
    ((kalmanEquiv A B C).symm (A x)).1.1.2 = 0 := by
  have hN : A x ∈ unobservableSubspace C A :=
    map_unobservableSubspace_le C A (Submodule.mem_map.mpr ⟨x, kalmanNuo_le A B C hx, rfl⟩)
  exact kalmanEquiv_symm_fst_fst_snd_eq_zero_of_mem_unobservable A B C hN

/-- **`A₄₃ = 0`.** On the third component `Nuo ⊆ N ⊆ W ⊔ N`, the `Ruo`-component
of `A` vanishes. -/
theorem kalman_A_43 (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) {x : X}
    (hx : x ∈ kalmanNuo A B C) :
    ((kalmanEquiv A B C).symm (A x)).2 = 0 := by
  have hN : A x ∈ unobservableSubspace C A :=
    map_unobservableSubspace_le C A (Submodule.mem_map.mpr ⟨x, kalmanNuo_le A B C hx, rfl⟩)
  exact (kalmanEquiv_symm_snd_eq_zero A B C).mpr (Submodule.mem_sup_right hN)

/-- **`B₃ = 0`.** Since `im B ⊆ W`, the `Nuo`-component of `B u` vanishes. -/
theorem kalman_B_3 (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) (u : U) :
    ((kalmanEquiv A B C).symm (B u)).1.2 = 0 := by
  have hBW : B u ∈ reachableSubspace A B := range_le_reachableSubspace A B ⟨u, rfl⟩
  exact (kalmanEquiv_symm_fst_snd_eq_zero A B C (Submodule.mem_sup_left hBW)).mpr hBW

/-- **`B₄ = 0`.** Since `im B ⊆ W ⊆ W ⊔ N`, the `Ruo`-component of `B u`
vanishes. -/
theorem kalman_B_4 (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) (u : U) :
    ((kalmanEquiv A B C).symm (B u)).2 = 0 :=
  (kalmanEquiv_symm_snd_eq_zero A B C).mpr
    (Submodule.mem_sup_left (range_le_reachableSubspace A B ⟨u, rfl⟩))

/-- **`C₁ = 0`.** The readout vanishes on the first component `I ⊆ N`. -/
theorem kalman_C_1 (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    C.comp (reachableUnobservable A B C).subtype = 0 := by
  ext i
  exact C_eq_zero_of_mem_unobservableSubspace (C := C) (A := A)
    (Submodule.mem_inf.mp i.2).2

/-- **`C₃ = 0`.** The readout vanishes on the third component `Nuo ⊆ N`. -/
theorem kalman_C_3 (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    C.comp (kalmanNuo A B C).subtype = 0 := by
  ext n
  exact C_eq_zero_of_mem_unobservableSubspace (C := C) (A := A) (kalmanNuo_le A B C n.2)

end LinearMap

namespace LinearMap

variable {𝕜 X U Y : Type*}
variable [Field 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup Y] [Module 𝕜 Y]

/-! ### Quotients of controllable pairs -/

/-- **Controllability survives taking a quotient by an invariant subspace.**
If `(A, B)` is controllable and `V` is `A`-invariant, then the induced pair on
`X ⧸ V` is controllable. -/
theorem isControllable_quotient (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (hAB : IsControllable A B) {V : Submodule 𝕜 X} (hV : Submodule.map A V ≤ V) :
    IsControllable (V.mapQ V A ((Submodule.map_le_iff_le_comap).mp hV))
      (V.mkQ.comp B) := by
  rw [isControllable_iff, eq_top_iff]
  intro z _
  let S : Submodule 𝕜 X :=
    Submodule.comap V.mkQ (reachableSubspace (V.mapQ V A ((Submodule.map_le_iff_le_comap).mp hV))
      (V.mkQ.comp B))
  have hB : LinearMap.range B ≤ S := by
    rintro y ⟨u, rfl⟩
    exact range_le_reachableSubspace _ _ (LinearMap.mem_range_self _ u)
  have hA : Submodule.map A S ≤ S := by
    rintro y ⟨x, hx, rfl⟩
    change V.mkQ (A x) ∈ reachableSubspace
      (V.mapQ V A ((Submodule.map_le_iff_le_comap).mp hV)) (V.mkQ.comp B)
    have hmap : (V.mapQ V A ((Submodule.map_le_iff_le_comap).mp hV)) (V.mkQ x) =
        V.mkQ (A x) := by
      rw [Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.mkQ_apply]
    rw [← hmap]
    exact map_reachableSubspace_le _ _ ⟨V.mkQ x, hx, rfl⟩
  have htop : reachableSubspace A B ≤ S := reachableSubspace_le A B hB hA
  rw [hAB] at htop
  obtain ⟨w, rfl⟩ := V.mkQ_surjective z
  exact htop trivial

end LinearMap

namespace LinearMap

variable {𝕜 X U Y : Type*}
variable [Field 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup Y] [Module 𝕜 Y]

/-! ### The controllable and observable realization -/

/-- The system restricted to the reachable subspace `W`. Its state map is the
restriction of `A`, its input map is `B` corestricted to `W`, and its readout is
`C` restricted to `W`; the feedthrough `D` is unchanged. -/
noncomputable def reachableRestriction (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (C : X →ₗ[𝕜] Y) (D : U →ₗ[𝕜] Y) :
    LinearSystem 𝕜 (reachableSubspace A B) U Y where
  A := reachableRestrictionA A B
  B := reachableRestrictionB A B
  C := C.comp (reachableSubspace A B).subtype
  D := D

/-- The unobservable subspace of the restricted system, pulled back to `W`; this
is the intersection `W ⊓ N` viewed as a subspace of `W`. -/
noncomputable def reachableIntersection (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (C : X →ₗ[𝕜] Y) : Submodule 𝕜 (reachableSubspace A B) :=
  Submodule.comap (reachableSubspace A B).subtype (reachableUnobservable A B C)

/-- The `k`-th power of the restricted state map, on the level of `X`, is the
`k`-th power of `A`. -/
theorem reachableRestrictionA_pow_coe (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (k : ℕ)
    (x : reachableSubspace A B) :
    ((reachableRestrictionA A B ^ k) x : X) = (A ^ k) x := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 : ((reachableRestrictionA A B ^ (k + 1)) x : X) =
          A ((reachableRestrictionA A B ^ k) x) := by
        rw [Module.End.iterate_succ', LinearMap.comp_apply]
        rfl
      rw [h1, ih, Module.End.iterate_succ', LinearMap.comp_apply]

/-- **The unobservable subspace of the restricted system is `W ⊓ N`.** -/
theorem unobservableSubspace_reachableRestriction (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (C : X →ₗ[𝕜] Y) (D : U →ₗ[𝕜] Y) :
    unobservableSubspace (reachableRestriction A B C D).C (reachableRestriction A B C D).A =
      reachableIntersection A B C := by
  ext x
  rw [reachableIntersection, Submodule.mem_comap, reachableUnobservable, Submodule.mem_inf,
    mem_unobservableSubspace, mem_unobservableSubspace]
  constructor
  · intro h
    refine ⟨x.2, fun k ↦ ?_⟩
    have := h k
    simpa only [reachableRestriction, LinearMap.comp_apply, Submodule.subtype_apply,
      reachableRestrictionA_pow_coe] using this
  · rintro ⟨_, hN⟩ k
    have := hN k
    simpa only [reachableRestriction, LinearMap.comp_apply, Submodule.subtype_apply,
      reachableRestrictionA_pow_coe] using this

/-- `W ⊓ N` is invariant under the restricted state map. -/
theorem map_reachableIntersection_le (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) :
    Submodule.map (reachableRestrictionA A B) (reachableIntersection A B C) ≤
      reachableIntersection A B C := by
  rw [← unobservableSubspace_reachableRestriction A B C 0]
  exact map_unobservableSubspace_le _ _

/-- **The controllable and observable realization.** Restrict the system to the
reachable subspace `W` and then quotient by `I = W ⊓ N`. The feedthrough `D` is
preserved. -/
noncomputable def controllableObservableRealization (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (C : X →ₗ[𝕜] Y) (D : U →ₗ[𝕜] Y) :
    LinearSystem 𝕜 (reachableSubspace A B ⧸ reachableIntersection A B C) U Y where
  A := (reachableIntersection A B C).mapQ (reachableIntersection A B C)
      (reachableRestrictionA A B)
      ((Submodule.map_le_iff_le_comap).mp (map_reachableIntersection_le A B C))
  B := (reachableIntersection A B C).mkQ.comp (reachableRestrictionB A B)
  C := (reachableIntersection A B C).liftQ (C.comp (reachableSubspace A B).subtype)
      (by
        intro x hx
        rw [reachableIntersection, Submodule.mem_comap] at hx
        exact C_eq_zero_of_mem_unobservableSubspace (C := C) (A := A)
          (Submodule.mem_inf.mp hx).2)
  D := D

/-- The feedthrough of the controllable and observable realization is the
original `D`. -/
@[simp]
theorem controllableObservableRealization_D (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (C : X →ₗ[𝕜] Y) (D : U →ₗ[𝕜] Y) :
    (controllableObservableRealization A B C D).D = D := rfl

/-- **The controllable and observable realization is controllable.** -/
theorem isControllable_controllableObservableRealization (A : X →ₗ[𝕜] X)
    (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) (D : U →ₗ[𝕜] Y) :
    IsControllable (controllableObservableRealization A B C D).A
      (controllableObservableRealization A B C D).B :=
  isControllable_quotient (reachableRestrictionA A B) (reachableRestrictionB A B)
    (isControllable_reachableRestriction A B) (map_reachableIntersection_le A B C)

/-- The state map of the realization commutes with the quotient projection. -/
theorem controllableObservableRealization_A_mkQ (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (C : X →ₗ[𝕜] Y) (D : U →ₗ[𝕜] Y) (y : reachableSubspace A B) :
    (controllableObservableRealization A B C D).A
        ((reachableIntersection A B C).mkQ y) =
      (reachableIntersection A B C).mkQ ((reachableRestrictionA A B) y) := by
  simp only [controllableObservableRealization, Submodule.mkQ_apply, Submodule.mapQ_apply]

/-- The powers of the state map of the realization commute with the quotient
projection. -/
theorem controllableObservableRealization_A_pow_mkQ (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (C : X →ₗ[𝕜] Y) (D : U →ₗ[𝕜] Y) (k : ℕ) (x : reachableSubspace A B) :
    ((controllableObservableRealization A B C D).A ^ k)
        ((reachableIntersection A B C).mkQ x) =
      (reachableIntersection A B C).mkQ ((reachableRestrictionA A B ^ k) x) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Module.End.iterate_succ', LinearMap.comp_apply, ih,
        controllableObservableRealization_A_mkQ, Module.End.iterate_succ',
        LinearMap.comp_apply]

/-- The readout of the realization commutes with the quotient projection. -/
theorem controllableObservableRealization_C_mkQ (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (C : X →ₗ[𝕜] Y) (D : U →ₗ[𝕜] Y) (x : reachableSubspace A B) :
    (controllableObservableRealization A B C D).C
        ((reachableIntersection A B C).mkQ x) = C (x : X) := by
  simp only [controllableObservableRealization, Submodule.mkQ_apply,
    Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.subtype_apply]

/-- **The controllable and observable realization is observable.** The quotient
by `I = W ⊓ N` is exactly the quotient of the restricted system by its
unobservable subspace. -/
theorem isObservable_controllableObservableRealization (A : X →ₗ[𝕜] X)
    (B : U →ₗ[𝕜] X) (C : X →ₗ[𝕜] Y) (D : U →ₗ[𝕜] Y) :
    IsObservable (controllableObservableRealization A B C D).C
      (controllableObservableRealization A B C D).A := by
  rw [isObservable_iff, Submodule.eq_bot_iff]
  intro z hz
  rw [mem_unobservableSubspace] at hz
  obtain ⟨x, rfl⟩ := (reachableIntersection A B C).mkQ_surjective z
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, reachableIntersection,
    Submodule.mem_comap, reachableUnobservable, Submodule.mem_inf]
  refine ⟨x.2, ?_⟩
  rw [mem_unobservableSubspace]
  intro k
  have hk := hz k
  rw [controllableObservableRealization_A_pow_mkQ, controllableObservableRealization_C_mkQ] at hk
  change C ((A ^ k) (x : X)) = 0
  simpa only [reachableRestrictionA_pow_coe] using hk

/-- The reduced system preserves every algebraic Markov parameter `C A^k B`.
This is an algebraic behavior bridge; continuous-time input/output equivalence is separate. -/
theorem controllableObservableRealization_markov (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (C : X →ₗ[𝕜] Y) (D : U →ₗ[𝕜] Y) (k : ℕ) :
    (controllableObservableRealization A B C D).C.comp
        (((controllableObservableRealization A B C D).A ^ k).comp
          (controllableObservableRealization A B C D).B) =
      C.comp ((A ^ k).comp B) := by
  ext u
  change (controllableObservableRealization A B C D).C
      (((controllableObservableRealization A B C D).A ^ k)
        ((reachableIntersection A B C).mkQ ((reachableRestrictionB A B) u))) =
    C ((A ^ k) (B u))
  rw [controllableObservableRealization_A_pow_mkQ,
    controllableObservableRealization_C_mkQ, reachableRestrictionA_pow_coe]
  rfl

end LinearMap
