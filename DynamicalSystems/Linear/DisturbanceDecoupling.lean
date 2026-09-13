/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.ConditionedInvariant
public import DynamicalSystems.Linear.Reachability

/-! # Disturbance decoupling: algebraic foundations

This file begins the disturbance-decoupling chapter of Trentelman, Stoorvogel
and Hautus, *Control Theory for Linear Systems*. It records the exact algebraic
predicates and their bridges to the accepted controlled- and conditioned-invariant
subspace API of `DynamicalSystems.Linear.ControlledInvariant` and
`DynamicalSystems.Linear.ConditionedInvariant`.

## The channel and its Markov parameters

A *disturbance channel* consists of a state map `A : X →ₗ[𝕜] X`, a disturbance
input map `E : W →ₗ[𝕜] X` and an output map `H : X →ₗ[𝕜] Z`, modelling

```
x'(t) = A x(t) + E d(t),
z(t)  = H x(t).
```

Its `k`-th **impulse-response coefficient** (Markov parameter) is the composite

`LinearMap.disturbanceResponse A E H k = H ∘ A ^ k ∘ E : W →ₗ[𝕜] Z`.

The channel is **disturbance decoupled** when every one of these coefficients
vanishes, `LinearMap.IsDisturbanceDecoupled A E H`. Over the reals and in finite
dimension this is exactly the vanishing of the impulse response `t ↦ H e^{tA} E`
of Trentelman–Stoorvogel–Hautus, equation (4.4), whose derivatives at `0` are
precisely the Markov parameters `H A ^ k E`; the equivalence is proved below as
`LinearMap.isDisturbanceDecoupled_iff_forall_expFlow`. The convolution form of
input-independence is proved below; the transfer-function form remains a separate
obligation, documented in the Deferred obligations section below and not claimed
here.

## Bridges to invariant subspaces

The algebraic content of the chapter is that decoupling is an invariant-subspace
existence statement:

* `LinearMap.isDisturbanceDecoupled_iff_reachableSubspace_le_ker`: the channel is
  decoupled if and only if `⟨A | im E⟩ ≤ ker H`.
* `LinearMap.isDisturbanceDecoupled_iff_exists_invariant`: the channel is
  decoupled if and only if there is an `A`-invariant subspace `V` with
  `im E ≤ V ≤ ker H`. This is Theorem 4.6, in the *least*/*greatest* form: the
  reachable subspace `⟨A | im E⟩` is the least admissible `V` and the
  unobservable subspace `⟨ker H | A⟩` is the greatest.
* `LinearMap.isStateFeedbackDisturbanceDecoupled_iff_exists_controlledInvariant`:
  disturbance decoupling by static state feedback (Definition 4.7 and
  Theorem 4.8) holds if and only if there is a *controlled invariant* `V` with
  `im E ≤ V ≤ ker H`. Both directions are proved.
* `LinearMap.isStateFeedbackDisturbanceDecoupled_iff_range_le_controlledInvariantSubspace`:
  in finite dimension this is the compact criterion `im E ≤ V*(ker H)` of
  Corollary 4.9.

## The conditioned-invariant bridge

The static state-feedback condition above is the `(A, B)`-half of the
measurement-feedback theory of Chapter 6. A `(C, A, B)`-pair
(`LinearMap.IsCABPair`) is a pair of subspaces `S ≤ V` with `S` conditioned
invariant and `V` controlled invariant; it is *between* `im E` and `ker H`
(`LinearMap.IsCABPairBetween`) when `im E ≤ S` and `V ≤ ker H`. The algebraic
core of Corollary 6.7 is

`LinearMap.exists_isCABPairBetween_iff`:
there exists a `(C, A, B)`-pair between `im E` and `ker H` if and only if
`S*(im E) ≤ V*(ker H)`.

The passage from such a pair to an actual dynamic measurement-feedback
controller (Theorem 6.4) is formalised in the separate module
`DynamicalSystems.Linear.DynamicFeedback`, as
`LinearSystem.exists_dynamicController_of_isCABPairBetween` and the closed-loop
decoupling theorem
`LinearSystem.isClosedLoopDisturbanceDecoupled_of_isCABPairBetween`.

## The analytic impulse-response bridge

Over the reals and in finite dimension, `LinearMap.isDisturbanceDecoupled_iff_forall_expFlow`
identifies the algebraic predicate with the identical vanishing of the analytic
impulse response `t ↦ H e^{tA} E`, using the accepted trajectory/unobservability
bridges of `DynamicalSystems.Linear.Reachability`. This is the sense in which the
Markov parameters are the derivatives at zero of the impulse response.

## The variation-of-constants / convolution bridge

The forced output of the channel is the variation-of-constants trajectory of the
associated `LinearSystem` (`LinearMap.forcedOutput`), with the zero-initial-state
part isolated as `LinearMap.disturbanceContribution`. Its explicit convolution
form is `LinearMap.forcedOutput_eq_convolution`:

`z(t) = H (e^{(t - t₀)A} x₀) + ∫_{t₀}^{t} H (e^{(t - s)A} E) d(s) ds`,

with impulse response `LinearMap.disturbanceImpulseResponse`, a Bochner integral
in the (complete) output space. Exact decoupling makes the convolution term vanish
for every locally integrable disturbance
(`LinearMap.isDisturbanceDecoupled_disturbanceContribution_eq_zero`), hence makes
the output independent of the admissible disturbance
(`LinearMap.isDisturbanceDecoupled_forcedOutput_eq_of_input`). Conversely, if the
disturbance contribution vanishes for every locally integrable disturbance then
the channel is decoupled; the proof tests the hypothesis on rectangular pulses and
uses the fundamental theorem of calculus to recover the impulse response. The two
directions are combined in
`LinearMap.isDisturbanceDecoupled_iff_forall_disturbanceContribution_eq_zero`.

The convolution bridge and the two implications above are stated for a **complete**
output space `Z`: completeness is the Bochner-integral regularity hypothesis needed
to commute the output map `H` with the integral
(`ContinuousLinearMap.intervalIntegral_comp_comm`). Finite-dimensional output
spaces, the intended control-theoretic case, are complete. The converse direction
`LinearMap.isDisturbanceDecoupled_of_forall_disturbanceContribution_eq_zero` does
not use the convolution bridge and therefore does not need completeness.

## Worked examples

The double integrator `A (x, y) = (y, 0)` exhibits both outcomes:
`LinearMap.isDisturbanceDecoupled_doubleIntegrator_position` proves that a
position disturbance is invisible to a velocity readout, while
`LinearMap.not_isDisturbanceDecoupled_doubleIntegrator_velocity` proves that a
velocity disturbance is seen by the position readout. These are non-vacuity
witnesses for the definitions.

## Deferred obligations

The following are deliberately **not** claimed here and remain the next
milestones:

* the transfer-function form `H (s I - A)⁻¹ E = 0`. The convolution form of
  input-independence is proved here, as the impulse response `K(t) = H e^{tA} E`
  is the Laplace kernel whose transform is the transfer function, but no
  unproved transfer-function claim is made here;
* the converse extraction of a `(C, A, B)`-pair from a decoupled closed loop
  (Trentelman–Stoorvogel–Hautus, Theorem 6.2 and the forward half of
  Theorem 6.6). The synthesis direction (Theorem 6.4) is proved in
  `DynamicalSystems.Linear.DynamicFeedback`;
* a measurement disturbance channel `F : D →ₗ[𝕜] Y` in the readout; only the
  state disturbance `E` is modelled here;
* the spectrum factorization of the extended system map and the internal and
  external stabilization results of Sections 6.3–6.4 and 4.7–4.8.

## Main definitions

* `LinearMap.disturbanceResponse`
* `LinearMap.IsDisturbanceDecoupled`, `LinearMap.IsStateFeedbackDisturbanceDecoupled`
* `LinearMap.IsCABPair`, `LinearMap.IsCABPairBetween`
* `LinearMap.disturbanceSystem`
* `LinearMap.disturbanceImpulseResponse`, `LinearMap.disturbanceContribution`,
  `LinearMap.forcedOutput`

## Main theorems

* `LinearMap.isDisturbanceDecoupled_iff_reachableSubspace_le_ker`
* `LinearMap.isDisturbanceDecoupled_iff_range_le_unobservableSubspace`
* `LinearMap.isDisturbanceDecoupled_iff_exists_invariant`
* `LinearMap.disturbanceResponse_changeState`, `LinearMap.isDisturbanceDecoupled_changeState_iff`
* `LinearMap.isStateFeedbackDisturbanceDecoupled_iff_exists_controlledInvariant`
* `LinearMap.isStateFeedbackDisturbanceDecoupled_iff_range_le_controlledInvariantSubspace`
* `LinearMap.exists_isCABPairBetween_iff`
* `LinearMap.isDisturbanceDecoupled_iff_forall_expFlow`
* `LinearMap.forcedOutput_eq_convolution`
* `LinearMap.isDisturbanceDecoupled_disturbanceContribution_eq_zero`
* `LinearMap.isDisturbanceDecoupled_forcedOutput_eq_of_input`
* `LinearMap.isDisturbanceDecoupled_iff_forall_disturbanceContribution_eq_zero`

## References

* H. L. Trentelman, A. A. Stoorvogel, M. Hautus, *Control Theory for Linear
  Systems*, Springer, 2001, Section 4.2 (equations (4.3)–(4.4), Theorem 4.6,
  Definition 4.7, Theorem 4.8, Corollary 4.9) and Section 6.1 (Definition 6.1,
  Corollary 6.7).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Interval Topology

namespace LinearMap

variable {𝕜 X U Y W Z : Type*}
variable [Field 𝕜]
variable [AddCommGroup X] [Module 𝕜 X]
variable [AddCommGroup U] [Module 𝕜 U]
variable [AddCommGroup Y] [Module 𝕜 Y]
variable [AddCommGroup W] [Module 𝕜 W]
variable [AddCommGroup Z] [Module 𝕜 Z]

/-! ## The disturbance channel and its response coefficients -/

/-- The `k`-th coefficient of the disturbance-to-output impulse response, i.e.
the Markov parameter `H A ^ k E : W →ₗ[𝕜] Z` of the channel
`x' = A x + E d`, `z = H x`.

These are the derivatives at `0` of the impulse response `t ↦ H e^{tA} E` of
Trentelman–Stoorvogel–Hautus, equation (4.4). -/
def disturbanceResponse (A : X →ₗ[𝕜] X) (E : W →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z)
    (k : ℕ) : W →ₗ[𝕜] Z :=
  H.comp ((A ^ k).comp E)

/-- Unfolding lemma for `disturbanceResponse`. -/
theorem disturbanceResponse_apply (A : X →ₗ[𝕜] X) (E : W →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z)
    (k : ℕ) (w : W) : disturbanceResponse A E H k w = H ((A ^ k) (E w)) := rfl

/-- The zeroth coefficient is the static gain `H E`. -/
@[simp]
theorem disturbanceResponse_zero (A : X →ₗ[𝕜] X) (E : W →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z) :
    disturbanceResponse A E H 0 = H.comp E := by
  ext w
  simp [disturbanceResponse]

/-- The coefficients satisfy `T (k + 1) = T k` with a state map inserted on the
left, i.e. `H A^{k+1} E = (H A) A^k E`. -/
theorem disturbanceResponse_succ (A : X →ₗ[𝕜] X) (E : W →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z)
    (k : ℕ) :
    disturbanceResponse A E H (k + 1) = (H.comp A).comp ((A ^ k).comp E) := by
  simp only [disturbanceResponse, pow_succ', Module.End.mul_eq_comp, LinearMap.comp_assoc]

/-- A channel is **disturbance decoupled** when all of its impulse-response
coefficients vanish, i.e. `H A ^ k E = 0` for every `k : ℕ`.

This is the algebraic form of `T = 0` in
Trentelman–Stoorvogel–Hautus, Section 4.2. Its equivalence with the vanishing of
the analytic impulse response `t ↦ H e^{tA} E` over the reals in finite dimension
is `LinearMap.isDisturbanceDecoupled_iff_forall_expFlow`; its equivalence with
zero disturbance contribution for every locally integrable disturbance is
`LinearMap.isDisturbanceDecoupled_iff_forall_disturbanceContribution_eq_zero`,
which yields input-independence via
`LinearMap.isDisturbanceDecoupled_forcedOutput_eq_of_input`.
The transfer-function form `H (sI - A)⁻¹ E = 0` remains a separate obligation,
stated in the Deferred obligations section. -/
def IsDisturbanceDecoupled (A : X →ₗ[𝕜] X) (E : W →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z) : Prop :=
  ∀ k : ℕ, disturbanceResponse A E H k = 0

/-- Unfolding lemma for `IsDisturbanceDecoupled`. -/
theorem isDisturbanceDecoupled_iff (A : X →ₗ[𝕜] X) (E : W →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z) :
    IsDisturbanceDecoupled A E H ↔
      ∀ k : ℕ, disturbanceResponse A E H k = 0 := Iff.rfl

/-- Pointwise form of decoupling: `H A ^ k E d = 0` for every `k` and every
disturbance value `d`. -/
theorem isDisturbanceDecoupled_iff_forall (A : X →ₗ[𝕜] X) (E : W →ₗ[𝕜] X)
    (H : X →ₗ[𝕜] Z) :
    IsDisturbanceDecoupled A E H ↔ ∀ k : ℕ, ∀ d : W, H ((A ^ k) (E d)) = 0 := by
  simp only [IsDisturbanceDecoupled, disturbanceResponse, LinearMap.ext_iff,
    LinearMap.comp_apply, LinearMap.zero_apply]

/-! ## Bridges to the reachable and unobservable subspaces -/

/-- **Decoupling means the disturbance reachable subspace is unobservable.**
The channel is disturbance decoupled if and only if the reachable subspace of the
pair `(A, E)` is contained in the kernel of the output map `H`.

Source: Trentelman–Stoorvogel–Hautus, Theorem 4.6, together with the extremal
characterisation of the reachable subspace (Corollary 3.3). -/
theorem isDisturbanceDecoupled_iff_reachableSubspace_le_ker
    (A : X →ₗ[𝕜] X) (E : W →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z) :
    IsDisturbanceDecoupled A E H ↔ reachableSubspace A E ≤ ker H := by
  rw [reachableSubspace, iSup_le_iff]
  constructor
  · intro h k
    rw [range_le_ker_iff]
    exact h k
  · intro h k
    change H.comp ((A ^ k).comp E) = 0
    rw [← range_le_ker_iff]
    exact h k

/-- **Decoupling means the disturbance enters the unobservable subspace.** The
channel is disturbance decoupled if and only if `im E` is contained in the
unobservable subspace of the pair `(H, A)`.

Source: Trentelman–Stoorvogel–Hautus, Theorem 4.6, via the extremal
characterisation of the unobservable subspace. -/
theorem isDisturbanceDecoupled_iff_range_le_unobservableSubspace
    (A : X →ₗ[𝕜] X) (E : W →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z) :
    IsDisturbanceDecoupled A E H ↔ range E ≤ unobservableSubspace H A := by
  rw [unobservableSubspace]
  constructor
  · intro h
    refine le_iInf fun k => ?_
    rw [range_le_ker_iff]
    exact h k
  · intro h k
    have hk : range E ≤ ker (H.comp (A ^ k)) :=
      le_trans h (iInf_le (fun k => ker (H.comp (A ^ k))) k)
    rw [range_le_ker_iff] at hk
    exact hk

/-! ## The invariant-subspace characterisation (Theorem 4.6) -/

/-- **Theorem 4.6.** The channel is disturbance decoupled if and only if there is
an `A`-invariant subspace `V` sandwiched between the disturbance image and the
output kernel, `im E ≤ V ≤ ker H`.

The witness `V := reachableSubspace A E` is the least such subspace and the
witness `V := unobservableSubspace H A` is the greatest; see
`reachableSubspace_le_of_invariant_le_ker`. -/
theorem isDisturbanceDecoupled_iff_exists_invariant
    (A : X →ₗ[𝕜] X) (E : W →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z) :
    IsDisturbanceDecoupled A E H ↔
      ∃ V : Submodule 𝕜 X, range E ≤ V ∧ V ≤ ker H ∧ Submodule.map A V ≤ V := by
  constructor
  · intro h
    exact ⟨reachableSubspace A E, range_le_reachableSubspace A E,
      (isDisturbanceDecoupled_iff_reachableSubspace_le_ker A E H).mp h,
      map_reachableSubspace_le A E⟩
  · rintro ⟨V, hE, hH, hA⟩
    exact (isDisturbanceDecoupled_iff_reachableSubspace_le_ker A E H).mpr
      (le_trans (reachableSubspace_le A E hE hA) hH)

/-- Any `A`-invariant subspace `V` sandwiched between `im E` and `ker H`
contains the reachable subspace `⟨A | im E⟩` and is contained in the
unobservable subspace `⟨ker H | A⟩`. This is the sandwich that makes
`reachableSubspace A E` the least and `unobservableSubspace H A` the greatest
invariant witness of Theorem 4.6. -/
theorem reachableSubspace_le_of_invariant_le_ker
    {A : X →ₗ[𝕜] X} {E : W →ₗ[𝕜] X} {H : X →ₗ[𝕜] Z} {V : Submodule 𝕜 X}
    (hE : range E ≤ V) (hH : V ≤ ker H) (hA : Submodule.map A V ≤ V) :
    reachableSubspace A E ≤ V ∧ V ≤ unobservableSubspace H A :=
  ⟨reachableSubspace_le A E hE hA, le_unobservableSubspace H A hH hA⟩

/-- **The greatest invariant witness.** `im E` is contained in the unobservable
subspace `⟨ker H | A⟩` exactly when the channel is decoupled; that subspace is
`A`-invariant and contained in `ker H`. Since every `A`-invariant witness inside
`ker H` is contained in it, this is the greatest admissible witness of
Theorem 4.6. -/
theorem isDisturbanceDecoupled_iff_range_le_unobservableSubspace'
    (A : X →ₗ[𝕜] X) (E : W →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z) :
    IsDisturbanceDecoupled A E H ↔
      range E ≤ unobservableSubspace H A ∧
        Submodule.map A (unobservableSubspace H A) ≤ unobservableSubspace H A ∧
        unobservableSubspace H A ≤ ker H := by
  rw [isDisturbanceDecoupled_iff_range_le_unobservableSubspace]
  exact ⟨fun h => ⟨h, map_unobservableSubspace_le H A, unobservableSubspace_le_ker H A⟩,
    fun h => h.1⟩

/-- **A sufficient condition.** If the state map kills the disturbance image,
`A (im E) = 0`, and the output map kills it as well, `im E ≤ ker H`, then the
channel is decoupled. This is the simplest non-vacuous decoupling criterion and
is used for the double-integrator example below. -/
theorem isDisturbanceDecoupled_of_map_range_eq_bot
    (A : X →ₗ[𝕜] X) (E : W →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z)
    (hAE : Submodule.map A (range E) = ⊥) (hHE : range E ≤ ker H) :
    IsDisturbanceDecoupled A E H := by
  intro k
  ext d
  cases k with
  | zero => simpa using mem_ker.mp (hHE ⟨d, rfl⟩)
  | succ n =>
    have h0 : A (E d) = 0 := by
      have : A (E d) ∈ Submodule.map A (range E) := ⟨E d, ⟨d, rfl⟩, rfl⟩
      rwa [hAE] at this
    have hk : (A ^ (n + 1)) (E d) = 0 := by
      rw [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply, h0, map_zero]
    rw [disturbanceResponse_apply, hk, map_zero, LinearMap.zero_apply]

/-! ## Coordinate invariance of the response

The Markov parameters are the matrix entries of the channel in a chosen basis, so
they are equivariant under a state-space equivalence `e : X' ≃ₗ[𝕜] X`, with
`A' = e.symm ∘ A ∘ e`, `E' = e.symm ∘ E` and `H' = H ∘ e`. In particular
decoupling is a coordinate-free property. -/

section ChangeState

variable {X' : Type*} [AddCommGroup X'] [Module 𝕜 X']

/-- The Markov parameters are carried to themselves by a state-space
equivalence. -/
theorem disturbanceResponse_changeState (A : X →ₗ[𝕜] X) (E : W →ₗ[𝕜] X)
    (H : X →ₗ[𝕜] Z) (e : X' ≃ₗ[𝕜] X) (k : ℕ) :
    disturbanceResponse (e.symm.conj A) (e.symm.toLinearMap.comp E)
        (H.comp e.toLinearMap) k =
      disturbanceResponse A E H k := by
  have hpow : ∀ k : ℕ, (e.symm.conj A) ^ k = e.symm.conj (A ^ k) := fun k =>
    (map_pow (LinearEquiv.conjRingEquiv e.symm) A k).symm
  ext w
  simp only [disturbanceResponse, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [hpow k, LinearEquiv.conj_apply]
  simp

/-- **Decoupling is invariant under a state-space equivalence.** -/
theorem isDisturbanceDecoupled_changeState_iff (A : X →ₗ[𝕜] X) (E : W →ₗ[𝕜] X)
    (H : X →ₗ[𝕜] Z) (e : X' ≃ₗ[𝕜] X) :
    IsDisturbanceDecoupled (e.symm.conj A) (e.symm.toLinearMap.comp E)
        (H.comp e.toLinearMap) ↔
      IsDisturbanceDecoupled A E H := by
  simp only [IsDisturbanceDecoupled, disturbanceResponse_changeState]

end ChangeState

/-! ## Disturbance decoupling by static state feedback (Theorem 4.8) -/

/-- The system with dynamics `A + B F` is the closed loop obtained from state
feedback `u = F x + v`. This predicate records that **disturbance decoupling by
static state feedback** (DDP, Definition 4.7) is achievable: there is a linear map
`F : X →ₗ[𝕜] U` such that the closed-loop channel `(A + B F, E, H)` is
decoupled. -/
def IsStateFeedbackDisturbanceDecoupled (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (E : W →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z) : Prop :=
  ∃ F : X →ₗ[𝕜] U, IsDisturbanceDecoupled (A + B.comp F) E H

/-- Unfolding lemma for `IsStateFeedbackDisturbanceDecoupled`. -/
theorem isStateFeedbackDisturbanceDecoupled_iff (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (E : W →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z) :
    IsStateFeedbackDisturbanceDecoupled A B E H ↔
      ∃ F : X →ₗ[𝕜] U, IsDisturbanceDecoupled (A + B.comp F) E H := Iff.rfl

/-- **Theorem 4.8.** Disturbance decoupling by static state feedback is possible
if and only if there is a *controlled invariant* subspace `V` with
`im E ≤ V ≤ ker H`.

Both directions are proved. The forward direction uses the feedback
characterisation of controlled invariance in reverse: an `(A + B F)`-invariant
subspace is `(A, B)`-invariant. The converse direction uses
`exists_stateFeedback_of_isControlledInvariant` to make `V` invariant. -/
theorem isStateFeedbackDisturbanceDecoupled_iff_exists_controlledInvariant
    (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (E : W →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z) :
    IsStateFeedbackDisturbanceDecoupled A B E H ↔
      ∃ V : Submodule 𝕜 X, range E ≤ V ∧ V ≤ ker H ∧ IsControlledInvariant A B V := by
  constructor
  · rintro ⟨F, hF⟩
    obtain ⟨V, hE, hH, hA⟩ := (isDisturbanceDecoupled_iff_exists_invariant
      (A + B.comp F) E H).mp hF
    exact ⟨V, hE, hH, isControlledInvariant_of_exists_stateFeedback ⟨F, hA⟩⟩
  · rintro ⟨V, hE, hH, hV⟩
    obtain ⟨F, hF⟩ := exists_stateFeedback_of_isControlledInvariant hV
    exact ⟨F, (isDisturbanceDecoupled_iff_exists_invariant (A + B.comp F) E H).mpr
      ⟨V, hE, hH, hF⟩⟩

/-- **Corollary 4.9.** In finite dimension, disturbance decoupling by static
state feedback is possible if and only if `im E ≤ V*(ker H)`, where `V*(ker H)`
is the largest controlled invariant subspace contained in `ker H`.

The forward direction uses that every controlled invariant subspace inside
`ker H` is contained in `V*(ker H)`; the converse takes `V := V*(ker H)`, which
in finite dimension is controlled invariant and contained in `ker H`. -/
theorem isStateFeedbackDisturbanceDecoupled_iff_range_le_controlledInvariantSubspace
    [FiniteDimensional 𝕜 X] (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (E : W →ₗ[𝕜] X)
    (H : X →ₗ[𝕜] Z) :
    IsStateFeedbackDisturbanceDecoupled A B E H ↔
      range E ≤ controlledInvariantSubspace A B (ker H) := by
  rw [isStateFeedbackDisturbanceDecoupled_iff_exists_controlledInvariant]
  constructor
  · rintro ⟨V, hE, hH, hV⟩
    exact le_trans hE (le_controlledInvariantSubspace hH hV)
  · intro h
    exact ⟨controlledInvariantSubspace A B (ker H), h,
      controlledInvariantSubspace_le_K A B (ker H),
      isControlledInvariant_controlledInvariantSubspace A B (ker H)⟩

/-! ## The conditioned-invariant bridge: `(C, A, B)`-pairs

The measurement-feedback theory of Chapter 6 replaces the single controlled
invariant subspace `V` by a pair `(S, V)` with `S ≤ V`, where `S` is conditioned
invariant and `V` is controlled invariant. The existence of a pair sandwiched
between `im E` and `ker H` is precisely the subspace inclusion
`S*(im E) ≤ V*(ker H)`; this is the algebraic core of Corollary 6.7. -/

/-- A **`(C, A, B)`-pair** of subspaces (Trentelman–Stoorvogel–Hautus,
Definition 6.1): a pair `S ≤ V` where `S` is `(C, A)`-invariant (conditioned
invariant) and `V` is `(A, B)`-invariant (controlled invariant). -/
def IsCABPair (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (S V : Submodule 𝕜 X) : Prop :=
  S ≤ V ∧ IsConditionedInvariant C A S ∧ IsControlledInvariant A B V

/-- A `(C, A, B)`-pair **between `im E` and `ker H`**: a `(C, A, B)`-pair with
`im E ≤ S` and `V ≤ ker H`. Such a pair is the subspace certificate used by the
measurement-feedback disturbance-decoupling theory of Chapter 6. -/
def IsCABPairBetween (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (E : W →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z) (S V : Submodule 𝕜 X) : Prop :=
  IsCABPair C A B S V ∧ range E ≤ S ∧ V ≤ ker H

/-- Unfolding lemma for `IsCABPair`. -/
theorem isCABPair_iff (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (S V : Submodule 𝕜 X) :
    IsCABPair C A B S V ↔
      S ≤ V ∧ IsConditionedInvariant C A S ∧ IsControlledInvariant A B V := Iff.rfl

/-- Unfolding lemma for `IsCABPairBetween`. -/
theorem isCABPairBetween_iff (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X)
    (E : W →ₗ[𝕜] X) (H : X →ₗ[𝕜] Z) (S V : Submodule 𝕜 X) :
    IsCABPairBetween C A B E H S V ↔
      IsCABPair C A B S V ∧ range E ≤ S ∧ V ≤ ker H := Iff.rfl

/-- **The algebraic core of Corollary 6.7.** In finite dimension there exists a
`(C, A, B)`-pair between `im E` and `ker H` if and only if the smallest
conditioned invariant subspace containing `im E` is contained in the largest
controlled invariant subspace contained in `ker H`:
`S*(im E) ≤ V*(ker H)`.

The forward direction is pure order theory on the subspace lattices: `S*(im E)`
is the least conditioned invariant subspace containing `im E`, and `V*(ker H)`
is the greatest controlled invariant subspace inside `ker H`. The converse takes
`(S, V) := (S*(im E), V*(ker H))`, which is a `(C, A, B)`-pair in finite
dimension by the accepted ISA/CISA termination results.

The passage from such a pair to an actual dynamic measurement-feedback controller
(Theorem 6.4) is not asserted by this theorem; it is constructed in the separate
module `DynamicalSystems.Linear.DynamicFeedback`. -/
theorem exists_isCABPairBetween_iff [FiniteDimensional 𝕜 X]
    (C : X →ₗ[𝕜] Y) (A : X →ₗ[𝕜] X) (B : U →ₗ[𝕜] X) (E : W →ₗ[𝕜] X)
    (H : X →ₗ[𝕜] Z) :
    (∃ S V : Submodule 𝕜 X, IsCABPairBetween C A B E H S V) ↔
      conditionedInvariantSubspace C A (range E) ≤
        controlledInvariantSubspace A B (ker H) := by
  constructor
  · rintro ⟨S, V, ⟨hSV, hS, hV⟩, hE, hH⟩
    exact le_trans (conditionedInvariantSubspace_le hE hS)
      (le_trans hSV (le_controlledInvariantSubspace hH hV))
  · intro h
    refine ⟨conditionedInvariantSubspace C A (range E),
      controlledInvariantSubspace A B (ker H), ⟨h, ?_, ?_⟩,
      le_conditionedInvariantSubspace C A (range E),
      controlledInvariantSubspace_le_K A B (ker H)⟩
    · exact isConditionedInvariant_conditionedInvariantSubspace C A (range E)
    · exact isControlledInvariant_controlledInvariantSubspace A B (ker H)

/-! ## Worked example: the double integrator

For the double integrator `A (x, y) = (y, 0)` the position state is killed by
the dynamics while the velocity state is not. A disturbance entering the position
is invisible to a velocity readout (possible decoupling), whereas a disturbance
entering the velocity is seen by a position readout (impossible decoupling). -/

section DoubleIntegrator

/-- The double-integrator state map `(x, y) ↦ (y, 0)` on `ℝ × ℝ`. -/
def doubleIntegratorStateMap : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun p := (p.2, 0)
  map_add' p q := by ext <;> simp
  map_smul' c p := by ext <;> simp

/-- Position disturbance map `d ↦ (d, 0)`. -/
def doubleIntegratorPositionDisturbance : ℝ →ₗ[ℝ] (ℝ × ℝ) := LinearMap.inl ℝ ℝ ℝ

/-- Velocity disturbance map `d ↦ (0, d)`. -/
def doubleIntegratorVelocityDisturbance : ℝ →ₗ[ℝ] (ℝ × ℝ) := LinearMap.inr ℝ ℝ ℝ

/-- Position readout `(x, y) ↦ x`. -/
def doubleIntegratorPositionReadout : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.fst ℝ ℝ ℝ

/-- Velocity readout `(x, y) ↦ y`. -/
def doubleIntegratorVelocityReadout : (ℝ × ℝ) →ₗ[ℝ] ℝ := LinearMap.snd ℝ ℝ ℝ

@[simp]
theorem doubleIntegratorStateMap_apply (p : ℝ × ℝ) :
    doubleIntegratorStateMap p = (p.2, 0) := rfl

@[simp]
theorem doubleIntegratorPositionDisturbance_apply (d : ℝ) :
    doubleIntegratorPositionDisturbance d = (d, 0) := rfl

@[simp]
theorem doubleIntegratorVelocityDisturbance_apply (d : ℝ) :
    doubleIntegratorVelocityDisturbance d = (0, d) := rfl

@[simp]
theorem doubleIntegratorPositionReadout_apply (p : ℝ × ℝ) :
    doubleIntegratorPositionReadout p = p.1 := rfl

@[simp]
theorem doubleIntegratorVelocityReadout_apply (p : ℝ × ℝ) :
    doubleIntegratorVelocityReadout p = p.2 := rfl

/-- A position disturbance is decoupled from the velocity readout: the
dynamics kills the position disturbance before it can reach the velocity state. -/
theorem isDisturbanceDecoupled_doubleIntegrator_position :
    IsDisturbanceDecoupled doubleIntegratorStateMap doubleIntegratorPositionDisturbance
      doubleIntegratorVelocityReadout := by
  refine isDisturbanceDecoupled_of_map_range_eq_bot _ _ _ ?_ ?_
  · rw [Submodule.eq_bot_iff]
    rintro x ⟨q, hq, rfl⟩
    obtain ⟨d, rfl⟩ := hq
    simp [doubleIntegratorStateMap]
  · intro x hx
    obtain ⟨d, rfl⟩ := hx
    simp

/-- A velocity disturbance is **not** decoupled from the position readout: after
one unit of time the position readout sees the disturbance. -/
theorem not_isDisturbanceDecoupled_doubleIntegrator_velocity :
    ¬ IsDisturbanceDecoupled doubleIntegratorStateMap doubleIntegratorVelocityDisturbance
        doubleIntegratorPositionReadout := by
  intro h
  have h1 : doubleIntegratorPositionReadout
      (doubleIntegratorStateMap (doubleIntegratorVelocityDisturbance 1)) = 0 :=
    LinearMap.congr_fun (h 1) 1
  norm_num at h1

end DoubleIntegrator

end LinearMap

namespace LinearMap

section Analytic

variable {X W Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-! ## The analytic impulse-response bridge

The Markov-parameter predicate `IsDisturbanceDecoupled` is the derivative-at-zero
form of the impulse response of Trentelman–Stoorvogel–Hautus, equation (4.4).
Over the reals and in finite dimension the two agree: the channel is decoupled
exactly when the analytic impulse response `t ↦ H e^{tA} E` vanishes identically.
This is proved by identifying the channel with the accepted LTI system API and
using the unobservability bridges of `DynamicalSystems.Linear.Reachability`.

The *convolution* form is proved below: vanishing of the impulse response is
equivalent to input-independence of the forced output
`t ↦ H (exp (tA) x₀ + ∫₀ᵗ exp ((t - s) A) E d(s) ds)` for every locally
integrable disturbance `d`, through the variation-of-constants formula. -/

/-- The LTI system `x' = A x + E d`, `z = H x` associated with a disturbance
channel, with the disturbance map as its input map. This is a bookkeeping device
that lets the accepted trajectory and unobservability API apply verbatim. -/
noncomputable def disturbanceSystem (A : X →ₗ[ℝ] X) (E : W →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    LinearSystem ℝ X W Z where
  A := A
  B := E
  C := H
  D := 0

@[simp]
theorem disturbanceSystem_A (A : X →ₗ[ℝ] X) (E : W →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    (disturbanceSystem A E H).A = A := rfl

@[simp]
theorem disturbanceSystem_B (A : X →ₗ[ℝ] X) (E : W →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    (disturbanceSystem A E H).B = E := rfl

@[simp]
theorem disturbanceSystem_C (A : X →ₗ[ℝ] X) (E : W →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    (disturbanceSystem A E H).C = H := rfl

@[simp]
theorem disturbanceSystem_D (A : X →ₗ[ℝ] X) (E : W →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    (disturbanceSystem A E H).D = 0 := rfl

variable [FiniteDimensional ℝ X]

/-- **Impulse-response form of decoupling.** Over the reals and in finite
dimension the algebraic predicate `IsDisturbanceDecoupled A E H` is equivalent
to the identical vanishing of the analytic impulse response
`t ↦ H (e^{tA} (E d))` for every disturbance direction `d`.

This is the precise sense in which the Markov parameters are the derivatives at
zero of the impulse response of Trentelman–Stoorvogel–Hautus, equation (4.4). -/
theorem isDisturbanceDecoupled_iff_forall_expFlow
    (A : X →ₗ[ℝ] X) (E : W →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    IsDisturbanceDecoupled A E H ↔
      ∀ d : W, ∀ t : ℝ, H ((disturbanceSystem A E H).expFlow t (E d)) = 0 := by
  rw [isDisturbanceDecoupled_iff_range_le_unobservableSubspace]
  constructor
  · intro h d t
    have hz : E d ∈ unobservableSubspace H A := h ⟨d, rfl⟩
    simpa [disturbanceSystem] using
      LinearSystem.continuousC_expFlow_eq_zero_of_mem_unobservableSubspace
        (disturbanceSystem A E H) hz t
  · intro h
    rw [range_le_iff_comap, eq_top_iff]
    intro d _
    change E d ∈ unobservableSubspace H A
    refine LinearSystem.mem_unobservableSubspace_of_forall_continuousC_expFlow_eq_zero
      (disturbanceSystem A E H) (T := 1) zero_lt_one ?_
    intro t _
    simpa [disturbanceSystem] using h d t

/-! ## The variation-of-constants / convolution bridge

Trentelman–Stoorvogel–Hautus, equations (3.2)–(3.3). For the disturbance channel
`x' = A x + E d`, `z = H x` and a locally integrable disturbance `d`, the forced
output from `x(t₀) = x₀` is the variation-of-constants trajectory of the
associated `LinearSystem`, read through `H`. It has the convolution form

`z(t) = H (exp ((t - t₀) A) x₀) + ∫_{t₀}^{t} K (t - s) d(s) ds`,

with impulse response `K(t) = H ∘ exp (t A) ∘ E`. The Bochner-integral form is
`forcedOutput_eq_convolution`; exact decoupling makes the whole convolution term
vanish for every locally integrable disturbance
(`isDisturbanceDecoupled_disturbanceContribution_eq_zero`), and this is an
equivalence (`isDisturbanceDecoupled_iff_forall_disturbanceContribution_eq_zero`).

The converse is proved by testing the hypothesis on rectangular pulses: the
response to `1_{(0,δ)} • w` at time `δ + r` is the `δ`-average of
`u ↦ H (e^{(r+u)A} E w)`, so the fundamental theorem of calculus recovers the
impulse response `H (e^{rA} E w)` as `δ → 0⁺`. -/

section ConvolutionDefinitions

variable [FiniteDimensional ℝ W]

/-- The disturbance-to-output **impulse response** `K(t) = H e^{tA} E` of the
channel, evaluated on a disturbance direction `w`. This is the kernel of the
convolution integral of Trentelman–Stoorvogel–Hautus, equation (3.3), with
`D = 0`. -/
noncomputable def disturbanceImpulseResponse (A : X →ₗ[ℝ] X) (E : W →ₗ[ℝ] X)
    (H : X →ₗ[ℝ] Z) (t : ℝ) (w : W) : Z :=
  H ((disturbanceSystem A E H).expFlow t (E w))

/-- The **disturbance contribution** to the output: the forced output from the
origin, i.e. the readout `H` of the variation-of-constants trajectory of
`x' = A x + E d` with `x(t₀) = 0`. Together with the free response
`H (exp ((t - t₀) A) x₀)` it makes up the full forced output. -/
noncomputable def disturbanceContribution (A : X →ₗ[ℝ] X) (E : W →ₗ[ℝ] X)
    (H : X →ₗ[ℝ] Z) (t₀ : ℝ) (d : ℝ → W) (t : ℝ) : Z :=
  H ((disturbanceSystem A E H).variationOfConstants t₀ 0 d t)

/-- The **forced output** of the disturbance channel from initial state `x₀` at
time `t₀`: the zero-feedthrough readout `H` of the variation-of-constants
trajectory of `x' = A x + E d`. -/
noncomputable def forcedOutput (A : X →ₗ[ℝ] X) (E : W →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (t₀ : ℝ) (x₀ : X) (d : ℝ → W) (t : ℝ) : Z :=
  (disturbanceSystem A E H).readout
    ((disturbanceSystem A E H).variationOfConstants t₀ x₀ d t) (d t)

/-- Unfolding lemma for `forcedOutput`: the zero-feedthrough readout is `H`. -/
@[simp]
theorem forcedOutput_apply (A : X →ₗ[ℝ] X) (E : W →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (t₀ : ℝ) (x₀ : X) (d : ℝ → W) (t : ℝ) :
    forcedOutput A E H t₀ x₀ d t =
      H ((disturbanceSystem A E H).variationOfConstants t₀ x₀ d t) := by
  simp [forcedOutput, LinearSystem.readout, disturbanceSystem]

/-- The forced output from the origin is exactly the disturbance contribution.
This is deliberately not a `@[simp]` lemma: `forcedOutput_apply` already rewrites
the left-hand side to the readout of the variation-of-constants trajectory, so a
`simp`-normal-form version is obtained by unfolding `disturbanceContribution`. -/
theorem forcedOutput_zero_initial (A : X →ₗ[ℝ] X) (E : W →ₗ[ℝ] X)
    (H : X →ₗ[ℝ] Z) (t₀ : ℝ) (d : ℝ → W) (t : ℝ) :
    forcedOutput A E H t₀ 0 d t = disturbanceContribution A E H t₀ d t := by
  simp [forcedOutput, disturbanceContribution, LinearSystem.readout, disturbanceSystem]

omit [FiniteDimensional ℝ W] in
/-- The exponential flow of the disturbance system is a semigroup in evaluation
form: `exp (a A) (exp (b A) z) = exp ((a + b) A) z`. -/
theorem disturbanceSystem_expFlow_add_apply (A : X →ₗ[ℝ] X) (E : W →ₗ[ℝ] X)
    (H : X →ₗ[ℝ] Z) (a b : ℝ) (z : X) :
    (disturbanceSystem A E H).expFlow a ((disturbanceSystem A E H).expFlow b z) =
      (disturbanceSystem A E H).expFlow (a + b) z := by
  rw [← mul_apply_eq_comp, LinearSystem.expFlow_add]

end ConvolutionDefinitions

section Convolution

variable [FiniteDimensional ℝ W] [CompleteSpace Z]

/-- **Variation-of-constants / convolution bridge.** The forced output of the
disturbance channel from `x(t₀) = x₀` under a locally integrable disturbance `d`
is the free response plus the convolution of the impulse response with `d`:

`z(t) = H (e^{(t - t₀)A} x₀) + ∫_{t₀}^{t} H (e^{(t - s)A} E) d(s) ds`.

Source: Trentelman–Stoorvogel–Hautus, equations (3.2) and (3.3), with `D = 0`.
The integral is a Bochner integral in the output space. -/
theorem forcedOutput_eq_convolution (A : X →ₗ[ℝ] X) (E : W →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    {t₀ : ℝ} {x₀ : X} {d : ℝ → W} (hd : LocallyIntegrable d volume) (t : ℝ) :
    forcedOutput A E H t₀ x₀ d t =
      H ((disturbanceSystem A E H).expFlow (t - t₀) x₀) +
        ∫ s in t₀..t, disturbanceImpulseResponse A E H (t - s) (d s) := by
  have hfd : IntervalIntegrable ((disturbanceSystem A E H).forcing t₀ d) volume t₀ t :=
    LinearSystem.intervalIntegrable_forcing (disturbanceSystem A E H) t₀ hd t₀ t
  have hcomp : (∫ s in t₀..t, (disturbanceSystem A E H).continuousC
        ((disturbanceSystem A E H).expFlow (t - t₀)
          ((disturbanceSystem A E H).forcing t₀ d s))) =
      (disturbanceSystem A E H).continuousC
        ((disturbanceSystem A E H).expFlow (t - t₀)
          (∫ s in t₀..t, (disturbanceSystem A E H).forcing t₀ d s)) := by
    simpa only [ContinuousLinearMap.comp_apply] using
      ContinuousLinearMap.intervalIntegral_comp_comm
        ((disturbanceSystem A E H).continuousC.comp
          ((disturbanceSystem A E H).expFlow (t - t₀))) hfd
  rw [forcedOutput_apply]
  simp only [LinearSystem.variationOfConstants, map_add]
  congr 1
  have hLapp : (disturbanceSystem A E H).continuousC
        ((disturbanceSystem A E H).expFlow (t - t₀)
          (∫ s in t₀..t, (disturbanceSystem A E H).forcing t₀ d s)) =
        H ((disturbanceSystem A E H).expFlow (t - t₀)
          (∫ s in t₀..t, (disturbanceSystem A E H).forcing t₀ d s)) := by
    simp [disturbanceSystem]
  rw [← hLapp, ← hcomp]
  apply intervalIntegral.integral_congr
  intro s _
  have hC : (disturbanceSystem A E H).continuousC
      ((disturbanceSystem A E H).expFlow (t - t₀)
        ((disturbanceSystem A E H).forcing t₀ d s)) =
      H ((disturbanceSystem A E H).expFlow (t - t₀)
        ((disturbanceSystem A E H).forcing t₀ d s)) := by
    simp [disturbanceSystem]
  have hforce : (disturbanceSystem A E H).forcing t₀ d s =
      (disturbanceSystem A E H).expFlow (-(s - t₀)) (E (d s)) := by
    simp [disturbanceSystem, LinearSystem.forcing]
  dsimp only
  rw [hC, hforce, disturbanceSystem_expFlow_add_apply, disturbanceImpulseResponse]
  rw [show (t - t₀) + -(s - t₀) = t - s by ring]

omit [FiniteDimensional ℝ W] [CompleteSpace Z] in
/-- Under exact decoupling the convolution term vanishes identically: for every
locally integrable disturbance the disturbance contribution to the output is
zero. This is the input-independence content of `T = 0`. -/
theorem isDisturbanceDecoupled_convolution_integral_eq_zero
    (A : X →ₗ[ℝ] X) (E : W →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : IsDisturbanceDecoupled A E H) {d : ℝ → W} (_hd : LocallyIntegrable d volume)
    (t₀ t : ℝ) :
    (∫ s in t₀..t, disturbanceImpulseResponse A E H (t - s) (d s)) = 0 := by
  have hrange : range E ≤ unobservableSubspace H A :=
    (isDisturbanceDecoupled_iff_range_le_unobservableSubspace A E H).mp h
  have hfun : (fun s : ℝ => disturbanceImpulseResponse A E H (t - s) (d s)) =
      fun _ => (0 : Z) := by
    funext s
    rw [disturbanceImpulseResponse]
    simpa using LinearSystem.continuousC_expFlow_eq_zero_of_mem_unobservableSubspace
      (disturbanceSystem A E H) (hrange ⟨d s, rfl⟩) (t - s)
  rw [hfun]
  simp

/-- The convolution form of the disturbance contribution (zero initial state). -/
theorem disturbanceContribution_eq_convolution (A : X →ₗ[ℝ] X) (E : W →ₗ[ℝ] X)
    (H : X →ₗ[ℝ] Z) {t₀ : ℝ} {d : ℝ → W} (hd : LocallyIntegrable d volume) (t : ℝ) :
    disturbanceContribution A E H t₀ d t =
      ∫ s in t₀..t, disturbanceImpulseResponse A E H (t - s) (d s) := by
  rw [← forcedOutput_zero_initial]
  simpa using forcedOutput_eq_convolution A E H (t₀ := t₀) (x₀ := 0) (d := d) hd t

/-- **Exact decoupling kills the disturbance contribution.** If the channel is
disturbance decoupled then the forced output from the origin is zero for every
locally integrable disturbance and every time. -/
theorem isDisturbanceDecoupled_disturbanceContribution_eq_zero
    (A : X →ₗ[ℝ] X) (E : W →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : IsDisturbanceDecoupled A E H) {t₀ : ℝ} {d : ℝ → W}
    (hd : LocallyIntegrable d volume) (t : ℝ) :
    disturbanceContribution A E H t₀ d t = 0 := by
  rw [disturbanceContribution_eq_convolution A E H hd t]
  exact isDisturbanceDecoupled_convolution_integral_eq_zero A E H h hd t₀ t

/-- **Input independence.** Under exact decoupling the output is independent of
the admissible disturbance: two locally integrable disturbances with the same
initial state produce the same output trajectory. -/
theorem isDisturbanceDecoupled_forcedOutput_eq_of_input
    (A : X →ₗ[ℝ] X) (E : W →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : IsDisturbanceDecoupled A E H) {t₀ : ℝ} {x₀ : X} {d₁ d₂ : ℝ → W}
    (hd₁ : LocallyIntegrable d₁ volume) (hd₂ : LocallyIntegrable d₂ volume) (t : ℝ) :
    forcedOutput A E H t₀ x₀ d₁ t = forcedOutput A E H t₀ x₀ d₂ t := by
  rw [forcedOutput_eq_convolution A E H hd₁ t, forcedOutput_eq_convolution A E H hd₂ t,
    isDisturbanceDecoupled_convolution_integral_eq_zero A E H h hd₁ t₀ t,
    isDisturbanceDecoupled_convolution_integral_eq_zero A E H h hd₂ t₀ t,
    add_zero]

omit [CompleteSpace Z] in
/-- **Converse of the convolution criterion.** If the disturbance contribution
vanishes for every locally integrable disturbance, every initial time and every
time, then the channel is disturbance decoupled.

The proof tests the hypothesis on rectangular pulses `1_{(0,δ)} • w`: the
response from the origin at time `δ + r` is the `δ`-average of the continuous
curve `u ↦ H (e^{(r + u)A} E w)`, so dividing by `δ` and letting `δ → 0⁺` uses
the fundamental theorem of calculus to recover `H (e^{rA} E w)`. Applying the
accepted analytic bridge `isDisturbanceDecoupled_iff_forall_expFlow` concludes. -/
theorem isDisturbanceDecoupled_of_forall_disturbanceContribution_eq_zero
    (A : X →ₗ[ℝ] X) (E : W →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : ∀ (t₀ : ℝ) (d : ℝ → W), LocallyIntegrable d volume →
      ∀ t : ℝ, disturbanceContribution A E H t₀ d t = 0) :
    IsDisturbanceDecoupled A E H := by
  rw [isDisturbanceDecoupled_iff_range_le_unobservableSubspace]
  intro x hx
  obtain ⟨w, rfl⟩ := hx
  let sys := disturbanceSystem A E H
  refine LinearSystem.mem_unobservableSubspace_of_forall_continuousC_expFlow_eq_zero
    sys (T := 1) zero_lt_one ?_
  intro t ht
  have ht_nonneg : 0 ≤ t := ht.1
  let φ : ℝ → X := fun u => sys.expFlow (-u) (E w)
  let F : ℝ → X := fun δ => ∫ u in (0 : ℝ)..δ, φ u
  let G : ℝ → X := fun δ => sys.expFlow (δ + t) (δ⁻¹ • F δ)
  have hφ : Continuous φ := by
    have hExp : Continuous (fun u : ℝ => sys.expFlow (-u)) := by
      have h := (LinearSystem.continuous_expFlow_sub sys 0).comp continuous_neg
      simpa only [Function.comp_def, sub_zero] using h
    exact hExp.clm_apply continuous_const
  have hF_deriv : HasDerivAt F (E w) 0 := by
    have h := intervalIntegral.integral_hasDerivAt_right
      (hφ.intervalIntegrable 0 0)
      (hφ.stronglyMeasurableAtFilter volume (𝓝 0)) hφ.continuousAt
    simpa [F, φ] using h
  have hF_tendsto : Tendsto (fun δ : ℝ => δ⁻¹ • F δ) (𝓝[>] (0 : ℝ)) (𝓝 (E w)) := by
    have h := hF_deriv.tendsto_slope_zero_right
    simpa [F] using h
  have hG : ∀ δ : ℝ, 0 < δ → H (G δ) = 0 := by
    intro δ hδ
    let d : ℝ → W := (Set.Ioc (0 : ℝ) δ).indicator (fun _ => w)
    have hd : LocallyIntegrable d volume :=
      (locallyIntegrable_const w).indicator measurableSet_Ioc
    have h0 : H (sys.expFlow (δ + t) (∫ s in (0 : ℝ)..(δ + t), sys.forcing 0 d s)) = 0 := by
      have hh := h 0 d hd (δ + t)
      simpa [sys, disturbanceContribution, LinearSystem.variationOfConstants] using hh
    have hsplit : (∫ s in (0 : ℝ)..(δ + t), sys.forcing 0 d s) =
        (∫ s in (0 : ℝ)..δ, sys.forcing 0 d s) +
          ∫ s in δ..(δ + t), sys.forcing 0 d s :=
      (intervalIntegral.integral_add_adjacent_intervals
        (LinearSystem.intervalIntegrable_forcing sys 0 hd 0 δ)
        (LinearSystem.intervalIntegrable_forcing sys 0 hd δ (δ + t))).symm
    have hsecond : (∫ s in δ..(δ + t), sys.forcing 0 d s) = 0 := by
      refine intervalIntegral.integral_zero_ae ?_
      filter_upwards with s hs
      rw [uIoc_of_le (by linarith)] at hs
      have hs' : s ∉ Set.Ioc (0 : ℝ) δ := by
        rw [Set.mem_Ioc] at hs ⊢
        exact fun h => absurd h.2 (not_le.mpr hs.1)
      have hds : d s = 0 := by simpa [d] using Set.indicator_of_notMem hs' (fun _ => w)
      simp [LinearSystem.forcing, hds]
    have hfirst : (∫ s in (0 : ℝ)..δ, sys.forcing 0 d s) = F δ := by
      have hcongr : (∫ s in (0 : ℝ)..δ, sys.forcing 0 d s) =
          ∫ s in (0 : ℝ)..δ, φ s := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards with s hs
        rw [uIoc_of_le (le_of_lt hδ)] at hs
        have hds : d s = w := by simpa [d] using Set.indicator_of_mem hs (fun _ => w)
        simp [LinearSystem.forcing, hds, φ, sys, disturbanceSystem]
      rw [hcongr]
    have h0' : H (sys.expFlow (δ + t) (F δ)) = 0 := by
      rw [hsplit, hsecond, add_zero, hfirst] at h0
      exact h0
    have hsmul : sys.expFlow (δ + t) (F δ) = δ • G δ := by
      have h1 : F δ = δ • (δ⁻¹ • F δ) := by
        rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hδ), one_smul]
      rw [h1, map_smul]
    have hz := h0'
    rw [hsmul, map_smul] at hz
    exact (smul_eq_zero.mp hz).resolve_left (ne_of_gt hδ)
  have hFlow : Tendsto (fun δ : ℝ => sys.expFlow (δ + t)) (𝓝[>] (0 : ℝ))
      (𝓝 (sys.expFlow t)) := by
    have hcont : Continuous (fun δ : ℝ => sys.expFlow (δ + t)) := by
      simpa only [sub_neg_eq_add] using LinearSystem.continuous_expFlow_sub sys (-t)
    have hca : ContinuousAt (fun δ : ℝ => sys.expFlow (δ + t)) 0 := hcont.continuousAt
    have hle : 𝓝[Set.Ioi (0 : ℝ)] (0 : ℝ) ≤ 𝓝 (0 : ℝ) := nhdsWithin_le_nhds
    have h := hca.tendsto.mono_left hle
    simpa using h
  have hprod : Tendsto G (𝓝[>] (0 : ℝ)) (𝓝 (sys.expFlow t (E w))) := by
    have hpair : Tendsto (fun δ : ℝ => (sys.expFlow (δ + t), δ⁻¹ • F δ))
        (𝓝[>] (0 : ℝ)) (𝓝 (sys.expFlow t, E w)) := by
      rw [nhds_prod_eq]
      exact hFlow.prodMk hF_tendsto
    have heval : ContinuousAt (fun p : (X →L[ℝ] X) × X => p.1 p.2)
        (sys.expFlow t, E w) :=
      (continuous_fst.clm_apply continuous_snd).continuousAt
    have := heval.tendsto.comp hpair
    simpa [G, Function.comp_def] using this
  have hzero : H (sys.expFlow t (E w)) = 0 := by
    have htend : Tendsto (fun δ : ℝ => H (G δ)) (𝓝[>] (0 : ℝ))
        (𝓝 (H (sys.expFlow t (E w)))) := by
      have := (sys.continuousC.continuous.tendsto (sys.expFlow t (E w))).comp hprod
      simpa [Function.comp_def, sys, disturbanceSystem] using this
    have hconst : Tendsto (fun δ : ℝ => H (G δ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hev : (fun δ : ℝ => H (G δ)) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => (0 : Z)) := by
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        exact hG δ hδ
      exact Tendsto.congr' hev.symm tendsto_const_nhds
    exact tendsto_nhds_unique htend hconst
  simpa [sys] using hzero

/-- **Exact decoupling is equivalent to zero disturbance contribution for every
admissible input.** -/
theorem isDisturbanceDecoupled_iff_forall_disturbanceContribution_eq_zero
    (A : X →ₗ[ℝ] X) (E : W →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    IsDisturbanceDecoupled A E H ↔
      ∀ (t₀ : ℝ) (d : ℝ → W), LocallyIntegrable d volume →
        ∀ t : ℝ, disturbanceContribution A E H t₀ d t = 0 :=
  ⟨fun h _ _ hd t => isDisturbanceDecoupled_disturbanceContribution_eq_zero A E H h hd t,
    fun h => isDisturbanceDecoupled_of_forall_disturbanceContribution_eq_zero A E H h⟩

end Convolution

end Analytic

end LinearMap
