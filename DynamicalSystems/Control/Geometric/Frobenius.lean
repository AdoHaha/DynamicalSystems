/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.Rectification
public import DynamicalSystems.Control.Geometric.LieBrackets
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Commuting vector fields: interface and the `k = 1` rectification base case

This file formalises the commuting-fields **interface** (`FlowsCommuteLocally`) and the
`k = 1` base case (`krenerLemma_base`) of Krener's rectification lemma. The simultaneous
rectification of all `k` fields is recorded as a target definition
(`SimultaneouslyRectifiable`) but is **not** proved here.

## Scope fence

The bridge between commuting flows and vanishing Lie brackets (in either direction)
is 600–1000 lines and absent from Mathlib. It is NOT proved here. Instead:

* `FlowsCommuteLocally` is the **hypothesis interface**: pairwise bracket-vanishing
  on a neighbourhood of `x₀`, which is what "commute" means at the infinitesimal
  level. The classical flows-commute interpretation is documented, not proved.
* `krenerLemma_base` proves only the **`k = 1` base case**: a single field `f i₀`
  (nonsingular at `x₀`) admits a rectifying chart in the trajectory form of G1's
  `rectifyingChart_rectifies`. It does **not** rectify the family simultaneously.
  The hypotheses `hind` (linear independence) and `hcomm` (commutativity) are
  **reserved** for the absent induction step and are not consumed by this theorem;
  they are kept for interface stability.
* `SimultaneouslyRectifiable` states the true Krener-lemma conclusion — a local
  diffeomorphism whose inverse straightens all `k` fields to `e₁, …, e_k` at once.
  It is NOT proved here; the transverse-slice descent and chart composition are
  deferred.

## References

* Krener, A. J., *Differential Geometric Methods in Nonlinear Control*, in
  *Encyclopedia of Systems and Control*, Springer, 2015, pp. 563–570.
* Sontag, E. D., *Mathematical Control Theory: Deterministic Finite Dimensional Systems*,
  2nd ed., Springer, 1998, Ch. 4 §4.2–§4.4 (printed pp. 141–176).
-/

@[expose] public section

open Set Metric
open scoped Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Local commutativity hypothesis for two vector fields near `x₀`, expressed as
pairwise bracket-vanishing on a neighbourhood of `x₀`.

This is the interface form of "f and g commute": classically, commuting flows
(`Fl_t ∘ Gs_s = Gs_s ∘ Fl_t` locally) is equivalent to `[f, g] = 0`, but that
equivalence is NOT proved here (it needs the variational equation and is absent
from Mathlib). We take the bracket form — stated with `lieBracket` from
`Control.Geometric.LieBrackets` — as the working hypothesis. -/
def FlowsCommuteLocally (f g : X → X) (x₀ : X) : Prop :=
  ∃ U ∈ 𝓝 x₀, ∀ x ∈ U, lieBracket f g x = 0

/-- A globally vanishing bracket implies the local commutativity hypothesis. -/
theorem flowsCommuteLocally_of_global {f g : X → X} {x₀ : X}
    (h : ∀ x, lieBracket f g x = 0) : FlowsCommuteLocally f g x₀ :=
  ⟨Set.univ, Filter.univ_mem, fun x _ => h x⟩

/-- The local commutativity hypothesis is symmetric. -/
theorem flowsCommuteLocally_symm {f g : X → X} {x₀ : X}
    (h : FlowsCommuteLocally f g x₀) : FlowsCommuteLocally g f x₀ := by
  obtain ⟨U, hU, hfg⟩ := h
  refine ⟨U, hU, fun x hx => ?_⟩
  have h1 := lieBracket_swap g f x
  rw [hfg x hx, neg_zero] at h1
  exact h1

/-- Every field locally commutes with itself. -/
theorem flowsCommuteLocally_self (f : X → X) (x₀ : X) : FlowsCommuteLocally f f x₀ := by
  refine flowsCommuteLocally_of_global fun x => ?_
  rw [lieBracket_self]
  rfl

/-- The local commutativity hypothesis gives bracket-vanishing at the base point. -/
theorem flowsCommuteLocally_bracket_at {f g : X → X} {x₀ : X}
    (h : FlowsCommuteLocally f g x₀) : lieBracket f g x₀ = 0 :=
  let ⟨_, hU, hfg⟩ := h
  hfg x₀ (mem_of_mem_nhds hU)

/-- Target statement of the full Krener lemma: simultaneous rectification of a commuting
family of vector fields.

There is a local diffeomorphism `Φ` from coordinates `Fin n → ℝ` into `X` with `Φ 0 = x₀`
whose inverse straightens all `k` fields `f i` at once to the standard coordinate fields
`e₁, …, e_k`: the differential of `Φ` sends the `i`-th coordinate basis vector to `f i`
(so the coordinate lines are the integral curves of all the fields simultaneously).

**NOT proved here; the transverse-slice descent + chart composition is deferred.**
The statement is recorded so that the final rectification theorem has a name. -/
def SimultaneouslyRectifiable {k : ℕ} (f : Fin k → X → X) (x₀ : X) : Prop :=
  ∃ (n : ℕ) (hn : k ≤ n) (Φ : OpenPartialHomeomorph (Fin n → ℝ) X),
    Φ 0 = x₀ ∧ 0 ∈ Φ.source ∧
      ∀ i : Fin k, ∀ z ∈ Φ.source,
        fderiv ℝ (Φ : (Fin n → ℝ) → X) z (Pi.single (Fin.castLE hn i) 1) = f i (Φ z)

/-- k=1 base: rectifies one field only; simultaneous rectification is deferred.

The `k = 1` base case of Krener's lemma. For a family `f : Fin k → X → X` of `C¹`
vector fields that are pointwise linearly independent at `x₀` and pairwise
bracket-vanishing near `x₀`, the distinguished nonsingular field `f i₀` admits a
rectifying chart: an `OpenPartialHomeomorph` `Ψ` near `x₀` whose coordinate lines are
integral curves of `f i₀` (the trajectory-rectification form of G1's
`rectifyingChart`). This rectifies ONE field only and makes no claim about the other
fields of the family.

The hypotheses `hind` (linear independence) and `hcomm` (commutativity) are
**reserved** for the absent induction step and are not consumed by this theorem; they
are kept for interface stability. The transverse-slice descent and chart composition
needed for joint rectification are deferred; the target statement is
`SimultaneouslyRectifiable`. -/
theorem krenerLemma_base [CompleteSpace X] [FiniteDimensional ℝ X]
    {k : ℕ} {f : Fin k → X → X} {x₀ : X}
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀)
    (hind : LinearIndependent ℝ (fun i => f i x₀))
    (hcomm : ∀ i j, FlowsCommuteLocally (f i) (f j) x₀)
    (i₀ : Fin k) (hv : f i₀ x₀ ≠ 0) :
    ∃ Ψ : OpenPartialHomeomorph (ℝ × ↥(flowComplement (f i₀ x₀))) X,
      ∀ (z' : ↥(flowComplement (f i₀ x₀))) (t : ℝ),
        t ∈ Ioo (-(localFlowTime (hf i₀))) (localFlowTime (hf i₀)) →
        x₀ + (flowComplement (f i₀ x₀)).subtypeL z' ∈
          closedBall x₀ (localFlowRadius (hf i₀)) →
        ((t, z') : ℝ × ↥(flowComplement (f i₀ x₀))) ∈ Ψ.source →
        HasDerivAt (fun s ↦ Ψ (s, z')) ((f i₀) (Ψ (t, z'))) t := by
  have _hind := hind
  have _hcomm := hcomm i₀ i₀
  exact ⟨rectifyingChart (hf i₀) hv,
    fun z' t ht hz hmem => rectifyingChart_rectifies (hf i₀) hv z' t ht hz hmem⟩

/-- Per-field corollary of the `k = 1` base case: every nonsingular field of a
pairwise-commuting, pointwise-independent family admits its own rectifying chart. Each
field is rectified separately, not simultaneously. -/
theorem krenerLemma_base_all [CompleteSpace X] [FiniteDimensional ℝ X]
    {k : ℕ} {f : Fin k → X → X} {x₀ : X}
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀)
    (hind : LinearIndependent ℝ (fun i => f i x₀))
    (hcomm : ∀ i j, FlowsCommuteLocally (f i) (f j) x₀)
    (hv : ∀ i, f i x₀ ≠ 0) (i : Fin k) :
    ∃ Ψ : OpenPartialHomeomorph (ℝ × ↥(flowComplement (f i x₀))) X,
      ∀ (z' : ↥(flowComplement (f i x₀))) (t : ℝ),
        t ∈ Ioo (-(localFlowTime (hf i))) (localFlowTime (hf i)) →
        x₀ + (flowComplement (f i x₀)).subtypeL z' ∈
          closedBall x₀ (localFlowRadius (hf i)) →
        ((t, z') : ℝ × ↥(flowComplement (f i x₀))) ∈ Ψ.source →
        HasDerivAt (fun s ↦ Ψ (s, z')) ((f i) (Ψ (t, z'))) t :=
  krenerLemma_base hf hind hcomm i (hv i)

/-! # G3: the algebraic miracle — involutive implies commuting basis (flat local form)

This section formalises the standard "commuting frame" reduction step in the proof of the
Frobenius integrability theorem: an involutive distribution in graph form already has
pairwise-vanishing Lie brackets. This is pure linear algebra plus the Leibniz rule
(no flows, no ODEs).

## References (binding attribution; these results are classical, not original)

* Krener, A. J., "Differential Geometric Methods in Nonlinear Control", in
  *Encyclopedia of Systems and Control*, 2nd ed., Springer, 2015, pp. ~566
  (the "involutive" closed-under-bracket definition and the commuting-frame reduction).
* Sontag, E. D., *Mathematical Control Theory: Deterministic Finite Dimensional Systems*,
  2nd ed., Springer, 1998, Ch. 4 §4.2–§4.4.
* Lee, J. M., *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Theorem 19.12
  (the canonical textbook statement of the Frobenius theorem; cited as the standard
  reference even though it is not in our corpus).
-/ 

/-- Pointwise involutivity of a finite family of vector fields: for every `i j` and `x`,
the bracket `lieBracket (f i) (f j) x` lies in the pointwise span `span ℝ {f m x | m}`.

This is the "closed under bracket" condition; it is Krener's "involutive" definition
(Krener, *Encyclopedia of Systems and Control*, 2nd ed., pp. ~566; see also Sontag,
*Mathematical Control Theory* 2nd ed., Ch. 4 §4.2–§4.4, and Lee, *Introduction to Smooth
Manifolds*, Thm 19.12). Reuses `lieBracket` from `Control/Geometric/LieBrackets`. -/
def InvolutiveDistribution {k : ℕ} (f : Fin k → X → X) : Prop :=
  ∀ i j x, lieBracket (f i) (f j) x ∈ Submodule.span ℝ (Set.range fun m ↦ f m x)

/-- The algebraic miracle (flat, finite-dimensional, local form): an involutive distribution
in graph form is already pairwise commuting.

Hypothesis `hgraph` says the distribution is in **graph form** over the first `k`
coordinates: writing a point of `(Fin k → ℝ) × Y` as `(x₁, x')`, the projection of
each `f i x` onto the first `k` coordinates is the constant `i`-th coordinate vector
eᵢ (`Pi.single i 1`). Under this hypothesis and `InvolutiveDistribution f`, the fields
are pairwise commuting: `∀ i j x, lieBracket (f i) (f j) x = 0`.

*Proof (the miracle; Krener p. ~566; Sontag Ch. 4 §4.2–§4.4; Lee Thm 19.12):* the first
`k` components of each `f i` are the constant eᵢ, so by `fderiv_const` /
`HasFDerivAt.const` the first-`k` block of
`lieBracket (f i) (f j) x = D(f j)(f i x) - D(f i)(f j x)` vanishes (derivative of a
constant is zero); by involutivity the bracket lies in `span {f m x}`; in graph form the
projection onto the first `k` coordinates is injective on that span (the eᵢ are linearly
independent, via `Pi.basisFun`), so a vector in the span with zero first-`k` block is
zero.

*Documented gap:* `hgraph` is assumed rather than derived from a general involutive
distribution. Classically graph form is obtained in two steps, neither of them formalised
here: (1) choose coordinates near `x₀` in which the distribution `Δ` satisfies
`Δ(x₀) = span{e₁, …, e_k}`; this is a constant linear change of coordinates, making `Δ`
transverse to the complementary coordinate directions at `x₀`, and (2) pass to the unique
frame of `Δ` whose first-`k` block is `e_i`; this is an `x`-dependent change of frame, not
a change of coordinates. The passage from a general pointwise-independent involutive
family to graph form is the missing preamble. -/
theorem commutingBasis_of_involutive {k : ℕ} {Y : Type*} [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] {f : Fin k → ((Fin k → ℝ) × Y) → ((Fin k → ℝ) × Y)}
    (hf : ∀ i x, DifferentiableAt ℝ (f i) x)
    (hgraph : ∀ i x, ((f i x).1 = (Pi.single i (1 : ℝ) : Fin k → ℝ)))
    (hinv : InvolutiveDistribution f) :
    ∀ i j x, lieBracket (f i) (f j) x = 0 := by
  have hfirst : ∀ (m : Fin k) (y : (Fin k → ℝ) × Y) (v : (Fin k → ℝ) × Y),
      ((fderiv ℝ (f m) y v).1 = 0) := by
    intro m y v
    have hcomp : (fun z ↦ ((f m z).1)) = fun _ ↦ (Pi.single m (1 : ℝ) : Fin k → ℝ) :=
      funext fun z ↦ hgraph m z
    have h1 : HasFDerivAt (fun z : (Fin k → ℝ) × Y ↦ ((f m z).1))
        (0 : ((Fin k → ℝ) × Y) →L[ℝ] (Fin k → ℝ)) y := by
      rw [hcomp]
      exact hasFDerivAt_const _ _
    have hchain : HasFDerivAt (fun z : (Fin k → ℝ) × Y ↦ ((f m z).1))
        ((ContinuousLinearMap.fst ℝ (Fin k → ℝ) Y).comp (fderiv ℝ (f m) y)) y :=
      (ContinuousLinearMap.fst ℝ (Fin k → ℝ) Y).hasFDerivAt.comp y (hf m y).hasFDerivAt
    have heq : (ContinuousLinearMap.fst ℝ (Fin k → ℝ) Y).comp
        (fderiv ℝ (f m) y) = 0 := by
      rw [← hchain.fderiv, h1.fderiv]
    have happ := congrArg
      (fun L : ((Fin k → ℝ) × Y) →L[ℝ] (Fin k → ℝ) ↦ L v) heq
    simpa using happ
  intro i j x
  have hproj : ((lieBracket (f i) (f j) x).1 : Fin k → ℝ) = 0 := by
    rw [lieBracket_apply]
    have e1 := hfirst j x (f i x)
    have e2 := hfirst i x (f j x)
    simp only [Prod.fst_sub, e1, e2, sub_self]
  have hmem := hinv i j x
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hpush : (ContinuousLinearMap.fst ℝ (Fin k → ℝ) Y)
      (c.sum fun m a ↦ a • f m x)
      = c.sum (fun m a ↦ a • (Pi.single m (1 : ℝ) : Fin k → ℝ)) := by
    change (ContinuousLinearMap.fst ℝ (Fin k → ℝ) Y)
      (∑ m ∈ c.support, (c m) • f m x)
      = ∑ m ∈ c.support, (c m) • (Pi.single m (1 : ℝ) : Fin k → ℝ)
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [map_smul]
    congr 1
    exact hgraph m x
  have hfst0 : (ContinuousLinearMap.fst ℝ (Fin k → ℝ) Y)
      (lieBracket (f i) (f j) x) = 0 := hproj
  have hcsum : c.sum (fun m a ↦ a • (Pi.single m (1 : ℝ) : Fin k → ℝ)) = 0 := by
    have harg := congrArg (ContinuousLinearMap.fst ℝ (Fin k → ℝ) Y) hc
    rw [hpush, hfst0] at harg
    exact harg
  have hbasis_eq : (fun m : Fin k ↦ (Pi.single m (1 : ℝ) : Fin k → ℝ))
      = ⇑(Pi.basisFun ℝ (Fin k)) := by
    funext m
    rw [Pi.basisFun_apply]
  have hindep : LinearIndependent ℝ
      (fun m : Fin k ↦ (Pi.single m (1 : ℝ) : Fin k → ℝ)) := by
    rw [hbasis_eq]
    exact (Pi.basisFun ℝ (Fin k)).linearIndependent
  rw [linearIndependent_iff] at hindep
  have hc0 : c = 0 := by
    apply hindep
    rw [Finsupp.linearCombination_apply]
    exact hcsum
  rw [← hc, hc0]
  simp

/-! # G8: Frobenius theorem — curvature, compatibility, and the involutivity bridge

This section ports the clean statements of Igor Khavkine and Jan Růžička's partial
formalization of the Frobenius theorem (`github.com/igorkhavkine/lean-dg-frobenius`,
branch `honza`, Apache 2.0). The ported declarations are `Curvature`,
`TotalFderivCompat`, and `frobeniusTheorem`; each carries a docstring noting the port.
Authors of the ported statements: Igor Khavkine, Jan Růžička. No originality is
claimed for the ported material.

The bridge lemma `involutive_iff_totalFderivCompat` (proved here) connects our
formulation (involutivity via `lieBracket`, following Krener, *Encyclopedia of
Systems and Control*, 2nd ed., and Sontag, *Mathematical Control Theory*, 2nd ed.,
Ch. 4 §4.4) to theirs (vanishing of `Curvature`): for the graph distribution spanned
by the vector fields `X_d (x, z) = (d, g (x, z) d)`, involutivity holds if and only
if the curvature tensor vanishes.
-/

section FrobeniusG8

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The Frobenius integrability tensor ("curvature") of a graph connection `g`.

Statement ported from Khavkine–Růžička, lean-dg-frobenius (Apache 2.0).
Here `g` is the "connection" (the distribution as a graph: the subspace at `(x, z)`
is `{(d, g (x, z) d) : d ∈ X}`); `p = (x, z)` and `d1 d2 : X` are horizontal
directions. See also Krener, *Encyclopedia of Systems and Control*, 2nd ed., and
Sontag, *Mathematical Control Theory*, 2nd ed., Ch. 4 §4.4. -/
noncomputable def Curvature (g : X × Y → X →L[ℝ] Y) (p : X × Y) (d1 d2 : X) : Y :=
  fderiv ℝ g p (d1, 0) d2 + fderiv ℝ g p (0, g p d1) d2 -
    (fderiv ℝ g p (d2, 0) d1 + fderiv ℝ g p (0, g p d2) d1)

/-- The flatness/involutivity condition: vanishing of `Curvature` over `U`.

Statement ported from Khavkine–Růžička, lean-dg-frobenius (Apache 2.0). See also
Krener, *Encyclopedia of Systems and Control*, 2nd ed., and Sontag,
*Mathematical Control Theory*, 2nd ed., Ch. 4 §4.4. -/
def TotalFderivCompat (g : X × Y → X →L[ℝ] Y) (U : Set (X × Y)) : Prop :=
  ∀ p ∈ U, ∀ d1 d2 : X, Curvature g p d1 d2 = 0

/-- The graph vector field in horizontal direction `d`: `X_d (x, z) = (d, g (x, z) d)`.
The graph distribution is spanned by these fields as `d` ranges over `X`. -/
def graphField (g : X × Y → X →L[ℝ] Y) (d : X) : X × Y → X × Y :=
  fun p => (d, g p d)

/-- The graph frame: the finite family of graph fields over the coordinate directions
`Pi.single i 1` of `Fin k → ℝ`, used to phrase involutivity of the graph distribution
with our `InvolutiveDistribution`. -/
noncomputable def graphFrame {k : ℕ} (g : (Fin k → ℝ) × Y → (Fin k → ℝ) →L[ℝ] Y) :
    Fin k → ((Fin k → ℝ) × Y) → ((Fin k → ℝ) × Y) :=
  fun i => graphField g (Pi.single i (1 : ℝ))

/-- A graph field is differentiable wherever `g` is. -/
theorem graphField_differentiableAt (g : X × Y → X →L[ℝ] Y) (d : X) (p : X × Y)
    (hg : DifferentiableAt ℝ g p) : DifferentiableAt ℝ (graphField g d) p :=
  (differentiableAt_const d).prodMk
    ((ContinuousLinearMap.apply ℝ Y d).differentiableAt.comp p hg)

/-- The Fréchet derivative of a graph field: the horizontal component is constant, so
its derivative vanishes, and the vertical component is evaluation of `fderiv g`. -/
theorem graphField_fderiv_apply (g : X × Y → X →L[ℝ] Y) (d : X) (p v : X × Y)
    (hg : DifferentiableAt ℝ g p) :
    fderiv ℝ (graphField g d) p v = (0, fderiv ℝ g p v d) := by
  have h1 : HasFDerivAt (fun _ : X × Y => d) (0 : (X × Y) →L[ℝ] X) p :=
    hasFDerivAt_const d p
  have h2 : HasFDerivAt (fun p : X × Y => g p d)
      ((ContinuousLinearMap.apply ℝ Y d).comp (fderiv ℝ g p)) p :=
    (ContinuousLinearMap.apply ℝ Y d).hasFDerivAt.comp p hg.hasFDerivAt
  have h := h1.prodMk h2
  have hder := h.fderiv
  rw [show (fun x : X × Y => ((fun _ : X × Y => d) x, (fun p : X × Y => g p d) x)) =
      graphField g d from rfl] at hder
  rw [hder]
  simp only [ContinuousLinearMap.prod_apply, zero_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]

/-- The Lie bracket of two graph fields is vertical, with vertical component exactly
`Curvature`: the horizontal parts cancel since the horizontal components are constant.
This computation is the bridge between our `lieBracket` formulation (Krener; Sontag
Ch. 4 §4.4) and the Khavkine–Růžička curvature tensor (statement ported from
Khavkine–Růžička, lean-dg-frobenius, Apache 2.0). -/
theorem bracket_graphField (g : X × Y → X →L[ℝ] Y) (d1 d2 : X) (p : X × Y)
    (hg : DifferentiableAt ℝ g p) :
    lieBracket (graphField g d1) (graphField g d2) p = (0, Curvature g p d1 d2) := by
  rw [lieBracket_apply, graphField_fderiv_apply g d2 _ _ hg,
    graphField_fderiv_apply g d1 _ _ hg]
  show (0, fderiv ℝ g p (d1, g p d1) d2) - (0, fderiv ℝ g p (d2, g p d2) d1) =
    (0, Curvature g p d1 d2)
  have s1 : ((d1, g p d1) : X × Y) = (d1, 0) + (0, g p d1) := by
    rw [Prod.mk_add_mk, add_zero, zero_add]
  have s2 : ((d2, g p d2) : X × Y) = (d2, 0) + (0, g p d2) := by
    rw [Prod.mk_add_mk, add_zero, zero_add]
  rw [s1, s2]
  simp only [map_add, add_apply]
  unfold Curvature
  simp only [Prod.mk_sub_mk, sub_self]

/-- `Curvature` is additive in its first horizontal argument. -/
theorem Curvature_add_left (g : X × Y → X →L[ℝ] Y) (p : X × Y) (d1 d1' d2 : X) :
    Curvature g p (d1 + d1') d2 = Curvature g p d1 d2 + Curvature g p d1' d2 := by
  unfold Curvature
  have h1 : ((d1 + d1', (0 : Y)) : X × Y) = (d1, 0) + (d1', 0) := by
    rw [Prod.mk_add_mk, add_zero]
  have h2 : g p (d1 + d1') = g p d1 + g p d1' := map_add _ _ _
  have h3 : ((0 : X), g p (d1 + d1')) = (0, g p d1) + (0, g p d1') := by
    rw [h2, Prod.mk_add_mk, add_zero]
  rw [h1, h3]
  simp only [map_add, add_apply]
  abel

/-- `Curvature` is additive in its second horizontal argument. -/
theorem Curvature_add_right (g : X × Y → X →L[ℝ] Y) (p : X × Y) (d1 d2 d2' : X) :
    Curvature g p d1 (d2 + d2') = Curvature g p d1 d2 + Curvature g p d1 d2' := by
  unfold Curvature
  have h1 : ((d2 + d2', (0 : Y)) : X × Y) = (d2, 0) + (d2', 0) := by
    rw [Prod.mk_add_mk, add_zero]
  have h2 : g p (d2 + d2') = g p d2 + g p d2' := map_add _ _ _
  have h3 : ((0 : X), g p (d2 + d2')) = (0, g p d2) + (0, g p d2') := by
    rw [h2, Prod.mk_add_mk, add_zero]
  rw [h1, h3]
  simp only [map_add, add_apply]
  abel

/-- `Curvature` is homogeneous in its first horizontal argument. -/
theorem Curvature_smul_left (g : X × Y → X →L[ℝ] Y) (p : X × Y) (c : ℝ) (d1 d2 : X) :
    Curvature g p (c • d1) d2 = c • Curvature g p d1 d2 := by
  unfold Curvature
  have h1 : ((c • d1, (0 : Y)) : X × Y) = c • (d1, 0) := by
    rw [Prod.smul_mk, smul_zero]
  have h2 : g p (c • d1) = c • g p d1 := map_smul _ _ _
  have h3 : ((0 : X), g p (c • d1)) = c • ((0, g p d1) : X × Y) := by
    rw [h2, Prod.smul_mk, smul_zero]
  rw [h1, h3]
  simp only [map_smul, smul_apply, smul_add, smul_sub]

/-- `Curvature` is homogeneous in its second horizontal argument. -/
theorem Curvature_smul_right (g : X × Y → X →L[ℝ] Y) (p : X × Y) (c : ℝ) (d1 d2 : X) :
    Curvature g p d1 (c • d2) = c • Curvature g p d1 d2 := by
  unfold Curvature
  have h1 : ((c • d2, (0 : Y)) : X × Y) = c • (d2, 0) := by
    rw [Prod.smul_mk, smul_zero]
  have h2 : g p (c • d2) = c • g p d2 := map_smul _ _ _
  have h3 : ((0 : X), g p (c • d2)) = c • ((0, g p d2) : X × Y) := by
    rw [h2, Prod.smul_mk, smul_zero]
  rw [h1, h3]
  simp only [map_smul, smul_apply, smul_add, smul_sub]

/-- `Curvature` vanishes when its first horizontal argument is zero. -/
theorem Curvature_zero_left (g : X × Y → X →L[ℝ] Y) (p : X × Y) (d2 : X) :
    Curvature g p 0 d2 = 0 := by
  unfold Curvature
  have z1 : ((0 : X), (0 : Y)) = (0 : X × Y) := rfl
  have z2 : g p (0 : X) = 0 := map_zero _
  rw [z1, z2, z1]
  simp

/-- `Curvature` vanishes when its second horizontal argument is zero. -/
theorem Curvature_zero_right (g : X × Y → X →L[ℝ] Y) (p : X × Y) (d1 : X) :
    Curvature g p d1 0 = 0 := by
  unfold Curvature
  have z1 : ((0 : X), (0 : Y)) = (0 : X × Y) := rfl
  have z2 : g p (0 : X) = 0 := map_zero _
  rw [z2, z1]
  simp

/-- `Curvature` distributes over finite sums in its first horizontal argument. -/
theorem Curvature_sum_left {ι : Type*} [DecidableEq ι] (g : X × Y → X →L[ℝ] Y)
    (p : X × Y) (d2 : X) (s : Finset ι) (e : ι → X) :
    Curvature g p (∑ i ∈ s, e i) d2 = ∑ i ∈ s, Curvature g p (e i) d2 := by
  refine Finset.induction_on s ?_ ?_
  · simp [Curvature_zero_left]
  · intro a t hat ih
    rw [Finset.sum_insert hat, Finset.sum_insert hat, Curvature_add_left, ih]

/-- `Curvature` distributes over finite sums in its second horizontal argument. -/
theorem Curvature_sum_right {ι : Type*} [DecidableEq ι] (g : X × Y → X →L[ℝ] Y)
    (p : X × Y) (d1 : X) (s : Finset ι) (e : ι → X) :
    Curvature g p d1 (∑ i ∈ s, e i) = ∑ i ∈ s, Curvature g p d1 (e i) := by
  refine Finset.induction_on s ?_ ?_
  · simp [Curvature_zero_right]
  · intro a t hat ih
    rw [Finset.sum_insert hat, Finset.sum_insert hat, Curvature_add_right, ih]

/-- Involutivity of the graph distribution is equivalent to vanishing curvature.

This bridges our formulation (involutivity via `lieBracket`, following Krener,
*Encyclopedia of Systems and Control*, 2nd ed., and Sontag, *Mathematical Control
Theory*, 2nd ed., Ch. 4 §4.4) to the Khavkine–Růžička flatness condition
`TotalFderivCompat` (statement ported from Khavkine–Růžička, lean-dg-frobenius,
Apache 2.0). The proof computes `lieBracket` of the graph fields (whose vertical
component is exactly `Curvature` by `bracket_graphField`), uses G3's
`commutingBasis_of_involutive` for the forward direction, and bilinearity of
`Curvature` to pass between coordinate directions and arbitrary horizontal vectors. -/
theorem involutive_iff_totalFderivCompat {k : ℕ}
    (g : (Fin k → ℝ) × Y → (Fin k → ℝ) →L[ℝ] Y)
    (hg : ∀ p, DifferentiableAt ℝ g p) :
    InvolutiveDistribution (graphFrame g) ↔ TotalFderivCompat g Set.univ := by
  constructor
  · intro hinv p _ d1 d2
    have hdiff : ∀ i x, DifferentiableAt ℝ ((graphFrame g) i) x :=
      fun i x => graphField_differentiableAt g _ x (hg x)
    have hgraph : ∀ i x, (((graphFrame g) i x).1 = (Pi.single i (1 : ℝ) : Fin k → ℝ)) :=
      fun i x => rfl
    have hcomm := commutingBasis_of_involutive hdiff hgraph hinv
    have hbasis : ∀ i j (q : (Fin k → ℝ) × Y),
        Curvature g q (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)) = 0 := by
      intro i j q
      have h : lieBracket (graphField g (Pi.single i (1 : ℝ)))
          (graphField g (Pi.single j (1 : ℝ))) q = 0 := hcomm i j q
      rw [bracket_graphField g _ _ q (hg q)] at h
      exact (Prod.mk_eq_zero.mp h).2
    have hexpand : ∀ d : Fin k → ℝ, (∑ i : Fin k, d i • Pi.single i (1 : ℝ)) = d := by
      intro d
      have h := (Pi.basisFun ℝ (Fin k)).sum_repr d
      simpa [Pi.basisFun_repr, Pi.basisFun_apply] using h
    rw [← hexpand d1, Curvature_sum_left]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← hexpand d2, Curvature_sum_right]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Curvature_smul_left, Curvature_smul_right, hbasis i j p, smul_zero, smul_zero]
  · intro hcompat i j x
    have hcurv : Curvature g x (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)) = 0 :=
      hcompat x (Set.mem_univ x) _ _
    have h := bracket_graphField g (Pi.single i (1 : ℝ)) (Pi.single j (1 : ℝ)) x (hg x)
    rw [hcurv] at h
    have h0 : ((0, (0 : Y)) : (Fin k → ℝ) × Y) = 0 := rfl
    rw [h0] at h
    have e1 : graphFrame g i = graphField g (Pi.single i (1 : ℝ)) := rfl
    have e2 : graphFrame g j = graphField g (Pi.single j (1 : ℝ)) := rfl
    rw [e1, e2, h]
    exact (Submodule.span ℝ _).zero_mem

/-- The Frobenius existence theorem (ported target statement).

Statement ported from Khavkine–Růžička, lean-dg-frobenius (Apache 2.0): their
`exists_sol_of_fderiv_compat`, adapted from the `oNormedSpace`/`SmoothFunction`
bundle to plain `[NormedAddCommGroup] [NormedSpace ℝ] [CompleteSpace]`
`[FiniteDimensional]` hypotheses. See also Krener, *Encyclopedia of Systems and
Control*, 2nd ed., and Sontag, *Mathematical Control Theory*, 2nd ed., Ch. 4 §4.4.

NOT proved here — the compatible-PDE integration (Khavkine–Růžička's Lemma 9) and
the simultaneous-rectification route remain the outstanding step. The statement is
recorded as a `Prop`-valued definition so that the target has a name without any
outstanding proof obligation. -/
def frobeniusTheorem : Prop :=
  ∀ (g : X × Y → X →L[ℝ] Y), ContDiff ℝ ⊤ g → TotalFderivCompat g Set.univ →
    ∀ [CompleteSpace X] [CompleteSpace Y] [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]
      (x₀ : X) (z : Y), ∃ (s : Set X) (_ : s ∈ 𝓝 x₀) (w : X → Y),
      ContDiffOn ℝ ⊤ w (interior s) ∧ w x₀ = z ∧
        ∀ x ∈ s, fderivWithin ℝ w (interior s) x = g (x, w x)

end FrobeniusG8

#check @Curvature
#check @TotalFderivCompat
#check @involutive_iff_totalFderivCompat
#check @frobeniusTheorem

