/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.Rectification
public import DynamicalSystems.Control.Geometric.LieBrackets
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

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
