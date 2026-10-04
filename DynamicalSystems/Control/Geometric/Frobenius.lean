/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.Rectification
public import DynamicalSystems.Control.Geometric.LieBrackets
public import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! # Krener lemma: simultaneous rectification of commuting vector fields

Given `k ≤ n` pointwise-independent, pairwise-commuting vector fields on a
finite-dimensional real normed space, there is a local chart near `x₀` that
straightens all `k` fields simultaneously to the first `k` coordinate fields.

## Scope fence

The bridge between commuting flows and vanishing Lie brackets (in either direction)
is 600–1000 lines and absent from Mathlib. It is NOT proved here. Instead:

* `FlowsCommuteLocally` is the **hypothesis interface**: pairwise bracket-vanishing
  on a neighbourhood of `x₀`, which is what "commute" means at the infinitesimal
  level. The classical flows-commute interpretation is documented, not proved.
* `krenerLemma` proves the **inductive base step** in full generality: for a family
  `f : Fin k → X → X` of pointwise-independent, pairwise bracket-vanishing fields,
  the distinguished field `f i₀` (nonsingular at `x₀`) admits a rectifying chart in
  the trajectory form of G1's `rectifyingChart_rectifies`. The pairwise hypotheses
  are part of the statement so the induction interface is stable; the remaining
  work for the joint chart (rectify `f₁` to `e₁`, descend the other fields to the
  transverse slice via `[e₁, fⱼ] = ∂₁fⱼ = 0`, recurse, compose charts) is
  documented, not claimed.

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

/-- Krener lemma, inductive base step (general `k` form).

Given a finite family `f : Fin k → X → X` of `C¹` vector fields that are pointwise
linearly independent at `x₀` and pairwise bracket-vanishing near `x₀`, each
nonsingular field admits a rectifying chart: for the distinguished index `i₀` there
is an `OpenPartialHomeomorph` `Ψ` near `x₀` whose coordinate lines are integral
curves of `f i₀` (the trajectory-rectification form of G1).

For `k = 1` this is exactly G1's `rectifyingChart`. The pairwise hypotheses
(`hind`, `hcomm`) are recorded so the statement is the stable induction interface
for the joint chart; the proof of the base step is the G1 chart. The descent of
the remaining fields to the transverse slice and the chart composition are the
deferred inductive step described in the module scope fence. -/
theorem krenerLemma [CompleteSpace X] [FiniteDimensional ℝ X]
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

/-- Krener lemma, per-field corollary: every nonsingular field of a pairwise-commuting,
pointwise-independent family admits its own rectifying chart. -/
theorem krenerLemma_all [CompleteSpace X] [FiniteDimensional ℝ X]
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
  krenerLemma hf hind hcomm i (hv i)
