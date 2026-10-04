/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.Accessibility
public import DynamicalSystems.Control.Geometric.Rectification
public import DynamicalSystems.Control.Geometric.LocalControllability
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Chow / LARC sufficiency: full rank implies reachable set has nonempty interior

Attribution (binding): this file formalises the **sufficiency** half of the Chow /
Lie algebra rank condition theorem: if the accessibility Lie algebra has full rank `n`
at `x₀`, then the set reachable by piecewise-constant controls has nonempty interior.
The classical references are Krener, "Differential Geometric Methods in Nonlinear
Control", *Encyclopedia of Systems and Control*, 2nd ed., and Sontag, *Mathematical
Control Theory*, 2nd ed., Ch. 4 §4.3 (Theorem 9, p. 156). No originality is claimed;
this is a formalisation of Krener (1971) / Sontag Theorem 9 following the same
open-mapping argument as S7's
`Control/Geometric/LocalControllability.localSurjectivity_of_controllable_linearization`.

## Scope fence

The step "each iterated Lie bracket direction is realised as the derivative (at `t = 0`)
of a finite piecewise-constant flow (a commutator of flows)" is itself a nontrivial lemma:
it is equivalent to the flows-commute / bracket-vanishing bridge, which is 600–1000 lines
and absent from Mathlib. It is therefore taken as explicit hypotheses (`hBracket` and
`hReach` of `chowInterior`) and DOCUMENTED as the deferred bridge there; the `k = 1`
first-order case (the bracket `[fᵢ, fⱼ]` as the `t`-derivative of the 4-segment commutator
flow) is not proved here either.

What IS proved here is the FINAL open-mapping step: given `n` directions (each the
derivative of a piecewise-constant-flow end-point map) spanning `X`, the joint end-point
map `(t₁,…,tₙ) ↦ …` has a surjective strict derivative at the base parameter `0`, hence
`HasStrictFDerivAt.map_nhds_eq_of_surj` gives a neighbourhood of its image point in the
image, so the reachable set has nonempty interior.

Statement fidelity (Sontag, Ch. 4 §4.3, Theorem 9): the classical end-point map `F` has
surjective derivative at a parameter `t⁰` that is generically NON-ZERO, and the anchor
`F(t⁰)` is a REACHABLE point, NOT the initial state `x₀`. This formalisation
reparametrises the anchor to the base parameter `0` and takes the derivative-range
condition as the explicit hypothesis `hBracket`.

The *necessity* direction (rank `< n` implies empty interior, via Frobenius foliations)
is a separate deferred item and is NOT attempted here.

The reachable set is formalised as the union over all horizons (no time parameter `T`);
the classical refinement "for some (small) `T`" (bounding the total switching time) is
not tracked.

## Main definitions

* `reachableByPiecewiseConstant`: the set of states reachable from `x₀` by concatenating
  finitely many integral-curve segments of the control vector fields `f 0, …, f (m-1)`.
  Each segment is witnessed by a curve `γ` with `γ 0`, `γ T` the segment endpoints and
  `γ'(t) = fᵢ (γ t)` on the segment; in practice these curves are supplied by
  `Rectification.localFlow` (see `localFlow_segment_hasDerivAt`).

## Main results

* `self_mem_reachableByPiecewiseConstant`: the starting point is reachable.
* `localFlow_segment_hasDerivAt`: a local-flow curve satisfies the single-segment
  trajectory predicate on its domain (the `Rectification.localFlow` reuse).
* `chowInterior`: THE theorem — full accessibility rank at `x₀`, plus the deferred
  bracket-direction bridge (`hBracket`, `hReach`), implies the reachable set has
  nonempty interior.
-/

@[expose] public section

open Filter Set
open scoped Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {m : ℕ}

/-- The set of states reachable from `x₀` by piecewise-constant controls using the vector
fields `f 0, …, f (m-1)` as control directions: `y` is reachable if there is a finite
chain of points from `x₀` to `y` where each consecutive pair is joined by an integral
curve segment `γ` of one of the fields (`γ'(t) = fᵢ (γ t)` on the segment between `0`
and `T`). This is the union over all horizons; the classical "within (small) time `T`"
refinement is not tracked. In practice each segment curve is a local-flow line
`t ↦ Rectification.localFlow hf t x` (see `localFlow_segment_hasDerivAt`, which shows
such curves satisfy the segment predicate on the flow domain).

Caveat: this is NOT the set reachable by arbitrary piecewise-constant controls of the
driftless system `ẋ = Σ uᵢ fᵢ`. It is the Chow orbit of the individual flows: a
concatenation of integral curves of the individual generators `fᵢ`, one generator per
segment and with reverse time allowed (`T` may be negative), matching the `F`
construction in Sontag, Ch. 4 §4.3. -/
def reachableByPiecewiseConstant (f : Fin m → X → X) (x₀ : X) : Set X :=
  { y | ∃ n : ℕ, ∃ pts : Fin (n + 1) → X, ∃ idx : Fin n → Fin m,
    pts 0 = x₀ ∧
      pts (Fin.last n) = y ∧
      ∀ k : Fin n, ∃ T : ℝ, ∃ γ : ℝ → X,
        γ 0 = pts k.castSucc ∧ γ T = pts k.succ ∧
        ∀ t ∈ Set.uIcc 0 T, HasDerivAt γ (f (idx k) (γ t)) t }

/-- The starting point is reachable from itself (the empty concatenation). -/
theorem self_mem_reachableByPiecewiseConstant (f : Fin m → X → X) (x₀ : X) :
    x₀ ∈ reachableByPiecewiseConstant f x₀ :=
  ⟨0, fun _ ↦ x₀, fun k ↦ Fin.elim0 k, rfl, rfl, fun k ↦ Fin.elim0 k⟩

/-- A local-flow curve `s ↦ localFlow hf s z` satisfies the single-segment trajectory
predicate on its whole time domain: it is an integral curve of `g` at every point of the
segment `uIcc 0 T` (Sontag, Ch. 4 §4.2; the flow property behind `Rectification`,
whose `LocalFlowData.ϕ_hasDerivAt` is reused here). This is the fact that lets the
abstract trajectory segments in `reachableByPiecewiseConstant` be inhabited by the
concrete local flows `Rectification.localFlow`. -/
theorem localFlow_segment_hasDerivAt [CompleteSpace X]
    (g : X → X) (z : X) (hg : ContDiffAt ℝ 1 g z)
    {T : ℝ} (hT : T ∈ Set.Ioo (-localFlowTime hg) (localFlowTime hg)) :
    ∀ t ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun s ↦ localFlow hg s z) (g (localFlow hg t z)) t := by
  obtain ⟨hTlo, hThi⟩ := Set.mem_Ioo.mp hT
  intro t ht
  have hIoo : t ∈ Set.Ioo (-localFlowTime hg) (localFlowTime hg) := by
    rw [Set.mem_uIcc] at ht
    rw [Set.mem_Ioo]
    rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  exact (getLocalFlowData hg).ϕ_hasDerivAt t hIoo z
    (Metric.mem_closedBall_self (le_of_lt (getLocalFlowData hg).hr))

/-- **Chow / LARC sufficiency (Krener 1971; Sontag, Ch. 4 §4.3, Theorem 9, p. 156):**
if the accessibility distribution of the control fields has full rank at `x₀`, then the
set reachable by piecewise-constant controls has nonempty interior.

The classical proof: full rank means `n` iterated Lie brackets of the `f i` evaluate to a
basis of `X` at `x₀`; each iterated bracket direction is the derivative of a finite
piecewise-constant flow (a "commutator of flows"). Sontag's end-point map `F` then has
surjective derivative at a parameter `t⁰` that is generically NON-ZERO, and the image
`F(t⁰)` is a REACHABLE point — not the initial state `x₀`; by the inverse-function /
open-mapping theorem the image of `F` contains a neighbourhood of that reachable anchor.
This formalisation proves the FINAL open-mapping step, reparametrises the classical
anchor to the base parameter `0`, and takes the bracket-direction bridge as explicit
hypotheses:

* `hBracket` (deferred bridge, algebraic half): every accessibility direction lies in the
  range of the end-point map derivative — i.e. the iterated-bracket directions spanning
  `Δ(x₀)` are realised as derivatives at `0` of piecewise-constant-flow curves. The
  `k = 1` instance is the identity `[fᵢ, fⱼ] = d/dt|₀` (4-segment commutator flow); the
  general case iterates it. Together with `hRank` (`Δ(x₀) = ⊤`) this makes `L` surjective.
* `hReach` (deferred bridge, dynamical half): the end-point map lands in the reachable
  set near `0` — i.e. each flow-composition curve is a genuine piecewise-constant
  trajectory (a concatenation of `Rectification.localFlow` segments, cf.
  `localFlow_segment_hasDerivAt`).

Given these, `HasStrictFDerivAt.map_nhds_eq_of_surj` (the same tool S7's
`localSurjectivity_of_controllable_linearization` used for the linearization) yields a
neighbourhood of `E 0` contained in the reachable set, hence nonempty interior. The
necessity direction (via Frobenius foliations) is deferred and not attempted here. -/
theorem chowInterior [CompleteSpace X] [FiniteDimensional ℝ X]
    (f : Fin m → X → X) (x₀ : X)
    (hRank : lieAlgebraRankCondition (Set.range f) x₀)
    (E : (Fin (Module.finrank ℝ X) → ℝ) → X)
    (L : (Fin (Module.finrank ℝ X) → ℝ) →L[ℝ] X)
    (hE : HasStrictFDerivAt E L 0)
    (hBracket : accessibilityDistribution (Set.range f) x₀ ≤ L.range)
    (hReach : ∀ᶠ t in 𝓝 (0 : Fin (Module.finrank ℝ X) → ℝ),
      E t ∈ reachableByPiecewiseConstant f x₀) :
    (interior (reachableByPiecewiseConstant f x₀)).Nonempty := by
  have hfin : Module.finrank ℝ (accessibilityDistribution (Set.range f) x₀)
      = Module.finrank ℝ X :=
    (lieAlgebraRankCondition_iff_finrank _ _).mp hRank
  have hLrange : L.range = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ((Submodule.finrank_le _).antisymm ?_)
    calc Module.finrank ℝ X
        = Module.finrank ℝ (accessibilityDistribution (Set.range f) x₀) := hfin.symm
      _ ≤ Module.finrank ℝ L.range := Submodule.finrank_mono hBracket
  have hmap : Filter.map E (𝓝 (0 : Fin (Module.finrank ℝ X) → ℝ)) = 𝓝 (E 0) :=
    hE.map_nhds_eq_of_surj hLrange
  have hmem : reachableByPiecewiseConstant f x₀ ∈ 𝓝 (E 0) := by
    rw [← hmap, Filter.mem_map]
    exact hReach
  exact ⟨E 0, mem_interior_iff_mem_nhds.mpr hmem⟩
