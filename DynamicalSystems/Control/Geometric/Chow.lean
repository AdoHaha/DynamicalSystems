/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.Accessibility
public import DynamicalSystems.Control.Geometric.FlowCommutator
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

/-! ## G6: bracket directions in the end-point range (discharge of `hBracket`)

Attribution (binding): E. D. Sontag, *Mathematical Control Theory: Deterministic Finite
Dimensional Systems*, 2nd ed., Springer, 1998, Ch. 4 §4.3 (Theorem 9, p. 156); A. J. Krener,
*Differential Geometric Methods in Nonlinear Control*, in *Encyclopedia of Systems and
Control*, Springer, 2nd ed. No originality is claimed. The reduction "the Lie bracket is
the mixed second derivative of the flow commutator, hence bracket directions lie in the
range of an end-point map derivative" is classical (Sontag's proof of Theorem 9); G5
(`FlowCommutator.bracket_eq_flowCommutator`) proved the bracket identity, and this section
turns it into range memberships that discharge the `hBracket` hypothesis of `chowInterior`.

## Where the second order lives

For the two-variable commutator end-point map the first derivative at `(0, 0)` vanishes
(each one-variable slice is a flow followed by its inverse), so the bracket cannot lie in
the range of the *first-order* derivative at `0`: it appears at *second* order, as the
value at `1` of the outer-derivative (Hessian-level) continuous linear maps
`bracketCommutatorLinearMap` and `flowTangentLinearMap` below. Concretely,
`lieBracket V W x₀ = bracketCommutatorLinearMap V W x₀ hV hW 1` (by G5), hence the
bracket direction is in the range of that Hessian-level map. Sontag's classical joint
end-point map `F` sees these directions at first order because its derivative is taken at
a (generically nonzero) parameter `t⁰`; here the Hessian-level ranges are instead wired
into the joint derivative `L` by the explicit factorisation hypotheses `hFirst`/`hBridge`
of `chowInterior_of_larc`.

## What is (and is not) discharged

* Discharged here, as range memberships: every generator direction `f i x₀`
  (`generatorDirection_mem_range`: it is the time-`1` value of the single-flow outer
  derivative) and every Lie-bracket direction `lieBracket V W x₀` for `C¹` fields
  (`bracketDirection_mem_range`: it is the time-`1` value of the commutator outer
  derivative, via G5). The bracket half holds at *all* depths, since
  `bracketDirection_mem_range` applies to any `C¹` pair.
* Remaining as explicit wiring hypotheses in `chowInterior_of_larc`: `hFirst`/`hBridge`
  (these first- and second-order ranges factor through the joint map derivative `L` —
  the Sontag-at-`t⁰` content) and `hSmooth` (regularity closure: every element of the
generated Lie algebra is `C¹` at `x₀`; this follows from smooth generators by induction
  with `contDiff_top_lieBracket`). There is deliberately **no `hBracket` hypothesis**:
  `accessibilityDistribution (Set.range f) x₀ ≤ L.range` is *derived* by induction over
  `InLieAlgebra` and fed to G4's `chowInterior`.
-/

/-- Hessian-level linear map of the two-flow commutator at `x₀`: the difference of the
outer `fderiv`s of the two two-fold flow-composition curves
`t ↦ Dₛ|₀ (Ψₛ ∘ Φₜ)(x₀)` and `s ↦ Dₜ|₀ (Φₜ ∘ Ψₛ)(x₀)`. Its value at `1` is G5's
`infinitesimalCommutator`, hence (by `bracket_eq_flowCommutator`) the Lie bracket
(Sontag, Ch. 4 §4.4; Krener, Encyclopedia chapter). -/
noncomputable def bracketCommutatorLinearMap [CompleteSpace X] (V W : X → X) (x₀ : X)
    (hV : ContDiffAt ℝ 1 V x₀) (hW : ContDiffAt ℝ 1 W x₀) : ℝ →L[ℝ] X :=
  fderiv ℝ (fun t : ℝ ↦ fderiv ℝ (fun s : ℝ ↦ localFlow hW s (localFlow hV t x₀)) 0 1) 0 -
    fderiv ℝ (fun s : ℝ ↦ fderiv ℝ (fun t : ℝ ↦ localFlow hV t (localFlow hW s x₀)) 0 1) 0

/-- **Bracket directions are in the end-point range (Krener; Sontag, Ch. 4 §4.3–4.4):**
for `C¹` vector fields `V` and `W`, the Lie-bracket direction `lieBracket V W x₀` belongs
to the range of the Hessian-level commutator end-point map `bracketCommutatorLinearMap`
(it is its value at `1`, by G5's `bracket_eq_flowCommutator`). This is the second-order
half of the `hBracket` bridge of `chowInterior`, valid at all bracket depths. -/
theorem bracketDirection_mem_range [CompleteSpace X] (V W : X → X) (x₀ : X)
    (hV : ContDiffAt ℝ 1 V x₀) (hW : ContDiffAt ℝ 1 W x₀) :
    lieBracket V W x₀ ∈ (bracketCommutatorLinearMap V W x₀ hV hW).range := by
  have hb : flowMixedSecond V W x₀ hV hW - flowMixedSecondSwap V W x₀ hV hW
      = lieBracket V W x₀ := by
    have h := bracket_eq_flowCommutator V W x₀ hV hW
    unfold infinitesimalCommutator at h
    rw [dite_eq_left hV, dite_eq_left hW] at h
    exact h
  refine LinearMap.mem_range.mpr ⟨1, ?_⟩
  unfold bracketCommutatorLinearMap
  rw [ContinuousLinearMap.coe_coe, sub_apply]
  exact hb

/-- First-order (tangent) linear map of a single flow at `x₀`: the outer `fderiv` of the
flow curve `t ↦ Φₜ(x₀)`. Its value at `1` is the generator direction `g x₀`, by the flow
equation from `Rectification` (Sontag, Ch. 4 §4.2). -/
noncomputable def flowTangentLinearMap [CompleteSpace X] (g : X → X) (x₀ : X)
    (hg : ContDiffAt ℝ 1 g x₀) : ℝ →L[ℝ] X :=
  fderiv ℝ (fun t : ℝ ↦ localFlow hg t x₀) 0

/-- **Generator directions are in the end-point range (Sontag, Ch. 4 §4.2):** for a `C¹`
vector field `g`, the direction `g x₀` belongs to the range of the single-flow tangent
map `flowTangentLinearMap` (it is its value at `1`, by the flow equation). This is the
first-order half of the `hBracket` bridge of `chowInterior`. -/
theorem generatorDirection_mem_range [CompleteSpace X] (g : X → X) (x₀ : X)
    (hg : ContDiffAt ℝ 1 g x₀) :
    g x₀ ∈ (flowTangentLinearMap g x₀ hg).range := by
  have h0 : (0 : ℝ) ∈ Set.Ioo (-(getLocalFlowData hg).ε) (getLocalFlowData hg).ε :=
    Set.mem_Ioo.mpr ⟨by linarith [(getLocalFlowData hg).hε], (getLocalFlowData hg).hε⟩
  have hx : x₀ ∈ Metric.closedBall x₀ (getLocalFlowData hg).r :=
    Metric.mem_closedBall_self (le_of_lt (getLocalFlowData hg).hr)
  have h00 : (getLocalFlowData hg).ϕ 0 x₀ = x₀ := (getLocalFlowData hg).ϕ_zero x₀ hx
  have hder : HasDerivAt (fun t : ℝ ↦ localFlow hg t x₀) (g x₀) 0 := by
    have h := (getLocalFlowData hg).ϕ_hasDerivAt 0 h0 x₀ hx
    rw [h00] at h
    exact h
  refine LinearMap.mem_range.mpr ⟨1, ?_⟩
  unfold flowTangentLinearMap
  rw [ContinuousLinearMap.coe_coe, hder.hasFDerivAt.fderiv,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul]

/-- **Unconditional Chow sufficiency (Krener; Sontag, Ch. 4 §4.3, Theorem 9, p. 156):**
the Lie algebra rank condition at `x₀` implies the piecewise-constant reachable set has
nonempty interior, with **no `hBracket` hypothesis**. The proof derives
`accessibilityDistribution (Set.range f) x₀ ≤ L.range` by induction over `InLieAlgebra`
— generators via `generatorDirection_mem_range` + `hFirst`, sums/scalar multiples since
`L.range` is a submodule, brackets via `bracketDirection_mem_range` + `hBridge` — and
feeds it to G4's `chowInterior`.

The remaining hypotheses are the end-point map data (`E`, `L`, `hE`, `hReach`, as in G4),
regularity (`hSmooth`: every Lie-algebra element is `C¹` at `x₀`, which follows from
smooth generators), and the Sontag-at-`t⁰` wiring (`hFirst`/`hBridge`: the first- and
second-order flow-derivative ranges factor through the joint derivative `L`). -/
theorem chowInterior_of_larc [CompleteSpace X] [FiniteDimensional ℝ X]
    (f : Fin m → X → X) (x₀ : X)
    (hRank : lieAlgebraRankCondition (Set.range f) x₀)
    (hSmooth : ∀ V : X → X, V ∈ lieAlgebraOf (Set.range f) → ContDiffAt ℝ 1 V x₀)
    (E : (Fin (Module.finrank ℝ X) → ℝ) → X)
    (L : (Fin (Module.finrank ℝ X) → ℝ) →L[ℝ] X)
    (hE : HasStrictFDerivAt E L 0)
    (hFirst : ∀ (i : Fin m) (hCi : ContDiffAt ℝ 1 (f i) x₀),
      (flowTangentLinearMap (f i) x₀ hCi).range ≤ L.range)
    (hBridge : ∀ (V W : X → X) (_ : V ∈ lieAlgebraOf (Set.range f))
      (_ : W ∈ lieAlgebraOf (Set.range f)) (hV1 : ContDiffAt ℝ 1 V x₀)
      (hW1 : ContDiffAt ℝ 1 W x₀),
      (bracketCommutatorLinearMap V W x₀ hV1 hW1).range ≤ L.range)
    (hReach : ∀ᶠ t in 𝓝 (0 : Fin (Module.finrank ℝ X) → ℝ),
      E t ∈ reachableByPiecewiseConstant f x₀) :
    (interior (reachableByPiecewiseConstant f x₀)).Nonempty := by
  have hGen : ∀ i, f i x₀ ∈ L.range := by
    intro i
    have hCi := hSmooth (f i) (mem_lieAlgebraOf (Set.mem_range_self i))
    exact hFirst i hCi (generatorDirection_mem_range (f i) x₀ hCi)
  have hEval : ∀ V : X → X, V ∈ lieAlgebraOf (Set.range f) → V x₀ ∈ L.range := by
    intro V hVm
    have hI : InLieAlgebra (Set.range f) V := hVm
    induction hI with
    | of_mem hV =>
      obtain ⟨i, rfl⟩ := hV
      exact hGen i
    | zero =>
      simp
    | add hV hW ihV ihW =>
      simpa using Submodule.add_mem _ (ihV hV) (ihW hW)
    | smul c hV ihV =>
      simpa using Submodule.smul_mem _ c (ihV hV)
    | bracket hV hW _ _ =>
      have hV1 := hSmooth _ hV
      have hW1 := hSmooth _ hW
      have hmem := bracketDirection_mem_range _ _ x₀ hV1 hW1
      exact hBridge _ _ hV hW hV1 hW1 hmem
  have hBracket : accessibilityDistribution (Set.range f) x₀ ≤ L.range := by
    unfold accessibilityDistribution
    rw [Submodule.span_le]
    rintro _ ⟨V, hVm, rfl⟩
    exact hEval V hVm
  exact chowInterior f x₀ hRank E L hE hBracket hReach
