/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.LieBrackets
public import DynamicalSystems.Control.Geometric.Rectification
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! # The Lie bracket as the infinitesimal commutator of flows

This file formalises the classical identity: the Lie bracket of two vector
fields is the infinitesimal (mixed-second-order) commutator of their flows, i.e. the
`∂²/∂t∂s` derivative at `(0, 0)` of the difference of the two flow compositions. This
identifies the value of the mixed second derivative — a prerequisite for, but not by
itself a discharge of, the bracket-direction bridge used by `Chow.chowInterior`
(which additionally needs the `k`-fold-bracket-to-flow-composition wiring).

## Attribution

This identity is classical; no originality is claimed:

* E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional
  Systems*, 2nd ed., Springer, 1998, Ch. 4 §4.4 (the `Ad` operator and Lemma 4.4.2,
  `∂ₜ Ad_{tX}Y = Ad_{tX}[X,Y]`; cf. Exercise 4.2.6 for the four-fold flow commutator).
* A. J. Krener, *Differential Geometric Methods in Nonlinear Control*, in
  *Encyclopedia of Systems and Control*, Springer, 2015.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012,
  Ch. 9 and Ch. 20 (flows and the Lie derivative; the `∂²/∂t∂s` flow-commutator
  computation).

## Scope and conventions

We work locally on a complete real normed space `X` (flat, at a basepoint
`x₀`), with the local flows `Rectification.localFlow` of `C¹` vector fields. The
definition we formalise is the difference of the two mixed second derivatives
`∂²/∂t∂s|₍₀,₀₎ (Ψₛ ∘ Φₜ)(x₀) − ∂²/∂s∂t|₍₀,₀₎ (Φₜ ∘ Ψₛ)(x₀)`, spelling each mixed
partial with Mathlib `fderiv` iterated twice (the diagonal terms of the two
compositions cancel). The four-fold flow commutator `(Φₜ ∘ Ψₛ ∘ Φ₋ₜ ∘ Ψ₋ₛ)(x₀)` has
this difference form as the **negative** of its mixed second derivative at `(0, 0)`:
reversing the order of the two flows negates the bracket. (The swapped ordering
`(Ψₛ ∘ Φₜ ∘ Ψ₋ₛ ∘ Φ₋ₜ)(x₀)` has the opposite sign.)

## A remark on the differentiation order

The computation needs, for each composition, one time-jet of each flow only: for
fixed `t`, the curve `s ↦ Ψₛ (Φₜ x₀)` has derivative `g (Φₜ x₀)` at `s = 0` (the flow
equation from `Rectification`), and `t ↦ g (Φₜ x₀)` then differentiates at `t = 0` to
`Dg(x₀) (f x₀)` by the ordinary chain rule. In particular the first-order expansion
of the *spatial* derivative of the flow (`DΦₜ = id + t • Df + o(t)`, the baby
variational equation, which is not in Mathlib) is not needed in this differentiation
order, so the main theorem below takes no variational hypothesis. The `t = 0` case of
that expansion (`DΦ₀ = id`) is recorded separately as `flow_deriv_at_zero`.

## Main definitions

* `infinitesimalCommutator`: the mixed second derivative
  `∂²/∂t∂s|₀ (Ψₛ ∘ Φₜ)(x₀) − ∂²/∂s∂t|₀ (Φₜ ∘ Ψₛ)(x₀)` of the flow commutator.

## Main results

* `flow_deriv_at_zero`: the spatial derivative of the local flow at time `0` is the
  identity.
* `flowMixedSecond_eq`, `flowMixedSecondSwap_eq`: each mixed partial computes to the
  expected iterated derivative (`Dg(f)` and `Df(g)` respectively).
* `bracket_eq_flowCommutator`: THE theorem — the infinitesimal commutator equals the
  Lie bracket `Dg(f) − Df(g)` at `x₀`. This is a prerequisite only: it identifies the
  value of the mixed second derivative but does not by itself discharge the `hBracket`
  hypothesis of `Chow.chowInterior` (that needs the `k`-fold-to-flow-composition wiring).
* `lieDerivative_along_flow` (G7): the pullback of `g` along the flow of `f` has time
  derivative `[f, g](x₀)` at `t = 0` (Path B: assumes the `t = 0` variational derivative).
* `flowsCommute_of_bracketVanishing` (G7): `[f, g] = 0` ⇒ the local flows commute near `x₀`
  (Path B: assumes the transported spatial variational facts; the integration argument is
  fully proved). See the G7 section at the end of the file.
-/

@[expose] public section

open Filter
open scoped Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- First mixed second derivative of the two-flow composition: for `C¹` fields `f` and
`g` with local flows `Φ` and `Ψ`, this is `∂²/∂t∂s|₍₀,₀₎ (Ψₛ ∘ Φₜ)(x₀)`, spelled as
`fderiv` iterated twice (Sontag, Ch. 4 §4.4; Lee, Ch. 9 and Ch. 20). -/
noncomputable def flowMixedSecond (f g : X → X) (x₀ : X)
    (hf : ContDiffAt ℝ 1 f x₀) (hg : ContDiffAt ℝ 1 g x₀) : X :=
  fderiv ℝ (fun t : ℝ ↦ fderiv ℝ (fun s : ℝ ↦ localFlow hg s (localFlow hf t x₀)) 0 1) 0 1

/-- Swapped mixed second derivative: `∂²/∂s∂t|₍₀,₀₎ (Φₜ ∘ Ψₛ)(x₀)`, spelled as `fderiv`
iterated twice (Sontag, Ch. 4 §4.4; Lee, Ch. 9 and Ch. 20). -/
noncomputable def flowMixedSecondSwap (f g : X → X) (x₀ : X)
    (hf : ContDiffAt ℝ 1 f x₀) (hg : ContDiffAt ℝ 1 g x₀) : X :=
  fderiv ℝ (fun s : ℝ ↦ fderiv ℝ (fun t : ℝ ↦ localFlow hf t (localFlow hg s x₀)) 0 1) 0 1

/-- The infinitesimal commutator of the flows of `f` and `g` at `x₀`: by definition the
difference `∂²/∂t∂s|₍₀,₀₎ (Ψₛ ∘ Φₜ)(x₀) − ∂²/∂s∂t|₍₀,₀₎ (Φₜ ∘ Ψₛ)(x₀)` of the two
mixed second derivatives of the two-fold flow compositions. This difference form is the
**negative** of the mixed second derivative of the four-fold flow commutator
`(Φₜ ∘ Ψₛ ∘ Φ₋ₜ ∘ Ψ₋ₛ)(x₀)` at `(0, 0)` (Sontag, Ch. 4 §4.4; Krener, Encyclopedia
chapter; Lee, Ch. 9 and Ch. 20). The `dite` wrapper makes the definition total: off the
`C¹` locus it is `0`, while `bracket_eq_flowCommutator` shows it equals the Lie bracket
on the `C¹` locus. -/
noncomputable def infinitesimalCommutator (f g : X → X) (x₀ : X) : X := by
  classical
  exact if hf : ContDiffAt ℝ 1 f x₀ then
    if hg : ContDiffAt ℝ 1 g x₀ then
      flowMixedSecond f g x₀ hf hg - flowMixedSecondSwap f g x₀ hf hg
    else 0
  else 0

/-- The spatial derivative of the local flow at time `0` is the identity (the `t = 0`
case of the first-order variational expansion of the flow; Sontag, Ch. 4 §4.2). -/
theorem flow_deriv_at_zero (f : X → X) (x₀ : X) (hf : ContDiffAt ℝ 1 f x₀) :
    fderiv ℝ (localFlow hf 0) x₀ = ContinuousLinearMap.id ℝ X := by
  have hx : x₀ ∈ Metric.closedBall x₀ (getLocalFlowData hf).r :=
    Metric.mem_closedBall_self (le_of_lt (getLocalFlowData hf).hr)
  have hmem : Metric.closedBall x₀ (getLocalFlowData hf).r ∈ 𝓝 x₀ :=
    Metric.closedBall_mem_nhds x₀ (getLocalFlowData hf).hr
  have heq : localFlow hf 0 =ᶠ[𝓝 x₀] id := by
    filter_upwards [hmem] with y hy
    exact (getLocalFlowData hf).ϕ_zero y hy
  rw [heq.fderiv_eq]
  simp

/-- The first mixed partial computes to `Dg(f)`: `∂²/∂t∂s|₍₀,₀₎ (Ψₛ ∘ Φₜ)(x₀)` equals
`fderiv ℝ g x₀ (f x₀)` (Lee, Ch. 9 and Ch. 20). The inner derivative in `s` is the flow
equation of `g`; the outer derivative in `t` is the chain rule along the flow of `f`. -/
theorem flowMixedSecond_eq (f g : X → X) (x₀ : X)
    (hf : ContDiffAt ℝ 1 f x₀) (hg : ContDiffAt ℝ 1 g x₀) :
    flowMixedSecond f g x₀ hf hg = fderiv ℝ g x₀ (f x₀) := by
  have h0F : (0 : ℝ) ∈ Set.Ioo (-(getLocalFlowData hf).ε) (getLocalFlowData hf).ε :=
    Set.mem_Ioo.mpr ⟨by linarith [(getLocalFlowData hf).hε], (getLocalFlowData hf).hε⟩
  have h0G : (0 : ℝ) ∈ Set.Ioo (-(getLocalFlowData hg).ε) (getLocalFlowData hg).ε :=
    Set.mem_Ioo.mpr ⟨by linarith [(getLocalFlowData hg).hε], (getLocalFlowData hg).hε⟩
  have hxF : x₀ ∈ Metric.closedBall x₀ (getLocalFlowData hf).r :=
    Metric.mem_closedBall_self (le_of_lt (getLocalFlowData hf).hr)
  have h00F : (getLocalFlowData hf).ϕ 0 x₀ = x₀ := (getLocalFlowData hf).ϕ_zero x₀ hxF
  have hΦ0 : localFlow hf 0 x₀ = x₀ := (getLocalFlowData hf).ϕ_zero x₀ hxF
  have hΦt : HasDerivAt (fun t : ℝ ↦ localFlow hf t x₀) (f x₀) 0 := by
    have h := (getLocalFlowData hf).ϕ_hasDerivAt 0 h0F x₀ hxF
    rw [h00F] at h
    exact h
  have hcont : ContinuousAt (fun t : ℝ ↦ localFlow hf t x₀) 0 := hΦt.continuousAt
  have hF0 : (fun t : ℝ ↦ localFlow hf t x₀) 0 = x₀ := hΦ0
  have hmem : ∀ᶠ t in 𝓝 (0 : ℝ),
      localFlow hf t x₀ ∈ Metric.closedBall x₀ (getLocalFlowData hg).r := by
    apply hcont.eventually
    rw [hF0]
    exact Filter.eventually_of_mem (Metric.closedBall_mem_nhds x₀ (getLocalFlowData hg).hr)
      fun _ h ↦ h
  have hinner : (fun t : ℝ ↦ fderiv ℝ (fun s : ℝ ↦ localFlow hg s (localFlow hf t x₀)) 0 1)
      =ᶠ[𝓝 (0 : ℝ)] (fun t : ℝ ↦ g (localFlow hf t x₀)) := by
    filter_upwards [hmem] with t ht
    have h00 : (getLocalFlowData hg).ϕ 0 (localFlow hf t x₀) = localFlow hf t x₀ :=
      (getLocalFlowData hg).ϕ_zero _ ht
    have hΨ : HasDerivAt (fun s : ℝ ↦ localFlow hg s (localFlow hf t x₀))
        (g (localFlow hf t x₀)) 0 := by
      have h := (getLocalFlowData hg).ϕ_hasDerivAt 0 h0G (localFlow hf t x₀) ht
      rw [h00] at h
      exact h
    have hfd := hΨ.hasFDerivAt.fderiv
    rw [hfd, ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  have hg_diff : DifferentiableAt ℝ g x₀ := hg.differentiableAt_one
  have hFderiv0 : HasFDerivAt g (fderiv ℝ g x₀) ((fun t : ℝ ↦ localFlow hf t x₀) 0) := by
    rw [hF0]
    exact hg_diff.hasFDerivAt
  have hcomp : HasDerivAt (fun t : ℝ ↦ g (localFlow hf t x₀)) (fderiv ℝ g x₀ (f x₀)) 0 := by
    have h := HasFDerivAt.comp_hasDerivAt (f := fun t : ℝ ↦ localFlow hf t x₀)
      (f' := f x₀) (x := 0) hFderiv0 hΦt
    exact h
  unfold flowMixedSecond
  rw [hinner.fderiv_eq, hcomp.hasFDerivAt.fderiv, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul]

/-- The swapped mixed partial computes to `Df(g)`: `∂²/∂s∂t|₍₀,₀₎ (Φₜ ∘ Ψₛ)(x₀)` equals
`fderiv ℝ f x₀ (g x₀)` (Lee, Ch. 9 and Ch. 20). -/
theorem flowMixedSecondSwap_eq (f g : X → X) (x₀ : X)
    (hf : ContDiffAt ℝ 1 f x₀) (hg : ContDiffAt ℝ 1 g x₀) :
    flowMixedSecondSwap f g x₀ hf hg = fderiv ℝ f x₀ (g x₀) := by
  have h0F : (0 : ℝ) ∈ Set.Ioo (-(getLocalFlowData hf).ε) (getLocalFlowData hf).ε :=
    Set.mem_Ioo.mpr ⟨by linarith [(getLocalFlowData hf).hε], (getLocalFlowData hf).hε⟩
  have h0G : (0 : ℝ) ∈ Set.Ioo (-(getLocalFlowData hg).ε) (getLocalFlowData hg).ε :=
    Set.mem_Ioo.mpr ⟨by linarith [(getLocalFlowData hg).hε], (getLocalFlowData hg).hε⟩
  have hxG : x₀ ∈ Metric.closedBall x₀ (getLocalFlowData hg).r :=
    Metric.mem_closedBall_self (le_of_lt (getLocalFlowData hg).hr)
  have h00G : (getLocalFlowData hg).ϕ 0 x₀ = x₀ := (getLocalFlowData hg).ϕ_zero x₀ hxG
  have hΨ0 : localFlow hg 0 x₀ = x₀ := (getLocalFlowData hg).ϕ_zero x₀ hxG
  have hΨs : HasDerivAt (fun s : ℝ ↦ localFlow hg s x₀) (g x₀) 0 := by
    have h := (getLocalFlowData hg).ϕ_hasDerivAt 0 h0G x₀ hxG
    rw [h00G] at h
    exact h
  have hcont : ContinuousAt (fun s : ℝ ↦ localFlow hg s x₀) 0 := hΨs.continuousAt
  have hG0 : (fun s : ℝ ↦ localFlow hg s x₀) 0 = x₀ := hΨ0
  have hmem : ∀ᶠ s in 𝓝 (0 : ℝ),
      localFlow hg s x₀ ∈ Metric.closedBall x₀ (getLocalFlowData hf).r := by
    apply hcont.eventually
    rw [hG0]
    exact Filter.eventually_of_mem (Metric.closedBall_mem_nhds x₀ (getLocalFlowData hf).hr)
      fun _ h ↦ h
  have hinner : (fun s : ℝ ↦ fderiv ℝ (fun t : ℝ ↦ localFlow hf t (localFlow hg s x₀)) 0 1)
      =ᶠ[𝓝 (0 : ℝ)] (fun s : ℝ ↦ f (localFlow hg s x₀)) := by
    filter_upwards [hmem] with s hs
    have h00 : (getLocalFlowData hf).ϕ 0 (localFlow hg s x₀) = localFlow hg s x₀ :=
      (getLocalFlowData hf).ϕ_zero _ hs
    have hΦ : HasDerivAt (fun t : ℝ ↦ localFlow hf t (localFlow hg s x₀))
        (f (localFlow hg s x₀)) 0 := by
      have h := (getLocalFlowData hf).ϕ_hasDerivAt 0 h0F (localFlow hg s x₀) hs
      rw [h00] at h
      exact h
    have hfd := hΦ.hasFDerivAt.fderiv
    rw [hfd, ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  have hf_diff : DifferentiableAt ℝ f x₀ := hf.differentiableAt_one
  have hFderiv0 : HasFDerivAt f (fderiv ℝ f x₀) ((fun s : ℝ ↦ localFlow hg s x₀) 0) := by
    rw [hG0]
    exact hf_diff.hasFDerivAt
  have hcomp : HasDerivAt (fun s : ℝ ↦ f (localFlow hg s x₀)) (fderiv ℝ f x₀ (g x₀)) 0 := by
    have h := HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ ↦ localFlow hg s x₀)
      (f' := g x₀) (x := 0) hFderiv0 hΨs
    exact h
  unfold flowMixedSecondSwap
  rw [hinner.fderiv_eq, hcomp.hasFDerivAt.fderiv, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul]

/-- **The Lie bracket as infinitesimal commutator of flows (Sontag, Ch. 4 §4.4; Krener,
Encyclopedia chapter; Lee, Ch. 9 and Ch. 20):** for `C¹` vector fields `f` and `g`, the
mixed second derivative of the flow commutator at `(0, 0)` equals the Lie bracket
`Dg(f) − Df(g)` at `x₀`.

*Status:* this identifies the value of the mixed second derivative, a PREREQUISITE for
the bracket-direction bridge. It does **not** by itself discharge the `hBracket`
hypothesis of `Chow.chowInterior`: that additionally needs the
`k`-fold-bracket-to-flow-composition wiring (the piecewise-constant end-point map),
which is not built here. -/
theorem bracket_eq_flowCommutator (f g : X → X) (x₀ : X)
    (hf : ContDiffAt ℝ 1 f x₀) (hg : ContDiffAt ℝ 1 g x₀) :
    infinitesimalCommutator f g x₀ = lieBracket f g x₀ := by
  unfold infinitesimalCommutator
  rw [dite_eq_left hf, dite_eq_left hg, flowMixedSecond_eq f g x₀ hf hg,
    flowMixedSecondSwap_eq f g x₀ hf hg, lieBracket_apply]

/-! ## G7: the Lie derivative of a vector field along a flow

We now pass from the mixed-second-derivative form of the bracket (G5 above) to the
*Lie derivative along the flow*,
`∂/∂t|₀ (Φₜ)^* g (x₀) = [f, g](x₀)`, where `(Φₜ)^* g (x) = (DΦₜ(x))⁻¹ g(Φₜ x)` is Mathlib's
`VectorField.pullback` (so `(Φₜ)^* g = (Φ₋ₜ)₊ g` by the group law). References: Sontag Ch. 4
§4.2 and §4.4 (the `Ad` operator, Lemma 4.4.2); Lee, *Introduction to Smooth Manifolds*,
Prop. 18.4 and Cor. 20.6 (Lie derivative). No originality is claimed.

### Honest scoping (Path B)

The *spatial* first-order expansion `DΦₜ(x₀) = id + t • Df(x₀) + o(t)` (the baby variational
equation — the flow is differentiable in the initial condition with `∂ₜ DΦₜ = Df(Φₜ) DΦₜ`) is
**not** in Mathlib, and the Picard–Lindelöf bundle `LocalFlowData` records only Lipschitz
dependence on the initial condition. The G5 inner-`s`-first trick does not remove it here,
because the pullback genuinely involves `DΦₜ`. We therefore take it as an explicit,
documented hypothesis:

* `lieDerivative_along_flow` assumes `hVar : HasDerivAt (t ↦ DΦₜ(x₀)) (Df(x₀)) 0` (the
  `t = 0` variational derivative; the `t = 0` value `DΦ₀ = id` is `flow_deriv_at_zero`).
* `flowsCommute_of_bracketVanishing` assumes the transport of this statement to every time
  and base point in the flow box (`hdiff`, `hinv`, `hTrans`: spatial differentiability and
  invertibility of the time-`t` flow, and the Lie-derivative identity at time `t`), and then
  proves — with no further assumption — the *integration* argument: bracket zero ⇒
  `(Φₜ)^* g = g` ⇒ `DΦₜ g = g ∘ Φₜ` ⇒ both `s ↦ Φₜ(Ψₛ x₀)` and `s ↦ Ψₛ(Φₜ x₀)` solve the
  `g`-ODE with the same initial value ⇒ they coincide (Mathlib ODE uniqueness).
-/

/-- The time-`0` value of the local flow is the identity at the base point. -/
theorem localFlow_zero_apply (f : X → X) (x₀ : X) (hf : ContDiffAt ℝ 1 f x₀) :
    localFlow hf 0 x₀ = x₀ :=
  (getLocalFlowData hf).ϕ_zero x₀
    (Metric.mem_closedBall_self (le_of_lt (getLocalFlowData hf).hr))

/-- The flow equation at the base point and time `0`: `d/dt|₀ Φₜ(x₀) = f(x₀)`. -/
theorem localFlow_hasDerivAt_zero (f : X → X) (x₀ : X) (hf : ContDiffAt ℝ 1 f x₀) :
    HasDerivAt (fun t : ℝ ↦ localFlow hf t x₀) (f x₀) 0 := by
  have h0F : (0 : ℝ) ∈ Set.Ioo (-(getLocalFlowData hf).ε) (getLocalFlowData hf).ε :=
    Set.mem_Ioo.mpr ⟨by linarith [(getLocalFlowData hf).hε], (getLocalFlowData hf).hε⟩
  have hxF : x₀ ∈ Metric.closedBall x₀ (getLocalFlowData hf).r :=
    Metric.mem_closedBall_self (le_of_lt (getLocalFlowData hf).hr)
  have h := (getLocalFlowData hf).ϕ_hasDerivAt 0 h0F x₀ hxF
  rwa [(getLocalFlowData hf).ϕ_zero x₀ hxF] at h

/-- A `C¹` field `g` evaluated along the flow of `f` through `x₀` has time derivative
`Dg(x₀)(f x₀)` at `t = 0` (chain rule along the flow). -/
theorem hasDerivAt_field_along_flow (f g : X → X) (x₀ : X)
    (hf : ContDiffAt ℝ 1 f x₀) (hg : ContDiffAt ℝ 1 g x₀) :
    HasDerivAt (fun t : ℝ ↦ g (localFlow hf t x₀)) (fderiv ℝ g x₀ (f x₀)) 0 := by
  have hFd : HasFDerivAt g (fderiv ℝ g x₀) (localFlow hf 0 x₀) := by
    rw [localFlow_zero_apply f x₀ hf]
    exact hg.differentiableAt_one.hasFDerivAt
  exact hFd.comp_hasDerivAt (0 : ℝ) (localFlow_hasDerivAt_zero f x₀ hf)

/-- **G7 (derivative form): the Lie derivative of `g` along the flow of `f` is the Lie bracket
(Sontag, Ch. 4 §4.2/§4.4; Lee, Prop. 18.4 and Cor. 20.6).** The pullback
`(Φₜ)^* g (x₀) = (DΦₜ(x₀))⁻¹ g(Φₜ x₀)` (Mathlib `VectorField.pullback`; equal to
`DΦ₋ₜ(Φₜ x₀) g(Φₜ x₀)` by the group law) has time derivative `[f, g](x₀)` at `t = 0`.

*Path B hypothesis.* `hVar` is the baby variational equation at `t = 0`:
`t ↦ DΦₜ(x₀)` has derivative `Df(x₀)` at `0` (as a map `ℝ → (X →L[ℝ] X)`). It is not in
Mathlib (see the section header); all else is proved, using `flow_deriv_at_zero`
(`DΦ₀ = id`), the differentiability of `Ring.inverse` at `1`, and the chain rule along the
flow. The bracket arises as `Dg(f) − Df(g)`: the first term from `t ↦ g(Φₜ x₀)`, the second
from `d/dt (DΦₜ)⁻¹|₀ = −Df(x₀)`. -/
theorem lieDerivative_along_flow (f g : X → X) (x₀ : X)
    (hf : ContDiffAt ℝ 1 f x₀) (hg : ContDiffAt ℝ 1 g x₀)
    (hVar : HasDerivAt (fun t : ℝ ↦ fderiv ℝ (localFlow hf t) x₀) (fderiv ℝ f x₀) 0) :
    HasDerivAt (fun t : ℝ ↦ VectorField.pullback ℝ (localFlow hf t) g x₀)
      (lieBracket f g x₀) 0 := by
  have hA0 : fderiv ℝ (localFlow hf 0) x₀ = ((1 : (X →L[ℝ] X)ˣ) : X →L[ℝ] X) := by
    rw [flow_deriv_at_zero f x₀ hf]
    rfl
  have hu := hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (X →L[ℝ] X)ˣ)
  have hB : HasDerivAt (fun t : ℝ ↦ Ring.inverse (fderiv ℝ (localFlow hf t) x₀))
      ((-ContinuousLinearMap.mulLeftRight ℝ (X →L[ℝ] X) (↑(1 : (X →L[ℝ] X)ˣ)⁻¹)
        (↑(1 : (X →L[ℝ] X)ˣ))) (fderiv ℝ f x₀)) 0 := by
    have h := (show HasFDerivAt (Ring.inverse : (X →L[ℝ] X) → (X →L[ℝ] X)) _
      (fderiv ℝ (localFlow hf 0) x₀) by rw [hA0]; exact hu).comp_hasDerivAt (0 : ℝ) hVar
    exact h
  have hprod := hB.clm_apply (hasDerivAt_field_along_flow f g x₀ hf hg)
  have hfun : (fun t : ℝ ↦ VectorField.pullback ℝ (localFlow hf t) g x₀)
      = fun t : ℝ ↦ (Ring.inverse (fderiv ℝ (localFlow hf t) x₀)) (g (localFlow hf t x₀)) := by
    funext t
    rw [ContinuousLinearMap.ringInverse_eq_inverse]
    rfl
  rw [hfun, lieBracket_apply]
  convert hprod using 1
  rw [localFlow_zero_apply f x₀ hf, hA0]
  simp [sub_eq_add_neg, add_comm]

/-- The time-`0` flow has derivative `id` at every interior point of the flow box. -/
theorem flow_deriv_zero_of_mem_ball (f : X → X) (x₀ : X) (hf : ContDiffAt ℝ 1 f x₀)
    {y : X} (hy : y ∈ Metric.ball x₀ (getLocalFlowData hf).r) :
    fderiv ℝ (localFlow hf 0) y = ContinuousLinearMap.id ℝ X := by
  have heq : localFlow hf 0 =ᶠ[𝓝 y] id := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
    exact (getLocalFlowData hf).ϕ_zero z (Metric.ball_subset_closedBall hz)
  rw [heq.fderiv_eq]
  simp

/-- The local flow is jointly continuous at `(0, x₀)` (a consequence of the strict
differentiability `flowStrictFDerivAt`). -/
theorem localFlow_continuousAt (f : X → X) (x₀ : X) (hf : ContDiffAt ℝ 1 f x₀) :
    ContinuousAt (fun p : ℝ × X ↦ localFlow hf p.1 p.2) (0, x₀) :=
  (flowStrictFDerivAt hf).hasFDerivAt.continuousAt

/-- **The flows-commute bridge (Sontag, Ch. 4 §4.2/§4.4; Lee, Cor. 20.6 and Thm 9.44).**
If the Lie bracket `[f, g]` vanishes identically, then the local flows of `f` and `g` commute
near `x₀`: there is `δ > 0` with `Φₜ(Ψₛ x₀) = Ψₛ(Φₜ x₀)` for all `|t|, |s| < δ`.

*Path B hypotheses* (the spatial variational theory of the flow, not in Mathlib):
* `hdiff` — the time-`t` flow `Φₜ` is differentiable at every interior point of the flow box;
* `hinv` — its derivative there is invertible;
* `hTrans` — the Lie-derivative identity at an arbitrary time `t` and base point `y` in the
  box: `∂ₜ (Φₜ)^* g (y) = (Φₜ)^* [f, g] (y)` (the `t`-transported form of
  `lieDerivative_along_flow`, Sontag Lemma 4.4.2).

From these the proof is complete (no further assumption): (1) `[f, g] = 0` makes
`τ ↦ (Φ_τ)^* g (y)` constant on `(-ε, ε)`, hence equal to its value `g y` at `τ = 0`
(`flow_deriv_zero_of_mem_ball`), i.e. `DΦₜ(y) g(y) = g(Φₜ y)`; (2) for fixed `t`, the two
curves `s ↦ Φₜ(Ψₛ x₀)` (chain rule and (1)) and `s ↦ Ψₛ(Φₜ x₀)` (flow equation) solve
`ẏ = g(y)` with the same value `Φₜ x₀` at `s = 0`, and stay in the ball where `g` is
Lipschitz (joint continuity of the flows at `(0, x₀)`); Mathlib's
`ODE_solution_unique_of_mem_Ioo` identifies them. -/
theorem flowsCommute_of_bracketVanishing (f g : X → X) (x₀ : X)
    (hf : ContDiffAt ℝ 1 f x₀) (hg : ContDiffAt ℝ 1 g x₀)
    (hbr : ∀ x, lieBracket f g x = 0)
    (hdiff : ∀ t ∈ Set.Ioo (-localFlowTime hf) (localFlowTime hf),
      ∀ y ∈ Metric.ball x₀ (localFlowRadius hf), DifferentiableAt ℝ (localFlow hf t) y)
    (hinv : ∀ t ∈ Set.Ioo (-localFlowTime hf) (localFlowTime hf),
      ∀ y ∈ Metric.ball x₀ (localFlowRadius hf), (fderiv ℝ (localFlow hf t) y).IsInvertible)
    (hTrans : ∀ y ∈ Metric.ball x₀ (localFlowRadius hf),
      ∀ t ∈ Set.Ioo (-localFlowTime hf) (localFlowTime hf),
        HasDerivAt (fun τ : ℝ ↦ VectorField.pullback ℝ (localFlow hf τ) g y)
          (VectorField.pullback ℝ (localFlow hf t) (lieBracket f g) y) t) :
    ∃ δ > 0, ∀ t ∈ Set.Ioo (-δ) δ, ∀ s ∈ Set.Ioo (-δ) δ,
      localFlow hf t (localFlow hg s x₀) = localFlow hg s (localFlow hf t x₀) := by
  -- Step 1: `DΦₜ(y) g(y) = g(Φₜ y)` on the flow box.
  have key : ∀ t ∈ Set.Ioo (-localFlowTime hf) (localFlowTime hf),
      ∀ y ∈ Metric.ball x₀ (localFlowRadius hf),
        fderiv ℝ (localFlow hf t) y (g y) = g (localFlow hf t y) := by
    intro t ht y hy
    have hεT : 0 < localFlowTime hf := (getLocalFlowData hf).hε
    have h0 : (0 : ℝ) ∈ Set.Ioo (-localFlowTime hf) (localFlowTime hf) :=
      Set.mem_Ioo.mpr ⟨by linarith [hεT], hεT⟩
    have hderiv : ∀ τ ∈ Set.Ioo (-localFlowTime hf) (localFlowTime hf),
        deriv (fun σ : ℝ ↦ VectorField.pullback ℝ (localFlow hf σ) g y) τ = 0 := by
      intro τ hτ
      rw [(hTrans y hy τ hτ).deriv]
      simp [VectorField.pullback, hbr]
    have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun τ hτ ↦ (hTrans y hy τ hτ).differentiableAt.differentiableWithinAt) hderiv ht h0
    have h00 : VectorField.pullback ℝ (localFlow hf 0) g y = g y := by
      simp only [VectorField.pullback, flow_deriv_zero_of_mem_ball f x₀ hf hy,
        ContinuousLinearMap.inverse_id, ContinuousLinearMap.id_apply]
      congr 1
      exact (getLocalFlowData hf).ϕ_zero y (Metric.ball_subset_closedBall hy)
    rw [h00] at hconst
    rw [← VectorField.fderiv_pullback (𝕜 := ℝ) (localFlow hf t) g y (hinv t ht y hy), hconst]
  -- Step 2: choose a common box `δ`.
  have hucG : ContinuousAt (fun s : ℝ ↦ localFlow hg s x₀) 0 :=
    (localFlow_hasDerivAt_zero g x₀ hg).continuousAt
  have hucF : ContinuousAt (fun t : ℝ ↦ localFlow hf t x₀) 0 :=
    (localFlow_hasDerivAt_zero f x₀ hf).continuousAt
  have hF0 := localFlow_zero_apply f x₀ hf
  have hG0 := localFlow_zero_apply g x₀ hg
  have hFc := localFlow_continuousAt f x₀ hf
  have hGc := localFlow_continuousAt g x₀ hg
  -- (ii) `Ψₛ x₀ ∈ ball x₀ rf`
  have hP2 : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
      localFlow hg p.2 x₀ ∈ Metric.ball x₀ (localFlowRadius hf) := by
    have h := (hucG.comp (f := Prod.snd) (x := ((0 : ℝ), (0 : ℝ))) continuousAt_snd)
    refine h.eventually_mem ?_
    change Metric.ball x₀ (localFlowRadius hf) ∈ 𝓝 (localFlow hg 0 x₀)
    rw [hG0]
    exact Metric.ball_mem_nhds x₀ (getLocalFlowData hf).hr
  -- (iii) `Φₜ x₀ ∈ closedBall x₀ rg`
  have hP3 : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
      localFlow hf p.1 x₀ ∈ Metric.closedBall x₀ (getLocalFlowData hg).r := by
    have h := (hucF.comp (f := Prod.fst) (x := ((0 : ℝ), (0 : ℝ))) continuousAt_fst)
    refine h.eventually_mem ?_
    change Metric.closedBall x₀ (getLocalFlowData hg).r ∈ 𝓝 (localFlow hf 0 x₀)
    rw [hF0]
    exact Metric.closedBall_mem_nhds x₀ (getLocalFlowData hg).hr
  -- (iv) `Φₜ(Ψₛ x₀) ∈ closedBall x₀ ag`
  have hP4 : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
      localFlow hf p.1 (localFlow hg p.2 x₀) ∈ Metric.closedBall x₀ (getLocalFlowData hg).a := by
    have hm : ContinuousAt (fun p : ℝ × ℝ ↦ (p.1, localFlow hg p.2 x₀)) (0, 0) :=
      continuousAt_fst.prodMk (hucG.comp (f := Prod.snd) (x := ((0 : ℝ), (0 : ℝ))) continuousAt_snd)
    have hm0 : (fun p : ℝ × ℝ ↦ (p.1, localFlow hg p.2 x₀)) (0, 0) = (0, x₀) := by
      simp [hG0]
    have h := hFc.comp_of_eq hm hm0
    refine h.eventually_mem ?_
    change Metric.closedBall x₀ (getLocalFlowData hg).a ∈ 𝓝 (localFlow hf 0 (localFlow hg 0 x₀))
    rw [hG0, hF0]
    exact Metric.closedBall_mem_nhds x₀ (getLocalFlowData hg).ha
  -- (v) `Ψₛ(Φₜ x₀) ∈ closedBall x₀ ag`
  have hP5 : ∀ᶠ p : ℝ × ℝ in 𝓝 (0, 0),
      localFlow hg p.2 (localFlow hf p.1 x₀) ∈ Metric.closedBall x₀ (getLocalFlowData hg).a := by
    have hm : ContinuousAt (fun p : ℝ × ℝ ↦ (p.2, localFlow hf p.1 x₀)) (0, 0) :=
      continuousAt_snd.prodMk (hucF.comp (f := Prod.fst) (x := ((0 : ℝ), (0 : ℝ))) continuousAt_fst)
    have hm0 : (fun p : ℝ × ℝ ↦ (p.2, localFlow hf p.1 x₀)) (0, 0) = (0, x₀) := by
      simp [hF0]
    have h := hGc.comp_of_eq hm hm0
    refine h.eventually_mem ?_
    change Metric.closedBall x₀ (getLocalFlowData hg).a ∈ 𝓝 (localFlow hg 0 (localFlow hf 0 x₀))
    rw [hF0, hG0]
    exact Metric.closedBall_mem_nhds x₀ (getLocalFlowData hg).ha
  obtain ⟨ε', hε', hball⟩ := Metric.eventually_nhds_iff.mp
    (hP2.and (hP3.and (hP4.and hP5)))
  have hεf := (getLocalFlowData hf).hε
  have hεg := (getLocalFlowData hg).hε
  refine ⟨min ε' (min (getLocalFlowData hf).ε (getLocalFlowData hg).ε), lt_min hε'
    (lt_min hεf hεg), ?_⟩
  set δ := min ε' (min (getLocalFlowData hf).ε (getLocalFlowData hg).ε) with hδ
  have hδpos : 0 < δ := lt_min hε' (lt_min hεf hεg)
  have hδ1 : δ ≤ ε' := min_le_left _ _
  have hδf : δ ≤ (getLocalFlowData hf).ε := (min_le_right _ _).trans (min_le_left _ _)
  have hδg : δ ≤ (getLocalFlowData hg).ε := (min_le_right _ _).trans (min_le_right _ _)
  have habs : ∀ {u : ℝ}, u ∈ Set.Ioo (-δ) δ → |u| < δ := fun hu ↦ abs_lt.mpr hu
  have hP : ∀ t ∈ Set.Ioo (-δ) δ, ∀ s ∈ Set.Ioo (-δ) δ,
      localFlow hg s x₀ ∈ Metric.ball x₀ (localFlowRadius hf) ∧
      localFlow hf t x₀ ∈ Metric.closedBall x₀ (getLocalFlowData hg).r ∧
      localFlow hf t (localFlow hg s x₀) ∈ Metric.closedBall x₀ (getLocalFlowData hg).a ∧
      localFlow hg s (localFlow hf t x₀) ∈ Metric.closedBall x₀ (getLocalFlowData hg).a := by
    intro t ht s hs
    have hd : dist (t, s) ((0 : ℝ), (0 : ℝ)) < ε' := by
      rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, sub_zero]
      exact max_lt ((habs ht).trans_le hδ1) ((habs hs).trans_le hδ1)
    exact hball hd
  intro t ht s hs
  -- the ODE uniqueness on `s ∈ (-δ, δ)`
  have htF : t ∈ Set.Ioo (-localFlowTime hf) (localFlowTime hf) :=
    ⟨lt_of_le_of_lt (neg_le_neg hδf) ht.1, lt_of_lt_of_le ht.2 hδf⟩
  have hsG : ∀ σ ∈ Set.Ioo (-δ) δ, σ ∈ Set.Ioo (-(getLocalFlowData hg).ε) (getLocalFlowData hg).ε :=
    fun σ hσ ↦ ⟨by linarith [hσ.1], lt_of_lt_of_le hσ.2 hδg⟩
  have hx₀G : x₀ ∈ Metric.closedBall x₀ (getLocalFlowData hg).r :=
    Metric.mem_closedBall_self (le_of_lt (getLocalFlowData hg).hr)
  have hmain := ODE_solution_unique_of_mem_Ioo
    (v := fun _ : ℝ ↦ g) (s := fun _ : ℝ ↦ Metric.closedBall x₀ (getLocalFlowData hg).a)
    (K := (getLocalFlowData hg).K) (a := -δ) (b := δ) (t₀ := 0)
    (f := fun σ : ℝ ↦ localFlow hf t (localFlow hg σ x₀))
    (g := fun σ : ℝ ↦ localFlow hg σ (localFlow hf t x₀))
    (fun _ _ ↦ (getLocalFlowData hg).f_lipschitz)
    ⟨by linarith [hδpos], hδpos⟩
    (by
      intro σ hσ
      obtain ⟨hy, -, h4, -⟩ := hP t ht σ hσ
      refine ⟨?_, h4⟩
      have hΨ : HasDerivAt (fun σ' : ℝ ↦ localFlow hg σ' x₀) (g (localFlow hg σ x₀)) σ :=
        (getLocalFlowData hg).ϕ_hasDerivAt σ (hsG σ hσ) x₀ hx₀G
      have hΦ : HasFDerivAt (localFlow hf t) (fderiv ℝ (localFlow hf t) (localFlow hg σ x₀))
          (localFlow hg σ x₀) := (hdiff t htF _ hy).hasFDerivAt
      have h := hΦ.comp_hasDerivAt σ hΨ
      rwa [key t htF _ hy] at h)
    (by
      intro σ hσ
      obtain ⟨-, h3, -, h5⟩ := hP t ht σ hσ
      exact ⟨(getLocalFlowData hg).ϕ_hasDerivAt σ (hsG σ hσ) _ h3, h5⟩)
    (by
      have h3 := (hP t ht 0 ⟨by linarith [hδpos], hδpos⟩).2.1
      simp only [hG0]
      exact ((getLocalFlowData hg).ϕ_zero _ h3).symm)
  exact hmain hs
