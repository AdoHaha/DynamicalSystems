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
