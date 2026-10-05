/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Calculus of variations: first variation and the Euler–Lagrange equation

This file formalises the first variation of a continuous-time cost functional and
the Euler–Lagrange equation for the classical problem of the calculus of
variations, following Sontag, *Mathematical Control Theory: Deterministic Finite
Dimensional Systems*, 2nd ed., 1998, Ch. 9 §9.2–9.3 (printed pp. 399–421), and
Liberzon, *Calculus of Variations and Optimal Control Theory*, 2012, Ch. 1–2.

For a running cost (Lagrangian) `L : ℝ → E → E → ℝ`, a terminal cost
`K : E → ℝ`, a horizon `T`, and a curve `x : ℝ → E`, the cost functional is

`J x = ∫ t in 0..T, L t (x t) (deriv x t) + K (x T)`.

The **first variation** of `J` at `x` in direction `η` is the linearisation of
the running and terminal costs,

`δJ(x; η) = ∫ t in 0..T, (∂ₓL t (x t) (x' t)) (η t)
    + (∂ᵥL t (x t) (x' t)) (η' t)  +  (∂K (x T)) (η T)`,

which is definitionally `firstVariation`.  Classically this is the Gateaux
derivative `d/dε |_{ε=0} J (x + ε • η)`; identifying the two requires
differentiating under the interval integral, which is not formalised here (see
the implementation notes).

The **Euler–Lagrange equation** is the pointwise ODE

`d/dt (∂ᵥL t (x t) (x' t)) = ∂ₓL t (x t) (x' t)`,

see `eulerLagrange`.  The classical theorem `eulerLagrange_of_firstVariation_zero`
says that if the first variation vanishes for every curve perturbation `η`
vanishing at both endpoints, then `x` satisfies the Euler–Lagrange equation.
The proof integrates `δJ` by parts and invokes the fundamental lemma of the
calculus of variations, `integral_mul_eq_zero_of_continuous`.

## Main definitions

* `cvFunctional`: the cost functional `J`.
* `firstVariation`: the explicit first variation `δJ(x; η)`.
* `HasVanishingFirstVariation`: vanishing of the first variation on
  endpoint-vanishing perturbations.
* `eulerLagrange`: the Euler–Lagrange equation at a curve.

## Main results

* `integral_mul_eq_zero_of_continuous`: the fundamental lemma of the calculus of
  variations for continuous scalar functions (Sontag §9.3, Liberzon Lemma 2.1).
* `integral_apply_eq_zero_of_continuous`: the dual-valued fundamental lemma,
  deduced from the scalar one by testing with `η = φ • e`.
* `integral_deriv_mul_eq_neg_integral_mul_deriv`: scalar integration by parts for
  an endpoint-vanishing weight.
* `eulerLagrange_of_firstVariation_zero`: vanishing first variation, together
  with differentiability and continuity of the velocity derivative curve,
  implies the Euler–Lagrange equation.

## Implementation notes

The state space `E` is an arbitrary real normed space; the partial derivatives of
the Lagrangian are the genuine Fréchet derivatives `fderiv ℝ`, so the Euler–
Lagrange equation is an equality in the continuous dual `E →L[ℝ] ℝ`.  Curves are
only assumed differentiable (`HasDerivAt`), and integrability is carried by the
hypotheses rather than baked into a structure, matching the relational style of
`DynamicalSystems.OptimalControl.ContinuousTime.ContinuousOCP`.

Two points are deliberately left out of scope.  First, the identification of
`firstVariation` with the Gateaux derivative `d/dε |_{ε=0} J (x + ε • η)` would
require differentiating the interval integral with respect to the perturbation
parameter (Mathlib's `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`),
and is not proved here.  Second, `eulerLagrange_of_firstVariation_zero` assumes
that the velocity derivative curve `t ↦ ∂ᵥL t (x t) (x' t)` is already
differentiable with some derivative `Q`; the du Bois-Reymond argument that would
derive this differentiability from the vanishing first variation alone (via the
fundamental-lemma variant for `η'`) is not formalised.
-/

@[expose] public section

open scoped Interval Topology

open MeasureTheory

variable {E : Type*}

section Definitions

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The cost functional of the calculus of variations problem: the running cost
`L t (x t) (x' t)` integrated over `[0, T]` plus the terminal cost `K (x T)`.
This is `J x = ∫₀ᵀ L(t, x t, x' t) dt + K (x T)` (Sontag, *Mathematical Control
Theory*, 2nd ed., 1998, Ch. 9 §9.2, printed p. 399). -/
noncomputable def cvFunctional (L : ℝ → E → E → ℝ) (K : E → ℝ) (T : ℝ)
    (x : ℝ → E) : ℝ :=
  (∫ t in 0..T, L t (x t) (deriv x t)) + K (x T)

/-- The first variation `δJ(x; η)` of the cost functional at the curve `x` in the
direction `η`, in its explicit linearised form.  The state derivative `∂ₓL` and
the velocity derivative `∂ᵥL` are the Fréchet derivatives of `L` in its second
and third arguments, and `∂K` is the Fréchet derivative of the terminal cost:

`δJ(x; η) = ∫₀ᵀ (∂ₓL · η + ∂ᵥL · η') + ∂K (x T) · η T`
(Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 9 §9.2–9.3, printed
pp. 399–421; Liberzon, *Calculus of Variations and Optimal Control Theory*, 2012,
Eq. (2.14)). -/
noncomputable def firstVariation (L : ℝ → E → E → ℝ) (K : E → ℝ) (T : ℝ)
    (x η : ℝ → E) : ℝ :=
  (∫ t in 0..T,
      (fderiv ℝ (fun y : E ↦ L t y (deriv x t)) (x t)) (η t)
        + (fderiv ℝ (fun v : E ↦ L t (x t) v) (deriv x t)) (deriv η t))
    + (fderiv ℝ K (x T)) (η T)

/-- The first variation vanishes on all differentiable perturbations that vanish
at both endpoints (the admissible perturbations of the fixed-endpoint variational
problem; Liberzon, *Calculus of Variations and Optimal Control Theory*, 2012,
Eq. (2.11)). -/
def HasVanishingFirstVariation (L : ℝ → E → E → ℝ) (K : E → ℝ) (T : ℝ)
    (x : ℝ → E) : Prop :=
  ∀ η : ℝ → E, (∀ t, HasDerivAt η (deriv η t) t) → η 0 = 0 → η T = 0 →
    firstVariation L K T x η = 0

/-- The Euler–Lagrange equation along the curve `x`:

`d/dt (∂ᵥL t (x t) (x' t)) = ∂ₓL t (x t) (x' t)` for `t ∈ [0, T]`.

Both sides are elements of the continuous dual `E →L[ℝ] ℝ`; the left-hand side is
the derivative of the dual-valued curve `t ↦ ∂ᵥL t (x t) (x' t)` (Sontag,
*Mathematical Control Theory*, 2nd ed., 1998, Ch. 9 §9.3, Eq. (9.20), printed
p. 410). -/
def eulerLagrange (L : ℝ → E → E → ℝ) (T : ℝ) (x : ℝ → E) : Prop :=
  ∀ t ∈ Set.Icc 0 T,
    HasDerivAt (fun s : ℝ ↦ fderiv ℝ (fun v : E ↦ L s (x s) v) (deriv x s))
      (fderiv ℝ (fun y : E ↦ L t y (deriv x t)) (x t)) t

end Definitions

section FundamentalLemma

/-- The fundamental lemma of the calculus of variations, scalar version: a
continuous function `f` on `[0, T]` that is orthogonal to every smooth function
`φ` compactly supported in `(0, T)` (so `φ` vanishes at both endpoints) is
identically zero.  This is the crux of the passage from the vanishing first
variation to the Euler–Lagrange equation (Sontag, *Mathematical Control Theory*,
2nd ed., 1998, Ch. 9 §9.3, printed p. 410; Liberzon, *Calculus of Variations and
Optimal Control Theory*, 2012, Lemma 2.1).

Only global continuity of `f` is assumed; on the interval this is the classical
regularity hypothesis, and it is exactly what is available for the Euler–Lagrange
defect `∂ₓL - d/dt ∂ᵥL` below. -/
theorem integral_mul_eq_zero_of_continuous {f : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf : Continuous f)
    (h : ∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → tsupport φ ⊆ Set.Ioo 0 T →
        ∫ t in 0..T, f t * φ t = 0) :
    ∀ t ∈ Set.Icc 0 T, f t = 0 := by
  -- It suffices to rule out a positive value, applied to `f` and to `-f`.
  have key : ∀ g : ℝ → ℝ, Continuous g →
      (∀ φ : ℝ → ℝ, ContDiff ℝ 1 φ → tsupport φ ⊆ Set.Ioo 0 T →
        ∫ t in 0..T, g t * φ t = 0) →
      ¬ ∃ t ∈ Set.Icc 0 T, 0 < g t := by
    intro g hg hgint
    rintro ⟨t₀, ht₀, hpos⟩
    -- Find an interior point `p` with `g p > 0`.
    have hp : ∃ p ∈ Set.Ioo 0 T, 0 < g p := by
      have hev : ∀ᶠ y in 𝓝 t₀, 0 < g y :=
        hg.continuousAt.eventually (isOpen_Ioi.mem_nhds hpos)
      rw [Metric.eventually_nhds_iff] at hev
      obtain ⟨δ, hδpos, hδ⟩ := hev
      rcases lt_or_ge t₀ T with ht₀T | ht₀T
      · refine ⟨(t₀ + min T (t₀ + δ)) / 2, ?_, ?_⟩
        · rw [Set.mem_Ioo]
          have h1 : t₀ < min T (t₀ + δ) := lt_min ht₀T (by linarith)
          have h2 : min T (t₀ + δ) ≤ T := min_le_left _ _
          constructor
          · linarith [ht₀.1, h1]
          · linarith [ht₀T, h2]
        · apply hδ
          rw [Real.dist_eq]
          have h1 : t₀ < min T (t₀ + δ) := lt_min ht₀T (by linarith)
          have h2 : min T (t₀ + δ) ≤ t₀ + δ := min_le_right _ _
          rw [abs_of_pos (by linarith : 0 < (t₀ + min T (t₀ + δ)) / 2 - t₀)]
          linarith
      · have ht₀eq : t₀ = T := le_antisymm ht₀.2 ht₀T
        refine ⟨(max 0 (T - δ) + T) / 2, ?_, ?_⟩
        · rw [Set.mem_Ioo]
          have h1 : max 0 (T - δ) < T := max_lt hT (by linarith)
          have h2 : 0 ≤ max 0 (T - δ) := le_max_left _ _
          constructor
          · linarith [h2]
          · linarith [h1]
        · apply hδ
          have h1 : max 0 (T - δ) < T := max_lt hT (by linarith)
          have h2 : T - δ ≤ max 0 (T - δ) := le_max_right _ _
          rw [Real.dist_eq, ht₀eq,
            abs_of_neg (by linarith : (max 0 (T - δ) + T) / 2 - T < 0)]
          linarith
    obtain ⟨p, hpIoo, hppos⟩ := hp
    have hp_pos : 0 < p := hpIoo.1
    have hpT : p < T := hpIoo.2
    -- A neighbourhood `(p - rOut, p + rOut)` of `p` on which `g > 0`, contained in `(0, T)`.
    have hev : ∀ᶠ y in 𝓝 p, 0 < g y :=
      hg.continuousAt.eventually (isOpen_Ioi.mem_nhds hppos)
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδpos, hδ⟩ := hev
    set rOut : ℝ := min (δ / 2) (min p (T - p) / 2) with hrOut
    have hrOut_pos : 0 < rOut := by
      rw [hrOut]; exact lt_min (by linarith) (by positivity)
    have hrOut_le_δ : rOut ≤ δ / 2 := by rw [hrOut]; exact min_le_left _ _
    have hrOut_lt_p : rOut < p := by
      have : rOut ≤ min p (T - p) / 2 := by rw [hrOut]; exact min_le_right _ _
      have : min p (T - p) ≤ p := min_le_left _ _
      nlinarith
    have hrOut_lt_Tp : rOut < T - p := by
      have : rOut ≤ min p (T - p) / 2 := by rw [hrOut]; exact min_le_right _ _
      have : min p (T - p) ≤ T - p := min_le_right _ _
      nlinarith
    -- positivity of `g` on `(p - rOut, p + rOut)`
    have hgpos : ∀ y ∈ Set.Ioo (p - rOut) (p + rOut), 0 < g y := by
      intro y hy
      apply hδ
      rw [Real.dist_eq]
      have hy' : |y - p| < rOut := by
        rw [abs_lt]; constructor <;> linarith [hy.1, hy.2]
      linarith
    -- the smooth bump supported in `(p - rOut, p + rOut)`
    let φ : ContDiffBump p := ⟨rOut / 2, rOut, by positivity, by linarith⟩
    have hφrOut : φ.rOut = rOut := rfl
    have hφrIn : φ.rIn = rOut / 2 := rfl
    have hφsupp : tsupport (φ : ℝ → ℝ) ⊆ Set.Ioo 0 T := by
      rw [φ.tsupport_eq, hφrOut]
      intro x hx
      rw [Metric.mem_closedBall, Real.dist_eq] at hx
      rw [Set.mem_Ioo]
      constructor <;> linarith [abs_le.mp hx |>.1, abs_le.mp hx |>.2, hrOut_lt_p, hrOut_lt_Tp]
    -- the product is nonnegative everywhere
    have hgnonneg : ∀ t, 0 ≤ g t * φ t := by
      intro t
      rcases eq_or_ne (φ t) 0 with hφ0 | hφne
      · rw [hφ0, mul_zero]
      · have ht : t ∈ Function.support (fun t ↦ (φ : ℝ → ℝ) t) :=
          Function.mem_support.mpr hφne
        rw [φ.support_eq] at ht
        rw [Metric.mem_ball, hφrOut, Real.dist_eq] at ht
        exact mul_nonneg (hgpos t (by
          rw [Set.mem_Ioo]; constructor <;> linarith [abs_lt.mp ht |>.1, abs_lt.mp ht |>.2])).le
          φ.nonneg
    -- support inclusions
    have hsupp0 : Function.support (fun t ↦ g t * φ t) ⊆ Set.Ioc 0 T := by
      intro t ht
      have htφ : t ∈ Function.support (fun t ↦ (φ : ℝ → ℝ) t) :=
        Function.mem_support.mpr (fun hφ0 ↦ Function.mem_support.mp ht (by rw [hφ0, mul_zero]))
      rw [φ.support_eq, Metric.mem_ball, hφrOut, Real.dist_eq] at htφ
      rw [Set.mem_Ioc]
      constructor <;> linarith [abs_lt.mp htφ |>.1, abs_lt.mp htφ |>.2]
    have hsuppOut : Function.support (fun t ↦ g t * φ t) ⊆ Set.Ioc (p - rOut) (p + rOut) := by
      intro t ht
      have htφ : t ∈ Function.support (fun t ↦ (φ : ℝ → ℝ) t) :=
        Function.mem_support.mpr (fun hφ0 ↦ Function.mem_support.mp ht (by rw [hφ0, mul_zero]))
      rw [φ.support_eq, Metric.mem_ball, hφrOut, Real.dist_eq] at htφ
      rw [Set.mem_Ioc]
      constructor <;> linarith [abs_lt.mp htφ |>.1, abs_lt.mp htφ |>.2]
    -- the inner integral is positive
    have hcont : Continuous (fun t ↦ g t * φ t) := hg.mul φ.continuous
    have hinner : 0 < ∫ t in (p - φ.rIn)..(p + φ.rIn), g t * φ t := by
      apply intervalIntegral.intervalIntegral_pos_of_pos_on
      · exact hcont.continuousOn.intervalIntegrable
      · intro x hx
        have hxball : x ∈ Metric.closedBall p φ.rIn := by
          rw [Metric.mem_closedBall, Real.dist_eq]
          exact le_of_lt (abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)
        rw [φ.one_of_mem_closedBall hxball, mul_one]
        exact hgpos x (by
          rw [Set.mem_Ioo] at hx ⊢
          constructor <;> linarith [φ.rIn_pos, φ.rIn_lt_rOut])
      · linarith [φ.rIn_pos]
    -- relate the two interval integrals to the full integral
    have hEq : (∫ t in 0..T, g t * φ t)
        = ∫ t in (p - rOut)..(p + rOut), g t * φ t :=
      (intervalIntegral.integral_eq_integral_of_support_subset hsupp0).trans
        (intervalIntegral.integral_eq_integral_of_support_subset hsuppOut).symm
    -- decompose the outer integral and bound the tails below by zero
    have hI_ab : IntervalIntegrable (fun t ↦ g t * φ t) volume (p - rOut) (p - φ.rIn) :=
      hcont.continuousOn.intervalIntegrable
    have hI_bc : IntervalIntegrable (fun t ↦ g t * φ t) volume (p - φ.rIn) (p + φ.rIn) :=
      hcont.continuousOn.intervalIntegrable
    have hI_cd : IntervalIntegrable (fun t ↦ g t * φ t) volume (p + φ.rIn) (p + rOut) :=
      hcont.continuousOn.intervalIntegrable
    have hI_bd : IntervalIntegrable (fun t ↦ g t * φ t) volume (p - φ.rIn) (p + rOut) :=
      hcont.continuousOn.intervalIntegrable
    have htail1 : 0 ≤ ∫ t in (p - rOut)..(p - φ.rIn), g t * φ t :=
      intervalIntegral.integral_nonneg_of_forall (by linarith [φ.rIn_lt_rOut]) hgnonneg
    have htail2 : 0 ≤ ∫ t in (p + φ.rIn)..(p + rOut), g t * φ t :=
      intervalIntegral.integral_nonneg_of_forall (by linarith [φ.rIn_lt_rOut]) hgnonneg
    have hout : 0 < ∫ t in (p - rOut)..(p + rOut), g t * φ t := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hI_ab hI_bd,
        ← intervalIntegral.integral_add_adjacent_intervals hI_bc hI_cd]
      linarith
    have hzero : (∫ t in 0..T, g t * φ t) = 0 :=
      hgint φ φ.contDiff hφsupp
    rw [hEq] at hzero
    linarith
  intro t ht
  have h1 : ¬ 0 < f t := fun hpos ↦ key f hf h ⟨t, ht, hpos⟩
  have h2 : ¬ 0 < -f t := by
    refine fun hpos ↦ key (fun t ↦ -f t) hf.neg ?_ ⟨t, ht, hpos⟩
    intro φ hφ hsupp
    have : (∫ t in 0..T, (-f t) * φ t) = -∫ t in 0..T, f t * φ t := by
      rw [← intervalIntegral.integral_neg]
      apply intervalIntegral.integral_congr
      intro x _
      ring
    rw [this, h φ hφ hsupp, neg_zero]
  linarith

end FundamentalLemma

section FundamentalLemmaDual

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The fundamental lemma of the calculus of variations, dual-valued version: a
continuous curve `ξ : ℝ → E →L[ℝ] ℝ` in the continuous dual of `E` that is
orthogonal to every differentiable perturbation `η` vanishing at both endpoints
is identically zero.  It is deduced from the scalar version
`integral_mul_eq_zero_of_continuous` by testing `η = φ • e`. -/
theorem integral_apply_eq_zero_of_continuous {ξ : ℝ → E →L[ℝ] ℝ} {T : ℝ} (hT : 0 < T)
    (hξ : Continuous ξ)
    (h : ∀ η : ℝ → E, (∀ t, HasDerivAt η (deriv η t) t) → η 0 = 0 → η T = 0 →
        ∫ t in 0..T, (ξ t) (η t) = 0) :
    ∀ t ∈ Set.Icc 0 T, ξ t = 0 := by
  intro t ht
  ext e
  refine integral_mul_eq_zero_of_continuous hT (hξ.clm_apply continuous_const) ?_ t ht
  intro φ hφ hsupp
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hφ0 : φ 0 = 0 := by
    by_contra hne
    exact absurd (hsupp (subset_closure (Function.mem_support.mpr hne))) (by simp)
  have hφT : φ T = 0 := by
    by_contra hne
    exact absurd (hsupp (subset_closure (Function.mem_support.mpr hne))) (by simp)
  have hηdiff : ∀ s, HasDerivAt (fun s ↦ φ s • e) (deriv (fun s ↦ φ s • e) s) s := by
    intro s
    rw [deriv_smul_const hφd.differentiableAt e]
    exact hφd.differentiableAt.hasDerivAt.smul_const e
  have hη := h (fun s ↦ φ s • e) hηdiff (by rw [hφ0, zero_smul]) (by rw [hφT, zero_smul])
  have hcongr : (∫ t in 0..T, (ξ t) e * φ t)
      = ∫ t in 0..T, (ξ t) (φ t • e) := by
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    rw [map_smul, smul_eq_mul]
    ring
  rw [hcongr, hη]

end FundamentalLemmaDual

section EulerLagrange

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Integration by parts for the scalar functions `u` and `v` with explicit
endpoints-vanishing weight and explicit derivatives `u'`, `v'`:
`∫ u' v = - ∫ u v'`.  This is the shape of Mathlib's
`intervalIntegral.integral_deriv_mul_eq_sub`, specialised to a weight `u` that
vanishes at both endpoints. -/
theorem integral_deriv_mul_eq_neg_integral_mul_deriv
    {u v u' v' : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x)
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (v' x) x)
    (hui : IntervalIntegrable u' volume a b)
    (hvi : IntervalIntegrable v' volume a b)
    (hua : u a = 0) (hub : u b = 0) :
    ∫ x in a..b, u' x * v x = -∫ x in a..b, u x * v' x := by
  have h1 : IntervalIntegrable (fun x ↦ u' x * v x) volume a b :=
    hui.mul_continuousOn (HasDerivAt.continuousOn hv)
  have h2 : IntervalIntegrable (fun x ↦ u x * v' x) volume a b :=
    hvi.continuousOn_mul (HasDerivAt.continuousOn hu)
  have h := intervalIntegral.integral_deriv_mul_eq_sub hu hv hui hvi
  rw [hub, hua, zero_mul, zero_mul, sub_zero, intervalIntegral.integral_add h1 h2] at h
  linarith

/-- The built-in-derivative special case of
`integral_deriv_mul_eq_neg_integral_mul_deriv`: integration by parts for the
scalar functions `u` and `v` when `u` vanishes at both endpoints and derivatives
are written with `deriv`, `∫ u' v = - ∫ u v'`. -/
theorem integral_deriv_mul_eq_neg_integral_mul_deriv_deriv
    {u v : ℝ → ℝ} {a b : ℝ}
    (hu : ∀ x ∈ Set.uIcc a b, HasDerivAt u (deriv u x) x)
    (hv : ∀ x ∈ Set.uIcc a b, HasDerivAt v (deriv v x) x)
    (hui : IntervalIntegrable (deriv u) volume a b)
    (hvi : IntervalIntegrable (deriv v) volume a b)
    (hua : u a = 0) (hub : u b = 0) :
    ∫ x in a..b, deriv u x * v x = -∫ x in a..b, u x * deriv v x :=
  integral_deriv_mul_eq_neg_integral_mul_deriv hu hv hui hvi hua hub

/-- **Euler–Lagrange equation from vanishing first variation.**  If the first
variation of the cost functional vanishes on every differentiable perturbation
`η` with `η 0 = η T = 0`, and if the velocity derivative curve
`t ↦ ∂ᵥL t (x t) (x' t)` is differentiable with derivative `Q` (with `Q` and the
state derivative `∂ₓL` continuous), then `∂ₓL = Q` and hence `x` satisfies the
Euler–Lagrange equation `d/dt ∂ᵥL = ∂ₓL` (Sontag, *Mathematical Control Theory*,
2nd ed., 1998, Ch. 9 §9.3, Eq. (9.20), printed p. 410; Liberzon, *Calculus of
Variations and Optimal Control Theory*, 2012, Theorem 2.1).  The terminal cost `K`
is arbitrary here: fixed-endpoint (endpoint-vanishing) variations satisfy `η T = 0`,
so the terminal-penalty term `(∂K (x T)) (η T)` vanishes and `K` does not enter the
interior Euler–Lagrange equation. The continuity hypotheses (`hPcont`, `hQcont`, `hScont`)
are assumed globally on `ℝ`, a mild over-strengthening of the book's interval-local regularity
on `[0, T]`. -/
theorem eulerLagrange_of_firstVariation_zero (L : ℝ → E → E → ℝ) (K : E → ℝ)
    (Q : ℝ → E →L[ℝ] ℝ) (T : ℝ) (x : ℝ → E)
    (hT : 0 < T)
    (hvan : HasVanishingFirstVariation L K T x)
    (hPderiv : ∀ t ∈ Set.Icc 0 T,
      HasDerivAt (fun s ↦ fderiv ℝ (fun v : E ↦ L s (x s) v) (deriv x s)) (Q t) t)
    (hPcont : Continuous (fun s ↦ fderiv ℝ (fun v : E ↦ L s (x s) v) (deriv x s)))
    (hQcont : Continuous Q)
    (hScont : Continuous (fun t ↦ fderiv ℝ (fun y : E ↦ L t y (deriv x t)) (x t))) :
    eulerLagrange L T x := by
  let P : ℝ → E →L[ℝ] ℝ := fun s ↦ fderiv ℝ (fun v : E ↦ L s (x s) v) (deriv x s)
  let S : ℝ → E →L[ℝ] ℝ := fun t ↦ fderiv ℝ (fun y : E ↦ L t y (deriv x t)) (x t)
  -- The weak form of the Euler–Lagrange equation: for every `e` and every smooth
  -- endpoint-vanishing `φ`, `∫ (S e - Q e) * φ = 0`.
  have hweak : ∀ (e : E) (φ : ℝ → ℝ), ContDiff ℝ 1 φ → tsupport φ ⊆ Set.Ioo 0 T →
      ∫ t in 0..T, ((S t) e - (Q t) e) * φ t = 0 := by
    intro e φ hφ hsupp
    have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
    have hφ0 : φ 0 = 0 := by
      by_contra hne
      exact absurd (hsupp (subset_closure (Function.mem_support.mpr hne))) (by simp)
    have hφT : φ T = 0 := by
      by_contra hne
      exact absurd (hsupp (subset_closure (Function.mem_support.mpr hne))) (by simp)
    have hηdiff : ∀ s, HasDerivAt (fun s : ℝ ↦ φ s • e)
        (deriv (fun s : ℝ ↦ φ s • e) s) s := by
      intro s
      rw [deriv_smul_const hφd.differentiableAt e]
      exact hφd.differentiableAt.hasDerivAt.smul_const e
    have hfirst := hvan (fun s : ℝ ↦ φ s • e) hηdiff
      (by rw [hφ0, zero_smul]) (by rw [hφT, zero_smul])
    -- The first variation reduces to the scalar integral plus a vanishing endpoint term.
    have hfirst' : (∫ t in 0..T, ((S t) e) * φ t + deriv φ t * ((P t) e)) = 0 := by
      have hcongr : (∫ t in 0..T,
            (fderiv ℝ (fun y : E ↦ L t y (deriv x t)) (x t)) ((fun s : ℝ ↦ φ s • e) t)
              + (fderiv ℝ (fun v : E ↦ L t (x t) v) (deriv x t))
                  (deriv (fun s : ℝ ↦ φ s • e) t))
          = ∫ t in 0..T, ((S t) e) * φ t + deriv φ t * ((P t) e) := by
        apply intervalIntegral.integral_congr
        intro t _
        dsimp only [P, S]
        rw [deriv_smul_const hφd.differentiableAt e, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        ring
      unfold firstVariation at hfirst
      rw [hcongr] at hfirst
      rw [show (fun s : ℝ ↦ φ s • e) T = 0 from by simp only [hφT, zero_smul], map_zero,
        add_zero] at hfirst
      exact hfirst
    -- Integration by parts on the `(P e) * deriv φ` term.
    have hPe_deriv : ∀ t ∈ Set.uIcc 0 T, HasDerivAt (fun s ↦ (P s) e) ((Q t) e) t := by
      intro t ht
      have ht' : t ∈ Set.Icc 0 T := by rwa [Set.uIcc_of_le hT.le] at ht
      have h := (hPderiv t ht').clm_apply (hasDerivAt_const (x := t) e)
      simpa only [P, map_zero, add_zero] using h
    have hφ_deriv : ∀ t ∈ Set.uIcc 0 T, HasDerivAt φ (deriv φ t) t :=
      fun t _ ↦ hφd.differentiableAt.hasDerivAt
    have hui : IntervalIntegrable (deriv φ) volume 0 T :=
      hφ.continuous_deriv_one.continuousOn.intervalIntegrable
    have hvi : IntervalIntegrable (fun t ↦ (Q t) e) volume 0 T :=
      (hQcont.clm_apply continuous_const).continuousOn.intervalIntegrable
    have hIb : IntervalIntegrable (fun t ↦ deriv φ t * ((P t) e)) volume 0 T :=
      (hφ.continuous_deriv_one.mul
        (hPcont.clm_apply continuous_const)).continuousOn.intervalIntegrable
    have hIc : IntervalIntegrable (fun t ↦ φ t * ((Q t) e)) volume 0 T :=
      (hφ.continuous.mul (hQcont.clm_apply continuous_const)).continuousOn.intervalIntegrable
    have hIS : IntervalIntegrable (fun t ↦ ((S t) e) * φ t) volume 0 T :=
      ((hScont.clm_apply continuous_const).mul hφ.continuous).continuousOn.intervalIntegrable
    have hibp : (∫ t in 0..T, deriv φ t * ((P t) e))
        = -∫ t in 0..T, φ t * ((Q t) e) :=
      integral_deriv_mul_eq_neg_integral_mul_deriv hφ_deriv hPe_deriv hui hvi hφ0 hφT
    have hsplit : (∫ t in 0..T, ((S t) e) * φ t + deriv φ t * ((P t) e))
        = (∫ t in 0..T, ((S t) e) * φ t) + (∫ t in 0..T, deriv φ t * ((P t) e)) :=
      intervalIntegral.integral_add hIS hIb
    have hgoal : (∫ t in 0..T, ((S t) e - (Q t) e) * φ t)
        = (∫ t in 0..T, ((S t) e) * φ t) - (∫ t in 0..T, φ t * ((Q t) e)) := by
      rw [← intervalIntegral.integral_sub hIS hIc]
      apply intervalIntegral.integral_congr
      intro t _
      ring
    rw [hsplit, hibp] at hfirst'
    rw [hgoal]
    linarith
  -- Apply the scalar fundamental lemma componentwise.
  have hSQ : ∀ t ∈ Set.Icc 0 T, S t = Q t := by
    intro t ht
    ext e
    have hcont : Continuous (fun s ↦ ((S s) e - (Q s) e)) :=
      (hScont.clm_apply continuous_const).sub (hQcont.clm_apply continuous_const)
    have h := integral_mul_eq_zero_of_continuous hT hcont
      (fun φ hφ hsupp ↦ hweak e φ hφ hsupp) t ht
    simpa only [Pi.sub_apply, sub_eq_zero] using h
  intro t ht
  change HasDerivAt P (S t) t
  rw [show S t = Q t from hSQ t ht]
  exact hPderiv t ht

end EulerLagrange

/-! ## Weierstrass–Erdmann corner conditions

This section formalises the first (and, for autonomous Lagrangians, the second)
Weierstrass–Erdmann corner condition for a piecewise-`C¹` extremal, following Kirk,
*Optimal Control Theory: An Introduction* (Dover, 2004), §4.4, and Liberzon,
*Calculus of Variations and Optimal Control Theory* (2012), §4.4.

Where `eulerLagrange_of_firstVariation_zero` treats a `C¹` extremal with
endpoint-vanishing perturbations, the corner conditions generalise to a curve `x`
that is `C¹` on each of `[0, τ]` and `[τ, T]` and continuous at the corner `τ`,
while `deriv x` may jump there.  Integrating the first variation by parts
separately on the two sub-intervals leaves boundary terms at `τ`; since the
perturbation `η` is free at `τ` (it need only vanish at `0` and `T`), those terms
can cancel for every admissible `η` only if the momentum
`∂ᵥL τ (x τ) (x' τ)` is continuous across the corner.  For an autonomous
Lagrangian the same argument applied to time reparametrisations gives continuity
of the energy `⟪x', ∂ᵥL⟫ − L`.
-/

section WeierstrassErdmann

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A curve `x : ℝ → E` is piecewise-`C¹` on `[0, T]` with a single corner at `τ`:
it is continuous on `[0, T]`, has left derivative `vL t` at every `t ∈ [0, τ]`
(so `vL` is the genuine two-sided derivative on `[0, τ)`), and right derivative
`vR t` at every `t ∈ [τ, T]`.  The one-sided derivatives `vL τ` and `vR τ` may
differ: that jump is the corner (Kirk, *Optimal Control Theory*, Dover 2004,
§4.4; Liberzon, *Calculus of Variations and Optimal Control Theory*, 2012,
§4.4). -/
def IsPiecewiseC₁On (x vL vR : ℝ → E) (T τ : ℝ) : Prop :=
  0 < τ ∧ τ < T ∧ ContinuousOn x (Set.Icc 0 T) ∧
    (∀ t ∈ Set.Icc 0 τ, HasDerivWithinAt x (vL t) (Set.Iic τ) t) ∧
    (∀ t ∈ Set.Icc τ T, HasDerivWithinAt x (vR t) (Set.Ici τ) t)

/-- ASCII alias for `IsPiecewiseC₁On` (the task statement spells it `IsPiecewiseC¹On`
with a superscript `¹`, which is not a valid Lean identifier character; the subscript `₁`
is the closest compilable spelling). -/
abbrev IsPiecewiseC1On (x vL vR : ℝ → E) (T τ : ℝ) : Prop :=
  IsPiecewiseC₁On x vL vR T τ

/-- The momentum (velocity-derivative) curve `P(t) = ∂ᵥL t (x t) (v t)`, the
Fréchet derivative of the Lagrangian in its velocity argument evaluated along
the curve `x` with velocity field `v`. -/
noncomputable def momentumCurve (L : ℝ → E → E → ℝ) (x v : ℝ → E) :
    ℝ → E →L[ℝ] ℝ :=
  fun t ↦ fderiv ℝ (fun w : E ↦ L t (x t) w) (v t)

/-- The state-derivative curve `S(t) = ∂ₓL t (x t) (v t)`, the Fréchet derivative
of the Lagrangian in its state argument evaluated along `x` with velocity `v`. -/
noncomputable def stateDerivCurve (L : ℝ → E → E → ℝ) (x v : ℝ → E) :
    ℝ → E →L[ℝ] ℝ :=
  fun t ↦ fderiv ℝ (fun y : E ↦ L t y (v t)) (x t)

/-- The energy curve `H(t) = ⟪v t, ∂ᵥL⟫ − L` for an autonomous Lagrangian
`L : E → E → ℝ`, i.e. `H(t) = (∂ᵥL (x t) (v t)) (v t) − L (x t) (v t)`. -/
noncomputable def energyCurve (L : E → E → ℝ) (x v : ℝ → E) : ℝ → ℝ :=
  fun t ↦ (fderiv ℝ (fun w : E ↦ L (x t) w) (v t)) (v t) - L (x t) (v t)

/-- The first variation split at the corner `τ`: the running-cost linearisation
integrated separately over `[0, τ]` (with left velocity field `vL`) and
`[τ, T]` (with right velocity field `vR`), plus the terminal term.  For a `C¹`
curve (`vL = vR = deriv x`) this agrees with `firstVariation` up to the null
set `{τ}`. -/
noncomputable def firstVariation_piecewise (L : ℝ → E → E → ℝ) (K : E → ℝ)
    (T τ : ℝ) (x vL vR η wL wR : ℝ → E) : ℝ :=
  (∫ t in 0..τ, (stateDerivCurve L x vL t) (η t)
      + (momentumCurve L x vL t) (wL t))
    + (∫ t in τ..T, (stateDerivCurve L x vR t) (η t)
        + (momentumCurve L x vR t) (wR t))
    + (fderiv ℝ K (x T)) (η T)

/-- A piecewise-`C¹` perturbation: `η` is continuous on `[0, T]`, vanishes at
both endpoints (but is free at the corner `τ`), and has left derivative `wL`
on `[0, τ]` and right derivative `wR` on `[τ, T]`. -/
def IsPiecewisePerturbation (η wL wR : ℝ → E) (T τ : ℝ) : Prop :=
  0 < τ ∧ τ < T ∧ ContinuousOn η (Set.Icc 0 T) ∧ η 0 = 0 ∧ η T = 0 ∧
    (∀ t ∈ Set.Icc 0 τ, HasDerivWithinAt η (wL t) (Set.Iic τ) t) ∧
    (∀ t ∈ Set.Icc τ T, HasDerivWithinAt η (wR t) (Set.Ici τ) t)

/-- The (split) first variation vanishes on every admissible piecewise-`C¹`
perturbation.  This is the corner-setting analogue of
`HasVanishingFirstVariation`. -/
def HasVanishingPiecewiseFirstVariation (L : ℝ → E → E → ℝ) (K : E → ℝ)
    (T τ : ℝ) (x vL vR : ℝ → E) : Prop :=
  ∀ η wL wR : ℝ → E, IsPiecewisePerturbation η wL wR T τ →
    firstVariation_piecewise L K T τ x vL vR η wL wR = 0

/-- A `C¹` curve is piecewise-`C¹` with any corner (both one-sided derivative
fields can be taken to be `deriv x`). -/
theorem isPiecewiseC1On_of_hasDerivAt {x : ℝ → E} {T τ : ℝ}
    (h0 : 0 < τ) (hT : τ < T) (hcont : ContinuousOn x (Set.Icc 0 T))
    (hderiv : ∀ t ∈ Set.Icc 0 T, HasDerivAt x (deriv x t) t) :
    IsPiecewiseC₁On x (fun t ↦ deriv x t) (fun t ↦ deriv x t) T τ := by
  refine ⟨h0, hT, hcont, ?_, ?_⟩
  · intro t ht
    exact ((hderiv t ⟨ht.1, le_trans ht.2 hT.le⟩).hasDerivWithinAt)
  · intro t ht
    exact ((hderiv t ⟨le_trans h0.le ht.1, ht.2⟩).hasDerivWithinAt)

/-- **First Weierstrass–Erdmann corner condition** (Kirk, *Optimal Control
Theory*, Dover 2004, §4.4; Liberzon, *Calculus of Variations and Optimal
Control Theory*, 2012, §4.4): if the (split) first variation vanishes for every
piecewise-`C¹` endpoint-vanishing perturbation, and each arc satisfies the
Euler–Lagrange equation (`hEL₁`, `hEL₂`: these follow from the vanishing first
variation on each sub-interval by the standard `eulerLagrange`-style argument,
cf. `eulerLagrange_of_firstVariation_zero`), then the momentum is continuous
across the corner: `∂ᵥL τ (x τ) (vL τ) = ∂ᵥL τ (x τ) (vR τ)`.

The proof integrates by parts on `[0, τ]` and `[τ, T]`
(`intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt`, which needs only
interior differentiability plus endpoint continuity, hence no spurious
two-sided hypothesis at the corner).  The bulk terms cancel by the arc-wise
Euler–Lagrange equations, leaving `(P⁻ τ − P⁺ τ) (η τ)`; testing against the
smooth bump `η = φ • e` with `φ τ = 1` supported in `(0, T)` forces
`P⁻ τ = P⁺ τ`.  The continuity hypotheses are stated globally on `ℝ`, a mild
over-strengthening of the books' interval-local regularity, matching the style
of `eulerLagrange_of_firstVariation_zero`. -/
theorem weierstrassErdmannMomentum
    {L : ℝ → E → E → ℝ} {K : E → ℝ} {T τ : ℝ} {x vL vR : ℝ → E}
    {Q₁ Q₂ : ℝ → E →L[ℝ] ℝ}
    (hcorner : IsPiecewiseC₁On x vL vR T τ)
    (hvan : HasVanishingPiecewiseFirstVariation L K T τ x vL vR)
    (hP₁deriv : ∀ t ∈ Set.Ioo 0 τ, HasDerivAt (momentumCurve L x vL) (Q₁ t) t)
    (hP₂deriv : ∀ t ∈ Set.Ioo τ T, HasDerivAt (momentumCurve L x vR) (Q₂ t) t)
    (hEL₁ : ∀ t ∈ Set.Icc 0 τ, stateDerivCurve L x vL t = Q₁ t)
    (hEL₂ : ∀ t ∈ Set.Icc τ T, stateDerivCurve L x vR t = Q₂ t)
    (hS₁cont : Continuous (stateDerivCurve L x vL))
    (hP₁cont : Continuous (momentumCurve L x vL))
    (hQ₁cont : Continuous Q₁)
    (hS₂cont : Continuous (stateDerivCurve L x vR))
    (hP₂cont : Continuous (momentumCurve L x vR))
    (hQ₂cont : Continuous Q₂) :
    momentumCurve L x vL τ = momentumCurve L x vR τ := by
  obtain ⟨h0τ, hτT, -, -, -⟩ := hcorner
  apply ContinuousLinearMap.ext
  intro e
  -- A bump radius with `closedBall τ rOut ⊆ (0, T)`.
  have hTτ : (0 : ℝ) < T - τ := sub_pos.mpr hτT
  set rOut : ℝ := min τ (T - τ) / 2 with hrOut
  have hmin_pos : (0 : ℝ) < min τ (T - τ) := lt_min h0τ hTτ
  have hrOut_pos : 0 < rOut := by rw [hrOut]; linarith
  have hrOut_τ : rOut ≤ τ / 2 := by
    rw [hrOut]
    have hmin : min τ (T - τ) ≤ τ := min_le_left _ _
    linarith
  have hrOut_T : rOut ≤ (T - τ) / 2 := by
    rw [hrOut]
    have hmin : min τ (T - τ) ≤ T - τ := min_le_right _ _
    linarith
  have hball : Metric.closedBall τ rOut ⊆ Set.Ioo 0 T := by
    intro y hy
    rw [Metric.mem_closedBall, Real.dist_eq] at hy
    obtain ⟨hlo, hhi⟩ := abs_le.mp hy
    rw [Set.mem_Ioo]
    constructor <;> linarith
  -- The smooth bump at the corner, equal to `1` at `τ`.
  let φ : ContDiffBump τ := ⟨rOut / 2, rOut, by linarith, by linarith⟩
  have hφrOut : φ.rOut = rOut := rfl
  have hφrIn : φ.rIn = rOut / 2 := rfl
  have hφ : ContDiff ℝ 1 (φ : ℝ → ℝ) := φ.contDiff
  have hφd : Differentiable ℝ (φ : ℝ → ℝ) := hφ.differentiable (by norm_num)
  have hφτ : (φ : ℝ → ℝ) τ = 1 := by
    apply φ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_self, hφrIn]
    linarith
  have hφsupp : tsupport (φ : ℝ → ℝ) ⊆ Set.Ioo 0 T := by
    rw [φ.tsupport_eq, hφrOut]
    exact hball
  have hφ0 : (φ : ℝ → ℝ) 0 = 0 := by
    by_contra hne
    exact absurd (hφsupp (subset_closure (Function.mem_support.mpr hne))) (by simp)
  have hφT : (φ : ℝ → ℝ) T = 0 := by
    by_contra hne
    exact absurd (hφsupp (subset_closure (Function.mem_support.mpr hne))) (by simp)
  -- The test perturbation `η = φ • e`, free at `τ` with `η τ = e`.
  have hηderiv : ∀ s, HasDerivAt (fun s : ℝ ↦ (φ : ℝ → ℝ) s • e)
      (deriv (fun s : ℝ ↦ (φ : ℝ → ℝ) s • e) s) s := by
    intro s
    rw [deriv_smul_const hφd.differentiableAt e]
    exact hφd.differentiableAt.hasDerivAt.smul_const e
  have hadm : IsPiecewisePerturbation (fun s : ℝ ↦ (φ : ℝ → ℝ) s • e)
      (fun s : ℝ ↦ deriv (φ : ℝ → ℝ) s • e)
      (fun s : ℝ ↦ deriv (φ : ℝ → ℝ) s • e) T τ := by
    refine ⟨h0τ, hτT, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hφd.continuous.smul continuous_const).continuousOn
    · change (φ : ℝ → ℝ) 0 • e = 0
      rw [hφ0, zero_smul]
    · change (φ : ℝ → ℝ) T • e = 0
      rw [hφT, zero_smul]
    · intro t _
      have h := (hηderiv t).hasDerivWithinAt (s := Set.Iic τ)
      rwa [deriv_smul_const hφd.differentiableAt e] at h
    · intro t _
      have h := (hηderiv t).hasDerivWithinAt (s := Set.Ici τ)
      rwa [deriv_smul_const hφd.differentiableAt e] at h
  have hvan0 := hvan _ _ _ hadm
  simp only [firstVariation_piecewise] at hvan0
  rw [show (φ : ℝ → ℝ) T • e = 0 from by rw [hφT, zero_smul], map_zero,
    add_zero] at hvan0
  -- Clean scalar continuity facts.
  have hS₁e : Continuous (fun t ↦ (stateDerivCurve L x vL t) e) :=
    hS₁cont.clm_apply continuous_const
  have hP₁e : Continuous (fun t ↦ (momentumCurve L x vL t) e) :=
    hP₁cont.clm_apply continuous_const
  have hQ₁e : Continuous (fun t ↦ (Q₁ t) e) :=
    hQ₁cont.clm_apply continuous_const
  have hS₂e : Continuous (fun t ↦ (stateDerivCurve L x vR t) e) :=
    hS₂cont.clm_apply continuous_const
  have hP₂e : Continuous (fun t ↦ (momentumCurve L x vR t) e) :=
    hP₂cont.clm_apply continuous_const
  have hQ₂e : Continuous (fun t ↦ (Q₂ t) e) :=
    hQ₂cont.clm_apply continuous_const
  -- Left arc: the split integral reduces to the `τ` boundary term.
  have hleft : (∫ t in 0..τ, (stateDerivCurve L x vL t) ((φ : ℝ → ℝ) t • e)
        + (momentumCurve L x vL t) (deriv (φ : ℝ → ℝ) t • e))
      = (momentumCurve L x vL τ) e := by
    have hcongr : (∫ t in 0..τ, (stateDerivCurve L x vL t) ((φ : ℝ → ℝ) t • e)
          + (momentumCurve L x vL t) (deriv (φ : ℝ → ℝ) t • e))
        = (∫ t in 0..τ, (stateDerivCurve L x vL t e) * (φ : ℝ → ℝ) t
          + deriv (φ : ℝ → ℝ) t * ((momentumCurve L x vL t) e)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [map_smul, smul_eq_mul]
      ring
    have hPe : ∀ t ∈ Set.Ioo (min 0 τ) (max 0 τ),
        HasDerivAt (fun s ↦ (momentumCurve L x vL s) e) ((Q₁ t) e) t := by
      intro t ht
      rw [min_eq_left h0τ.le, max_eq_right h0τ.le] at ht
      have h := (hP₁deriv t ht).clm_apply (hasDerivAt_const (x := t) e)
      simpa only [map_zero, add_zero] using h
    have hφu : ∀ t ∈ Set.Ioo (min 0 τ) (max 0 τ),
        HasDerivAt (φ : ℝ → ℝ) (deriv (φ : ℝ → ℝ) t) t :=
      fun t _ ↦ hφd.differentiableAt.hasDerivAt
    have hui : IntervalIntegrable (deriv (φ : ℝ → ℝ)) volume 0 τ :=
      hφ.continuous_deriv_one.continuousOn.intervalIntegrable
    have hvi : IntervalIntegrable (fun t ↦ (Q₁ t) e) volume 0 τ :=
      hQ₁e.continuousOn.intervalIntegrable
    have hibp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
      hφd.continuous.continuousOn hP₁e.continuousOn hφu hPe hui hvi
    have hELe : (∫ t in 0..τ, (stateDerivCurve L x vL t e) * (φ : ℝ → ℝ) t)
        = ∫ t in 0..τ, ((Q₁ t) e) * (φ : ℝ → ℝ) t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htI : t ∈ Set.Icc 0 τ := by
        rwa [Set.uIcc_of_le h0τ.le] at ht
      change (stateDerivCurve L x vL t e) * (φ : ℝ → ℝ) t
        = ((Q₁ t) e) * (φ : ℝ → ℝ) t
      rw [hEL₁ t htI]
    have hI1 : IntervalIntegrable
        (fun t ↦ (stateDerivCurve L x vL t e) * (φ : ℝ → ℝ) t) volume 0 τ :=
      (hS₁e.mul hφd.continuous).continuousOn.intervalIntegrable
    have hI2 : IntervalIntegrable
        (fun t ↦ deriv (φ : ℝ → ℝ) t * ((momentumCurve L x vL t) e)) volume 0 τ :=
      (hφ.continuous_deriv_one.mul hP₁e).continuousOn.intervalIntegrable
    have hI3 : IntervalIntegrable
        (fun t ↦ (φ : ℝ → ℝ) t * ((Q₁ t) e)) volume 0 τ :=
      (hφd.continuous.mul hQ₁e).continuousOn.intervalIntegrable
    have hcomm : (∫ t in 0..τ, ((Q₁ t) e) * (φ : ℝ → ℝ) t)
        = ∫ t in 0..τ, (φ : ℝ → ℝ) t * ((Q₁ t) e) := by
      apply intervalIntegral.integral_congr
      intro t ht
      change ((Q₁ t) e) * (φ : ℝ → ℝ) t = (φ : ℝ → ℝ) t * ((Q₁ t) e)
      ring
    rw [hcongr, intervalIntegral.integral_add hI1 hI2, hELe, hcomm]
    rw [hφτ, hφ0, one_mul, zero_mul, sub_zero] at hibp
    rw [intervalIntegral.integral_add hI2 hI3] at hibp
    linear_combination hibp
  -- Right arc: the split integral reduces to minus the `τ` boundary term.
  have hright : (∫ t in τ..T, (stateDerivCurve L x vR t) ((φ : ℝ → ℝ) t • e)
        + (momentumCurve L x vR t) (deriv (φ : ℝ → ℝ) t • e))
      = -((momentumCurve L x vR τ) e) := by
    have hcongr : (∫ t in τ..T, (stateDerivCurve L x vR t) ((φ : ℝ → ℝ) t • e)
          + (momentumCurve L x vR t) (deriv (φ : ℝ → ℝ) t • e))
        = (∫ t in τ..T, (stateDerivCurve L x vR t e) * (φ : ℝ → ℝ) t
          + deriv (φ : ℝ → ℝ) t * ((momentumCurve L x vR t) e)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [map_smul, smul_eq_mul]
      ring
    have hPe : ∀ t ∈ Set.Ioo (min τ T) (max τ T),
        HasDerivAt (fun s ↦ (momentumCurve L x vR s) e) ((Q₂ t) e) t := by
      intro t ht
      rw [min_eq_left hτT.le, max_eq_right hτT.le] at ht
      have h := (hP₂deriv t ht).clm_apply (hasDerivAt_const (x := t) e)
      simpa only [map_zero, add_zero] using h
    have hφu : ∀ t ∈ Set.Ioo (min τ T) (max τ T),
        HasDerivAt (φ : ℝ → ℝ) (deriv (φ : ℝ → ℝ) t) t :=
      fun t _ ↦ hφd.differentiableAt.hasDerivAt
    have hui : IntervalIntegrable (deriv (φ : ℝ → ℝ)) volume τ T :=
      hφ.continuous_deriv_one.continuousOn.intervalIntegrable
    have hvi : IntervalIntegrable (fun t ↦ (Q₂ t) e) volume τ T :=
      hQ₂e.continuousOn.intervalIntegrable
    have hibp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivAt
      hφd.continuous.continuousOn hP₂e.continuousOn hφu hPe hui hvi
    have hELe : (∫ t in τ..T, (stateDerivCurve L x vR t e) * (φ : ℝ → ℝ) t)
        = ∫ t in τ..T, ((Q₂ t) e) * (φ : ℝ → ℝ) t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htI : t ∈ Set.Icc τ T := by
        rwa [Set.uIcc_of_le hτT.le] at ht
      change (stateDerivCurve L x vR t e) * (φ : ℝ → ℝ) t
        = ((Q₂ t) e) * (φ : ℝ → ℝ) t
      rw [hEL₂ t htI]
    have hI1 : IntervalIntegrable
        (fun t ↦ (stateDerivCurve L x vR t e) * (φ : ℝ → ℝ) t) volume τ T :=
      (hS₂e.mul hφd.continuous).continuousOn.intervalIntegrable
    have hI2 : IntervalIntegrable
        (fun t ↦ deriv (φ : ℝ → ℝ) t * ((momentumCurve L x vR t) e)) volume τ T :=
      (hφ.continuous_deriv_one.mul hP₂e).continuousOn.intervalIntegrable
    have hI3 : IntervalIntegrable
        (fun t ↦ (φ : ℝ → ℝ) t * ((Q₂ t) e)) volume τ T :=
      (hφd.continuous.mul hQ₂e).continuousOn.intervalIntegrable
    have hcomm : (∫ t in τ..T, ((Q₂ t) e) * (φ : ℝ → ℝ) t)
        = ∫ t in τ..T, (φ : ℝ → ℝ) t * ((Q₂ t) e) := by
      apply intervalIntegral.integral_congr
      intro t ht
      change ((Q₂ t) e) * (φ : ℝ → ℝ) t = (φ : ℝ → ℝ) t * ((Q₂ t) e)
      ring
    rw [hcongr, intervalIntegral.integral_add hI1 hI2, hELe, hcomm]
    rw [hφT, hφτ, zero_mul, one_mul, zero_sub] at hibp
    rw [intervalIntegral.integral_add hI2 hI3] at hibp
    linear_combination hibp
  -- The two `τ` boundary terms must cancel.
  rw [hleft, hright] at hvan0
  linarith

/-- **Second Weierstrass–Erdmann corner condition** (Kirk, *Optimal Control
Theory*, Dover 2004, §4.4; Liberzon, *Calculus of Variations and Optimal
Control Theory*, 2012, §4.4): for an autonomous Lagrangian (no explicit `t`
dependence), vanishing of the first variation under time reparametrisations
forces the energy `H = ⟪v, ∂ᵥL⟫ − L` to be continuous across the corner.

Here `hvan` packages the weak form of that time-reparametrisation first
variation — the integrated product-rule identity on each arc — while `hcons₁`
and `hcons₂` are the arc-wise energy-conservation laws (for autonomous `L`,
Euler–Lagrange solutions have constant energy on each smooth arc).  The proof
is the scalar analogue of `weierstrassErdmannMomentum`: with the bump
`ψ = φ`, `ψ τ = 1`, the fundamental theorem of calculus
(`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`) turns each arc
integral into a `τ` boundary term, and the two must cancel.  The continuity
hypotheses are stated globally on `ℝ`, as in `weierstrassErdmannMomentum`. -/
theorem weierstrassErdmannEnergy
    {L : E → E → ℝ} {T τ : ℝ} {x vL vR : ℝ → E} {D₁ D₂ : ℝ → ℝ}
    (hcorner : IsPiecewiseC₁On x vL vR T τ)
    (hH₁deriv : ∀ t ∈ Set.Ioo 0 τ, HasDerivAt (energyCurve L x vL) (D₁ t) t)
    (hH₂deriv : ∀ t ∈ Set.Ioo τ T, HasDerivAt (energyCurve L x vR) (D₂ t) t)
    (hcons₁ : ∀ t ∈ Set.Icc 0 τ, D₁ t = 0)
    (hcons₂ : ∀ t ∈ Set.Icc τ T, D₂ t = 0)
    (hH₁cont : Continuous (energyCurve L x vL))
    (hH₂cont : Continuous (energyCurve L x vR))
    (hD₁cont : Continuous D₁)
    (hD₂cont : Continuous D₂)
    (hvan : ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ 0 = 0 → ψ T = 0 →
      (∫ t in 0..τ, (energyCurve L x vL t) * deriv ψ t + D₁ t * ψ t)
        + (∫ t in τ..T, (energyCurve L x vR t) * deriv ψ t + D₂ t * ψ t) = 0) :
    energyCurve L x vL τ = energyCurve L x vR τ := by
  obtain ⟨h0τ, hτT, -, -, -⟩ := hcorner
  -- A bump radius with `closedBall τ rOut ⊆ (0, T)`.
  have hTτ : (0 : ℝ) < T - τ := sub_pos.mpr hτT
  set rOut : ℝ := min τ (T - τ) / 2 with hrOut
  have hmin_pos : (0 : ℝ) < min τ (T - τ) := lt_min h0τ hTτ
  have hrOut_pos : 0 < rOut := by rw [hrOut]; linarith
  have hball : Metric.closedBall τ rOut ⊆ Set.Ioo 0 T := by
    intro y hy
    rw [Metric.mem_closedBall, Real.dist_eq] at hy
    obtain ⟨hlo, hhi⟩ := abs_le.mp hy
    have hr1 : rOut ≤ τ / 2 := by
      rw [hrOut]
      have hmin : min τ (T - τ) ≤ τ := min_le_left _ _
      linarith
    have hr2 : rOut ≤ (T - τ) / 2 := by
      rw [hrOut]
      have hmin : min τ (T - τ) ≤ T - τ := min_le_right _ _
      linarith
    rw [Set.mem_Ioo]
    constructor <;> linarith
  -- The smooth time-reparametrisation bump, equal to `1` at `τ`.
  let φ : ContDiffBump τ := ⟨rOut / 2, rOut, by linarith, by linarith⟩
  have hφrOut : φ.rOut = rOut := rfl
  have hφ : ContDiff ℝ 1 (φ : ℝ → ℝ) := φ.contDiff
  have hφd : Differentiable ℝ (φ : ℝ → ℝ) := hφ.differentiable (by norm_num)
  have hφτ : (φ : ℝ → ℝ) τ = 1 := by
    apply φ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_self, show φ.rIn = rOut / 2 from rfl]
    linarith
  have hφsupp : tsupport (φ : ℝ → ℝ) ⊆ Set.Ioo 0 T := by
    rw [φ.tsupport_eq, hφrOut]
    exact hball
  have hφ0 : (φ : ℝ → ℝ) 0 = 0 := by
    by_contra hne
    exact absurd (hφsupp (subset_closure (Function.mem_support.mpr hne))) (by simp)
  have hφT : (φ : ℝ → ℝ) T = 0 := by
    by_contra hne
    exact absurd (hφsupp (subset_closure (Function.mem_support.mpr hne))) (by simp)
  have hvan0 := hvan (φ : ℝ → ℝ) hφ hφ0 hφT
  -- Arc-wise energy conservation kills the bulk `D` terms in the variation.
  have hD₁zero : (∫ t in 0..τ, D₁ t * (φ : ℝ → ℝ) t) = 0 := by
    have hcongr0 : (∫ t in 0..τ, D₁ t * (φ : ℝ → ℝ) t) = ∫ _ in 0..τ, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htI : t ∈ Set.Icc 0 τ := by
        rwa [Set.uIcc_of_le h0τ.le] at ht
      change D₁ t * (φ : ℝ → ℝ) t = 0
      rw [hcons₁ t htI, zero_mul]
    rw [hcongr0, intervalIntegral.integral_zero]
  have hD₂zero : (∫ t in τ..T, D₂ t * (φ : ℝ → ℝ) t) = 0 := by
    have hcongr0 : (∫ t in τ..T, D₂ t * (φ : ℝ → ℝ) t) = ∫ _ in τ..T, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htI : t ∈ Set.Icc τ T := by
        rwa [Set.uIcc_of_le hτT.le] at ht
      change D₂ t * (φ : ℝ → ℝ) t = 0
      rw [hcons₂ t htI, zero_mul]
    rw [hcongr0, intervalIntegral.integral_zero]
  have hIH₁ : IntervalIntegrable
      (fun t ↦ (energyCurve L x vL t) * deriv (φ : ℝ → ℝ) t) volume 0 τ :=
    (hH₁cont.mul hφ.continuous_deriv_one).continuousOn.intervalIntegrable
  have hID₁ : IntervalIntegrable (fun t ↦ D₁ t * (φ : ℝ → ℝ) t) volume 0 τ :=
    (hD₁cont.mul hφd.continuous).continuousOn.intervalIntegrable
  have hIH₂ : IntervalIntegrable
      (fun t ↦ (energyCurve L x vR t) * deriv (φ : ℝ → ℝ) t) volume τ T :=
    (hH₂cont.mul hφ.continuous_deriv_one).continuousOn.intervalIntegrable
  have hID₂ : IntervalIntegrable (fun t ↦ D₂ t * (φ : ℝ → ℝ) t) volume τ T :=
    (hD₂cont.mul hφd.continuous).continuousOn.intervalIntegrable
  have e1 : (∫ t in 0..τ, (energyCurve L x vL t) * deriv (φ : ℝ → ℝ) t
        + D₁ t * (φ : ℝ → ℝ) t)
      = ∫ t in 0..τ, (energyCurve L x vL t) * deriv (φ : ℝ → ℝ) t := by
    rw [intervalIntegral.integral_add hIH₁ hID₁, hD₁zero, add_zero]
  have e2 : (∫ t in τ..T, (energyCurve L x vR t) * deriv (φ : ℝ → ℝ) t
        + D₂ t * (φ : ℝ → ℝ) t)
      = ∫ t in τ..T, (energyCurve L x vR t) * deriv (φ : ℝ → ℝ) t := by
    rw [intervalIntegral.integral_add hIH₂ hID₂, hD₂zero, add_zero]
  rw [e1, e2] at hvan0
  -- Left arc: the integral reduces to the energy at `τ`.
  have hleft : (∫ t in 0..τ, (energyCurve L x vL t) * deriv (φ : ℝ → ℝ) t)
      = energyCurve L x vL τ := by
    have hprod : ∀ t ∈ Set.Ioo 0 τ,
        HasDerivAt (fun s ↦ (energyCurve L x vL s) * (φ : ℝ → ℝ) s)
          ((energyCurve L x vL t) * deriv (φ : ℝ → ℝ) t) t := by
      intro t ht
      have htI : t ∈ Set.Icc 0 τ := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      have h := (hH₁deriv t ht).mul hφd.differentiableAt.hasDerivAt
      rwa [hcons₁ t htI, zero_mul, zero_add] at h
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h0τ.le
      (hH₁cont.mul hφd.continuous).continuousOn hprod hIH₁
    simp only [Pi.mul_apply, hφτ, hφ0, mul_one, mul_zero, sub_zero] at hftc
    linear_combination hftc
  -- Right arc: the integral reduces to minus the energy at `τ`.
  have hright : (∫ t in τ..T, (energyCurve L x vR t) * deriv (φ : ℝ → ℝ) t)
      = -(energyCurve L x vR τ) := by
    have hprod : ∀ t ∈ Set.Ioo τ T,
        HasDerivAt (fun s ↦ (energyCurve L x vR s) * (φ : ℝ → ℝ) s)
          ((energyCurve L x vR t) * deriv (φ : ℝ → ℝ) t) t := by
      intro t ht
      have htI : t ∈ Set.Icc τ T := ⟨le_of_lt ht.1, le_of_lt ht.2⟩
      have h := (hH₂deriv t ht).mul hφd.differentiableAt.hasDerivAt
      rwa [hcons₂ t htI, zero_mul, zero_add] at h
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hτT.le
      (hH₂cont.mul hφd.continuous).continuousOn hprod hIH₂
    simp only [Pi.mul_apply, hφT, hφτ, mul_zero, mul_one, zero_sub] at hftc
    linear_combination hftc
  -- The two `τ` boundary terms must cancel.
  rw [hleft, hright] at hvan0
  linarith

end WeierstrassErdmann

section Foundations

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The uncurried Lagrangian `(t, y, v) ↦ L t y v`, used to state joint `C¹`
regularity in the state and velocity variables. -/
noncomputable def uncurryLagrangian (L : ℝ → E → E → ℝ) : ℝ × E × E → ℝ :=
  fun q ↦ L q.1 q.2.1 q.2.2

/-- The running part of the first variation `δJ(x; η)`, without the terminal term. -/
noncomputable def firstVariationIntegrand (L : ℝ → E → E → ℝ) (x η : ℝ → E) (t : ℝ) : ℝ :=
  (fderiv ℝ (fun y : E ↦ L t y (deriv x t)) (x t)) (η t)
    + (fderiv ℝ (fun v : E ↦ L t (x t) v) (deriv x t)) (deriv η t)

/-- `firstVariation` is the integral of `firstVariationIntegrand` plus the terminal
term. -/
theorem firstVariation_eq_integrand (L : ℝ → E → E → ℝ) (K : E → ℝ) (T : ℝ)
    (x η : ℝ → E) :
    firstVariation L K T x η =
      (∫ t in 0..T, firstVariationIntegrand L x η t) + (fderiv ℝ K (x T)) (η T) :=
  rfl

/-- Globally continuously differentiable curves with the specified endpoint values. -/
def fixedEndpointC1Curves (T : ℝ) (a b : E) : Set (ℝ → E) :=
  {y | ContDiff ℝ 1 y ∧ y 0 = a ∧ y T = b}

end Foundations

open Set

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The original variational functional depends only on the curve on its horizon.
Derivative values at the two endpoints do not affect its interval integral. -/
theorem _root_.cvFunctional_eq_of_eqOn (L : ℝ → E → E → ℝ) (K : E → ℝ)
    {T : ℝ} (hT : 0 < T) {x y : ℝ → E} (heq : EqOn x y (Icc 0 T)) :
    cvFunctional L K T x = cvFunctional L K T y := by
  unfold cvFunctional
  rw [heq ⟨hT.le, le_rfl⟩]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le hT.le
  intro t ht
  have hn : x =ᶠ[𝓝 t] y := by
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact heq hs
  change L t (x t) (deriv x t) = L t (y t) (deriv y t)
  rw [heq ⟨ht.1.le, ht.2.le⟩, hn.deriv_eq]

#check @IsPiecewiseC₁On
#check @IsPiecewiseC1On
#check @weierstrassErdmannMomentum
#check @weierstrassErdmannEnergy
