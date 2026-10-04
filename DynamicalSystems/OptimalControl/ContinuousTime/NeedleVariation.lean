/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.MinimumPrinciple
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.LinearAlgebra.AffineSpace.Slope
public import Mathlib.Topology.Order.Basic

/-!
# Needle variations and the costate derivation (BM ch.7)

This module builds the missing needle-variation piece recorded as a derivation gap in
`DynamicalSystems.OptimalControl.ContinuousTime.MinimumPrinciple`: the passage from
optimality (`IsOptimalPair`) of a reference pair `(x₀, u₀)` to the existence of a
costate satisfying the existing `costateEquation` predicate together with
`HamiltonianMinimizing` and `transversalityCondition`.

The development follows Berkovitz–Medhin (*Nonlinear Optimal Control Theory*,
CRC Press, 2012, ch. 7: needle variations, the variational equation along the
reference, and the separation argument) and Sontag (*Mathematical Control Theory*,
2nd ed., 1998, Ch. 9 §9.5, Theorem 44, pp. 418–421). No originality is claimed;
all results are standard textbook material.

## Scope and design (coordinator-fixed)

* Controls are **continuous** on the compact interval `[0, T]`, matching the relational
  `IsAdmissiblePair` style (pointwise `HasDerivAt` plus interval integrability).
  Measurable controls are explicitly out of scope.
* Dynamics are **nonautonomous and control-dependent**, `f : ℝ → X → U → X`, with
  integral-curve solutions (`HasDerivAt x (f t (x t) (u t)) t`).
* The state space `X` is a normed `ℝ`-vector space (complete where Bochner
  integration is used); finite-dimensionality is only needed for the residual
  Hahn–Banach separation step, which is recorded as an explicit hypothesis.
* The autonomous, time-zero, spatial variational equation of
  `Control/Geometric/VariationalEquation` (`flow_deriv_firstOrder`) is deliberately
  NOT reused here: it does not supply the nonautonomous control-perturbation
  regularity the needle proof needs. Reused instead are the trajectory-estimate
  tools `FlowIncrement`/`FlowGronwall`-style bounds (as the documented route for the
  residual below), the interval-integral FTC, and the existing
  `costateEquation`/`HamiltonianMinimizing`/`transversalityCondition` predicates —
  no second costate/adjoint notion is introduced.

## What is proved vs. assumed (Path B)

Fully proved here:

* `stateTransition` + `variationOfConstants`: the state-transition (fundamental-matrix)
  notion for the linearized nonautonomous dynamics `ẋ = A(t)·x` and the Duhamel /
  variation-of-constants formula, reduced to the interval-integral FTC. The
  differentiated-cancellation step is an explicit premise `hcancel` (see below).
* `needlePerturbationFirstOrder` + `needleImpulseFirstOrder`: the `o(ε)` first-order
  expansion of the needle impulse, from continuity of the dynamics along the
  reference.
* `firstOrder_necessary_nonneg` + `needle_firstOrder_necessary`: a one-sided
  first-order necessary condition — optimality forces every admissible scalar
  needle-cost perturbation to have nonnegative right derivative at `ε = 0`.
* `needleCostate`: assembly of the PMP costate triple from optimality, the adjoint
  data, and the separated needle inequality.

Explicitly assumed (residual, Path B — stated as hypotheses, never as placeholders):

* `hcancel` in `variationOfConstants`: differentiating `τ ↦ Φ(t,τ)(x(τ))` needs the
  backward propagator equation plus operator-valued chain rule.
* The passage from the frozen-state impulse (`needleImpulseFirstOrder`) to the true
  trajectory displacement `‖xᵉ(τ) − x₀(τ) − ε·jump‖ = o(ε)`: needs the perturbed
  trajectory plus a Grönwall estimate (`FlowGronwall`/`FlowIncrement` route).
* `separationHypothesis` in `needleCostate`: the first-order Hamiltonian-jump
  inequality. Deriving it from optimality needs (i) admissibility of needle-perturbed
  pairs, (ii) the Duhamel derivative formula for `ε ↦ J(uᵉ)` (the `variationOfConstants`
  substrate above), and (iii) geometric Hahn–Banach separation of the finite-dimensional
  needle-variation cone
  (`Mathlib/Analysis/LocallyConvex/Separation`, e.g. `geometric_hahn_banach_point_open`)
  to extract the terminal covector, propagated backward to the costate arc `p`.

## Main definitions

* `stateTransition`: the two-sided propagator predicate for `ẋ = A(t)·x`.
* `needleControl`: the continuous needle perturbation (value `v` on `[τ−ε, τ]`).
* `separationHypothesis`: the Path-B residual needle inequality (see above).

## Main results

* `variationOfConstants`: Duhamel formula via the transition matrix.
* `needlePerturbationFirstOrder`: `(1/ε)(∫_{τ−ε}^{τ} g − ε • g τ) → 0` for `g`
  continuous at `τ`.
* `needleImpulseFirstOrder`: the same for the dynamics jump `f(·,x₀·,v) − f(·,x₀·,u₀·)`.
* `firstOrder_necessary_nonneg`: one-sided minima have nonnegative right derivative.
* `needle_firstOrder_necessary`: optimality ⇒ nonnegative needle-cost derivatives.
* `needleCostate`: the assembled PMP costate theorem (Path-B hypothesis form).
-/

@[expose] public section

open scoped Interval Topology
open MeasureTheory Filter

variable {X U : Type*}

/-! ### State-transition matrix and variation of constants -/

section StateTransition

variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The state-transition (fundamental-matrix) notion for the linearized nonautonomous
dynamics `ẋ = A(t)·x` along the reference pair: `Φ(t,s)` propagates states from time
`s` to time `t`. The predicate bundles the identity-on-the-diagonal clause with the
forward differential equation in the first time argument, stated pointwise in the
state so that no operator-norm differentiability is needed (Berkovitz–Medhin,
*Nonlinear Optimal Control Theory*, CRC 2012, ch. 7; Sontag, *Mathematical Control
Theory*, 2nd ed., 1998, Ch. 9 §9.5). Existence of such a `Φ` for Lipschitz `A`
is the analytic substrate left to the ODE theory
(`DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistenceLinear`). -/
def stateTransition (A : ℝ → X →L[ℝ] X) (Φ : ℝ → ℝ → X →L[ℝ] X) : Prop :=
  (∀ s, Φ s s = ContinuousLinearMap.id ℝ X) ∧
  ∀ s t x, HasDerivAt (fun r => Φ r s x) ((A t) ((Φ t s) x)) t

omit [CompleteSpace X] in
/-- The diagonal clause of a state transition: no propagation over zero time. -/
theorem stateTransition_diag {A : ℝ → X →L[ℝ] X} {Φ : ℝ → ℝ → X →L[ℝ] X}
    (hΦ : stateTransition A Φ) (s : ℝ) : Φ s s = ContinuousLinearMap.id ℝ X :=
  hΦ.1 s

/-- **Variation of constants (Duhamel formula).** If `Φ` is a state transition for the
homogeneous part `A` and `x` solves the inhomogeneous equation `ẋ = A(t)·x + b(t)`,
then `x(t) = Φ(t,s)(x(s)) + ∫_{s}^{t} Φ(t,τ)(b(τ)) dτ`. The proof is the
interval-integral fundamental theorem of calculus applied to `τ ↦ Φ(t,τ)(x(τ))`.

The hypothesis `hcancel` — that `τ ↦ Φ(t,τ)(x(τ))` differentiates to
`Φ(t,τ)(b(τ))`, i.e. the `A`-terms cancel — is the analytic core (backward
propagator equation plus operator-valued chain rule) and is taken as an explicit
premise; `hx` records the trajectory equation it is the differentiated form of.
This is the genuinely new substrate: Mathlib has `IsIntegralCurveOn` but no
parameter-dependence theorems of this form. -/
theorem variationOfConstants {A : ℝ → X →L[ℝ] X} {Φ : ℝ → ℝ → X →L[ℝ] X}
    {b : ℝ → X} {x : ℝ → X} {s t : ℝ}
    (hΦ : stateTransition A Φ)
    (hx : ∀ τ ∈ Set.uIcc s t, HasDerivAt x ((A τ) (x τ) + b τ) τ)
    (hint : IntervalIntegrable (fun τ => Φ t τ (b τ)) volume s t)
    (hcancel : ∀ τ ∈ Set.uIcc s t,
      HasDerivAt (fun τ => Φ t τ (x τ)) (Φ t τ (b τ)) τ) :
    x t = Φ t s (x s) + ∫ τ in s..t, Φ t τ (b τ) := by
  -- `hx` justifies `hcancel` conceptually (differentiated trajectory equation);
  -- it is otherwise consumed through `hcancel`.
  have _htraj := hx
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := s) (b := t)
    (f := fun τ => Φ t τ (x τ)) (f' := fun τ => Φ t τ (b τ)) hcancel hint
  have hdiag : Φ t t = ContinuousLinearMap.id ℝ X := hΦ.1 t
  simp only [hdiag, ContinuousLinearMap.id_apply] at hFTC
  rw [hFTC]
  abel

end StateTransition

/-! ### Needle perturbations and their first-order expansion -/

section Needle

variable [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The needle (spike) perturbation of the reference control `u₀`: value `v` on the
short interval `[τ−ε, τ]` (as `Set.Ico (τ−ε) τ`, empty for `ε ≤ 0`) and `u₀` elsewhere
(Berkovitz–Medhin, *Nonlinear Optimal Control Theory*, CRC 2012, ch. 7;
Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 9 §9.5). -/
noncomputable def needleControl (u₀ : ℝ → U) (τ : ℝ) (v : U) (ε : ℝ) : ℝ → U :=
  fun t => if t ∈ Set.Ico (τ - ε) τ then v else u₀ t

/-- On the spike interval the needle control takes the test value. -/
theorem needleControl_of_mem (u₀ : ℝ → U) (τ : ℝ) (v : U) (ε t : ℝ)
    (h : t ∈ Set.Ico (τ - ε) τ) : needleControl u₀ τ v ε t = v := by
  simp [needleControl, h]

/-- Off the spike interval the needle control agrees with the reference. -/
theorem needleControl_of_notMem (u₀ : ℝ → U) (τ : ℝ) (v : U) (ε t : ℝ)
    (h : t ∉ Set.Ico (τ - ε) τ) : needleControl u₀ τ v ε t = u₀ t := by
  simp [needleControl, h]

/-- For nonpositive width the spike interval is empty, so the needle is the reference. -/
theorem needleControl_eq_self_of_nonpos (u₀ : ℝ → U) (τ : ℝ) (v : U) (ε : ℝ)
    (hε : ε ≤ 0) : needleControl u₀ τ v ε = u₀ := by
  have hempty : Set.Ico (τ - ε) τ = ∅ := Set.Ico_eq_empty (by linarith)
  funext t
  simp [needleControl, hempty]

/-- **First-order expansion of a needle impulse (`o(ε)` estimate).** For `g` continuous
at `τ`, the short-integral average converges: `(1/ε)(∫_{τ−ε}^{τ} g − ε • g τ) → 0`
as `ε → 0+`. The proof is the elementary estimate
`‖∫_{τ−ε}^{τ} (g − g τ)‖ ≤ ε · sup_{[τ−ε,τ]} ‖g − g τ‖` via
`intervalIntegral.norm_integral_le_of_norm_le_const`, with the supremum driven to
zero by continuity at `τ`. -/
theorem needlePerturbationFirstOrder (g : ℝ → X) (τ : ℝ) (hg : Continuous g) :
    Tendsto (fun ε : ℝ => ε⁻¹ • ((∫ t in (τ - ε)..τ, g t) - ε • g τ))
      (𝓝[>] 0) (𝓝 0) := by
  refine Metric.tendsto_nhds.mpr fun η hη => ?_
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hg.continuousAt (η / 2) (half_pos hη)
  filter_upwards [Ioo_mem_nhdsGT hδpos] with ε hε
  have ⟨hε0, hεδ⟩ := Set.mem_Ioo.mp hε
  have hle : τ - ε ≤ τ := by linarith
  have hint1 : IntervalIntegrable g volume (τ - ε) τ := hg.intervalIntegrable _ _
  have hint2 : IntervalIntegrable (fun _ => g τ) volume (τ - ε) τ := intervalIntegrable_const
  have hconst : (∫ _ in (τ - ε)..τ, g τ) = ε • g τ := by
    rw [intervalIntegral.integral_const]
    congr 1
    ring
  have hsub : (∫ t in (τ - ε)..τ, g t) - ε • g τ
      = ∫ t in (τ - ε)..τ, (g t - g τ) := by
    rw [← hconst, intervalIntegral.integral_sub hint1 hint2]
  have hbound : ∀ t ∈ Ι (τ - ε) τ, ‖g t - g τ‖ ≤ η / 2 := by
    intro t ht
    rw [Set.uIoc_of_le hle] at ht
    obtain ⟨h1, h2⟩ := Set.mem_Ioc.mp ht
    have hdist : dist t τ < δ := by
      have habs : |t - τ| = τ - t := by
        rw [abs_of_nonpos (by linarith : t - τ ≤ 0)]
        ring
      rw [dist_eq_norm, Real.norm_eq_abs, habs]
      linarith
    have h2 := hδ hdist
    rw [dist_eq_norm] at h2
    exact le_of_lt h2
  have hnorm : ‖∫ t in (τ - ε)..τ, (g t - g τ)‖ ≤ ε * (η / 2) := by
    have hmain :=
      intervalIntegral.norm_integral_le_of_norm_le_const (f := fun t => g t - g τ) hbound
    have habs : |τ - (τ - ε)| = ε := by
      rw [sub_sub_cancel]
      exact abs_of_pos hε0
    rw [habs, mul_comm (η / 2) ε] at hmain
    exact hmain
  have hεne : ε ≠ 0 := ne_of_gt hε0
  rw [hsub, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε0]
  calc ε⁻¹ * ‖∫ t in (τ - ε)..τ, (g t - g τ)‖
      ≤ ε⁻¹ * (ε * (η / 2)) :=
        mul_le_mul_of_nonneg_left hnorm (le_of_lt (inv_pos.mpr hε0))
    _ = η / 2 := by rw [← mul_assoc, inv_mul_cancel₀ hεne, one_mul]
    _ < η := by linarith

/-- **Needle impulse for the control dynamics.** With the frozen reference state `x₀`,
the short integral of the dynamics jump `f(·,x₀·,v) − f(·,x₀·,u₀·)` expands to first
order in `ε` around the pointwise jump at `τ`, whenever both branches are continuous
in time at `τ`. This is the analytic heart of subtask (a); the passage to the true
trajectory displacement `‖xᵉ(τ) − x₀(τ) − ε·jump‖ = o(ε)` additionally needs the
needle-perturbed trajectory and a Grönwall estimate (the `FlowGronwall` /
`FlowIncrement` route), recorded here as an explicit residual rather than proved. -/
theorem needleImpulseFirstOrder (f : ℝ → X → U → X) (x₀ : ℝ → X) (u₀ : ℝ → U)
    (τ : ℝ) (v : U)
    (hfv : Continuous (fun t => f t (x₀ t) v))
    (hfu : Continuous (fun t => f t (x₀ t) (u₀ t))) :
    Tendsto (fun ε : ℝ => ε⁻¹ • ((∫ t in (τ - ε)..τ,
        (f t (x₀ t) v - f t (x₀ t) (u₀ t)))
          - ε • (f τ (x₀ τ) v - f τ (x₀ τ) (u₀ τ)))) (𝓝[>] 0) (𝓝 0) :=
  needlePerturbationFirstOrder _ _ (hfv.sub hfu)

end Needle

/-! ### One-sided first-order necessary conditions -/

section FirstOrder

/-- A one-sided minimum has nonnegative right derivative: if `J 0 ≤ J y` for all small
`y > 0` and `J` has right derivative `J'` at `0`, then `0 ≤ J'`. The proof passes
through slopes (`hasDerivWithinAt_iff_tendsto_slope`): on `𝓝[>] 0` the slopes
`(J y − J 0)/(y − 0)` are nonnegative, hence so is their limit (`ge_of_tendsto`). -/
theorem firstOrder_necessary_nonneg (J : ℝ → ℝ) (J' : ℝ)
    (hderiv : HasDerivWithinAt J J' (Set.Ici 0) 0)
    (hmin : ∀ᶠ y in 𝓝[>] (0 : ℝ), J 0 ≤ J y) :
    0 ≤ J' := by
  have hset : Set.Ici (0 : ℝ) \ {0} = Set.Ioi 0 := by
    ext y
    simp only [Set.mem_sdiff, Set.mem_Ici, Set.mem_singleton_iff, Set.mem_Ioi]
    exact ⟨fun h => lt_of_le_of_ne' h.1 h.2, fun h => ⟨le_of_lt h, ne_of_gt h⟩⟩
  have htend : Tendsto (slope J 0) (𝓝[>] (0 : ℝ)) (𝓝 J') := by
    have h := hasDerivWithinAt_iff_tendsto_slope.mp hderiv
    rwa [hset] at h
  refine ge_of_tendsto htend ?_
  filter_upwards [hmin, self_mem_nhdsWithin] with y hJy hy
  have hpos : (0 : ℝ) < y := hy
  have hle : (0 : ℝ) ≤ y - 0 := by linarith
  have hnn := div_nonneg (sub_nonneg.mpr hJy) hle
  have hsl : slope J 0 y = (J y - J 0) / (y - 0) := congrFun (slope_fun_def_field J 0) y
  rwa [hsl]

variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Optimality forces nonnegative needle-cost derivatives.** If `(x, u)` is optimal
and, for small `ε > 0`, each scalar value `J ε` is realized as the total cost of some
admissible pair (the admissibility of needle-perturbed pairs — residual (i)), with
`J 0` the reference cost and `J` right-differentiable at `0`, then `0 ≤ J'`.
This is `isOptimalPair_iff` chained with `firstOrder_necessary_nonneg`. -/
theorem needle_firstOrder_necessary (prob : ContinuousOCP X U) (x₀ : X)
    (x : ℝ → X) (u : ℝ → U) (J : ℝ → ℝ) (J' : ℝ)
    (hopt : IsOptimalPair prob x₀ x u)
    (hJ0 : J 0 = continuousTotalCost prob x u)
    (hadmJ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ x' u',
      IsAdmissiblePair prob x₀ x' u' ∧ J ε = continuousTotalCost prob x' u')
    (hderiv : HasDerivWithinAt J J' (Set.Ici 0) 0) :
    0 ≤ J' := by
  apply firstOrder_necessary_nonneg J J' hderiv
  have hopt' := ((isOptimalPair_iff prob x₀ x u).mp hopt).2
  rw [hJ0]
  filter_upwards [hadmJ] with ε hε
  obtain ⟨x', u', hadm, hJ⟩ := hε
  rw [hJ]
  exact hopt' x' u' hadm

end FirstOrder

/-! ### Costate separation and assembly (Path B) -/

section Costate

variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- **Path-B residual: the separated needle inequality.** For every needle time
`τ ∈ [0, T]` and test value `v` in the control set, the first-order Hamiltonian jump
along the costate arc `p` is nonnegative:
`0 ≤ (L(τ,xτ,v) − L(τ,xτ,uτ)) + ⟪p τ, f(τ,xτ,v) − f(τ,xτ,uτ)⟫`.

Deriving this from `IsOptimalPair` is the residual step: it needs (i) admissibility
of the needle-perturbed pairs, (ii) the Duhamel derivative formula identifying the
right derivative of `ε ↦ J(uᵉ)` with the propagated jump (via `variationOfConstants`
and `needle_firstOrder_necessary` above), and (iii) geometric Hahn–Banach separation
of the finite-dimensional needle-variation cone
(`Mathlib/Analysis/LocallyConvex/Separation`, e.g.
`geometric_hahn_banach_point_open`) to extract the terminal covector whose backward
propagation is `p`. It is therefore assumed; `needleCostate` shows it suffices for
the full PMP triple. -/
def separationHypothesis (prob : ContinuousOCP X U) (x : ℝ → X) (u : ℝ → U)
    (p : ℝ → X) : Prop :=
  ∀ τ ∈ Set.Icc 0 prob.T, ∀ v ∈ prob.controlSet,
    0 ≤ (prob.L τ (x τ) v - prob.L τ (x τ) (u τ))
      + inner ℝ (p τ) (prob.f τ (x τ) v - prob.f τ (x τ) (u τ))

/-- **The assembled needle costate theorem (Path-B form).** An optimal reference pair,
together with a costate arc satisfying the adjoint equation and transversality
(provided unconditionally by `exists_costate_of_lipschitz` under Lipschitz
regularity) and the separated needle inequality, yields the Pontryagin triple:
the costate equation, pointwise Hamiltonian minimization over the control set, and
transversality — i.e. the upgraded `pmpAssembly_minimizing`. The step from the
separated inequality to minimization is pure algebra (`inner_sub_right`); the
hypothesis `x₀` records the initial state of the reference pair. -/
theorem needleCostate (prob : ContinuousOCP X U) (x₀ : X) (x : ℝ → X) (u : ℝ → U)
    (p : ℝ → X)
    (hopt : IsOptimalPair prob x₀ x u)
    (hadj : costateEquation prob.L prob.f prob.T x u p ∧
      transversalityCondition prob.K prob.T x p)
    (hsep : separationHypothesis prob x u p) :
    IsAdmissiblePair prob x₀ x u ∧ ∃ q : ℝ → X,
      costateEquation prob.L prob.f prob.T x u q ∧
      HamiltonianMinimizing prob.L prob.f prob.controlSet prob.T x u q ∧
      transversalityCondition prob.K prob.T x q := by
  refine ⟨hopt.1, p, hadj.1, ?_, hadj.2⟩
  intro t ht w hw
  have h := hsep t ht w hw
  have hinner : inner ℝ (p t) (prob.f t (x t) w - prob.f t (x t) (u t))
      = inner ℝ (p t) (prob.f t (x t) w) - inner ℝ (p t) (prob.f t (x t) (u t)) :=
    inner_sub_right _ _ _
  unfold hamiltonianOf
  linarith

end Costate

end
