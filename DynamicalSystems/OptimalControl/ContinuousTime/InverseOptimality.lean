/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.DynamicProgramming
public import DynamicalSystems.Stability.Barbalat
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Nonlinear stabilizing optimal controls (optimal ⇒ stabilizing)

This file formalizes the *optimal ⇒ stabilizing* direction of Sontag, *Mathematical
Control Theory: Deterministic Finite Dimensional Systems*, 2nd ed., 1998, Ch. 8 §8.5
("Nonlinear Stabilizing Optimal Controls", printed pp. 390–394, PDF pp. 402–406):
an optimal control is stabilizing, with the value function serving as a Lyapunov
function for the closed loop.  The results are stated at the trajectory level over an
optimal admissible pair `(x, u)` together with the Bellman/HJB equality along the
trajectory; no global optimal-input function `x ↦ u` is postulated.  This mirrors the
relational style of the dynamic-programming development in
`DynamicalSystems.OptimalControl.ContinuousTime.DynamicProgramming`.

The book's §8.5 treats the infinite-horizon problem `J∞(x, ω) = ∫₀^∞ q(ξ, ω) dt` over
stabilizing controls.  The substrate available here is the finite-horizon problem
`ContinuousOCP` whose value function is `valueFunctionFrom prob t x = sInf` over the
costs of the time-shifted tail problem `continuousTailProblem prob t` (horizon
`prob.T - t`).  The three results below are therefore phrased as follows.

* `optimal_valueFunction_decrease`: along an optimal pair the value function decreases at
  exactly the running-cost rate, `d/dt valueFunctionFrom prob t (x t) = -L t (x t) (u t)`.
  This is the book's Lyapunov identity `V̇(ξ(t), ω(t)) + q(ξ(t), ω(t)) = 0` (Sontag
  (8.62), §8.5), obtained from the Bellman equality `V(t, x t) = ∫_t^T L + K(x T)` and the
  fundamental theorem of calculus.
* `optimal_stageCost_tendsto_zero`: if the value function is bounded below along the
  trajectory then the running cost vanishes asymptotically, `L t (x t) (u t) → 0`
  (Sontag §8.5, Proposition 8.5.1 and Theorem 42), via the monotone-decrease ⇒
  convergent-integral ⇒ Barbălat chain.
* `optimal_converges_to_origin`: if in addition the running cost is positive definite in
  the state (`c ‖x t‖² ≤ L t (x t) (u t)`, `c > 0`; the book's `q(x, u) > 0` for `x ≠ 0`),
  then the optimal trajectory converges to the origin, `‖x t‖ → 0` (Sontag §8.5,
  Theorem 42 / Corollary 8.5.3: "`V` is a global Lyapunov function for the closed-loop
  system").

## Implementation notes and honest hypotheses

The finite-horizon substrate cannot literally express the book's infinite horizon
`prob.T = ∞`.  Consequently:

* The Bellman equality is obtained from the *dynamic-programming optimality principle*
  `IsTailOptimal`: every time-shifted tail of the optimal pair is optimal for the
  corresponding tail subproblem.  This is the trajectory-formulated Bellman principle and
  it is what lets `continuousValueFunction_eq_continuousTotalCost` identify the
  cost-to-go along `(x, u)`.  (Deriving tail-optimality from a single optimal pair would
  require splicing controls, which the pointwise `HasDerivAt` admissibility predicate
  does not support.)
* The derivative statement `optimal_valueFunction_decrease` is therefore proved on the
  interior of the finite horizon, `t ∈ (0, prob.T)`.
* The asymptotic statements `optimal_stageCost_tendsto_zero` and
  `optimal_converges_to_origin` are the infinite-horizon conclusions `t → ∞`.  They take
  as an explicit hypothesis the *global* decrease
  `∀ t ≥ 0, HasDerivAt (fun s ↦ valueFunctionFrom prob s (x s)) (-L t (x t) (u t)) t`,
  i.e. the extension of `optimal_valueFunction_decrease` to all forward times (the
  infinite-horizon setting of §8.5).  Uniform continuity of the running-cost signal on
  `[0, ∞)` is the additional regularity hypothesis of the continuous-time Barbălat
  argument, and is stated explicitly.

## References

* E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional Systems*,
  2nd ed., Springer, 1998, Ch. 8 §8.5, printed pp. 390–394.
* L. D. Berkovitz and N. G. Medhin, *Nonlinear Optimal Control Theory*, CRC Press, 2013,
  Ch. 4 (existence of optimal pairs), used to justify the optimality relation.
-/

@[expose] public section

open scoped Interval Topology
open Filter MeasureTheory

variable {X U : Type*}

section Normed

variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Dynamic-programming optimality principle along a trajectory** (Sontag,
*Mathematical Control Theory*, 2nd ed., 1998, Ch. 8 §8.5, printed pp. 390–394).

Every time-shifted tail of `(x, u)`, started at `t` with initial state `x t` and horizon
`prob.T - t`, is an optimal admissible pair for the corresponding tail subproblem.  This is
the trajectory-level Bellman principle: it is the honest substitute (under the relational
admissibility predicate `IsAdmissiblePair`) for "`(x, u)` solves the finite-horizon problem
for every initial time". -/
def IsTailOptimal (prob : ContinuousOCP X U) (x : ℝ → X) (u : ℝ → U) : Prop :=
  ∀ t ∈ Set.Icc 0 prob.T,
    IsOptimalPair (continuousTailProblem prob t) (x t)
      (fun s ↦ x (t + s)) (fun s ↦ u (t + s))

/-- **Bellman equality along an optimal trajectory.**  Under the dynamic-programming
optimality principle `IsTailOptimal`, the value function evaluated along the trajectory
equals the cost-to-go `∫_t^T L + K(x T)` (Sontag, *Mathematical Control Theory*, 2nd ed.,
1998, Ch. 8 §8.5, printed pp. 390–394).  This is the identity `V(x₀) = J∞(x₀, ω)` of
Proposition 8.5.1 in finite-horizon form, and it is the "HJB verification equality" used to
derive the value-function decrease.

The proof combines the relational optimality supplied by `IsTailOptimal` with
`continuousValueFunction_eq_continuousTotalCost`, then rewrites the time-shifted tail
integral over `0..(T - t)` as an integral over `t..T`. -/
theorem valueFunctionFrom_eq_integral_of_isTailOptimal
    (prob : ContinuousOCP X U) (x : ℝ → X) (u : ℝ → U)
    (hopt : IsTailOptimal prob x u) :
    ∀ t ∈ Set.Icc 0 prob.T,
      valueFunctionFrom prob t (x t) =
        (∫ s in t..prob.T, prob.L s (x s) (u s)) + prob.K (x prob.T) := by
  intro t ht
  have hcost := continuousValueFunction_eq_continuousTotalCost
    (continuousTailProblem prob t) (x t) (fun s ↦ x (t + s)) (fun s ↦ u (t + s))
    (hopt t ht)
  unfold valueFunctionFrom
  rw [hcost]
  unfold continuousTotalCost
  simp only [continuousTailProblem_T, continuousTailProblem_L, continuousTailProblem_K]
  rw [intervalIntegral.integral_comp_add_left (f := fun s ↦ prob.L s (x s) (u s)) t]
  have hT : t + (prob.T - t) = prob.T := by ring
  rw [hT, add_zero]

/-- **The value function decreases at the running-cost rate along an optimal pair**
(Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 8 §8.5, equation (8.62),
printed pp. 390–394).

This is the Lyapunov identity `V̇(ξ(t), ω(t)) + q(ξ(t), ω(t)) = 0` along the optimal
trajectory: at every interior time `t ∈ (0, T)`,

`d/dt valueFunctionFrom prob t (x t) = -L t (x t) (u t)`.

It is proved from the Bellman equality `valueFunctionFrom_eq_integral_of_isTailOptimal` and
the fundamental theorem of calculus (the derivative of `t ↦ ∫_t^T L` is `-L t`), with the
running-cost signal assumed continuous on `[0, T]` so that the FTC applies pointwise. -/
theorem optimal_valueFunction_decrease (prob : ContinuousOCP X U) (x : ℝ → X) (u : ℝ → U)
    (hopt : IsTailOptimal prob x u)
    (hcont : ContinuousOn (fun s ↦ prob.L s (x s) (u s)) (Set.Icc 0 prob.T))
    {t : ℝ} (ht : t ∈ Set.Ioo 0 prob.T) :
    HasDerivAt (fun s ↦ valueFunctionFrom prob s (x s)) (-(prob.L t (x t) (u t))) t := by
  let g : ℝ → ℝ := fun s ↦ prob.L s (x s) (u s)
  have hbell := valueFunctionFrom_eq_integral_of_isTailOptimal prob x u hopt
  have hcontIoo : ContinuousOn g (Set.Ioo 0 prob.T) := hcont.mono Set.Ioo_subset_Icc_self
  have hcontAt : ContinuousAt g t :=
    hcontIoo.continuousAt (IsOpen.mem_nhds isOpen_Ioo ht)
  have hmeas : StronglyMeasurableAtFilter g (𝓝 t) volume :=
    ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hcontIoo t ht
  have hint : IntervalIntegrable g volume t prob.T :=
    ContinuousOn.intervalIntegrable_of_Icc ht.2.le
      (hcont.mono fun s hs ↦ ⟨le_trans (le_of_lt ht.1) hs.1, hs.2⟩)
  have hderiv_int : HasDerivAt (fun s ↦ ∫ r in s..prob.T, g r) (-g t) t :=
    intervalIntegral.integral_hasDerivAt_left hint hmeas hcontAt
  have hderiv_rhs :
      HasDerivAt (fun s ↦ (∫ r in s..prob.T, g r) + prob.K (x prob.T)) (-g t) t :=
    hderiv_int.add_const _
  have hev : (fun s ↦ valueFunctionFrom prob s (x s)) =ᶠ[𝓝 t]
      (fun s ↦ (∫ r in s..prob.T, g r) + prob.K (x prob.T)) := by
    filter_upwards [IsOpen.mem_nhds isOpen_Ioo ht] with s hs
    exact hbell s (Set.Ioo_subset_Icc_self hs)
  rw [Filter.EventuallyEq.hasDerivAt_iff hev]
  exact hderiv_rhs

/-- **The running cost vanishes along an optimal trajectory** (Sontag, *Mathematical
Control Theory*, 2nd ed., 1998, Ch. 8 §8.5, Proposition 8.5.1 and Theorem 42, printed
pp. 390–394).

If the value function is bounded below along the trajectory (`BddBelow`; for instance
supplied by nonnegative costs through `bddBelow_continuousCostSet`), the running cost is
nonnegative, the value function decreases at the running-cost rate for all forward times,
and the running-cost signal is uniformly continuous on `[0, ∞)`, then

`L t (x t) (u t) → 0` as `t → ∞`.

The proof is the continuous-time analogue of the MPC campaign's
`mpc_stageCost_tendsto_zero`: the monotone decrease makes the integral
`t ↦ ∫₀ᵗ L` bounded, hence convergent, and Barbălat's lemma upgrades the convergent
integral of the uniformly continuous nonnegative signal to convergence of the signal
itself (Barbalat.tendsto_zero_of_hasDerivAt_le_neg_of_boundedBelow_of_uniformContinuousOn).

The global decrease hypothesis is the extension of `optimal_valueFunction_decrease` to all
forward times, i.e. the infinite-horizon setting of §8.5; see the module implementation
notes. -/
theorem optimal_stageCost_tendsto_zero (prob : ContinuousOCP X U) (x : ℝ → X) (u : ℝ → U)
    (hV : BddBelow ((fun t ↦ valueFunctionFrom prob t (x t)) '' Set.Ici 0))
    (hL : ∀ t, 0 ≤ t → 0 ≤ prob.L t (x t) (u t))
    (hdec : ∀ t, 0 ≤ t → HasDerivAt (fun s ↦ valueFunctionFrom prob s (x s))
      (-(prob.L t (x t) (u t))) t)
    (huc : UniformContinuousOn (fun t ↦ prob.L t (x t) (u t)) (Set.Ici 0)) :
    Tendsto (fun t ↦ prob.L t (x t) (u t)) atTop (𝓝 0) := by
  let V : ℝ → ℝ := fun t ↦ valueFunctionFrom prob t (x t)
  let w : ℝ → ℝ := fun t ↦ prob.L t (x t) (u t)
  have hV' : BddBelow (V '' Set.Ici 0) := hV
  have hw : ∀ t, 0 ≤ t → 0 ≤ w t := hL
  have hderiv : ∀ t, 0 ≤ t → HasDerivAt V (deriv V t) t := by
    intro t ht
    have h := hdec t ht
    rw [h.deriv]
    exact h
  have hineq : ∀ t, 0 ≤ t → deriv V t ≤ -(w t) := by
    intro t ht
    rw [(hdec t ht).deriv]
  change Tendsto w atTop (𝓝 0)
  exact Barbalat.tendsto_zero_of_hasDerivAt_le_neg_of_boundedBelow_of_uniformContinuousOn
    hV' hw hderiv hineq huc

/-- **The optimal trajectory converges to the origin** (Sontag, *Mathematical Control
Theory*, 2nd ed., 1998, Ch. 8 §8.5, Theorem 42 and Corollary 8.5.3, printed pp. 390–394).

Under the hypotheses of `optimal_stageCost_tendsto_zero`, if in addition the running cost is
positive definite in the state along the trajectory,
`c ‖x t‖² ≤ L t (x t) (u t)` for some `c > 0` (the book's `q(x, u) > 0` for `x ≠ 0`,
formalized as a quadratic coercivity lower bound), then

`‖x t‖ → 0` as `t → ∞`,

i.e. `V` is a global Lyapunov function for the closed-loop system and the optimal
trajectory is attracted to the origin.

The proof squeezes the positive-definite state norm from below by the running cost and
applies `Barbalat.tendsto_zero_of_tendsto_zero_of_sq_le` to the convergence of the latter. -/
theorem optimal_converges_to_origin (prob : ContinuousOCP X U) (x : ℝ → X) (u : ℝ → U)
    (hV : BddBelow ((fun t ↦ valueFunctionFrom prob t (x t)) '' Set.Ici 0))
    (hL : ∀ t, 0 ≤ t → 0 ≤ prob.L t (x t) (u t))
    (hdec : ∀ t, 0 ≤ t → HasDerivAt (fun s ↦ valueFunctionFrom prob s (x s))
      (-(prob.L t (x t) (u t))) t)
    (huc : UniformContinuousOn (fun t ↦ prob.L t (x t) (u t)) (Set.Ici 0))
    {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ t, 0 ≤ t → c * ‖x t‖ ^ 2 ≤ prob.L t (x t) (u t)) :
    Tendsto (fun t ↦ ‖x t‖) atTop (𝓝 0) := by
  have hw := optimal_stageCost_tendsto_zero prob x u hV hL hdec huc
  exact Barbalat.tendsto_zero_of_tendsto_zero_of_sq_le hc hw hcoer

end Normed
