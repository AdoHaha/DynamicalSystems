/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.MPC.Basic
public import DynamicalSystems.OptimalControl.FiniteHorizon
public import DynamicalSystems.OptimalControl.ValueFunction
public import DynamicalSystems.DiscreteTime.Lyapunov
public import Mathlib.Topology.Order.Real
public import Mathlib.Analysis.Normed.Group.Basic

/-! # Closed-loop MPC stability and value-function descent

This file formalizes the central nominal stability theorem for receding-horizon model
predictive control following Rawlings, Mayne and Diehl, *Model Predictive Control: Theory,
Computation, and Design*, 2nd ed., 2019, Chapter 2, §2.4.2–2.4.3 (printed pp. 114–120).

## Mathematical overview

Given a finite-horizon optimal control problem `prob` with dynamics `f`, stage cost `ℓ`,
terminal cost `Vf`, terminal constraint set `Xf`, and horizon `N > 0`, the receding-horizon
control law `κ_N(x) = mpcLaw prob x hN h` applies the first control input of an optimal
sequence to the system, yielding the one-step closed-loop successor `x⁺ = mpcStep prob x hN h`.

1. **Value-function descent (eq. (2.17), §2.4.2, printed p. 117):**
   If `Vf` is a discrete terminal control-Lyapunov function on `Xf` (`IsTerminalCLF`) and
   `Xf ⊆ Xs`, then the value function satisfies
   `V(x⁺) ≤ V(x) − ℓ(x, κ_N(x))`.
   The candidate warm-start input for `x⁺` is `ũ = Fin.snoc (Fin.tail u*) w` where `w ∈ Us` is
   the stabilizing terminal control selected by `IsTerminalCLF` at the terminal state
   `x_N = rollout x u* (Fin.last N) ∈ Xf`; this warm-start pattern has the form of eq. (2.26),
   §2.7, printed p. 147. (Value-function monotonicity is Proposition 2.18, printed p. 118.)

2. **Decay rate convergence (discrete dissipation bridge):**
   Instantiating the scalar dissipation bridge `tendsto_zero_of_succ_le_sub` with
   `v n = V(x_n)` and `w n = ℓ(x_n, κ_N(x_n))` turns the telescoping decrease
   `v (n + 1) ≤ v n − w n` into summability and convergence of the stage cost:
   `ℓ(x_n, κ_N(x_n)) → 0`.

3. **Convergence to the origin (Theorem 2.19, printed pp. 119–120):**
   If the stage cost is coercive (`∃ α : ℝ → ℝ` with `α 0 = 0`, strictly increasing, and
   `α ‖y‖ ≤ ℓ y u`), the stage-cost convergence implies `α ‖x_n‖ → 0`, and by class-K
   inversion `‖x_n‖ → 0` as `n → ∞`.
   Note: the continuous-time stability notion `IsAsymptoticallyStable` in this library is
   restricted to ℝ-flows; this theorem proves convergence of the iterates to the origin in norm
   (attractivity), not the full ε–δ asymptotic stability statement.

## Main definitions and theorems

* `mpcStep`: convenient one-step closed-loop map `mpcClosedLoop prob x hN h`.
* `mpc_valueFunction_decrease`: value-function descent `V(x⁺) ≤ V(x) − ℓ(x, κ(x))`.
* `mpc_valueFunction_decrease_of_nonneg`: descent under non-negative stage and terminal costs.
* `costSet_bddBelow_of_nonneg`: non-negative costs guarantee `BddBelow (costSet prob y)`.
* `valueFunction_nonneg`: non-negative costs guarantee `0 ≤ valueFunction prob y`.
* `mpc_stageCost_tendsto_zero`: convergence of stage cost along closed-loop trajectories.
* `mpc_converges_to_origin`: norm convergence of closed-loop states to the origin (attractivity).
* `mpc_valueFunction_tendsto_zero`: convergence of the value function to zero when upper bounded
  by a continuous comparison function (Rawlings–Mayne–Diehl Assumption 2.17).
* `suboptimal_cost_bound`: warm-start cost bound `V(f x (u 0)) ≤ V_N(x, u) − ℓ(x, u(0))` for an
  arbitrary admissible (not necessarily optimal) `u` (Rawlings–Mayne–Diehl §2.7, Algorithm 2.43).
* `suboptimal_descent`: the ε-suboptimal perturbed descent obtained by combining
  `suboptimal_cost_bound` with the ε-suboptimality of `u`.
* `mpc_geometric_decay`: the one-step geometric value-function contraction
  `V(x⁺) ≤ (1 − γ) V(x)` under the domination `γ V(y) ≤ ℓ(y, κ_N(y))`.
* `mpc_geometric_iterate`: the n-step geometric contraction
  `V(x_n) ≤ (1 − γ)^n V(x_0)`, the scalar value-function analogue of
  `quadForm_pow_mulVec_le` (Rawlings–Mayne–Diehl §2.4.3, printed p. 120).

## Corrections relative to the task statement

1. **Conditional completeness (`hbd`):**
   In Mathlib, `ℝ` is conditionally complete, so `sInf` on an unbounded-below set evaluates to `0`.
   Applying `valueFunction_le` requires `BddBelow (costSet prob (mpcStep ...))`. The descent
   theorem `mpc_valueFunction_decrease` therefore carries this standard conditional completeness
   hypothesis, matching `valueFunction_le` and `bellman` in `ValueFunction.lean`.
   For convenience, `mpc_valueFunction_decrease_of_nonneg` derives `hbd` automatically from
   `0 ≤ stageCost` and `0 ≤ terminalCost`.
2. **Dissipation target:**
   `tendsto_zero_of_succ_le_sub` proves convergence of the decay rate `w n = ℓ(x_n, κ(x_n)) → 0`,
   not the Lyapunov sequence `v n`. This decay-rate convergence is formalized as
   `mpc_stageCost_tendsto_zero` and directly delivers state convergence `‖x_n‖ → 0` in
   `mpc_converges_to_origin`. Convergence of the value function itself,
   `mpc_valueFunction_tendsto_zero`, requires an upper bound $V_N(x) \le \alpha_2(\|x\|)$
   (weak controllability, Rawlings Assumption 2.17).
3. **Suboptimal descent (§2.7):**
   `suboptimal_cost_bound` carries the same conditional-completeness hypothesis `hbd` as
   `mpc_valueFunction_decrease`, because it also invokes `valueFunction_le`; without it the
   `sInf` convention on unbounded-below cost sets makes the statement false.  In
   `suboptimal_descent` the gap parameter `ε` is an explicit real argument, and the intended
   non-negativity hypothesis `0 ≤ ε` is dropped as unused (the estimate is linear in `hopt`).
4. **Geometric-rate hypotheses (`hγ0`, `hγ1`):**
   The task's listed signature of `mpc_geometric_decay` carries both `0 ≤ γ` and `γ ≤ 1`.  Neither
   is needed for the one-step contraction: `γ V(y) ≤ ℓ(y, κ_N(y))` alone gives
   `V(x⁺) ≤ V(x) − ℓ(x, κ_N(x)) ≤ V(x) − γ V(x) = (1 − γ) V(x)`, and the estimate is linear in
   `γ`.  Both hypotheses are therefore dropped from `mpc_geometric_decay` (recorded here rather
   than silently changed).  The iterate theorem `mpc_geometric_iterate` keeps `γ ≤ 1`, which is
   exactly what supplies `0 ≤ 1 − γ` for its induction step.
-/

open scoped Topology

@[expose] public section

variable {X U : Type*}

/-- The one-step MPC closed-loop transition map from state `x`: evaluates the receding-horizon
control `mpcLaw prob x hN h` and advances the dynamics by one step
(Rawlings–Mayne–Diehl 2019, 2nd ed., Ch. 2 §2.2, printed p. 99). -/
noncomputable def mpcStep (prob : FiniteHorizonProblem X U) (x : X) (hN : 0 < prob.horizon)
    (h : ∃ u : Fin prob.horizon → U, IsOptimalInput prob x u) : X :=
  mpcClosedLoop prob x hN h

/-- The suboptimal (warm-start) cost bound: for an arbitrary *admissible* — not necessarily
optimal — input sequence `u`, the value function at the successor state `f x (u 0)` is bounded
by the current total cost with the first stage cost removed.  This is the one-step estimate
underlying suboptimal MPC (Rawlings–Mayne–Diehl 2019, 2nd ed., Ch. 2 §2.7, Algorithm 2.43,
printed pp. 147–152 / PDF pp. 190–195).

The candidate warm start `Fin.snoc (Fin.tail u) w` drops the applied control `u 0`, shifts the
remaining controls and appends the terminal control `w` produced by `IsTerminalCLF` at the
terminal state `x_N`; it is admissible from `f x (u 0)` by `finiteHorizonAdmissible_snoc`.
`valueFunction_le` bounds the value function by its cost, `totalCost_snoc` + `totalCost_succ_split`
expose the shared running-sum term, and the terminal closed-loop inequality of `hCLF` cancels the
terminal cost, leaving exactly `finiteHorizonTotalCost prob x u - stageCost x (u 0)`.

## Correction

The conditional-completeness hypothesis `hbd` is required.  `valueFunction` is an `sInf` into the
conditionally complete order `ℝ`, and `valueFunction_le` needs `BddBelow (costSet prob ·)`;
without it the `sInf` convention for unbounded-below sets makes the statement false.  This is the
same correction already recorded for `mpc_valueFunction_decrease` and is not a weakening of the
desired content. -/
theorem suboptimal_cost_bound (prob : FiniteHorizonProblem X U) (x : X)
    (u : Fin prob.horizon → U) (hN : 0 < prob.horizon)
    (hadm : FiniteHorizonAdmissible prob x u)
    (hCLF : IsTerminalCLF prob.f prob.stageCost prob.terminalCost prob.terminalSet prob.inputSet)
    (hsub : prob.terminalSet ⊆ prob.stateSet)
    (hbd : BddBelow (costSet prob (prob.f x (u ⟨0, hN⟩)))) :
    valueFunction prob (prob.f x (u ⟨0, hN⟩)) ≤
      finiteHorizonTotalCost prob x u - prob.stageCost x (u ⟨0, hN⟩) := by
  obtain ⟨f, ℓ, Vf, N, Xs, Us, Xf⟩ := prob
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hN)
  have hterm : finiteHorizonRollout ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x u (Fin.last (M + 1)) ∈ Xf :=
    hadm.2
  obtain ⟨w, hwU, hwXf, hwdec⟩ := hCLF _ hterm
  have htermXs : finiteHorizonRollout ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x u (Fin.last (M + 1)) ∈ Xs :=
    hsub hterm
  let u_tilde : Fin (M + 1) → U := Fin.snoc (Fin.tail u) w
  have hadm_tilde : FiniteHorizonAdmissible ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ (f x (u 0)) u_tilde :=
    finiteHorizonAdmissible_snoc x u w hadm htermXs hwU hwXf
  have hle_tilde : valueFunction ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ (f x (u 0)) ≤
      finiteHorizonTotalCost ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ (f x (u 0)) u_tilde :=
    valueFunction_le ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ (f x (u 0)) u_tilde hadm_tilde hbd
  have hcost_snoc := totalCost_snoc f ℓ Vf M Xs Us Xf x u w
  have hcost_split := totalCost_succ_split f ℓ Vf M Xs Us Xf x u
  change valueFunction ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ (f x (u 0)) ≤
    finiteHorizonTotalCost ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x u - ℓ x (u 0)
  linarith [hle_tilde, hcost_snoc, hcost_split, hwdec]

/-- The fundamental value-function descent property of receding-horizon MPC
(Rawlings–Mayne–Diehl 2019, 2nd ed., Ch. 2 §2.4.2, eq. (2.17), printed p. 117):
the optimal cost-to-go at the successor state decreases by at least the stage cost of the applied
control input, `V(x⁺) ≤ V(x) − ℓ(x, κ_N(x))`.

The proof constructs the candidate input `ũ = Fin.snoc (Fin.tail u*) w`, the warm-start pattern of
eq. (2.26), §2.7, printed p. 147, using the stabilizing terminal control `w` from `IsTerminalCLF`,
verifies admissibility with `finiteHorizonAdmissible_snoc`, and telescopes the stage costs using
`totalCost_snoc` and `totalCost_succ_split`. -/
theorem mpc_valueFunction_decrease (prob : FiniteHorizonProblem X U) (x : X)
    (hN : 0 < prob.horizon) (h : ∃ u : Fin prob.horizon → U, IsOptimalInput prob x u)
    (hCLF : IsTerminalCLF prob.f prob.stageCost prob.terminalCost prob.terminalSet prob.inputSet)
    (hsub : prob.terminalSet ⊆ prob.stateSet)
    (hbd : BddBelow (costSet prob (mpcStep prob x hN h))) :
    valueFunction prob (mpcStep prob x hN h) ≤
      valueFunction prob x - prob.stageCost x (mpcLaw prob x hN h) := by
  let u := Classical.choose h
  have hu : IsOptimalInput prob x u := Classical.choose_spec h
  have hbound := suboptimal_cost_bound prob x u hN hu.1 hCLF hsub (by
    show BddBelow (costSet prob (prob.f x (u ⟨0, hN⟩)))
    rw [show prob.f x (u ⟨0, hN⟩) = mpcStep prob x hN h from rfl]
    exact hbd)
  have hVeq : valueFunction prob x = finiteHorizonTotalCost prob x u :=
    valueFunction_eq prob x u hu
  rw [hVeq]
  exact hbound

/-- The ε-suboptimal perturbed descent of Rawlings–Mayne–Diehl 2019, 2nd ed., Ch. 2 §2.7
(printed pp. 147–152 / PDF pp. 190–195).  If the admissible input `u` is ε-suboptimal, i.e.
`finiteHorizonTotalCost prob x u ≤ valueFunction prob x + ε`, then the value function at the
successor obeys the perturbed descent
`valueFunction prob (f x (u 0)) ≤ valueFunction prob x + ε - stageCost x (u 0)`.

The gap `ε` perturbs the exact decrease `V(x⁺) ≤ V(x) - ℓ(x, κ_N(x))` of
`mpc_valueFunction_decrease`; at `ε = 0`, with `u` optimal, `valueFunction_eq` identifies the
total cost with the value function and the two statements coincide.

## Correction

The non-negativity hypothesis `0 ≤ ε` that the book's perturbed descent suggests is omitted:
the estimate is a purely linear consequence of `hopt` and `suboptimal_cost_bound`, so it holds
for every real gap and the extra hypothesis would only be flagged by `unusedArguments`. -/
theorem suboptimal_descent (prob : FiniteHorizonProblem X U) (x : X)
    (u : Fin prob.horizon → U) (hN : 0 < prob.horizon)
    (hadm : FiniteHorizonAdmissible prob x u)
    (hCLF : IsTerminalCLF prob.f prob.stageCost prob.terminalCost prob.terminalSet prob.inputSet)
    (hsub : prob.terminalSet ⊆ prob.stateSet)
    (hbd : BddBelow (costSet prob (prob.f x (u ⟨0, hN⟩))))
    (ε : ℝ) (hopt : finiteHorizonTotalCost prob x u ≤ valueFunction prob x + ε) :
    valueFunction prob (prob.f x (u ⟨0, hN⟩)) ≤
      valueFunction prob x + ε - prob.stageCost x (u ⟨0, hN⟩) := by
  have h := suboptimal_cost_bound prob x u hN hadm hCLF hsub hbd
  linarith

/-- Non-negative stage costs and terminal cost guarantee that the admissible cost set is
bounded below by `0` everywhere. -/
theorem costSet_bddBelow_of_nonneg (prob : FiniteHorizonProblem X U) (y : X)
    (hℓ : ∀ x u, 0 ≤ prob.stageCost x u)
    (hVf : ∀ x ∈ prob.terminalSet, 0 ≤ prob.terminalCost x) :
    BddBelow (costSet prob y) := by
  refine ⟨0, ?_⟩
  rintro r ⟨v, hv, rfl⟩
  unfold finiteHorizonTotalCost
  have hsum : 0 ≤ ∑ k : Fin prob.horizon,
      prob.stageCost (finiteHorizonRollout prob y v k.castSucc) (v k) :=
    Finset.sum_nonneg fun k _ ↦ hℓ _ _
  have hterm : 0 ≤ prob.terminalCost (finiteHorizonRollout prob y v (Fin.last prob.horizon)) :=
    hVf _ hv.2
  linarith

/-- The dynamic-programming value function is non-negative everywhere when the stage costs and
terminal cost are non-negative. -/
theorem valueFunction_nonneg (prob : FiniteHorizonProblem X U) (y : X)
    (hℓ : ∀ x u, 0 ≤ prob.stageCost x u)
    (hVf : ∀ x ∈ prob.terminalSet, 0 ≤ prob.terminalCost x) :
    0 ≤ valueFunction prob y := by
  by_cases hne : (costSet prob y).Nonempty
  · refine le_csInf hne ?_
    rintro r ⟨v, hv, rfl⟩
    unfold finiteHorizonTotalCost
    have hsum : 0 ≤ ∑ k : Fin prob.horizon,
        prob.stageCost (finiteHorizonRollout prob y v k.castSucc) (v k) :=
      Finset.sum_nonneg fun k _ ↦ hℓ _ _
    have hterm : 0 ≤ prob.terminalCost (finiteHorizonRollout prob y v (Fin.last prob.horizon)) :=
      hVf _ hv.2
    linarith
  · unfold valueFunction
    have hcs : costSet prob y = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hcs, Real.sInf_empty]

/-- The value-function descent specialized to problems with non-negative stage and terminal
costs, discharging the lower-boundedness condition automatically. -/
theorem mpc_valueFunction_decrease_of_nonneg (prob : FiniteHorizonProblem X U) (x : X)
    (hN : 0 < prob.horizon) (h : ∃ u : Fin prob.horizon → U, IsOptimalInput prob x u)
    (hCLF : IsTerminalCLF prob.f prob.stageCost prob.terminalCost prob.terminalSet prob.inputSet)
    (hsub : prob.terminalSet ⊆ prob.stateSet)
    (hℓ : ∀ x u, 0 ≤ prob.stageCost x u)
    (hVf : ∀ x ∈ prob.terminalSet, 0 ≤ prob.terminalCost x) :
    valueFunction prob (mpcStep prob x hN h) ≤
      valueFunction prob x - prob.stageCost x (mpcLaw prob x hN h) :=
  mpc_valueFunction_decrease prob x hN h hCLF hsub (costSet_bddBelow_of_nonneg prob _ hℓ hVf)

/-- One-step value-function descent along an optimal closed-loop trajectory:
`V(x_{n+1}) ≤ V(x_n) − ℓ(x_n, u_n(0))`.

This is the region-of-attraction formulation (stability on the feasible set `X_N`),
matching Rawlings' `X_N`-feasible-region statement. -/
theorem mpc_trajectory_valueFunction_decrease (prob : FiniteHorizonProblem X U)
    (hN : 0 < prob.horizon) (x : ℕ → X) (u : ℕ → Fin prob.horizon → U)
    (hopt : ∀ n, IsOptimalInput prob (x n) (u n))
    (hstep : ∀ n, x (n + 1) = prob.f (x n) ((u n) ⟨0, hN⟩))
    (hCLF : IsTerminalCLF prob.f prob.stageCost prob.terminalCost prob.terminalSet prob.inputSet)
    (hsub : prob.terminalSet ⊆ prob.stateSet) (n : ℕ) :
    valueFunction prob (x (n + 1)) ≤
      valueFunction prob (x n) - prob.stageCost (x n) ((u n) ⟨0, hN⟩) := by
  have hbd : BddBelow (costSet prob (x (n + 1))) :=
    ⟨finiteHorizonTotalCost prob (x (n + 1)) (u (n + 1)), fun r hr ↦ by
      obtain ⟨v, hv, rfl⟩ := hr
      exact (hopt (n + 1)).2 v hv⟩
  rw [hstep n]
  have hbound := suboptimal_cost_bound prob (x n) (u n) hN (hopt n).1 hCLF hsub (by
    rw [← hstep n]
    exact hbd)
  have hVeq : valueFunction prob (x n) = finiteHorizonTotalCost prob (x n) (u n) :=
    valueFunction_eq prob (x n) (u n) (hopt n)
  rw [hVeq]
  exact hbound

/-- The stage cost along the closed-loop MPC trajectory converges to zero
(Rawlings–Mayne–Diehl 2019, 2nd ed., Ch. 2 §2.4.2, printed p. 116).

This is the region-of-attraction formulation (stability on the feasible set `X_N`),
matching Rawlings' `X_N`-feasible-region statement. This is the direct discrete dissipation
consequence of the telescoping decrease `V(x_{n+1}) ≤ V(x_n) − ℓ(x_n, u_n(0))`
via `tendsto_zero_of_succ_le_sub`. -/
theorem mpc_stageCost_tendsto_zero (prob : FiniteHorizonProblem X U) (hN : 0 < prob.horizon)
    (x : ℕ → X) (u : ℕ → Fin prob.horizon → U)
    (hopt : ∀ n, IsOptimalInput prob (x n) (u n))
    (hstep : ∀ n, x (n + 1) = prob.f (x n) ((u n) ⟨0, hN⟩))
    (hCLF : IsTerminalCLF prob.f prob.stageCost prob.terminalCost prob.terminalSet prob.inputSet)
    (hsub : prob.terminalSet ⊆ prob.stateSet)
    (hℓ : ∀ x u, 0 ≤ prob.stageCost x u)
    (hVf : ∀ x ∈ prob.terminalSet, 0 ≤ prob.terminalCost x) :
    Filter.Tendsto (fun n ↦ prob.stageCost (x n) ((u n) ⟨0, hN⟩)) Filter.atTop (𝓝 0) := by
  let v : ℕ → ℝ := fun n ↦ valueFunction prob (x n)
  let w : ℕ → ℝ := fun n ↦ prob.stageCost (x n) ((u n) ⟨0, hN⟩)
  have hv : ∀ t, 0 ≤ v t := fun t ↦ valueFunction_nonneg prob (x t) hℓ hVf
  have hw : ∀ t, 0 ≤ w t := fun t ↦ hℓ _ _
  have hdec : ∀ t, v (t + 1) ≤ v t - w t := fun t ↦
    mpc_trajectory_valueFunction_decrease prob hN x u hopt hstep hCLF hsub t
  exact tendsto_zero_of_succ_le_sub hv hw hdec

/-- **One-step geometric value-function contraction** (Rawlings–Mayne–Diehl 2019, 2nd ed.,
Ch. 2 §2.4.3, exponential stability, printed p. 120 / PDF p. 163).  If the stage cost dominates
`γ` times the value function along the receding-horizon law, `γ V(x) ≤ ℓ(x, κ_N(x))`, then the
closed-loop value function contracts by the factor `1 − γ`, `V(x⁺) ≤ (1 − γ) V(x)`.

The proof is the descent `V(x⁺) ≤ V(x) − ℓ(x, κ_N(x))` of `mpc_valueFunction_decrease` combined
with `ℓ(x, κ_N(x)) ≥ γ V(x)`.

## Correction (recorded for the campaign)

The book states the rate for `γ ∈ [0, 1]`.  Neither `0 ≤ γ` nor `γ ≤ 1` is used by this one-step
estimate: the implication is linear in `γ` and holds for every real `γ`.  Both hypotheses are
therefore omitted here (keeping hypotheses tight); the iterate theorem `mpc_geometric_iterate`
retains `γ ≤ 1`, which is genuinely needed for `0 ≤ 1 − γ`.

This is the scalar value-function analogue of `quadForm_pow_mulVec_le`
(`DynamicalSystems.DiscreteTime.MatrixLyapunov`); the quadratic (LQR) instantiation over
`quadForm`/`exists_factor` is a separate bridge and is not re-derived here. -/
theorem mpc_geometric_decay (prob : FiniteHorizonProblem X U) (x : X) (hN : 0 < prob.horizon)
    (hopt : ∃ u, IsOptimalInput prob x u)
    (hCLF : IsTerminalCLF prob.f prob.stageCost prob.terminalCost prob.terminalSet prob.inputSet)
    (hsub : prob.terminalSet ⊆ prob.stateSet)
    (hbd : BddBelow (costSet prob (mpcStep prob x hN hopt)))
    {γ : ℝ}
    (hdom : γ * valueFunction prob x ≤ prob.stageCost x (mpcLaw prob x hN hopt)) :
    valueFunction prob (mpcStep prob x hN hopt) ≤ (1 - γ) * valueFunction prob x := by
  have hdec := mpc_valueFunction_decrease prob x hN hopt hCLF hsub hbd
  linarith [hdom]

/-- One-step geometric value-function contraction under non-negative stage and terminal costs,
discharging the lower-boundedness condition automatically. -/
theorem mpc_geometric_decay_of_nonneg (prob : FiniteHorizonProblem X U) (x : X)
    (hN : 0 < prob.horizon) (hopt : ∃ u, IsOptimalInput prob x u)
    (hCLF : IsTerminalCLF prob.f prob.stageCost prob.terminalCost prob.terminalSet prob.inputSet)
    (hsub : prob.terminalSet ⊆ prob.stateSet)
    (hℓ : ∀ x u, 0 ≤ prob.stageCost x u)
    (hVf : ∀ x ∈ prob.terminalSet, 0 ≤ prob.terminalCost x)
    {γ : ℝ}
    (hdom : γ * valueFunction prob x ≤ prob.stageCost x (mpcLaw prob x hN hopt)) :
    valueFunction prob (mpcStep prob x hN hopt) ≤ (1 - γ) * valueFunction prob x :=
  mpc_geometric_decay prob x hN hopt hCLF hsub (costSet_bddBelow_of_nonneg prob _ hℓ hVf) hdom

/-- **n-step geometric value-function contraction** (Rawlings–Mayne–Diehl 2019, 2nd ed.,
Ch. 2 §2.4.3, exponential stability, printed p. 120 / PDF p. 163): along an optimal closed-loop
trajectory `x_{n+1} = f(x_n, u_n(0))`, the value function contracts geometrically:
`V(x_n) ≤ (1 − γ)^n V(x_0)`.

This is the region-of-attraction formulation (stability on the feasible set `X_N`),
matching Rawlings' `X_N`-feasible-region statement. This is the scalar (value-function) analogue of
`quadForm_pow_mulVec_le` in `DynamicalSystems.DiscreteTime.MatrixLyapunov`; the quadratic
instantiation `V = quadForm P` via the LQR terminal cost should bridge to
`quadForm_pow_mulVec_le`/`exists_factor` directly rather than re-derive the contraction.

The only rate hypothesis needed is `γ ≤ 1`, which yields `0 ≤ 1 − γ` for the induction step. -/
theorem mpc_geometric_iterate (prob : FiniteHorizonProblem X U) (hN : 0 < prob.horizon)
    (x : ℕ → X) (u : ℕ → Fin prob.horizon → U)
    (hopt : ∀ n, IsOptimalInput prob (x n) (u n))
    (hstep : ∀ n, x (n + 1) = prob.f (x n) ((u n) ⟨0, hN⟩))
    (hCLF : IsTerminalCLF prob.f prob.stageCost prob.terminalCost prob.terminalSet prob.inputSet)
    (hsub : prob.terminalSet ⊆ prob.stateSet)
    {γ : ℝ} (hγ1 : γ ≤ 1)
    (hdom : ∀ n, γ * valueFunction prob (x n) ≤ prob.stageCost (x n) ((u n) ⟨0, hN⟩))
    (n : ℕ) :
    valueFunction prob (x n) ≤ (1 - γ) ^ n * valueFunction prob (x 0) := by
  have hc : 0 ≤ 1 - γ := by linarith
  induction n with
  | zero => simp
  | succ n ih =>
      have hdec := mpc_trajectory_valueFunction_decrease prob hN x u hopt hstep hCLF hsub n
      have hstep_decay : valueFunction prob (x (n + 1)) ≤ (1 - γ) * valueFunction prob (x n) := by
        linarith [hdec, hdom n]
      calc
        valueFunction prob (x (n + 1))
            ≤ (1 - γ) * valueFunction prob (x n) := hstep_decay
        _ ≤ (1 - γ) * ((1 - γ) ^ n * valueFunction prob (x 0)) :=
              mul_le_mul_of_nonneg_left ih hc
        _ = (1 - γ) ^ n.succ * valueFunction prob (x 0) := by rw [pow_succ']; ring

variable [NormedAddCommGroup X] [NormedAddCommGroup U]

/-- Inverting convergence under a strictly increasing comparison function with `α 0 = 0`:
if a non-negative sequence `s n` satisfies `α (s n) ≤ w n` and `w n → 0`, then `s n → 0`. -/
private theorem tendsto_zero_of_classK {s w : ℕ → ℝ} (hs : ∀ n, 0 ≤ s n)
    (α : ℝ → ℝ) (hα0 : α 0 = 0) (hmono : StrictMono α)
    (hle : ∀ n, α (s n) ≤ w n)
    (hw : Filter.Tendsto w Filter.atTop (𝓝 0)) :
    Filter.Tendsto s Filter.atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at hw ⊢
  intro ε hε
  have hαpos : 0 < α ε := by
    rw [← hα0]
    exact hmono hε
  obtain ⟨k, hk⟩ := hw (α ε) hαpos
  refine ⟨k, fun n hn ↦ ?_⟩
  have hwn : dist (w n) 0 < α ε := hk n hn
  rw [Real.dist_0_eq_abs] at hwn
  have hw_lt : w n < α ε := (le_abs_self (w n)).trans_lt hwn
  have hαs : α (s n) < α ε := (hle n).trans_lt hw_lt
  have hsn : s n < ε := hmono.lt_iff_lt.mp hαs
  rw [Real.dist_0_eq_abs, abs_of_nonneg (hs n)]
  exact hsn

omit [NormedAddCommGroup U] in
/-- Convergence to the origin (attractivity) of the MPC closed-loop trajectory
(Rawlings–Mayne–Diehl 2019, 2nd ed., Ch. 2 §2.4.2, Theorem 2.19, printed pp. 119–120):
under coercive stage cost `α ‖y‖ ≤ ℓ y u` with `α 0 = 0` and `StrictMono α`, the closed-loop state
trajectory converges in norm to the origin, `Tendsto (fun n ↦ ‖x n‖) atTop (𝓝 0)`.

This is the region-of-attraction formulation (stability on the feasible set `X_N`),
matching Rawlings' `X_N`-feasible-region statement. This proves convergence of the trajectory
to the origin in norm (attractivity), not full asymptotic stability; full
asymptotic stability (equilibrium plus Lyapunov ε–δ stability via `isStableOn_discreteFlow`) is a
separate step not stated here. -/
theorem mpc_converges_to_origin (prob : FiniteHorizonProblem X U) (hN : 0 < prob.horizon)
    (x : ℕ → X) (u : ℕ → Fin prob.horizon → U)
    (hopt : ∀ n, IsOptimalInput prob (x n) (u n))
    (hstep : ∀ n, x (n + 1) = prob.f (x n) ((u n) ⟨0, hN⟩))
    (hCLF : IsTerminalCLF prob.f prob.stageCost prob.terminalCost prob.terminalSet prob.inputSet)
    (hsub : prob.terminalSet ⊆ prob.stateSet)
    (hℓ : ∀ x u, 0 ≤ prob.stageCost x u)
    (hVf : ∀ x ∈ prob.terminalSet, 0 ≤ prob.terminalCost x)
    (hcoercive : ∃ α : ℝ → ℝ, α 0 = 0 ∧ StrictMono α ∧
      ∀ y u, α ‖y‖ ≤ prob.stageCost y u) :
    Filter.Tendsto (fun n ↦ ‖x n‖) Filter.atTop (𝓝 0) := by
  obtain ⟨α, hα0, hmono, hle⟩ := hcoercive
  have hw := mpc_stageCost_tendsto_zero prob hN x u hopt hstep hCLF hsub hℓ hVf
  refine tendsto_zero_of_classK (fun n ↦ norm_nonneg _) α hα0 hmono ?_ hw
  intro n
  exact hle _ _

omit [NormedAddCommGroup U] in
/-- Convergence of the value function along closed-loop trajectories to zero
(Rawlings–Mayne–Diehl 2019, 2nd ed., Ch. 2 §2.4.2, Theorem 2.19(a), printed pp. 119–120),
given weak controllability (Assumption 2.17: upper bound `V_N(y) ≤ α₂ ‖y‖` with `α₂`
continuous at `0` and `α₂ 0 = 0`).

This is the region-of-attraction formulation (stability on the feasible set `X_N`),
matching Rawlings' `X_N`-feasible-region statement. -/
theorem mpc_valueFunction_tendsto_zero (prob : FiniteHorizonProblem X U) (hN : 0 < prob.horizon)
    (x : ℕ → X) (u : ℕ → Fin prob.horizon → U)
    (hopt : ∀ n, IsOptimalInput prob (x n) (u n))
    (hstep : ∀ n, x (n + 1) = prob.f (x n) ((u n) ⟨0, hN⟩))
    (hCLF : IsTerminalCLF prob.f prob.stageCost prob.terminalCost prob.terminalSet prob.inputSet)
    (hsub : prob.terminalSet ⊆ prob.stateSet)
    (hℓ : ∀ x u, 0 ≤ prob.stageCost x u)
    (hVf : ∀ x ∈ prob.terminalSet, 0 ≤ prob.terminalCost x)
    (hcoercive : ∃ α : ℝ → ℝ, α 0 = 0 ∧ StrictMono α ∧
      ∀ y u, α ‖y‖ ≤ prob.stageCost y u)
    (hVupper : ∃ α₂ : ℝ → ℝ, α₂ 0 = 0 ∧ ContinuousAt α₂ 0 ∧ ∀ y, valueFunction prob y ≤ α₂ ‖y‖) :
    Filter.Tendsto (fun n ↦ valueFunction prob (x n)) Filter.atTop (𝓝 0) := by
  obtain ⟨α₂, hα₂0, hcont, hVle⟩ := hVupper
  have hx := mpc_converges_to_origin prob hN x u hopt hstep hCLF hsub hℓ hVf hcoercive
  have hα₂ : Filter.Tendsto (fun n ↦ α₂ ‖x n‖) Filter.atTop (𝓝 0) := by
    have hlim := hcont.tendsto.comp hx
    rw [hα₂0] at hlim
    exact hlim
  rw [Metric.tendsto_atTop] at hα₂ ⊢
  intro ε hε
  obtain ⟨k, hk⟩ := hα₂ ε hε
  refine ⟨k, fun n hn ↦ ?_⟩
  have hnα := hk n hn
  rw [Real.dist_0_eq_abs] at hnα ⊢
  have hVnn : 0 ≤ valueFunction prob (x n) := valueFunction_nonneg prob _ hℓ hVf
  have hVup := hVle (x n)
  rw [abs_of_nonneg hVnn]
  have hlt : α₂ ‖x n‖ < ε := (le_abs_self _).trans_lt hnα
  exact hVup.trans_lt hlt
