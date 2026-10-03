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

1. **Value-function descent (Lemma 2.18 / eq. (2.26), printed p. 117):**
   If `Vf` is a discrete terminal control-Lyapunov function on `Xf` (`IsTerminalCLF`) and
   `Xf ⊆ Xs`, then the value function satisfies
   `V(x⁺) ≤ V(x) − ℓ(x, κ_N(x))`.
   The candidate warm-start input for `x⁺` is `ũ = Fin.snoc (Fin.tail u*) w` where `w ∈ Us` is
   the stabilizing terminal control selected by `IsTerminalCLF` at the terminal state
   `x_N = rollout x u* (Fin.last N) ∈ Xf`.

2. **Decay rate convergence (discrete dissipation bridge):**
   Instantiating the scalar dissipation bridge `tendsto_zero_of_succ_le_sub` with
   `v n = V(x_n)` and `w n = ℓ(x_n, κ_N(x_n))` turns the telescoping decrease
   `v (n + 1) ≤ v n − w n` into summability and convergence of the stage cost:
   `ℓ(x_n, κ_N(x_n)) → 0`.

3. **Asymptotic stability (Theorem 2.19, printed p. 116 / 120):**
   If the stage cost is coercive (`∃ α : ℝ → ℝ` with `α 0 = 0`, strictly increasing, and
   `α ‖y‖ ≤ ℓ y u`), the stage-cost convergence implies `α ‖x_n‖ → 0`, and by class-K
   inversion `‖x_n‖ → 0` as `n → ∞`.
   Note: the continuous-time stability notion `IsAsymptoticallyStable` in this library is
   restricted to ℝ-flows; asymptotic stability in discrete time is formulated honestly as
   the convergence of iterates to the origin in norm: `Tendsto (fun n ↦ ‖x_n‖) atTop (𝓝 0)`.

## Main definitions and theorems

* `mpcStep`: convenient one-step closed-loop map `mpcClosedLoop prob x hN h`.
* `totalCost_snoc`, `totalCost_succ_split`: Finset cost splitting and shift identities.
* `mpc_valueFunction_decrease`: value-function descent `V(x⁺) ≤ V(x) − ℓ(x, κ(x))`.
* `mpc_valueFunction_decrease_of_nonneg`: descent under non-negative stage and terminal costs.
* `costSet_bddBelow_of_nonneg`: non-negative costs guarantee `BddBelow (costSet prob y)`.
* `valueFunction_nonneg`: non-negative costs guarantee `0 ≤ valueFunction prob y`.
* `mpc_stageCost_tendsto_zero`: convergence of stage cost along closed-loop trajectories.
* `mpc_asymptoticallyStable`: norm convergence of closed-loop states to the origin.
* `mpc_valueFunction_tendsto_zero`: convergence of the value function to zero when upper bounded
  by a continuous comparison function (Rawlings–Mayne–Diehl Assumption 2.17).

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
   `mpc_asymptoticallyStable`. Convergence of the value function itself,
   `mpc_valueFunction_tendsto_zero`, requires an upper bound $V_N(x) \le \alpha_2(\|x\|)$
   (weak controllability, Rawlings Assumption 2.17).
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

/-- Expanding the total cost of an extended input sequence `Fin.snoc (Fin.tail u) w`: the running
sum shifts by one index along the original rollout, the last stage cost evaluates at the terminal
state `x_N` with input `w`, and the terminal cost evaluates at `f x_N w`. -/
theorem totalCost_snoc (f : X → U → X) (ℓ : X → U → ℝ) (Vf : X → ℝ)
    (M : ℕ) (Xs : Set X) (Us : Set U) (Xf : Set X)
    (x : X) (u : Fin (M + 1) → U) (w : U) :
    finiteHorizonTotalCost ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ (f x (u 0)) (Fin.snoc (Fin.tail u) w) =
      (∑ j : Fin M, ℓ (finiteHorizonRollout ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x u j.succ.castSucc)
        (u j.succ)) +
        ℓ (finiteHorizonRollout ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x u (Fin.last (M + 1))) w +
        Vf (f (finiteHorizonRollout ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x u (Fin.last (M + 1))) w) := by
  unfold finiteHorizonTotalCost
  rw [Fin.sum_univ_castSucc]
  rw [finiteHorizonRollout_snoc_last]
  congr 1
  congr 1
  · refine Finset.sum_congr rfl ?_
    intro j _
    rw [finiteHorizonRollout_snoc, Fin.snoc_castSucc, Fin.tail]
    rw [Fin.castSucc_succ]
  · rw [finiteHorizonRollout_snoc, Fin.snoc_last, Fin.succ_last]

/-- Splitting off the first stage cost from the finite-horizon total cost of sequence `u`. -/
theorem totalCost_succ_split (f : X → U → X) (ℓ : X → U → ℝ) (Vf : X → ℝ)
    (M : ℕ) (Xs : Set X) (Us : Set U) (Xf : Set X)
    (x : X) (u : Fin (M + 1) → U) :
    finiteHorizonTotalCost ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x u =
      ℓ x (u 0) +
        (∑ j : Fin M, ℓ (finiteHorizonRollout ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x u j.succ.castSucc)
          (u j.succ)) +
        Vf (finiteHorizonRollout ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x u (Fin.last (M + 1))) := by
  unfold finiteHorizonTotalCost
  rw [Fin.sum_univ_succ]
  rw [Fin.castSucc_zero, finiteHorizonRollout_zero]

/-- The fundamental value-function descent property of receding-horizon MPC
(Rawlings–Mayne–Diehl 2019, 2nd ed., Ch. 2 §2.4.2, Lemma 2.18 / eq. (2.26), printed p. 117):
the optimal cost-to-go at the successor state decreases by at least the stage cost of the applied
control input, `V(x⁺) ≤ V(x) − ℓ(x, κ_N(x))`.

The proof constructs the candidate input `ũ = Fin.snoc (Fin.tail u*) w` using the stabilizing
terminal control `w` from `IsTerminalCLF`, verifies admissibility with
`finiteHorizonAdmissible_snoc`, and telescopes the stage costs using `totalCost_snoc` and
`totalCost_succ_split`. -/
theorem mpc_valueFunction_decrease (prob : FiniteHorizonProblem X U) (x : X)
    (hN : 0 < prob.horizon) (h : ∃ u : Fin prob.horizon → U, IsOptimalInput prob x u)
    (hCLF : IsTerminalCLF prob.f prob.stageCost prob.terminalCost prob.terminalSet prob.inputSet)
    (hsub : prob.terminalSet ⊆ prob.stateSet)
    (hbd : BddBelow (costSet prob (mpcStep prob x hN h))) :
    valueFunction prob (mpcStep prob x hN h) ≤
      valueFunction prob x - prob.stageCost x (mpcLaw prob x hN h) := by
  obtain ⟨f, ℓ, Vf, N, Xs, Us, Xf⟩ := prob
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hN)
  let u := Classical.choose h
  have hu : IsOptimalInput ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x u := Classical.choose_spec h
  have hadm : FiniteHorizonAdmissible ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x u := hu.1
  have hterm : finiteHorizonRollout ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x u (Fin.last (M + 1)) ∈ Xf :=
    hadm.2
  obtain ⟨w, hwU, hwXf, hwdec⟩ := hCLF _ hterm
  have htermXs : finiteHorizonRollout ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x u (Fin.last (M + 1)) ∈ Xs :=
    hsub hterm
  let u_tilde : Fin (M + 1) → U := Fin.snoc (Fin.tail u) w
  have hadm_tilde : FiniteHorizonAdmissible ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ (f x (u 0)) u_tilde :=
    finiteHorizonAdmissible_snoc x u w hadm htermXs hwU hwXf
  have hmcl : mpcClosedLoop ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x hN h = f x (u 0) := by
    simp only [mpcClosedLoop, mpcLaw]; rfl
  have hmstep : mpcStep ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x hN h = f x (u 0) := hmcl
  have hlaw : mpcLaw ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x hN h = u 0 := rfl
  have hVeq : valueFunction ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x =
      finiteHorizonTotalCost ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x u :=
    valueFunction_eq ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x u hu
  have hle_tilde : valueFunction ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ (f x (u 0)) ≤
      finiteHorizonTotalCost ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ (f x (u 0)) u_tilde := by
    have hbd' : BddBelow (costSet ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ (f x (u 0))) := by
      rw [← hmstep]
      exact hbd
    exact valueFunction_le ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ (f x (u 0)) u_tilde hadm_tilde hbd'
  have hcost_snoc := totalCost_snoc f ℓ Vf M Xs Us Xf x u w
  have hcost_split := totalCost_succ_split f ℓ Vf M Xs Us Xf x u
  rw [hmstep, hlaw, hVeq]
  linarith [hle_tilde, hcost_snoc, hcost_split, hwdec]

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

/-- The stage cost along the closed-loop MPC trajectory converges to zero
(Rawlings–Mayne–Diehl 2019, 2nd ed., Ch. 2 §2.4.2, printed p. 116).

This is the direct discrete dissipation consequence of the telescoping decrease
`V(x⁺) ≤ V(x) − ℓ(x, κ_N(x))` via `tendsto_zero_of_succ_le_sub`. -/
theorem mpc_stageCost_tendsto_zero (prob : FiniteHorizonProblem X U) (x : X)
    (hN : 0 < prob.horizon) (hopt : ∀ y, ∃ u, IsOptimalInput prob y u)
    (hCLF : IsTerminalCLF prob.f prob.stageCost prob.terminalCost prob.terminalSet prob.inputSet)
    (hsub : prob.terminalSet ⊆ prob.stateSet)
    (hℓ : ∀ x u, 0 ≤ prob.stageCost x u)
    (hVf : ∀ x ∈ prob.terminalSet, 0 ≤ prob.terminalCost x) :
    Filter.Tendsto (fun n ↦ prob.stageCost ((fun y ↦ mpcStep prob y hN (hopt y))^[n] x)
      (mpcLaw prob ((fun y ↦ mpcStep prob y hN (hopt y))^[n] x) hN (hopt _)))
      Filter.atTop (𝓝 0) := by
  let step : X → X := fun y ↦ mpcStep prob y hN (hopt y)
  let v : ℕ → ℝ := fun n ↦ valueFunction prob (step^[n] x)
  let w : ℕ → ℝ := fun n ↦
    prob.stageCost (step^[n] x) (mpcLaw prob (step^[n] x) hN (hopt (step^[n] x)))
  have hv : ∀ t, 0 ≤ v t := fun t ↦ valueFunction_nonneg prob (step^[t] x) hℓ hVf
  have hw : ∀ t, 0 ≤ w t := fun t ↦ hℓ _ _
  have hdec : ∀ t, v (t + 1) ≤ v t - w t := by
    intro t
    dsimp only [v, w]
    rw [Function.iterate_succ_apply']
    dsimp only [step]
    have hbd : BddBelow (costSet prob (mpcStep prob (step^[t] x) hN (hopt (step^[t] x)))) :=
      costSet_bddBelow_of_nonneg prob _ hℓ hVf
    exact mpc_valueFunction_decrease prob (step^[t] x) hN (hopt (step^[t] x)) hCLF hsub hbd
  exact tendsto_zero_of_succ_le_sub hv hw hdec

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
/-- Asymptotic stability of the MPC closed-loop system
(Rawlings–Mayne–Diehl 2019, 2nd ed., Ch. 2 §2.4.2, Theorem 2.19, printed p. 116 / 120):
under coercive stage cost `α ‖y‖ ≤ ℓ y u` with class-K function `α`, the closed-loop state
converges in norm to the origin, `Tendsto (fun n ↦ ‖x_n‖) atTop (𝓝 0)`.

Discrete-time asymptotic stability in this library is formulated as state convergence to the
origin, avoiding continuous-flow restrictions (`IsAsymptoticallyStable` is ℝ-flow only). -/
theorem mpc_asymptoticallyStable (prob : FiniteHorizonProblem X U) (x : X)
    (hN : 0 < prob.horizon) (hopt : ∀ y, ∃ u, IsOptimalInput prob y u)
    (hCLF : IsTerminalCLF prob.f prob.stageCost prob.terminalCost prob.terminalSet prob.inputSet)
    (hsub : prob.terminalSet ⊆ prob.stateSet)
    (hℓ : ∀ x u, 0 ≤ prob.stageCost x u)
    (hVf : ∀ x ∈ prob.terminalSet, 0 ≤ prob.terminalCost x)
    (hcoercive : ∃ α : ℝ → ℝ, α 0 = 0 ∧ StrictMono α ∧ Filter.Tendsto α Filter.atTop Filter.atTop ∧
      ∀ y u, α ‖y‖ ≤ prob.stageCost y u) :
    Filter.Tendsto (fun n ↦ ‖(fun y ↦ mpcStep prob y hN (hopt y))^[n] x‖) Filter.atTop (𝓝 0) := by
  obtain ⟨α, hα0, hmono, -, hle⟩ := hcoercive
  have hw := mpc_stageCost_tendsto_zero prob x hN hopt hCLF hsub hℓ hVf
  refine tendsto_zero_of_classK (fun n ↦ norm_nonneg _) α hα0 hmono ?_ hw
  intro n
  exact hle _ _

omit [NormedAddCommGroup U] in
/-- Convergence of the value function along closed-loop trajectories to zero
(Rawlings–Mayne–Diehl 2019, 2nd ed., Ch. 2 §2.4.2, Theorem 2.19(a), printed p. 116 / 120),
given weak controllability (Assumption 2.17: upper bound `V_N(y) ≤ α₂ ‖y‖` with `α₂`
continuous at `0` and `α₂ 0 = 0`). -/
theorem mpc_valueFunction_tendsto_zero (prob : FiniteHorizonProblem X U) (x : X)
    (hN : 0 < prob.horizon) (hopt : ∀ y, ∃ u, IsOptimalInput prob y u)
    (hCLF : IsTerminalCLF prob.f prob.stageCost prob.terminalCost prob.terminalSet prob.inputSet)
    (hsub : prob.terminalSet ⊆ prob.stateSet)
    (hℓ : ∀ x u, 0 ≤ prob.stageCost x u)
    (hVf : ∀ x ∈ prob.terminalSet, 0 ≤ prob.terminalCost x)
    (hcoercive : ∃ α : ℝ → ℝ, α 0 = 0 ∧ StrictMono α ∧ Filter.Tendsto α Filter.atTop Filter.atTop ∧
      ∀ y u, α ‖y‖ ≤ prob.stageCost y u)
    (hVupper : ∃ α₂ : ℝ → ℝ, α₂ 0 = 0 ∧ ContinuousAt α₂ 0 ∧ ∀ y, valueFunction prob y ≤ α₂ ‖y‖) :
    Filter.Tendsto (fun n ↦ valueFunction prob ((fun y ↦ mpcStep prob y hN (hopt y))^[n] x))
      Filter.atTop (𝓝 0) := by
  obtain ⟨α₂, hα₂0, hcont, hVle⟩ := hVupper
  have hx := mpc_asymptoticallyStable prob x hN hopt hCLF hsub hℓ hVf hcoercive
  have hα₂ : Filter.Tendsto (fun n ↦ α₂ ‖(fun y ↦ mpcStep prob y hN (hopt y))^[n] x‖)
      Filter.atTop (𝓝 0) := by
    have hlim := hcont.tendsto.comp hx
    rw [hα₂0] at hlim
    exact hlim
  rw [Metric.tendsto_atTop] at hα₂ ⊢
  intro ε hε
  obtain ⟨k, hk⟩ := hα₂ ε hε
  refine ⟨k, fun n hn ↦ ?_⟩
  have hnα := hk n hn
  rw [Real.dist_0_eq_abs] at hnα ⊢
  have hVnn : 0 ≤ valueFunction prob ((fun y ↦ mpcStep prob y hN (hopt y))^[n] x) :=
    valueFunction_nonneg prob _ hℓ hVf
  have hVup := hVle ((fun y ↦ mpcStep prob y hN (hopt y))^[n] x)
  rw [abs_of_nonneg hVnn]
  have hlt : α₂ ‖(fun y ↦ mpcStep prob y hN (hopt y))^[n] x‖ < ε :=
    (le_abs_self _).trans_lt hnα
  exact hVup.trans_lt hlt
