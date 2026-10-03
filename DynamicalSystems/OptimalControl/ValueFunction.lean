/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.FiniteHorizon
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # Dynamic-programming value function

This file develops the value function of the finite-horizon deterministic optimal
control problem and the dynamic-programming (Bellman) recursion that it satisfies.

The value function `valueFunction prob x₀` is the infimum of `finiteHorizonTotalCost`
over all admissible input sequences starting at `x₀`.  The tail problem obtained by
peeling off the first control step is `tailProblem prob`; the central result `bellman`
identifies the value function with the one-step recursion over the first control
followed by the value function of the tail problem.

The material follows Rawlings, Mayne and Diehl, *Model Predictive Control: Theory,
Computation, and Design*, 2nd ed., 2019, Ch. 1 §1.3.2–1.3.3 (printed pp. 12–20) and
Ch. 2 §2.3 (printed p. 107).

## Main definitions

* `tailProblem`: the horizon-one tail problem obtained by shifting the horizon.
* `costSet`: the set of costs of admissible input sequences.
* `valueFunction`: the infimum of `costSet`, i.e. the optimal cost-to-go.
* `firstControls`: the set of first controls together with a feasible tail.

## Main results

* `finiteHorizonRollout_tail`, `finiteHorizonTotalCost_tail`,
  `finiteHorizonAdmissible_tail`: the one-step decomposition of the trajectory,
  the cost and admissibility.
* `valueFunction_le`: the value function is a lower bound for every admissible cost.
* `le_valueFunction`: a lower bound of every admissible cost bounds the value function.
* `valueFunction_eq`: the value function equals the cost of an optimal input.
* `bellman`: the dynamic-programming recursion.

## Implementation notes

The value function is a genuine `sInf` into `ℝ`, which is only conditionally complete.
Consequently the recursion `bellman` needs hypotheses making the relevant infima
well posed: the cost set is nonempty and bounded below, every tail cost set is bounded
below, and the candidate values are bounded below.  When these fail the `sInf`
convention (`sInf ∅ = 0`, unbounded-below sets evaluate to `0`) breaks the recursion.
No trajectory-level probabilistic or martingale content is in scope here.
-/

@[expose] public section

variable {X U : Type*}

/-- The horizon-one tail problem obtained by removing the first control step from
`prob`: same dynamics, stage cost, terminal cost and constraint sets, but horizon
`prob.horizon - 1` (Rawlings–Mayne–Diehl 2019, Ch. 1 §1.3.2, printed p. 12). -/
def tailProblem (prob : FiniteHorizonProblem X U) : FiniteHorizonProblem X U where
  f := prob.f
  stageCost := prob.stageCost
  terminalCost := prob.terminalCost
  horizon := prob.horizon - 1
  stateSet := prob.stateSet
  inputSet := prob.inputSet
  terminalSet := prob.terminalSet

/-- The set of total costs of admissible input sequences from `x₀`. -/
def costSet (prob : FiniteHorizonProblem X U) (x₀ : X) : Set ℝ :=
  {r | ∃ u : Fin prob.horizon → U,
    FiniteHorizonAdmissible prob x₀ u ∧ finiteHorizonTotalCost prob x₀ u = r}

/-- The dynamic-programming value function: the infimum of the total cost over the
admissible input sequences, i.e. the optimal cost-to-go (Rawlings–Mayne–Diehl 2019,
Ch. 1 §1.3.2, printed p. 12). -/
noncomputable def valueFunction (prob : FiniteHorizonProblem X U) (x₀ : X) : ℝ :=
  sInf (costSet prob x₀)

/-- The first controls that are admissible at `x₀` and whose tail problem is feasible
at the successor state. This is the index type of the Bellman recursion. -/
def firstControls (prob : FiniteHorizonProblem X U) (x₀ : X) : Set U :=
  {u | x₀ ∈ prob.stateSet ∧ u ∈ prob.inputSet ∧
    (costSet (tailProblem prob) (prob.f x₀ u)).Nonempty}

/-! ### One-step decomposition -/

/-- The rollout of a problem with horizon `M + 1` at a positive index equals the
rollout of the tail problem. -/
theorem finiteHorizonRollout_tail {f : X → U → X} {ℓ : X → U → ℝ} {Vf : X → ℝ}
    {M : ℕ} {Xs : Set X} {Us : Set U} {Xf : Set X} (x₀ : X) (u : Fin (M + 1) → U)
    (j : Fin (M + 1)) :
    finiteHorizonRollout ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x₀ u j.succ =
      finiteHorizonRollout ⟨f, ℓ, Vf, M, Xs, Us, Xf⟩ (f x₀ (u 0)) (Fin.tail u) j := by
  induction j using Fin.induction with
  | zero =>
    rw [finiteHorizonRollout_succ, Fin.castSucc_zero, finiteHorizonRollout_zero,
      finiteHorizonRollout_zero]
  | succ k ih =>
    rw [finiteHorizonRollout_succ, finiteHorizonRollout_succ, Fin.castSucc_succ, ih]
    rfl

/-- Splitting off the first control from the total cost. -/
theorem finiteHorizonTotalCost_tail {f : X → U → X} {ℓ : X → U → ℝ} {Vf : X → ℝ}
    {M : ℕ} {Xs : Set X} {Us : Set U} {Xf : Set X} (x₀ : X) (u : Fin (M + 1) → U) :
    finiteHorizonTotalCost ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x₀ u =
      ℓ x₀ (u 0) +
        finiteHorizonTotalCost ⟨f, ℓ, Vf, M, Xs, Us, Xf⟩ (f x₀ (u 0)) (Fin.tail u) := by
  unfold finiteHorizonTotalCost
  rw [Fin.sum_univ_succ]
  rw [(Fin.succ_last M).symm]
  rw [Fin.castSucc_zero, finiteHorizonRollout_zero]
  simp only [Fin.castSucc_succ, finiteHorizonRollout_tail, Fin.tail]
  ring

/-- Splitting off the first control from admissibility. -/
theorem finiteHorizonAdmissible_tail {f : X → U → X} {ℓ : X → U → ℝ} {Vf : X → ℝ}
    {M : ℕ} {Xs : Set X} {Us : Set U} {Xf : Set X} (x₀ : X) (u : Fin (M + 1) → U) :
    FiniteHorizonAdmissible ⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ x₀ u ↔
      x₀ ∈ Xs ∧ u 0 ∈ Us ∧
        FiniteHorizonAdmissible ⟨f, ℓ, Vf, M, Xs, Us, Xf⟩ (f x₀ (u 0)) (Fin.tail u) := by
  unfold FiniteHorizonAdmissible
  rw [Fin.forall_fin_succ]
  rw [(Fin.succ_last M).symm]
  rw [Fin.castSucc_zero, finiteHorizonRollout_zero]
  simp only [Fin.castSucc_succ, finiteHorizonRollout_tail, Fin.tail]
  tauto

/-! ### Value-function sandwich -/

/-- The value function is a lower bound of the cost of every admissible input sequence.
The boundedness hypothesis is needed because `ℝ` is only conditionally complete. -/
theorem valueFunction_le (prob : FiniteHorizonProblem X U) (x₀ : X)
    (u : Fin prob.horizon → U) (hu : FiniteHorizonAdmissible prob x₀ u)
    (hbd : BddBelow (costSet prob x₀)) :
    valueFunction prob x₀ ≤ finiteHorizonTotalCost prob x₀ u :=
  csInf_le hbd ⟨u, hu, rfl⟩

/-- A lower bound of every admissible cost bounds the value function. -/
theorem le_valueFunction (prob : FiniteHorizonProblem X U) (x₀ : X) {a : ℝ}
    (hne : (costSet prob x₀).Nonempty)
    (ha : ∀ r ∈ costSet prob x₀, a ≤ r) : a ≤ valueFunction prob x₀ :=
  le_csInf hne ha

/-! ### Attainment -/

/-- An admissible input sequence whose cost is minimal: a minimizer of the
finite-horizon problem (Rawlings–Mayne–Diehl 2019, Ch. 1 §1.3.1). -/
def IsOptimalInput (prob : FiniteHorizonProblem X U) (x₀ : X)
    (u : Fin prob.horizon → U) : Prop :=
  FiniteHorizonAdmissible prob x₀ u ∧
    ∀ v, FiniteHorizonAdmissible prob x₀ v →
      finiteHorizonTotalCost prob x₀ u ≤ finiteHorizonTotalCost prob x₀ v

/-- When a minimizer exists, the value function equals its cost.  If no minimizer
exists this fails in general and one should use the `valueFunction_le` /
`le_valueFunction` sandwich instead. -/
theorem valueFunction_eq (prob : FiniteHorizonProblem X U) (x₀ : X)
    (u : Fin prob.horizon → U) (hu : IsOptimalInput prob x₀ u)
    (hbd : BddBelow (costSet prob x₀)) :
    valueFunction prob x₀ = finiteHorizonTotalCost prob x₀ u := by
  refine le_antisymm ?_ ?_
  · exact csInf_le hbd ⟨u, hu.1, rfl⟩
  · refine le_csInf ⟨finiteHorizonTotalCost prob x₀ u, ⟨u, hu.1, rfl⟩⟩ ?_
    intro r hr
    obtain ⟨v, hv, rfl⟩ := hr
    exact hu.2 v hv

/-! ### Dynamic-programming recursion -/

/-- The dynamic-programming (Bellman) recursion: the optimal cost-to-go equals the
infimum over the admissible first controls of the stage cost plus the optimal
cost-to-go of the tail problem (Rawlings–Mayne–Diehl 2019, Ch. 1 §1.3.3, printed
p. 13, and Ch. 2 §2.3, printed p. 107).

The hypotheses make the relevant infima well posed; in particular every admissible
first control must have a feasible tail, and all cost sets involved must be bounded
below.  Without them the `sInf` convention for unbounded or empty sets breaks the
recursion (the value function would evaluate an infeasible tail to `0`). -/
theorem bellman (prob : FiniteHorizonProblem X U) (x₀ : X) (hN : 0 < prob.horizon)
    (hsub : (costSet prob x₀).Nonempty)
    (hbd : BddBelow (costSet prob x₀))
    (hbdt : ∀ u : U, BddBelow (costSet (tailProblem prob) (prob.f x₀ u)))
    (hbdr : BddBelow (Set.range (fun u : (firstControls prob x₀) =>
        prob.stageCost x₀ u.1 + valueFunction (tailProblem prob) (prob.f x₀ u.1)))) :
    valueFunction prob x₀ = ⨅ u : (firstControls prob x₀),
        prob.stageCost x₀ u.1 + valueFunction (tailProblem prob) (prob.f x₀ u.1) := by
  obtain ⟨f, ℓ, Vf, N, Xs, Us, Xf⟩ := prob
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hN)
  let g : (firstControls (⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ : FiniteHorizonProblem X U) x₀) → ℝ :=
    fun u => ℓ x₀ u.1 +
      sInf (costSet (⟨f, ℓ, Vf, M, Xs, Us, Xf⟩ : FiniteHorizonProblem X U) (f x₀ u.1))
  change sInf (costSet (⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ : FiniteHorizonProblem X U) x₀)
    = sInf (Set.range g)
  have hA : (firstControls
      (⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ : FiniteHorizonProblem X U) x₀).Nonempty := by
    obtain ⟨r, u, hu, _⟩ := hsub
    have hdec := (finiteHorizonAdmissible_tail (Xs := Xs) (Us := Us) (Xf := Xf) x₀ u).mp hu
    exact ⟨u 0, by simpa using (hu.1 0).1, (hu.1 0).2,
      ⟨finiteHorizonTotalCost (⟨f, ℓ, Vf, M, Xs, Us, Xf⟩ : FiniteHorizonProblem X U)
          (f x₀ (u 0)) (Fin.tail u), Fin.tail u, hdec.2.2, rfl⟩⟩
  refine le_antisymm ?_ ?_
  · refine le_csInf ?_ ?_
    · rcases hA with ⟨u₀, hu₀⟩
      exact ⟨g ⟨u₀, hu₀⟩, ⟨⟨u₀, hu₀⟩, rfl⟩⟩
    · intro y hy
      obtain ⟨u, rfl⟩ := hy
      obtain ⟨u, xu, uu, hCu⟩ := u
      have hbu : BddBelow (costSet
          (⟨f, ℓ, Vf, M, Xs, Us, Xf⟩ : FiniteHorizonProblem X U) (f x₀ u)) := hbdt u
      refine le_of_forall_pos_le_add ?_
      intro ε hε
      have hlt : sInf (costSet (⟨f, ℓ, Vf, M, Xs, Us, Xf⟩ : FiniteHorizonProblem X U) (f x₀ u))
          < sInf (costSet (⟨f, ℓ, Vf, M, Xs, Us, Xf⟩ : FiniteHorizonProblem X U) (f x₀ u))
            + ε := by
        linarith
      obtain ⟨r, hrC, hrlt⟩ := (csInf_lt_iff hbu hCu).mp hlt
      have hmemS : ℓ x₀ u + r ∈
          costSet (⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ : FiniteHorizonProblem X U) x₀ := by
        obtain ⟨v, hv, hvr⟩ := hrC
        refine ⟨Fin.cons u v, ?_, ?_⟩
        · rw [finiteHorizonAdmissible_tail]
          exact ⟨xu, uu, by rw [Fin.cons_zero, Fin.tail_cons]; exact hv⟩
        · rw [finiteHorizonTotalCost_tail, Fin.cons_zero, Fin.tail_cons, hvr]
      have hSle : sInf (costSet (⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ : FiniteHorizonProblem X U) x₀)
          ≤ ℓ x₀ u + r := csInf_le hbd hmemS
      have hgr : ℓ x₀ u + r < g ⟨u, xu, uu, hCu⟩ + ε := by
        simp only [g]
        linarith
      linarith
  · refine le_csInf hsub ?_
    intro s hs
    obtain ⟨u0, hu0, hs⟩ := hs
    have hdec := (finiteHorizonAdmissible_tail (Xs := Xs) (Us := Us) (Xf := Xf) x₀ u0).mp hu0
    have hmem : u0 0 ∈ firstControls
        (⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ : FiniteHorizonProblem X U) x₀ :=
      ⟨hdec.1, hdec.2.1,
        ⟨finiteHorizonTotalCost (⟨f, ℓ, Vf, M, Xs, Us, Xf⟩ : FiniteHorizonProblem X U)
            (f x₀ (u0 0)) (Fin.tail u0), Fin.tail u0, hdec.2.2, rfl⟩⟩
    have hgr : sInf (Set.range g) ≤ g ⟨u0 0, hmem⟩ :=
      csInf_le hbdr ⟨⟨u0 0, hmem⟩, rfl⟩
    have hgl : g ⟨u0 0, hmem⟩ ≤ s := by
      have hcs : sInf (costSet
          (⟨f, ℓ, Vf, M, Xs, Us, Xf⟩ : FiniteHorizonProblem X U) (f x₀ (u0 0)))
          ≤ finiteHorizonTotalCost (⟨f, ℓ, Vf, M, Xs, Us, Xf⟩ : FiniteHorizonProblem X U)
              (f x₀ (u0 0)) (Fin.tail u0) :=
        csInf_le (hbdt (u0 0)) ⟨Fin.tail u0, hdec.2.2, rfl⟩
      have hcost : finiteHorizonTotalCost
            (⟨f, ℓ, Vf, M + 1, Xs, Us, Xf⟩ : FiniteHorizonProblem X U) x₀ u0
          = ℓ x₀ (u0 0) + finiteHorizonTotalCost
              (⟨f, ℓ, Vf, M, Xs, Us, Xf⟩ : FiniteHorizonProblem X U)
              (f x₀ (u0 0)) (Fin.tail u0) :=
        finiteHorizonTotalCost_tail x₀ u0
      simp only [g]
      rw [← hs, hcost]
      linarith
    linarith
