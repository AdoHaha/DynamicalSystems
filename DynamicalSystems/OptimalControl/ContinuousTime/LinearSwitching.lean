/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.Reachability
public import DynamicalSystems.Linear.Kalman
public import DynamicalSystems.Mathlib.Analysis.Analytic.FiniteZeros
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.Deriv.Shift

/-!
# Nondegenerate switching functions for linear systems

For `x' = A x + B u`, a terminal covector `q` produces the switching function
`q (exp ((T - t) A) b)` for an input column `b`. The finite Krylov spanning
condition is imposed **on each input column**, not merely on the combined pair
`(A, B)`. From this algebraic condition and `q ≠ 0` we derive nontriviality and
then finiteness of the zero set on every compact interval.

No nonvanishing/finite-zero assumption is hidden in the data, and no
optimality-to-PMP implication is asserted in this structural module.
-/

@[expose] public section

open Set

namespace OptimalControl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A single input column is cyclic when its finite Krylov family spans the
whole state space. This is the per-input controllability condition used by the
finite-switch theorem. -/
def CyclicInput (A : E →L[ℝ] E) (b : E) : Prop :=
  Submodule.span ℝ (Set.range (fun k : Fin (Module.finrank ℝ E) =>
    (A.toLinearMap ^ (k : ℕ)) b)) = ⊤

/-- Covector propagated backwards from terminal time `T`. -/
noncomputable def terminalAdjointCovector (A : E →L[ℝ] E) (q : E →L[ℝ] ℝ)
    (T t : ℝ) : E →L[ℝ] ℝ :=
  q.comp (NormedSpace.exp ((T - t) • A))

/-- Switching coefficient of one input channel. -/
noncomputable def linearSwitchingFunction (A : E →L[ℝ] E) (q : E →L[ℝ] ℝ)
    (b : E) (T t : ℝ) : ℝ :=
  q (NormedSpace.exp ((T - t) • A) b)

omit [FiniteDimensional ℝ E] in
@[simp] theorem terminalAdjointCovector_apply (A : E →L[ℝ] E)
    (q : E →L[ℝ] ℝ) (T t : ℝ) (b : E) :
    terminalAdjointCovector A q T t b = linearSwitchingFunction A q b T t := rfl

omit [FiniteDimensional ℝ E] in
@[simp] theorem terminalAdjointCovector_terminal (A : E →L[ℝ] E)
    (q : E →L[ℝ] ℝ) (T : ℝ) : terminalAdjointCovector A q T T = q := by
  ext b
  simp [terminalAdjointCovector]

/-- The propagated covector satisfies the actual homogeneous adjoint ODE,
not just a formula bearing the name of a costate. -/
theorem hasDerivAt_terminalAdjointCovector (A : E →L[ℝ] E)
    (q : E →L[ℝ] ℝ) (T t : ℝ) :
    HasDerivAt (terminalAdjointCovector A q T)
      (-(terminalAdjointCovector A q T t).comp A) t := by
  have he := (hasDerivAt_exp_smul_const A (T - t)).comp_const_sub T t
  have hp := (hasDerivAt_const (x := t) (c := q)).clm_comp he
  convert hp using 1
  · rfl
  · ext b
    simp [terminalAdjointCovector]

/-- Every linear switching function is analytic on the entire real line,
including the horizon endpoints. -/
theorem analytic_linearSwitchingFunction (A : E →L[ℝ] E) (q : E →L[ℝ] ℝ)
    (b : E) (T : ℝ) : AnalyticOnNhd ℝ (linearSwitchingFunction A q b T) univ := by
  intro t _
  have hs : AnalyticAt ℝ (fun s : ℝ => (T - s) • A) t :=
    (analyticAt_const.sub analyticAt_id).smul analyticAt_const
  have he : AnalyticAt ℝ (fun s : ℝ => NormedSpace.exp ((T - s) • A)) t :=
    (NormedSpace.exp_analytic (𝕂 := ℝ) ((T - t) • A)).comp
      (f := fun s : ℝ => (T - s) • A) hs
  exact (q.analyticAt _).comp (((ContinuousLinearMap.apply ℝ E b).analyticAt _).comp he)

/-- The finite Krylov rank condition really excludes an identically zero
switching coefficient for every nonzero terminal covector. -/
theorem exists_ne_zero_linearSwitchingFunction (A : E →L[ℝ] E)
    (q : E →L[ℝ] ℝ) (b : E) (T : ℝ) (hb : CyclicInput A b) (hq : q ≠ 0) :
    ∃ t, linearSwitchingFunction A q b T t ≠ 0 := by
  by_contra h
  push Not at h
  let sys : LinearSystem ℝ E ℝ ℝ :=
    { A := A.toLinearMap, B := 0, C := q.toLinearMap, D := 0 }
  have hA : sys.continuousA = A := by ext z; rfl
  have hz : ∀ t ∈ Icc (0 : ℝ) 1, sys.C (sys.expFlow t b) = 0 := by
    intro t _
    change q (NormedSpace.exp (t • sys.continuousA) b) = 0
    rw [hA]
    have ht := h (T - t)
    simpa [linearSwitchingFunction] using ht
  have hk := LinearMap.mem_unobservableSubspace.mp
    (sys.mem_unobservableSubspace_of_forall_continuousC_expFlow_eq_zero
      (by norm_num : (0 : ℝ) < 1) hz)
  have hker : Submodule.span ℝ (Set.range (fun k : Fin (Module.finrank ℝ E) =>
      (A.toLinearMap ^ (k : ℕ)) b)) ≤ LinearMap.ker q.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro z ⟨k, rfl⟩
    exact hk k
  rw [hb] at hker
  apply hq
  ext z
  exact hker (Submodule.mem_top)

/-- A single nondegenerate input has only finitely many switching-function
zeros on a compact interval. The interval can be empty or a singleton. -/
theorem finite_zeroSet_linearSwitchingFunction (A : E →L[ℝ] E)
    (q : E →L[ℝ] ℝ) (b : E) (T a c : ℝ) (hb : CyclicInput A b) (hq : q ≠ 0) :
    {t | t ∈ Icc a c ∧ linearSwitchingFunction A q b T t = 0}.Finite :=
  (analytic_linearSwitchingFunction A q b T).finite_zeroSet_Icc
    (exists_ne_zero_linearSwitchingFunction A q b T hb hq) a c

/-- All input switching zeros are contained in one finite set when every input
column is cyclic. Combined controllability of `(A,B)` is not used as a
substitute for the per-input assumptions. -/
theorem finite_all_switching_zeros {ι : Type*} [Finite ι]
    (A : E →L[ℝ] E) (q : E →L[ℝ] ℝ) (b : ι → E) (T a c : ℝ)
    (hb : ∀ i, CyclicInput A (b i)) (hq : q ≠ 0) :
    {t | t ∈ Icc a c ∧ ∃ i, linearSwitchingFunction A q (b i) T t = 0}.Finite := by
  have hf : (⋃ i, {t | t ∈ Icc a c ∧
      linearSwitchingFunction A q (b i) T t = 0}).Finite :=
    Set.finite_iUnion (fun i => finite_zeroSet_linearSwitchingFunction A q (b i) T a c
      (hb i) hq)
  convert hf using 1
  ext t
  simp only [mem_ofPred_eq, mem_iUnion]
  aesop

end OptimalControl
