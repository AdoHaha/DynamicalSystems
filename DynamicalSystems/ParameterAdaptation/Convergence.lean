/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.ParameterAdaptation.Excitation
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! # Parametric convergence under persistent excitation (Landau Theorem 3.5)

This file formalizes the deterministic parametric-convergence result of
I. D. Landau, R. Lozano, M'Saad and A. Karimi, *Adaptive Control: Algorithms,
Analysis and Applications*, 2nd ed., Springer 2011, Sect. 3.4.3 (Theorem 3.5,
printed pp. 116–118).

The plant is `y(t) = φ(t)ᵀθ`, the predictor `ŷ(t) = φ(t)ᵀθ̂(t)`, and the
parameter error is `θ̃ = θ − θ̂`. The regressor `φ` is persistently exciting
when every sliding window of `N ≥ 1` consecutive regressors satisfies the
finite-window quadratic-form lower bound

`alpha * ∑ k, v k ^ 2 ≤ ∑ j : Fin N, (∑ k, φ(t + j) k * v k) ^ 2`,

i.e. the sliding sample-covariance dominates `alpha • 1` (compare
`pe_quadform_lower_bound` in `ParameterAdaptation/Excitation.lean` and the
persistent-excitation condition (3.296) / Theorem 3.4).

The two main results are:

* `pe_parameter_convergence_static`: if the prediction error
  `(φ(t)ᵀθ̃) → 0`, then `θ̃ = 0`. This is the parametrized core of Landau
  Theorem 3.5: the persistent excitation makes the identifiability matrix
  coercive, so a vanishing prediction error forces the parameter error to
  vanish.
* `pe_parameter_convergence_dynamic`: for a time-varying parameter error
  `θ̃(t)` with vanishing prediction error `(φ(t)ᵀθ̃(t)) → 0`, bounded regressor
  `‖φ(t)‖² ≤ Mphi`, and vanishing increments
  `(∑ k, (θ̃(t+1) k − θ̃(t) k)²) → 0`, the parameter-error norm also vanishes:
  `(∑ k, θ̃(t) k²) → 0`. No convergence of `θ̃(t)` itself is assumed.

## Main results

* `pe_parameter_convergence_static`
* `pe_parameter_convergence_dynamic`
-/

@[expose] public section

open Filter
open scoped Topology

/-- The squared norm of one parameter-adaptation increment,
`∑ k, (θ(t+1) k − θ(t) k)²`. This is the decay rate whose vanishing is assumed
in `pe_parameter_convergence_dynamic`. -/
private def stepSq {n : ℕ} (theta : ℕ → Fin n → ℝ) (t : ℕ) : ℝ :=
  ∑ k, (theta (t + 1) k - theta t k) ^ 2

/-- Telescoping norm bound for the drift of a sequence over a window of length
`j`: the squared norm of `θ(t) − θ(t+j)` is at most `j` times the sum of the
squared norms of the consecutive increments across the window
(Cauchy–Schwarz along the window). -/
private lemma sum_sq_sub_shift_le {n : ℕ} (theta : ℕ → Fin n → ℝ) (j t : ℕ) :
    ∑ k, (theta t k - theta (t + j) k) ^ 2 ≤
      (j : ℝ) * ∑ i ∈ Finset.range j, stepSq theta (t + i) := by
  have htel : ∀ k, theta t k - theta (t + j) k =
      -∑ i ∈ Finset.range j, (theta (t + i + 1) k - theta (t + i) k) := by
    intro k
    have h := Finset.sum_range_sub (fun i => theta (t + i) k) j
    have h' : (∑ i ∈ Finset.range j, (theta (t + i + 1) k - theta (t + i) k)) =
        theta (t + j) k - theta t k := by
      simpa only [← Nat.add_assoc, Nat.add_zero] using h
    rw [h']
    ring
  calc ∑ k, (theta t k - theta (t + j) k) ^ 2
      = ∑ k, (∑ i ∈ Finset.range j,
            (theta (t + i + 1) k - theta (t + i) k)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro k _
        rw [htel k]
        ring
    _ ≤ ∑ k, (j : ℝ) * ∑ i ∈ Finset.range j,
          (theta (t + i + 1) k - theta (t + i) k) ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        have h := sq_sum_le_card_mul_sum_sq (s := Finset.range j)
          (f := fun i => theta (t + i + 1) k - theta (t + i) k)
        simpa [Finset.card_range] using h
    _ = (j : ℝ) * ∑ i ∈ Finset.range j, stepSq theta (t + i) := by
        simp only [stepSq, Finset.mul_sum]
        rw [Finset.sum_comm]

/-- If the consecutive increments `θ(t+1) − θ(t)` have squared norm tending to
`0`, then so does the drift `θ(t) − θ(t+j)` over any fixed window length `j`. -/
private lemma tendsto_sum_sq_sub_shift_zero {n : ℕ} (theta : ℕ → Fin n → ℝ)
    (hstep : Filter.Tendsto (stepSq theta) Filter.atTop (𝓝 0)) (j : ℕ) :
    Filter.Tendsto (fun t ↦ ∑ k, (theta t k - theta (t + j) k) ^ 2)
      Filter.atTop (𝓝 0) := by
  have hU : Filter.Tendsto
      (fun t => (j : ℝ) * ∑ i ∈ Finset.range j, stepSq theta (t + i))
      Filter.atTop (𝓝 0) := by
    have hsum : Filter.Tendsto (fun t => ∑ i ∈ Finset.range j, stepSq theta (t + i))
        Filter.atTop (𝓝 0) := by
      have h := tendsto_finsetSum (s := Finset.range j) (a := fun _ : ℕ => (0 : ℝ))
        (f := fun (i : ℕ) (t : ℕ) => stepSq theta (t + i))
        (fun i _ => by simpa using (Filter.tendsto_add_atTop_iff_nat i).mpr hstep)
      simpa using h
    simpa using hsum.const_mul (j : ℝ)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hU
    (fun t => Finset.sum_nonneg (fun k _ => sq_nonneg _))
    (fun t => sum_sq_sub_shift_le theta j t)

/-- **Static parametric convergence (Landau Theorem 3.5).** Let `φ` be a
persistently exciting regressor with sliding-window excitation level `alpha > 0`
and constant parameter error `θ̃`. If the prediction error `φ(t)ᵀθ̃ → 0`, then
`θ̃ = 0`. -/
theorem pe_parameter_convergence_static {n N : ℕ} (phi : ℕ → Fin n → ℝ)
    (thetaTilde : Fin n → ℝ) {alpha : ℝ} (halpha : 0 < alpha)
    (hPE : ∀ t, ∀ v : Fin n → ℝ,
      alpha * ∑ k, v k ^ 2 ≤ ∑ j : Fin N, (∑ k, phi (t + j.val) k * v k) ^ 2)
    (herr : Filter.Tendsto (fun t ↦ ∑ k, phi t k * thetaTilde k) Filter.atTop (𝓝 0)) :
    thetaTilde = 0 := by
  have hbound : ∀ t, alpha * ∑ k, thetaTilde k ^ 2 ≤
      ∑ j : Fin N, (∑ k, phi (t + j.val) k * thetaTilde k) ^ 2 :=
    fun t => hPE t thetaTilde
  have hg : Filter.Tendsto
      (fun t => ∑ j : Fin N, (∑ k, phi (t + j.val) k * thetaTilde k) ^ 2)
      Filter.atTop (𝓝 0) := by
    have h := tendsto_finsetSum (s := Finset.univ) (a := fun _ : Fin N => (0 : ℝ))
      (f := fun (j : Fin N) (t : ℕ) =>
        (∑ k, phi (t + j.val) k * thetaTilde k) ^ 2) (fun j _ => by
          have hj : Filter.Tendsto (fun t => ∑ k, phi (t + j.val) k * thetaTilde k)
              Filter.atTop (𝓝 0) :=
            (Filter.tendsto_add_atTop_iff_nat j.val).mpr herr
          simpa using hj.pow 2)
    simpa using h
  have hle : alpha * ∑ k, thetaTilde k ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hg hbound
  have hS0 : ∑ k, thetaTilde k ^ 2 = 0 := by
    have hle0 : ∑ k, thetaTilde k ^ 2 ≤ 0 := nonpos_of_mul_nonpos_right hle halpha
    have hge0 : 0 ≤ ∑ k, thetaTilde k ^ 2 :=
      Finset.sum_nonneg (fun k _ => sq_nonneg _)
    linarith
  funext k
  exact sq_eq_zero_iff.mp
    ((Finset.sum_eq_zero_iff_of_nonneg
      (fun k (_ : k ∈ Finset.univ) => sq_nonneg (thetaTilde k))).mp hS0 k
        (Finset.mem_univ k))

/-- **Dynamic parametric convergence (Landau Theorem 3.5).** Let `φ` be a
persistently exciting regressor with sliding-window excitation level `alpha > 0`
and let `θ̃(t)` be a time-varying parameter error with bounded regressor
`‖φ(t)‖² ≤ Mphi`. If the prediction error `φ(t)ᵀθ̃(t) → 0` and the parameter
increments satisfy `‖θ̃(t+1) − θ̃(t)‖² → 0`, then the parameter-error norm
vanishes: `‖θ̃(t)‖² → 0`. No convergence of `θ̃(t)` is assumed. -/
theorem pe_parameter_convergence_dynamic {n N : ℕ} (phi : ℕ → Fin n → ℝ)
    (thetaTilde : ℕ → Fin n → ℝ) {alpha : ℝ} (halpha : 0 < alpha)
    (hPE : ∀ t, ∀ v : Fin n → ℝ,
      alpha * ∑ k, v k ^ 2 ≤ ∑ j : Fin N, (∑ k, phi (t + j.val) k * v k) ^ 2)
    (herr : Filter.Tendsto (fun t ↦ ∑ k, phi t k * thetaTilde t k) Filter.atTop (𝓝 0))
    (hstep : Filter.Tendsto (fun t ↦ ∑ k, (thetaTilde (t + 1) k - thetaTilde t k) ^ 2)
      Filter.atTop (𝓝 0))
    (hphi : ∃ Mphi, ∀ t, ∑ k, (phi t k) ^ 2 ≤ Mphi) :
    Filter.Tendsto (fun t ↦ ∑ k, (thetaTilde t k) ^ 2) Filter.atTop (𝓝 0) := by
  obtain ⟨Mphi, hMphi⟩ := hphi
  have ha : Filter.Tendsto
      (fun t => ∑ j : Fin N, (∑ k, phi (t + j.val) k * thetaTilde t k) ^ 2)
      Filter.atTop (𝓝 0) := by
    have h := tendsto_finsetSum (s := Finset.univ) (a := fun _ : Fin N => (0 : ℝ))
      (f := fun (j : Fin N) (t : ℕ) =>
        (∑ k, phi (t + j.val) k * thetaTilde t k) ^ 2) (fun j _ => by
          have hP : Filter.Tendsto
              (fun t => (∑ k, phi (t + j.val) k * thetaTilde (t + j.val) k) ^ 2)
              Filter.atTop (𝓝 0) := by
            have hj := (Filter.tendsto_add_atTop_iff_nat j.val).mpr herr
            simpa using hj.pow 2
          have hA : Filter.Tendsto
              (fun t => ∑ k, (thetaTilde t k - thetaTilde (t + j.val) k) ^ 2)
              Filter.atTop (𝓝 0) :=
            tendsto_sum_sq_sub_shift_zero thetaTilde hstep j.val
          have hU : Filter.Tendsto
              (fun t => 2 * (∑ k, phi (t + j.val) k * thetaTilde (t + j.val) k) ^ 2 +
                2 * ((∑ k, (thetaTilde t k - thetaTilde (t + j.val) k) ^ 2) * Mphi))
              Filter.atTop (𝓝 0) := by
            have h2 : Filter.Tendsto
                (fun t => 2 * (∑ k, phi (t + j.val) k * thetaTilde (t + j.val) k) ^ 2)
                Filter.atTop (𝓝 0) := by
              simpa using hP.const_mul (2 : ℝ)
            have h3 : Filter.Tendsto
                (fun t => (∑ k, (thetaTilde t k - thetaTilde (t + j.val) k) ^ 2) * Mphi)
                Filter.atTop (𝓝 0) := by
              simpa using hA.mul tendsto_const_nhds
            have h4 : Filter.Tendsto
                (fun t => 2 * ((∑ k, (thetaTilde t k - thetaTilde (t + j.val) k) ^ 2) * Mphi))
                Filter.atTop (𝓝 0) := by
              simpa using h3.const_mul (2 : ℝ)
            simpa using h2.add h4
          refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hU
            (fun t => sq_nonneg _) (fun t => ?_)
          have hsplit : (∑ k, phi (t + j.val) k * thetaTilde t k) =
              (∑ k, phi (t + j.val) k * thetaTilde (t + j.val) k) +
              ∑ k, phi (t + j.val) k * (thetaTilde t k - thetaTilde (t + j.val) k) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro k _
            ring
          have hE2 :
              (∑ k, phi (t + j.val) k * (thetaTilde t k - thetaTilde (t + j.val) k)) ^ 2 ≤
                Mphi * ∑ k, (thetaTilde t k - thetaTilde (t + j.val) k) ^ 2 := by
            calc _ ≤ (∑ k, (phi (t + j.val) k) ^ 2) *
                  ∑ k, (thetaTilde t k - thetaTilde (t + j.val) k) ^ 2 :=
                  Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
              _ ≤ Mphi * ∑ k, (thetaTilde t k - thetaTilde (t + j.val) k) ^ 2 :=
                  mul_le_mul_of_nonneg_right (hMphi (t + j.val))
                    (Finset.sum_nonneg (fun k _ => sq_nonneg _))
          rw [hsplit]
          calc ((∑ k, phi (t + j.val) k * thetaTilde (t + j.val) k) +
                  ∑ k, phi (t + j.val) k * (thetaTilde t k - thetaTilde (t + j.val) k)) ^ 2
              ≤ 2 * ((∑ k, phi (t + j.val) k * thetaTilde (t + j.val) k) ^ 2 +
                  (∑ k, phi (t + j.val) k * (thetaTilde t k - thetaTilde (t + j.val) k)) ^ 2) :=
                add_sq_le
            _ ≤ 2 * ((∑ k, phi (t + j.val) k * thetaTilde (t + j.val) k) ^ 2 +
                  Mphi * ∑ k, (thetaTilde t k - thetaTilde (t + j.val) k) ^ 2) := by
                apply mul_le_mul_of_nonneg_left
                · exact add_le_add_right hE2 _
                · norm_num
            _ = 2 * (∑ k, phi (t + j.val) k * thetaTilde (t + j.val) k) ^ 2 +
                  2 * ((∑ k, (thetaTilde t k - thetaTilde (t + j.val) k) ^ 2) * Mphi) := by
                ring)
    simpa using h
  have hbound : ∀ t, alpha * ∑ k, (thetaTilde t k) ^ 2 ≤
      ∑ j : Fin N, (∑ k, phi (t + j.val) k * thetaTilde t k) ^ 2 :=
    fun t => hPE t (thetaTilde t)
  have h1 : Filter.Tendsto (fun t => alpha * ∑ k, (thetaTilde t k) ^ 2)
      Filter.atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ha
      (fun t => mul_nonneg halpha.le (Finset.sum_nonneg (fun k _ => sq_nonneg _)))
      hbound
  have h2 : Filter.Tendsto
      (fun t => alpha⁻¹ * (alpha * ∑ k, (thetaTilde t k) ^ 2)) Filter.atTop (𝓝 0) := by
    simpa using h1.const_mul alpha⁻¹
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun t => ?_)) h2
  rw [inv_mul_cancel_left₀ (ne_of_gt halpha)]
