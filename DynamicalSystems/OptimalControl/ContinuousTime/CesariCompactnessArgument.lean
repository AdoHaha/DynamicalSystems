/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.MeasureTheory.EquiIntegrableTrajectories
public import DynamicalSystems.OptimalControl.ContinuousTime.CesariExistenceArgument

/-!
# Cesari lower closure from uniformly integrable velocities

Weak L1 compactness is constructed by truncation and Hilbert compactness, and
uniqueness of indefinite integrals yields weak convergence along a uniformly
convergent trajectory subsequence. The existing Mazur/Fatou theorem then recovers
feasible limiting epigraph points using property (Q).

These are Steps 1 and 3 of BM Theorem 5.4.4; noncompact relaxed-control realization
and assembly of the full variable-endpoint optimal-control problem remain separate.
-/

@[expose] public section

open Set Filter MeasureTheory Topology
open DynamicalSystems.EquiIntegrableTrajectories
open scoped ENNReal BoundedContinuousFunction

namespace OptimalControl

section IntervalExtraction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {a b : ℝ}

/-- A trajectory on a compact interval, extended by zero for measure-theoretic
statements on the ambient real line. Only its values on the interval are used. -/
noncomputable def intervalPathValue (x : Icc a b →ᵇ E) (t : ℝ) : E := by
  classical
  exact if ht : t ∈ Icc a b then x ⟨t, ht⟩ else 0

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The interval extension agrees with the original trajectory on its domain. -/
theorem intervalPathValue_of_mem (x : Icc a b →ᵇ E) (t : ℝ) (ht : t ∈ Icc a b) :
    intervalPathValue x t = x ⟨t, ht⟩ := by
  simp [intervalPathValue, ht]

/-- Joint compactness and Cesari/Fatou lower closure on a fixed compact interval.
The limit trajectory, its L1 velocity, the integral law, and the feasible cost
epigraph are all constructed. The original velocities have only uniformly
absolutely continuous integrals; neither weak convergence nor an L2 bound is
assumed. Property (Q) is used in the lower-closure step.
This is fixed-interval analytic extraction in BM Theorem 5.4.4;
measurable relaxed-control realization and global optimality are not conclusions. -/
theorem exists_limit_trajectory_cost_epigraph_of_unifIntegrable
    (hab : a ≤ b) (x : ℕ → Icc a b →ᵇ E)
    (w : ℕ → Lp E 1 (volume.restrict (Icc a b)))
    (Q : ℝ → E → Set (E × ℝ)) (c : ℕ → ℝ → ℝ) (γ : ℝ)
    (K : Set E) (hK : IsCompact K) (hvalues : ∀ n t, x n t ∈ K)
    (hUI : UnifIntegrable (fun n t ↦ w n t) 1 (volume.restrict (Icc a b)))
    (hlaw : ∀ n (s t : Icc a b), x n t - x n s =
      ∫ r in (s : ℝ)..(t : ℝ), w n r ∂volume.restrict (Icc a b))
    (hcesari : ∀ t ∈ Icc a b, ∀ y ∈ K, HasWeakCesariProperty Q t y)
    (hw : ∀ n, ∀ᵐ t ∂volume.restrict (Icc a b),
      (w n t, c n t) ∈ Q t (intervalPathValue (x n) t))
    (hc : ∀ n, ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ c n t)
    (hci : ∀ n, Integrable (c n) (volume.restrict (Icc a b)))
    (hcost : Tendsto (fun n ↦ ∫ t, c n t ∂volume.restrict (Icc a b)) atTop (𝓝 γ)) :
    ∃ (xlim : Icc a b →ᵇ E) (vlim : Lp E 1 (volume.restrict (Icc a b)))
      (costLimit : ℝ → ℝ) (k : ℕ → ℕ), StrictMono k ∧
      Tendsto (x ∘ k) atTop (𝓝 xlim) ∧ (∀ t, xlim t ∈ K) ∧
      (∀ t : Icc a b, xlim t - xlim ⟨a, le_rfl, hab⟩ =
        ∫ r in Ioc a (t : ℝ), vlim r ∂volume.restrict (Icc a b)) ∧
      Integrable costLimit (volume.restrict (Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        (vlim t, costLimit t) ∈ Q t (intervalPathValue xlim t)) ∧
      (∫ t, costLimit t ∂volume.restrict (Icc a b)) ≤ γ := by
  obtain ⟨xlim, vlim, k, hk, hlim, hvalueslim, hweak, hlawlim⟩ :=
    exists_uniform_limit_weak_L1_tendsto_integral_law hab x w K hK hvalues hUI hlaw
  have hcesarilim : ∀ᵐ t ∂volume.restrict (Icc a b),
      HasWeakCesariProperty Q t (intervalPathValue xlim t) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [intervalPathValue_of_mem xlim t ht]
    exact hcesari t ht _ (hvalueslim ⟨t, ht⟩)
  have hxlim : ∀ᵐ t ∂volume.restrict (Icc a b),
      Tendsto (fun n ↦ intervalPathValue (x (k n)) t) atTop
        (𝓝 (intervalPathValue xlim t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [intervalPathValue_of_mem _ t ht, Function.comp_apply] using
      hlim.eval_const ⟨t, ht⟩
  obtain ⟨costLimit, hcostLimit⟩ := exists_integrable_cost_epigraph_of_weak_Lp_tendsto
    Q (intervalPathValue xlim) (fun n ↦ intervalPathValue (x (k n)))
    (fun n ↦ w (k n)) (fun n ↦ c (k n)) vlim γ hcesarilim hxlim
    (fun n ↦ hw (k n)) (fun n ↦ hc (k n)) (fun n ↦ hci (k n))
    (hcost.comp hk.tendsto_atTop) hweak
  exact ⟨xlim, vlim, costLimit, k, hk, hlim, hvalueslim, hlawlim, hcostLimit⟩

end IntervalExtraction

end OptimalControl
