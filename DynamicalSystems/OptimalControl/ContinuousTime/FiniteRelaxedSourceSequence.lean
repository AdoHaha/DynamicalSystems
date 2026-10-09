/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.FiniteRelaxedAdmissible
public import DynamicalSystems.OptimalControl.ContinuousTime.IntegralCostShift

/-!
# Analytic data derived from admissible finite relaxed pairs

The shifted costs, epigraph membership, integral laws and compactness inputs are
constructed from the original admissible pairs. Time-state compactness is also
preserved at the limiting endpoints, not only at interior times.
-/

@[expose] public section

open Set MeasureTheory Filter
open DynamicalSystems.ClassicalEquiAC
open scoped Topology BoundedContinuousFunction

namespace OptimalControl

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace U]

namespace FiniteRelaxedAdmissiblePair

variable {N : ℕ} {P : FiniteRelaxedBolzaData E U} (p : FiniteRelaxedAdmissiblePair N P)

/-- Subtract the lower bound on the pair's actual interval, then extend by zero.
The order of these operations is important for moving endpoints. -/
noncomputable def shiftedCost (β : ℝ → ℝ) : ℝ → ℝ :=
  zeroExtension p.startTime p.endTime (fun t ↦ p.cost t - β t)

/-- Integrability of the shifted ambient cost follows from source integrability. -/
theorem shiftedCost_integrable {β : ℝ → ℝ} (hβ : IntegrableOn β (Icc P.a P.b)) :
    Integrable (p.shiftedCost β) (volume.restrict (Icc P.a P.b)) := by
  have hβp := hβ.mono_set (show Icc (p.startTime : ℝ) (p.endTime : ℝ) ⊆ Icc P.a P.b from
    fun t ht ↦ ⟨p.startTime.property.1.trans ht.1, ht.2.trans p.endTime.property.2⟩)
  exact (integrable_zeroExtension (p.cost_integrable.sub hβp)).restrict

/-- The original ordinary lower-cost bound also bounds every admissible
finite relaxed cost, since its weights are a normalized nonnegative simplex. -/
theorem cost_ge_lowerBound {β : ℝ → ℝ}
    (hlower : ∀ q ∈ P.controlGraph, β q.1 ≤ P.runningCost q) :
    ∀ᵐ t ∂volume.restrict (Icc (p.startTime : ℝ) (p.endTime : ℝ)), β t ≤ p.cost t := by
  filter_upwards [p.graph_mem] with t ht
  exact finiteRelaxedRunningCost_ge_of_lowerBound N P.controlGraph P.runningCost _ ht
    (β t) (fun u hu ↦ hlower _ hu)

/-- Nonnegativity on the common interval is proved, not supplied by the source. -/
theorem shiftedCost_nonneg {β : ℝ → ℝ}
    (hlower : ∀ q ∈ P.controlGraph, β q.1 ≤ P.runningCost q) :
    ∀ᵐ t ∂volume.restrict (Icc P.a P.b), 0 ≤ p.shiftedCost β t :=
  ae_nonneg_zeroExtension_sub (p.cost_ge_lowerBound hlower)

/-- The transformed analytic objective is exactly the original pair's objective. -/
theorem shifted_objective_eq {β : ℝ → ℝ} (hβ : IntegrableOn β (Icc P.a P.b)) :
    compensatedTerminalCost P.a P.b β P.terminalCost
        ((p.startTime : ℝ), p.extendedPath p.startTime,
          (p.endTime : ℝ), p.extendedPath p.endTime) +
      (∫ t, p.shiftedCost β t ∂volume.restrict (Icc P.a P.b)) = p.objective := by
  simpa only [extendedPath_start, extendedPath_end, shiftedCost, objective, endpointData] using
    compensated_objective_eq p.startTime.property.1 p.endTime.property.2 p.time_lt.le
      P.terminalCost (p.path p.startTime) (p.path p.endTime) p.cost β p.cost_integrable hβ

/-- The actual extended velocity and shifted cost belong to the shifted
relaxed epigraph on the pair's own interior interval. Exterior feasibility is
not imposed: the analytic moving-interval theorem handles that region. -/
theorem shifted_epigraph_mem (β : ℝ → ℝ) :
    ∀ᵐ t ∂volume.restrict (Icc P.a P.b),
      t ∈ Ioo (p.startTime : ℝ) (p.endTime : ℝ) →
        (p.extendedVelocityLp t, p.shiftedCost β t) ∈
          shiftedVelocityCostSet (P.relaxedEpigraph N) β t (intervalPathValue p.extendedPath t) := by
  have HG : ∀ᵐ t ∂volume, t ∈ Icc (p.startTime : ℝ) (p.endTime : ℝ) →
      (t, p.path t, p.control t) ∈ finiteRelaxedControlGraph N P.controlGraph :=
    (ae_restrict_iff' measurableSet_Icc).mp p.graph_mem
  filter_upwards [HG.filter_mono ae_restrict_le, p.extendedVelocityLp_ae,
    ae_restrict_mem measurableSet_Icc] with t hg hv ht
  intro hi
  have hioc : t ∈ Ioc (p.startTime : ℝ) (p.endTime : ℝ) := ⟨hi.1, hi.2.le⟩
  have hicc : t ∈ Icc (p.startTime : ℝ) (p.endTime : ℝ) := ⟨hi.1.le, hi.2.le⟩
  have hpath : intervalPathValue p.extendedPath t = p.path t := by
    rw [intervalPathValue_of_mem _ _ ht]
    exact p.extendedPath_eq ⟨t, ht⟩ hicc
  have hvel : p.extendedVelocityLp t = p.velocity t := by
    rw [hv]
    exact indicator_of_mem hioc _
  have hcost : p.shiftedCost β t = p.cost t - β t := indicator_of_mem hioc _
  apply (mem_shiftedVelocityCostSet_iff _ _ _ _ _).mpr
  rw [hpath, hvel, hcost, sub_add_cancel]
  exact ⟨p.control t, hg hicc, rfl, le_rfl⟩

end FiniteRelaxedAdmissiblePair

/-- A bundled interval path has a continuous ambient representative on its
own closed interval, although its zero extension need not be globally continuous. -/
theorem continuousOn_intervalPathValue {a b : ℝ} (x : Icc a b →ᵇ E) :
    ContinuousOn (intervalPathValue x) (Icc a b) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : (Icc a b).domRestrict (intervalPathValue x) = (x : Icc a b → E) := by
    funext t
    exact intervalPathValue_of_mem x t t.property
  rw [heq]
  exact x.continuous

/-- The limiting time-state graph stays in the original compact set at *every*
time of the limiting interval, including its endpoints. Clamping a fixed time
to each source interval gives points converging to the actual limiting point. -/
theorem mem_compact_of_tendsto_extendedPaths
    {N : ℕ} {P : FiniteRelaxedBolzaData E U}
    (p : ℕ → FiniteRelaxedAdmissiblePair N P) (R : Set (ℝ × E)) (hR : IsCompact R)
    (hstate : ∀ n t, t ∈ Icc ((p n).startTime : ℝ) ((p n).endTime : ℝ) →
      (t, (p n).path t) ∈ R)
    (x : Icc P.a P.b →ᵇ E) (l r : Icc P.a P.b) (k : ℕ → ℕ)
    (hx : Tendsto (fun n ↦ (p (k n)).extendedPath) atTop (𝓝 x))
    (hl : Tendsto (fun n ↦ (p (k n)).startTime) atTop (𝓝 l))
    (hr : Tendsto (fun n ↦ (p (k n)).endTime) atTop (𝓝 r))
    (t : Icc P.a P.b) (ht : (t : ℝ) ∈ Icc (l : ℝ) (r : ℝ)) :
    ((t : ℝ), x t) ∈ R := by
  have hl' := (continuous_subtype_val.tendsto l).comp hl
  have hr' := (continuous_subtype_val.tendsto r).comp hr
  have hclamp : Tendsto
      (fun n ↦ clampTime (p (k n)).startTime (p (k n)).endTime t)
      atTop (𝓝 (t : ℝ)) := by
    convert hl'.max (hr'.min tendsto_const_nhds) using 1
    exact (clampTime_eq_self ht).symm
  apply hR.isClosed.mem_of_tendsto (hclamp.prodMk_nhds (hx.eval_const t))
  exact Eventually.of_forall fun n ↦ hstate (k n) _
    (clampTime_mem_Icc _ _ _ (p (k n)).time_lt.le)

end OptimalControl
