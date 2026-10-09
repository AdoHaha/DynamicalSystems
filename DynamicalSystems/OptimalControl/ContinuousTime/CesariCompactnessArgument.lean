/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.MeasureTheory.EquiIntegrableTrajectories
public import DynamicalSystems.Mathlib.MeasureTheory.MeasurableEpigraphLift
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

section ControlRealization

variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SigmaCompactSpace E] [SecondCountableTopology E]
  [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [SigmaCompactSpace U]
  {a b : ℝ}

omit [InnerProductSpace ℝ E] [CompleteSpace E] [SigmaCompactSpace E]
  [SecondCountableTopology E] in
/-- The interval trajectory extension is measurable. -/
theorem measurable_intervalPathValue (x : Icc a b →ᵇ E) :
    Measurable (intervalPathValue x) := by
  classical
  exact x.continuous.measurable.dite measurable_const measurableSet_Icc

/-- Compactness, Cesari lower closure, and noncompact measurable epigraph
realization construct an actual feasible limiting control and its cost bound.
The state-dependent graph is closed, dynamics continuous, and cost lower
semicontinuous and nonnegative on the graph. No recovery certificate is assumed.
This joins the fixed-interval analytic and selection steps of BM Theorem 5.4.4;
identification with finite-atomic relaxed controls and minimizer assembly are separate. -/
theorem exists_limit_control_of_unifIntegrable_constrained_epigraph
    (hab : a < b) (C : Set (ℝ × E × U)) (f : ℝ × E × U → E) (c : ℝ × E × U → ℝ)
    (hC : IsClosed C) (hf : Continuous f) (hc : LowerSemicontinuous c)
    (hnonneg : ∀ p ∈ C, 0 ≤ c p)
    (x : ℕ → Icc a b →ᵇ E) (w : ℕ → Lp E 1 (volume.restrict (Icc a b)))
    (cost : ℕ → ℝ → ℝ) (γ : ℝ)
    (K : Set E) (hK : IsCompact K) (hvalues : ∀ n t, x n t ∈ K)
    (hUI : UnifIntegrable (fun n t ↦ w n t) 1 (volume.restrict (Icc a b)))
    (hlaw : ∀ n (s t : Icc a b), x n t - x n s =
      ∫ r in (s : ℝ)..(t : ℝ), w n r ∂volume.restrict (Icc a b))
    (hcesari : ∀ t ∈ Icc a b, ∀ y ∈ K,
      HasWeakCesariProperty (DynamicalSystems.MeasurableLift.constrainedVelocityCostSet C f c) t y)
    (hw : ∀ n, ∀ᵐ t ∂volume.restrict (Icc a b), (w n t, cost n t) ∈
      DynamicalSystems.MeasurableLift.constrainedVelocityCostSet C f c t
        (intervalPathValue (x n) t))
    (hci : ∀ n, Integrable (cost n) (volume.restrict (Icc a b)))
    (hcost : Tendsto (fun n ↦ ∫ t, cost n t ∂volume.restrict (Icc a b)) atTop (𝓝 γ)) :
    ∃ (xlim : Icc a b →ᵇ E) (u : ℝ → U) (k : ℕ → ℕ),
      StrictMono k ∧ Tendsto (x ∘ k) atTop (𝓝 xlim) ∧ (∀ t, xlim t ∈ K) ∧
      Measurable u ∧ (∀ᵐ t ∂volume.restrict (Icc a b),
        (t, intervalPathValue xlim t, u t) ∈ C) ∧
      (∀ t : Icc a b, xlim t - xlim ⟨a, le_rfl, hab.le⟩ =
        ∫ r in Ioc a (t : ℝ), f (r, intervalPathValue xlim r, u r)
          ∂volume.restrict (Icc a b)) ∧
      Integrable (fun t ↦ f (t, intervalPathValue xlim t, u t))
        (volume.restrict (Icc a b)) ∧
      Integrable (fun t ↦ c (t, intervalPathValue xlim t, u t))
        (volume.restrict (Icc a b)) ∧
      (∫ t, c (t, intervalPathValue xlim t, u t) ∂volume.restrict (Icc a b)) ≤ γ := by
  have hnonnegseq : ∀ n, ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ cost n t := by
    intro n
    filter_upwards [hw n] with t ht
    obtain ⟨u, hu, _, hcu⟩ := ht
    exact (hnonneg _ hu).trans hcu
  obtain ⟨xlim, vlim, costLimit, k, hk, hlim, hvalueslim, hlawlim, hciLim, hepi, hbound⟩ :=
    exists_limit_trajectory_cost_epigraph_of_unifIntegrable hab.le x w
      (DynamicalSystems.MeasurableLift.constrainedVelocityCostSet C f c) cost γ
      K hK hvalues hUI hlaw hcesari hw hnonnegseq hci hcost
  let η := hciLim.aestronglyMeasurable.mk costLimit
  have hη : costLimit =ᵐ[volume.restrict (Icc a b)] η :=
    hciLim.aestronglyMeasurable.ae_eq_mk
  have hepiη : ∀ᵐ t ∂volume.restrict (Icc a b), (vlim t, η t) ∈
      DynamicalSystems.MeasurableLift.constrainedVelocityCostSet C f c t
        (intervalPathValue xlim t) := by
    filter_upwards [hepi, hη] with t ht hηt
    rwa [← hηt]
  have hμ : volume.restrict (Icc a b) ≠ 0 := by
    intro hzero
    have h := Measure.restrict_eq_zero.mp hzero
    rw [Real.volume_Icc] at h
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))) h
  obtain ⟨u, hu, hreal⟩ :=
    DynamicalSystems.MeasurableLift.exists_measurable_control_of_constrained_epigraph
      C f c hC hf (hc.lowerSemicontinuousOn C) id (intervalPathValue xlim) vlim η
      measurable_id (measurable_intervalPathValue xlim) (Lp.stronglyMeasurable vlim).measurable
      hciLim.aestronglyMeasurable.measurable_mk hμ hepiη
  have hrunmeas : Measurable (fun t ↦ c (t, intervalPathValue xlim t, u t)) :=
    hc.measurable.comp (measurable_id.prodMk ((measurable_intervalPathValue xlim).prodMk hu))
  have hrunint : Integrable (fun t ↦ c (t, intervalPathValue xlim t, u t))
      (volume.restrict (Icc a b)) := by
    apply (hciLim.congr hη).mono_nonneg hrunmeas.aestronglyMeasurable
    · exact hreal.mono fun t ht ↦ hnonneg _ ht.1
    · exact hreal.mono fun t ht ↦ ht.2.2
  refine ⟨xlim, u, k, hk, hlim, hvalueslim, hu, hreal.mono (fun _ ht ↦ ht.1),
    fun t ↦ ?_, (memLp_one_iff_integrable.mp (Lp.memLp vlim)).congr
      (hreal.mono fun _ ht ↦ ht.2.1.symm), hrunint, ?_⟩
  · rw [hlawlim]
    apply setIntegral_congr_ae measurableSet_Ioc
    exact hreal.mono fun r hr _ ↦ hr.2.1.symm
  · calc
      (∫ t, c (t, intervalPathValue xlim t, u t) ∂volume.restrict (Icc a b)) ≤
          ∫ t, η t ∂volume.restrict (Icc a b) :=
        integral_mono_ae hrunint (hciLim.congr hη) (hreal.mono fun t ht ↦ ht.2.2)
      _ = ∫ t, costLimit t ∂volume.restrict (Icc a b) := integral_congr_ae hη.symm
      _ ≤ γ := hbound

/-- A measurable control and its actual integral trajectory on a fixed interval,
with the state-dependent graph constraint and integrable velocity and cost. -/
def IsConstrainedIntegralPair (hab : a ≤ b) (C : Set (ℝ × E × U))
    (f : ℝ × E × U → E) (c : ℝ × E × U → ℝ) (x : Icc a b →ᵇ E) (u : ℝ → U) : Prop :=
  Measurable u ∧ (∀ᵐ t ∂volume.restrict (Icc a b), (t, intervalPathValue x t, u t) ∈ C) ∧
    Integrable (fun t ↦ f (t, intervalPathValue x t, u t)) (volume.restrict (Icc a b)) ∧
    (∀ t : Icc a b, x t - x ⟨a, le_rfl, hab⟩ =
      ∫ r in Ioc a (t : ℝ), f (r, intervalPathValue x r, u r)
        ∂volume.restrict (Icc a b)) ∧
    Integrable (fun t ↦ c (t, intervalPathValue x t, u t)) (volume.restrict (Icc a b))

/-- The actual costs of all admissible fixed-interval integral pairs. -/
def constrainedIntegralCostValues (hab : a ≤ b) (C : Set (ℝ × E × U))
    (f : ℝ × E × U → E) (c : ℝ × E × U → ℝ) : Set ℝ :=
  {r | ∃ (x : Icc a b →ᵇ E) (u : ℝ → U), IsConstrainedIntegralPair hab C f c x u ∧
    (∫ t, c (t, intervalPathValue x t, u t) ∂volume.restrict (Icc a b)) = r}

/-- A genuine minimizer for the fixed-interval constrained integral problem.
The minimizing sequence has compact state range and equi-integrable velocities;
Cesari lower closure and sigma-compact measurable realization construct the pair,
and nonnegative costs give the infimum comparison. No feasible recovery,
compactness of the admissible space, or optimality certificate is assumed.
This is a fixed-interval specialization of the BM Theorem 5.4.4 argument, without
terminal cost or the finite-atomic relaxed-control identification. -/
theorem exists_integralMinimizer_of_weakCesariProperty
    (hab : a < b) (C : Set (ℝ × E × U)) (f : ℝ × E × U → E) (c : ℝ × E × U → ℝ)
    (hC : IsClosed C) (hf : Continuous f) (hc : LowerSemicontinuous c)
    (hnonneg : ∀ p ∈ C, 0 ≤ c p)
    (x : ℕ → Icc a b →ᵇ E) (u : ℕ → ℝ → U)
    (hseq : ∀ n, IsConstrainedIntegralPair hab.le C f c (x n) (u n))
    (K : Set E) (hK : IsCompact K) (hvalues : ∀ n t, x n t ∈ K)
    (hUI : UnifIntegrable (fun n t ↦ f (t, intervalPathValue (x n) t, u n t)) 1
      (volume.restrict (Icc a b)))
    (hcesari : ∀ t ∈ Icc a b, ∀ y ∈ K,
      HasWeakCesariProperty (DynamicalSystems.MeasurableLift.constrainedVelocityCostSet C f c) t y)
    (hmin : Tendsto (fun n ↦ ∫ t, c (t, intervalPathValue (x n) t, u n t)
        ∂volume.restrict (Icc a b)) atTop
      (𝓝 (sInf (constrainedIntegralCostValues hab.le C f c)))) :
    ∃ (xlim : Icc a b →ᵇ E) (ulim : ℝ → U),
      IsConstrainedIntegralPair hab.le C f c xlim ulim ∧
      ∀ (y : Icc a b →ᵇ E) (v : ℝ → U), IsConstrainedIntegralPair hab.le C f c y v →
        (∫ t, c (t, intervalPathValue xlim t, ulim t) ∂volume.restrict (Icc a b)) ≤
          ∫ t, c (t, intervalPathValue y t, v t) ∂volume.restrict (Icc a b) := by
  let velocity n t := f (t, intervalPathValue (x n) t, u n t)
  have hvel : ∀ n, MemLp (velocity n) 1 (volume.restrict (Icc a b)) :=
    fun n ↦ memLp_one_iff_integrable.mpr (hseq n).2.2.1
  let w n := (hvel n).toLp (velocity n)
  have hweq : ∀ n, w n =ᵐ[volume.restrict (Icc a b)] velocity n :=
    fun n ↦ MemLp.coeFn_toLp (hvel n)
  have hUIw : UnifIntegrable (fun n t ↦ w n t) 1 (volume.restrict (Icc a b)) :=
    (unifIntegrable_congr_ae hweq).mpr hUI
  have hlaw : ∀ n (s t : Icc a b), x n t - x n s =
      ∫ r in (s : ℝ)..(t : ℝ), w n r ∂volume.restrict (Icc a b) := by
    intro n s t
    have hst := (hseq n).2.2.2.1 t
    have hss := (hseq n).2.2.2.1 s
    rw [← intervalIntegral.integral_of_le t.property.1] at hst
    rw [← intervalIntegral.integral_of_le s.property.1] at hss
    have hwlaw : ∀ t : Icc a b, (∫ r in a..(t : ℝ), w n r
        ∂volume.restrict (Icc a b)) =
        ∫ r in a..(t : ℝ), velocity n r ∂volume.restrict (Icc a b) :=
      fun t ↦ intervalIntegral.integral_congr_ae ((hweq n).mono fun r hr _ ↦ hr)
    have hi : ∀ r q : ℝ, IntervalIntegrable (w n) (volume.restrict (Icc a b)) r q :=
      fun r q ↦ (memLp_one_iff_integrable.mp (Lp.memLp (w n))).intervalIntegrable
    rw [← intervalIntegral.integral_interval_sub_left (hi a t) (hi a s), hwlaw t, hwlaw s]
    rw [← hst, ← hss]
    abel
  have hw : ∀ n, ∀ᵐ t ∂volume.restrict (Icc a b),
      (w n t, c (t, intervalPathValue (x n) t, u n t)) ∈
        DynamicalSystems.MeasurableLift.constrainedVelocityCostSet C f c t
          (intervalPathValue (x n) t) := by
    intro n
    filter_upwards [(hseq n).2.1, hweq n] with t ht hwt
    exact ⟨u n t, ht, hwt.symm, le_rfl⟩
  obtain ⟨xlim, ulim, _, _, _, _, hu, hgraph, hlawlim, hflim, hclim, hbound⟩ :=
    exists_limit_control_of_unifIntegrable_constrained_epigraph hab C f c hC hf hc hnonneg
      x w (fun n t ↦ c (t, intervalPathValue (x n) t, u n t))
      (sInf (constrainedIntegralCostValues hab.le C f c))
      K hK hvalues hUIw hlaw hcesari hw (fun n ↦ (hseq n).2.2.2.2) hmin
  have hbelow : BddBelow (constrainedIntegralCostValues hab.le C f c) := by
    refine ⟨0, ?_⟩
    rintro r ⟨y, v, hv, rfl⟩
    exact integral_nonneg_of_ae (hv.2.1.mono fun t ht ↦ hnonneg _ ht)
  refine ⟨xlim, ulim, ⟨hu, hgraph, hflim, hlawlim, hclim⟩, fun y v hv ↦ ?_⟩
  exact hbound.trans (csInf_le hbelow ⟨y, v, hv, rfl⟩)

end ControlRealization

end OptimalControl
