/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.FiniteRelaxedSourceSequence
public import DynamicalSystems.OptimalControl.ContinuousTime.FiniteRelaxedRelativeEpigraph
public import DynamicalSystems.OptimalControl.ContinuousTime.FiniteRelaxedConvexHull

/-!
# Relaxed existence from actual classical equi-AC minimizing pairs

The original admissible pairs supply the common-interval paths, L1 velocities,
shifted cost densities and their exact compensated objectives. Property (Q)
recovers the limiting epigraph. Relative-domain measurable selection uses the
original cost; the integrable lower bound is restored only after lower closure.
-/

@[expose] public section

open Set Filter MeasureTheory Topology
open DynamicalSystems.ClassicalEquiAC DynamicalSystems.MeasurableLift
open scoped ENNReal BoundedContinuousFunction BigOperators

namespace OptimalControl

variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SigmaCompactSpace E] [SecondCountableTopology E]
  [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [SigmaCompactSpace U]

/-- Actual classical equi-AC admissible source pairs and a convergent objective
produce an admissible limiting relaxed pair with no larger objective. The lower
bound is merely integrable and dynamics need only be continuous on their graph.
This assembles Steps 1--5 of BM Theorem 5.4.4 before the final minimum comparison. -/
theorem exists_admissibleRelaxedPair_objective_le
    (N : ℕ) (P : FiniteRelaxedBolzaData E U)
    (hC : IsClosed P.controlGraph) (hf : ContinuousOn P.dynamics P.controlGraph)
    (hc : LowerSemicontinuousOn P.runningCost P.controlGraph)
    (β : ℝ → ℝ) (hβ : IntegrableOn β (Icc P.a P.b))
    (hlower : ∀ z ∈ P.controlGraph, β z.1 ≤ P.runningCost z)
    (hB : IsClosed P.boundary) (hBtime : ∀ z ∈ P.boundary, z.1 < z.2.2.1)
    (hg : LowerSemicontinuousOn P.terminalCost P.boundary)
    (p : ℕ → FiniteRelaxedAdmissiblePair N P)
    (R : Set (ℝ × E)) (hR : IsCompact R) (hRD : R ⊆ P.stateDomain)
    (hstate : ∀ n t, t ∈ Icc ((p n).startTime : ℝ) ((p n).endTime : ℝ) →
      (t, (p n).path t) ∈ R)
    (hAC : EquiAbsolutelyContinuousOn (fun n ↦ (p n).path)
      (fun n ↦ ((p n).startTime : ℝ)) (fun n ↦ ((p n).endTime : ℝ)))
    (hcesari : ∀ z ∈ R, HasWeakCesariProperty (P.relaxedEpigraph N) z.1 z.2)
    (m : ℝ) (hobj : Tendsto (fun n ↦ (p n).objective) atTop (𝓝 m)) :
    ∃ q : FiniteRelaxedAdmissiblePair N P, q.objective ≤ m := by
  let g := compensatedTerminalCost P.a P.b β P.terminalCost
  have hshiftcesari : ∀ z ∈ R,
      HasWeakCesariProperty (shiftedVelocityCostSet (P.relaxedEpigraph N) β) z.1 z.2 :=
    fun z hz ↦ hasWeakCesariProperty_shiftedVelocityCostSet _ β _ _ (hcesari z hz)
  have hsource : Tendsto (fun n ↦
      g (((p n).startTime : ℝ), (p n).extendedPath (p n).startTime,
        ((p n).endTime : ℝ), (p n).extendedPath (p n).endTime) +
      ∫ t, (p n).shiftedCost β t ∂volume.restrict (Icc P.a P.b)) atTop (𝓝 m) := by
    simpa only [g, FiniteRelaxedAdmissiblePair.shifted_objective_eq _ hβ] using hobj
  obtain ⟨x, v, l, r, cost, k, hk, hx, _, hl, hr, hlr, hboundary,
    _, hlaw, _, _, hcost, hepi, hbound⟩ :=
    exists_limit_endpoints_objective_epigraph_of_unifIntegrable P.time_order
      (fun n ↦ (p n).extendedPath) (fun n ↦ (p n).extendedVelocityLp)
      (fun n ↦ (p n).startTime) (fun n ↦ (p n).endTime)
      (shiftedVelocityCostSet (P.relaxedEpigraph N) β)
      (fun n ↦ (p n).shiftedCost β) R hR
      (fun n t ht ↦ by rw [(p n).extendedPath_eq t ht]; exact hstate n t ht)
      (unifIntegrable_extendedVelocityLp_of_equiAC p hAC)
      (fun n ↦ (p n).extendedPath_intervalIntegral_law)
      (fun n ↦ (p n).extendedPath_left) (fun n ↦ (p n).extendedPath_right)
      P.boundary hB hBtime (fun n ↦ (p n).extended_boundary_mem)
      g (lowerSemicontinuousOn_compensatedTerminalCost hβ hg) hshiftcesari
      (fun n ↦ (p n).shifted_epigraph_mem β)
      (fun n ↦ (p n).shiftedCost_nonneg hlower)
      (fun n ↦ (p n).shiftedCost_integrable hβ) m hsource
  have hsubset : Icc (l : ℝ) (r : ℝ) ⊆ Icc P.a P.b := fun t ht ↦
    ⟨l.property.1.trans ht.1, ht.2.trans r.property.2⟩
  have hrestrict : (volume.restrict (Icc P.a P.b)).restrict (Icc (l : ℝ) (r : ℝ)) =
      volume.restrict (Icc (l : ℝ) (r : ℝ)) := by
    rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hsubset]
  have hv : Integrable (fun t ↦ v t) (volume.restrict (Icc (l : ℝ) (r : ℝ))) := by
    rw [← hrestrict]
    exact (memLp_one_iff_integrable.mp (Lp.memLp v)).restrict
  have hβlr := hβ.mono_set hsubset
  have hepiOriginal : ∀ᵐ t ∂volume.restrict (Icc (l : ℝ) (r : ℝ)),
      (v t, cost t + β t) ∈ P.relaxedEpigraph N t (intervalPathValue x t) :=
    hepi.mono fun t ht ↦ (mem_shiftedVelocityCostSet_iff _ β _ _ _).mp ht
  have hμ : volume.restrict (Icc (l : ℝ) (r : ℝ)) ≠ 0 := by
    intro hzero
    have h := Measure.restrict_eq_zero.mp hzero
    rw [Real.volume_Icc] at h
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hlr))) h
  obtain ⟨u, hu, hgraph, hvel, hvi, hci, hcbound⟩ :=
    exists_integrable_finiteRelaxedControl_of_integrable_lowerBound_of_continuousOn
      N P.controlGraph P.dynamics P.runningCost hC hf hc
      id (intervalPathValue x) v (fun t ↦ cost t + β t) measurable_id
      (measurable_intervalPathValue x) hv (hcost.add hβlr) β hβlr
      (Eventually.of_forall fun t u hu ↦ hlower _ hu) hμ hepiOriginal
  let q : FiniteRelaxedAdmissiblePair N P := {
    startTime := l
    endTime := r
    time_lt := hlr
    path := intervalPathValue x
    control := u
    measurable_control := hu
    continuous_path := (continuousOn_intervalPathValue x).mono hsubset
    state_mem := fun t ht ↦ hRD (by
      have htab := hsubset ht
      have h := mem_compact_of_tendsto_extendedPaths p R hR hstate x l r k
        hx hl hr ⟨t, htab⟩ ht
      simpa only [intervalPathValue_of_mem x t htab] using h)
    graph_mem := hgraph
    velocity_integrable := hvi
    cost_integrable := hci
    integral_law := by
      intro s hs t ht hst
      have hlt (z : ℝ) (hz : z ∈ Icc (l : ℝ) (r : ℝ)) :
          intervalPathValue x z - intervalPathValue x l =
            ∫ y in (l : ℝ)..z, v y ∂volume.restrict (Icc (l : ℝ) (r : ℝ)) := by
        rw [intervalPathValue_of_mem x z (hsubset hz),
          intervalPathValue_of_mem x l l.property,
          intervalIntegral.integral_of_le hz.1]
        exact hlaw ⟨z, hz⟩
      have heq : (∫ y in s..t, v y ∂volume.restrict (Icc (l : ℝ) (r : ℝ))) =
          ∫ y in s..t, finiteRelaxedVelocity N P.dynamics (y, intervalPathValue x y, u y) := by
        rw [intervalIntegral.integral_of_le hst, intervalIntegral.integral_of_le hst,
          Measure.restrict_restrict measurableSet_Ioc,
          inter_eq_left.mpr (show Ioc s t ⊆ Icc (l : ℝ) (r : ℝ) from
            fun z hz ↦ ⟨hs.1.trans hz.1.le, hz.2.trans ht.2⟩)]
        apply setIntegral_congr_ae measurableSet_Ioc
        have H := (ae_restrict_iff' measurableSet_Icc).mp hvel
        exact H.mono fun z hz hzt ↦ (hz ⟨hs.1.trans hzt.1.le, hzt.2.trans ht.2⟩).symm
      calc
        intervalPathValue x t - intervalPathValue x s =
            (intervalPathValue x t - intervalPathValue x l) -
              (intervalPathValue x s - intervalPathValue x l) := by abel
        _ = (∫ y in (l : ℝ)..t, v y ∂volume.restrict (Icc (l : ℝ) (r : ℝ))) -
            ∫ y in (l : ℝ)..s, v y ∂volume.restrict (Icc (l : ℝ) (r : ℝ)) := by
          rw [hlt t ht, hlt s hs]
        _ = ∫ y in s..t, v y ∂volume.restrict (Icc (l : ℝ) (r : ℝ)) :=
          intervalIntegral.integral_interval_sub_left hv.intervalIntegrable hv.intervalIntegrable
        _ = ∫ y in s..t,
            finiteRelaxedVelocity N P.dynamics (y, intervalPathValue x y, u y) := heq
        _ = _ := intervalIntegral.integral_of_le hst
    boundary_mem := by
      simpa only [intervalPathValue_of_mem x _ l.property,
        intervalPathValue_of_mem x _ r.property] using hboundary }
  refine ⟨q, ?_⟩
  have hrestore : P.terminalCost ((l : ℝ), x l, (r : ℝ), x r) +
      (∫ t, cost t + β t ∂volume.restrict (Icc (l : ℝ) (r : ℝ))) =
        g ((l : ℝ), x l, (r : ℝ), x r) +
          ∫ t, cost t ∂volume.restrict (Icc (l : ℝ) (r : ℝ)) := by
    rw [integral_add hcost hβlr]
    simp only [g, compensatedTerminalCost]
    rw [lowerCostPrimitive_sub l.property.1 r.property.2 hlr.le hβ]
    ring
  have hqbound : q.objective ≤ P.terminalCost ((l : ℝ), x l, (r : ℝ), x r) +
      ∫ t, cost t + β t ∂volume.restrict (Icc (l : ℝ) (r : ℝ)) := by
    simpa only [q, FiniteRelaxedAdmissiblePair.objective,
      FiniteRelaxedAdmissiblePair.endpointData, FiniteRelaxedAdmissiblePair.cost,
      intervalPathValue_of_mem x _ l.property, intervalPathValue_of_mem x _ r.property,
      id_eq] using add_le_add
        (le_refl (P.terminalCost ((l : ℝ), x l, (r : ℝ), x r))) hcbound
  exact hqbound.trans (hrestore.symm ▸ hbound)

/-- A source sequence approaches the infimum over actual admissible relaxed pairs.
This formulation does not presuppose a finite infimum or a limiting feasible pair. -/
def IsRelaxedMinimizingSequence (N : ℕ) (P : FiniteRelaxedBolzaData E U)
    (p : ℕ → FiniteRelaxedAdmissiblePair N P) : Prop :=
  ∀ q : FiniteRelaxedAdmissiblePair N P, ∀ ε : ℝ, 0 < ε →
    ∀ᶠ n in atTop, (p n).objective ≤ q.objective + ε

/-- BM Theorem 5.4.4: compact containment and classical equi-absolute continuity
of an actual minimizing sequence give an admissible relaxed minimizer. Weak
Cesari closure is used to recover the limit's velocity-cost epigraph, before
selection of a measurable control and restoration of the integrable cost shift. -/
theorem exists_relaxedMinimizer_of_weakCesariProperty
    (N : ℕ) (P : FiniteRelaxedBolzaData E U)
    (hC : IsClosed P.controlGraph) (hf : ContinuousOn P.dynamics P.controlGraph)
    (hc : LowerSemicontinuousOn P.runningCost P.controlGraph)
    (β : ℝ → ℝ) (hβ : IntegrableOn β (Icc P.a P.b))
    (hlower : ∀ z ∈ P.controlGraph, β z.1 ≤ P.runningCost z)
    (hB : IsClosed P.boundary) (hBtime : ∀ z ∈ P.boundary, z.1 < z.2.2.1)
    (hg : LowerSemicontinuousOn P.terminalCost P.boundary)
    (p : ℕ → FiniteRelaxedAdmissiblePair N P)
    (hmin : IsRelaxedMinimizingSequence N P p)
    (R : Set (ℝ × E)) (hR : IsCompact R) (hRD : R ⊆ P.stateDomain)
    (hstate : ∀ n t, t ∈ Icc ((p n).startTime : ℝ) ((p n).endTime : ℝ) →
      (t, (p n).path t) ∈ R)
    (hAC : EquiAbsolutelyContinuousOn (fun n ↦ (p n).path)
      (fun n ↦ ((p n).startTime : ℝ)) (fun n ↦ ((p n).endTime : ℝ)))
    (hcesari : ∀ z ∈ R, HasWeakCesariProperty (P.relaxedEpigraph N) z.1 z.2) :
    ∃ q : FiniteRelaxedAdmissiblePair N P,
      ∀ z : FiniteRelaxedAdmissiblePair N P, q.objective ≤ z.objective := by
  let K := Prod.snd '' R
  have hK : IsCompact K := hR.image continuous_snd
  let S := (Icc P.a P.b ×ˢ (K ×ˢ (Icc P.a P.b ×ˢ K))) ∩ P.boundary
  have hS : IsCompact S :=
    (isCompact_Icc.prod (hK.prod (isCompact_Icc.prod hK))).inter_right hB
  have hep (n : ℕ) : (p n).endpointData ∈ S := by
    refine ⟨⟨(p n).startTime.property, ?_, (p n).endTime.property, ?_⟩,
      (p n).boundary_mem⟩
    · exact ⟨(_, (p n).path (p n).startTime),
        hstate n _ ⟨le_rfl, (p n).time_lt.le⟩, rfl⟩
    · exact ⟨(_, (p n).path (p n).endTime),
        hstate n _ ⟨(p n).time_lt.le, le_rfl⟩, rfl⟩
  let g := compensatedTerminalCost P.a P.b β P.terminalCost
  obtain ⟨A, hA⟩ := (lowerSemicontinuousOn_compensatedTerminalCost hβ hg).mono
    (show S ⊆ P.boundary from inter_subset_right) |>.bddBelow_of_isCompact hS
  have hlow (n : ℕ) : A ≤ (p n).objective := by
    have hterminal : A ≤ g (p n).endpointData := hA ⟨_, hep n, rfl⟩
    have hnonneg := integral_nonneg_of_ae ((p n).shiftedCost_nonneg hlower)
    have hid := (p n).shifted_objective_eq hβ
    have hid' : g (p n).endpointData +
        ∫ t, (p n).shiftedCost β t ∂volume.restrict (Icc P.a P.b) =
          (p n).objective := by
      simpa only [g, FiniteRelaxedAdmissiblePair.endpointData,
        FiniteRelaxedAdmissiblePair.extendedPath_start,
        FiniteRelaxedAdmissiblePair.extendedPath_end] using hid
    exact (hterminal.trans (le_add_of_nonneg_right hnonneg)).trans_eq hid'
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hmin (p 0) 1 zero_lt_one)
  obtain ⟨m, _, k, hk, hlim⟩ := isCompact_Icc.tendsto_subseq
    (fun n ↦ show (p (n + n₀)).objective ∈ Icc A ((p 0).objective + 1) from
      ⟨hlow _, hn₀ _ (Nat.le_add_left _ _)⟩)
  let j : ℕ → ℕ := fun n ↦ k n + n₀
  have hj : StrictMono j := fun n m h ↦ Nat.add_lt_add_right (hk h) n₀
  have hobj : Tendsto (fun n ↦ (p (j n)).objective) atTop (𝓝 m) := hlim
  have hACj : EquiAbsolutelyContinuousOn (fun n ↦ (p (j n)).path)
      (fun n ↦ ((p (j n)).startTime : ℝ)) (fun n ↦ ((p (j n)).endTime : ℝ)) := by
    intro ε hε
    obtain ⟨δ, hδ, hmod⟩ := hAC ε hε
    exact ⟨δ, hδ, fun n ↦ hmod (j n)⟩
  obtain ⟨q, hq⟩ := exists_admissibleRelaxedPair_objective_le N P hC hf hc β hβ
    hlower hB hBtime hg (p ∘ j) R hR hRD (fun n ↦ hstate (j n)) hACj hcesari m hobj
  refine ⟨q, fun z ↦ hq.trans ?_⟩
  by_contra h
  have hε : 0 < (m - z.objective) / 2 := by linarith
  have hm := le_of_tendsto hobj
    (hj.tendsto_atTop.eventually (hmin z ((m - z.objective) / 2) hε))
  linarith

omit [CompleteSpace E] in
/-- Convexity of the ordinary epigraph recovers an ordinary control along an
actual relaxed pair, preserving the trajectory and lowering its objective.
The returned finite tuple repeats one ordinary atom, so its velocity and cost
are precisely the original ordinary dynamics and running cost. -/
theorem exists_ordinaryRelaxedPair_objective_le
    (N : ℕ) (P : FiniteRelaxedBolzaData E U)
    (hC : IsClosed P.controlGraph) (hf : ContinuousOn P.dynamics P.controlGraph)
    (hc : LowerSemicontinuousOn P.runningCost P.controlGraph)
    (β : ℝ → ℝ) (hβ : IntegrableOn β (Icc P.a P.b))
    (hlower : ∀ z ∈ P.controlGraph, β z.1 ≤ P.runningCost z)
    (hconvex : ∀ z ∈ P.stateDomain,
      Convex ℝ (constrainedVelocityCostSet P.controlGraph P.dynamics P.runningCost z.1 z.2))
    (p : FiniteRelaxedAdmissiblePair N P) :
    ∃ q : FiniteRelaxedAdmissiblePair N P, ∃ u : ℝ → U,
      Measurable u ∧ (∀ t i, (q.control t).2 i = u t) ∧
      (∀ t, q.velocity t = P.dynamics (t, q.path t, u t)) ∧
      (∀ t, q.cost t = P.runningCost (t, q.path t, u t)) ∧
      q.objective ≤ p.objective := by
  classical
  let I := Icc (p.startTime : ℝ) (p.endTime : ℝ)
  have hsubset : I ⊆ Icc P.a P.b := fun t ht ↦
    ⟨p.startTime.property.1.trans ht.1, ht.2.trans p.endTime.property.2⟩
  let x := intervalPathValue p.extendedPath
  have hx (t : ℝ) (ht : t ∈ I) : x t = p.path t := by
    change intervalPathValue p.extendedPath t = p.path t
    rw [intervalPathValue_of_mem _ t (hsubset ht)]
    exact p.extendedPath_eq _ ht
  have hμ : volume.restrict I ≠ 0 := by
    intro hz
    have h := Measure.restrict_eq_zero.mp hz
    rw [Real.volume_Icc] at h
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr p.time_lt))) h
  have hepi : ∀ᵐ t ∂volume.restrict I,
      (p.velocity t, p.cost t) ∈
        constrainedVelocityCostSet P.controlGraph P.dynamics P.runningCost t (x t) := by
    filter_upwards [p.graph_mem, ae_restrict_mem measurableSet_Icc] with t ht hti
    rw [hx t hti]
    apply finiteRelaxedVelocityCostSet_subset_of_convex N _ _ _ t (p.path t)
      (hconvex _ (p.state_mem t hti))
    exact ⟨p.control t, ht, rfl, le_rfl⟩
  obtain ⟨u, hu, hgraph, hvel, hvi, hci, hcost⟩ :=
    exists_integrable_control_of_constrained_epigraph_of_continuousOn
      P.controlGraph P.dynamics P.runningCost hC hf hc id x p.velocity p.cost
      measurable_id (measurable_intervalPathValue p.extendedPath)
      p.velocity_integrable p.cost_integrable β (hβ.mono_set hsubset)
      (Eventually.of_forall fun t u ht ↦ hlower _ ht) hμ hepi
  have : NeZero (volume.restrict I) := ⟨hμ⟩
  obtain ⟨t₀, ht₀⟩ := p.graph_mem.exists
  let w := (p.control t₀).1
  have hw : ∀ i, 0 ≤ w i := ht₀.1
  have hsum : (∑ i, w i) = 1 := ht₀.2.1
  let c : ℝ → FiniteRelaxedControl N U := fun t ↦ (w, fun _ ↦ u t)
  have hcv (t : ℝ) : finiteRelaxedVelocity N P.dynamics (t, p.path t, c t) =
      P.dynamics (t, p.path t, u t) := by
    simp only [finiteRelaxedVelocity, c, ← Finset.sum_smul, hsum, one_smul]
  have hcc (t : ℝ) : finiteRelaxedRunningCost N P.runningCost (t, p.path t, c t) =
      P.runningCost (t, p.path t, u t) := by
    simp only [finiteRelaxedRunningCost, c, ← Finset.sum_mul, hsum, one_mul]
  have hxp : (fun t ↦ x t) =ᵐ[volume.restrict I] p.path :=
    (ae_restrict_mem measurableSet_Icc).mono fun t ht ↦ hx t ht
  have hvp : (fun t ↦ P.dynamics (t, p.path t, u t)) =ᵐ[volume.restrict I] p.velocity := by
    filter_upwards [hvel, hxp] with t ht hxt
    simpa only [id_eq, hxt] using ht
  have hcip : IntegrableOn (fun t ↦ P.runningCost (t, p.path t, u t)) I := by
    apply hci.congr
    filter_upwards [hxp] with t ht
    simp only [id_eq, ht]
  let q : FiniteRelaxedAdmissiblePair N P := {
    startTime := p.startTime
    endTime := p.endTime
    time_lt := p.time_lt
    path := p.path
    control := c
    measurable_control := measurable_const.prodMk (Measurable.of_eval fun _ ↦ hu)
    continuous_path := p.continuous_path
    state_mem := p.state_mem
    graph_mem := by
      filter_upwards [hgraph, hxp] with t ht hxt
      exact ⟨hw, hsum, fun _ ↦ by simpa only [id_eq, hxt] using ht⟩
    velocity_integrable := p.velocity_integrable.congr
      (hvp.symm.trans (Eventually.of_forall fun t ↦ (hcv t).symm))
    cost_integrable := hcip.congr (Eventually.of_forall fun t ↦ (hcc t).symm)
    integral_law := by
      intro s hs t ht hst
      rw [p.integral_law s hs t ht hst]
      apply setIntegral_congr_ae measurableSet_Ioc
      have hv := (ae_restrict_iff' measurableSet_Icc).mp hvp
      filter_upwards [hv] with z hz hzt
      exact (hz ⟨hs.1.trans hzt.1.le, hzt.2.trans ht.2⟩).symm.trans (hcv z).symm
    boundary_mem := p.boundary_mem }
  refine ⟨q, u, hu, fun _ _ ↦ rfl, hcv, hcc, ?_⟩
  have hcq : (∫ t in I, q.cost t) =
      ∫ t in I, P.runningCost (id t, x t, u t) := by
    apply integral_congr_ae
    filter_upwards [hxp] with t ht
    change finiteRelaxedRunningCost N P.runningCost (t, p.path t, c t) = _
    rw [hcc t, ht]
    rfl
  change P.terminalCost p.endpointData + (∫ t in I, q.cost t) ≤ p.objective
  rw [hcq]
  exact add_le_add (le_refl _) hcost

/-- The convexity conclusion of BM Theorem 5.4.4: a measurable ordinary control
is optimal among all admissible relaxed pairs and hence among ordinary pairs.
The ordinary pair is represented by repeating its one atom in the finite tuple. -/
theorem exists_ordinaryMinimizer_of_weakCesariProperty_of_convex
    (N : ℕ) (P : FiniteRelaxedBolzaData E U)
    (hC : IsClosed P.controlGraph) (hf : ContinuousOn P.dynamics P.controlGraph)
    (hc : LowerSemicontinuousOn P.runningCost P.controlGraph)
    (β : ℝ → ℝ) (hβ : IntegrableOn β (Icc P.a P.b))
    (hlower : ∀ z ∈ P.controlGraph, β z.1 ≤ P.runningCost z)
    (hB : IsClosed P.boundary) (hBtime : ∀ z ∈ P.boundary, z.1 < z.2.2.1)
    (hg : LowerSemicontinuousOn P.terminalCost P.boundary)
    (p : ℕ → FiniteRelaxedAdmissiblePair N P)
    (hmin : IsRelaxedMinimizingSequence N P p)
    (R : Set (ℝ × E)) (hR : IsCompact R) (hRD : R ⊆ P.stateDomain)
    (hstate : ∀ n t, t ∈ Icc ((p n).startTime : ℝ) ((p n).endTime : ℝ) →
      (t, (p n).path t) ∈ R)
    (hAC : EquiAbsolutelyContinuousOn (fun n ↦ (p n).path)
      (fun n ↦ ((p n).startTime : ℝ)) (fun n ↦ ((p n).endTime : ℝ)))
    (hcesari : ∀ z ∈ R, HasWeakCesariProperty (P.relaxedEpigraph N) z.1 z.2)
    (hconvex : ∀ z ∈ P.stateDomain,
      Convex ℝ (constrainedVelocityCostSet P.controlGraph P.dynamics P.runningCost z.1 z.2)) :
    ∃ q : FiniteRelaxedAdmissiblePair N P, ∃ u : ℝ → U,
      Measurable u ∧ (∀ t i, (q.control t).2 i = u t) ∧
      (∀ t, q.velocity t = P.dynamics (t, q.path t, u t)) ∧
      (∀ t, q.cost t = P.runningCost (t, q.path t, u t)) ∧
      ∀ z : FiniteRelaxedAdmissiblePair N P, q.objective ≤ z.objective := by
  obtain ⟨p₀, hp₀⟩ := exists_relaxedMinimizer_of_weakCesariProperty N P hC hf hc β hβ
    hlower hB hBtime hg p hmin R hR hRD hstate hAC hcesari
  obtain ⟨q, u, hu, hatoms, hvel, hcost, hobj⟩ :=
    exists_ordinaryRelaxedPair_objective_le N P hC hf hc β hβ hlower hconvex p₀
  exact ⟨q, u, hu, hatoms, hvel, hcost, fun z ↦ hobj.trans (hp₀ z)⟩

end OptimalControl
