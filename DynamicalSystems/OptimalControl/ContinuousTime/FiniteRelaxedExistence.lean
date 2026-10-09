/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.CesariMovingInterval
public import DynamicalSystems.OptimalControl.ContinuousTime.FiniteRelaxedEpigraph

/-!
# Moving-interval finite relaxed control realization

The moving-endpoint Cesari limit is realized as measurable simplex weights and
admissible atoms with actual weighted integral dynamics and integrable running
cost. The full terminal-plus-running objective bound is preserved.

This joins the analytic Steps 1–3 and the concrete Step 4 of BM Theorem 5.4.4
for nonnegative running costs. Converting the book's equi-AC source assumption,
constructing extensions from source pairs, and the general integrable cost shift
remain separate bridges to the full book headline.
-/

@[expose] public section

open Set Filter MeasureTheory Topology
open scoped ENNReal BoundedContinuousFunction

namespace OptimalControl

variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SigmaCompactSpace E] [SecondCountableTopology E]
  [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [SigmaCompactSpace U]
  {a b : ℝ}

/-- Moving-endpoint compactness and property (Q), followed by concrete finite
relaxed realization, give actual weighted integral dynamics and a full objective
bound. No measurable recovery, supplied weak limit, or limiting integrability
certificate is assumed. The number of atoms is explicit (BM uses dimension + 2). -/
theorem exists_limit_finiteRelaxedControl_of_unifIntegrable
    (N : ℕ) (hab : a ≤ b) (C : Set (ℝ × E × U))
    (f : ℝ × E × U → E) (c : ℝ × E × U → ℝ)
    (hC : IsClosed C) (hf : Continuous f) (hc : LowerSemicontinuousOn c C)
    (hnonneg : ∀ p ∈ C, 0 ≤ c p)
    (x : ℕ → Icc a b →ᵇ E) (w : ℕ → Lp E 1 (volume.restrict (Icc a b)))
    (l r : ℕ → Icc a b) (cost : ℕ → ℝ → ℝ)
    (R : Set (ℝ × E)) (hR : IsCompact R)
    (hstate : ∀ n (t : Icc a b), (t : ℝ) ∈ Icc (l n : ℝ) (r n : ℝ) → ((t : ℝ), x n t) ∈ R)
    (hUI : UnifIntegrable (fun n t ↦ w n t) 1 (volume.restrict (Icc a b)))
    (hlaw : ∀ n (s t : Icc a b), x n t - x n s =
      ∫ z in (s : ℝ)..(t : ℝ), w n z ∂volume.restrict (Icc a b))
    (hleft : ∀ n (t : Icc a b), (t : ℝ) ≤ l n → x n t = x n (l n))
    (hright : ∀ n (t : Icc a b), (r n : ℝ) ≤ t → x n t = x n (r n))
    (B : Set (ℝ × E × ℝ × E)) (hB : IsClosed B)
    (hBtime : ∀ p ∈ B, p.1 < p.2.2.1)
    (hboundary : ∀ n, ((l n : ℝ), x n (l n), (r n : ℝ), x n (r n)) ∈ B)
    (g : ℝ × E × ℝ × E → ℝ) (hg : LowerSemicontinuousOn g B)
    (hcesari : ∀ p ∈ R, HasWeakCesariProperty
      (DynamicalSystems.MeasurableLift.constrainedVelocityCostSet
        (finiteRelaxedControlGraph N C) (finiteRelaxedVelocity N f)
        (finiteRelaxedRunningCost N c)) p.1 p.2)
    (hw : ∀ n, ∀ᵐ t ∂volume.restrict (Icc a b), t ∈ Ioo (l n : ℝ) (r n : ℝ) →
      (w n t, cost n t) ∈ DynamicalSystems.MeasurableLift.constrainedVelocityCostSet
        (finiteRelaxedControlGraph N C) (finiteRelaxedVelocity N f)
        (finiteRelaxedRunningCost N c) t (intervalPathValue (x n) t))
    (hcostnonneg : ∀ n, ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ cost n t)
    (hci : ∀ n, Integrable (cost n) (volume.restrict (Icc a b)))
    (m : ℝ) (hcost : Tendsto (fun n ↦
      g ((l n : ℝ), x n (l n), (r n : ℝ), x n (r n)) +
        ∫ t, cost n t ∂volume.restrict (Icc a b)) atTop (𝓝 m)) :
    ∃ (xlim : Icc a b →ᵇ E) (u : ℝ → FiniteRelaxedControl N U)
      (l₀ r₀ : Icc a b) (k : ℕ → ℕ), StrictMono k ∧
      Tendsto (x ∘ k) atTop (𝓝 xlim) ∧ (∀ t, xlim t ∈ Prod.snd '' R) ∧
      Tendsto (l ∘ k) atTop (𝓝 l₀) ∧ Tendsto (r ∘ k) atTop (𝓝 r₀) ∧
      (l₀ : ℝ) < r₀ ∧ ((l₀ : ℝ), xlim l₀, (r₀ : ℝ), xlim r₀) ∈ B ∧
      (∀ t : Icc a b, (t : ℝ) ≤ l₀ → xlim t = xlim l₀) ∧
      (∀ t : Icc a b, (r₀ : ℝ) ≤ t → xlim t = xlim r₀) ∧
      Measurable u ∧
      (∀ᵐ t ∂volume.restrict (Icc (l₀ : ℝ) (r₀ : ℝ)),
        (t, intervalPathValue xlim t, u t) ∈ finiteRelaxedControlGraph N C) ∧
      (∀ t : Icc (l₀ : ℝ) (r₀ : ℝ),
        xlim ⟨t, l₀.property.1.trans t.property.1, t.property.2.trans r₀.property.2⟩ - xlim l₀ =
          ∫ z in Ioc (l₀ : ℝ) (t : ℝ),
            finiteRelaxedVelocity N f (z, intervalPathValue xlim z, u z)
              ∂volume.restrict (Icc (l₀ : ℝ) (r₀ : ℝ))) ∧
      Integrable (fun t ↦ finiteRelaxedVelocity N f (t, intervalPathValue xlim t, u t))
        (volume.restrict (Icc (l₀ : ℝ) (r₀ : ℝ))) ∧
      Integrable (fun t ↦ finiteRelaxedRunningCost N c (t, intervalPathValue xlim t, u t))
        (volume.restrict (Icc (l₀ : ℝ) (r₀ : ℝ))) ∧
      g ((l₀ : ℝ), xlim l₀, (r₀ : ℝ), xlim r₀) +
        (∫ t, finiteRelaxedRunningCost N c (t, intervalPathValue xlim t, u t)
          ∂volume.restrict (Icc (l₀ : ℝ) (r₀ : ℝ))) ≤ m := by
  obtain ⟨xlim, v, l₀, r₀, costLimit, k, hk, hx, hvalues, hl, hr, hlr, hboundarylim,
    _, hlawlim, hleftlim, hrightlim, hlimitint, hepi, hbound⟩ :=
    exists_limit_endpoints_objective_epigraph_of_unifIntegrable hab x w l r
      (DynamicalSystems.MeasurableLift.constrainedVelocityCostSet
        (finiteRelaxedControlGraph N C) (finiteRelaxedVelocity N f)
        (finiteRelaxedRunningCost N c)) cost R hR hstate hUI hlaw hleft hright
      B hB hBtime hboundary g hg hcesari hw hcostnonneg hci m hcost
  have hsubset : Icc (l₀ : ℝ) (r₀ : ℝ) ⊆ Icc a b := fun t ht ↦
    ⟨l₀.property.1.trans ht.1, ht.2.trans r₀.property.2⟩
  have hrestrict : (volume.restrict (Icc a b)).restrict (Icc (l₀ : ℝ) (r₀ : ℝ)) =
      volume.restrict (Icc (l₀ : ℝ) (r₀ : ℝ)) := by
    rw [Measure.restrict_restrict measurableSet_Icc, inter_eq_left.mpr hsubset]
  have hv : Integrable (fun t ↦ v t) (volume.restrict (Icc (l₀ : ℝ) (r₀ : ℝ))) := by
    rw [← hrestrict]
    exact (memLp_one_iff_integrable.mp (Lp.memLp v)).restrict
  have hμ : volume.restrict (Icc (l₀ : ℝ) (r₀ : ℝ)) ≠ 0 := by
    intro hzero
    have h := Measure.restrict_eq_zero.mp hzero
    rw [Real.volume_Icc] at h
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hlr))) h
  obtain ⟨u, hu, hgraph, hvel, hvelint, hrunint, hrunbound⟩ :=
    exists_integrable_finiteRelaxedControl_of_epigraph N C f c hC hf hc hnonneg
      id (intervalPathValue xlim) v costLimit measurable_id
      (measurable_intervalPathValue xlim) hv hlimitint hμ hepi
  refine ⟨xlim, u, l₀, r₀, k, hk, hx, hvalues, hl, hr, hlr, hboundarylim,
    hleftlim, hrightlim, hu, hgraph, ?_, hvelint, hrunint,
    (add_le_add (le_refl _) hrunbound).trans hbound⟩
  intro t
  rw [hlawlim]
  apply setIntegral_congr_ae measurableSet_Ioc
  exact hvel.mono fun z hz _ ↦ hz.symm

end OptimalControl
