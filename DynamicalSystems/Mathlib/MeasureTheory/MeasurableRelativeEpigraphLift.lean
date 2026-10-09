/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.MeasureTheory.MeasurableEpigraphLift

/-!
# Measurable epigraph realization with relative continuity

Only the values of the dynamics on the original admissible control graph enter
selection. Continuity on that graph is sufficient: the map from the closed
cost epigraph is continuous on its subtype. No extension of the dynamics to a
continuous function on the whole ambient vector space is required.

This supplies the relative-domain selection bridge in Berkovitz--Medhin,
Theorem 5.4.4, Step 4. The state remains in its ambient vector space; it is not
replaced by a closed subtype with unjustified vector-space instances.
-/

@[expose] public section

open Set MeasureTheory Topology

namespace DynamicalSystems.MeasurableLift

variable {A T E U : Type*} [MeasurableSpace A] {μ : Measure A}
  [MetricSpace T] [MeasurableSpace T] [BorelSpace T]
  [SigmaCompactSpace T] [SecondCountableTopology T]
  [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SigmaCompactSpace E] [SecondCountableTopology E]
  [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [SigmaCompactSpace U]

/-- A closed control graph, relatively continuous dynamics and relatively lower
semicontinuous cost admit a measurable realization of an almost everywhere
feasible velocity--cost pair. No global continuous extension is assumed. -/
theorem exists_measurable_control_of_constrained_epigraph_of_continuousOn
    (C : Set (T × E × U)) (f : T × E × U → E) (c : T × E × U → ℝ)
    (hC : IsClosed C) (hf : ContinuousOn f C) (hc : LowerSemicontinuousOn c C)
    (τ : A → T) (x v : A → E) (costLimit : A → ℝ)
    (hτ : Measurable τ) (hx : Measurable x) (hv : Measurable v)
    (hcostLimit : Measurable costLimit) (hμ : μ ≠ 0)
    (hepi : ∀ᵐ t ∂μ, (v t, costLimit t) ∈
      constrainedVelocityCostSet C f c (τ t) (x t)) :
    ∃ u : A → U, Measurable u ∧
      ∀ᵐ t ∂μ, (τ t, x t, u t) ∈ C ∧
        f (τ t, x t, u t) = v t ∧ c (τ t, x t, u t) ≤ costLimit t := by
  classical
  let S : Set ((T × E × U) × ℝ) := {p | p.1 ∈ C ∧ c p.1 ≤ p.2}
  have hS : IsClosed S := (lowerSemicontinuousOn_iff_isClosed_epigraph hC).mp hc
  let : SigmaCompactSpace S := hS.sigmaCompactSpace
  let Φ (p : S) : (T × E) × E × ℝ :=
    ((p.val.1.1, p.val.1.2.1), f p.val.1, p.val.2)
  let Γ (t : A) : (T × E) × E × ℝ := ((τ t, x t), v t, costLimit t)
  have hfS : Continuous (fun p : S ↦ f p.val.1) :=
    hf.comp_continuous (continuous_fst.comp continuous_subtype_val)
      (fun p ↦ p.property.1)
  have hΦ : Continuous Φ := by
    exact ((continuous_fst.fst.comp continuous_subtype_val).prodMk
      (continuous_fst.snd.fst.comp continuous_subtype_val)).prodMk
      (hfS.prodMk (continuous_snd.comp continuous_subtype_val))
  have hΓ : Measurable Γ := (hτ.prodMk hx).prodMk (hv.prodMk hcostLimit)
  have hrange : ∀ᵐ t ∂μ, Γ t ∈ range Φ := by
    filter_upwards [hepi] with t ht
    obtain ⟨u, hu, hfu, hcu⟩ := ht
    exact ⟨⟨((τ t, x t, u), costLimit t), hu, hcu⟩, by simp [Φ, Γ, hfu]⟩
  let : NeZero μ := ⟨hμ⟩
  obtain ⟨t, ht⟩ := hrange.exists
  obtain ⟨p, _⟩ := ht
  let : Nonempty S := ⟨p⟩
  obtain ⟨s, hs, hslift⟩ :=
    exists_measurable_ae_lift_of_continuous_sigmaCompact Φ Γ hΦ hΓ hrange
  refine ⟨fun t ↦ (s t).val.1.2.2,
    measurable_snd.comp (measurable_snd.comp (measurable_fst.comp
      (measurable_subtype_coe.comp hs))), ?_⟩
  filter_upwards [hslift] with t ht
  have htime := congrArg (fun p : (T × E) × E × ℝ ↦ p.1.1) ht
  have hstate := congrArg (fun p : (T × E) × E × ℝ ↦ p.1.2) ht
  have hvel := congrArg (fun p : (T × E) × E × ℝ ↦ p.2.1) ht
  have hcost := congrArg (fun p : (T × E) × E × ℝ ↦ p.2.2) ht
  change (s t).val.1.1 = τ t at htime
  change (s t).val.1.2.1 = x t at hstate
  change f (s t).val.1 = v t at hvel
  change (s t).val.2 = costLimit t at hcost
  have heq : (s t).val.1 = (τ t, x t, (s t).val.1.2.2) := by
    ext <;> simp [htime, hstate]
  refine ⟨?_, ?_, ?_⟩
  · exact heq ▸ (s t).property.1
  · exact (congrArg f heq).symm.trans hvel
  · exact (congrArg c heq).symm.trans_le ((s t).property.2.trans_eq hcost)

end DynamicalSystems.MeasurableLift
