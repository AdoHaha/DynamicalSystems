/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.MeasureTheory.MeasurableSigmaCompactLift
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Measurable realization of constrained velocity–cost epigraphs

A closed state-dependent control graph and a lower semicontinuous running cost
form a closed epigraph in a sigma-compact space. The existing sigma-compact lift
then realizes a measurable feasible velocity–cost pair. Feasibility holds almost
everywhere, and no inverse or compact control space is supplied.

This is the selection mechanism in BM Theorem 5.4.4, Step 4. Specializing the
control space to finite relaxed combinations still requires a separate bridge.
-/

@[expose] public section

open Set MeasureTheory Topology

namespace DynamicalSystems.MeasurableLift

/-- An almost everywhere version of sigma-compact measurable lifting. The range
is measurable because it is a countable union of compact images. -/
theorem exists_measurable_ae_lift_of_continuous_sigmaCompact
    {A S Y : Type*} [MeasurableSpace A] {μ : Measure A}
    [MetricSpace S] [MeasurableSpace S] [BorelSpace S] [SigmaCompactSpace S] [Nonempty S]
    [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
    (Φ : S → Y) (Γ : A → Y) (hΦ : Continuous Φ) (hΓ : Measurable Γ)
    (hrange : ∀ᵐ t ∂μ, Γ t ∈ range Φ) :
    ∃ s : A → S, Measurable s ∧ ∀ᵐ t ∂μ, Φ (s t) = Γ t := by
  classical
  obtain ⟨K, hK, hcover⟩ := isSigmaCompact_range hΦ
  have hmeas : MeasurableSet (range Φ) := by
    rw [← hcover]
    exact MeasurableSet.iUnion fun n ↦ (hK n).measurableSet
  let good : Set A := Γ ⁻¹' range Φ
  have hgood : MeasurableSet good := hmeas.preimage hΓ
  obtain ⟨s, hs, hslift⟩ := exists_measurable_lift_of_continuous_sigmaCompact
    Φ (fun t : good ↦ Γ t) hΦ (hΓ.comp measurable_subtype_coe) (fun t ↦ t.property)
  let s₀ : S := Classical.choice inferInstance
  let r (t : A) : S := if ht : t ∈ good then s ⟨t, ht⟩ else s₀
  refine ⟨r, hs.dite measurable_const hgood, ?_⟩
  filter_upwards [hrange] with t ht
  have htgood : t ∈ good := ht
  simpa only [r, dite_eq_left htgood] using hslift ⟨t, htgood⟩

section ConstrainedEpigraph

variable {A T E U : Type*} [MeasurableSpace A] {μ : Measure A}
  [MetricSpace T] [MeasurableSpace T] [BorelSpace T]
  [SigmaCompactSpace T] [SecondCountableTopology T]
  [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SigmaCompactSpace E] [SecondCountableTopology E]
  [MetricSpace U] [MeasurableSpace U] [BorelSpace U] [SigmaCompactSpace U]

/-- The velocity–cost epigraph constrained by the actual time/state/control graph. -/
def constrainedVelocityCostSet (C : Set (T × E × U))
    (f : T × E × U → E) (c : T × E × U → ℝ) (t : T) (x : E) : Set (E × ℝ) :=
  {p | ∃ u, (t, x, u) ∈ C ∧ f (t, x, u) = p.1 ∧ c (t, x, u) ≤ p.2}

/-- Closed control graph and lower semicontinuous cost construct measurable
controls realizing an a.e. feasible velocity–cost epigraph. Sigma-compactness is
used for selection, not compactness of the whole control set.
This is the noncompact epigraph realization argument in BM Theorem 5.4.4, Step 4. -/
theorem exists_measurable_control_of_constrained_epigraph
    (C : Set (T × E × U)) (f : T × E × U → E) (c : T × E × U → ℝ)
    (hC : IsClosed C) (hf : Continuous f) (hc : LowerSemicontinuousOn c C)
    (τ : A → T) (x v : A → E) (costLimit : A → ℝ)
    (hτ : Measurable τ) (hx : Measurable x) (hv : Measurable v) (hcostLimit : Measurable costLimit)
    (hμ : μ ≠ 0)
    (hepi : ∀ᵐ t ∂μ, (v t, costLimit t) ∈ constrainedVelocityCostSet C f c (τ t) (x t)) :
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
  have hΦ : Continuous Φ := by
    exact ((continuous_fst.fst.prodMk continuous_fst.snd.fst).prodMk
      ((hf.comp continuous_fst).prodMk continuous_snd)).comp continuous_subtype_val
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

end ConstrainedEpigraph

end DynamicalSystems.MeasurableLift
