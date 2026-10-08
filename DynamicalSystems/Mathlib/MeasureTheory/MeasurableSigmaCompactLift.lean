/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.MeasureTheory.MeasurableArgmin
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Measurable lifts through continuous maps on sigma-compact metric spaces

A measurable map into the range of a continuous map from a sigma-compact metric
space has a measurable lift. Compact exhaustion reduces the selection to the
existing compact measurable argmin theorem, applied to distance from the target.
The first compact set whose image contains the target is a measurable index.

This is the measurable realization mechanism used in Berkovitz & Medhin,
Theorem 5.4.4, Step 4 (via their Theorem 3.4.1).
-/

@[expose] public section

open Set MeasureTheory

namespace DynamicalSystems.MeasurableLift

variable {T S Y : Type*} [MeasurableSpace T]
  [MetricSpace S] [MeasurableSpace S] [BorelSpace S] [SigmaCompactSpace S] [Nonempty S]
  [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]

/-- Measurable realization through a continuous map with sigma-compact metric
domain. No compactness of the entire domain and no preselected inverse are assumed. -/
theorem exists_measurable_lift_of_continuous_sigmaCompact
    (Φ : S → Y) (Γ : T → Y) (hΦ : Continuous Φ) (hΓ : Measurable Γ)
    (hrange : ∀ t, Γ t ∈ range Φ) :
    ∃ s : T → S, Measurable s ∧ ∀ t, Φ (s t) = Γ t := by
  classical
  let z₀ : S := Classical.choice inferInstance
  let K n := compactCovering S n ∪ {z₀}
  have hK : ∀ n, IsCompact (K n) := fun n ↦
    (isCompact_compactCovering S n).union isCompact_singleton
  have hselector : ∀ n, ∃ s : T → S, Measurable s ∧
      ∀ t, Γ t ∈ Φ '' K n → Φ (s t) = Γ t := by
    intro n
    have : Nonempty (K n) := ⟨⟨z₀, Or.inr (mem_singleton z₀)⟩⟩
    have : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
    obtain ⟨s, hs, hmin⟩ := MeasurableArgmin.exists_measurable_isMinOn
      (φ := fun t (u : K n) ↦ dist (Φ u) (Γ t))
      (fun _ ↦ measurable_const.dist hΓ)
      (fun _ ↦ (hΦ.comp continuous_subtype_val).dist continuous_const)
    refine ⟨fun t ↦ (s t : S), measurable_subtype_coe.comp hs, ?_⟩
    intro t ht
    obtain ⟨u, hu, heq⟩ := ht
    have h := hmin t ⟨u, hu⟩
    rw [heq, dist_self] at h
    exact dist_eq_zero.mp (le_antisymm h dist_nonneg)
  choose s hs hslift using hselector
  have hexists : ∀ t, ∃ n, Γ t ∈ Φ '' K n := by
    intro t
    obtain ⟨u, hu⟩ := hrange t
    obtain ⟨n, hn⟩ := exists_mem_compactCovering u
    exact ⟨n, u, Or.inl hn, hu⟩
  let idx t := Nat.find (hexists t)
  have hidx : Measurable idx := measurable_find hexists fun n ↦
    ((hK n).image hΦ).isClosed.measurableSet.preimage hΓ
  have hprod : Measurable (fun p : ℕ × T ↦ s p.1 p.2) :=
    measurable_from_prod_countable_right hs
  exact ⟨fun t ↦ s (idx t) t, hprod.comp (hidx.prodMk measurable_id),
    fun t ↦ hslift (idx t) t (Nat.find_spec (hexists t))⟩

end DynamicalSystems.MeasurableLift
