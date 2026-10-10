/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.MeasureTheory.MovingIntervalCompactness

/-!
# Closed time-state constraints under moving-interval convergence

Clamped evaluation preserves the original time-state set, including the
limiting endpoints. Membership in the state projection is not substituted
for membership in the original time-state set.
-/

@[expose] public section

open Set Filter Topology
open scoped BoundedContinuousFunction

namespace DynamicalSystems.EquiIntegrableTrajectories

variable {E : Type*} [MetricSpace E] {a b : ℝ}

/-- Closed time-state constraints pass to every time in the limiting active
interval. Clamping handles endpoints without assuming that they eventually
belong to every source interval. -/
theorem mem_closed_timeStateSet_of_uniform_tendsto_endpoints
    (x : ℕ → Icc a b →ᵇ E) (xlim : Icc a b →ᵇ E)
    (l r : ℕ → Icc a b) (l₀ r₀ : Icc a b)
    (hx : Tendsto x atTop (𝓝 xlim))
    (hl : Tendsto l atTop (𝓝 l₀))
    (hr : Tendsto r atTop (𝓝 r₀))
    (hordered : ∀ n, (l n : ℝ) ≤ r n)
    (R : Set (ℝ × E)) (hR : IsClosed R)
    (hstate : ∀ n (t : Icc a b),
      (t : ℝ) ∈ Icc (l n : ℝ) (r n : ℝ) →
        ((t : ℝ), x n t) ∈ R) :
    ∀ t : Icc a b,
      (t : ℝ) ∈ Icc (l₀ : ℝ) (r₀ : ℝ) →
        ((t : ℝ), xlim t) ∈ R := by
  intro t ht
  let τ : ℕ → Icc a b := fun n ↦ max (l n) (min (r n) t)
  have hlt : l₀ ≤ t := ht.1
  have htr : t ≤ r₀ := ht.2
  have htconst : Tendsto (fun _ : ℕ ↦ t) atTop (𝓝 t) :=
    tendsto_const_nhds
  have hτ : Tendsto τ atTop (𝓝 t) := by
    simpa only [min_eq_right htr, max_eq_right hlt] using
      hl.max (hr.min htconst)
  have hτmem (n : ℕ) :
      ((τ n : Icc a b) : ℝ) ∈ Icc (l n : ℝ) (r n : ℝ) := by
    change l n ≤ τ n ∧ τ n ≤ r n
    exact ⟨le_max_left _ _,
      max_le (hordered n) (min_le_left _ _)⟩
  apply hR.mem_of_tendsto
    (((continuous_subtype_val.tendsto t).comp hτ).prodMk_nhds
      (hx.eval hτ))
  exact Eventually.of_forall fun n ↦ hstate n (τ n) (hτmem n)

end DynamicalSystems.EquiIntegrableTrajectories
