/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Stability.Definitions
public import DynamicalSystems.Stability.LaSalle

/-! # Sublevel-set region of attraction

This file is slice L4 of the formalization of J. Kabziński and P. Mosiołek,
*Projektowanie nieliniowych układów sterowania*, Komitet Automatyki i Robotyki PAN,
Monografie tom 22. It records Theorem 2.4 (Chapter 2), which bounds a region of
attraction by a sublevel set of a Lyapunov function.

The statement concerns an autonomous flow `Φ`, a continuous function `v : E → ℝ` and a
level `c`. If the sublevel set `{x | v x ≤ c}` is compact and positively invariant under
`Φ`, and `v` is a local Lyapunov function on that set whose derivative along the flow is
strictly negative away from the equilibrium `x₀`, then every point of the sublevel set
belongs to the region of attraction of `x₀`. Compactness supplies the non-empty limit set
used by LaSalle's invariance principle, while positive invariance guarantees that
trajectories starting in the sublevel set never leave it. This bridges the filter-level
convergence theorems of `DynamicalSystems.Stability.LaSalle` to the set-theoretic basin of
attraction `regionOfAttraction` of `DynamicalSystems.Stability.Definitions`.

## Main statements

* `sublevelSet_subset_regionOfAttraction`
-/

@[expose] public section

open Filter Set

variable {E : Type*} [NormedAddCommGroup E]

/-- **Sublevel-set region of attraction (Kabziński & Mosiołek Theorem 2.4).**
If a sublevel set `{x | v x ≤ c}` is compact and positively invariant under the
bundled autonomous flow `Phi`, and `v` is a local Lyapunov function on `{x | v x ≤ c}`
whose derivative along the flow is strictly negative away from the equilibrium `x0`,
then the sublevel set is contained in the region of attraction of `x0`. -/
theorem sublevelSet_subset_regionOfAttraction
    {Φ : Flow ℝ E} {v : E → ℝ} {c : ℝ} {x₀ : E}
    (hs : IsCompact {x | v x ≤ c})
    (hinv : {x | v x ≤ c}.IsInvariantOn Φ (Set.Ici 0))
    (h_lya : IsLyapunovOn v Φ {x | v x ≤ c})
    {f' : E → ℝ} (hf' : ∀ x ∈ {x | v x ≤ c}, HasDerivAt (v <| Φ · x) (f' x) 0)
    (hneg : ∀ x ∈ {x | v x ≤ c}, x ≠ x₀ → f' x < 0) :
    {x | v x ≤ c} ⊆ regionOfAttraction Φ x₀ := by
  intro y hy
  rw [mem_regionOfAttraction_iff]
  refine IsLyapunovOn.tendsto_nhds_of_hasDerivAt_neg hs h_lya ?_ hf' hneg
  rw [Filter.eventually_atTop]
  exact ⟨0, fun t ht ↦ hinv ht hy⟩
