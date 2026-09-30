/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Basic.NonAutonomous
public import DynamicalSystems.Stability.Basic
public import DynamicalSystems.Stability.Equilibrium

/-! # Stability definitions and the region of attraction

This file records the Chapter 1 stability vocabulary of Kabziński and Mosiołek,
*Projektowanie nieliniowych układów sterowania*, together with the region of
attraction and its immediate interface lemmas.

## Main definitions

* `IsLyapunovStable`: Lyapunov stability of an equilibrium of an autonomous flow.
* `IsUnstable`: the negation of Lyapunov stability.
* `IsAsymptoticallyStable`: Lyapunov stability plus local attractiveness.
* `IsGloballyAsymptoticallyStable`: asymptotic stability with full region of attraction.
* `IsExponentiallyStableAt`: exponential decay of nearby trajectories.
* `IsUniformlyStableAt`: stability uniform in the initial time for a non-autonomous flow.
* `IsUniformlyAsymptoticallyStableAt`: uniform stability plus convergence uniform in the
  initial time.
* `regionOfAttraction`: the set of initial states whose trajectory converges to the
  equilibrium.
-/

open Filter
open scoped Topology

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E]

/-- Lyapunov stability of the equilibrium `x₀` for the autonomous flow `Φ`. -/
def IsLyapunovStable (Φ : ℝ → E → E) (x₀ : E) : Prop :=
  (𝓝 x₀).IsStableOn Φ (Set.Ici 0)

/-- Instability of `x₀`: the autonomous flow `Φ` is not Lyapunov stable at `x₀`. -/
def IsUnstable (Φ : ℝ → E → E) (x₀ : E) : Prop :=
  ¬ IsLyapunovStable Φ x₀

/-- Asymptotic stability of `x₀`: Lyapunov stability together with local attractiveness. -/
def IsAsymptoticallyStable (Φ : ℝ → E → E) (x₀ : E) : Prop :=
  IsLyapunovStable Φ x₀ ∧ Filter.IsAttractive (l := 𝓝 x₀) (Φ := Φ) (l' := Filter.atTop)

/-- The region of attraction of `x₀` for the autonomous flow `Φ`: the set of initial states
whose trajectory converges to `x₀`. -/
def regionOfAttraction (Φ : ℝ → E → E) (x₀ : E) : Set E :=
  {x | Tendsto (fun t ↦ Φ t x) Filter.atTop (𝓝 x₀)}

/-- Global asymptotic stability: `x₀` is asymptotically stable and its region of attraction is
the whole state space. -/
def IsGloballyAsymptoticallyStable (Φ : ℝ → E → E) (x₀ : E) : Prop :=
  IsAsymptoticallyStable Φ x₀ ∧ regionOfAttraction Φ x₀ = Set.univ

/-- Exponential stability of `x₀`: nearby trajectories decay to `x₀` at an exponential rate. -/
def IsExponentiallyStableAt (Φ : ℝ → E → E) (x₀ : E) : Prop :=
  ∃ C > 0, ∃ α > 0, ∀ᶠ x in 𝓝 x₀,
    ∀ t ≥ 0, dist (Φ t x) x₀ ≤ C * Real.exp (-α * t) * dist x x₀

/-- Uniform stability at `x₀` for the non-autonomous flow `Φ`: the stability threshold may
depend on the tolerance but not on the initial time. -/
def IsUniformlyStableAt (Φ : NonautonomousFlow ℝ E) (x₀ : E) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t₀ ≥ 0, ∀ x, dist x x₀ < δ →
    ∀ t ≥ t₀, dist (Φ t₀ x t) x₀ < ε

/-- Uniform asymptotic stability at `x₀` for the non-autonomous flow `Φ`: uniform stability
together with convergence to `x₀` that is uniform in the initial time. -/
def IsUniformlyAsymptoticallyStableAt (Φ : NonautonomousFlow ℝ E) (x₀ : E) : Prop :=
  IsUniformlyStableAt Φ x₀ ∧
    ∃ δ > 0, ∀ ε > 0, ∃ τ > 0, ∀ t₀ ≥ 0, ∀ x, dist x x₀ < δ →
      ∀ t ≥ t₀ + τ, dist (Φ t₀ x t) x₀ < ε

/-- Membership in the region of attraction is exactly convergence of the trajectory to `x₀`. -/
theorem mem_regionOfAttraction_iff {Φ : ℝ → E → E} {x₀ x : E} :
    x ∈ regionOfAttraction Φ x₀ ↔ Tendsto (fun t ↦ Φ t x) Filter.atTop (𝓝 x₀) :=
  Iff.rfl

/-- A globally asymptotically stable equilibrium is asymptotically stable. This is the forward
direction of the defining conjunction. -/
theorem isAsymptoticallyStable_of_isGloballyAsymptoticallyStable
    {Φ : ℝ → E → E} {x₀ : E} (h : IsGloballyAsymptoticallyStable Φ x₀) :
    IsAsymptoticallyStable Φ x₀ :=
  h.1

/-- If the origin is a stationary point of the flow, then the origin lies in its own region of
attraction: the constant trajectory through the origin converges to the origin. -/
theorem mem_regionOfAttraction_zero_of_stationary {Φ : ℝ → E → E}
    (hfix : ∀ t, Φ t 0 = 0) : 0 ∈ regionOfAttraction Φ 0 := by
  rw [mem_regionOfAttraction_iff]
  simpa only [hfix] using tendsto_const_nhds

/-- For a flow that is stationary at the origin, the trajectory starting at the origin converges
to the origin. -/
theorem tendsto_zero_of_stationary {Φ : ℝ → E → E} (hfix : ∀ t, Φ t 0 = 0) :
    Tendsto (fun t ↦ Φ t 0) Filter.atTop (𝓝 0) := by
  rw [← mem_regionOfAttraction_iff]
  exact mem_regionOfAttraction_zero_of_stationary hfix

/-- If the origin belongs to the region of attraction, then the trajectory starting at the
origin converges to the origin. -/
theorem tendsto_zero_of_mem_regionOfAttraction_zero {Φ : ℝ → E → E}
    (h : 0 ∈ regionOfAttraction Φ 0) :
    Tendsto (fun t ↦ Φ t 0) Filter.atTop (𝓝 0) :=
  h

/-- Instability of `x₀` is exactly the negation of Lyapunov stability at `x₀`. -/
theorem isUnstable_iff_not_isLyapunovStable {Φ : ℝ → E → E} {x₀ : E} :
    IsUnstable Φ x₀ ↔ ¬ IsLyapunovStable Φ x₀ :=
  Iff.rfl

/-- For an autonomous flow, uniform stability of its non-autonomous incarnation at `x₀` is
exactly filter stability of the autonomous flow restricted to `[0, ∞)`.

Indeed `(Φ.toNonautonomousFlow) t₀ x t = Φ (t - t₀) x`, so quantifying over all `t₀ ≥ 0` and
`t ≥ t₀` is the same as quantifying over all forward times `t - t₀ ≥ 0`; the ε-δ uniformity in
`t₀` is precisely the filter-stability condition. -/
theorem isUniformlyStableAt_toNonautonomousFlow_iff (Φ : AutonomousFlow ℝ E) (x₀ : E) :
    IsUniformlyStableAt Φ.toNonautonomousFlow x₀ ↔ (𝓝 x₀).IsStableOn Φ (Set.Ici 0) := by
  constructor
  · intro h
    rw [(Metric.nhds_basis_ball (x := x₀)).isStableOn_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h ε hε
    refine ⟨δ, hδ, ?_⟩
    intro t _ht x hx
    rw [Metric.mem_ball] at hx ⊢
    have := hδ' 0 le_rfl x hx t _ht
    simpa only [AutonomousFlow.toNonautonomousFlow_apply, sub_zero] using this
  · intro h
    rw [(Metric.nhds_basis_ball (x := x₀)).isStableOn_iff] at h
    intro ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h ε hε
    refine ⟨δ, hδ, ?_⟩
    intro t₀ ht₀ x hx t ht
    have hxball : x ∈ Metric.ball x₀ δ := Metric.mem_ball.mpr hx
    have ht' : t - t₀ ∈ Set.Ici (0 : ℝ) := by
      simp only [Set.mem_Ici]
      linarith
    have := hδ' (t - t₀) ht' x hxball
    rw [Metric.mem_ball] at this
    simpa only [AutonomousFlow.toNonautonomousFlow_apply] using this

/-- The modern exponential-stability predicate implies the book's ε-δ form (Definition 1.9):
the constant `C` in the ratio estimate is absorbed into the tolerance `ε`, and the decay rate `α`
is unchanged. The converse is not claimed here; without a Lipschitz-dependence hypothesis on the
initial state the ε-δ form does not recover the ratio estimate. -/
theorem isExponentiallyStableAt_implies_eps_delta (Φ : ℝ → E → E) (x₀ : E)
    (h : IsExponentiallyStableAt Φ x₀) :
    ∃ α > 0, ∀ ε > 0, ∃ δ > 0, ∀ x, dist x x₀ < δ →
      ∀ t ≥ 0, dist (Φ t x) x₀ ≤ ε * Real.exp (-α * t) := by
  obtain ⟨C, hC, α, hα, hstab⟩ := h
  obtain ⟨δ₀, hδ₀, hsub⟩ := Metric.mem_nhds_iff.mp hstab
  refine ⟨α, hα, fun ε hε ↦ ?_⟩
  refine ⟨min δ₀ (ε / C), lt_min hδ₀ (div_pos hε hC), ?_⟩
  intro x hx t ht
  have hxδ₀ : dist x x₀ < δ₀ := lt_of_lt_of_le hx (min_le_left _ _)
  have hxε : dist x x₀ ≤ ε / C := le_of_lt (lt_of_lt_of_le hx (min_le_right _ _))
  have hroot := hsub (Metric.mem_ball.mpr hxδ₀) t ht
  calc dist (Φ t x) x₀
      ≤ C * Real.exp (-α * t) * dist x x₀ := hroot
    _ ≤ C * Real.exp (-α * t) * (ε / C) := by
        exact mul_le_mul_of_nonneg_left hxε (by positivity)
    _ = ε * Real.exp (-α * t) := by
        field_simp
