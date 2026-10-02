/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Stability.HomogeneityContraction
public import DynamicalSystems.Stability.Homogeneity
public import DynamicalSystems.Stability.FiniteTime
public import DynamicalSystems.Basic.NonAutonomous

/-! # Homogeneity implies finite-time stability (Levant's Theorem 1)

This file formalises the implication `3° ⇒ 1°` of Theorem 1 of A. Levant and
L. Alelishvili, *Discontinuous Homogeneous Control*, Chapter 4 of G. Bartolini,
L. Fridman, A. Pisano and E. Usai (eds.), *Modern Sliding Mode Control Theory: New
Perspectives and Applications*, LNCIS 375, Springer 2008 (printed p. 72, PDF p. 88).

A *dilation action* `d` satisfies `d 1 = id` and `d (κ * μ) = d κ ∘ d μ`; a flow is
*homogeneous* with time exponent `p` when it intertwines the dilation with the rescaled
time, `Φ (κ ^ p * t) (d κ x) = d κ (Φ t x)` (the book's combined transformation
`G_κ : (t, x) ↦ (κ ^ p t, d_κ x)`). A set `D` containing the origin is *dilation
retractable* when `d_κ D ⊆ D` for `0 < κ ≤ 1` and *contractive* when one step of the
time-`T` flow maps `D` into `d_λ D` for some `0 < λ < 1`.

The proof is geometric, not Lyapunov-theoretic. Iterating the contraction together with
homogeneity places the trajectory started at `x ∈ D` at time `s_N = T ∑_{k < N} (λ ^ p) ^ k`
inside `d (λ ^ N) '' D`; since `s_N → T / (1 - λ ^ p)`, continuity of the orbit sends the
limit into every `closure (d (λ ^ N) '' D)`, and the shrinking hypothesis forces it to be
`0`. Once the orbit is at the origin at the settling time it stays there by the fixed-point
hypothesis, using the semigroup law.

## Main definitions

* `IsDilationAction`: the one-parameter dilation laws `d 1 = id`, `d (κ * μ) = d κ ∘ d μ`.
* `IsHomogeneousFlow`: the flow–dilation scaling law `Φ (κ ^ p * t) (d κ x) = d κ (Φ t x)`.

## Main results

* `weightedDilation_isDilationAction`: the weighted dilation of slice S4 is a dilation action.
* `eventually_eq_zero_of_isHomogeneousFlow_of_contractive`: Levant's Theorem 1, `3° ⇒ 1°`,
  in unbundled form with an explicit semigroup law.
* `AutonomousFlow.eventually_eq_zero_of_isHomogeneousFlow_of_contractive`: the bundled
  `AutonomousFlow` specialization.
* `isFiniteTimeAttractiveAt_of_isHomogeneousFlow_of_contractive`: the bridge to slice S1,
  a contracting retractable neighbourhood of `0` gives `IsFiniteTimeAttractiveAt Φ 0`.
-/

open Filter
open scoped Topology

@[expose] public section

/-- A **dilation action** on `E`: the identity at exponent `1` and the multiplicative
one-parameter group law `d (κ * μ) = d κ ∘ d μ` for positive exponents. -/
def IsDilationAction {E : Type*} (d : ℝ → E → E) : Prop :=
  (d 1 = id) ∧ ∀ κ μ, 0 < κ → 0 < μ → ∀ x, d (κ * μ) x = d κ (d μ x)

/-- A flow `Φ` is **homogeneous of time exponent `p`** with respect to a dilation `d` when
the book's combined transformation `G_κ : (t, x) ↦ (κ ^ p * t, d_κ x)` maps trajectories to
trajectories, i.e. `Φ (κ ^ p * t) (d κ x) = d κ (Φ t x)` for every `κ > 0`. -/
def IsHomogeneousFlow {E : Type*} (Φ : ℝ → E → E) (d : ℝ → E → E) (p : ℝ) : Prop :=
  ∀ κ, 0 < κ → ∀ t, 0 ≤ t → ∀ x, Φ (κ ^ p * t) (d κ x) = d κ (Φ t x)

/-- The weighted dilation `d_λ x = fun i ↦ λ ^ (r i) * x i` of slice S4 is a dilation
action: `d_1 = id` and `d_{λ μ} = d_λ ∘ d_μ` for positive exponents. -/
theorem weightedDilation_isDilationAction {ι : Type*} (r : ι → ℝ) :
    IsDilationAction (weightedDilation r) :=
  ⟨weightedDilation_one r, fun _κ _μ hκ hμ x ↦ weightedDilation_mul r hκ hμ x⟩

/-- **Levant's Theorem 1, `3° ⇒ 1°` (unbundled).** Let `Φ` be a flow homogeneous of positive
time exponent `p` with respect to a dilation action `d`, with semigroup law `hcomp`. Suppose
`D` is dilation retractable, `λ ∈ (0, 1)`, `T > 0`, one time-`T` step maps `D` into `d_λ D`,
the orbit through `x ∈ D` is continuous at the settling time `T / (1 - λ ^ p)`, the origin is
a fixed point of the forward flow, and any point lying in every `closure (d (λ ^ N) '' D)`
is `0`. Then the orbit through `x` reaches `0` by time `T / (1 - λ ^ p)` and stays there. -/
theorem eventually_eq_zero_of_isHomogeneousFlow_of_contractive
    {E : Type*} [NormedAddCommGroup E] {Φ : ℝ → E → E} {d : ℝ → E → E} {p : ℝ}
    (hd : IsDilationAction d) (hΦ : IsHomogeneousFlow Φ d p) (hp : 0 < p)
    (hcomp : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ y, Φ (s + t) y = Φ s (Φ t y))
    {D : Set E} (hD : ∀ κ, 0 < κ → κ ≤ 1 → ∀ y ∈ D, d κ y ∈ D)
    {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {T : ℝ} (hT : 0 < T)
    (hcontract : ∀ y ∈ D, Φ T y ∈ d l '' D) {x : E} (hx : x ∈ D)
    (hcont : ContinuousAt (Φ · x) (T / (1 - l ^ p)))
    (hfix : ∀ s, 0 ≤ s → Φ s 0 = 0)
    (hshrink : ∀ y, (∀ N : ℕ, y ∈ closure (d (l ^ N) '' D)) → y = 0) :
    ∀ t, T / (1 - l ^ p) ≤ t → Φ t x = 0 := by
  intro t ht
  have hlp1 : l ^ p < 1 := Real.rpow_lt_one hl0.le hl1 hp
  have hden : 0 < 1 - l ^ p := sub_pos.mpr hlp1
  have hτpos : 0 < T / (1 - l ^ p) := div_pos hT hden
  have hstep_nonneg : ∀ n : ℕ, 0 ≤ (l ^ p) ^ n := fun n ↦
    pow_nonneg (Real.rpow_nonneg hl0.le p) n
  have hs_nonneg : ∀ N : ℕ, 0 ≤ geometricPartialSum T l p N := by
    intro N
    unfold geometricPartialSum
    exact mul_nonneg hT.le (Finset.sum_nonneg fun k _ ↦ hstep_nonneg k)
  -- Induction: the orbit sits inside `d (λ ^ N) '' D` at the geometric partial sum `s_N`.
  have hind : ∀ N : ℕ, 1 ≤ N →
      Φ (geometricPartialSum T l p N) x ∈ d (l ^ N) '' D := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base =>
      have h1 : geometricPartialSum T l p 1 = T := by
        simp only [geometricPartialSum, Finset.sum_range_one, pow_zero, mul_one]
      rw [h1, pow_one]
      exact hcontract x hx
    | succ n _ ih =>
      obtain ⟨y, hyD, hy⟩ := ih
      obtain ⟨z, hzD, hz⟩ := hcontract y hyD
      have hs : geometricPartialSum T l p (n + 1)
          = T * (l ^ p) ^ n + geometricPartialSum T l p n := by
        unfold geometricPartialSum
        rw [Finset.sum_range_succ]
        ring
      refine ⟨z, hzD, ?_⟩
      rw [hs]
      rw [hcomp (T * (l ^ p) ^ n) (geometricPartialSum T l p n)
        (mul_nonneg hT.le (hstep_nonneg n)) (hs_nonneg n) x]
      rw [← hy]
      have harg : T * (l ^ p) ^ n = (l ^ n) ^ p * T := by
        rw [mul_comm T, rpow_pow_comm hl0.le p n]
      rw [harg, hΦ (l ^ n) (pow_pos hl0 n) T hT.le y]
      rw [← hz]
      rw [← hd.2 (l ^ n) l (pow_pos hl0 n) hl0 z]
      rw [show l ^ n * l = l ^ (n + 1) from (pow_succ l n).symm]
  -- The partial sums converge to the settling time, so the orbit converges there.
  have hs_tend : Tendsto (geometricPartialSum T l p) atTop (𝓝 (T / (1 - l ^ p))) :=
    tendsto_geometricPartialSum hp hl0.le hl1
  have hτzero : Φ (T / (1 - l ^ p)) x = 0 := by
    apply hshrink
    intro M
    have hlim : Tendsto (fun N : ℕ ↦ Φ (geometricPartialSum T l p (N + 1)) x) atTop
        (𝓝 (Φ (T / (1 - l ^ p)) x)) :=
      (show Tendsto (fun s : ℝ ↦ Φ s x) (𝓝 (T / (1 - l ^ p)))
          (𝓝 (Φ (T / (1 - l ^ p)) x)) from hcont).comp
        (hs_tend.comp (tendsto_add_atTop_nat 1))
    have hev : ∀ᶠ N in atTop,
        Φ (geometricPartialSum T l p (N + 1)) x ∈ d (l ^ M) '' D := by
      filter_upwards [eventually_ge_atTop M] with N hN
      exact image_subset_of_le hd hl0 hl1 hD (by omega) (hind (N + 1) (by omega))
    exact mem_closure_of_tendsto hlim hev
  -- Once the orbit is at the origin it stays there, by the semigroup law and `hfix`.
  rw [show t = (t - T / (1 - l ^ p)) + T / (1 - l ^ p) by ring]
  rw [hcomp (t - T / (1 - l ^ p)) (T / (1 - l ^ p)) (sub_nonneg.mpr ht) hτpos.le x]
  rw [hτzero, hfix (t - T / (1 - l ^ p)) (sub_nonneg.mpr ht)]

/-- **Levant's Theorem 1, `3° ⇒ 1°` for a bundled `AutonomousFlow`.** The semigroup law is
discharged by `AutonomousFlow.map_comp`; all other hypotheses are those of
`eventually_eq_zero_of_isHomogeneousFlow_of_contractive`. -/
theorem AutonomousFlow.eventually_eq_zero_of_isHomogeneousFlow_of_contractive
    {E : Type*} [NormedAddCommGroup E] {Φ : AutonomousFlow ℝ E} {d : ℝ → E → E} {p : ℝ}
    (hd : IsDilationAction d) (hΦ : IsHomogeneousFlow (Φ : ℝ → E → E) d p) (hp : 0 < p)
    {D : Set E} (hD : ∀ κ, 0 < κ → κ ≤ 1 → ∀ y ∈ D, d κ y ∈ D)
    {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {T : ℝ} (hT : 0 < T)
    (hcontract : ∀ y ∈ D, Φ T y ∈ d l '' D) {x : E} (hx : x ∈ D)
    (hcont : ContinuousAt (Φ · x) (T / (1 - l ^ p)))
    (hfix : ∀ s, 0 ≤ s → Φ s 0 = 0)
    (hshrink : ∀ y, (∀ N : ℕ, y ∈ closure (d (l ^ N) '' D)) → y = 0) :
    ∀ t, T / (1 - l ^ p) ≤ t → Φ t x = 0 :=
  _root_.eventually_eq_zero_of_isHomogeneousFlow_of_contractive hd hΦ hp
    (fun s t _ _ y ↦ (Φ.map_comp s t y).symm) hD hl0 hl1 hT hcontract hx hcont hfix hshrink

/-- **Bridge to finite-time attractivity (slice S1).** If `D` is a neighbourhood of the
origin and every point of `D` has a continuous orbit at the settling time `T / (1 - λ ^ p)`,
then the flow is finite-time attractive at `0`: the settling time `T / (1 - λ ^ p)` witnesses
the finitely many nearby initial states. -/
theorem isFiniteTimeAttractiveAt_of_isHomogeneousFlow_of_contractive
    {E : Type*} [NormedAddCommGroup E] {Φ : ℝ → E → E} {d : ℝ → E → E} {p : ℝ}
    (hd : IsDilationAction d) (hΦ : IsHomogeneousFlow Φ d p) (hp : 0 < p)
    (hcomp : ∀ s t, 0 ≤ s → 0 ≤ t → ∀ y, Φ (s + t) y = Φ s (Φ t y))
    {D : Set E} (hD : ∀ κ, 0 < κ → κ ≤ 1 → ∀ y ∈ D, d κ y ∈ D)
    {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {T : ℝ} (hT : 0 < T)
    (hcontract : ∀ y ∈ D, Φ T y ∈ d l '' D)
    (hcont : ∀ y ∈ D, ContinuousAt (Φ · y) (T / (1 - l ^ p)))
    (hfix : ∀ s, 0 ≤ s → Φ s 0 = 0)
    (hshrink : ∀ y, (∀ N : ℕ, y ∈ closure (d (l ^ N) '' D)) → y = 0)
    (hD_nhds : D ∈ 𝓝 (0 : E)) : IsFiniteTimeAttractiveAt Φ 0 := by
  have hlp1 : l ^ p < 1 := Real.rpow_lt_one hl0.le hl1 hp
  have hτnonneg : 0 ≤ T / (1 - l ^ p) := (div_pos hT (sub_pos.mpr hlp1)).le
  rw [IsFiniteTimeAttractiveAt]
  filter_upwards [hD_nhds] with x hx
  exact ⟨T / (1 - l ^ p), hτnonneg, fun t ht ↦
    eventually_eq_zero_of_isHomogeneousFlow_of_contractive hd hΦ hp hcomp hD hl0 hl1 hT
      hcontract hx (hcont x hx) hfix hshrink t ht⟩
