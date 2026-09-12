/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.Trajectory
public import DynamicalSystems.Linear.Subspaces

/-! # Finite-horizon reachability and output distinguishability

This file relates the trajectory notions of Chapter 3 of Trentelman, Stoorvogel
and Hautus, *Control Theory for Linear Systems*, to the algebraic pair
predicates of `DynamicalSystems.Linear.Subspaces`.

For a real finite-dimensional linear time-invariant system we define

* `LinearSystem.reachableSetAt sys T`, the set of states reachable from the
  origin at time `T` by a locally integrable input, i.e. the set of points
  `∫₀ᵀ exp((T - s) A) B u(s) ds`;
* `LinearSystem.IndistinguishableOn sys T x₀ x₁`, meaning that the two initial
  states `x₀` and `x₁` produce the same output on `[0,T]` for every admissible
  input.

The trajectory notion of distinguishability is proved equivalent to the
algebraic unobservability predicate for every strictly positive horizon:
`LinearSystem.indistinguishableOn_iff_mem_unobservableSubspace` states that two
states are indistinguishable on `[0,T]` (`T > 0`) exactly when their difference
lies in `LinearMap.unobservableSubspace sys.C sys.A`. The two directions are
`LinearSystem.continuousC_expFlow_eq_zero_of_mem_unobservableSubspace` (the
power-series evaluation) and
`LinearSystem.mem_unobservableSubspace_of_forall_continuousC_expFlow_eq_zero`
(the differentiation of the zero output curve).

## Main definitions

* `LinearSystem.reachableSetAt`, `LinearSystem.reachableSetAtSubmodule`
* `LinearSystem.IndistinguishableOn`

## Main results

* `LinearSystem.reachableSetAtSubmodule` is a submodule of the state space
* `LinearSystem.continuousC_expFlow_eq_zero_of_mem_unobservableSubspace`
* `LinearSystem.mem_unobservableSubspace_of_forall_continuousC_expFlow_eq_zero`
* `LinearSystem.indistinguishableOn_iff_mem_unobservableSubspace`

## References

* H. L. Trentelman, A. A. Stoorvogel, M. Hautus, *Control Theory for Linear
  Systems*, Springer, 2001, Section 3.2 (Theorem 3.1, Corollaries 3.2–3.4) and
  Section 3.3 (Definition 3.6, Theorem 3.8).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Interval

namespace LinearSystem

variable {X U Y : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-! ### The finite-horizon reachable set -/

/-- The set of states reachable from the origin at time `T` by a locally
integrable input. This is the set `W_T` of Trentelman–Stoorvogel–Hautus,
equation (3.5). It is presented through the variation-of-constants curve, which
makes linearity in the input available directly. -/
def reachableSetAt (sys : LinearSystem ℝ X U Y) (T : ℝ) : Set X :=
  {x | ∃ u : ℝ → U, LocallyIntegrable u volume ∧
    sys.variationOfConstants 0 0 u T = x}

/-- Membership unfolding for `LinearSystem.reachableSetAt`. -/
theorem mem_reachableSetAt {sys : LinearSystem ℝ X U Y} {T : ℝ} {x : X} :
    x ∈ sys.reachableSetAt T ↔
      ∃ u : ℝ → U, LocallyIntegrable u volume ∧
        sys.variationOfConstants 0 0 u T = x := Iff.rfl

/-- The variation-of-constants curve at time `T` is the transported forcing
integral. This is the form used to prove linearity of `reachableSetAt`. -/
theorem variationOfConstants_zero_eq (sys : LinearSystem ℝ X U Y) (T : ℝ) (u : ℝ → U) :
    sys.variationOfConstants 0 0 u T =
      sys.expFlow T (∫ s in (0 : ℝ)..T, sys.forcing 0 u s) := by
  simp [variationOfConstants]

/-- The forcing integrand is additive in the input. -/
theorem forcing_add (sys : LinearSystem ℝ X U Y) (u w : ℝ → U) :
    sys.forcing 0 (u + w) = sys.forcing 0 u + sys.forcing 0 w := by
  funext s
  simp only [forcing, Pi.add_apply, map_add, continuousB_apply]

/-- The forcing integrand is homogeneous in the input. -/
theorem forcing_smul (sys : LinearSystem ℝ X U Y) (c : ℝ) (u : ℝ → U) :
    sys.forcing 0 (c • u) = c • sys.forcing 0 u := by
  funext s
  simp only [forcing, Pi.smul_apply, map_smul, continuousB_apply]

/-- Linearity of the variation-of-constants solution in the input, at zero
initial state. -/
theorem variationOfConstants_zero_add (sys : LinearSystem ℝ X U Y) (T : ℝ)
    (u w : ℝ → U) (hu : LocallyIntegrable u volume) (hw : LocallyIntegrable w volume) :
    sys.variationOfConstants 0 0 (u + w) T =
      sys.variationOfConstants 0 0 u T + sys.variationOfConstants 0 0 w T := by
  rw [variationOfConstants_zero_eq, variationOfConstants_zero_eq, variationOfConstants_zero_eq,
    forcing_add]
  simp only [Pi.add_apply]
  rw [intervalIntegral.integral_add
      (intervalIntegrable_forcing sys 0 hu 0 T) (intervalIntegrable_forcing sys 0 hw 0 T),
    map_add]

/-- Homogeneity of the variation-of-constants solution in the input, at zero
initial state. -/
theorem variationOfConstants_zero_smul (sys : LinearSystem ℝ X U Y) (T c : ℝ) (u : ℝ → U) :
    sys.variationOfConstants 0 0 (c • u) T =
      c • sys.variationOfConstants 0 0 u T := by
  rw [variationOfConstants_zero_eq, variationOfConstants_zero_eq, forcing_smul]
  simp only [Pi.smul_apply]
  rw [intervalIntegral.integral_smul, map_smul]

/-- With zero input the variation-of-constants curve is the homogeneous flow. -/
theorem variationOfConstants_zero_input (sys : LinearSystem ℝ X U Y) (x : X) (t : ℝ) :
    sys.variationOfConstants 0 x 0 t = sys.expFlow t x := by
  simp [variationOfConstants, forcing]

/-- The variation-of-constants curve with initial time `0` in explicit form. -/
theorem variationOfConstants_eq (sys : LinearSystem ℝ X U Y) (x : X) (u : ℝ → U)
    (t : ℝ) :
    sys.variationOfConstants 0 x u t =
      sys.expFlow t (x + ∫ s in (0 : ℝ)..t, sys.forcing 0 u s) := by
  simp [variationOfConstants]

/-- The finite-horizon reachable set is a submodule of the state space. -/
noncomputable def reachableSetAtSubmodule (sys : LinearSystem ℝ X U Y) (T : ℝ) :
    Submodule ℝ X where
  carrier := sys.reachableSetAt T
  zero_mem' := by
    refine ⟨fun _ : ℝ => 0, locallyIntegrable_const (0 : U), ?_⟩
    simp [variationOfConstants, forcing]
  add_mem' := by
    rintro x y ⟨u, hu, hx⟩ ⟨w, hw, hy⟩
    refine ⟨u + w, hu.add hw, ?_⟩
    rw [variationOfConstants_zero_add sys T u w hu hw, hx, hy]
  smul_mem' := by
    intro c x ⟨u, hu, hx⟩
    refine ⟨c • u, hu.smul c, ?_⟩
    rw [variationOfConstants_zero_smul, hx]

/-- Membership in the finite-horizon reachable submodule. -/
theorem mem_reachableSetAtSubmodule {sys : LinearSystem ℝ X U Y} {T : ℝ} {x : X} :
    x ∈ sys.reachableSetAtSubmodule T ↔
      ∃ u : ℝ → U, LocallyIntegrable u volume ∧
        sys.variationOfConstants 0 0 u T = x := Iff.rfl

/-! ### Exponential series -/

omit [FiniteDimensional ℝ U] in
/-- The operator exponential as a norm-convergent power series. This is the
form used both to evaluate the exponential on vectors and to differentiate it. -/
theorem expFlow_hasSum (sys : LinearSystem ℝ X U Y) (t : ℝ) :
    HasSum (fun n : ℕ => ((Nat.factorial n : ℝ))⁻¹ • (t • sys.continuousA) ^ n)
      (sys.expFlow t) := by
  have hmem : (t • sys.continuousA) ∈
      Metric.eball (0 : X →L[ℝ] X) (NormedSpace.expSeries ℝ (X →L[ℝ] X)).radius :=
    (NormedSpace.expSeries_radius_eq_top ℝ (X →L[ℝ] X)).symm ▸ edist_lt_top _ _
  have hsummable :=
    NormedSpace.expSeries_summable_of_mem_ball' (𝕂 := ℝ) (t • sys.continuousA) hmem
  have htsum : sys.expFlow t =
      ∑' n : ℕ, ((Nat.factorial n : ℝ))⁻¹ • (t • sys.continuousA) ^ n := by
    rw [expFlow]
    exact congrFun (NormedSpace.exp_eq_tsum ℝ) _
  rw [htsum]
  exact hsummable.hasSum

omit [FiniteDimensional ℝ U] in
/-- The scalar multiple of a power of the state map, evaluated on a vector. -/
theorem smul_pow_continuousA_apply (sys : LinearSystem ℝ X U Y) (t : ℝ) (n : ℕ) (z : X) :
    ((t • sys.continuousA) ^ n) z = t ^ n • ((sys.A ^ n) z) := by
  rw [smul_pow]
  simp only [smul_apply]
  congr 1
  change (((sys.continuousA ^ n : X →L[ℝ] X) : X →ₗ[ℝ] X)) z = (sys.A ^ n) z
  rw [ContinuousLinearMap.toLinearMap_pow]
  rfl

/-! ### Output distinguishability -/

/-- Two initial states are indistinguishable on `[0,T]` when for every locally
integrable input the outputs agree on the whole interval. Source:
Trentelman–Stoorvogel–Hautus, Definition 3.6. -/
def IndistinguishableOn (sys : LinearSystem ℝ X U Y) (T : ℝ) (x₀ x₁ : X) : Prop :=
  ∀ u : ℝ → U, LocallyIntegrable u volume →
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      sys.readout (sys.variationOfConstants 0 x₀ u t) (u t) =
        sys.readout (sys.variationOfConstants 0 x₁ u t) (u t)

/-- Two initial states are indistinguishable exactly when the zero-input output
curves agree, i.e. when `C exp (t A) (x₀ - x₁) = 0` on `[0,T]`. The input and
the feedthrough cancel because the variation-of-constants solution is affine in
the initial state. -/
theorem indistinguishableOn_iff_continuousC_expFlow_eq_zero
    (sys : LinearSystem ℝ X U Y) (T : ℝ) (x₀ x₁ : X) :
    sys.IndistinguishableOn T x₀ x₁ ↔
      ∀ t ∈ Set.Icc (0 : ℝ) T, sys.C (sys.expFlow t (x₀ - x₁)) = 0 := by
  constructor
  · intro h t ht
    have h0 := h 0 (locallyIntegrable_const (0 : U)) t ht
    simp only [readout, Pi.zero_apply, map_zero, add_zero] at h0
    rw [variationOfConstants_zero_input, variationOfConstants_zero_input] at h0
    calc sys.C (sys.expFlow t (x₀ - x₁))
        = sys.C (sys.expFlow t x₀) - sys.C (sys.expFlow t x₁) := by rw [map_sub, map_sub]
      _ = 0 := by rw [h0, sub_self]
  · intro h u hu t ht
    have hdiff : sys.variationOfConstants 0 x₀ u t - sys.variationOfConstants 0 x₁ u t =
        sys.expFlow t (x₀ - x₁) := by
      rw [variationOfConstants_eq, variationOfConstants_eq, ← map_sub]
      congr 1
      abel
    rw [readout, readout, ← sub_eq_zero]
    have hsub : sys.C (sys.variationOfConstants 0 x₀ u t) + sys.D (u t) -
        (sys.C (sys.variationOfConstants 0 x₁ u t) + sys.D (u t)) =
        sys.C (sys.variationOfConstants 0 x₀ u t - sys.variationOfConstants 0 x₁ u t) := by
      rw [map_sub]; abel
    rw [hsub, hdiff]
    exact h t ht

omit [FiniteDimensional ℝ U] in
/-- The algebraic unobservability predicate implies that the zero-input output
curve vanishes. Source: Trentelman–Stoorvogel–Hautus, Theorem 3.8, (iii) ⇒
(iv), via the power-series expansion of the exponential. -/
theorem continuousC_expFlow_eq_zero_of_mem_unobservableSubspace
    (sys : LinearSystem ℝ X U Y) {z : X}
    (hz : z ∈ LinearMap.unobservableSubspace sys.C sys.A) (t : ℝ) :
    sys.C (sys.expFlow t z) = 0 := by
  rw [LinearMap.mem_unobservableSubspace] at hz
  have hpoint := (expFlow_hasSum sys t).mapL (ContinuousLinearMap.apply ℝ X z)
  have hC := hpoint.mapL sys.continuousC
  simp only [ContinuousLinearMap.apply_apply] at hC
  have hterm : ∀ n : ℕ,
      sys.continuousC ((((Nat.factorial n : ℝ))⁻¹ • (t • sys.continuousA) ^ n) z) = 0 := by
    intro n
    rw [smul_apply, map_smul, smul_pow_continuousA_apply, map_smul, continuousC_apply, hz n]
    simp
  have hfun : (fun n : ℕ =>
      sys.continuousC ((((Nat.factorial n : ℝ))⁻¹ • (t • sys.continuousA) ^ n) z)) =
      fun _ => (0 : Y) := funext hterm
  rw [hfun] at hC
  simpa using hC.tsum_eq.symm

omit [FiniteDimensional ℝ U] in
/-- The derivative of the zero-input output curve family
`t ↦ C (A ^ k (exp (t A) z))`. -/
theorem hasDerivAt_continuousC_pow_expFlow (sys : LinearSystem ℝ X U Y) (k : ℕ) (z : X)
    (t : ℝ) :
    HasDerivAt
      (fun s => (sys.continuousC.comp ((sys.continuousA : X →L[ℝ] X) ^ k)) (sys.expFlow s z))
      ((sys.continuousC.comp ((sys.continuousA : X →L[ℝ] X) ^ k)) (sys.A (sys.expFlow t z)))
      t :=
  (ContinuousLinearMap.hasFDerivAt
    (sys.continuousC.comp ((sys.continuousA : X →L[ℝ] X) ^ k))).comp_hasDerivAt t
      (hasDerivAt_expFlow_apply_state sys t z)

omit [FiniteDimensional ℝ U] in
/-- The derivative family advances the power: the derivative of
`t ↦ C (A ^ k (exp (t A) z))` is `t ↦ C (A ^ (k + 1) (exp (t A) z))`. -/
theorem hasDerivAt_continuousC_pow_expFlow_succ (sys : LinearSystem ℝ X U Y) (k : ℕ)
    (z : X) (t : ℝ) :
    HasDerivAt
      (fun s => (sys.continuousC.comp ((sys.continuousA : X →L[ℝ] X) ^ k)) (sys.expFlow s z))
      ((sys.continuousC.comp ((sys.continuousA : X →L[ℝ] X) ^ (k + 1))) (sys.expFlow t z))
      t := by
  have h := hasDerivAt_continuousC_pow_expFlow sys k z t
  have hsucc : (sys.continuousC.comp ((sys.continuousA : X →L[ℝ] X) ^ k))
        (sys.A (sys.expFlow t z)) =
      (sys.continuousC.comp ((sys.continuousA : X →L[ℝ] X) ^ (k + 1)))
        (sys.expFlow t z) := by
    simp only [continuousC_apply, ContinuousLinearMap.comp_apply]
    rw [pow_succ]
    rfl
  rwa [hsucc] at h

omit [FiniteDimensional ℝ U] in
/-- The trajectory condition implies the algebraic unobservability predicate.
Source: Trentelman–Stoorvogel–Hautus, Theorem 3.8, (iv) ⇒ (iii), proved by
differentiating the identically zero output curve on the open interval `(0,T)`
and using continuity at the initial time. -/
theorem mem_unobservableSubspace_of_forall_continuousC_expFlow_eq_zero
    (sys : LinearSystem ℝ X U Y) {z : X} {T : ℝ} (hT : 0 < T)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, sys.C (sys.expFlow t z) = 0) :
    z ∈ LinearMap.unobservableSubspace sys.C sys.A := by
  rw [LinearMap.mem_unobservableSubspace]
  let g : ℕ → ℝ → Y := fun k t =>
    (sys.continuousC.comp ((sys.continuousA : X →L[ℝ] X) ^ k)) (sys.expFlow t z)
  have hgderiv : ∀ k t, HasDerivAt (g k) (g (k + 1) t) t := by
    intro k t
    simpa only [g] using hasDerivAt_continuousC_pow_expFlow_succ sys k z t
  have hgcont : ∀ k, Continuous (g k) := by
    intro k
    have hE : Continuous (fun s : ℝ => sys.expFlow s) := by
      simpa using continuous_expFlow_sub sys 0
    exact ((sys.continuousC.comp ((sys.continuousA : X →L[ℝ] X) ^ k)).continuous).comp
      ((ContinuousLinearMap.apply ℝ X z).continuous.comp hE)
  have hgzero : ∀ k t, t ∈ Set.Ioo (0 : ℝ) T → g k t = 0 := by
    intro k
    induction k with
    | zero =>
        intro t ht
        exact h t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    | succ k ih =>
        intro t ht
        have hloc : g k =ᶠ[𝓝 t] (fun _ => (0 : Y)) := by
          filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
          exact ih s hs
        have hzero : HasDerivAt (g k) 0 t :=
          (hasDerivAt_const (x := t) (c := (0 : Y))).congr_of_eventuallyEq hloc
        have huniq := hzero.unique (hgderiv k t)
        simpa using huniq.symm
  intro k
  have hcont : ContinuousAt (g k) 0 := (hgcont k).continuousAt
  have hev : g k =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => (0 : Y)) := by
    filter_upwards [Ioo_mem_nhdsGT hT] with s hs
    exact hgzero k s hs
  have h1 : Tendsto (g k) (𝓝[>] (0 : ℝ)) (𝓝 (g k 0)) :=
    hcont.tendsto.mono_left inf_le_left
  have h2 : Tendsto (g k) (𝓝[>] (0 : ℝ)) (𝓝 (0 : Y)) :=
    Tendsto.congr' hev.symm tendsto_const_nhds
  have hgk : g k 0 = 0 := tendsto_nhds_unique h1 h2
  have hgk' : sys.continuousC (((sys.continuousA : X →L[ℝ] X) ^ k) z) = 0 := by
    simpa [g] using hgk
  have hconv : sys.continuousC (((sys.continuousA : X →L[ℝ] X) ^ k) z) =
      sys.C ((sys.A ^ k) z) := by
    rw [continuousC_apply]
    apply congrArg sys.C
    change (((sys.continuousA ^ k : X →L[ℝ] X) : X →ₗ[ℝ] X)) z = (sys.A ^ k) z
    rw [ContinuousLinearMap.toLinearMap_pow]
    rfl
  rwa [hconv] at hgk'

/-- The main equivalence of Theorem 3.8: two states are indistinguishable on a
strictly positive horizon exactly when their difference lies in the algebraic
unobservable subspace. -/
theorem indistinguishableOn_iff_mem_unobservableSubspace
    (sys : LinearSystem ℝ X U Y) {T : ℝ} (hT : 0 < T) (x₀ x₁ : X) :
    sys.IndistinguishableOn T x₀ x₁ ↔
      x₀ - x₁ ∈ LinearMap.unobservableSubspace sys.C sys.A := by
  rw [indistinguishableOn_iff_continuousC_expFlow_eq_zero]
  constructor
  · intro h
    exact mem_unobservableSubspace_of_forall_continuousC_expFlow_eq_zero sys hT h
  · intro hz t ht
    simpa using continuousC_expFlow_eq_zero_of_mem_unobservableSubspace sys hz t

end LinearSystem
