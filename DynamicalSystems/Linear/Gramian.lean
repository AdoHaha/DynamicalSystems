/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.Trajectory
public import DynamicalSystems.Linear.Subspaces
public import DynamicalSystems.Linear.Reachability
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Controllability and observability Gramians

For a real finite-dimensional linear time-invariant system on inner product
spaces we define the finite-horizon controllability and observability Gramians

```
W_c(T) = ∫₀ᵀ exp(s A) B B* exp(s A)* ds,
W_o(T) = ∫₀ᵀ exp(s A)* C* C exp(s A) ds,
```

as continuous linear endomorphisms of the state space, obtained by integrating
the continuous operator-valued integrands. The main results are the energy
identities

```
⟪x, W_c(T) x⟫ = ∫₀ᵀ ‖B* exp(s A)* x‖² ds,
⟪x, W_o(T) x⟫ = ∫₀ᵀ ‖C exp(s A) x‖² ds,
```

the resulting positive semidefiniteness, and, on a strictly positive horizon,
the positive-definiteness criteria for controllability and observability. The
kernel of the controllability Gramian is the orthogonal complement of the
algebraic reachable subspace, which identifies its range with the reachable set
and yields the trajectory/algebraic equivalence `reachableSetAt_eq_reachableSubspace`.

## Main definitions

* `LinearSystem.controllabilityGramian`
* `LinearSystem.observabilityGramian`
* `LinearSystem.IsPositiveDefinite`

## Main results

* `LinearSystem.inner_controllabilityGramian`,
  `LinearSystem.inner_observabilityGramian`
* `LinearSystem.controllabilityGramian_nonneg`,
  `LinearSystem.observabilityGramian_nonneg`
* `LinearSystem.adjoint_expFlow_eq`, `LinearSystem.mem_orthogonal_reachableSubspace_iff`,
  `LinearSystem.mem_reachableSubspace_orthogonal_of_forall_adjoint_expFlow_eq_zero`
* `LinearSystem.ker_controllabilityGramian`,
  `LinearSystem.reachableSetAt_eq_reachableSubspace`
* `LinearSystem.controllabilityGramian_posDef_iff_isControllable`,
  `LinearSystem.observabilityGramian_posDef_iff_isObservable`
* `LinearSystem.Examples.scalarIntegrator_controllable`,
  `LinearSystem.Examples.scalarIntegrator_observable`

## References

* H. L. Trentelman, A. A. Stoorvogel, M. Hautus, *Control Theory for Linear
  Systems*, Springer, 2001, Sections 5.2–5.3 (Gramians and observability).
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped Interval InnerProduct

namespace LinearSystem

variable {X U Y : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]

/-! ### Definitions -/

/-- The finite-horizon controllability Gramian
`W_c(T) = ∫₀ᵀ exp(s A) B B* exp(s A)* ds`, as a continuous endomorphism of the
state space. Source: Trentelman–Stoorvogel–Hautus, Section 5.2. -/
noncomputable def controllabilityGramian (sys : LinearSystem ℝ X U Y) (T : ℝ) :
    X →L[ℝ] X :=
  ∫ s in (0 : ℝ)..T,
    (sys.expFlow s).comp (sys.continuousB.comp ((ContinuousLinearMap.adjoint sys.continuousB).comp ((ContinuousLinearMap.adjoint (sys.expFlow s)))))

/-- The finite-horizon observability Gramian
`W_o(T) = ∫₀ᵀ exp(s A)* C* C exp(s A) ds`, as a continuous endomorphism of the
state space. Source: Trentelman–Stoorvogel–Hautus, Section 5.3. -/
noncomputable def observabilityGramian (sys : LinearSystem ℝ X U Y) (T : ℝ) :
    X →L[ℝ] X :=
  ∫ s in (0 : ℝ)..T,
    ((ContinuousLinearMap.adjoint (sys.expFlow s))).comp ((ContinuousLinearMap.adjoint sys.continuousC).comp (sys.continuousC.comp (sys.expFlow s)))

/-! ### Continuity of the integrands -/

omit [FiniteDimensional ℝ Y] in
/-- The controllability Gramian integrand is continuous in time. -/
theorem continuous_controllabilityIntegrand (sys : LinearSystem ℝ X U Y) :
    Continuous (fun s : ℝ =>
      (sys.expFlow s).comp
        (sys.continuousB.comp ((ContinuousLinearMap.adjoint sys.continuousB).comp ((ContinuousLinearMap.adjoint (sys.expFlow s)))))) := by
  have hE : Continuous (fun s : ℝ => sys.expFlow s) := by
    simpa using continuous_expFlow_sub sys 0
  have hEa : Continuous (fun s : ℝ => (ContinuousLinearMap.adjoint (sys.expFlow s))) :=
    ContinuousLinearMap.adjoint.continuous.comp hE
  exact hE.clm_comp (continuous_const.clm_comp (continuous_const.clm_comp hEa))

omit [FiniteDimensional ℝ U] in
/-- The observability Gramian integrand is continuous in time. -/
theorem continuous_observabilityIntegrand (sys : LinearSystem ℝ X U Y) :
    Continuous (fun s : ℝ =>
      ((ContinuousLinearMap.adjoint (sys.expFlow s))).comp
        ((ContinuousLinearMap.adjoint sys.continuousC).comp (sys.continuousC.comp (sys.expFlow s)))) := by
  have hE : Continuous (fun s : ℝ => sys.expFlow s) := by
    simpa using continuous_expFlow_sub sys 0
  have hEa : Continuous (fun s : ℝ => (ContinuousLinearMap.adjoint (sys.expFlow s))) :=
    ContinuousLinearMap.adjoint.continuous.comp hE
  exact hEa.clm_comp (continuous_const.clm_comp (continuous_const.clm_comp hE))

/-! ### Energy identities -/

omit [FiniteDimensional ℝ Y] in
/-- The controllability energy identity: the quadratic form of `W_c(T)` is the
integral of the squared norm `‖B* exp(s A)* x‖²`. -/
theorem inner_controllabilityGramian (sys : LinearSystem ℝ X U Y) (T : ℝ) (x : X) :
    inner ℝ x (sys.controllabilityGramian T x) =
      ∫ s in (0 : ℝ)..T, ‖(ContinuousLinearMap.adjoint sys.continuousB) (((ContinuousLinearMap.adjoint (sys.expFlow s))) x)‖ ^ 2 := by
  let L : ℝ → X →L[ℝ] X := fun s =>
    (sys.expFlow s).comp (sys.continuousB.comp ((ContinuousLinearMap.adjoint sys.continuousB).comp ((ContinuousLinearMap.adjoint (sys.expFlow s)))))
  have hcontL : Continuous L := continuous_controllabilityIntegrand sys
  have hIntL : IntervalIntegrable L volume (0 : ℝ) T := hcontL.intervalIntegrable _ _
  have happly : sys.controllabilityGramian T x = ∫ s in (0 : ℝ)..T, L s x := by
    rw [controllabilityGramian]
    exact ContinuousLinearMap.intervalIntegral_apply hIntL x
  have hcontLx : Continuous (fun s : ℝ => L s x) := hcontL.clm_apply continuous_const
  have hIntLx : IntervalIntegrable (fun s : ℝ => L s x) volume (0 : ℝ) T :=
    hcontLx.intervalIntegrable _ _
  rw [happly]
  rw [show inner ℝ x (∫ s in (0 : ℝ)..T, L s x) =
      (innerSL ℝ x) (∫ s in (0 : ℝ)..T, L s x) from rfl]
  rw [← (innerSL ℝ x).intervalIntegral_comp_comm hIntLx]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [L, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  rw [← ContinuousLinearMap.adjoint_inner_left (sys.expFlow s)
    (sys.continuousB ((ContinuousLinearMap.adjoint sys.continuousB) (((ContinuousLinearMap.adjoint (sys.expFlow s))) x))) x]
  rw [← ContinuousLinearMap.adjoint_inner_left sys.continuousB
    ((ContinuousLinearMap.adjoint sys.continuousB) (((ContinuousLinearMap.adjoint (sys.expFlow s))) x)) (((ContinuousLinearMap.adjoint (sys.expFlow s))) x)]
  rw [real_inner_self_eq_norm_sq]

omit [FiniteDimensional ℝ U] in
/-- The observability energy identity: the quadratic form of `W_o(T)` is the
integral of the squared norm `‖C exp(s A) x‖²`. -/
theorem inner_observabilityGramian (sys : LinearSystem ℝ X U Y) (T : ℝ) (x : X) :
    inner ℝ x (sys.observabilityGramian T x) =
      ∫ s in (0 : ℝ)..T, ‖sys.continuousC (sys.expFlow s x)‖ ^ 2 := by
  let L : ℝ → X →L[ℝ] X := fun s =>
    ((ContinuousLinearMap.adjoint (sys.expFlow s))).comp ((ContinuousLinearMap.adjoint sys.continuousC).comp (sys.continuousC.comp (sys.expFlow s)))
  have hcontL : Continuous L := continuous_observabilityIntegrand sys
  have hIntL : IntervalIntegrable L volume (0 : ℝ) T := hcontL.intervalIntegrable _ _
  have happly : sys.observabilityGramian T x = ∫ s in (0 : ℝ)..T, L s x := by
    rw [observabilityGramian]
    exact ContinuousLinearMap.intervalIntegral_apply hIntL x
  have hcontLx : Continuous (fun s : ℝ => L s x) := hcontL.clm_apply continuous_const
  have hIntLx : IntervalIntegrable (fun s : ℝ => L s x) volume (0 : ℝ) T :=
    hcontLx.intervalIntegrable _ _
  rw [happly]
  rw [show inner ℝ x (∫ s in (0 : ℝ)..T, L s x) =
      (innerSL ℝ x) (∫ s in (0 : ℝ)..T, L s x) from rfl]
  rw [← (innerSL ℝ x).intervalIntegral_comp_comm hIntLx]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [L, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  rw [ContinuousLinearMap.adjoint_inner_right (sys.expFlow s) x
    ((ContinuousLinearMap.adjoint sys.continuousC) (sys.continuousC (sys.expFlow s x)))]
  rw [ContinuousLinearMap.adjoint_inner_right sys.continuousC (sys.expFlow s x)
    (sys.continuousC (sys.expFlow s x))]
  rw [real_inner_self_eq_norm_sq]

/-! ### Positive semidefiniteness -/

omit [FiniteDimensional ℝ Y] in
/-- The controllability Gramian is positive semidefinite. -/
theorem controllabilityGramian_nonneg (sys : LinearSystem ℝ X U Y) {T : ℝ} (hT : 0 ≤ T)
    (x : X) : 0 ≤ inner ℝ x (sys.controllabilityGramian T x) := by
  rw [inner_controllabilityGramian]
  exact intervalIntegral.integral_nonneg hT fun s _ => sq_nonneg _

omit [FiniteDimensional ℝ U] in
/-- The observability Gramian is positive semidefinite. -/
theorem observabilityGramian_nonneg (sys : LinearSystem ℝ X U Y) {T : ℝ} (hT : 0 ≤ T)
    (x : X) : 0 ≤ inner ℝ x (sys.observabilityGramian T x) := by
  rw [inner_observabilityGramian]
  exact intervalIntegral.integral_nonneg hT fun s _ => sq_nonneg _

/-! ### Positive definiteness -/

/-- A continuous endomorphism of a real inner product space is positive definite when
its quadratic form is strictly positive on nonzero vectors. -/
def IsPositiveDefinite (T : X →L[ℝ] X) : Prop :=
  ∀ x : X, x ≠ 0 → 0 < inner ℝ x (T x)

/-! ### Adjoints of the exponential flow and the reachable subspace -/

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ Y] in
/-- The adjoint of the exponential flow is the exponential of the adjoint state map. -/
theorem adjoint_expFlow_eq (sys : LinearSystem ℝ X U Y) (s : ℝ) :
    (sys.expFlow s)† = NormedSpace.exp (s • (sys.continuousA)†) := by
  rw [← ContinuousLinearMap.star_eq_adjoint, expFlow, NormedSpace.star_exp]
  congr 1
  rw [star_smul, ContinuousLinearMap.star_eq_adjoint]
  simp

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ Y] in
/-- Evaluation of a power of the continuous state map agrees with the algebraic one. -/
theorem continuousA_pow_apply (sys : LinearSystem ℝ X U Y) (k : ℕ) (z : X) :
    (sys.continuousA ^ k) z = (sys.A ^ k) z := by
  change (((sys.continuousA ^ k : X →L[ℝ] X) : X →ₗ[ℝ] X)) z = (sys.A ^ k) z
  rw [ContinuousLinearMap.toLinearMap_pow]
  rfl

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ Y] in
/-- The adjoint of a power of the state map is the power of the adjoint. -/
theorem adjoint_continuousA_pow (sys : LinearSystem ℝ X U Y) (k : ℕ) :
    (sys.continuousA ^ k)† = ((sys.continuousA)†)^k := by
  rw [← ContinuousLinearMap.star_eq_adjoint (sys.continuousA ^ k), star_pow,
    ContinuousLinearMap.star_eq_adjoint]

omit [FiniteDimensional ℝ Y] in
/-- Membership in the orthogonal complement of the reachable subspace is equivalent to
the vanishing of all `B* (A*)^k x`. This is the inner-product form of the duality
between reachability and observability. -/
theorem mem_orthogonal_reachableSubspace_iff (sys : LinearSystem ℝ X U Y) (x : X) :
    x ∈ (LinearMap.reachableSubspace sys.A sys.B)ᗮ ↔
      ∀ k, ((sys.continuousB)†) ((((sys.continuousA)†)^k) x) = 0 := by
  constructor
  · intro hx k
    apply ext_inner_right ℝ
    intro u
    rw [ContinuousLinearMap.adjoint_inner_left]
    rw [← adjoint_continuousA_pow]
    rw [ContinuousLinearMap.adjoint_inner_left]
    simp only [inner_zero_left]
    rw [continuousB_apply]
    rw [continuousA_pow_apply]
    exact (Submodule.mem_orthogonal' (LinearMap.reachableSubspace sys.A sys.B) x).mp hx _
      (LinearMap.mem_reachableSubspace_of_mem sys.A sys.B k u)
  · intro h
    change x ∈ (⨆ k : ℕ, LinearMap.range ((sys.A ^ k).comp sys.B))ᗮ
    rw [← Submodule.iInf_orthogonal]
    rw [Submodule.mem_iInf]
    intro k
    rw [Submodule.mem_orthogonal']
    intro y hy
    obtain ⟨u, rfl⟩ := hy
    have hk := h k
    simp only [LinearMap.comp_apply]
    rw [← continuousA_pow_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left (sys.continuousA ^ k) (sys.B u) x]
    rw [adjoint_continuousA_pow]
    rw [← continuousB_apply]
    rw [← ContinuousLinearMap.adjoint_inner_left (sys.continuousB) u ((((sys.continuousA)†)^k) x)]
    rw [hk, inner_zero_left]

omit [FiniteDimensional ℝ Y] in
/-- The power series evaluation of `B* exp(s A*) x` vanishes when all `B* (A*)^k x` do. -/
theorem continuousB_adjoint_expFlow_adjoint_eq_zero_of_forall
    (sys : LinearSystem ℝ X U Y) {x : X}
    (h : ∀ k, ((sys.continuousB)†) ((((sys.continuousA)†)^k) x) = 0) (s : ℝ) :
    ((sys.continuousB)†) (((sys.expFlow s)†) x) = 0 := by
  rw [adjoint_expFlow_eq]
  have hsum := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (s • (sys.continuousA)†)
  have hmap := hsum.mapL (ContinuousLinearMap.apply ℝ X x)
  have hmap2 := hmap.mapL ((sys.continuousB)†)
  have hzero : (fun n : ℕ => ((sys.continuousB)†)
      ((((Nat.factorial n : ℝ))⁻¹ • (s • (sys.continuousA)†) ^ n) x)) =
      fun _ => (0 : U) := by
    funext n
    have hn : (s • (sys.continuousA)†) ^ n = s ^ n • ((sys.continuousA)†) ^ n := by
      rw [smul_pow]
    rw [hn]
    simp only [smul_apply, map_smul, h n, smul_zero]
  simp only [ContinuousLinearMap.apply_apply] at hmap2
  rw [hzero] at hmap2
  simpa using hmap2.tsum_eq.symm

omit [FiniteDimensional ℝ Y] in
/-- The transpose/dual system attached to `sys`: the state map is `A†`, the output map
is `B†`. -/
noncomputable def adjointSystem (sys : LinearSystem ℝ X U Y) : LinearSystem ℝ X Y U where
  A := (sys.continuousA)†.toLinearMap
  B := 0
  C := (sys.continuousB)†.toLinearMap
  D := 0

omit [FiniteDimensional ℝ Y] in
theorem adjointSystem_continuousA (sys : LinearSystem ℝ X U Y) :
    (adjointSystem sys).continuousA = (sys.continuousA)† := by
  change (((sys.continuousA)†.toLinearMap).toContinuousLinearMap) = (sys.continuousA)†
  rfl

omit [FiniteDimensional ℝ Y] in
theorem adjointSystem_continuousC (sys : LinearSystem ℝ X U Y) :
    (adjointSystem sys).continuousC = (sys.continuousB)† := by
  change (((sys.continuousB)†.toLinearMap).toContinuousLinearMap) = (sys.continuousB)†
  rfl

omit [FiniteDimensional ℝ Y] in
theorem adjointSystem_expFlow (sys : LinearSystem ℝ X U Y) (t : ℝ) :
    (adjointSystem sys).expFlow t = (sys.expFlow t)† := by
  rw [expFlow, adjointSystem_continuousA, ← adjoint_expFlow_eq]

omit [FiniteDimensional ℝ Y] in
/-- If the adjoint output `B* exp(t A*) x` vanishes on `[0,T]` for `T > 0`, then `x` is
orthogonal to the reachable subspace. This is the differentiation direction of the
duality between reachability and observability, proved on the adjoint system. -/
theorem mem_reachableSubspace_orthogonal_of_forall_adjoint_expFlow_eq_zero
    (sys : LinearSystem ℝ X U Y) {x : X} {T : ℝ} (hT : 0 < T)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, ((sys.continuousB)†) (((sys.expFlow t)†) x) = 0) :
    x ∈ (LinearMap.reachableSubspace sys.A sys.B)ᗮ := by
  rw [mem_orthogonal_reachableSubspace_iff]
  have h' : ∀ t ∈ Set.Icc (0 : ℝ) T, (adjointSystem sys).continuousC
      ((adjointSystem sys).expFlow t x) = 0 := by
    intro t ht
    rw [adjointSystem_continuousC, adjointSystem_expFlow]
    exact h t ht
  have hmem := mem_unobservableSubspace_of_forall_continuousC_expFlow_eq_zero
    (adjointSystem sys) hT h'
  rw [LinearMap.mem_unobservableSubspace] at hmem
  intro k
  have hmemk := hmem k
  change (sys.continuousB)†.toLinearMap ((((sys.continuousA)†.toLinearMap)^k) x) = 0 at hmemk
  rw [← ContinuousLinearMap.toLinearMap_pow ((sys.continuousA)†) k] at hmemk
  exact hmemk

/-! ### Energy identities: the bilinear/adjoint forms -/

omit [FiniteDimensional ℝ Y] in
/-- The variation-of-constants solution at zero initial state as the transported forcing
integral `∫₀ᵀ exp((T - s) A) B u(s) ds`. -/
theorem variationOfConstants_zero_integral (sys : LinearSystem ℝ X U Y) {u : ℝ → U}
    (hu : LocallyIntegrable u volume) (T : ℝ) :
    sys.variationOfConstants 0 0 u T =
      ∫ s in (0 : ℝ)..T, sys.expFlow (T - s) (sys.continuousB (u s)) := by
  rw [variationOfConstants_zero_eq]
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm (sys.expFlow T)
    (intervalIntegrable_forcing sys 0 hu 0 T)]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [forcing, sub_zero]
  change (sys.expFlow T * sys.expFlow (-s)) (sys.continuousB (u s)) =
    sys.expFlow (T - s) (sys.continuousB (u s))
  rw [← expFlow_add]
  congr 1

omit [FiniteDimensional ℝ Y] in
/-- The inner product of the state with the exponential of the forcing vanishes whenever
`x` is orthogonal to the reachable subspace. -/
theorem inner_expFlow_forcing_eq_zero (sys : LinearSystem ℝ X U Y) {x : X}
    (hk : ∀ k, ((sys.continuousB)†) ((((sys.continuousA)†)^k) x) = 0)
    (u : ℝ → U) (T s : ℝ) :
    inner ℝ x (sys.expFlow T (sys.forcing 0 u s)) = 0 := by
  have hstep : sys.expFlow T (sys.forcing 0 u s) =
      sys.expFlow (T - s) (sys.continuousB (u s)) := by
    simp only [forcing, sub_zero]
    change (sys.expFlow T * sys.expFlow (-s)) (sys.continuousB (u s)) =
      sys.expFlow (T - s) (sys.continuousB (u s))
    rw [← expFlow_add]
    congr 1
  rw [hstep]
  rw [← ContinuousLinearMap.adjoint_inner_left (sys.expFlow (T - s))
    (sys.continuousB (u s)) x]
  rw [← ContinuousLinearMap.adjoint_inner_left (sys.continuousB) (u s)
    (((sys.expFlow (T - s))†) x)]
  rw [continuousB_adjoint_expFlow_adjoint_eq_zero_of_forall sys hk (T - s), inner_zero_left]

/-! ### The reachable set and the algebraic reachable subspace -/

omit [FiniteDimensional ℝ Y] in
/-- Every point of the finite-horizon reachable set lies in the algebraic reachable
subspace. The proof uses the duality between reachability and observability: an element
orthogonal to the reachable subspace is annihilated by every `B* exp(s A*)`. -/
theorem reachableSetAtSubmodule_le_reachableSubspace (sys : LinearSystem ℝ X U Y) (T : ℝ) :
    sys.reachableSetAtSubmodule T ≤ LinearMap.reachableSubspace sys.A sys.B := by
  have h : (LinearMap.reachableSubspace sys.A sys.B)ᗮ ≤
      (sys.reachableSetAtSubmodule T)ᗮ := by
    intro x hx
    rw [Submodule.mem_orthogonal']
    intro y hy
    rw [mem_reachableSetAtSubmodule] at hy
    obtain ⟨u, hu, rfl⟩ := hy
    have hk := (mem_orthogonal_reachableSubspace_iff sys x).mp hx
    rw [variationOfConstants_zero_eq]
    rw [← ContinuousLinearMap.adjoint_inner_left (sys.expFlow T)
      (∫ s in (0 : ℝ)..T, sys.forcing 0 u s) x]
    change (innerSL ℝ (E := X) (((sys.expFlow T)†) x))
      (∫ s in (0 : ℝ)..T, sys.forcing 0 u s) = 0
    rw [← (innerSL ℝ (E := X) (((sys.expFlow T)†) x)).intervalIntegral_comp_comm
      (intervalIntegrable_forcing sys 0 hu 0 T)]
    simp only [innerSL_apply_apply]
    have hzero : (fun s : ℝ => inner ℝ (((sys.expFlow T)†) x) (sys.forcing 0 u s)) =
        fun _ => (0 : ℝ) := by
      funext s
      rw [ContinuousLinearMap.adjoint_inner_left (sys.expFlow T) (sys.forcing 0 u s) x]
      exact inner_expFlow_forcing_eq_zero sys hk u T s
    rw [hzero, intervalIntegral.integral_zero]
  rw [← Submodule.orthogonal_orthogonal (sys.reachableSetAtSubmodule T),
    ← Submodule.orthogonal_orthogonal (LinearMap.reachableSubspace sys.A sys.B)]
  exact Submodule.orthogonal_le h

omit [FiniteDimensional ℝ Y] in
/-- The range of the controllability Gramian is contained in the finite-horizon reachable
set. The realizing input is `s ↦ B* exp((T - s) A)* z`. -/
theorem controllabilityGramian_mem_reachableSetAt (sys : LinearSystem ℝ X U Y) (T : ℝ)
    (z : X) : sys.controllabilityGramian T z ∈ sys.reachableSetAtSubmodule T := by
  let u : ℝ → U := fun s => ((sys.continuousB)†) (((sys.expFlow (T - s))†) z)
  have hcontu : Continuous u := by
    have hE : Continuous (fun t : ℝ => sys.expFlow t) := by
      simpa using continuous_expFlow_sub sys 0
    have hcontE : Continuous (fun s : ℝ => (sys.expFlow (T - s))†) :=
      ContinuousLinearMap.adjoint.continuous.comp
        (hE.comp (continuous_const.sub continuous_id))
    exact ((sys.continuousB)†).continuous.comp (hcontE.clm_apply continuous_const)
  refine ⟨u, hcontu.locallyIntegrable, ?_⟩
  rw [variationOfConstants_zero_integral sys hcontu.locallyIntegrable T]
  have hrefl : (∫ s in (0 : ℝ)..T,
        sys.expFlow (T - s) (sys.continuousB (((sys.continuousB)†) (((sys.expFlow (T - s))†) z)))) =
      ∫ s in (0 : ℝ)..T,
        sys.expFlow s (sys.continuousB (((sys.continuousB)†) (((sys.expFlow s)†) z))) := by
    have h := intervalIntegral.integral_comp_sub_left
      (f := fun r : ℝ => sys.expFlow r (sys.continuousB (((sys.continuousB)†) (((sys.expFlow r)†) z))))
      (a := (0 : ℝ)) (b := T) T
    simpa using h
  rw [hrefl]
  rw [controllabilityGramian, ContinuousLinearMap.intervalIntegral_apply
    ((continuous_controllabilityIntegrand sys).intervalIntegrable _ _) z]
  rfl

/-! ### The kernel of the controllability Gramian -/

omit [FiniteDimensional ℝ Y] in
/-- If the quadratic form of the controllability Gramian vanishes, then the state is
orthogonal to the reachable subspace. -/
theorem mem_orthogonal_of_inner_controllabilityGramian_eq_zero
    (sys : LinearSystem ℝ X U Y) {T : ℝ} (hT : 0 < T) {x : X}
    (h : inner ℝ x (sys.controllabilityGramian T x) = 0) :
    x ∈ (LinearMap.reachableSubspace sys.A sys.B)ᗮ := by
  rw [inner_controllabilityGramian] at h
  have hcontE : Continuous (fun s : ℝ => (sys.expFlow s)†) :=
    ContinuousLinearMap.adjoint.continuous.comp (by simpa using continuous_expFlow_sub sys 0)
  have hcont : Continuous
      (fun s : ℝ => ‖((sys.continuousB)†) (((sys.expFlow s)†) x)‖ ^ 2) :=
    (((sys.continuousB)†).continuous.comp (hcontE.clm_apply continuous_const)).norm.pow 2
  have hInt : IntervalIntegrable
      (fun s : ℝ => ‖((sys.continuousB)†) (((sys.expFlow s)†) x)‖ ^ 2) volume (0 : ℝ) T :=
    hcont.intervalIntegrable _ _
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) T)]
      (fun s : ℝ => ‖((sys.continuousB)†) (((sys.expFlow s)†) x)‖ ^ 2) :=
    Eventually.of_forall fun s => sq_nonneg _
  have hae : (fun s : ℝ => ‖((sys.continuousB)†) (((sys.expFlow s)†) x)‖ ^ 2) =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) T)] 0 :=
    (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hT.le hnonneg hInt).mp h
  have haeIcc : (fun s : ℝ => ‖((sys.continuousB)†) (((sys.expFlow s)†) x)‖ ^ 2) =ᵐ[
      volume.restrict (Set.Icc (0 : ℝ) T)] 0 := by
    rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
    exact hae
  have hEq := Measure.eqOn_Icc_of_ae_eq (μ := volume) hT.ne haeIcc
    hcont.continuousOn continuousOn_const
  refine mem_reachableSubspace_orthogonal_of_forall_adjoint_expFlow_eq_zero sys hT ?_
  intro s hs
  have hs0 : ‖((sys.continuousB)†) (((sys.expFlow s)†) x)‖ = 0 :=
    sq_eq_zero_iff.mp (by simpa using hEq hs)
  exact norm_eq_zero.mp hs0

omit [FiniteDimensional ℝ Y] in
/-- The kernel of the controllability Gramian is the orthogonal complement of the
reachable subspace. -/
theorem ker_controllabilityGramian (sys : LinearSystem ℝ X U Y) {T : ℝ} (hT : 0 < T) (x : X) :
    x ∈ LinearMap.ker (sys.controllabilityGramian T).toLinearMap ↔
      x ∈ (LinearMap.reachableSubspace sys.A sys.B)ᗮ := by
  constructor
  · intro hx
    rw [LinearMap.mem_ker] at hx
    have henergy : inner ℝ x (sys.controllabilityGramian T x) = 0 := by
      change inner ℝ x ((sys.controllabilityGramian T).toLinearMap x) = 0
      rw [hx, inner_zero_right]
    exact mem_orthogonal_of_inner_controllabilityGramian_eq_zero sys hT henergy
  · intro hx
    rw [LinearMap.mem_ker]
    change (sys.controllabilityGramian T) x = 0
    have hk := (mem_orthogonal_reachableSubspace_iff sys x).mp hx
    rw [controllabilityGramian, ContinuousLinearMap.intervalIntegral_apply
      ((continuous_controllabilityIntegrand sys).intervalIntegrable _ _) x]
    have hfun : (fun s : ℝ =>
        (sys.expFlow s).comp (sys.continuousB.comp ((ContinuousLinearMap.adjoint sys.continuousB).comp
          ((ContinuousLinearMap.adjoint (sys.expFlow s))))) x) = fun _ => (0 : X) := by
      funext s
      simp only [ContinuousLinearMap.comp_apply]
      rw [continuousB_adjoint_expFlow_adjoint_eq_zero_of_forall sys hk s, map_zero, map_zero]
    rw [hfun, intervalIntegral.integral_zero]

omit [FiniteDimensional ℝ Y] in
/-- On every strictly positive horizon the finite-horizon reachable set is exactly the
algebraic reachable subspace. This is the trajectory/algebraic equivalence of
Trentelman–Stoorvogel–Hautus, Corollary 3.2 and Corollary 3.4. -/
theorem reachableSetAt_eq_reachableSubspace (sys : LinearSystem ℝ X U Y) {T : ℝ} (hT : 0 < T) :
    sys.reachableSetAtSubmodule T = LinearMap.reachableSubspace sys.A sys.B := by
  refine le_antisymm (reachableSetAtSubmodule_le_reachableSubspace sys T) ?_
  have hker_eq : LinearMap.ker (sys.controllabilityGramian T).toLinearMap =
      (LinearMap.reachableSubspace sys.A sys.B)ᗮ := by
    ext x
    exact ker_controllabilityGramian sys hT x
  have hle : (sys.controllabilityGramian T).range ≤
      LinearMap.reachableSubspace sys.A sys.B := by
    intro y hy
    obtain ⟨z, rfl⟩ := hy
    exact reachableSetAtSubmodule_le_reachableSubspace sys T
      (controllabilityGramian_mem_reachableSetAt sys T z)
  have hdim : Module.finrank ℝ (sys.controllabilityGramian T).range =
      Module.finrank ℝ (LinearMap.reachableSubspace sys.A sys.B) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker
      (f := (sys.controllabilityGramian T).toLinearMap)
    have h2 := Submodule.finrank_add_finrank_orthogonal
      (K := LinearMap.reachableSubspace sys.A sys.B)
    rw [hker_eq] at h1
    omega
  have heq : (sys.controllabilityGramian T).range =
      LinearMap.reachableSubspace sys.A sys.B :=
    Submodule.eq_of_le_of_finrank_eq hle hdim
  rw [← heq]
  intro y hy
  obtain ⟨z, rfl⟩ := hy
  exact controllabilityGramian_mem_reachableSetAt sys T z

omit [FiniteDimensional ℝ Y] in
/-- Set-level form of the reachability equivalence: for a strictly positive horizon the
states reachable from the origin are exactly the algebraic reachable subspace. -/
theorem reachableSetAt_eq_reachableSubspace_set (sys : LinearSystem ℝ X U Y) {T : ℝ}
    (hT : 0 < T) :
    sys.reachableSetAt T = (LinearMap.reachableSubspace sys.A sys.B : Set X) := by
  rw [← reachableSetAt_eq_reachableSubspace sys hT]
  rfl

/-! ### Positive-definiteness criteria -/

omit [FiniteDimensional ℝ Y] in
/-- The controllability Gramian is positive definite on a strictly positive horizon
exactly when the pair `(A, B)` is controllable. -/
theorem controllabilityGramian_posDef_iff_isControllable
    (sys : LinearSystem ℝ X U Y) {T : ℝ} (hT : 0 < T) :
    IsPositiveDefinite (sys.controllabilityGramian T) ↔
      LinearMap.IsControllable sys.A sys.B := by
  constructor
  · intro hpd
    rw [LinearMap.isControllable_iff]
    by_contra hne
    have hneOrth : (LinearMap.reachableSubspace sys.A sys.B)ᗮ ≠ ⊥ := by
      intro h
      apply hne
      rw [← Submodule.orthogonal_orthogonal (LinearMap.reachableSubspace sys.A sys.B), h,
        Submodule.bot_orthogonal_eq_top]
    obtain ⟨x, hxmem, hxne⟩ := (Submodule.ne_bot_iff _).mp hneOrth
    have hzero : inner ℝ x (sys.controllabilityGramian T x) = 0 := by
      rw [inner_controllabilityGramian]
      have hk := (mem_orthogonal_reachableSubspace_iff sys x).mp hxmem
      have hterm : ∀ s : ℝ,
          ((sys.continuousB)†) (((sys.expFlow s)†) x) = 0 :=
        fun s => continuousB_adjoint_expFlow_adjoint_eq_zero_of_forall sys hk s
      simp [hterm]
    have := hpd x hxne
    rw [hzero] at this
    exact lt_irrefl 0 this
  · intro hcontr x hxne
    rcases lt_or_eq_of_le (controllabilityGramian_nonneg sys hT.le x) with hlt | heq
    · exact hlt
    · exfalso
      have hxorth := mem_orthogonal_of_inner_controllabilityGramian_eq_zero sys hT heq.symm
      rw [hcontr, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at hxorth
      exact hxne hxorth

omit [FiniteDimensional ℝ U] in
/-- The observability Gramian is positive definite on a strictly positive horizon exactly
when the pair `(C, A)` is observable. -/
theorem observabilityGramian_posDef_iff_isObservable
    (sys : LinearSystem ℝ X U Y) {T : ℝ} (hT : 0 < T) :
    IsPositiveDefinite (sys.observabilityGramian T) ↔
      LinearMap.IsObservable sys.C sys.A := by
  constructor
  · intro hpd
    rw [LinearMap.isObservable_iff, Submodule.eq_bot_iff]
    intro x hx
    by_contra hxne
    have hzero : inner ℝ x (sys.observabilityGramian T x) = 0 := by
      rw [inner_observabilityGramian]
      have hterm : ∀ s : ℝ, sys.continuousC (sys.expFlow s x) = 0 :=
        fun s => continuousC_expFlow_eq_zero_of_mem_unobservableSubspace sys hx s
      simp [hterm]
    have := hpd x hxne
    rw [hzero] at this
    exact lt_irrefl 0 this
  · intro hobs x hxne
    rw [LinearMap.isObservable_iff] at hobs
    rw [inner_observabilityGramian]
    have hnot : ¬ ∀ t ∈ Set.Icc (0 : ℝ) T, sys.continuousC (sys.expFlow t x) = 0 := by
      intro hall
      have hxmem : x ∈ LinearMap.unobservableSubspace sys.C sys.A :=
        mem_unobservableSubspace_of_forall_continuousC_expFlow_eq_zero sys hT hall
      rw [hobs, Submodule.mem_bot] at hxmem
      exact hxne hxmem
    push Not at hnot
    obtain ⟨c, hc, hcne⟩ := hnot
    have hE : Continuous (fun s : ℝ => sys.expFlow s) := by
      simpa using continuous_expFlow_sub sys 0
    have hcontE : Continuous (fun s : ℝ => sys.expFlow s x) :=
      hE.clm_apply continuous_const
    have hcont : Continuous (fun s : ℝ => ‖sys.continuousC (sys.expFlow s x)‖ ^ 2) :=
      (sys.continuousC.continuous.comp hcontE).norm.pow 2
    have hpos : 0 < ‖sys.continuousC (sys.expFlow c x)‖ ^ 2 :=
      sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hcne)
    exact intervalIntegral.integral_pos hT hcont.continuousOn
      (fun s _ => sq_nonneg _) ⟨c, hc, hpos⟩

end LinearSystem

namespace LinearSystem.Examples

open EuclideanSpace

/-- The scalar integrator `x' = u`, `y = x` on `EuclideanSpace ℝ (Fin 1)`. It is the
smallest concrete Euclidean system exhibiting the Gramian criteria. -/
noncomputable def scalarIntegrator :
    LinearSystem ℝ (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))
      (EuclideanSpace ℝ (Fin 1)) where
  A := 0
  B := LinearMap.id
  C := LinearMap.id
  D := 0

/-- The scalar integrator is controllable. -/
theorem scalarIntegrator_controllable :
    LinearMap.IsControllable scalarIntegrator.A scalarIntegrator.B := by
  rw [LinearMap.isControllable_iff, eq_top_iff]
  intro x _
  simpa [scalarIntegrator] using
    (LinearMap.mem_reachableSubspace_of_mem scalarIntegrator.A scalarIntegrator.B 0 x)

/-- The scalar integrator is observable. -/
theorem scalarIntegrator_observable :
    LinearMap.IsObservable scalarIntegrator.C scalarIntegrator.A := by
  rw [LinearMap.isObservable_iff, eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_unobservableSubspace] at hx
  simpa [scalarIntegrator] using hx 0

/-- Euclidean regression: on the scalar integrator the controllability Gramian is positive
definite on every strictly positive horizon. -/
example (T : ℝ) (hT : 0 < T) :
    IsPositiveDefinite (scalarIntegrator.controllabilityGramian T) :=
  (controllabilityGramian_posDef_iff_isControllable scalarIntegrator hT).mpr
    scalarIntegrator_controllable

/-- Euclidean regression: on the scalar integrator the observability Gramian is positive
definite on every strictly positive horizon. -/
example (T : ℝ) (hT : 0 < T) :
    IsPositiveDefinite (scalarIntegrator.observabilityGramian T) :=
  (observabilityGramian_posDef_iff_isObservable scalarIntegrator hT).mpr
    scalarIntegrator_observable

end LinearSystem.Examples
