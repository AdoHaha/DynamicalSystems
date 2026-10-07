/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Weak compactness of Hilbert balls and weak lower semicontinuity

* `WeakSpace` closed balls of a real Hilbert space are compact
  (Banach–Alaoglu transported along the Riesz isomorphism, realised as a homeomorphism
  `WeakSpace ℝ H ≃ₜ WeakDual ℝ H`).
* Convex norm-lower-semicontinuous functions (in particular `v ↦ ‖v - v₀‖²`) are weakly
  lower semicontinuous (Mazur, via `Convex.toWeakSpace_closure`).
* Direct method: a weakly lower semicontinuous function attains its minimum on a nonempty
  weakly compact set, specialised to balls of `Lp E 2 μ`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace DynamicalSystems.WeakL2

/-! ### Riesz homeomorphism between the weak topology and the weak-star topology -/

section Hilbert

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Riesz representation as a homeomorphism from the weak topology of a real Hilbert space to
the weak-star topology of its dual. -/
noncomputable def weakSpaceHomeomorphWeakDual : WeakSpace ℝ H ≃ₜ WeakDual ℝ H where
  toFun x := StrongDual.toWeakDual
    (InnerProductSpace.toDual ℝ H ((toWeakSpace ℝ H).symm x))
  invFun g := toWeakSpace ℝ H ((InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual g))
  left_inv x := by simp
  right_inv g := by simp
  continuous_toFun := by
    refine WeakDual.continuous_of_continuous_eval fun z => ?_
    exact (WeakBilin.eval_continuous (topDualPairing ℝ H).flip
      (InnerProductSpace.toDual ℝ H z)).congr fun x => by
        exact real_inner_comm _ _
  continuous_invFun := by
    refine WeakBilin.continuous_of_continuous_eval _ fun f => ?_
    refine (WeakBilin.eval_continuous (topDualPairing ℝ H)
      ((InnerProductSpace.toDual ℝ H).symm f)).congr fun g => ?_
    have key := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := H)
      (x := (InnerProductSpace.toDual ℝ H).symm f)
      (y := WeakDual.toStrongDual (show WeakDual ℝ H from g))
    have h1 : ∀ w : H, f w = inner ℝ ((InnerProductSpace.toDual ℝ H).symm f) w := fun w => by
      conv_lhs => rw [← (InnerProductSpace.toDual ℝ H).apply_symm_apply f]
      rfl
    change (show WeakDual ℝ H from g) ((InnerProductSpace.toDual ℝ H).symm f) =
      f ((InnerProductSpace.toDual ℝ H).symm
        (WeakDual.toStrongDual (show WeakDual ℝ H from g)))
    rw [h1, real_inner_comm]
    exact key.symm


/-- **Weak compactness of Hilbert balls** (Banach–Alaoglu transported along the Riesz
isomorphism): the closed ball of a real Hilbert space is compact in the weak topology. -/
theorem isCompact_toWeakSpace_image_closedBall (r : ℝ) :
    IsCompact (toWeakSpace ℝ H '' Metric.closedBall (0 : H) r) := by
  have h := (weakSpaceHomeomorphWeakDual H).isCompact_preimage.mpr
    (WeakDual.isCompact_closedBall (𝕜 := ℝ) (E := H) 0 r)
  convert h using 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [weakSpaceHomeomorphWeakDual] using hy
  · intro hx
    exact ⟨(toWeakSpace ℝ H).symm x, by simpa [weakSpaceHomeomorphWeakDual] using hx, by simp⟩

/-- Closed convex bounded subsets of a real Hilbert space are weakly compact. -/
theorem isCompact_toWeakSpace_image_of_convex_isClosed_isBounded {K : Set H}
    (hconv : Convex ℝ K) (hclosed : IsClosed K) (hbdd : Bornology.IsBounded K) :
    IsCompact (toWeakSpace ℝ H '' K) := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : H)).mp hbdd
  refine (isCompact_toWeakSpace_image_closedBall H r).of_isClosed_subset ?_
    (image_mono hr)
  rw [← closure_eq_iff_isClosed, ← hconv.toWeakSpace_closure (𝕜 := ℝ), hclosed.closure_eq]

end Hilbert

/-! ### Weak lower semicontinuity -/

section LowerSemicontinuity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Mazur-type lemma: a norm-lower-semicontinuous function with convex sublevel sets (in
particular any convex one) is lower semicontinuous for the weak topology. -/
theorem lowerSemicontinuous_weakSpace_of_convex_sublevel {f : E → ℝ}
    (hlsc : LowerSemicontinuous f) (hconv : ∀ r : ℝ, Convex ℝ {x | f x ≤ r}) :
    LowerSemicontinuous fun x : WeakSpace ℝ E => f ((toWeakSpace ℝ E).symm x) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro r
  have hcl : IsClosed {x | f x ≤ r} := by
    simpa [preimage] using (lowerSemicontinuous_iff_isClosed_preimage.1 hlsc r)
  have himg : (fun x : WeakSpace ℝ E => f ((toWeakSpace ℝ E).symm x)) ⁻¹' Iic r =
      toWeakSpace ℝ E '' {x | f x ≤ r} := by
    ext x
    simp only [mem_preimage, mem_Iic, mem_image, mem_ofPred_eq]
    exact ⟨fun h => ⟨(toWeakSpace ℝ E).symm x, h, by simp⟩, by
      rintro ⟨y, hy, rfl⟩; simpa using hy⟩
  rw [himg, ← closure_eq_iff_isClosed, ← (hconv r).toWeakSpace_closure (𝕜 := ℝ), hcl.closure_eq]

/-- A norm-lower-semicontinuous convex function is weakly lower semicontinuous. -/
theorem lowerSemicontinuous_weakSpace_of_convexOn {f : E → ℝ}
    (hlsc : LowerSemicontinuous f) (hconv : ConvexOn ℝ univ f) :
    LowerSemicontinuous fun x : WeakSpace ℝ E => f ((toWeakSpace ℝ E).symm x) :=
  lowerSemicontinuous_weakSpace_of_convex_sublevel hlsc fun r => by simpa using hconv.convex_le r

/-- The norm is weakly lower semicontinuous. -/
theorem lowerSemicontinuous_weakSpace_norm :
    LowerSemicontinuous fun x : WeakSpace ℝ E => ‖(toWeakSpace ℝ E).symm x‖ :=
  lowerSemicontinuous_weakSpace_of_convexOn continuous_norm.lowerSemicontinuous
    convexOn_univ_norm

/-- Weak lower semicontinuity of the squared distance to a fixed point, `v ↦ ‖v - v₀‖²`. -/
theorem lowerSemicontinuous_weakSpace_norm_sub_sq (v₀ : E) :
    LowerSemicontinuous fun x : WeakSpace ℝ E => ‖(toWeakSpace ℝ E).symm x - v₀‖ ^ 2 := by
  refine lowerSemicontinuous_weakSpace_of_convex_sublevel
    (f := fun x : E => ‖x - v₀‖ ^ 2) (by fun_prop : Continuous _).lowerSemicontinuous
    fun r => ?_
  by_cases hr : r < 0
  · have : {x : E | ‖x - v₀‖ ^ 2 ≤ r} = ∅ := by
      ext x; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le hr (sq_nonneg _)
    rw [this]; exact convex_empty
  · have : {x : E | ‖x - v₀‖ ^ 2 ≤ r} = Metric.closedBall v₀ (Real.sqrt r) := by
      ext x
      simp only [mem_ofPred_eq, Metric.mem_closedBall, dist_eq_norm]
      exact (Real.le_sqrt (norm_nonneg _) (not_lt.mp hr)).symm
    rw [this]; exact convex_closedBall _ _

/-- Sequential/filter form: if `u i ⇀ v` weakly along `l` and the norms are bounded above
eventually, then `‖v‖ ≤ liminf ‖u i‖`. -/
theorem norm_le_liminf_of_tendsto_weakSpace {ι : Type*} {l : Filter ι} [l.NeBot]
    {u : ι → E} {v : E}
    (hu : Tendsto (fun i => toWeakSpace ℝ E (u i)) l (𝓝 (toWeakSpace ℝ E v)))
    (hb : IsBoundedUnder (· ≤ ·) l fun i => ‖u i‖) :
    ‖v‖ ≤ liminf (fun i => ‖u i‖) l := by
  refine le_of_forall_lt fun c hc => ?_
  obtain ⟨c', hcc', hc'v⟩ := exists_between hc
  have hev := hu.eventually
    ((lowerSemicontinuous_weakSpace_norm (E := E)) (toWeakSpace ℝ E v) c' (by simpa using hc'v))
  refine lt_of_lt_of_le hcc' (le_liminf_of_le hb.isCoboundedUnder_ge ?_)
  filter_upwards [hev] with i hi using by simpa using hi.le

end LowerSemicontinuity

/-! ### Direct method -/

section DirectMethod

/-- **Direct method** on a real Hilbert space: a weakly lower semicontinuous function attains
its minimum on a nonempty norm-closed ball. -/
theorem exists_isMinOn_closedBall_of_lowerSemicontinuous_weakSpace
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {f : WeakSpace ℝ H → ℝ} (hf : LowerSemicontinuous f) {r : ℝ} (hr : 0 ≤ r) :
    ∃ v : H, ‖v‖ ≤ r ∧ ∀ w : H, ‖w‖ ≤ r → f (toWeakSpace ℝ H v) ≤ f (toWeakSpace ℝ H w) := by
  obtain ⟨a, ⟨v, hv, rfl⟩, hmin⟩ := hf.lowerSemicontinuousOn (s := _) |>.exists_isMinOn
    ((Metric.nonempty_closedBall.mpr hr).image _) (isCompact_toWeakSpace_image_closedBall H r)
  exact ⟨v, by simpa using hv, fun w hw => hmin ⟨w, by simpa using hw, rfl⟩⟩

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The squared `L²` norm is the integral of the squared pointwise norm. -/
theorem Lp_two_norm_sq_eq_integral (v : Lp E 2 μ) : ‖v‖ ^ 2 = ∫ a, ‖v a‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

omit [CompleteSpace E] in
/-- The `L²` ball described by the energy integral is the closed norm ball. -/
theorem integral_norm_sq_le_iff (v : Lp E 2 μ) {C : ℝ} (hC : 0 ≤ C) :
    ∫ a, ‖v a‖ ^ 2 ∂μ ≤ C ↔ ‖v‖ ≤ Real.sqrt C := by
  rw [← Lp_two_norm_sq_eq_integral, Real.le_sqrt (norm_nonneg _) hC]

/-- **Weak compactness of the `L²` energy ball.** -/
theorem isCompact_toWeakSpace_image_integral_norm_sq_le (C : ℝ) :
    IsCompact (toWeakSpace ℝ (Lp E 2 μ) ''
      {v : Lp E 2 μ | ∫ a, ‖v a‖ ^ 2 ∂μ ≤ C}) := by
  by_cases hC : 0 ≤ C
  · convert isCompact_toWeakSpace_image_closedBall (Lp E 2 μ) (Real.sqrt C) using 2
    ext v
    simpa using integral_norm_sq_le_iff v hC
  · have : {v : Lp E 2 μ | ∫ a, ‖v a‖ ^ 2 ∂μ ≤ C} = ∅ := by
      ext v
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le (not_le.mp hC) (integral_nonneg fun a => sq_nonneg _)
    rw [this]; simp

/-- **Direct-method corollary on `L²`.** A weakly lower semicontinuous functional attains its
minimum on the energy ball `{v | ∫ ‖v‖² ≤ C}`. -/
theorem exists_isMinOn_integral_norm_sq_le
    {f : WeakSpace ℝ (Lp E 2 μ) → ℝ} (hf : LowerSemicontinuous f) {C : ℝ} (hC : 0 ≤ C) :
    ∃ v : Lp E 2 μ, ∫ a, ‖v a‖ ^ 2 ∂μ ≤ C ∧
      ∀ w : Lp E 2 μ, ∫ a, ‖w a‖ ^ 2 ∂μ ≤ C →
        f (toWeakSpace ℝ (Lp E 2 μ) v) ≤ f (toWeakSpace ℝ (Lp E 2 μ) w) := by
  obtain ⟨v, hv, hmin⟩ := exists_isMinOn_closedBall_of_lowerSemicontinuous_weakSpace hf
    (Real.sqrt_nonneg C)
  exact ⟨v, (integral_norm_sq_le_iff v hC).mpr hv,
    fun w hw => hmin w ((integral_norm_sq_le_iff w hC).mp hw)⟩

/-- Minimising the squared `L²` distance to a reference function `v₀` over the energy ball
(weak lsc of `v ↦ ‖v - v₀‖²` plus weak compactness). -/
theorem exists_isMinOn_norm_sub_sq_integral_norm_sq_le (v₀ : Lp E 2 μ) {C : ℝ} (hC : 0 ≤ C) :
    ∃ v : Lp E 2 μ, ∫ a, ‖v a‖ ^ 2 ∂μ ≤ C ∧
      ∀ w : Lp E 2 μ, ∫ a, ‖w a‖ ^ 2 ∂μ ≤ C → ‖v - v₀‖ ^ 2 ≤ ‖w - v₀‖ ^ 2 := by
  simpa using exists_isMinOn_integral_norm_sq_le
    (lowerSemicontinuous_weakSpace_norm_sub_sq v₀) hC

end DirectMethod

end DynamicalSystems.WeakL2
