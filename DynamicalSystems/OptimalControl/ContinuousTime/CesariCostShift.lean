/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.CesariMovingInterval
public import Mathlib.Analysis.Normed.Affine.Isometry

/-!
# Cost translation preserves the weak Cesari property

The weak Cesari property compares state fibers at a fixed time. Translating the
cost coordinate by an arbitrary time-dependent lower bound therefore preserves
it, even when that lower bound is merely measurable. This is the property (Q)
part of the integrable lower-cost shift in BM Theorem 5.4.4.
-/

@[expose] public section

open Set

namespace OptimalControl

/-- Applying an affine isometry to each epigraph fiber preserves property (Q).
The proof transports closed convex hulls and the Cesari core through the actual
invertible continuous affine map. -/
theorem hasWeakCesariProperty_image_affineIsometryEquiv
    {T E F : Type*} [PseudoMetricSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Q : T → E → Set F) (t : T) (x : E) (e : F ≃ᵃⁱ[ℝ] F)
    (hcesari : HasWeakCesariProperty Q t x) :
    HasWeakCesariProperty (fun s y ↦ e '' Q s y) t x := by
  have htube (δ : ℝ) : cesariTube (fun s y ↦ e '' Q s y) t x δ =
      e '' cesariTube Q t x δ := by
    simp only [cesariTube, image_iUnion]
  have hhull (δ : ℝ) : cesariHull (fun s y ↦ e '' Q s y) t x δ =
      e '' cesariHull Q t x δ := by
    unfold cesariHull
    rw [htube]
    change closure (convexHull ℝ (e.toAffineEquiv.toAffineMap '' cesariTube Q t x δ)) = _
    rw [← e.toAffineEquiv.toAffineMap.image_convexHull]
    exact e.toHomeomorph.isClosedMap.closure_image_eq_of_continuous
      e.toHomeomorph.continuous _
  intro p hp
  have hcore : e.symm p ∈ cesariCore Q t x := by
    apply (mem_cesariCore_iff Q t x _).mpr
    intro δ hδ
    have h := (mem_cesariCore_iff _ t x p).mp hp δ hδ
    rw [hhull] at h
    obtain ⟨q, hq, rfl⟩ := h
    simpa using hq
  exact ⟨e.symm p, hcesari hcore, e.apply_symm_apply p⟩

/-- Subtract a time-dependent lower bound from the cost coordinate. -/
def shiftedVelocityCostSet {T E : Type*} (Q : T → E → Set (E × ℝ)) (β : T → ℝ) :
    T → E → Set (E × ℝ) :=
  fun t x ↦ (fun p : E × ℝ ↦ (p.1, p.2 - β t)) '' Q t x

/-- An arbitrary time-dependent cost shift preserves weak property (Q): the
translation is constant across all state fibers at the time under consideration.
No continuity assumption on the lower-bound function is needed. -/
theorem hasWeakCesariProperty_shiftedVelocityCostSet
    {T E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Q : T → E → Set (E × ℝ)) (β : T → ℝ) (t : T) (x : E)
    (hcesari : HasWeakCesariProperty Q t x) :
    HasWeakCesariProperty (shiftedVelocityCostSet Q β) t x := by
  let e := AffineIsometryEquiv.constVAdd ℝ (E × ℝ) (0, -β t)
  have h := hasWeakCesariProperty_image_affineIsometryEquiv Q t x e hcesari
  apply (hasWeakCesariProperty_congr_at_time (shiftedVelocityCostSet Q β)
    (fun s y ↦ e '' Q s y) t x ?_).mpr h
  funext y
  unfold shiftedVelocityCostSet
  congr 1
  funext p
  change (p.1, p.2 - β t) = (0, -β t) + p
  ext <;> simp [sub_eq_add_neg, add_comm]

end OptimalControl
