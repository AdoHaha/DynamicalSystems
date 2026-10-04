/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.FrameComplement
public import DynamicalSystems.Control.Geometric.FlowCommutator
public import DynamicalSystems.Control.Geometric.FlowRegularity
public import Mathlib.Data.List.FinRange

/-! # Finite compositions of local flows

The classical simultaneous rectification map is a finite composition of local flows,
starting on a complementary affine slice. Its derivative at the origin is the direct sum
of the vector-field frame and the inclusion of the slice.

References: Krener, *Differential Geometric Methods in Nonlinear Control*, Encyclopedia of
Systems and Control, 2nd ed.; Sontag, *Mathematical Control Theory*, Ch. 4 §4.2.
-/

@[expose] public section

open Set Filter
open scoped Topology BigOperators

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  {k : ℕ} {f : Fin k → X → X} {x₀ : X}

/-- Read one time coordinate in the product of time and transverse coordinates. -/
noncomputable def flowTimeCoordinate (i : Fin k) : ((Fin k → ℝ) × Y) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ (Fin k → ℝ) Y)

@[simp] theorem flowTimeCoordinate_apply (i : Fin k) (p : (Fin k → ℝ) × Y) :
    flowTimeCoordinate i p = p.1 i := rfl

/-- Apply the listed flows, with the first listed flow applied last. -/
noncomputable def localFlowCompose (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀)
    (ι : Y →L[ℝ] X) : List (Fin k) → ((Fin k → ℝ) × Y) → X
  | [], p => x₀ + ι p.2
  | i :: l, p => localFlow (hf i) (p.1 i) (localFlowCompose hf ι l p)

@[simp] theorem localFlowCompose_zero (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀)
    (ι : Y →L[ℝ] X) (l : List (Fin k)) : localFlowCompose hf ι l 0 = x₀ := by
  induction l with
  | nil => simp [localFlowCompose]
  | cons i l ih =>
    simp only [localFlowCompose, Prod.fst_zero, Pi.zero_apply, ih]
    exact localFlow_zero_apply (f i) x₀ (hf i)

/-- The linearization of a finite flow composition at zero. -/
noncomputable def localFlowComposeLinear (v : Fin k → X) (ι : Y →L[ℝ] X) :
    List (Fin k) → ((Fin k → ℝ) × Y) →L[ℝ] X
  | [] => ι.comp (ContinuousLinearMap.snd ℝ (Fin k → ℝ) Y)
  | i :: l => localFlowComposeLinear v ι l + (flowTimeCoordinate i).smulRight (v i)

omit [CompleteSpace X] in
theorem localFlowComposeLinear_apply (v : Fin k → X) (ι : Y →L[ℝ] X)
    (l : List (Fin k)) (p : (Fin k → ℝ) × Y) :
    localFlowComposeLinear v ι l p = (l.map (fun i => p.1 i • v i)).sum + ι p.2 := by
  induction l with
  | nil => simp [localFlowComposeLinear]
  | cons i l ih =>
    simp only [localFlowComposeLinear, add_apply,
      ContinuousLinearMap.smulRight_apply, flowTimeCoordinate_apply, ih,
      List.map_cons, List.sum_cons]
    abel

/-- The strict derivative of a finite composition of local flows at its base point. -/
theorem localFlowCompose_hasStrictFDerivAt
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀) (ι : Y →L[ℝ] X) (l : List (Fin k)) :
    HasStrictFDerivAt (localFlowCompose hf ι l)
      (localFlowComposeLinear (fun i => f i x₀) ι l) 0 := by
  induction l with
  | nil =>
    exact (ι.comp (ContinuousLinearMap.snd ℝ (Fin k → ℝ) Y)).hasStrictFDerivAt.const_add x₀
  | cons i l ih =>
    have hp := (flowTimeCoordinate (Y := Y) i).hasStrictFDerivAt.prodMk ih
    have hzero : (flowTimeCoordinate (Y := Y) i 0, localFlowCompose hf ι l 0) =
        (0, x₀) := by simp
    have houter := flowStrictFDerivAt (hf i)
    rw [← hzero] at houter
    apply (houter.comp 0 hp).congr_fderiv
    apply ContinuousLinearMap.ext
    intro p
    simp [localFlowComposeLinear]

/-- A finite composition of the chosen flows is continuously differentiable near zero. -/
theorem localFlowCompose_contDiffAt [FiniteDimensional ℝ X]
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀) (ι : Y →L[ℝ] X) (l : List (Fin k)) :
    ContDiffAt ℝ 1 (localFlowCompose hf ι l) 0 := by
  induction l with
  | nil =>
    exact contDiffAt_const.add
      (ι.comp (ContinuousLinearMap.snd ℝ (Fin k → ℝ) Y)).contDiff.contDiffAt
  | cons i l ih =>
    have hp := (flowTimeCoordinate (Y := Y) i).contDiff.contDiffAt.prodMk ih
    have hzero : (flowTimeCoordinate (Y := Y) i 0, localFlowCompose hf ι l 0) =
        (0, x₀) := by simp
    have houter := contDiffAt_localFlow_joint (hf i)
    rw [← hzero] at houter
    exact houter.comp 0 hp

/-- The map obtained by flowing once along each field from the complementary slice. -/
noncomputable def simultaneousRectifyingMap [FiniteDimensional ℝ X]
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀) :
    ((Fin k → ℝ) × ↥(frameComplement (fun i => f i x₀))) → X :=
  localFlowCompose hf (frameComplement (fun i => f i x₀)).subtypeL (List.finRange k)

@[simp] theorem simultaneousRectifyingMap_zero [FiniteDimensional ℝ X]
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀) : simultaneousRectifyingMap hf 0 = x₀ :=
  localFlowCompose_zero hf _ _

/-- The simultaneous flow map is `C¹` on a neighborhood of zero. -/
theorem simultaneousRectifyingMap_contDiffAt [FiniteDimensional ℝ X]
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀) :
    ContDiffAt ℝ 1 (simultaneousRectifyingMap hf) 0 :=
  localFlowCompose_contDiffAt hf _ _

/-- Linear independence makes the derivative of the simultaneous map invertible. -/
theorem simultaneousRectifyingMap_hasStrictFDerivAt [FiniteDimensional ℝ X]
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀)
    (hind : LinearIndependent ℝ (fun i => f i x₀)) :
    HasStrictFDerivAt (simultaneousRectifyingMap hf)
      (frameEquiv (fun i => f i x₀) hind).toContinuousLinearMap 0 := by
  apply (localFlowCompose_hasStrictFDerivAt hf _ _).congr_fderiv
  apply ContinuousLinearMap.ext
  intro p
  simp only [localFlowComposeLinear_apply, ← List.ofFn_eq_map, List.sum_ofFn,
    ContinuousLinearEquiv.coe_coe, frameEquiv_apply]
  rfl

/-- Every coordinate already included in a composition differentiates to its vector field.
Coordinates not yet included have zero derivative. The common neighborhood is chosen before
quantifying over the coordinate directions. -/
theorem eventually_localFlowCompose_fderiv [FiniteDimensional ℝ X]
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀) (ι : Y →L[ℝ] X)
    (hcomm : ∀ i j, ∀ᶠ x in 𝓝 x₀, lieBracket (f i) (f j) x = 0)
    (l : List (Fin k)) (hl : l.Nodup) :
    ∀ᶠ p : (Fin k → ℝ) × Y in 𝓝 0,
      DifferentiableAt ℝ (localFlowCompose hf ι l) p ∧
        ∀ i, fderiv ℝ (localFlowCompose hf ι l) p (Pi.single i 1, 0) =
          if i ∈ l then f i (localFlowCompose hf ι l p) else 0 := by
  classical
  induction l with
  | nil =>
    apply Eventually.of_forall
    intro p
    have hd : HasFDerivAt (localFlowCompose hf ι [])
        (ι.comp (ContinuousLinearMap.snd ℝ (Fin k → ℝ) Y)) p :=
      (ι.comp (ContinuousLinearMap.snd ℝ (Fin k → ℝ) Y)).hasFDerivAt.const_add x₀
    refine ⟨hd.differentiableAt, fun i => ?_⟩
    rw [hd.fderiv]
    simp
  | cons j l ih =>
    have hnodup := List.nodup_cons.mp hl
    have ht := ih hnodup.2
    have hpair : Tendsto (fun p : (Fin k → ℝ) × Y =>
        (p.1 j, localFlowCompose hf ι l p)) (𝓝 0) (𝓝 (0, x₀)) := by
      have h := ((flowTimeCoordinate (Y := Y) j).continuous.continuousAt.prodMk
        (localFlowCompose_hasStrictFDerivAt hf ι l).continuousAt).tendsto
      simpa only [flowTimeCoordinate_apply, localFlowCompose_zero,
        Prod.fst_zero, Pi.zero_apply] using h
    have hjet := hpair.eventually (eventually_hasFDerivAt_localFlow_joint (hf j))
    have hpush : ∀ᶠ p : (Fin k → ℝ) × Y in 𝓝 0, ∀ i,
        fderiv ℝ (localFlow (hf j) (p.1 j)) (localFlowCompose hf ι l p)
          (f i (localFlowCompose hf ι l p)) =
            f i (localFlow (hf j) (p.1 j) (localFlowCompose hf ι l p)) :=
      Filter.eventually_all.mpr fun i => hpair.eventually
        (eventually_fderiv_localFlow_apply (hf j) (hf i) (hcomm j i))
    filter_upwards [ht, hjet, hpush] with p hp hj hpres
    have hinner := (flowTimeCoordinate (Y := Y) j).hasFDerivAt.prodMk hp.1.hasFDerivAt
    have hder := hj.comp p hinner
    change HasFDerivAt (localFlowCompose hf ι (j :: l)) _ p at hder
    refine ⟨hder.differentiableAt, fun i => ?_⟩
    rw [hder.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      add_apply, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.coe_fst', flowTimeCoordinate_apply, hp.2 i]
    by_cases hij : i = j
    · subst i
      simp [hnodup.1, localFlowCompose]
    · by_cases hi : i ∈ l
      · simp [hi, hij, Ne.symm hij, hpres i, localFlowCompose]
      · simp [hi, hij, Ne.symm hij]

/-- On a neighborhood of zero, the simultaneous flow map sends each time coordinate
direction to the corresponding vector field. -/
theorem eventually_simultaneousRectifyingMap_fderiv [FiniteDimensional ℝ X]
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀)
    (hcomm : ∀ i j, ∀ᶠ x in 𝓝 x₀, lieBracket (f i) (f j) x = 0) :
    ∀ᶠ p : (Fin k → ℝ) × ↥(frameComplement (fun i => f i x₀)) in 𝓝 0,
      DifferentiableAt ℝ (simultaneousRectifyingMap hf) p ∧
        ∀ i, fderiv ℝ (simultaneousRectifyingMap hf) p (Pi.single i 1, 0) =
          f i (simultaneousRectifyingMap hf p) := by
  simpa only [simultaneousRectifyingMap, List.mem_finRange, ite_true] using
    eventually_localFlowCompose_fderiv hf _ hcomm (List.finRange k) (List.nodup_finRange k)

end
