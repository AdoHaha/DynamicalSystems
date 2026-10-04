/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.Frobenius
public import DynamicalSystems.Control.Geometric.MultiFlow
public import DynamicalSystems.Control.Geometric.LocalDiffeomorph
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-! # Simultaneous rectification of commuting vector fields

A finite family of continuously differentiable vector fields, independent at a base point
and with pairwise vanishing brackets nearby, admits one chart straightening every field.
The construction composes the fixed chosen local flows on a complementary affine slice.
Uniform field preservation differentiates this composition without a flow-reordering step.
The chart is restricted so every required derivative identity holds throughout its source.

This is the classical Krener simultaneous rectification lemma. References: Krener,
*Differential Geometric Methods in Nonlinear Control*, Encyclopedia of Systems and Control,
2nd ed.; Sontag, *Mathematical Control Theory*, 2nd ed., Ch. 4 §4.2.
-/

@[expose] public section

open Set Filter
open scoped Topology

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [CompleteSpace X] [FiniteDimensional ℝ X]
  {k : ℕ} {f : Fin k → X → X} {x₀ : X}

omit [CompleteSpace X] [FiniteDimensional ℝ X] in
/-- The local bracket hypothesis in neighborhood-filter form. -/
theorem FlowsCommuteLocally.eventually_eq_zero {f g : X → X}
    (h : FlowsCommuteLocally f g x₀) : ∀ᶠ x in 𝓝 x₀, lieBracket f g x = 0 := by
  obtain ⟨U, hU, hbr⟩ := h
  filter_upwards [hU] with x hx using hbr x hx

/-- A simultaneous chart with source-wide continuous differentiability, invertible derivatives, and
the explicit derivative of its inverse. Its source discharges the local flow conditions. -/
theorem exists_simultaneousRectifyingChart
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀)
    (hind : LinearIndependent ℝ (fun i => f i x₀))
    (hcomm : ∀ i j, FlowsCommuteLocally (f i) (f j) x₀) :
    ∃ Ψ : OpenPartialHomeomorph
        ((Fin k → ℝ) × ↥(frameComplement (fun i => f i x₀))) X,
      (Ψ : _ → X) = simultaneousRectifyingMap hf ∧ 0 ∈ Ψ.source ∧
        (∀ p ∈ Ψ.source, ContDiffAt ℝ 1 Ψ p) ∧
        (∀ p ∈ Ψ.source, (fderiv ℝ Ψ p).IsInvertible) ∧
        (∀ i p, p ∈ Ψ.source → fderiv ℝ Ψ p (Pi.single i 1, 0) = f i (Ψ p)) ∧
        ∀ q ∈ Ψ.target, HasFDerivAt Ψ.symm (fderiv ℝ Ψ (Ψ.symm q)).inverse q := by
  have hgood := eventually_simultaneousRectifyingMap_fderiv hf
    (fun i j => (hcomm i j).eventually_eq_zero)
  have hdiff := hgood.mono fun _ hp => hp.1
  have hregular := (simultaneousRectifyingMap_contDiffAt hf).eventually (by simp)
  obtain ⟨Ψ, hcoe, hzero, hsub, hdiffΨ, hinv, hsymm⟩ :=
    (simultaneousRectifyingMap_hasStrictFDerivAt hf hind).exists_local_differentiable_chart
      hdiff (hregular.and hgood)
  refine ⟨Ψ, hcoe, hzero, ?_, hinv, ?_, hsymm⟩
  · intro p hp
    simpa only [hcoe] using (hsub hp).1
  · intro i p hp
    simpa only [hcoe] using (hsub hp).2.2 i

/-- The simultaneous rectifying chart, restricted to a common valid neighborhood. -/
noncomputable def simultaneousRectifyingChart
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀)
    (hind : LinearIndependent ℝ (fun i => f i x₀))
    (hcomm : ∀ i j, FlowsCommuteLocally (f i) (f j) x₀) :
    OpenPartialHomeomorph ((Fin k → ℝ) × ↥(frameComplement (fun i => f i x₀))) X :=
  (exists_simultaneousRectifyingChart hf hind hcomm).choose

theorem simultaneousRectifyingChart_spec
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀)
    (hind : LinearIndependent ℝ (fun i => f i x₀))
    (hcomm : ∀ i j, FlowsCommuteLocally (f i) (f j) x₀) :
    let Ψ := simultaneousRectifyingChart hf hind hcomm
    (Ψ : _ → X) = simultaneousRectifyingMap hf ∧ 0 ∈ Ψ.source ∧
      (∀ p ∈ Ψ.source, ContDiffAt ℝ 1 Ψ p) ∧
      (∀ p ∈ Ψ.source, (fderiv ℝ Ψ p).IsInvertible) ∧
      (∀ i p, p ∈ Ψ.source → fderiv ℝ Ψ p (Pi.single i 1, 0) = f i (Ψ p)) ∧
      ∀ q ∈ Ψ.target, HasFDerivAt Ψ.symm (fderiv ℝ Ψ (Ψ.symm q)).inverse q :=
  (exists_simultaneousRectifyingChart hf hind hcomm).choose_spec

@[simp] theorem simultaneousRectifyingChart_zero
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀)
    (hind : LinearIndependent ℝ (fun i => f i x₀))
    (hcomm : ∀ i j, FlowsCommuteLocally (f i) (f j) x₀) :
    simultaneousRectifyingChart hf hind hcomm 0 = x₀ := by
  rw [(simultaneousRectifyingChart_spec hf hind hcomm).1]
  exact simultaneousRectifyingMap_zero hf

theorem zero_mem_simultaneousRectifyingChart_source
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀)
    (hind : LinearIndependent ℝ (fun i => f i x₀))
    (hcomm : ∀ i j, FlowsCommuteLocally (f i) (f j) x₀) :
    0 ∈ (simultaneousRectifyingChart hf hind hcomm).source :=
  (simultaneousRectifyingChart_spec hf hind hcomm).2.1

theorem simultaneousRectifyingChart_differentiableAt
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀)
    (hind : LinearIndependent ℝ (fun i => f i x₀))
    (hcomm : ∀ i j, FlowsCommuteLocally (f i) (f j) x₀)
    (p) (hp : p ∈ (simultaneousRectifyingChart hf hind hcomm).source) :
    DifferentiableAt ℝ (simultaneousRectifyingChart hf hind hcomm) p :=
  ((simultaneousRectifyingChart_spec hf hind hcomm).2.2.1 p hp).differentiableAt_one

/-- The forward simultaneous chart is `C¹` throughout its source. -/
theorem simultaneousRectifyingChart_contDiffOn
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀)
    (hind : LinearIndependent ℝ (fun i => f i x₀))
    (hcomm : ∀ i j, FlowsCommuteLocally (f i) (f j) x₀) :
    ContDiffOn ℝ 1 (simultaneousRectifyingChart hf hind hcomm)
      (simultaneousRectifyingChart hf hind hcomm).source :=
  fun p hp => ((simultaneousRectifyingChart_spec hf hind hcomm).2.2.1 p hp).contDiffWithinAt

/-- The inverse simultaneous chart is `C¹` throughout its target. -/
theorem simultaneousRectifyingChart_symm_contDiffOn
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀)
    (hind : LinearIndependent ℝ (fun i => f i x₀))
    (hcomm : ∀ i j, FlowsCommuteLocally (f i) (f j) x₀) :
    ContDiffOn ℝ 1 (simultaneousRectifyingChart hf hind hcomm).symm
      (simultaneousRectifyingChart hf hind hcomm).target := by
  intro q hq
  let Ψ := simultaneousRectifyingChart hf hind hcomm
  have hs := simultaneousRectifyingChart_spec hf hind hcomm
  have hp : Ψ.symm q ∈ Ψ.source := Ψ.map_target hq
  obtain ⟨A, hA⟩ := hs.2.2.2.1 (Ψ.symm q) hp
  have hd : HasFDerivAt Ψ (A : _ →L[ℝ] X) (Ψ.symm q) := by
    rw [hA]
    exact (hs.2.2.1 (Ψ.symm q) hp).differentiableAt_one.hasFDerivAt
  exact (Ψ.contDiffAt_symm hq hd (hs.2.2.1 (Ψ.symm q) hp)).contDiffWithinAt

/-- The differential sends every time coordinate vector to its assigned vector field. -/
theorem simultaneousRectifyingChart_fderiv
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀)
    (hind : LinearIndependent ℝ (fun i => f i x₀))
    (hcomm : ∀ i j, FlowsCommuteLocally (f i) (f j) x₀)
    (i : Fin k) (p) (hp : p ∈ (simultaneousRectifyingChart hf hind hcomm).source) :
    fderiv ℝ (simultaneousRectifyingChart hf hind hcomm) p (Pi.single i 1, 0) =
      f i (simultaneousRectifyingChart hf hind hcomm p) :=
  (simultaneousRectifyingChart_spec hf hind hcomm).2.2.2.2.1 i p hp

/-- Each coordinate line is an integral curve of its vector field at every source point. -/
theorem simultaneousRectifyingChart_rectifies
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀)
    (hind : LinearIndependent ℝ (fun i => f i x₀))
    (hcomm : ∀ i j, FlowsCommuteLocally (f i) (f j) x₀)
    (i : Fin k) (p) (hp : p ∈ (simultaneousRectifyingChart hf hind hcomm).source) :
    HasDerivAt (fun t => simultaneousRectifyingChart hf hind hcomm
        (Function.update p.1 i t, p.2))
      (f i (simultaneousRectifyingChart hf hind hcomm p)) (p.1 i) := by
  classical
  have hline := (hasDerivAt_update p.1 i (p.1 i)).prodMk
    (hasDerivAt_const (p.1 i) p.2)
  have hchart := (simultaneousRectifyingChart_differentiableAt hf hind hcomm p hp).hasFDerivAt
  have hpoint : (Function.update p.1 i (p.1 i), p.2) = p := by simp
  rw [← hpoint] at hchart
  have h := hchart.comp_hasDerivAt (p.1 i) hline
  simpa only [Function.comp_def, hpoint,
    simultaneousRectifyingChart_fderiv hf hind hcomm i p hp] using h

/-- Krener's simultaneous rectification lemma for an arbitrary finite commuting family.
Only local continuous differentiability, independence at the base point, and local bracket
vanishing are assumed. The conclusion is the existing canonical finite-coordinate interface. -/
theorem krenerLemma
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀)
    (hind : LinearIndependent ℝ (fun i => f i x₀))
    (hcomm : ∀ i j, FlowsCommuteLocally (f i) (f j) x₀) :
    SimultaneouslyRectifiable f x₀ := by
  let v : Fin k → X := fun i => f i x₀
  let n := k + Module.finrank ℝ ↥(frameComplement v)
  let hn : k ≤ n := Nat.le_add_right k _
  let C := frameCoordinates v
  let Ψ := simultaneousRectifyingChart hf hind hcomm
  let Φ := C.toHomeomorph.toOpenPartialHomeomorph.trans Ψ
  refine ⟨n, hn, Φ, ?_, ?_, ?_⟩
  · change Ψ (C 0) = x₀
    simp only [map_zero, simultaneousRectifyingChart_zero, Ψ]
  · change 0 ∈ Set.univ ∧ C 0 ∈ Ψ.source
    exact ⟨mem_univ _, by simpa only [map_zero] using
      zero_mem_simultaneousRectifyingChart_source hf hind hcomm⟩
  · intro i z hz
    have hmem : C z ∈ Ψ.source := hz.2
    have hd := (simultaneousRectifyingChart_differentiableAt hf hind hcomm
      (C z) hmem).hasFDerivAt.comp z C.hasFDerivAt
    change HasFDerivAt (Φ : (Fin n → ℝ) → X) _ z at hd
    rw [hd.fderiv]
    change fderiv ℝ Ψ (C z) (C (Pi.single (Fin.castLE hn i) 1)) = f i (Ψ (C z))
    rw [frameCoordinates_single]
    exact simultaneousRectifyingChart_fderiv hf hind hcomm i (C z) hmem

end
