/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.MinimumTimeMaximumPrinciple
public import Mathlib.Analysis.Convex.Exposed

/-!
# Normality and almost-everywhere extreme controls

Berkovitz & Medhin, Definition 6.7.4 and Corollary 6.7.5: normality means
almost-everywhere uniqueness of the optimizing linear form on the control set.
It is a property of the system and control set, distinct from positivity of the
cost multiplier. Unique linear minimizers are exposed and hence extreme.

For a time-invariant box system, the per-input Krylov rank condition implies
this uniqueness a.e. and therefore an extreme control a.e. Combined Kalman
controllability alone does not imply this per-input condition (see Theorem 6.7.14).

The horizontal-variation proof of Theorem 6.3.22 is still absent. This module
does not infer terminal Hamiltonian vanishing from fixed-horizon optimality.
-/

@[expose] public section

open Set MeasureTheory

namespace OptimalControl

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A unique minimizer of a continuous linear form is extreme. This is the
geometric step of Berkovitz & Medhin Corollary 6.7.5. -/
theorem mem_extremePoints_of_unique_linear_minimum
    (C : Set V) (l : V →L[ℝ] ℝ) (u : V) (hu : u ∈ C)
    (hmin : ∀ v ∈ C, l u ≤ l v)
    (hunique : ∀ v ∈ C, l v ≤ l u → v = u) : u ∈ C.extremePoints ℝ := by
  apply exposedPoints_subset_extremePoints
  refine ⟨hu, -l, fun v hv ↦ ⟨?_, ?_⟩⟩
  · simpa using neg_le_neg (hmin v hv)
  · intro h
    apply hunique v hv
    simpa using neg_le_neg h

/-- Normality relative to a control set: every nonzero terminal covector
gives a unique linear Hamiltonian minimizer at almost every time.
This is Definition 6.7.4, in the minimum convention. -/
def HasLinearControlNormality {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℝ → (E →L[ℝ] ℝ) → V →L[ℝ] ℝ) (C : Set V) (a b : ℝ) : Prop :=
  ∀ q, q ≠ 0 → ∀ᵐ t ∂volume.restrict (Icc a b),
    ∀ u ∈ C, (∀ v ∈ C, L t q u ≤ L t q v) →
      ∀ v ∈ C, L t q v ≤ L t q u → v = u

/-- Normality and the a.e. Hamiltonian minimum force any admissible extremal
to take extreme values a.e., for an arbitrary control set. Compactness and
convexity are not needed once the minimizing control and uniqueness are given. -/
theorem ae_mem_extremePoints_of_linearControlNormality
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℝ → (E →L[ℝ] ℝ) → V →L[ℝ] ℝ) (C : Set V) (a b : ℝ)
    (hnormal : HasLinearControlNormality L C a b) (q : E →L[ℝ] ℝ) (hq : q ≠ 0)
    (u : ℝ → V) (hu : ∀ᵐ t ∂volume.restrict (Icc a b), u t ∈ C)
    (hmin : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ v ∈ C, L t q (u t) ≤ L t q v) :
    ∀ᵐ t ∂volume.restrict (Icc a b), u t ∈ C.extremePoints ℝ := by
  filter_upwards [hnormal q hq, hu, hmin] with t hn hut hmint
  exact mem_extremePoints_of_unique_linear_minimum C (L t q) (u t) hut hmint
    (hn (u t) hut hmint)

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Per-input Kalman rank implies the extreme-control conclusion a.e. for an
LTI box extremal. Analytic switching functions have finitely many zeros by
the merged rank theorem; the box minimum then uniquely determines the control.
This is the box specialization of the normality route of Theorem 6.7.14 and
Corollary 6.7.5, not a new optimality-to-maximum-principle theorem. -/
theorem ae_mem_extremePoints_of_cyclic_box_minimizing
    (A : E →L[ℝ] E) (q : E →L[ℝ] ℝ) (b : ι → E) (T : ℝ)
    (hb : ∀ i, CyclicInput A (b i)) (hq : q ≠ 0)
    (u : ℝ → EuclideanSpace ℝ ι)
    (hu : ∀ᵐ t ∂volume.restrict (Icc 0 T), u t ∈ unitBox ι)
    (hmin : ∀ᵐ t ∂volume.restrict (Icc 0 T), ∀ w ∈ unitBox ι,
      terminalAdjointCovector A q T t (∑ i, u t i • b i) ≤
        terminalAdjointCovector A q T t (∑ i, w i • b i)) :
    ∀ᵐ t ∂volume.restrict (Icc 0 T), u t ∈ (unitBox ι).extremePoints ℝ := by
  have hn : ∀ᵐ t ∂volume.restrict (Icc 0 T), ∀ i,
      linearSwitchingVector A q b T t i ≠ 0 := by
    apply ae_all_iff.mpr
    intro i
    have hz := (finite_zeroSet_linearSwitchingFunction A q (b i) T 0 T
      (hb i) hq).countable.ae_notMem (volume.restrict (Icc 0 T))
    filter_upwards [hz, ae_restrict_mem measurableSet_Icc] with t ht hmem
    exact fun heq ↦ ht ⟨hmem, heq⟩
  filter_upwards [hu, hmin, hn] with t hut hmint hnt
  let l : EuclideanSpace ℝ ι →L[ℝ] ℝ := innerSL ℝ (linearSwitchingVector A q b T t)
  have hlin : ∀ w ∈ unitBox ι, l (u t) ≤ l w := by
    intro w hw
    change inner ℝ (linearSwitchingVector A q b T t) (u t) ≤
      inner ℝ (linearSwitchingVector A q b T t) w
    simpa only [terminalAdjointCovector_input_sum] using hmint w hw
  apply mem_extremePoints_of_unique_linear_minimum (unitBox ι) l (u t) hut hlin
  intro w hw hwu
  have hwmin : ∀ z ∈ unitBox ι, l w ≤ l z := fun z hz ↦ hwu.trans (hlin z hz)
  ext i
  have hwval := (linearMinimizer_bangBang (linearSwitchingVector A q b T t) w hw hwmin)
    |>.2.1 i (hnt i)
  have huval := (linearMinimizer_bangBang (linearSwitchingVector A q b T t) (u t) hut hlin)
    |>.2.1 i (hnt i)
  exact hwval.trans huval.symm

end OptimalControl
