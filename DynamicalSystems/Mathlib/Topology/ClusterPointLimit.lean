/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.ClusterPt
public import Mathlib.Topology.Compactness.CountablyCompact
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Passing bounds at cluster points of a sequence

Two elementary but reusable facts about a cluster point `a` of a sequence `u` in
an arbitrary topological space:

* a lower semicontinuous `f` bounded above by `c` along `u` satisfies `f a ≤ c`;
* a nonnegative continuous `f` with `f (u n) ≤ C / n` satisfies `f a = 0`.

They are the topological core of the contradiction argument for the boundary
positivity of the penalty `F_K` (Berkovitz & Medhin, *Nonlinear Optimal Control
Theory* (CRC 2012), Lemma 11.3.3).  No metrizability or first countability of the
ambient space is needed.
-/

@[expose] public section

open Filter Set Topology

namespace DynamicalSystems

/-- If `f` is lower semicontinuous and bounded above by `c` at every term of a
sequence `u`, then any cluster point `a` of `u` satisfies `f a ≤ c`. -/
theorem le_of_mapClusterPt_of_lowerSemicontinuous {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} (hf : LowerSemicontinuous f) {u : ℕ → X} {a : X} {c : ℝ}
    (ha : MapClusterPt a atTop u) (h : ∀ n, f (u n) ≤ c) : f a ≤ c := by
  by_contra hlt
  push Not at hlt
  obtain ⟨d, hcd, hda⟩ := exists_between hlt
  have hnhds : ∀ᶠ x in 𝓝 a, d < f x := hf a d hda
  obtain ⟨n, hn⟩ := (ha.frequently hnhds).exists
  exact absurd (h n) (not_le.mpr (lt_trans hcd hn))

/-- If `f` is nonnegative and continuous and `f (u n) ≤ g n` where `g → 0`, then any
cluster point `a` of `u` satisfies `f a = 0`. -/
theorem eq_zero_of_mapClusterPt_of_continuous_of_nonneg_of_tendsto_zero
    {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f)
    (hnonneg : ∀ x, 0 ≤ f x) {u : ℕ → X} {a : X} {g : ℕ → ℝ}
    (hg : Tendsto g atTop (𝓝 0)) (ha : MapClusterPt a atTop u)
    (h : ∀ n, f (u n) ≤ g n) : f a = 0 := by
  have hfa : 0 ≤ f a := hnonneg a
  by_contra hne
  have hpos : 0 < f a := lt_of_le_of_ne hfa (Ne.symm hne)
  have hhalf : f a / 2 < f a := by linarith
  have hnhds : ∀ᶠ x in 𝓝 a, f a / 2 < f x :=
    hf.continuousAt (isOpen_Ioi.mem_nhds hhalf)
  have hfreq : ∃ᶠ n in atTop, f a / 2 < f (u n) := ha.frequently hnhds
  have hev : ∀ᶠ n : ℕ in atTop, g n < f a / 2 :=
    hg (Iio_mem_nhds (by linarith : (0 : ℝ) < f a / 2))
  obtain ⟨n, hn1, hn2⟩ := (hfreq.and_eventually hev).exists
  have hn := h n
  linarith

/-- If `f` is nonnegative and continuous and `f (u n) ≤ C / n` at every term of a
sequence `u`, then any cluster point `a` of `u` satisfies `f a = 0`. -/
theorem eq_zero_of_mapClusterPt_of_continuous_of_nonneg_of_le_div
    {X : Type*} [TopologicalSpace X] {f : X → ℝ} (hf : Continuous f)
    (hnonneg : ∀ x, 0 ≤ f x) {u : ℕ → X} {a : X} {C : ℝ}
    (ha : MapClusterPt a atTop u) (h : ∀ n, f (u n) ≤ C / n) : f a = 0 :=
  eq_zero_of_mapClusterPt_of_continuous_of_nonneg_of_tendsto_zero hf hnonneg
    (tendsto_const_div_atTop_nhds_zero_nat C) ha h

end DynamicalSystems
