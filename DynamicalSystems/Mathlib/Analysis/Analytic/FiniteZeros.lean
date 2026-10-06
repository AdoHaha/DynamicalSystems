/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Topology.Order.Compact

/-!
# Finitely many zeros of a nontrivial analytic curve on a compact interval

Analyticity is required on a neighbourhood, including the interval endpoints.
Analyticity only on the open interval does not suffice. The nontriviality
hypothesis below is a witness somewhere on the real line; it need not be inside
the interval on which zeros are counted.
-/

@[expose] public section

open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A globally real-analytic, nontrivial curve has finitely many zeros on every
compact interval. This also handles empty and singleton intervals. -/
theorem AnalyticOnNhd.finite_zeroSet_Icc {f : ℝ → E}
    (hf : AnalyticOnNhd ℝ f univ) (hne : ∃ t, f t ≠ 0) (a b : ℝ) :
    {t | t ∈ Icc a b ∧ f t = 0}.Finite := by
  have hcd : ∀ᶠ t in codiscreteWithin (univ : Set ℝ), f t ≠ 0 := by
    rcases hf.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with
      hz | h
    · obtain ⟨t, ht⟩ := hne
      exact (ht (hz (mem_univ t))).elim
    · exact h
  have hcd' : {t | f t ≠ 0} ∈ codiscreteWithin (Icc a b) :=
    hcd.filter_mono (codiscreteWithin_mono (subset_univ _))
  convert isCompact_Icc.finite_sdiff_of_mem_codiscreteWithin hcd' using 1
  ext t
  simp

/-- The compact-connected version makes the endpoint-neighbourhood requirement
explicit and needs only a nonzero witness in the set itself. -/
theorem AnalyticOnNhd.finite_zeroSet_of_isCompact_of_isPreconnected
    {f : ℝ → E} {s : Set ℝ} (hf : AnalyticOnNhd ℝ f s)
    (hs : IsCompact s) (hc : IsPreconnected s) (hne : ∃ t ∈ s, f t ≠ 0) :
    {t | t ∈ s ∧ f t = 0}.Finite := by
  rcases hf.eqOn_zero_or_eventually_ne_zero_of_preconnected hc with hz | h
  · obtain ⟨t, ht, hnt⟩ := hne
    exact (hnt (hz ht)).elim
  · convert hs.finite_sdiff_of_mem_codiscreteWithin h using 1
    ext t
    simp
