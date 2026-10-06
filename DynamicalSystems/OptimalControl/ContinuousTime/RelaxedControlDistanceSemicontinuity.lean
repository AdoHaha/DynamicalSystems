/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.EpsilonOptimality
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Regular
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Weak lower semicontinuity of the relaxed-control distance

The distance `relaxedControlDistance P ρ σ = sup_A |ρ(A) - σ(A)|` of two relaxed
controls is lower semicontinuous in `ρ` for the weak topology of probability
measures.  The proof is the portmanteau route (no dual-norm/Riesz substrate is
needed):

* for an **open** set `O` the map `ρ ↦ ρ(O)` is lower semicontinuous
  (`ProbabilityMeasure.le_liminf_measure_open_of_tendsto`);
* any measurable `B` with `ρ₀(B) - σ(B) > y` is enlarged to an open `O ⊇ B` with
  `σ(O) ≤ σ(B) + η` (outer regularity of the finite measure `σ`,
  `Set.exists_isOpen_lt_add`), whence `ρ(O) - σ(O) > y` near `ρ₀`;
* `|ρ(A) - σ(A)|` for probability measures is attained, up to complement, by
  the one-sided differences, which handles the absolute value.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2) and (11.3.6): the term `ε‖ν - ν₀‖_L` of `F_K`.  Concept
names only; the citation lives in docstrings.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace OptimalControl

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] [MetricSpace Ω] [BorelSpace Ω]

/-- The mass of an open set is a lower semicontinuous (real-valued) function of a
probability measure in the weak topology (portmanteau).

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2). -/
theorem lowerSemicontinuous_measureReal_isOpen {O : Set Ω} (hO : IsOpen O) :
    LowerSemicontinuous fun ρ : ProbabilityMeasure Ω => (ρ : Measure Ω).real O := by
  have h1 : LowerSemicontinuous fun ρ : ProbabilityMeasure Ω => (ρ : Measure Ω) O := by
    rw [lowerSemicontinuous_iff_le_liminf]
    intro ρ
    exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      (L := 𝓝 ρ) (μs := id) tendsto_id hO
  intro ρ₀ y hy
  replace hy : y < (ρ₀ : Measure Ω).real O := hy
  change ∀ᶠ ρ : ProbabilityMeasure Ω in 𝓝 ρ₀, y < (ρ : Measure Ω).real O
  rcases lt_or_ge y 0 with hy0 | hy0
  · exact Eventually.of_forall fun ρ => lt_of_lt_of_le hy0 ENNReal.toReal_nonneg
  · have hfin : ∀ ρ : ProbabilityMeasure Ω, (ρ : Measure Ω) O ≠ ∞ := fun ρ =>
      measure_ne_top _ _
    have hlt : ENNReal.ofReal y < (ρ₀ : Measure Ω) O := by
      rw [measureReal_def] at hy
      exact (ENNReal.ofReal_lt_iff_lt_toReal hy0 (hfin ρ₀)).2 hy
    filter_upwards [h1 ρ₀ _ hlt] with ρ hρ
    rw [measureReal_def]
    exact (ENNReal.ofReal_lt_iff_lt_toReal hy0 (hfin ρ)).1 hρ

/-- **Weak lower semicontinuity of the total-variation-type distance.**  For a
fixed probability measure `σ`, the map
`ρ ↦ sup_A |ρ(A) - σ(A)|` is lower semicontinuous on `ProbabilityMeasure Ω` in
the weak topology.  The supremum over *all* measurable sets is not a supremum of
continuous functions; lower semicontinuity comes from enlarging sets to open
sets (outer regularity of `σ`) and applying the portmanteau theorem.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2) and (11.3.6). -/
theorem lowerSemicontinuous_sSup_abs_measureReal_sub (σ : ProbabilityMeasure Ω) :
    LowerSemicontinuous fun ρ : ProbabilityMeasure Ω =>
      sSup {d : ℝ | ∃ A : Set Ω, MeasurableSet A ∧
        d = |(ρ : Measure Ω).real A - (σ : Measure Ω).real A|} := by
  have hbdd : ∀ ρ : ProbabilityMeasure Ω, BddAbove {d : ℝ | ∃ A : Set Ω, MeasurableSet A ∧
      d = |(ρ : Measure Ω).real A - (σ : Measure Ω).real A|} := by
    intro ρ
    refine ⟨1, ?_⟩
    rintro d ⟨A, -, rfl⟩
    have h1 : (ρ : Measure Ω).real A ≤ 1 := measureReal_le_one
    have h2 : (σ : Measure Ω).real A ≤ 1 := measureReal_le_one
    have h3 : 0 ≤ (ρ : Measure Ω).real A := measureReal_nonneg
    have h4 : 0 ≤ (σ : Measure Ω).real A := measureReal_nonneg
    rw [abs_le]
    constructor <;> linarith
  have hne : ∀ ρ : ProbabilityMeasure Ω, {d : ℝ | ∃ A : Set Ω, MeasurableSet A ∧
      d = |(ρ : Measure Ω).real A - (σ : Measure Ω).real A|}.Nonempty :=
    fun ρ => ⟨_, ∅, MeasurableSet.empty, rfl⟩
  intro ρ₀ y hy
  obtain ⟨d, ⟨A, hA, rfl⟩, hyd⟩ := (lt_csSup_iff (hbdd ρ₀) (hne ρ₀)).1 hy
  -- a measurable set with a one-sided gap exceeding `y`
  obtain ⟨B, hB, hyB⟩ : ∃ B : Set Ω, MeasurableSet B ∧
      y < (ρ₀ : Measure Ω).real B - (σ : Measure Ω).real B := by
    rcases le_total 0 ((ρ₀ : Measure Ω).real A - (σ : Measure Ω).real A) with h | h
    · exact ⟨A, hA, by rwa [abs_of_nonneg h] at hyd⟩
    · refine ⟨Aᶜ, hA.compl, ?_⟩
      have e1 : (ρ₀ : Measure Ω).real Aᶜ = 1 - (ρ₀ : Measure Ω).real A := by
        rw [probReal_compl_eq_one_sub hA]
      have e2 : (σ : Measure Ω).real Aᶜ = 1 - (σ : Measure Ω).real A := by
        rw [probReal_compl_eq_one_sub hA]
      rw [e1, e2]
      rw [abs_of_nonpos h] at hyd
      linarith
  set η : ℝ := (ρ₀ : Measure Ω).real B - (σ : Measure Ω).real B - y with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  obtain ⟨O, hBO, hO, hσO⟩ := Set.exists_isOpen_lt_add (μ := (σ : Measure Ω)) B
    (measure_ne_top _ _) (ENNReal.ofReal_pos.2 hηpos).ne'
  have hσOreal : (σ : Measure Ω).real O < (σ : Measure Ω).real B + η := by
    have := (ENNReal.toReal_lt_toReal (measure_ne_top _ _)
      (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩)).2 hσO
    rwa [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hηpos.le] at this
  have hρBO : (ρ₀ : Measure Ω).real B ≤ (ρ₀ : Measure Ω).real O :=
    measureReal_mono hBO
  have hy' : y + (σ : Measure Ω).real O < (ρ₀ : Measure Ω).real O := by
    rw [hη] at hσOreal
    linarith
  filter_upwards [lowerSemicontinuous_measureReal_isOpen hO ρ₀ _ hy'] with ρ hρ
  refine lt_of_lt_of_le ?_ (le_csSup (hbdd ρ) ⟨O, hO.measurableSet, rfl⟩)
  refine lt_of_lt_of_le ?_ (le_abs_self _)
  linarith

end Generic

namespace BoundedState.Problem

variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- **Weak lower semicontinuity of the relaxed-control distance.**  On the
compact space of relaxed controls (weak topology inherited from probability
measures on `time × Ω`), `ρ ↦ relaxedControlDistance P ρ σ` is lower
semicontinuous.  This is the `ε‖ν − ν₀‖_L` term of the penalty `F_K`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2) and (11.3.6). -/
theorem lowerSemicontinuous_relaxedControlDistance (P : Problem E V W) (σ : P.Relaxed) :
    LowerSemicontinuous fun ρ : P.Relaxed => relaxedControlDistance P ρ σ := by
  have h := lowerSemicontinuous_sSup_abs_measureReal_sub (Ω := P.Time × P.Control) σ.1
  intro ρ y hy
  exact ((continuous_subtype_val (p := fun μ : ProbabilityMeasure (P.Time × P.Control) =>
    μ.map Prod.fst = horizonProbability P.horizon P.horizon_pos)).tendsto ρ).eventually
    (h ρ.1 y hy)

end BoundedState.Problem

end OptimalControl
