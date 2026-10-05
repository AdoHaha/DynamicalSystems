/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.UniformlyLocallyLipschitzUniqueness
public import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistenceGrowth
public import DynamicalSystems.Mathlib.Analysis.ODE.ContinuousDependence

/-!
# Continuation and complete vector fields

Local uniqueness lets integral curves with a common initial value be glued on
the union of their existence intervals. If every curve on a bounded open
interval extends across its endpoints, the possible symmetric existence radii
are unbounded. This gives a global curve without requiring compact state-space
balls.
-/

@[expose] public noncomputable section

open Set Filter Topology Metric
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {f : ℝ → E → E}

namespace ODE

/-- Two local solutions with the same initial value agree wherever their
symmetric open existence intervals overlap. -/
theorem eq_of_mem_common_existence_intervals
    (hf : UniformlyLocallyLipschitz f) {α β : ℝ → E} {t₀ r s t : ℝ}
    (hr : 0 < r) (hs : 0 < s) (h₀ : α t₀ = β t₀)
    (hα : ∀ u ∈ Ioo (t₀ - r) (t₀ + r), HasDerivAt α (f u (α u)) u)
    (hβ : ∀ u ∈ Ioo (t₀ - s) (t₀ + s), HasDerivAt β (f u (β u)) u)
    (htr : t ∈ Ioo (t₀ - r) (t₀ + r))
    (hts : t ∈ Ioo (t₀ - s) (t₀ + s)) : α t = β t := by
  have hp : 0 < min r s := lt_min hr hs
  have hsubr : Ioo (t₀ - min r s) (t₀ + min r s) ⊆ Ioo (t₀ - r) (t₀ + r) := by
    intro u hu
    exact ⟨by linarith [hu.1, min_le_left r s], by linarith [hu.2, min_le_left r s]⟩
  have hsubs : Ioo (t₀ - min r s) (t₀ + min r s) ⊆ Ioo (t₀ - s) (t₀ + s) := by
    intro u hu
    exact ⟨by linarith [hu.1, min_le_right r s], by linarith [hu.2, min_le_right r s]⟩
  apply IsIntegralCurveOn.eqOn_Ioo_of_uniformlyLocallyLipschitz hf
    (a := t₀ - min r s) (b := t₀ + min r s) (t₀ := t₀)
    ⟨by linarith, by linarith⟩
    (fun u hu => (hα u (hsubr hu)).hasDerivWithinAt)
    (fun u hu => (hβ u (hsubs hu)).hasDerivWithinAt) h₀
  simp only [mem_Ioo, sub_lt_iff_lt_add] at *
  rcases le_total r s with hrs | hsr
  · simpa [min_eq_left hrs] using htr
  · simpa [min_eq_right hsr] using hts

/-- A family of integral curves with a common initial condition can be glued
on the union of symmetric open existence intervals. -/
theorem exists_curve_on_existence_intervals
    (hf : UniformlyLocallyLipschitz f) {t₀ : ℝ} {x₀ : E} {S : Set ℝ}
    (hpos : ∀ r ∈ S, 0 < r) (hne : S.Nonempty)
    (hsol : ∀ r ∈ S, ∃ α : ℝ → E, α t₀ = x₀ ∧
      ∀ t ∈ Ioo (t₀ - r) (t₀ + r), HasDerivAt α (f t (α t)) t) :
    ∃ γ : ℝ → E, γ t₀ = x₀ ∧ ∀ r ∈ S,
      ∀ t ∈ Ioo (t₀ - r) (t₀ + r), HasDerivAt γ (f t (γ t)) t := by
  classical
  choose α hα₀ hα using (fun r : S => hsol r r.property)
  let covered : ℝ → Prop := fun t => ∃ r : S, t ∈ Ioo (t₀ - r) (t₀ + r)
  let γ : ℝ → E := fun t => if ht : covered t then α ht.choose t else x₀
  have hagree (r : S) : EqOn γ (α r) (Ioo (t₀ - r) (t₀ + r)) := by
    intro t ht
    have hcovered : covered t := ⟨r, ht⟩
    simp only [γ, dite_eq_left hcovered]
    exact eq_of_mem_common_existence_intervals hf
      (hpos _ hcovered.choose.property) (hpos r r.property)
      ((hα₀ hcovered.choose).trans (hα₀ r).symm)
      (hα hcovered.choose) (hα r) hcovered.choose_spec ht
  refine ⟨γ, ?_, fun r hr t ht => ?_⟩
  · obtain ⟨r, hr⟩ := hne
    have hp := hpos r hr
    exact (hagree ⟨r, hr⟩ ⟨by linarith, by linarith⟩).trans (hα₀ ⟨r, hr⟩)
  · rw [hagree ⟨r, hr⟩ ht]
    apply (hα ⟨r, hr⟩ t ht).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds ht] with u hu
    exact hagree ⟨r, hr⟩ hu

/-- A locally well-posed vector field is complete if each solution on a
bounded symmetric open interval extends to a larger such interval.

The proof glues all local curves for an initial condition and rules out a
finite supremum of their existence radii. -/
theorem isCompleteVectorField_of_extension [CompleteSpace E]
    (hf : UniformlyLocallyLipschitz f) (hcont : Continuous f.uncurry)
    (hext : ∀ (t₀ r : ℝ), 0 < r → ∀ α : ℝ → E,
      (∀ t ∈ Ioo (t₀ - r) (t₀ + r), HasDerivAt α (f t (α t)) t) →
      ∃ ε > 0, ∃ β : ℝ → E, EqOn β α (Ioo (t₀ - r) (t₀ + r)) ∧
        ∀ t ∈ Ioo (t₀ - (r + ε)) (t₀ + (r + ε)),
          HasDerivAt β (f t (β t)) t) : IsCompleteVectorField f := by
  classical
  intro t₀ x₀
  let S : Set ℝ := {r | 0 < r ∧ ∃ α : ℝ → E, α t₀ = x₀ ∧
    ∀ t ∈ Ioo (t₀ - r) (t₀ + r), HasDerivAt α (f t (α t)) t}
  have hfpi : Continuous f := continuous_pi fun x =>
    hcont.comp (continuous_id.prodMk continuous_const)
  obtain ⟨r₀, hr₀, ρ, hρ, α, hα⟩ :=
    hf.exists_forall_mem_closedBall_eq_isIntegralCurveOn hfpi t₀ x₀
  obtain ⟨hα₀, hαderiv⟩ := hα x₀ (mem_closedBall_self hρ.le)
  have hr₀S : r₀ ∈ S := by
    refine ⟨hr₀, α x₀, hα₀, fun t ht => ?_⟩
    exact (hαderiv t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hne : S.Nonempty := ⟨r₀, hr₀S⟩
  obtain ⟨γ, hγ₀, hγ⟩ := exists_curve_on_existence_intervals hf
    (fun r (hr : r ∈ S) => hr.1) hne (fun r (hr : r ∈ S) => hr.2)
  have hunbounded : ¬ BddAbove S := by
    intro hb
    let R : ℝ := sSup S
    have hR : 0 < R := hr₀.trans_le (le_csSup hb hr₀S)
    have hγR : ∀ t ∈ Ioo (t₀ - R) (t₀ + R), HasDerivAt γ (f t (γ t)) t := by
      intro t ht
      have habs : |t - t₀| < R := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      obtain ⟨r, hr, htr⟩ := exists_lt_of_lt_csSup hne habs
      have htr' := abs_lt.mp htr
      exact hγ r hr t ⟨by linarith [htr'.1], by linarith [htr'.2]⟩
    obtain ⟨ε, hε, β, hβγ, hβ⟩ := hext t₀ R hR γ hγR
    have hnew : R + ε ∈ S := by
      refine ⟨by linarith, β, ?_, hβ⟩
      exact (hβγ ⟨by linarith, by linarith⟩).trans hγ₀
    have hle : R + ε ≤ R := le_csSup hb hnew
    linarith
  refine ⟨γ, hγ₀, fun t => ?_⟩
  obtain ⟨r, hr, htr⟩ := not_bddAbove_iff.mp hunbounded |t - t₀|
  have htr' := abs_lt.mp htr
  exact hγ r hr t ⟨by linarith [htr'.1], by linarith [htr'.2]⟩

end ODE

/-- A uniformly locally Lipschitz, jointly continuous vector field with linear
growth uniform on each compact time interval is complete on a Banach space.

The growth estimate controls every solution by Grönwall, hence bounds its
speed on bounded time intervals. Completeness supplies finite endpoint limits;
local existence and uniqueness then continue the solution. -/
theorem UniformlyLocallyLipschitz.isCompleteVectorField_of_continuous_uncurry [CompleteSpace E]
    (hf : UniformlyLocallyLipschitz f) (hcont : Continuous f.uncurry)
    (hgrowth : LocallyUniformLinearGrowth f) : IsCompleteVectorField f := by
  apply ODE.isCompleteVectorField_of_extension hf hcont
  intro t₀ r hr α hα
  obtain ⟨C, C', hbound⟩ := hgrowth (t₀ - r) (t₀ + r)
  obtain ⟨K, hK⟩ := ODE.lipschitzOnWith_of_linear_growth_Ioo hr hα hbound
  obtain ⟨ε, hε, β, hβα, hβ⟩ := ODE.exists_extension_Ioo hf hcont
    (by linarith : t₀ - r < t₀ + r) hα hK
  refine ⟨ε, hε, β, hβα, fun t ht => hβ t ?_⟩
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- Pointwise continuity in time suffices because uniform local Lipschitz
continuity in the state makes the vector field jointly continuous. -/
theorem UniformlyLocallyLipschitz.isCompleteVectorField [CompleteSpace E]
    (hf : UniformlyLocallyLipschitz f) (htime : Continuous f)
    (hgrowth : LocallyUniformLinearGrowth f) : IsCompleteVectorField f :=
  hf.isCompleteVectorField_of_continuous_uncurry (hf.continuous_uncurry htime) hgrowth

/-- A single uniform linear-growth estimate is a sufficient special case. -/
theorem UniformlyLocallyLipschitz.isCompleteVectorField_of_bound [CompleteSpace E]
    (hf : UniformlyLocallyLipschitz f) (hcont : Continuous f.uncurry)
    {C C' : ℝ≥0} (hbound : ∀ t x, ‖f t x‖ ≤ (C : ℝ) * ‖x‖ + C') :
    IsCompleteVectorField f :=
  hf.isCompleteVectorField_of_continuous_uncurry hcont
    (locallyUniformLinearGrowth_of_bound hbound)
