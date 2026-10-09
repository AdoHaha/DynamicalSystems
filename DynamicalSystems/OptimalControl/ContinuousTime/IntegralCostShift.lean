/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.CesariCostShift
public import DynamicalSystems.Mathlib.MeasureTheory.IntegralTrajectoryExtension
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The integrable lower-cost shift on moving intervals

A merely integrable lower bound has a continuous primitive. Compensating the
terminal cost by the primitive's endpoint difference preserves the *complete*
objective while making the zero-extended running costs nonnegative. No
continuity of the lower bound and no lower semicontinuity of the shifted running
cost are asserted. Measurable recovery must use the original running cost.
-/

@[expose] public section

open Set MeasureTheory
open DynamicalSystems.ClassicalEquiAC
open scoped Topology

namespace OptimalControl

/-- Primitive of an integrable time-dependent lower bound on the common time
interval. It is defined on the whole real line. -/
noncomputable def lowerCostPrimitive (a b : ℝ) (β : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ z in a..t, β z ∂volume.restrict (Icc a b)

/-- An integrable lower bound has a continuous primitive; it need not itself
be continuous or lower semicontinuous. -/
theorem continuous_lowerCostPrimitive {a b : ℝ} {β : ℝ → ℝ}
    (hβ : IntegrableOn β (Icc a b)) : Continuous (lowerCostPrimitive a b β) :=
  intervalIntegral.continuous_primitive (fun _ _ ↦ hβ.intervalIntegrable) a

/-- The primitive difference is the lower-bound integral over the actual
moving interval, not over the whole ambient interval. -/
theorem lowerCostPrimitive_sub {a b l r : ℝ} (hal : a ≤ l) (hrb : r ≤ b)
    (hlr : l ≤ r) {β : ℝ → ℝ} (hβ : IntegrableOn β (Icc a b)) :
    lowerCostPrimitive a b β r - lowerCostPrimitive a b β l =
      ∫ z in Icc l r, β z := by
  simp only [lowerCostPrimitive]
  rw [intervalIntegral.integral_interval_sub_left hβ.intervalIntegrable hβ.intervalIntegrable,
    intervalIntegral.integral_of_le hlr, Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (show Ioc l r ⊆ Icc a b from
      fun z hz ↦ ⟨hal.trans hz.1.le, hz.2.trans hrb⟩)]
  exact integral_Icc_eq_integral_Ioc.symm

/-- Terminal compensation for subtracting a time-dependent running-cost lower
bound on the moving interval. -/
noncomputable def compensatedTerminalCost {E : Type*} (a b : ℝ) (β : ℝ → ℝ)
    (g : ℝ × E × ℝ × E → ℝ) (p : ℝ × E × ℝ × E) : ℝ :=
  g p + (lowerCostPrimitive a b β p.2.2.1 - lowerCostPrimitive a b β p.1)

/-- The compensated terminal cost retains lower semicontinuity on the original
closed boundary set, using continuity of the primitive rather than of `β`. -/
theorem lowerSemicontinuousOn_compensatedTerminalCost {E : Type*} [TopologicalSpace E]
    {a b : ℝ} {β : ℝ → ℝ} (hβ : IntegrableOn β (Icc a b))
    {B : Set (ℝ × E × ℝ × E)} {g : ℝ × E × ℝ × E → ℝ}
    (hg : LowerSemicontinuousOn g B) :
    LowerSemicontinuousOn (compensatedTerminalCost a b β g) B := by
  have hF := continuous_lowerCostPrimitive hβ
  exact hg.add ((hF.comp (by fun_prop)).sub (hF.comp (by fun_prop))).continuousOn.
    lowerSemicontinuousOn

/-- Exact invariance of the terminal-plus-running objective under the
integrable lower-bound shift and zero extension. -/
theorem compensated_objective_eq {E : Type*} {a b l r : ℝ}
    (hal : a ≤ l) (hrb : r ≤ b) (hlr : l ≤ r)
    (g : ℝ × E × ℝ × E → ℝ) (xl xr : E) (cost β : ℝ → ℝ)
    (hc : IntegrableOn cost (Icc l r)) (hβ : IntegrableOn β (Icc a b)) :
    compensatedTerminalCost a b β g (l, xl, r, xr) +
        (∫ z, zeroExtension l r (fun t ↦ cost t - β t) z
          ∂volume.restrict (Icc a b)) =
      g (l, xl, r, xr) + ∫ z in Icc l r, cost z := by
  have hβlr : IntegrableOn β (Icc l r) :=
    hβ.mono_set (fun z hz ↦ ⟨hal.trans hz.1, hz.2.trans hrb⟩)
  simp only [compensatedTerminalCost]
  rw [lowerCostPrimitive_sub hal hrb hlr hβ,
    integral_zeroExtension_restrict hal hrb, integral_sub hc hβlr]
  ring

/-- A lower bound on the source interval yields a nonnegative shifted density
on the entire common interval. Outside the source interval it is zero, not
`-β`. -/
theorem ae_nonneg_zeroExtension_sub {a b l r : ℝ} {cost β : ℝ → ℝ}
    (hlower : ∀ᵐ t ∂volume.restrict (Icc l r), β t ≤ cost t) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      0 ≤ zeroExtension l r (fun z ↦ cost z - β z) t := by
  have H : ∀ᵐ t ∂volume, t ∈ Icc l r → β t ≤ cost t :=
    (ae_restrict_iff' measurableSet_Icc).mp hlower
  filter_upwards [H.filter_mono ae_restrict_le] with t ht
  by_cases hmem : t ∈ Ioc l r
  · simpa only [zeroExtension, indicator_of_mem hmem] using
      sub_nonneg.mpr (ht (Ioc_subset_Icc_self hmem))
  · simp only [zeroExtension, indicator_of_notMem hmem, le_refl]

/-- Membership in the shifted epigraph is precisely membership in the original
epigraph after restoring the lower-bound value. -/
theorem mem_shiftedVelocityCostSet_iff {T E : Type*}
    (Q : T → E → Set (E × ℝ)) (β : T → ℝ) (t : T) (x : E) (p : E × ℝ) :
    p ∈ shiftedVelocityCostSet Q β t x ↔ (p.1, p.2 + β t) ∈ Q t x := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa only [sub_add_cancel, Prod.eta] using hq
  · intro hp
    refine ⟨(p.1, p.2 + β t), hp, ?_⟩
    simp only [add_sub_cancel_right, Prod.eta]

end OptimalControl
