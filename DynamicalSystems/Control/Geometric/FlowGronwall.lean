/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-! # Grönwall estimates on a symmetric open interval

These elementary consequences of Mathlib's Grönwall inequality let local ODE arguments
treat positive and negative times together. In particular, the final estimate is linear
in the size of an inhomogeneous remainder, with a constant independent of that remainder.
-/

@[expose] public section

open Set

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A local, two-sided Grönwall estimate with zero initial value. -/
theorem norm_le_gronwall_symmetric
    {e e' : ℝ → X} {T K η : ℝ}
    (hT : 0 < T) (hK : 0 < K) (he0 : e 0 = 0)
    (he : ∀ t ∈ Ioo (-T) T, HasDerivAt e (e' t) t)
    (hbound : ∀ t ∈ Ioo (-T) T, ‖e' t‖ ≤ K * ‖e t‖ + η)
    {t : ℝ} (ht : t ∈ Ioo (-T) T) :
    ‖e t‖ ≤ (η / K) * (Real.exp (K * |t|) - 1) := by
  have hforward {g g' : ℝ → X} {b : ℝ} (hb : 0 ≤ b)
      (hg0 : g 0 = 0)
      (hg : ∀ s ∈ Icc 0 b, HasDerivAt g (g' s) s)
      (hgbound : ∀ s ∈ Ico 0 b, ‖g' s‖ ≤ K * ‖g s‖ + η) :
      ‖g b‖ ≤ (η / K) * (Real.exp (K * b) - 1) := by
    have hgcont : ContinuousOn g (Icc 0 b) :=
      fun s hs ↦ (hg s hs).continuousAt.continuousWithinAt
    have h := norm_le_gronwallBound_of_norm_deriv_right_le
      (δ := 0) (K := K) (ε := η) hgcont
      (fun s hs ↦ (hg s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (by simp [hg0]) hgbound b (right_mem_Icc.mpr hb)
    simpa [gronwallBound_of_K_ne_0 (ne_of_gt hK)] using h
  by_cases ht0 : 0 ≤ t
  · rw [abs_of_nonneg ht0]
    exact hforward ht0 he0
      (fun s hs ↦ he s ⟨by linarith [hs.1], lt_of_le_of_lt hs.2 ht.2⟩)
      (fun s hs ↦ hbound s ⟨by linarith [hs.1], lt_trans hs.2 ht.2⟩)
  · have hneg : t < 0 := lt_of_not_ge ht0
    have hmem : ∀ s ∈ Icc 0 (-t), -s ∈ Ioo (-T) T := by
      intro s hs
      constructor <;> linarith [hs.1, hs.2, ht.1]
    have h := hforward (g := fun s ↦ e (-s)) (g' := fun s ↦ -(e' (-s)))
      (b := -t) (by linarith) (by simpa using he0)
      (fun s hs ↦ by
        simpa [Function.comp_def] using (he (-s) (hmem s hs)).scomp s (hasDerivAt_neg s))
      (fun s hs ↦ by simpa using hbound (-s) (hmem s (Ico_subset_Icc_self hs)))
    simpa [abs_of_neg hneg] using h

/-- A fixed-time-horizon version of the two-sided Grönwall estimate. The multiplier
`(exp (K * T) - 1) / K` depends only on the horizon and growth constant. -/
theorem norm_le_gronwall_symmetric_uniform
    {e e' : ℝ → X} {T K η : ℝ}
    (hT : 0 < T) (hK : 0 < K) (hη : 0 ≤ η) (he0 : e 0 = 0)
    (he : ∀ t ∈ Ioo (-T) T, HasDerivAt e (e' t) t)
    (hbound : ∀ t ∈ Ioo (-T) T, ‖e' t‖ ≤ K * ‖e t‖ + η)
    {t : ℝ} (ht : t ∈ Ioo (-T) T) :
    ‖e t‖ ≤ ((Real.exp (K * T) - 1) / K) * η := by
  have habs : |t| ≤ T := le_of_lt (abs_lt.mpr ht)
  calc
    ‖e t‖ ≤ (η / K) * (Real.exp (K * |t|) - 1) :=
      norm_le_gronwall_symmetric hT hK he0 he hbound ht
    _ ≤ (η / K) * (Real.exp (K * T) - 1) := by
      gcongr
    _ = ((Real.exp (K * T) - 1) / K) * η := by ring

/-- The fixed multiplier in `norm_le_gronwall_symmetric_uniform` is positive. -/
theorem gronwall_symmetric_multiplier_pos {T K : ℝ} (hT : 0 < T) (hK : 0 < K) :
    0 < (Real.exp (K * T) - 1) / K := by
  exact div_pos (sub_pos.mpr (Real.one_lt_exp_iff.mpr (mul_pos hK hT))) hK

/-- The constant in the symmetric Grönwall estimate can be chosen independently
of the curve and of its inhomogeneous remainder bound. -/
theorem norm_le_mul_of_deriv_le_symmetric {T K : ℝ} (hT : 0 < T) (hK : 0 < K) :
    ∃ C > 0, ∀ {e e' : ℝ → X} {η : ℝ}, 0 ≤ η → e 0 = 0 →
      (∀ t ∈ Ioo (-T) T, HasDerivAt e (e' t) t) →
      (∀ t ∈ Ioo (-T) T, ‖e' t‖ ≤ K * ‖e t‖ + η) →
      ∀ t ∈ Ioo (-T) T, ‖e t‖ ≤ C * η := by
  refine ⟨(Real.exp (K * T) - 1) / K, gronwall_symmetric_multiplier_pos hT hK, ?_⟩
  intro e e' η hη he0 he hbound t ht
  exact norm_le_gronwall_symmetric_uniform hT hK hη he0 he hbound ht
