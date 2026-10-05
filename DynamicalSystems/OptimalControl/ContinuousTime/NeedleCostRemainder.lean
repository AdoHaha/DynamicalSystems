/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Nonlinear errors in an actual needle cost difference

The spatial Taylor error and the state-dependent control-increment error are
actual finite differences. A derivative estimate on their line segment gives
the Taylor bound. The integrated error theorem then combines a fixed-horizon
quadratic Taylor error, a shrinking-interval Lipschitz error, and a terminal
Taylor error. Uniform `O(ε)` displacement makes the total error `O(ε²)`, hence
`o(ε)`. No cost sensitivity, first variation or Hamiltonian inequality is an
input.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology Interval

namespace K1NeedleCost

section Normed

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The actual spatial error after subtracting the proposed linearization. -/
def taylorError (F : E → G) (A : E →L[ℝ] G) (x y : E) : G :=
  F y - F x - A (y - x)

/-- The extra state dependence introduced when replacing one control branch
by another. This term is integrated only on the needle interval. -/
def controlIncrementError (Fv F₀ : E → G) (x y : E) : G :=
  (Fv y - Fv x) - (F₀ y - F₀ x)

/-- A spatial derivative modulus on the actual segment gives a Taylor bound.
The derivative at intermediate points is supplied and checked through
`HasFDerivAt`; no Taylor remainder estimate is assumed. -/
theorem norm_taylorError_le_of_derivative_bound
    {F : E → G} {D : E → E →L[ℝ] G} {A : E →L[ℝ] G} {x y : E} {b : ℝ}
    (hD : ∀ z ∈ segment ℝ x y, HasFDerivAt F (D z) z)
    (hbound : ∀ z ∈ segment ℝ x y, ‖D z - A‖ ≤ b) :
    ‖taylorError F A x y‖ ≤ b * ‖y - x‖ := by
  have h := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (f := fun z => F z - A z) (f' := fun z => D z - A)
    (fun z hz => ((hD z hz).sub A.hasFDerivAt).hasFDerivWithinAt)
    hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [taylorError, map_sub, sub_sub_sub_comm] using h

/-- A Lipschitz bound for the spatial derivative gives a quadratic error.
The non-sharp constant avoids needing a Taylor integral formula. -/
theorem norm_taylorError_le_quadratic
    {F : E → G} {D : E → E →L[ℝ] G} {x y : E} {B : ℝ}
    (hB : 0 ≤ B)
    (hD : ∀ z ∈ segment ℝ x y, HasFDerivAt F (D z) z)
    (hLip : ∀ z ∈ segment ℝ x y, ‖D z - D x‖ ≤ B * ‖z - x‖) :
    ‖taylorError F (D x) x y‖ ≤ B * ‖y - x‖ ^ 2 := by
  have h := norm_taylorError_le_of_derivative_bound hD
    (b := B * ‖y - x‖) (fun z hz => (hLip z hz).trans
      (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hB))
  convert h using 1
  ring

omit [NormedSpace ℝ E] [NormedSpace ℝ G] in
/-- Lipschitz bounds on the two dynamics/cost branches control the extra
state increment on a needle. -/
theorem norm_controlIncrementError_le
    {Fv F₀ : E → G} {x y : E} {Bv B₀ : ℝ}
    (hv : ‖Fv y - Fv x‖ ≤ Bv * ‖y - x‖)
    (h₀ : ‖F₀ y - F₀ x‖ ≤ B₀ * ‖y - x‖) :
    ‖controlIncrementError Fv F₀ x y‖ ≤ (Bv + B₀) * ‖y - x‖ := by
  exact (norm_sub_le _ _).trans ((add_le_add hv h₀).trans_eq (by ring))

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The scalar error left after the exact adjoint cancellation, split into
the nominal Taylor error and the short-interval control-increment error. -/
noncomputable def remainder (rK : ℝ → ℝ) (rL cL : ℝ → ℝ → ℝ)
    (rf cf : ℝ → ℝ → E) (p : ℝ → E) (T τ ε : ℝ) : ℝ :=
  rK ε + (∫ t in 0..T, rL ε t + inner ℝ (p t) (rf ε t)) +
    ∫ t in (τ - ε)..τ, cL ε t + inner ℝ (p t) (cf ε t)

/-- A finite-parameter bound for the actual remainder terms. The derivative
lemmas above provide the nominal/terminal quadratic hypotheses; branch
Lipschitz bounds provide the shrinking-interval hypotheses. -/
theorem norm_remainder_le_quadratic
    {d rf cf : ℝ → ℝ → E} {rK : ℝ → ℝ} {rL cL : ℝ → ℝ → ℝ}
    {p : ℝ → E} {T τ ε C P Bf BL BK Df DL : ℝ}
    (hT : 0 ≤ T) (hε : 0 < ε) (ha : 0 ≤ τ - ε) (hτ : τ ≤ T)
    (hP : 0 ≤ P) (hBf : 0 ≤ Bf) (hBL : 0 ≤ BL)
    (hBK : 0 ≤ BK) (hDf : 0 ≤ Df) (hDL : 0 ≤ DL)
    (hd : ∀ t ∈ Icc 0 T, ‖d ε t‖ ≤ C * ε)
    (hp : ∀ t ∈ Icc 0 T, ‖p t‖ ≤ P)
    (hrf : ∀ t ∈ Icc 0 T, ‖rf ε t‖ ≤ Bf * ‖d ε t‖ ^ 2)
    (hrL : ∀ t ∈ Icc 0 T, ‖rL ε t‖ ≤ BL * ‖d ε t‖ ^ 2)
    (hrK : ‖rK ε‖ ≤ BK * ‖d ε T‖ ^ 2)
    (hcf : ∀ t ∈ Icc (τ - ε) τ, ‖cf ε t‖ ≤ Df * ‖d ε t‖)
    (hcL : ∀ t ∈ Icc (τ - ε) τ, ‖cL ε t‖ ≤ DL * ‖d ε t‖) :
    ‖remainder rK rL cL rf cf p T τ ε‖ ≤
      ((BK + T * (BL + P * Bf)) * C ^ 2 + (DL + P * Df) * C) * ε ^ 2 := by
  have hTmem : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
  have hsquare (t : ℝ) (ht : t ∈ Icc 0 T) : ‖d ε t‖ ^ 2 ≤ (C * ε) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hd t ht) 2
  have hnom (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖rL ε t + inner ℝ (p t) (rf ε t)‖ ≤ (BL + P * Bf) * (C * ε) ^ 2 := by
    calc
      _ ≤ ‖rL ε t‖ + ‖inner ℝ (p t) (rf ε t)‖ := norm_add_le _ _
      _ ≤ BL * ‖d ε t‖ ^ 2 + P * (Bf * ‖d ε t‖ ^ 2) := by
        apply add_le_add (hrL t ht)
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul (hp t ht) (hrf t ht) (norm_nonneg _) hP)
      _ = (BL + P * Bf) * ‖d ε t‖ ^ 2 := by ring
      _ ≤ (BL + P * Bf) * (C * ε) ^ 2 :=
        mul_le_mul_of_nonneg_left (hsquare t ht) (by positivity)
  have hnomint : ‖∫ t in 0..T, rL ε t + inner ℝ (p t) (rf ε t)‖ ≤
      (BL + P * Bf) * (C * ε) ^ 2 * T := by
    have hbound : ∀ t ∈ Ι (0 : ℝ) T,
        ‖rL ε t + inner ℝ (p t) (rf ε t)‖ ≤ (BL + P * Bf) * (C * ε) ^ 2 := by
      intro t ht
      rw [uIoc_of_le hT] at ht
      exact hnom t ⟨ht.1.le, ht.2⟩
    simpa [abs_of_nonneg hT] using
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hshort (t : ℝ) (ht : t ∈ Icc (τ - ε) τ) :
      ‖cL ε t + inner ℝ (p t) (cf ε t)‖ ≤ (DL + P * Df) * (C * ε) := by
    have htT : t ∈ Icc (0 : ℝ) T := ⟨ha.trans ht.1, ht.2.trans hτ⟩
    calc
      _ ≤ ‖cL ε t‖ + ‖inner ℝ (p t) (cf ε t)‖ := norm_add_le _ _
      _ ≤ DL * ‖d ε t‖ + P * (Df * ‖d ε t‖) := by
        apply add_le_add (hcL t ht)
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul (hp t htT) (hcf t ht) (norm_nonneg _) hP)
      _ = (DL + P * Df) * ‖d ε t‖ := by ring
      _ ≤ (DL + P * Df) * (C * ε) :=
        mul_le_mul_of_nonneg_left (hd t htT) (by positivity)
  have hshortint : ‖∫ t in (τ - ε)..τ, cL ε t + inner ℝ (p t) (cf ε t)‖ ≤
      (DL + P * Df) * (C * ε) * ε := by
    have hbound : ∀ t ∈ Ι (τ - ε) τ,
        ‖cL ε t + inner ℝ (p t) (cf ε t)‖ ≤ (DL + P * Df) * (C * ε) := by
      intro t ht
      rw [uIoc_of_le (by linarith : τ - ε ≤ τ)] at ht
      exact hshort t ⟨ht.1.le, ht.2⟩
    simpa [abs_of_pos hε] using
      intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hterm : ‖rK ε‖ ≤ BK * (C * ε) ^ 2 :=
    hrK.trans (mul_le_mul_of_nonneg_left (hsquare T hTmem) hBK)
  calc
    _ ≤ ‖rK ε‖ + ‖∫ t in 0..T, rL ε t + inner ℝ (p t) (rf ε t)‖ +
        ‖∫ t in (τ - ε)..τ, cL ε t + inner ℝ (p t) (cf ε t)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ BK * (C * ε) ^ 2 + (BL + P * Bf) * (C * ε) ^ 2 * T +
        (DL + P * Df) * (C * ε) * ε :=
      add_le_add (add_le_add hterm hnomint) hshortint
    _ = _ := by ring

/-- A quadratic error vanishes after division by the positive needle width. -/
theorem tendsto_scaled_of_quadratic_bound
    {R : ℝ → ℝ} {B : ℝ}
    (hR : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖R ε‖ ≤ B * ε ^ 2) :
    Tendsto (fun ε : ℝ => ε⁻¹ * R ε) (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ‖ε⁻¹ * R ε‖ ≤ B * ε := by
    filter_upwards [hR, self_mem_nhdsWithin] with ε hε hpos
    have hεpos : 0 < ε := hpos
    rw [norm_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hεpos]
    calc
      ε⁻¹ * ‖R ε‖ ≤ ε⁻¹ * (B * ε ^ 2) :=
        mul_le_mul_of_nonneg_left hε (inv_nonneg.mpr hεpos.le)
      _ = B * ε := by field_simp [ne_of_gt hεpos]
  have hlinear : Tendsto (fun ε : ℝ => B * ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul
      (tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hlinear

end InnerProduct

end K1NeedleCost
