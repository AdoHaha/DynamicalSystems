/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistenceLinear
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.ProjIcc

/-!
# Adjoint existence and pairing identities

Existence of the linear adjoint equation from continuous coefficients on a
compact horizon, and the differentiated/integrated pairing identities between
the linearized state and adjoint equations. The statements are generic linear
ODE facts; no control-theoretic data appears.
-/

@[expose] public section

open Set MeasureTheory
open scoped NNReal Interval


variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem exists_adjointOn_Icc
    {A : ℝ → E →L[ℝ] E} {ell : ℝ → E} {T : ℝ}
    (hT : 0 ≤ T) (hA : ContinuousOn A (Icc 0 T))
    (hell : ContinuousOn ell (Icc 0 T)) (k : E) :
    ∃ p : ℝ → E, Continuous p ∧ p T = k ∧
      ∀ t ∈ Icc 0 T, HasDerivAt p (-(A t).adjoint (p t) - ell t) t := by
  let Aext : ℝ → E →L[ℝ] E := fun t => A (projIcc 0 T hT t)
  let lext : ℝ → E := fun t => ell (projIcc 0 T hT t)
  have hAc : Continuous Aext := hA.domRestrict.comp continuous_projIcc
  have hlc : Continuous lext := hell.domRestrict.comp continuous_projIcc
  let B : ℝ → E →L[ℝ] E := fun t => -(Aext t).adjoint
  have hBc : Continuous B :=
    (ContinuousLinearMap.adjoint.continuous.comp hAc).neg
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  obtain ⟨N, hN⟩ := isCompact_Icc.exists_bound_of_continuousOn hell
  let K : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  have hBbound : ∀ t, ‖B t‖ ≤ (K : ℝ) := by
    intro t
    dsimp [B]
    rw [norm_neg, ContinuousLinearMap.adjoint.norm_map]
    exact (hM (projIcc 0 T hT t) (projIcc 0 T hT t).property).trans
      (le_max_left _ _)
  have hll : ∀ t, LipschitzWith K (fun y : E => B t y - lext t) := by
    intro t
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [dist_sub_right]
    exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le (hBbound t)).dist_le_mul y z
  have hzero : ∀ t, ‖B t 0 - lext t‖ ≤ N := by
    intro t
    simp only [map_zero, zero_sub, norm_neg]
    exact hN (projIcc 0 T hT t) (projIcc 0 T hT t).property
  have hV : Continuous (fun z : ℝ × E => B z.1 z.2 - lext z.1) :=
    ((hBc.comp continuous_fst).clm_apply continuous_snd).sub
      (hlc.comp continuous_fst)
  obtain ⟨F, hF⟩ := global_existence (f := fun t y => B t y - lext t)
    hll hzero hV
  let p := F T k
  have hp : ∀ t, HasDerivAt p (B t (p t) - lext t) t := (hF T k).1
  refine ⟨p, continuous_iff_continuousAt.mpr (fun t => (hp t).continuousAt),
    (hF T k).2, ?_⟩
  intro t ht
  simpa only [B, Aext, lext, projIcc_of_mem hT ht,
    neg_apply] using hp t

/-- The forward linear term and backward adjoint term cancel in the pairing. -/
theorem _root_.hasDerivWithinAt_adjoint_pairing
    {p d ell b : ℝ → E} {A : ℝ → E →L[ℝ] E} {s : Set ℝ} {t : ℝ}
    (hp : HasDerivWithinAt p (-(A t).adjoint (p t) - ell t) s t)
    (hd : HasDerivWithinAt d ((A t) (d t) + b t) s t) :
    HasDerivWithinAt (fun r => inner ℝ (p r) (d r))
      (inner ℝ (p t) (b t) - inner ℝ (ell t) (d t)) s t := by
  have h := hp.inner ℝ hd
  convert h using 1
  simp only [inner_add_right, inner_sub_left, inner_neg_left,
    ContinuousLinearMap.adjoint_inner_left]
  ring

/-- Integration of the derived pairing identity. At switches, right derivatives
are sufficient; the trajectories themselves remain continuous. -/
theorem integral_adjoint_pairing
    {p d ell b : ℝ → E} {A : ℝ → E →L[ℝ] E} {a z : ℝ}
    (haz : a ≤ z)
    (hpc : ContinuousOn p (Icc a z))
    (hdc : ContinuousOn d (Icc a z))
    (hp : ∀ t ∈ Ioo a z,
      HasDerivWithinAt p (-(A t).adjoint (p t) - ell t) (Ioi t) t)
    (hd : ∀ t ∈ Ioo a z,
      HasDerivWithinAt d ((A t) (d t) + b t) (Ioi t) t)
    (hbi : IntervalIntegrable (fun t => inner ℝ (p t) (b t)) volume a z)
    (hli : IntervalIntegrable (fun t => inner ℝ (ell t) (d t)) volume a z) :
    inner ℝ (p z) (d z) - inner ℝ (p a) (d a) +
        (∫ t in a..z, inner ℝ (ell t) (d t)) =
      ∫ t in a..z, inner ℝ (p t) (b t) := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le haz
    (hpc.inner hdc)
    (fun t ht => _root_.hasDerivWithinAt_adjoint_pairing (hp t ht) (hd t ht))
    (hbi.sub hli)
  rw [intervalIntegral.integral_sub hbi hli] at hFTC
  linarith

/-- Adding the running-cost expansion gives the exact finite-difference cost
identity. The forcing `b` can contain both the needle jump and its remainder. -/
theorem _root_.integral_adjoint_pairing_with_running_term
    {p d ell b : ℝ → E} {c : ℝ → ℝ} {A : ℝ → E →L[ℝ] E} {a z : ℝ}
    (haz : a ≤ z)
    (hpc : ContinuousOn p (Icc a z))
    (hdc : ContinuousOn d (Icc a z))
    (hp : ∀ t ∈ Ioo a z,
      HasDerivWithinAt p (-(A t).adjoint (p t) - ell t) (Ioi t) t)
    (hd : ∀ t ∈ Ioo a z,
      HasDerivWithinAt d ((A t) (d t) + b t) (Ioi t) t)
    (hbi : IntervalIntegrable (fun t => inner ℝ (p t) (b t)) volume a z)
    (hli : IntervalIntegrable (fun t => inner ℝ (ell t) (d t)) volume a z)
    (hci : IntervalIntegrable c volume a z) :
    (∫ t in a..z, inner ℝ (ell t) (d t) + c t) +
        inner ℝ (p z) (d z) - inner ℝ (p a) (d a) =
      ∫ t in a..z, c t + inner ℝ (p t) (b t) := by
  have h := integral_adjoint_pairing haz hpc hdc hp hd hbi hli
  rw [intervalIntegral.integral_add hli hci, intervalIntegral.integral_add hci hbi]
  linarith
