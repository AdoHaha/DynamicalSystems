/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.WeakEulerLagrange
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Weak Euler–Lagrange equations from an actual curve minimum

The derivative of the actual `cvFunctional` along an affine curve variation
is obtained from the existing parameterized integral differentiation theorem.
Endpoint-preserving affine curves are actual feasible competitors. Fermat then
gives stationarity, and the weak regularity theorem derives the momentum ODE.
-/

@[expose] public section

namespace KirkMedhin.WeakCoV

open Set Filter MeasureTheory
open scoped Interval Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual functional derivative along a one-parameter affine variation.
No endpoint restriction is imposed on the direction; this also handles the
nonzero local endpoint directions used in a corner variation. -/
theorem hasDerivAt_cvFunctional_affine
    (L : ℝ → E → E → ℝ) (K : E → ℝ) (T : ℝ) (x η : ℝ → E)
    (hL : ContDiff ℝ 1 (K3.uncurryLagrangian L)) (hK : ContDiff ℝ 1 K)
    (hx : ContDiff ℝ 1 x) (hη : ContDiff ℝ 1 η) (hT : 0 ≤ T) :
    HasDerivAt (fun ε : ℝ => cvFunctional L K T (fun t => x t + ε • η t))
      (firstVariation L K T x η) 0 := by
  have hd := (K3.hasStrictFDerivAt_cvFunctional_perturbed
    L K T x η (fun _ => 0) hL hK hx hη contDiff_const hT).hasFDerivAt
  have hparam : HasDerivAt (fun ε : ℝ => (ε, (0 : ℝ))) (1, 0) 0 :=
    (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  have h := hd.comp_hasDerivAt (f := fun ε : ℝ => (ε, (0 : ℝ))) 0 hparam
  have hcurve : ∀ ε : ℝ, K3.perturbedCurve x η (fun _ => 0) (ε, 0) =
      (fun t => x t + ε • η t) := by
    intro ε
    funext t
    change x t + (ε • η t + (0 : ℝ) • (0 : E)) = x t + ε • η t
    simp only [smul_zero, add_zero]
  simpa only [Function.comp_def, K3.parameterDerivative_one_zero, hcurve] using h

/-- A genuine minimum among all C1 curves with the fixed endpoint values has
zero actual first variation in every C1 endpoint-zero direction. -/
theorem firstVariation_zero_of_fixedEndpoint_min
    (L : ℝ → E → E → ℝ) (K : E → ℝ) (T : ℝ) (x : ℝ → E)
    (hL : ContDiff ℝ 1 (K3.uncurryLagrangian L)) (hK : ContDiff ℝ 1 K)
    (hx : ContDiff ℝ 1 x) (hT : 0 ≤ T)
    (hmin : IsMinOn (cvFunctional L K T)
      {y | ContDiff ℝ 1 y ∧ y 0 = x 0 ∧ y T = x T} x) :
    ∀ η : ℝ → E, ContDiff ℝ 1 η → η 0 = 0 → η T = 0 →
      firstVariation L K T x η = 0 := by
  intro η hη hη₀ hηT
  have hlocal : IsLocalMin
      (fun ε : ℝ => cvFunctional L K T (fun t => x t + ε • η t)) 0 := by
    apply Filter.Eventually.of_forall
    intro ε
    have hmem : (fun t => x t + ε • η t) ∈
        {y | ContDiff ℝ 1 y ∧ y 0 = x 0 ∧ y T = x T} :=
      ⟨hx.add (hη.const_smul ε), by simp [hη₀], by simp [hηT]⟩
    have hh : cvFunctional L K T x ≤
        cvFunctional L K T (fun t => x t + ε • η t) := hmin hmem
    simpa only [zero_smul, add_zero] using hh
  exact hlocal.hasDerivAt_eq_zero (hasDerivAt_cvFunctional_affine L K T x η hL hK
    hx hη hT)

/-- Primitive C1 data and an actual fixed-endpoint minimum imply the momentum
ODE on the full horizon, with one-sided endpoint meaning. -/
theorem eulerLagrange_hasDerivWithinAt_of_fixedEndpoint_min
    (L : ℝ → E → E → ℝ) (K : E → ℝ) (T : ℝ) (x : ℝ → E)
    (hL : ContDiff ℝ 1 (K3.uncurryLagrangian L)) (hK : ContDiff ℝ 1 K)
    (hx : ContDiff ℝ 1 x) (hT : 0 < T)
    (hmin : IsMinOn (cvFunctional L K T)
      {y | ContDiff ℝ 1 y ∧ y 0 = x 0 ∧ y T = x T} x) :
    ∀ t ∈ Icc 0 T,
      HasDerivWithinAt
        (fun s : ℝ => fderiv ℝ (fun v : E => L s (x s) v) (deriv x s))
        (fderiv ℝ (fun y : E => L t y (deriv x t)) (x t)) (Icc 0 T) t :=
  eulerLagrange_hasDerivWithinAt_of_firstVariation_zero hT hL hx
    (firstVariation_zero_of_fixedEndpoint_min L K T x hL hK hx hT.le hmin)

/-- The genuine two-sided Euler–Lagrange equation at every interior time is
also a consequence of the actual fixed-endpoint minimum. -/
theorem eulerLagrange_hasDerivAt_of_fixedEndpoint_min
    (L : ℝ → E → E → ℝ) (K : E → ℝ) (T : ℝ) (x : ℝ → E)
    (hL : ContDiff ℝ 1 (K3.uncurryLagrangian L)) (hK : ContDiff ℝ 1 K)
    (hx : ContDiff ℝ 1 x) (hT : 0 < T)
    (hmin : IsMinOn (cvFunctional L K T)
      {y | ContDiff ℝ 1 y ∧ y 0 = x 0 ∧ y T = x T} x) :
    ∀ t ∈ Ioo 0 T,
      HasDerivAt
        (fun s : ℝ => fderiv ℝ (fun v : E => L s (x s) v) (deriv x s))
        (fderiv ℝ (fun y : E => L t y (deriv x t)) (x t)) t := by
  intro t ht
  exact (eulerLagrange_hasDerivWithinAt_of_fixedEndpoint_min L K T x hL hK hx hT hmin
    t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)

end KirkMedhin.WeakCoV

end
