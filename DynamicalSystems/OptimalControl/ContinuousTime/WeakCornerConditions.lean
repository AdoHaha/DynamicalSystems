/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
import DynamicalSystems.OptimalControl.ContinuousTime.FinitePiecewiseVariations
import DynamicalSystems.OptimalControl.ContinuousTime.DuBoisReymond

/-!
# Corner energy from finite-piecewise ambient optimality

Optimality of the original functional implies local optimality of each smooth
subarc by actual splicing. Inner time variations then make its energy constant,
without differentiating velocity. A duration exchange equates the energies at
each corner, including corners embedded in arbitrary finite surrounding arcs.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace FinitePiecewise

open TimeReparametrization DuBoisReymond

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Weak du Bois–Reymond in the ambient class allowing any finite number of corners. -/
theorem energy_eq_of_finite_cvFunctional_min
    (L : E → E → ℝ) (K : E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {x v : ℝ → E} (hx : ∀ t, HasDerivAt x (v t) t) (hv : Continuous v)
    {T : ℝ} (hT : 0 < T)
    (hmin : IsMinOn (cvFunctional (fun _ ↦ L) K T)
      (fixedEndpointFinitePiecewiseC1Curves T (x 0) (x T)) x) :
    ∀ t ∈ Icc 0 T, energyCurve L x v t = energyCurve L x v 0 := by
  apply energy_eq_of_all_duration_exchange_min L hL hx hv hT
  intro a ha
  have hd : 0 < T - a := sub_pos.mpr ha.2
  have hsum : a + (T - a) = T := by ring
  have hvshift : Continuous (fun s ↦ v (a + s)) :=
    hv.comp (continuous_const.add continuous_id)
  have hjoin : x a = (fun s ↦ x (a + s)) 0 := by simp
  apply actualCornerCost_isLocalMin_of_ambient_min L K hL.continuous hx hv
    (hasDerivAt_shifted hx a) hvshift ha.1 hd
    (fixedEndpointFinitePiecewiseC1Curves (a + (T - a)) (x 0) (x (a + (T - a))))
  · intro ε hε
    exact durationExchange_mem_fixedEndpointFinitePiecewiseC1Curves
      hx hv (hasDerivAt_shifted hx a) hvshift ha.1 hd hjoin hε
  · simpa only [hsum, concatenate_shifted] using hmin

/-- The autonomous corner-energy condition follows from the actual functional minimum
with only continuous one-sided velocities. No Euler–Lagrange or energy equation,
velocity derivative, variation identity, or scalar minimum is an input. -/
theorem corner_energy_eq_of_cvFunctional_min_weak
    (L : E → E → ℝ) (K : E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : Continuous v₁)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : Continuous v₂)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hjoin : x₁ d₁ = x₂ 0)
    (hmin : IsMinOn (cvFunctional (fun _ ↦ L) K (d₁ + d₂))
      (fixedEndpointFinitePiecewiseC1Curves (d₁ + d₂) (x₁ 0) (x₂ d₂))
      (concatenate d₁ x₁ x₂)) :
    energyCurve L x₁ v₁ d₁ = energyCurve L x₂ v₂ 0 := by
  have h₁ : IsFinitePiecewiseC1 d₁ x₁ := .smooth hd₁ hx₁ hv₁
  have h₂ : IsFinitePiecewiseC1 d₂ x₂ := .smooth hd₂ hx₂ hv₂
  have href := concatenate_mem_fixedEndpointFinitePiecewiseC1Curves h₁ h₂ hjoin
  have hm := action_min_of_cvFunctional_min L K href.2.1 hmin
  have hm₁ := action_min_left L hL.continuous h₁ h₂ hjoin hm
  have hm₂ := action_min_right L hL.continuous h₁ h₂ hjoin hm
  have hE₁ := energy_eq_of_finite_cvFunctional_min L (fun _ ↦ 0) hL hx₁ hv₁ hd₁
    (cvFunctional_min_of_action_min L _ rfl hm₁)
  have hE₂ := energy_eq_of_finite_cvFunctional_min L (fun _ ↦ 0) hL hx₂ hv₂ hd₂
    (cvFunctional_min_of_action_min L _ rfl hm₂)
  apply corner_energy_eq_of_actual_min L hL hx₁ hv₁ hx₂ hv₂ hd₁ hd₂
    (fun t ht ↦ (hE₁ t ht).trans (hE₁ d₁ ⟨hd₁.le, le_rfl⟩).symm) hE₂
  exact actualCornerCost_isLocalMin_of_ambient_min L K hL.continuous hx₁ hv₁ hx₂ hv₂
    hd₁ hd₂ _ (fun ε hε ↦ durationExchange_mem_fixedEndpointFinitePiecewiseC1Curves
      hx₁ hv₁ hx₂ hv₂ hd₁ hd₂ hjoin hε) hmin

/-- Every corner surrounded by any finite collection of joined C1 arcs satisfies
energy matching. The context only describes actual prefix/suffix concatenations;
its feasibility and the local pair minimum are proved from the global minimum. -/
theorem corner_energy_eq_in_finite_context
    (L : E → E → ℝ) (K : E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {x₁ v₁ x₂ v₂ : ℝ → E}
    (hx₁ : ∀ t, HasDerivAt x₁ (v₁ t) t) (hv₁ : Continuous v₁)
    (hx₂ : ∀ t, HasDerivAt x₂ (v₂ t) t) (hv₂ : Continuous v₂)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) (hjoin : x₁ d₁ = x₂ 0)
    {T : ℝ} {A B : E} {F : (ℝ → E) → ℝ → E}
    (ctx : SpliceContext (d₁ + d₂) (x₁ 0) (x₂ d₂) T A B F)
    (hmin : IsMinOn (cvFunctional (fun _ ↦ L) K T)
      (fixedEndpointFinitePiecewiseC1Curves T A B) (F (concatenate d₁ x₁ x₂))) :
    energyCurve L x₁ v₁ d₁ = energyCurve L x₂ v₂ 0 := by
  have href := concatenate_mem_fixedEndpointFinitePiecewiseC1Curves
    (.smooth hd₁ hx₁ hv₁) (.smooth hd₂ hx₂ hv₂) hjoin
  have hamb := ctx.feasible href
  have hm := ctx.action_min L hL.continuous href
    (action_min_of_cvFunctional_min L K hamb.2.1 hmin)
  exact corner_energy_eq_of_cvFunctional_min_weak L (fun _ ↦ 0) hL hx₁ hv₁ hx₂ hv₂
    hd₁ hd₂ hjoin (cvFunctional_min_of_action_min L _ href.2.1 hm)

/-- The weak energy law also holds on every individual C1 arc in any finite context. -/
theorem energy_eq_in_finite_context
    (L : E → E → ℝ) (K : E → ℝ) (hL : ContDiff ℝ 1 L.uncurry)
    {x v : ℝ → E} (hx : ∀ t, HasDerivAt x (v t) t) (hv : Continuous v)
    {d : ℝ} (hd : 0 < d) {T : ℝ} {A B : E} {F : (ℝ → E) → ℝ → E}
    (ctx : SpliceContext d (x 0) (x d) T A B F)
    (hmin : IsMinOn (cvFunctional (fun _ ↦ L) K T)
      (fixedEndpointFinitePiecewiseC1Curves T A B) (F x)) :
    ∀ t ∈ Icc 0 d, energyCurve L x v t = energyCurve L x v 0 := by
  have href : x ∈ fixedEndpointFinitePiecewiseC1Curves d (x 0) (x d) :=
    ⟨rfl, rfl, .smooth hd hx hv⟩
  have hm := ctx.action_min L hL.continuous href
    (action_min_of_cvFunctional_min L K (ctx.feasible href).2.1 hmin)
  exact energy_eq_of_finite_cvFunctional_min L (fun _ ↦ 0) hL hx hv hd
    (cvFunctional_min_of_action_min L _ rfl hm)

end FinitePiecewise
