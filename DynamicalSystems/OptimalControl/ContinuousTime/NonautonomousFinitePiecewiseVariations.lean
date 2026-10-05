/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
import DynamicalSystems.OptimalControl.ContinuousTime.FinitePiecewiseVariations
import DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousTimeReparametrizationFamily

/-!
# Nonautonomous action and finite-piecewise splicing

Physical start times are retained when splitting actual action integrals and when
passing ambient optimality through a finite context to its distinguished subarc.
-/

open MeasureTheory Set Filter
open scoped Topology Interval

namespace FinitePiecewise

open TimeReparametrization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Actual integral action of a local-parameter arc starting at physical time `t₀`. -/
noncomputable def timeAction (L : ℝ → E → E → ℝ) (t₀ T : ℝ) (x : ℝ → E) : ℝ :=
  ∫ t in 0..T, L (t₀ + t) (x t) (deriv x t)

private theorem timeDensity_concatenate_left (L : ℝ → E → E → ℝ) (t₀ : ℝ)
    {s t : ℝ} {x₁ x₂ : ℝ → E} (ht : t < s) :
    L (t₀ + t) (concatenate s x₁ x₂ t) (deriv (concatenate s x₁ x₂) t) =
      L (t₀ + t) (x₁ t) (deriv x₁ t) := by
  have he : concatenate s x₁ x₂ =ᶠ[𝓝 t] x₁ := by
    filter_upwards [Iio_mem_nhds ht] with q hq
    simp [concatenate, (show q < s from hq).le]
  rw [he.deriv_eq]
  simp [concatenate, ht.le]

private theorem timeDensity_concatenate_right (L : ℝ → E → E → ℝ) (t₀ : ℝ)
    {s t : ℝ} {x₁ x₂ : ℝ → E} (ht : s < t) :
    L (t₀ + t) (concatenate s x₁ x₂ t) (deriv (concatenate s x₁ x₂) t) =
      L (t₀ + t) (x₂ (t - s)) (deriv x₂ (t - s)) := by
  have he : concatenate s x₁ x₂ =ᶠ[𝓝 t] fun q ↦ x₂ (q - s) := by
    filter_upwards [Ioi_mem_nhds ht] with q hq
    simp [concatenate, not_le_of_gt (show s < q from hq)]
  rw [he.deriv_eq, deriv_comp_sub_const]
  simp [concatenate, not_le_of_gt ht]

private theorem timeIntegrable_concatenate_parts (L : ℝ → E → E → ℝ) (t₀ : ℝ)
    {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂) {x₁ x₂ : ℝ → E}
    (hi₁ : IntervalIntegrable (fun t ↦ L (t₀ + t) (x₁ t) (deriv x₁ t)) volume 0 d₁)
    (hi₂ : IntervalIntegrable (fun t ↦ L (t₀ + d₁ + t) (x₂ t) (deriv x₂ t)) volume 0 d₂) :
    IntervalIntegrable (fun t ↦ L (t₀ + t) (concatenate d₁ x₁ x₂ t)
      (deriv (concatenate d₁ x₁ x₂) t)) volume 0 d₁ ∧
    IntervalIntegrable (fun t ↦ L (t₀ + t) (concatenate d₁ x₁ x₂ t)
      (deriv (concatenate d₁ x₁ x₂) t)) volume d₁ (d₁ + d₂) := by
  constructor
  · apply hi₁.congr_uIoo
    intro t ht
    symm
    exact timeDensity_concatenate_left L t₀ (show t < d₁ from
      (show t ∈ Ioo 0 d₁ by simpa [uIoo_of_le hd₁.le] using ht).2)
  · have hi := hi₂.comp_sub_right d₁
    have he : ∀ t, t₀ + d₁ + (t - d₁) = t₀ + t := fun t ↦ by ring
    have hi' : IntervalIntegrable
        (fun t ↦ L (t₀ + t) (x₂ (t - d₁)) (deriv x₂ (t - d₁)))
        volume d₁ (d₁ + d₂) := by
      simpa only [zero_add, add_comm d₂ d₁, he] using hi
    apply hi'.congr_uIoo
    intro t ht
    symm
    exact timeDensity_concatenate_right L t₀ (show d₁ < t from
      (show t ∈ Ioo d₁ (d₁ + d₂) by
        simpa [uIoo_of_le (le_add_of_nonneg_right hd₂.le)] using ht).1)

/-- A continuous time-dependent Lagrangian is integrable along each actual finite
piecewise-C1 curve, at every physical start time. -/
theorem IsFinitePiecewiseC1.timeIntervalIntegrable (L : ℝ → E → E → ℝ)
    (hL : Continuous (uncurryLagrangian L)) {T : ℝ} {x : ℝ → E}
    (hx : IsFinitePiecewiseC1 T x) (t₀ : ℝ) :
    IntervalIntegrable (fun t ↦ L (t₀ + t) (x t) (deriv x t)) volume 0 T := by
  induction hx generalizing t₀ with
  | @smooth T x v hT hx hv =>
    have hc : Continuous x := continuous_iff_continuousAt.mpr fun t ↦ (hx t).continuousAt
    simpa only [funext (fun t ↦ (hx t).deriv), Function.comp_def, Pi.add_apply, id_eq,
      uncurryLagrangian] using
      (hL.comp ((continuous_const.add continuous_id).prodMk (hc.prodMk hv))).intervalIntegrable 0 _
  | join h₁ h₂ hj hi₁ hi₂ =>
    have hi := timeIntegrable_concatenate_parts L t₀ h₁.duration_pos h₂.duration_pos
      (hi₁ t₀) (hi₂ _)
    exact hi.1.trans hi.2

/-- Exact physical-time action split for two finite-piecewise arcs. -/
theorem timeAction_concatenate (L : ℝ → E → E → ℝ)
    (hL : Continuous (uncurryLagrangian L)) (t₀ : ℝ)
    {d₁ d₂ : ℝ} {x₁ x₂ : ℝ → E}
    (h₁ : IsFinitePiecewiseC1 d₁ x₁) (h₂ : IsFinitePiecewiseC1 d₂ x₂) :
    timeAction L t₀ (d₁ + d₂) (concatenate d₁ x₁ x₂) =
      timeAction L t₀ d₁ x₁ + timeAction L (t₀ + d₁) d₂ x₂ := by
  have hi := timeIntegrable_concatenate_parts L t₀ h₁.duration_pos h₂.duration_pos
    (h₁.timeIntervalIntegrable L hL t₀) (h₂.timeIntervalIntegrable L hL (t₀ + d₁))
  unfold timeAction
  rw [← intervalIntegral.integral_add_adjacent_intervals hi.1 hi.2]
  congr 1
  · apply intervalIntegral.integral_congr_Ioo_of_le h₁.duration_pos.le
    intro t ht
    exact timeDensity_concatenate_left L t₀ ht.2
  · calc
      _ = ∫ t in d₁..d₁ + d₂, L (t₀ + t) (x₂ (t - d₁)) (deriv x₂ (t - d₁)) := by
        apply intervalIntegral.integral_congr_Ioo_of_le
          (le_add_of_nonneg_right h₂.duration_pos.le)
        intro t ht
        exact timeDensity_concatenate_right L t₀ ht.1
      _ = _ := by
        have he : ∀ t, t₀ + d₁ + (t - d₁) = t₀ + t := fun t ↦ by ring
        simpa only [sub_self, add_sub_cancel_left, he] using
          intervalIntegral.integral_comp_sub_right
            (fun t ↦ L (t₀ + d₁ + t) (x₂ t) (deriv x₂ t))
            (a := d₁) (b := d₁ + d₂) d₁

/-- Cancel the common fixed terminal penalty of the actual shifted functional. -/
theorem timeAction_min_of_cvFunctional_min (L : ℝ → E → E → ℝ) (K : E → ℝ)
    (t₀ : ℝ) {T : ℝ} {a b : E} {x : ℝ → E} (hx : x T = b)
    (hmin : IsMinOn (cvFunctional (fun t ↦ L (t₀ + t)) K T)
      (fixedEndpointFinitePiecewiseC1Curves T a b) x) :
    IsMinOn (timeAction L t₀ T) (fixedEndpointFinitePiecewiseC1Curves T a b) x := by
  intro y hy
  have h := hmin hy
  change timeAction L t₀ T x + K (x T) ≤ timeAction L t₀ T y + K (y T) at h
  rw [hx, hy.2.1] at h
  exact (add_le_add_iff_right _).mp h

/-- Restore the common fixed terminal penalty to the actual shifted functional. -/
theorem cvFunctional_min_of_timeAction_min (L : ℝ → E → E → ℝ) (K : E → ℝ)
    (t₀ : ℝ) {T : ℝ} {a b : E} {x : ℝ → E} (hx : x T = b)
    (hmin : IsMinOn (timeAction L t₀ T) (fixedEndpointFinitePiecewiseC1Curves T a b) x) :
    IsMinOn (cvFunctional (fun t ↦ L (t₀ + t)) K T)
      (fixedEndpointFinitePiecewiseC1Curves T a b) x := by
  intro y hy
  change timeAction L t₀ T x + K (x T) ≤ timeAction L t₀ T y + K (y T)
  rw [hx, hy.2.1]
  have h : timeAction L t₀ T x ≤ timeAction L t₀ T y := hmin hy
  linarith

/-- An actual replacement of the left arc preserves the physical-time right cost. -/
theorem timeAction_min_left (L : ℝ → E → E → ℝ)
    (hL : Continuous (uncurryLagrangian L)) (t₀ : ℝ)
    {d₁ d₂ : ℝ} {x₁ x₂ : ℝ → E}
    (h₁ : IsFinitePiecewiseC1 d₁ x₁) (h₂ : IsFinitePiecewiseC1 d₂ x₂)
    (hjoin : x₁ d₁ = x₂ 0)
    (hmin : IsMinOn (timeAction L t₀ (d₁ + d₂))
      (fixedEndpointFinitePiecewiseC1Curves (d₁ + d₂) (x₁ 0) (x₂ d₂))
      (concatenate d₁ x₁ x₂)) :
    IsMinOn (timeAction L t₀ d₁)
      (fixedEndpointFinitePiecewiseC1Curves d₁ (x₁ 0) (x₁ d₁)) x₁ := by
  intro y hy
  have hj : y d₁ = x₂ 0 := hy.2.1.trans hjoin
  have hm := concatenate_mem_fixedEndpointFinitePiecewiseC1Curves hy.2.2 h₂ hj
  rw [hy.1] at hm
  have h := hmin hm
  change timeAction L t₀ (d₁ + d₂) (concatenate d₁ x₁ x₂) ≤
    timeAction L t₀ (d₁ + d₂) (concatenate d₁ y x₂) at h
  rw [timeAction_concatenate L hL t₀ h₁ h₂, timeAction_concatenate L hL t₀ hy.2.2 h₂] at h
  exact (add_le_add_iff_right _).mp h

/-- Right-arc optimality uses its actual physical start time `t₀ + d₁`. -/
theorem timeAction_min_right (L : ℝ → E → E → ℝ)
    (hL : Continuous (uncurryLagrangian L)) (t₀ : ℝ)
    {d₁ d₂ : ℝ} {x₁ x₂ : ℝ → E}
    (h₁ : IsFinitePiecewiseC1 d₁ x₁) (h₂ : IsFinitePiecewiseC1 d₂ x₂)
    (hjoin : x₁ d₁ = x₂ 0)
    (hmin : IsMinOn (timeAction L t₀ (d₁ + d₂))
      (fixedEndpointFinitePiecewiseC1Curves (d₁ + d₂) (x₁ 0) (x₂ d₂))
      (concatenate d₁ x₁ x₂)) :
    IsMinOn (timeAction L (t₀ + d₁) d₂)
      (fixedEndpointFinitePiecewiseC1Curves d₂ (x₂ 0) (x₂ d₂)) x₂ := by
  intro y hy
  have hj : x₁ d₁ = y 0 := hjoin.trans hy.1.symm
  have hm := concatenate_mem_fixedEndpointFinitePiecewiseC1Curves h₁ hy.2.2 hj
  rw [hy.2.1] at hm
  have h := hmin hm
  change timeAction L t₀ (d₁ + d₂) (concatenate d₁ x₁ x₂) ≤
    timeAction L t₀ (d₁ + d₂) (concatenate d₁ x₁ y) at h
  rw [timeAction_concatenate L hL t₀ h₁ h₂, timeAction_concatenate L hL t₀ h₁ hy.2.2] at h
  exact (add_le_add_iff_left _).mp h

/-- A finite surrounding context with explicit physical start times for its hole
and for the complete curve. Its constructors encode only actual finite joins. -/
inductive TimeSpliceContext (start d : ℝ) (a b : E) :
    ℝ → ℝ → E → E → ((ℝ → E) → ℝ → E) → Prop
  | hole : TimeSpliceContext start d a b start d a b id
  | append {t₀ T s : ℝ} {A B : E} {F : (ℝ → E) → ℝ → E} {z : ℝ → E}
      (ctx : TimeSpliceContext start d a b t₀ T A B F) (hz : IsFinitePiecewiseC1 s z)
      (hj : B = z 0) :
      TimeSpliceContext start d a b t₀ (T + s) A (z s) (fun y ↦ concatenate T (F y) z)
  | prepend {t₀ T s : ℝ} {A B : E} {F : (ℝ → E) → ℝ → E} {z : ℝ → E}
      (ctx : TimeSpliceContext start d a b t₀ T A B F) (hz : IsFinitePiecewiseC1 s z)
      (hj : z s = A) :
      TimeSpliceContext start d a b (t₀ - s) (s + T) (z 0) B
        (fun y ↦ concatenate s z (F y))

/-- Forgetting physical time indices retains the existing actual splice context. -/
theorem TimeSpliceContext.toSpliceContext {start d t₀ T : ℝ} {a b A B : E}
    {F : (ℝ → E) → ℝ → E} (ctx : TimeSpliceContext start d a b t₀ T A B F) :
    SpliceContext d a b T A B F := by
  induction ctx with
  | hole => exact .hole
  | append _ hz hj ih => exact .append ih hz hj
  | prepend _ hz hj ih => exact .prepend ih hz hj

/-- The indexed context maps every actual feasible hole to an actual ambient curve. -/
theorem TimeSpliceContext.feasible {start d t₀ T : ℝ} {a b A B : E}
    {F : (ℝ → E) → ℝ → E} (ctx : TimeSpliceContext start d a b t₀ T A B F)
    {x : ℝ → E} (hx : x ∈ fixedEndpointFinitePiecewiseC1Curves d a b) :
    F x ∈ fixedEndpointFinitePiecewiseC1Curves T A B :=
  ctx.toSpliceContext.feasible hx

/-- Actual ambient optimality passes through any finite context to the hole,
retaining the physical time at which its Lagrangian is evaluated. -/
theorem TimeSpliceContext.timeAction_min (L : ℝ → E → E → ℝ)
    (hL : Continuous (uncurryLagrangian L))
    {start d t₀ T : ℝ} {a b A B : E} {F : (ℝ → E) → ℝ → E}
    (ctx : TimeSpliceContext start d a b t₀ T A B F)
    {x : ℝ → E} (hx : x ∈ fixedEndpointFinitePiecewiseC1Curves d a b)
    (hmin : IsMinOn (timeAction L t₀ T)
      (fixedEndpointFinitePiecewiseC1Curves T A B) (F x)) :
    IsMinOn (timeAction L start d) (fixedEndpointFinitePiecewiseC1Curves d a b) x := by
  induction ctx with
  | append ctx hz hj ih =>
    have hf := ctx.feasible hx
    have hm : IsMinOn _ (fixedEndpointFinitePiecewiseC1Curves _ _ _) _ := hmin
    rw [← hf.1] at hm
    have hh := timeAction_min_left L hL _ hf.2.2 hz (hf.2.1.trans hj) hm
    rw [hf.1, hf.2.1] at hh
    exact ih hh
  | prepend ctx hz hj ih =>
    have hf := ctx.feasible hx
    have hm : IsMinOn _ (fixedEndpointFinitePiecewiseC1Curves _ _ _) _ := hmin
    rw [← hf.2.1] at hm
    have hh := timeAction_min_right L hL _ hz hf.2.2 (hj.trans hf.1.symm) hm
    rw [hf.1, hf.2.1] at hh
    simp only [sub_add_cancel] at hh
    exact ih hh
  | hole => exact hmin

/-- A global minimum of the original unshifted `cvFunctional` implies the
physical-time action minimum in any actual finite surrounding context. -/
theorem TimeSpliceContext.timeAction_min_of_cvFunctional_min
    (L : ℝ → E → E → ℝ) (K : E → ℝ)
    (hL : Continuous (uncurryLagrangian L))
    {start d T : ℝ} {a b A B : E} {F : (ℝ → E) → ℝ → E}
    (ctx : TimeSpliceContext start d a b 0 T A B F)
    {x : ℝ → E} (hx : x ∈ fixedEndpointFinitePiecewiseC1Curves d a b)
    (hmin : IsMinOn (cvFunctional L K T)
      (fixedEndpointFinitePiecewiseC1Curves T A B) (F x)) :
    IsMinOn (timeAction L start d) (fixedEndpointFinitePiecewiseC1Curves d a b) x := by
  apply ctx.timeAction_min L hL hx
  apply FinitePiecewise.timeAction_min_of_cvFunctional_min L K 0
    (ctx.feasible hx).2.1
  simpa only [zero_add] using hmin

end FinitePiecewise
