/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.RealBohlTransport

/-! # Geometric necessity for generic controller state

The first Corollary 6.22 inclusion is extracted from a stable dynamic external
response for any finite-dimensional real controller state space. The plant
component of the closed-loop orbit is an open-loop variation-of-constants
trajectory with real Bohl forcing.
-/

@[expose] public section

open Filter Topology Set
open scoped Topology Matrix

namespace LinearSystem

noncomputable section

variable {X U Y D Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [AddCommGroup Y] [Module ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- The canonical generic zero-`F` interconnection associated with a dynamic
controller of state space `W`. -/
def genericZeroFInterconnection (sys : LinearSystem ℝ X U Y)
    (ctrl : DynamicController ℝ W Y U) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    DynamicInterconnection ℝ X U Y W D Z :=
  ⟨sys, ctrl, E, 0, H⟩

/-- Generic-`W` version of
`closedLoop_expFlow_fst_eq_variationOfConstants`: the plant component of the
closed-loop orbit is the variation-of-constants trajectory driven by the
resolved input. -/
lemma closedLoop_expFlow_fst_eq_variationOfConstants_generic
    (sys : LinearSystem ℝ X U Y) (sysZ : LinearSystem ℝ X U Z)
    (hA : sysZ.A = sys.A) (hB : sysZ.B = sys.B)
    (ctrl : DynamicController ℝ W Y U)
    (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) (d : D) :
    let ic := genericZeroFInterconnection sys ctrl E H
    let hwp := ic.isWellPosed_of_D_eq_zero hD
    let p : ℝ → X × W := fun t => (ic.closedLoopSystem hwp).expFlow t (E d, 0)
    let u : ℝ → U := fun t => ic.solvedInput hwp (p t)
    (fun t : ℝ => (p t).1) = sysZ.variationOfConstants 0 (E d) u := by
  classical
  intro ic hwp p u
  let x : ℝ → X := fun t => (p t).1
  have hx_cont : Continuous x := by
    rw [continuous_iff_continuousAt]
    intro t
    have hpderiv : HasDerivAt (fun s : ℝ => (ic.closedLoopSystem hwp).expFlow s (E d, 0))
        ((ic.closedLoopSystem hwp).A ((ic.closedLoopSystem hwp).expFlow t (E d, 0))) t :=
      hasDerivAt_expFlow_apply_state (ic.closedLoopSystem hwp) t (E d, 0)
    have hxderiv0 : HasDerivAt (fun s : ℝ => ((ic.closedLoopSystem hwp).expFlow s
        (E d, 0)).1)
        (((ic.closedLoopSystem hwp).A ((ic.closedLoopSystem hwp).expFlow t (E d, 0))).1) t :=
      (ContinuousLinearMap.fst ℝ X W).hasFDerivAt.comp_hasDerivAt t hpderiv
    have hxderiv : HasDerivAt x
        (((ic.closedLoopSystem hwp).A ((ic.closedLoopSystem hwp).expFlow t (E d, 0))).1) t := by
      simpa [x, p] using hxderiv0
    exact hxderiv.continuousAt
  have hu_cont : Continuous u := by
    have hp_cont : Continuous p := by
      rw [continuous_iff_continuousAt]
      intro t
      exact (hasDerivAt_expFlow_apply_state (ic.closedLoopSystem hwp) t (E d, 0)).continuousAt
    exact (ic.solvedInput hwp).continuous_of_finiteDimensional.comp hp_cont
  have hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume := hu_cont.locallyIntegrable
  have hx0 : x 0 = E d := by
    simp [x, p, LinearSystem.expFlow_zero]
  have hxderiv (t : ℝ) : HasDerivAt x (sys.dynamics (x t) (u t)) t := by
    have hpderiv : HasDerivAt (fun s : ℝ => (ic.closedLoopSystem hwp).expFlow s (E d, 0))
        ((ic.closedLoopSystem hwp).A ((ic.closedLoopSystem hwp).expFlow t (E d, 0))) t :=
      hasDerivAt_expFlow_apply_state (ic.closedLoopSystem hwp) t (E d, 0)
    have hxderiv0 : HasDerivAt (fun s : ℝ => ((ic.closedLoopSystem hwp).expFlow s
        (E d, 0)).1)
        (((ic.closedLoopSystem hwp).A ((ic.closedLoopSystem hwp).expFlow t (E d, 0))).1) t :=
      (ContinuousLinearMap.fst ℝ X W).hasFDerivAt.comp_hasDerivAt t hpderiv
    have hxderiv' : HasDerivAt x
        (((ic.closedLoopSystem hwp).A ((ic.closedLoopSystem hwp).expFlow t (E d, 0))).1) t := by
      simpa [x, p] using hxderiv0
    have hAe : ((ic.closedLoopSystem hwp).A ((ic.closedLoopSystem hwp).expFlow t
        (E d, 0))).1 = sys.dynamics (x t) (u t) := by
      have hfst := ic.closedLoopMap_fst hwp (p t)
      change (ic.closedLoopMap hwp (p t)).1 = sys.dynamics (x t) (u t)
      rw [hfst]
      change sys.A (p t).1 + sys.B (ic.solvedInput hwp (p t)) =
        sys.dynamics (x t) (u t)
      simp [x, p, u, LinearSystem.dynamics]
    convert hxderiv' using 1
    exact hAe.symm
  have hxderivZ (t : ℝ) : HasDerivAt x (sysZ.dynamics (x t) (u t)) t := by
    simpa [LinearSystem.dynamics, ← hA, ← hB] using hxderiv t
  have hx_int : ∀ t : ℝ, x t = E d + ∫ s in (0 : ℝ)..t, sysZ.dynamics (x s) (u s) := by
    intro t
    have hcont' : Continuous (fun s : ℝ => sysZ.dynamics (x s) (u s)) :=
      (sysZ.A.toContinuousLinearMap.continuous.comp hx_cont).add
        (sysZ.B.toContinuousLinearMap.continuous.comp hu_cont)
    have hFTC := intervalIntegral.sub_eq_integral_of_hasDerivAt
      (f := x) (f' := fun s : ℝ => sysZ.dynamics (x s) (u s))
      (fun s => hxderivZ s) hcont' 0 t
    rw [hx0] at hFTC
    rw [← hFTC]
    abel
  exact (integralSolution_unique sysZ 0 (E d) u hu
    hx_cont hx0 hx_int
    (continuous_variationOfConstants sysZ 0 (E d) u hu)
    (variationOfConstants_self sysZ 0 (E d) u)
    (fun t => variationOfConstants_integral sysZ 0 (E d) u hu t))

/-- **First geometric necessity inclusion for an arbitrary finite-dimensional
real controller state space `W`.** Given a dynamic controller `ctrl` of state
space `W` and pointwise decay of the external response of the generic zero-`F`
interconnection, the disturbance image lies in the output-stabilizable
subspace. -/
theorem range_E_le_outputStabilizableSubspace_of_genericStableResponse
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (ctrl : DynamicController ℝ W Y U) :
    (∀ d : D, Filter.Tendsto
      (fun t : ℝ => (genericZeroFInterconnection sys ctrl E H).externalResponse
        ((genericZeroFInterconnection sys ctrl E H).isWellPosed_of_D_eq_zero hD) t d)
      Filter.atTop (nhds 0)) →
    LinearMap.range E ≤ outputStabilizableSubspace sys.A sys.B H := by
  intro hdec
  classical
  let sysZ : LinearSystem ℝ X U Z := ⟨sys.A, sys.B, H, 0⟩
  rintro _ ⟨d, rfl⟩
  let ic := genericZeroFInterconnection sys ctrl E H
  let hwp := ic.isWellPosed_of_D_eq_zero hD
  let p : ℝ → X × W := fun t => (ic.closedLoopSystem hwp).expFlow t (E d, 0)
  let u : ℝ → U := fun t => ic.solvedInput hwp (p t)
  have hp_cont : Continuous p := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hasDerivAt_expFlow_apply_state (ic.closedLoopSystem hwp) t (E d, 0)).continuousAt
  have hu_cont : Continuous u :=
    (ic.solvedInput hwp).continuous_of_finiteDimensional.comp hp_cont
  have hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume := hu_cont.locallyIntegrable
  have hpBohl : IsRealBohl (fun t : ℝ => p t) := by
    have hfun : (fun t : ℝ => p t) =
        fun t : ℝ => NormedSpace.exp (t • (ic.closedLoopMap hwp).toContinuousLinearMap)
          (E d, 0) := by
      funext t
      simp [p, ic.closedLoopSystem_expFlow_eq hwp]
    rw [hfun]
    exact isRealBohl_expFlow_of_realLinear (ic.closedLoopMap hwp) (E d, 0)
  let r : X × W →ₗ[ℝ] (Fin (Module.finrank ℝ X) → ℂ) :=
    (coordComplexify (X := X)).comp (sys.B.comp (ic.solvedInput hwp))
  let rC : (Fin (Module.finrank ℝ (X × W)) → ℂ) →ₗ[ℝ]
      (Fin (Module.finrank ℝ X) → ℂ) := r.comp (coordRealify (X := X × W))
  have hBu : IsRealBohl (fun t : ℝ => sys.B (u t)) := by
    change IsExponentialPolynomial (fun t : ℝ => coordComplexify (sys.B (u t)))
    have hfun : (fun t : ℝ => coordComplexify (sys.B (u t))) =
        fun t : ℝ => rC (coordComplexify (p t)) := by
      funext t
      simp [u, r, rC, LinearMap.comp_apply, coordRealify_coordComplexify]
    rw [hfun]
    exact hpBohl.map_realLinear rC.toContinuousLinearMap
  have hresp_fun : (fun t : ℝ => ic.externalResponse hwp t d) = fun t : ℝ => H (p t).1 := by
    funext t
    rw [ic.externalResponse_apply]
    have hdist : ic.disturbanceMapWithF hwp d = (E d, 0) := by
      rw [ic.disturbanceMapWithF_of_F_eq_zero hwp rfl, ic.disturbanceMap_apply]
      change (E d, 0) = (E d, 0)
      rfl
    rw [hdist, ic.outputMap_apply]
    change H (((ic.closedLoopSystem hwp).expFlow t) (E d, 0)).1 = H (p t).1
    simp [p]
  have hdec_ic : Filter.Tendsto (fun t : ℝ => ic.externalResponse hwp t d)
      Filter.atTop (nhds 0) := by
    simpa [ic, hwp] using hdec d
  have hresp : Filter.Tendsto (fun t : ℝ => H (p t).1) Filter.atTop (nhds 0) := by
    convert hdec_ic using 1
    funext t
    exact (congrFun hresp_fun t).symm
  have htraj : (fun t : ℝ => (p t).1) = sysZ.variationOfConstants 0 (E d) u := by
    simpa [ic, hwp, p, u] using
      (closedLoop_expFlow_fst_eq_variationOfConstants_generic sys sysZ rfl rfl ctrl hD E H d)
  have hdecZ : Filter.Tendsto
      (fun t : ℝ => H (sysZ.variationOfConstants 0 (E d) u t)) Filter.atTop (nhds 0) := by
    have hfun : (fun t : ℝ => H (sysZ.variationOfConstants 0 (E d) u t)) =
        fun t : ℝ => H (p t).1 := by
      funext t
      rw [← congrFun htraj t]
    rw [hfun]
    exact hresp
  have hbohl : IsRealBohlOutputStabilizable sysZ H (E d) := ⟨u, hu, hBu, hdecZ⟩
  simpa [sysZ] using finiteBohlWBridge_real sysZ H (E d) hbohl

end

end LinearSystem
