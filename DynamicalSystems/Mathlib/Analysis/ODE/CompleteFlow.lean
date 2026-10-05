/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.ODE.ContinuousDependence
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Continuous flows of complete locally Lipschitz vector fields

A complete autonomous vector field supplies an integral curve through every
state. Local Lipschitz uniqueness makes these curves a group action, and
continuous dependence makes that action a continuous `Flow`. Completeness of
the state space is not needed once completeness of the vector field is given.
-/

@[expose] public noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace IsCompleteVectorField

variable {f : E → E}

/-- Every complete locally Lipschitz autonomous vector field generates a
continuous flow. The time variable is the first argument of the bundled flow. -/
def flow (hf : IsCompleteVectorField (fun _ ↦ f)) (h : LocallyLipschitz f) : Flow ℝ E where
  toFun t x := hf.flowAt 0 x t
  cont' :=
    (hf.flowAt_isFundamentalSolution.continuous_of_uniformlyLocallyLipschitz
      h.uniformlyLocallyLipschitz 0).comp continuous_swap
  map_add' := by
    intro t₁ t₂ x
    exact (hf.flowAt_isFundamentalSolution.add_apply'' f h t₁ t₂ x).symm
  map_zero' := hf.flowAt_zero 0

/-- The bundled flow uses the supplied integral curve with initial time zero. -/
theorem flow_apply (hf : IsCompleteVectorField (fun _ ↦ f)) (h : LocallyLipschitz f)
    (t : ℝ) (x : E) : hf.flow h t x = hf.flowAt 0 x t := rfl

/-- Each orbit of the generated flow solves the original autonomous ODE. -/
theorem isIntegralCurve_flow (hf : IsCompleteVectorField (fun _ ↦ f))
    (h : LocallyLipschitz f) (x : E) : IsIntegralCurve (hf.flow h · x) (fun _ ↦ f) :=
  hf.flowAt_isIntegralCurve 0 x

@[fun_prop]
theorem differentiable_flow (hf : IsCompleteVectorField (fun _ ↦ f))
    (h : LocallyLipschitz f) (x : E) : Differentiable ℝ (hf.flow h · x) :=
  hf.differentiable_flowAt 0 x

/-- Derivative of a generated flow orbit, in the form used by chain rules. -/
theorem hasDerivAt_flow (hf : IsCompleteVectorField (fun _ ↦ f))
    (h : LocallyLipschitz f) (t : ℝ) (x : E) :
    HasDerivAt (hf.flow h · x) (f (hf.flow h t x)) t :=
  hf.isIntegralCurve_flow h x t

@[simp]
theorem deriv_flow (hf : IsCompleteVectorField (fun _ ↦ f))
    (h : LocallyLipschitz f) (t : ℝ) (x : E) :
    deriv (hf.flow h · x) t = f (hf.flow h t x) :=
  (hf.hasDerivAt_flow h t x).deriv

variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative of an observable along the generated flow is its Fréchet
derivative applied to the vector field. -/
theorem deriv_comp_flow {v : E → F} (hv : Differentiable ℝ v)
    (hf : IsCompleteVectorField (fun _ ↦ f)) (h : LocallyLipschitz f)
    (t : ℝ) (x : E) :
    deriv (fun s ↦ v (hf.flow h s x)) t =
      fderiv ℝ v (hf.flow h t x) (f (hf.flow h t x)) := by
  calc
    _ = fderiv ℝ v (hf.flow h t x) (deriv (hf.flow h · x) t) :=
      fderiv_comp_deriv t (hv _) (hf.differentiable_flow h x t)
    _ = _ := by rw [hf.deriv_flow]

end IsCompleteVectorField
