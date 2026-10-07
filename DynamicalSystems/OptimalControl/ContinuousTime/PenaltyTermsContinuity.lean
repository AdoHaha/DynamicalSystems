/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.EpsilonOptimality
public import DynamicalSystems.OptimalControl.ContinuousTime.RelaxedSliceIntegralContinuity

/-!
# Continuity of the running-cost and Volterra-residual terms of `F_K`

For a continuous parameterised family of state paths `π : Q → P.Trajectory` (uniform topology),
the relaxed running cost and the Volterra residual energy of Berkovitz & Medhin (11.3.6) are
jointly continuous in `(parameter, relaxed control)`, the relaxed control carrying the weak
topology.  These are the non-velocity, non-endpoint terms that the direct method needs to be
(lower semicontinuous) continuous.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), (11.3.6).
Names are concept names; the citation lives in docstrings.
-/

@[expose] public section

open Set MeasureTheory
open scoped Topology BoundedContinuousFunction

namespace OptimalControl.BoundedState.Problem

variable {E V W : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]
  {Q : Type*} [TopologicalSpace Q]

omit [FiniteDimensional ℝ E] in
/-- **Continuity of the relaxed running cost** in the (uniform) path parameter and the weak
relaxed control.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.6). -/
theorem continuous_relaxedCost_param (P : Problem E V W) (π : Q → P.Trajectory)
    (hπ : Continuous π) :
    Continuous (fun q : Q × P.Relaxed => P.relaxedCost (π q.1) q.2) := by
  have hF : Continuous (Function.uncurry fun (p : Q) (z : P.Time × P.Control) =>
      P.runningCost z.1 (π p z.1) (z.2 : V)) := by
    have hev : Continuous fun y : Q × (P.Time × P.Control) => π y.1 y.2.1 :=
      (hπ.comp continuous_fst).eval (continuous_fst.comp continuous_snd)
    exact P.runningCost_continuous.comp
      ((continuous_fst.comp continuous_snd |>.prodMk hev).prodMk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))
  have hc := OptimalControl.RelaxedControl.continuous_setIntegral_param
    (ν := horizonProbability P.horizon P.horizon_pos)
    (fun (p : Q) (z : P.Time × P.Control) => P.runningCost z.1 (π p z.1) (z.2 : V))
    hF MeasurableSet.univ
  have h2 : Continuous fun p : Q × P.Relaxed => ∫ z, P.runningCost z.1 (π p.1 z.1) (z.2 : V)
      ∂p.2.measure := by
    simpa only [univ_prod_univ, setIntegral_univ] using hc
  exact h2

/-- **Continuity of the Volterra residual energy** `∫ ‖φ(t) − x₀ − t₁ ∫_{(0,t]} f dρ‖² dt`
(normalised horizon measure) in the path parameter and the weak relaxed control.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.6). -/
theorem continuous_dynamicsResidualEnergy_param (P : Problem E V W) (π : Q → P.Trajectory)
    (hπ : Continuous π) :
    Continuous (fun q : Q × P.Relaxed =>
      ∫ t, ‖P.dynamicsResidual (π q.1) q.2 t‖ ^ 2
        ∂(horizonProbability P.horizon P.horizon_pos).toMeasure) := by
  have hF : Continuous (Function.uncurry fun (p : Q) (z : P.Time × P.Control) =>
      P.dynamics z.1 (π p z.1) (z.2 : V)) := by
    have hev : Continuous fun y : Q × (P.Time × P.Control) => π y.1 y.2.1 :=
      (hπ.comp continuous_fst).eval (continuous_fst.comp continuous_snd)
    exact P.dynamics_continuous.comp
      ((continuous_fst.comp continuous_snd |>.prodMk hev).prodMk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))
  have hS := OptimalControl.RelaxedControl.continuous_sliceIntegral_joint
    (hT := P.horizon_pos)
    (fun (p : Q) (z : P.Time × P.Control) => P.dynamics z.1 (π p z.1) (z.2 : V)) hF
  have hX : Continuous fun y : (Q × P.Relaxed) × P.Time => π y.1.1 y.2 :=
    (hπ.comp (continuous_fst.comp continuous_fst)).eval continuous_snd
  have hR : Continuous (Function.uncurry fun (x : Q × P.Relaxed) (t : P.Time) =>
      ‖P.dynamicsResidual (π x.1) x.2 t‖ ^ 2) := by
    refine (Continuous.pow ?_ 2)
    refine Continuous.norm ?_
    exact ((hX.sub continuous_const).sub (continuous_const.smul hS))
  exact OptimalControl.RelaxedControl.continuous_integral_of_jointly_continuous _ _ hR

end OptimalControl.BoundedState.Problem
