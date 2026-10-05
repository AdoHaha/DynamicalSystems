/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
import DynamicalSystems.OptimalControl.ContinuousTime.K3IsoperimetricLift
import DynamicalSystems.OptimalControl.ContinuousTime.PiecewiseC1MinimumPrinciple
import Lean

/-!
# Actual proof-term paths through the completed K3/K4 constructions

These checks complement semantic review: they confirm that the final results
reference the genuine constructed families, actual functional derivatives,
derived momentum regularity, and weak energy arguments advertised in the report.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let rec depends (origin current target : Name) (fuel : Nat) : Bool :=
    match fuel with
    | 0 => false
    | fuel + 1 =>
      match env.find? current with
      | none => false
      | some decl =>
        match decl.value? true with
        | none => false
        | some proof =>
          let used := proof.getUsedConstants
          used.contains target || used.any (fun n =>
            origin.isPrefixOf n && n != current && depends origin n target fuel)
  let links : List (Name × Name) := [
    (``FinitePiecewise.weierstrassErdmann_of_piecewiseC1On_min,
      ``FinitePiecewise.weierstrassErdmann_of_original_piecewiseC1_min),
    (``FinitePiecewise.weierstrassErdmann_of_original_piecewiseC1_min,
      ``PiecewiseC1Extensions.exists_global_arcs),
    (``FinitePiecewise.weierstrassErdmann_of_original_piecewiseC1_min,
      ``FinitePiecewise.nonautonomous_weierstrassErdmann_at_every_represented_corner),
    (``FinitePiecewise.nonautonomous_weierstrassErdmann_at_every_represented_corner,
      ``cvFunctional_eq_of_eqOn),
    (``FinitePiecewise.nonautonomous_weierstrassErdmann_at_every_represented_corner,
      ``FinitePiecewise.weierstrassErdmann_in_timeSpliceContext),
    (``FinitePiecewise.weierstrassErdmann_in_timeSpliceContext,
      ``FinitePiecewise.corner_momentum_eq_in_timeSpliceContext),
    (``FinitePiecewise.weierstrassErdmann_in_timeSpliceContext,
      ``FinitePiecewise.corner_energy_eq_in_timeSpliceContext),
    (``FinitePiecewise.corner_momentum_eq_in_timeSpliceContext,
      ``FinitePiecewise.TimeSpliceContext.timeAction_min),
    (``FinitePiecewise.corner_momentum_eq_in_timeSpliceContext,
      ``FinitePiecewise.corner_momentum_eq_of_timeAction_min),
    (``FinitePiecewise.corner_momentum_eq_of_timeAction_min,
      ``FinitePiecewise.interior_EL_of_timeAction_min),
    (``FinitePiecewise.corner_momentum_eq_of_timeAction_min,
      ``FinitePiecewise.twoArc_firstVariation_zero_of_timeAction_min),
    (``FinitePiecewise.corner_momentum_eq_of_timeAction_min,
      ``FinitePiecewise.firstVariation_eq_boundary_of_interior_EL),
    (``FinitePiecewise.interior_EL_of_timeAction_min,
      ``WeakEulerLagrange.eulerLagrange_hasDerivAt_of_fixedEndpoint_min),
    (``FinitePiecewise.twoArc_firstVariation_zero_of_timeAction_min,
      ``hasDerivAt_cvFunctional_affine),
    (``FinitePiecewise.twoArc_firstVariation_zero_of_timeAction_min,
      ``FinitePiecewise.timeAction_concatenate),
    (``FinitePiecewise.corner_energy_eq_in_timeSpliceContext,
      ``FinitePiecewise.TimeSpliceContext.timeAction_min),
    (``FinitePiecewise.corner_energy_eq_in_timeSpliceContext,
      ``FinitePiecewise.corner_energy_eq_of_timeAction_min_weak),
    (``FinitePiecewise.corner_energy_eq_of_timeAction_min_weak,
      ``FinitePiecewise.weak_duBoisReymond_of_finite_cvFunctional_min),
    (``FinitePiecewise.corner_energy_eq_of_timeAction_min_weak,
      ``NonautonomousDuBoisReymond.corner_energy_eq_of_weak_dbr_min),
    (``FinitePiecewise.corner_energy_eq_of_timeAction_min_weak,
      ``NonautonomousTimeReparametrization.fixedParameterCost_isLocalMin_of_ambient_min),
    (``FinitePiecewise.weak_duBoisReymond_of_finite_cvFunctional_min,
      ``NonautonomousDuBoisReymond.weak_duBoisReymond_of_all_duration_exchange_min),
    (``FinitePiecewise.weak_duBoisReymond_of_finite_cvFunctional_min,
      ``NonautonomousTimeReparametrization.fixedParameterCost_isLocalMin_of_ambient_min),
    (``FinitePiecewise.weak_duBoisReymond_of_finite_cvFunctional_min,
      ``FinitePiecewise.durationExchange_mem_fixedEndpointFinitePiecewiseC1Curves),
    (``IsoperimetricVariation.augmentedEulerLagrange_of_isoperimetric,
      ``IsoperimetricVariation.augmentedEulerLagrangeWithin_of_isoperimetric),
    (``IsoperimetricVariation.augmentedEulerLagrange_of_isoperimetric,
      ``contDiff_momentumCovector_of_contDiff_two),
    (``IsoperimetricVariation.augmentedEulerLagrangeWithin_of_isoperimetric,
      ``IsoperimetricVariation.exists_augmented_stationarity_of_isoperimetric),
    (``IsoperimetricVariation.augmentedEulerLagrangeWithin_of_isoperimetric,
      ``WeakEulerLagrange.eulerLagrange_hasDerivWithinAt_of_firstVariation_zero),
    (``IsoperimetricVariation.augmentedEulerLagrangeWithin_of_isoperimetric,
      ``hasVanishingFirstVariation_of_eulerLagrange_within),
    (``IsoperimetricVariation.exists_augmented_stationarity_of_isoperimetric,
      ``IsoperimetricVariation.exists_common_isoperimetricMultiplier),
    (``IsoperimetricVariation.exists_augmented_stationarity_of_isoperimetric,
      ``firstVariation_add_smul),
    (``IsoperimetricVariation.exists_common_isoperimetricMultiplier,
      ``IsoperimetricVariation.isoperimetricMultiplier_exists),
    (``IsoperimetricVariation.exists_common_isoperimetricMultiplier,
      ``perturbedCurve_mem_fixedEndpointC1Curves),
    (``IsoperimetricVariation.isoperimetricMultiplier_exists,
      ``hasStrictFDerivAt_cvFunctional_perturbed),
    (``IsoperimetricVariation.isoperimetricMultiplier_exists,
      ``IsoperimetricVariation.exists_normal_multiplier_of_curve_family),
    (``hasStrictFDerivAt_parameterFunctional,
      ``hasStrictFDerivAt_cvFunctional_perturbed),
    (``hasStrictFDerivAt_cvFunctional_perturbed,
      ``hasStrictFDerivAt_perturbedIntegral),
    (``WeakEulerLagrange.momentum_hasDerivWithinAt_of_stationary,
      ``WeakEulerLagrange.momentum_eq_add_integral_of_stationary),
    (``WeakEulerLagrange.momentum_eq_add_integral_of_stationary,
      ``WeakEulerLagrange.eq_const_of_integral_mul_deriv_eq_zero),
    (``WeakEulerLagrange.firstVariation_zero_of_fixedEndpoint_min,
      ``hasDerivAt_cvFunctional_affine),
    (``hasDerivAt_cvFunctional_affine,
      ``hasStrictFDerivAt_cvFunctional_perturbed),
    (``NonautonomousDuBoisReymond.weak_duBoisReymond_of_cvFunctional_min,
      ``NonautonomousDuBoisReymond.weak_duBoisReymond_of_all_duration_exchange_min),
    (``NonautonomousDuBoisReymond.weak_duBoisReymond_of_all_duration_exchange_min,
      ``NonautonomousDuBoisReymond.hat_integral_eq_of_duration_exchange_min),
    (``NonautonomousDuBoisReymond.weak_duBoisReymond_of_all_duration_exchange_min,
      ``DuBoisReymond.compensated_eq_of_hat_integral_eq),
    (``NonautonomousDuBoisReymond.hat_integral_eq_of_duration_exchange_min,
      ``NonautonomousDuBoisReymond.hasDerivAt_fixedParameterCost),
    (``NonautonomousDuBoisReymond.hasDerivAt_fixedParameterCost,
      ``NonautonomousTimeReparametrization.hasDerivAt_movingArcCost),
    (``NonautonomousDuBoisReymond.corner_energy_eq_of_weak_dbr_min,
      ``NonautonomousDuBoisReymond.integral_weighted_energy_eq),
    (``NonautonomousDuBoisReymond.corner_energy_eq_of_weak_dbr_min,
      ``NonautonomousDuBoisReymond.hasDerivAt_fixedParameterCost),
    (``NonautonomousTimeReparametrization.fixedParameterCost_isLocalMin_of_ambient_min,
      ``NonautonomousTimeReparametrization.cvFunctional_durationExchange),
    (``NonautonomousTimeReparametrization.cvFunctional_durationExchange,
      ``NonautonomousTimeReparametrization.cvFunctional_concatenate)]
  for (source, target) in links do
    unless depends source source target 8 do
      throwError "Missing proof dependency: {source} -> {target}"
    logInfo m!"checked proof dependency: {source} -> {target}"
  logInfo m!"Verified {links.length} actual K3/K4 proof-term edges."
