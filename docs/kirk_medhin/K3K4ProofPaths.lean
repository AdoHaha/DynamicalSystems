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
    (``KirkMedhin.FinitePiecewise.weierstrassErdmann_of_piecewiseC1On_min,
      ``KirkMedhin.FinitePiecewise.weierstrassErdmann_of_original_piecewiseC1_min),
    (``KirkMedhin.FinitePiecewise.weierstrassErdmann_of_original_piecewiseC1_min,
      ``KirkMedhin.PiecewiseC1Extensions.exists_global_arcs),
    (``KirkMedhin.FinitePiecewise.weierstrassErdmann_of_original_piecewiseC1_min,
      ``KirkMedhin.FinitePiecewise.nonautonomous_weierstrassErdmann_at_every_represented_corner),
    (``KirkMedhin.FinitePiecewise.nonautonomous_weierstrassErdmann_at_every_represented_corner,
      ``KirkMedhin.FinitePiecewise.cvFunctional_eq_of_eqOn),
    (``KirkMedhin.FinitePiecewise.nonautonomous_weierstrassErdmann_at_every_represented_corner,
      ``KirkMedhin.FinitePiecewise.weierstrassErdmann_in_timeSpliceContext),
    (``KirkMedhin.FinitePiecewise.weierstrassErdmann_in_timeSpliceContext,
      ``KirkMedhin.FinitePiecewise.corner_momentum_eq_in_timeSpliceContext),
    (``KirkMedhin.FinitePiecewise.weierstrassErdmann_in_timeSpliceContext,
      ``KirkMedhin.FinitePiecewise.corner_energy_eq_in_timeSpliceContext),
    (``KirkMedhin.FinitePiecewise.corner_momentum_eq_in_timeSpliceContext,
      ``KirkMedhin.FinitePiecewise.TimeSpliceContext.timeAction_min),
    (``KirkMedhin.FinitePiecewise.corner_momentum_eq_in_timeSpliceContext,
      ``KirkMedhin.FinitePiecewise.corner_momentum_eq_of_timeAction_min),
    (``KirkMedhin.FinitePiecewise.corner_momentum_eq_of_timeAction_min,
      ``KirkMedhin.FinitePiecewise.interior_EL_of_timeAction_min),
    (``KirkMedhin.FinitePiecewise.corner_momentum_eq_of_timeAction_min,
      ``KirkMedhin.FinitePiecewise.twoArc_firstVariation_zero_of_timeAction_min),
    (``KirkMedhin.FinitePiecewise.corner_momentum_eq_of_timeAction_min,
      ``KirkMedhin.FinitePiecewise.firstVariation_eq_boundary_of_interior_EL),
    (``KirkMedhin.FinitePiecewise.interior_EL_of_timeAction_min,
      ``KirkMedhin.WeakCoV.eulerLagrange_hasDerivAt_of_fixedEndpoint_min),
    (``KirkMedhin.FinitePiecewise.twoArc_firstVariation_zero_of_timeAction_min,
      ``KirkMedhin.WeakCoV.hasDerivAt_cvFunctional_affine),
    (``KirkMedhin.FinitePiecewise.twoArc_firstVariation_zero_of_timeAction_min,
      ``KirkMedhin.FinitePiecewise.timeAction_concatenate),
    (``KirkMedhin.FinitePiecewise.corner_energy_eq_in_timeSpliceContext,
      ``KirkMedhin.FinitePiecewise.TimeSpliceContext.timeAction_min),
    (``KirkMedhin.FinitePiecewise.corner_energy_eq_in_timeSpliceContext,
      ``KirkMedhin.FinitePiecewise.corner_energy_eq_of_timeAction_min_weak),
    (``KirkMedhin.FinitePiecewise.corner_energy_eq_of_timeAction_min_weak,
      ``KirkMedhin.FinitePiecewise.weak_duBoisReymond_of_finite_cvFunctional_min),
    (``KirkMedhin.FinitePiecewise.corner_energy_eq_of_timeAction_min_weak,
      ``KirkMedhin.NonautonomousDuBoisReymond.corner_energy_eq_of_weak_dbr_min),
    (``KirkMedhin.FinitePiecewise.corner_energy_eq_of_timeAction_min_weak,
      ``KirkMedhin.NonautonomousTimeReparametrization.fixedParameterCost_isLocalMin_of_ambient_min),
    (``KirkMedhin.FinitePiecewise.weak_duBoisReymond_of_finite_cvFunctional_min,
      ``KirkMedhin.NonautonomousDuBoisReymond.weak_duBoisReymond_of_all_duration_exchange_min),
    (``KirkMedhin.FinitePiecewise.weak_duBoisReymond_of_finite_cvFunctional_min,
      ``KirkMedhin.NonautonomousTimeReparametrization.fixedParameterCost_isLocalMin_of_ambient_min),
    (``KirkMedhin.FinitePiecewise.weak_duBoisReymond_of_finite_cvFunctional_min,
      ``KirkMedhin.FinitePiecewise.durationExchange_mem_fixedEndpointFinitePiecewiseC1Curves),
    (``KirkMedhin.K3.augmentedEulerLagrange_of_isoperimetric,
      ``KirkMedhin.K3.augmentedEulerLagrangeWithin_of_isoperimetric),
    (``KirkMedhin.K3.augmentedEulerLagrange_of_isoperimetric,
      ``KirkMedhin.K3.contDiff_momentumCovector_of_contDiff_two),
    (``KirkMedhin.K3.augmentedEulerLagrangeWithin_of_isoperimetric,
      ``KirkMedhin.K3.exists_augmented_stationarity_of_isoperimetric),
    (``KirkMedhin.K3.augmentedEulerLagrangeWithin_of_isoperimetric,
      ``KirkMedhin.WeakCoV.eulerLagrange_hasDerivWithinAt_of_firstVariation_zero),
    (``KirkMedhin.K3.augmentedEulerLagrangeWithin_of_isoperimetric,
      ``hasVanishingFirstVariation_of_eulerLagrange_within),
    (``KirkMedhin.K3.exists_augmented_stationarity_of_isoperimetric,
      ``KirkMedhin.K3.exists_common_isoperimetricMultiplier),
    (``KirkMedhin.K3.exists_augmented_stationarity_of_isoperimetric,
      ``KirkMedhin.K3.firstVariation_augmented),
    (``KirkMedhin.K3.exists_common_isoperimetricMultiplier,
      ``KirkMedhin.K3.isoperimetricMultiplier_exists),
    (``KirkMedhin.K3.exists_common_isoperimetricMultiplier,
      ``KirkMedhin.K3.perturbedCurve_mem_fixedEndpointC1Curves),
    (``KirkMedhin.K3.isoperimetricMultiplier_exists,
      ``KirkMedhin.K3.hasStrictFDerivAt_cvFunctional_perturbed),
    (``KirkMedhin.K3.isoperimetricMultiplier_exists,
      ``IsoperimetricVariation.exists_normal_multiplier_of_curve_family),
    (``KirkMedhin.K3.hasStrictFDerivAt_parameterFunctional,
      ``KirkMedhin.K3.hasStrictFDerivAt_cvFunctional_perturbed),
    (``KirkMedhin.K3.hasStrictFDerivAt_cvFunctional_perturbed,
      ``KirkMedhin.K3.hasStrictFDerivAt_perturbedIntegral),
    (``KirkMedhin.WeakCoV.momentum_hasDerivWithinAt_of_stationary,
      ``KirkMedhin.WeakCoV.momentum_eq_add_integral_of_stationary),
    (``KirkMedhin.WeakCoV.momentum_eq_add_integral_of_stationary,
      ``KirkMedhin.WeakCoV.eq_const_of_integral_mul_deriv_eq_zero),
    (``KirkMedhin.WeakCoV.firstVariation_zero_of_fixedEndpoint_min,
      ``KirkMedhin.WeakCoV.hasDerivAt_cvFunctional_affine),
    (``KirkMedhin.WeakCoV.hasDerivAt_cvFunctional_affine,
      ``KirkMedhin.K3.hasStrictFDerivAt_cvFunctional_perturbed),
    (``KirkMedhin.NonautonomousDuBoisReymond.weak_duBoisReymond_of_cvFunctional_min,
      ``KirkMedhin.NonautonomousDuBoisReymond.weak_duBoisReymond_of_all_duration_exchange_min),
    (``KirkMedhin.NonautonomousDuBoisReymond.weak_duBoisReymond_of_all_duration_exchange_min,
      ``KirkMedhin.NonautonomousDuBoisReymond.hat_integral_eq_of_duration_exchange_min),
    (``KirkMedhin.NonautonomousDuBoisReymond.weak_duBoisReymond_of_all_duration_exchange_min,
      ``KirkMedhin.DuBoisReymond.compensated_eq_of_hat_integral_eq),
    (``KirkMedhin.NonautonomousDuBoisReymond.hat_integral_eq_of_duration_exchange_min,
      ``KirkMedhin.NonautonomousDuBoisReymond.hasDerivAt_fixedParameterCost),
    (``KirkMedhin.NonautonomousDuBoisReymond.hasDerivAt_fixedParameterCost,
      ``KirkMedhin.NonautonomousTimeReparametrization.hasDerivAt_movingArcCost),
    (``KirkMedhin.NonautonomousDuBoisReymond.corner_energy_eq_of_weak_dbr_min,
      ``KirkMedhin.NonautonomousDuBoisReymond.integral_weighted_energy_eq),
    (``KirkMedhin.NonautonomousDuBoisReymond.corner_energy_eq_of_weak_dbr_min,
      ``KirkMedhin.NonautonomousDuBoisReymond.hasDerivAt_fixedParameterCost),
    (``KirkMedhin.NonautonomousTimeReparametrization.fixedParameterCost_isLocalMin_of_ambient_min,
      ``KirkMedhin.NonautonomousTimeReparametrization.cvFunctional_durationExchange),
    (``KirkMedhin.NonautonomousTimeReparametrization.cvFunctional_durationExchange,
      ``KirkMedhin.NonautonomousTimeReparametrization.cvFunctional_concatenate)]
  for (source, target) in links do
    unless depends source source target 8 do
      throwError "Missing proof dependency: {source} -> {target}"
    logInfo m!"checked proof dependency: {source} -> {target}"
  logInfo m!"Verified {links.length} actual K3/K4 proof-term edges."
