import DynamicalSystems.OptimalControl.ContinuousTime.GeometricMinimumPrinciple
import DynamicalSystems.OptimalControl.ContinuousTime.NeedlePMP
import DynamicalSystems.OptimalControl.ContinuousTime.NeedlePMPOnHorizon
import DynamicalSystems.OptimalControl.ContinuousTime.TimeReparametrizationFamily
import Lean

/-! This audit checks actual proof-term references along the Hahn–Banach,
constructed-family, and terminal-sensitivity chains. It does not infer semantic
acceptance from declaration names. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  -- The compiler may lift a field proof into a subordinate auxiliary declaration.
  -- Follow only those auxiliaries of the same source, rather than unrelated lemmas.
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
    (``KirkMedhin.TimeReparametrization.corner_energy_eq_of_cvFunctional_min,
      ``KirkMedhin.TimeReparametrization.corner_energy_eq_of_eulerLagrange_min),
    (``KirkMedhin.TimeReparametrization.corner_energy_eq_of_cvFunctional_min,
      ``KirkMedhin.TimeReparametrization.actualCornerCost_isLocalMin_of_ambient_min),
    (``KirkMedhin.TimeReparametrization.corner_energy_eq_of_cvFunctional_min,
      ``KirkMedhin.TimeReparametrization.durationExchange_mem_fixedEndpointPiecewiseC1Curves),
    (``KirkMedhin.TimeReparametrization.actualCornerCost_isLocalMin_of_ambient_min,
      ``KirkMedhin.TimeReparametrization.cvFunctional_durationExchange),
    (``KirkMedhin.TimeReparametrization.cvFunctional_durationExchange,
      ``KirkMedhin.TimeReparametrization.cvFunctional_concatenate),
    (``KirkMedhin.TimeReparametrization.corner_energy_eq_of_eulerLagrange_min,
      ``KirkMedhin.TimeReparametrization.energy_eq_of_eulerLagrange),
    (``KirkMedhin.TimeReparametrization.corner_energy_eq_of_eulerLagrange_min,
      ``KirkMedhin.TimeReparametrization.corner_energy_eq_of_actual_min),
    (``KirkMedhin.TimeReparametrization.corner_energy_eq_of_actual_min,
      ``KirkMedhin.TimeReparametrization.hasDerivAt_actualCornerCost),
    (``KirkMedhin.TimeReparametrization.hasDerivAt_actualCornerCost,
      ``KirkMedhin.TimeReparametrization.hasDerivAt_actualArcCost_energy),
    (``KirkMedhin.TimeReparametrization.hasDerivAt_actualArcCost_energy,
      ``KirkMedhin.TimeReparametrization.hasDerivAt_rescaledArcCost_energy),
    (``KirkMedhin.TimeReparametrization.hasDerivAt_rescaledArcCost_energy,
      ``KirkMedhin.TimeReparametrization.hasDerivAt_rescaledArcCost),
    (``K1NeedlePMPOnHorizon.needleCostate_of_integralOptimality_onHorizon,
      ``K1NeedlePMP.needleCostate_of_integralOptimality_smooth),
    (``K1NeedlePMPOnHorizon.needleCostate_of_integralOptimality_onHorizon,
      ``K1NeedlePMPOnHorizon.clamped_optimal),
    (``K1NeedlePMPOnHorizon.needleCostate_of_integralOptimality_onHorizon,
      ``K1NeedlePMPOnHorizon.SmoothNeedleDataOnHorizon.clamped),
    (``K1NeedlePMPOnHorizon.clamped_optimal,
      ``K1NeedlePMPOnHorizon.clamped_admissible_iff),
    (``K1NeedlePMPOnHorizon.SmoothNeedleDataOnHorizon.clamped,
      ``K1NeedlePMPOnHorizon.exists_bound_at_zero),
    (``K1NeedlePMP.needleCostate_of_integralOptimality_smooth,
      ``K1NeedlePMP.needleCostate_of_globalIntegralOptimality),
    (``K1NeedlePMP.needleCostate_of_integralOptimality_smooth,
      ``NeedleIntegralModel.exists_global_optimal_reference_of_integral),
    (``K1NeedlePMP.needleCostate_of_globalIntegralOptimality,
      ``K1NeedlePMP.GlobalSmoothNeedleData.exists_costate),
    (``K1NeedlePMP.needleCostate_of_globalIntegralOptimality,
      ``NeedleIntegralModel.exists_feasible_needle_family),
    (``K1NeedlePMP.needleCostate_of_globalIntegralOptimality,
      ``K1NeedleCost.tendsto_scaled_actualFamilyRemainder_of_continuous),
    (``K1NeedlePMP.needleCostate_of_globalIntegralOptimality,
      ``K1NeedlePMP.costSlope_of_constructedNeedles),
    (``K1NeedlePMP.needleCostate_of_globalIntegralOptimality,
      ``KirkMedhin.K1.integralOptimal_costSlope_nonneg),
    (``K1NeedlePMP.needleCostate_of_globalIntegralOptimality,
      ``K1NeedlePMP.hamiltonianMinimizing_of_positive_time_jumps),
    (``K1NeedlePMP.costSlope_of_constructedNeedles,
      ``K1NeedleCost.cost_difference_eq_impulse_add_actualRemainder),
    (``K1NeedlePMP.GlobalSmoothNeedleData.exists_costate,
      ``K1AdjointExistence.exists_project_costate_of_spatial_derivatives),
    (``K1AdjointExistence.exists_project_costate_of_spatial_derivatives,
      ``K1AdjointExistence.exists_adjointOn_Icc),
    (``K1AdjointExistence.exists_adjointOn_Icc, ``global_existence),
    (``KirkMedhin.K1.integralOptimal_implies_PMP_via_hahnBanach_of_integral_reference,
      ``KirkMedhin.K1.integralOptimal_implies_PMP_via_hahnBanach),
    (``KirkMedhin.K1.integralOptimal_implies_PMP_via_hahnBanach_of_integral_reference,
      ``NeedleIntegralModel.exists_global_optimal_reference_of_integral),
    (``NeedleIntegralModel.exists_global_optimal_reference_of_integral, ``global_existence),
    (``KirkMedhin.K1.integralOptimal_implies_PMP_via_hahnBanach,
      ``KirkMedhin.K1.exists_geometricNormalPMP_of_primitive_data),
    (``KirkMedhin.K1.exists_geometricNormalPMP_of_primitive_data,
      ``KirkMedhin.K1.integralOptimal_normal_covector_of_endpointTangents),
    (``KirkMedhin.K1.integralOptimal_normal_covector_of_endpointTangents,
      ``KirkMedhin.K1.exists_normalized_terminal_covector_on_generators),
    (``KirkMedhin.K1.exists_normalized_terminal_covector_on_generators,
      ``KirkMedhin.K1.exists_normalized_hahnBanach_terminal_covector),
    (``KirkMedhin.K1.exists_normalized_hahnBanach_terminal_covector,
      ``KirkMedhin.K1.exists_hahnBanach_terminal_covector),
    (``KirkMedhin.K1.exists_hahnBanach_terminal_covector,
      ``geometric_hahn_banach_open),
    (``KirkMedhin.K1.exists_geometricNormalPMP_of_primitive_data,
      ``KirkMedhin.K1.exists_needle_endpointTangent_of_primitive_data),
    (``KirkMedhin.K1.exists_needle_endpointTangent_of_primitive_data,
      ``NeedleIntegralModel.exists_feasible_needle_family),
    (``NeedleIntegralModel.exists_feasible_needle_family,
      ``NeedleIntegralModel.exists_feasible_needle),
    (``NeedleIntegralModel.exists_feasible_needle,
      ``NeedleIntegralModel.exists_spliced_solution),
    (``NeedleIntegralModel.exists_spliced_solution, ``global_existence),
    (``KirkMedhin.K1.exists_needle_endpointTangent_of_primitive_data,
      ``NeedleIntegralModel.terminal_tangent_of_constructed_family),
    (``NeedleIntegralModel.terminal_tangent_of_constructed_family,
      ``KirkMedhin.terminal_tangent_of_right_ODE),
    (``KirkMedhin.K1.integralOptimal_normal_covector_of_endpointTangents,
      ``KirkMedhin.K1.integralOptimal_endpointGenerator_nonneg),
    (``KirkMedhin.K1.integralOptimal_endpointGenerator_nonneg,
      ``KirkMedhin.K1.integralOptimal_costSlope_nonneg)]
  for (a, b) in links do
    let some decl := env.find? a | throwError "Missing declaration {a}"
    let some _ := decl.value? true | throwError "No inspectable proof for {a}"
    unless depends a a b 8 do
      throwError "Expected proof dependency is absent: {a} -> {b}"
    logInfo m!"checked proof dependency: {a} -> {b}"
