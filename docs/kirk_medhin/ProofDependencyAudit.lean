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
    (``TimeReparametrization.corner_energy_eq_of_cvFunctional_min,
      ``TimeReparametrization.corner_energy_eq_of_eulerLagrange_min),
    (``TimeReparametrization.corner_energy_eq_of_cvFunctional_min,
      ``TimeReparametrization.actualCornerCost_isLocalMin_of_ambient_min),
    (``TimeReparametrization.corner_energy_eq_of_cvFunctional_min,
      ``TimeReparametrization.durationExchange_mem_fixedEndpointPiecewiseC1Curves),
    (``TimeReparametrization.actualCornerCost_isLocalMin_of_ambient_min,
      ``TimeReparametrization.cvFunctional_durationExchange),
    (``TimeReparametrization.cvFunctional_durationExchange,
      ``TimeReparametrization.cvFunctional_concatenate),
    (``TimeReparametrization.corner_energy_eq_of_eulerLagrange_min,
      ``TimeReparametrization.energy_eq_of_eulerLagrange),
    (``TimeReparametrization.corner_energy_eq_of_eulerLagrange_min,
      ``TimeReparametrization.corner_energy_eq_of_actual_min),
    (``TimeReparametrization.corner_energy_eq_of_actual_min,
      ``TimeReparametrization.hasDerivAt_actualCornerCost),
    (``TimeReparametrization.hasDerivAt_actualCornerCost,
      ``TimeReparametrization.hasDerivAt_actualArcCost_energy),
    (``TimeReparametrization.hasDerivAt_actualArcCost_energy,
      ``TimeReparametrization.hasDerivAt_rescaledArcCost_energy),
    (``TimeReparametrization.hasDerivAt_rescaledArcCost_energy,
      ``TimeReparametrization.hasDerivAt_rescaledArcCost),
    (``needleCostate_of_integralOptimality_onHorizon,
      ``needleCostate_of_integralOptimality_smooth),
    (``needleCostate_of_integralOptimality_onHorizon,
      ``NeedleIntegralModel.isIntegralOptimalPair_clampTime),
    (``needleCostate_of_integralOptimality_onHorizon,
      ``SmoothNeedleDataOnHorizon.clamped),
    (``NeedleIntegralModel.isIntegralOptimalPair_clampTime,
      ``NeedleIntegralModel.isIntegralAdmissiblePair_clampTime_iff),
    (``SmoothNeedleDataOnHorizon.clamped,
      ``exists_norm_bound_at_zero_on_Icc),
    (``needleCostate_of_integralOptimality_smooth,
      ``needleCostate_of_globalIntegralOptimality),
    (``needleCostate_of_integralOptimality_smooth,
      ``NeedleIntegralModel.exists_global_optimal_reference_of_integral),
    (``needleCostate_of_globalIntegralOptimality,
      ``GlobalSmoothNeedleData.exists_costate),
    (``needleCostate_of_globalIntegralOptimality,
      ``NeedleIntegralModel.exists_feasible_needle_family),
    (``needleCostate_of_globalIntegralOptimality,
      ``tendsto_scaled_actualNeedleCostFamilyRemainder_of_continuous),
    (``needleCostate_of_globalIntegralOptimality,
      ``costSlope_of_constructedNeedles),
    (``needleCostate_of_globalIntegralOptimality,
      ``integralOptimal_costSlope_nonneg),
    (``needleCostate_of_globalIntegralOptimality,
      ``hamiltonianMinimizing_of_positive_time_jumps),
    (``costSlope_of_constructedNeedles,
      ``cost_difference_eq_impulse_add_actualNeedleCostRemainder),
    (``GlobalSmoothNeedleData.exists_costate,
      ``exists_costate_of_spatial_derivatives),
    (``exists_costate_of_spatial_derivatives,
      ``exists_adjointOn_Icc),
    (``exists_adjointOn_Icc, ``global_existence),
    (``integralOptimal_implies_PMP_via_hahnBanach_of_integral_reference,
      ``integralOptimal_implies_PMP_via_hahnBanach),
    (``integralOptimal_implies_PMP_via_hahnBanach_of_integral_reference,
      ``NeedleIntegralModel.exists_global_optimal_reference_of_integral),
    (``NeedleIntegralModel.exists_global_optimal_reference_of_integral, ``global_existence),
    (``integralOptimal_implies_PMP_via_hahnBanach,
      ``exists_geometricNormalPMP_of_primitive_data),
    (``exists_geometricNormalPMP_of_primitive_data,
      ``integralOptimal_normal_covector_of_endpointTangents),
    (``integralOptimal_normal_covector_of_endpointTangents,
      ``exists_normalized_terminal_covector_on_generators),
    (``exists_normalized_terminal_covector_on_generators,
      ``exists_normalized_positive_multiple_separating_negative_halfspace),
    (``exists_normalized_positive_multiple_separating_negative_halfspace,
      ``exists_positive_multiple_separating_negative_halfspace),
    (``exists_positive_multiple_separating_negative_halfspace,
      ``geometric_hahn_banach_open),
    (``exists_geometricNormalPMP_of_primitive_data,
      ``exists_needle_endpointTangent_of_primitive_data),
    (``exists_needle_endpointTangent_of_primitive_data,
      ``NeedleIntegralModel.exists_feasible_needle_family),
    (``NeedleIntegralModel.exists_feasible_needle_family,
      ``NeedleIntegralModel.exists_feasible_needle),
    (``NeedleIntegralModel.exists_feasible_needle,
      ``NeedleIntegralModel.exists_spliced_solution),
    (``NeedleIntegralModel.exists_spliced_solution, ``global_existence),
    (``exists_needle_endpointTangent_of_primitive_data,
      ``NeedleIntegralModel.terminal_tangent_of_constructed_family),
    (``NeedleIntegralModel.terminal_tangent_of_constructed_family,
      ``terminal_tangent_of_right_ODE),
    (``integralOptimal_normal_covector_of_endpointTangents,
      ``integralOptimal_endpointGenerator_nonneg),
    (``integralOptimal_endpointGenerator_nonneg,
      ``integralOptimal_costSlope_nonneg)]
  for (a, b) in links do
    let some decl := env.find? a | throwError "Missing declaration {a}"
    let some _ := decl.value? true | throwError "No inspectable proof for {a}"
    unless depends a a b 8 do
      throwError "Expected proof dependency is absent: {a} -> {b}"
    logInfo m!"checked proof dependency: {a} -> {b}"
