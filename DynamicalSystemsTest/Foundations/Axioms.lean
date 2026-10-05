import DynamicalSystemsTest.Basic.ComparisonFunctions
import DynamicalSystemsTest.InputOutput.ClosedLoopCausality
import DynamicalSystemsTest.InputOutput.ClosedLoopCausalityCounterexample
import DynamicalSystemsTest.Mathlib.Dynamics.FlowCongruence
import DynamicalSystemsTest.Mathlib.Analysis.ODE.CompleteFlow
import DynamicalSystemsTest.Mathlib.Analysis.ODE.Duhamel
import DynamicalSystemsTest.Mathlib.Analysis.ODE.GlobalExistenceGrowth
import DynamicalSystemsTest.Mathlib.Analysis.ODE.PointwiseGrowthObstruction
import Lean.Util.CollectAxioms

/-!
# Enforced axiom audit for the foundational repairs

All seven target results, their main analytic bridges, generated flows, and
the counterexamples and applications are checked transitively. Missing names
are elaboration errors. Any dependency outside Lean's three standard classical
axioms is an error, so an admitted proof cannot silently pass this audit.
-/

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let targets : Array Lean.Name := #[
    ``MemKI.surjective,
    ``MemKI.orderIso,
    ``MemKI.symm,
    ``ComparisonFunction.exists_memKI_le_of_coercive,
    ``ComparisonFunction.exists_memKI_sandwich_of_coercive,
    ``ComparisonFunction.exists_memKI_bounds_of_isCompact,
    ``ComparisonFunction.exists_memKI_bounds_on_closedBall,
    ``ComparisonFunction.exists_memKI_bounds_of_radiallyUnbounded,
    ``Flow.isIntegralCurve,
    ``flow_congr,
    ``IsLinearlyBddVectorField.flow,
    ``IsLinearlyBddVectorField.deriv_flow,
    ``IsLinearlyBddVectorField.deriv_comp_flow,
    ``UniformlyLocallyLipschitz.continuous_uncurry,
    ``UniformlyLocallyLipschitz.exists_lipschitzOnWith_closedBall_along,
    ``norm_le_mul_exp_of_norm_deriv_le_on_closedBall,
    ``continuous_uncurry_of_isIntegralCurve,
    ``IsFundamentalSolution.continuous,
    ``IsFundamentalSolution.continuous_of_uniformlyLocallyLipschitz,
    ``IsCompleteVectorField.flow,
    ``IsCompleteVectorField.hasDerivAt_flow,
    ``IsCompleteVectorField.deriv_comp_flow,
    ``IsFundamentalSolution.linear_cocycle,
    ``IsFundamentalSolution.isStateTransition,
    ``IsFundamentalSolution.duhamelOperator_hasDerivAt,
    ``IsFundamentalSolution.duhamelOperator_isIntegralCurve,
    ``IsFundamentalSolution.duhamelOperator_deriv,
    ``IsFundamentalSolution.duhamelOperator_isFundamentalSolution,
    ``IsIntegralCurveOn.eqOn_Ioo_of_uniformlyLocallyLipschitz,
    ``locallyUniformLinearGrowth_of_continuous_bound,
    ``ODE.norm_le_gronwallBound_of_linear_growth_Ioo,
    ``ODE.lipschitzOnWith_of_linear_growth_Ioo,
    ``ODE.exists_tendsto_right_of_lipschitzOn,
    ``ODE.exists_extension_Ioo_right,
    ``ODE.exists_extension_Ioo,
    ``ODE.isCompleteVectorField_of_extension,
    ``UniformlyLocallyLipschitz.isCompleteVectorField,
    ``UniformlyLocallyLipschitz.isCompleteVectorField_of_continuous_uncurry,
    ``SetRel.closedLoop.mem_inputState_truncate,
    ``SetRel.closedLoop.isCausal_inputState,
    ``SetRel.closedLoop.isCausal_inputOutput_of_inputState,
    ``SetRel.closedLoop.isCausal_inputOutput,
    ``ComparisonFunctionTests.no_global_classK_lower_bound,
    ``ComparisonFunctionTests.decaying_local_bounds,
    ``ComparisonFunctionTests.quadratic_global_bounds,
    ``flow_eq_id_of_generator_zero,
    ``CompleteFlowRegression.constant_flow_apply,
    ``DuhamelTests.normalization_is_necessary,
    ``DuhamelTests.scalar_forced_fundamentalSolution,
    ``GlobalExistenceGrowthRegression.sin_square_complete,
    ``GlobalExistenceGrowthRegression.time_linear_complete,
    ``PointwiseGrowthObstruction.not_complete,
    ``ClosedLoopCausality.scalarLoop_isGraph,
    ``ClosedLoopCausality.scalarLoop_uniqueTruncatedStates,
    ``ClosedLoopCausalityCounterexample.loop_isGraph,
    ``ClosedLoopCausalityCounterexample.loop_locallyLpSolvable,
    ``ClosedLoopCausalityCounterexample.loop_not_causal,
    ``ClosedLoopCausalityCounterexample.loop_output_not_causal]
  for target in targets do
    unless ((← Lean.getEnv).find? target).isSome do
      throwError "Missing audited declaration: {target}"
    let axioms ← Lean.collectAxioms target
    let unexpected := axioms.filter (fun axiomName ↦ !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {target}: {unexpected.toList}"
    Lean.logInfo m!"{target}: {axioms.toList}"
  Lean.logInfo m!"Foundational axiom audit passed for {targets.size} declarations."
