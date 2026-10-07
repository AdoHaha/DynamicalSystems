/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
import DynamicalSystems.OptimalControl.ContinuousTime.AffineControlPath

/-! Primitive trajectory existence, actual uniqueness, exact response identities, and
normalized-horizon assembly use only the standard axioms. -/
#print axioms AffineIntegralResponse.response_integral_eq
#print axioms AffineIntegralResponse.exists_response_on_Icc
#print axioms AffineIntegralResponse.homogeneous_eq_zero
#print axioms AffineIntegralResponse.eq_response_of_integral_eq
#print axioms AffineIntegralResponse.sub_response
#print axioms AffineIntegralResponse.response_affine_mixture
#print axioms OptimalControl.integral_horizon_prefix
#print axioms OptimalControl.ConvexStateControlProblem.exists_affine_transition
#print axioms OptimalControl.ConvexStateControlProblem.exists_affine_candidate
#print axioms OptimalControl.ConvexStateControlProblem.affine_trajectory_eq_reference
#print axioms OptimalControl.ConvexStateControlProblem.affine_trajectory_sub
#print axioms OptimalControl.ConvexStateControlProblem.exists_affine_response_data
