/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
import DynamicalSystems.OptimalControl.ContinuousTime.DuBoisReymond
import DynamicalSystems.OptimalControl.ContinuousTime.FiniteCornerMinimumPrinciple
import DynamicalSystems.OptimalControl.ContinuousTime.FinitePiecewiseVariations
import DynamicalSystems.OptimalControl.ContinuousTime.FiniteSpatialVariations
import DynamicalSystems.OptimalControl.ContinuousTime.K3DifferentiableExtension
import DynamicalSystems.OptimalControl.ContinuousTime.K3IsoperimetricEulerLagrange
import DynamicalSystems.OptimalControl.ContinuousTime.K3IsoperimetricLift
import DynamicalSystems.OptimalControl.ContinuousTime.K3MomentumRegularity
import DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousDuBoisReymond
import DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousFiniteCornerConditions
import DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousFiniteCornerMinimumPrinciple
import DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousFinitePiecewiseVariations
import DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousFiniteSpatialVariations
import DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousTimeReparametrization
import DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousTimeReparametrizationFamily
import DynamicalSystems.OptimalControl.ContinuousTime.PiecewiseC1Extensions
import DynamicalSystems.OptimalControl.ContinuousTime.PiecewiseC1MinimumPrinciple
import DynamicalSystems.OptimalControl.ContinuousTime.WeakCornerConditions
import DynamicalSystems.OptimalControl.ContinuousTime.WeakEulerLagrange
import DynamicalSystems.OptimalControl.ContinuousTime.WeakEulerLagrangeMinimum
import DynamicalSystemsTest.OptimalControl.ContinuousTime.CalculusOfVariations.IsoperimetricMultiplier
import DynamicalSystemsTest.OptimalControl.ContinuousTime.CalculusOfVariations.NonautonomousDuBoisReymond
import DynamicalSystemsTest.OptimalControl.ContinuousTime.CalculusOfVariations.DuBoisReymondLowRegularity
import DynamicalSystemsTest.OptimalControl.ContinuousTime.CalculusOfVariations.TwoSidedEndpointDerivative
import Batteries.Tactic.Lint
import Lean

/-!
# Exhaustive K3/K4 axiom and declaration audit

Every declaration owned by the delivered modules is checked, including private
helpers and generated declarations. The check rejects every axiom except Lean's
standard `propext`, `Classical.choice`, and `Quot.sound`. It also includes the
pre-existing actual strict-integral differentiation module used by the final lift.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let modules : Array Name := #[
    `DynamicalSystems.OptimalControl.ContinuousTime.DuBoisReymond,
    `DynamicalSystems.OptimalControl.ContinuousTime.FiniteCornerMinimumPrinciple,
    `DynamicalSystems.OptimalControl.ContinuousTime.FinitePiecewiseVariations,
    `DynamicalSystems.OptimalControl.ContinuousTime.FiniteSpatialVariations,
    `DynamicalSystems.OptimalControl.ContinuousTime.K3DifferentiableExtension,
    `DynamicalSystems.OptimalControl.ContinuousTime.K3IsoperimetricEulerLagrange,
    `DynamicalSystems.OptimalControl.ContinuousTime.K3IsoperimetricLift,
    `DynamicalSystems.OptimalControl.ContinuousTime.K3MomentumRegularity,
    `DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousDuBoisReymond,
    `DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousFiniteCornerConditions,
    `DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousFiniteCornerMinimumPrinciple,
    `DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousFinitePiecewiseVariations,
    `DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousFiniteSpatialVariations,
    `DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousTimeReparametrization,
    `DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousTimeReparametrizationFamily,
    `DynamicalSystems.OptimalControl.ContinuousTime.PiecewiseC1Extensions,
    `DynamicalSystems.OptimalControl.ContinuousTime.PiecewiseC1MinimumPrinciple,
    `DynamicalSystems.OptimalControl.ContinuousTime.WeakCornerConditions,
    `DynamicalSystems.OptimalControl.ContinuousTime.WeakEulerLagrange,
    `DynamicalSystems.OptimalControl.ContinuousTime.WeakEulerLagrangeMinimum,
    `DynamicalSystemsTest.OptimalControl.ContinuousTime.CalculusOfVariations.IsoperimetricMultiplier,
    `DynamicalSystemsTest.OptimalControl.ContinuousTime.CalculusOfVariations.NonautonomousDuBoisReymond,
    `DynamicalSystemsTest.OptimalControl.ContinuousTime.CalculusOfVariations.DuBoisReymondLowRegularity,
    `DynamicalSystemsTest.OptimalControl.ContinuousTime.CalculusOfVariations.TwoSidedEndpointDerivative]
  let owned := env.constants.map₁.fold (init := #[]) fun names name _ =>
    match env.getModuleIdxFor? name with
    | none => names
    | some index =>
      if modules.contains env.header.moduleNames[index.toNat]! then names.push name else names
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in owned do
    let axioms ← collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Nonstandard axiom {ax} in {name}"
  for mod in modules do
    let count : Nat := owned.foldl (fun total name =>
      match env.getModuleIdxFor? name with
      | none => total
      | some index => if env.header.moduleNames[index.toNat]! == mod then total + 1 else total) 0
    if count == 0 then throwError "No declarations checked for {mod}"
    logInfo m!"standard-axiom audit: {mod}: {count} declarations"
  logInfo m!"Standard axioms only in all {owned.size} declarations from {modules.size} modules."

#lint in DynamicalSystems.OptimalControl.ContinuousTime.DuBoisReymond
#lint in DynamicalSystems.OptimalControl.ContinuousTime.FiniteCornerMinimumPrinciple
#lint in DynamicalSystems.OptimalControl.ContinuousTime.FinitePiecewiseVariations
#lint in DynamicalSystems.OptimalControl.ContinuousTime.FiniteSpatialVariations
#lint in DynamicalSystems.OptimalControl.ContinuousTime.K3DifferentiableExtension
#lint in DynamicalSystems.OptimalControl.ContinuousTime.K3IsoperimetricEulerLagrange
#lint in DynamicalSystems.OptimalControl.ContinuousTime.K3IsoperimetricLift
#lint in DynamicalSystems.OptimalControl.ContinuousTime.K3MomentumRegularity
#lint in DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousDuBoisReymond
#lint in DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousFiniteCornerConditions
#lint in DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousFiniteCornerMinimumPrinciple
#lint in DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousFinitePiecewiseVariations
#lint in DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousFiniteSpatialVariations
#lint in DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousTimeReparametrization
#lint in DynamicalSystems.OptimalControl.ContinuousTime.NonautonomousTimeReparametrizationFamily
#lint in DynamicalSystems.OptimalControl.ContinuousTime.PiecewiseC1Extensions
#lint in DynamicalSystems.OptimalControl.ContinuousTime.PiecewiseC1MinimumPrinciple
#lint in DynamicalSystems.OptimalControl.ContinuousTime.WeakCornerConditions
#lint in DynamicalSystems.OptimalControl.ContinuousTime.WeakEulerLagrange
#lint in DynamicalSystems.OptimalControl.ContinuousTime.WeakEulerLagrangeMinimum
#lint in DynamicalSystemsTest.OptimalControl.ContinuousTime.CalculusOfVariations.IsoperimetricMultiplier
#lint in DynamicalSystemsTest.OptimalControl.ContinuousTime.CalculusOfVariations.NonautonomousDuBoisReymond
#lint in DynamicalSystemsTest.OptimalControl.ContinuousTime.CalculusOfVariations.DuBoisReymondLowRegularity
#lint in DynamicalSystemsTest.OptimalControl.ContinuousTime.CalculusOfVariations.TwoSidedEndpointDerivative
