/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.RelaxedControls
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Measurable ordinary-control recovery by barycentres

For a compact convex control set in a finite-dimensional real vector space,
the conditional barycentre is an actual measurable admissible control.
It preserves every control-affine vector field exactly and does not increase
any continuous convex running cost. Thus the recovery mechanism is proved;
no measurable selector or ordinary-control realization is assumed.

This is the convex-control/control-affine regime. It is not a purification
claim for arbitrary nonconvex velocity sets.
-/

@[expose] public section

open Set MeasureTheory ProbabilityTheory

namespace OptimalControl.RelaxedControl

variable {τ V : Type*} [MeasurableSpace τ]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
  {K : Set V} [CompactSpace K] [Nonempty K]
  {ν : ProbabilityMeasure τ}

/-- Conditional barycentre of the constructed disintegration. -/
noncomputable def barycenter (ρ : RelaxedControl τ K ν) (t : τ) : V :=
  ∫ u : K, (u : V) ∂ρ.kernel t

/-- Integrability of the control coordinate follows from compactness. -/
theorem integrable_controlCoordinate (ρ : RelaxedControl τ K ν) (t : τ) :
    Integrable (fun u : K => (u : V)) (ρ.kernel t) :=
  continuous_subtype_val.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The recovered vector control is strongly measurable, not merely chosen
pointwise using classical choice. -/
theorem stronglyMeasurable_barycenter (ρ : RelaxedControl τ K ν) :
    StronglyMeasurable ρ.barycenter :=
  continuous_subtype_val.stronglyMeasurable.integral_kernel

/-- The conditional barycentre remains in the original compact convex set
at every time, including exceptional times of the disintegration. -/
theorem barycenter_mem (ρ : RelaxedControl τ K ν) (hK : Convex ℝ K) (t : τ) :
    ρ.barycenter t ∈ K := by
  exact hK.integral_mem (isCompact_iff_compactSpace.mpr inferInstance).isClosed
    (Filter.Eventually.of_forall fun u : K => u.2) (ρ.integrable_controlCoordinate t)

/-- The actual ordinary admissible control obtained from a relaxed control. -/
noncomputable def recoveredControl (ρ : RelaxedControl τ K ν) (hK : Convex ℝ K) (t : τ) : K :=
  ⟨ρ.barycenter t, ρ.barycenter_mem hK t⟩

/-- Measurability into the admissible-control subtype. -/
theorem measurable_recoveredControl (ρ : RelaxedControl τ K ν) (hK : Convex ℝ K) :
    Measurable (ρ.recoveredControl hK) :=
  ρ.stronglyMeasurable_barycenter.measurable.subtype_mk

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Recovery preserves the actual average of every affine vector field in
the control variable. State/time dependence can be substituted into `a` and
`B` without changing the statement. -/
theorem integral_affine_eq_barycenter (ρ : RelaxedControl τ K ν) (t : τ)
    (a : E) (B : V →L[ℝ] E) :
    (∫ u : K, a + B (u : V) ∂ρ.kernel t) = a + B (ρ.barycenter t) := by
  rw [integral_add (integrable_const a) (B.integrable_comp (ρ.integrable_controlCoordinate t)),
    B.integral_comp_comm (ρ.integrable_controlCoordinate t)]
  simp [barycenter]

/-- Pointwise Jensen inequality for the constructed ordinary control. -/
theorem convex_cost_barycenter_le (ρ : RelaxedControl τ K ν) (t : τ)
    (g : V → ℝ) (hg : ConvexOn ℝ K g) (hgc : ContinuousOn g K) :
    g (ρ.barycenter t) ≤ ∫ u : K, g (u : V) ∂ρ.kernel t := by
  apply hg.map_integral_le hgc (isCompact_iff_compactSpace.mpr inferInstance).isClosed
    (Filter.Eventually.of_forall fun u : K => u.2) (ρ.integrable_controlCoordinate t)
  exact hgc.domRestrict.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Restricted-time affine dynamics are preserved, so recovery preserves the
whole trajectory's Volterra equations, not merely its terminal state. -/
theorem setIntegral_affine_eq_recovered (ρ : RelaxedControl τ K ν)
    (hK : Convex ℝ K) (a : τ → E) (B : τ → V →L[ℝ] E)
    {s : Set τ} (hs : MeasurableSet s)
    (hf : IntegrableOn (fun z : τ × K => a z.1 + B z.1 (z.2 : V)) (s ×ˢ univ) ρ.measure) :
    (∫ z in s ×ˢ univ, a z.1 + B z.1 (z.2 : V) ∂ρ.measure) =
      ∫ t in s, a t + B t (ρ.recoveredControl hK t : V) ∂ν := by
  rw [← ρ.setIntegral_kernel hs hf]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => ρ.integral_affine_eq_barycenter t (a t) (B t)

/-- Integrated convex running costs do not increase under recovery. The
integrability premises concern the actual functions, not a comparison or
selection conclusion. -/
theorem integral_convex_cost_recovered_le (ρ : RelaxedControl τ K ν) (hK : Convex ℝ K)
    (g : τ → V → ℝ) (hg : ∀ t, ConvexOn ℝ K (g t)) (hgc : ∀ t, ContinuousOn (g t) K)
    (hgr : Integrable (fun t => g t (ρ.recoveredControl hK t : V)) ν.toMeasure)
    (hgo : Integrable (fun z : τ × K => g z.1 (z.2 : V)) ρ.measure) :
    (∫ t, g t (ρ.recoveredControl hK t : V) ∂ν) ≤
      ∫ z : τ × K, g z.1 (z.2 : V) ∂ρ.measure := by
  rw [← ρ.integral_kernel hgo]
  apply integral_mono_ae hgr
  · have hi := hgo.integral_condKernel
    rwa [ρ.fst_measure] at hi
  · exact Filter.Eventually.of_forall fun t => ρ.convex_cost_barycenter_le t (g t) (hg t) (hgc t)

end OptimalControl.RelaxedControl
