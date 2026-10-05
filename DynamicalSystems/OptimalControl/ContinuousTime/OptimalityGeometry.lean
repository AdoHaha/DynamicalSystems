import DynamicalSystems.OptimalControl.ContinuousTime.IntegralAdmissibility
import DynamicalSystems.OptimalControl.ContinuousTime.NeedleSeparation
import DynamicalSystems.Mathlib.Analysis.ODE.StateTransition
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Geometry.Convex.Cone.Pointed

/-!
# From feasible first variations to Hahn–Banach separation

Optimality is used against actual integral-admissible competitors. A proved
right-sided limit of actual cost differences therefore has nonnegative limit.
For augmented endpoint variations, a terminal Fréchet derivative and the actual
endpoint tangent imply that limit by the chain rule. The conic hull of these
endpoint generators is then disjoint from strict terminal descent. The final
multiplier is extracted through the existing geometric Hahn–Banach theorem.

The analytic limit and feasibility are explicit inputs; neither a Hamiltonian
inequality nor a separation hypothesis is an input to the optimality theorems.
-/


open Set Filter MeasureTheory
open scoped Topology

/-- A right-sided derivative of genuine nonnegative cost increments is nonnegative.
This elementary sign passage is independent of the control model. -/
theorem nonneg_of_eventually_minimizing_costSlope
    (J : ℝ → ℝ) (J₀ q : ℝ)
    (hmin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), J₀ ≤ J ε)
    (hslope : Tendsto (fun ε => ε⁻¹ * (J ε - J₀))
      (𝓝[>] (0 : ℝ)) (𝓝 q)) : 0 ≤ q := by
  apply ge_of_tendsto hslope
  filter_upwards [hmin, self_mem_nhdsWithin] with ε hε hpos
  exact mul_nonneg (inv_nonneg.mpr hpos.le) (sub_nonneg.mpr hε)

section IntegralOptimality

variable {X U : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Integral optimality implies the sign of any actual feasible cost derivative.
The conclusion is derived from the existing total-cost expression; the limiting
value need not have been identified with a Hamiltonian jump yet. -/
theorem integralOptimal_costSlope_nonneg
    (prob : ContinuousOCP X U) (x₀ : X) (x : ℝ → X) (u : ℝ → U)
    (hopt : NeedleIntegralModel.IsIntegralOptimalPair prob x₀ x u)
    (xε : ℝ → ℝ → X) (uε : ℝ → ℝ → U)
    (hfeasible : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      NeedleIntegralModel.IsIntegralAdmissiblePair prob x₀ (xε ε) (uε ε))
    (q : ℝ)
    (hslope : Tendsto
      (fun ε => ε⁻¹ *
        (continuousTotalCost prob (xε ε) (uε ε) - continuousTotalCost prob x u))
      (𝓝[>] (0 : ℝ)) (𝓝 q)) : 0 ≤ q := by
  apply nonneg_of_eventually_minimizing_costSlope
    (fun ε => continuousTotalCost prob (xε ε) (uε ε))
    (continuousTotalCost prob x u) q _ hslope
  filter_upwards [hfeasible] with ε hε
  exact hopt.2 (xε ε) (uε ε) hε

end IntegralOptimality

section EndpointChainRule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A terminal Fréchet derivative converts an actual augmented endpoint tangent
into the actual first cost derivative. No differentiability of the perturbed
solution map away from the zero needle length is needed. -/
theorem terminalCost_costSlope_of_endpointTangent
    (Ψ : E → ℝ) (c : E →L[ℝ] ℝ) (y : ℝ → E) (y₀ g : E)
    (hy₀ : y 0 = y₀) (hΨ : HasFDerivAt Ψ c y₀)
    (htangent : Tendsto (fun ε => ε⁻¹ • (y ε - y₀))
      (𝓝[>] (0 : ℝ)) (𝓝 g)) :
    Tendsto (fun ε => ε⁻¹ * (Ψ (y ε) - Ψ y₀))
      (𝓝[>] (0 : ℝ)) (𝓝 (c g)) := by
  have hy : HasDerivWithinAt y g (Ioi 0) 0 := by
    apply (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mpr
    change Tendsto (fun ε : ℝ => (ε - 0)⁻¹ • (y ε - y 0))
      (𝓝[>] (0 : ℝ)) (𝓝 g)
    simpa only [sub_zero, hy₀] using htangent
  have hΨ' : HasFDerivAt Ψ c (y 0) := hy₀.symm ▸ hΨ
  have hcomp := hΨ'.comp_hasDerivWithinAt 0 hy
  have hlim := (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mp hcomp
  change Tendsto (fun ε : ℝ => (ε - 0)⁻¹ • (Ψ (y ε) - Ψ (y 0)))
    (𝓝[>] (0 : ℝ)) (𝓝 (c g)) at hlim
  simpa only [sub_zero, hy₀, smul_eq_mul] using hlim

/-- The endpoint family need not already be defined at zero as the reference.
Changing its value at zero does not change a right-sided tangent or cost limit. -/
theorem terminalCost_costSlope_of_endpointTangent_punctured
    (Ψ : E → ℝ) (c : E →L[ℝ] ℝ) (y : ℝ → E) (y₀ g : E)
    (hΨ : HasFDerivAt Ψ c y₀)
    (htangent : Tendsto (fun ε => ε⁻¹ • (y ε - y₀))
      (𝓝[>] (0 : ℝ)) (𝓝 g)) :
    Tendsto (fun ε => ε⁻¹ * (Ψ (y ε) - Ψ y₀))
      (𝓝[>] (0 : ℝ)) (𝓝 (c g)) := by
  let y' : ℝ → E := fun ε => if ε = 0 then y₀ else y ε
  have heq : y' =ᶠ[𝓝[>] (0 : ℝ)] y := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hne : ε ≠ 0 := ne_of_gt hε
    simp [y', hne]
  have hlim : Tendsto (fun ε => ε⁻¹ • (y' ε - y₀))
      (𝓝[>] (0 : ℝ)) (𝓝 g) := by
    apply htangent.congr'
    filter_upwards [heq] with ε hε
    rw [hε]
  have hc := terminalCost_costSlope_of_endpointTangent Ψ c y' y₀ g
    (by simp [y']) hΨ hlim
  apply hc.congr'
  filter_upwards [heq] with ε hε
  rw [hε]

end EndpointChainRule

section ConeGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The closed nonnegative halfspace of a continuous linear functional is a
pointed convex cone. -/
def terminalNonnegativeCone (c : E →L[ℝ] ℝ) : PointedCone ℝ E where
  carrier := {y | 0 ≤ c y}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change 0 ≤ c (x + y)
    rw [map_add]
    exact add_nonneg hx hy
  smul_mem' := by
    intro r y hy
    change 0 ≤ c ((r : ℝ) • y)
    rw [map_smul, smul_eq_mul]
    exact mul_nonneg r.property hy

/-- The conic hull of the generators; in particular it contains zero and every
finite combination with nonnegative coefficients. This definition asserts no
unproved attainability of combinations. -/
def endpointVariationCone {ι : Type*} (g : ι → E) : PointedCone ℝ E :=
  PointedCone.hull ℝ (Set.range g)

/-- Each actual first-order endpoint generator belongs to the variation cone. -/
theorem mem_endpointVariationCone {ι : Type*} (g : ι → E) (i : ι) :
    g i ∈ endpointVariationCone g :=
  PointedCone.subset_hull (Set.mem_range_self i)

/-- Nonnegative terminal derivatives on generators extend to their entire conic
hull by linearity and nonnegative coefficients. -/
theorem terminal_nonneg_on_endpointVariationCone
    {ι : Type*} (c : E →L[ℝ] ℝ) (g : ι → E) (hg : ∀ i, 0 ≤ c (g i)) :
    ∀ y ∈ endpointVariationCone g, 0 ≤ c y := by
  have hle : endpointVariationCone g ≤ terminalNonnegativeCone c := by
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    exact hg i
  exact fun y hy => hle hy

/-- The descent halfspace is disjoint from the entire conic hull once optimality
has supplied nonnegative terminal derivatives for each generator. -/
theorem endpointVariationCone_disjoint_terminal_descent
    {ι : Type*} (c : E →L[ℝ] ℝ) (g : ι → E) (hg : ∀ i, 0 ≤ c (g i)) :
    Disjoint {y | c y < 0} (endpointVariationCone g : Set E) := by
  refine Set.disjoint_left.mpr ?_
  intro y hy hcone
  exact (not_lt_of_ge (terminal_nonneg_on_endpointVariationCone c g hg y hcone)) hy

/-- Hahn–Banach extraction on the constructed cone. The separating functional is
returned by geometric Hahn–Banach and then normalized at `e`. -/
theorem exists_normalized_terminal_covector_on_generators
    {ι : Type*} (c : E →L[ℝ] ℝ) (e : E) (he : c e = 1)
    (g : ι → E) (hg : ∀ i, 0 ≤ c (g i)) :
    ∃ (q : E →L[ℝ] ℝ) (α : ℝ),
      q ≠ 0 ∧ 0 < α ∧ (∀ y ∈ endpointVariationCone g, 0 ≤ q y) ∧
      q e = α ∧ α⁻¹ • q = c := by
  exact _root_.exists_normalized_positive_multiple_separating_negative_halfspace c e he
    (endpointVariationCone g) (endpointVariationCone g).convex
    (endpointVariationCone g).zero_mem
    (endpointVariationCone_disjoint_terminal_descent c g hg)

end ConeGeometry

section AugmentedEndpointOptimality

variable {X U ι : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual accumulated running cost and terminal state, formed from an
ordinary trajectory/control pair. -/
noncomputable def costAugmentedEndpoint (prob : ContinuousOCP X U)
    (x : ℝ → X) (u : ℝ → U) : ℝ × X :=
  (∫ t in 0..prob.T, prob.L t (x t) (u t), x prob.T)

/-- The ordinary Bolza cost expressed as a terminal objective on augmented state. -/
def _root_.bolzaTerminalCost (K : X → ℝ) (y : ℝ × X) : ℝ := y.1 + K y.2

omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
@[simp]
theorem _root_.bolzaTerminalCost_endpoint (prob : ContinuousOCP X U)
    (x : ℝ → X) (u : ℝ → U) :
    _root_.bolzaTerminalCost prob.K (costAugmentedEndpoint prob x u) =
      continuousTotalCost prob x u := rfl

/-- Differentiating the actual augmented terminal objective produces `(1, DK)`. -/
theorem _root_.hasFDerivAt_bolzaTerminalCost
    (K : X → ℝ) (DK : X →L[ℝ] ℝ) (y : ℝ × X)
    (hK : HasFDerivAt K DK y.2) :
    HasFDerivAt (_root_.bolzaTerminalCost K) (_root_.bolzaTerminalDifferential DK) y := by
  exact (ContinuousLinearMap.fst ℝ ℝ X).hasFDerivAt.add
    (hK.comp y (ContinuousLinearMap.snd ℝ ℝ X).hasFDerivAt)

/-- Optimality makes each actual first-order augmented endpoint variation
nonnegative under the terminal differential. The endpoint variation itself is a
limit of accumulated running costs and terminal states of feasible competitors. -/
theorem integralOptimal_endpointGenerator_nonneg
    (prob : ContinuousOCP X U) (x₀ : X) (x : ℝ → X) (u : ℝ → U)
    (hopt : NeedleIntegralModel.IsIntegralOptimalPair prob x₀ x u)
    (DK : X →L[ℝ] ℝ) (hK : HasFDerivAt prob.K DK (x prob.T))
    (xε : ℝ → ℝ → X) (uε : ℝ → ℝ → U)
    (hfeasible : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      NeedleIntegralModel.IsIntegralAdmissiblePair prob x₀ (xε ε) (uε ε))
    (g : ℝ × X)
    (htangent : Tendsto
      (fun ε => ε⁻¹ • (costAugmentedEndpoint prob (xε ε) (uε ε) -
        costAugmentedEndpoint prob x u))
      (𝓝[>] (0 : ℝ)) (𝓝 g)) :
    0 ≤ _root_.bolzaTerminalDifferential DK g := by
  apply integralOptimal_costSlope_nonneg prob x₀ x u hopt xε uε hfeasible
  have hΨ := _root_.hasFDerivAt_bolzaTerminalCost prob.K DK
    (costAugmentedEndpoint prob x u) hK
  have hlim := terminalCost_costSlope_of_endpointTangent_punctured
    (_root_.bolzaTerminalCost prob.K) (_root_.bolzaTerminalDifferential DK)
    (fun ε => costAugmentedEndpoint prob (xε ε) (uε ε))
    (costAugmentedEndpoint prob x u) g hΨ htangent
  simpa only [_root_.bolzaTerminalCost_endpoint] using hlim

/-- Complete optimality-to-separation connection for an indexed family of actual
endpoint tangents. Convexity, the cone, disjointness, and the normalized separator
are all derived. The analytic tangent and integral feasibility remain explicit
and are the objects to be supplied by the needle construction and estimates. -/
theorem integralOptimal_normal_covector_of_endpointTangents
    (prob : ContinuousOCP X U) (x₀ : X) (x : ℝ → X) (u : ℝ → U)
    (hopt : NeedleIntegralModel.IsIntegralOptimalPair prob x₀ x u)
    (DK : X →L[ℝ] ℝ) (hK : HasFDerivAt prob.K DK (x prob.T))
    (xε : ι → ℝ → ℝ → X) (uε : ι → ℝ → ℝ → U)
    (hfeasible : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      NeedleIntegralModel.IsIntegralAdmissiblePair prob x₀ (xε i ε) (uε i ε))
    (g : ι → ℝ × X)
    (htangent : ∀ i, Tendsto
      (fun ε => ε⁻¹ • (costAugmentedEndpoint prob (xε i ε) (uε i ε) -
        costAugmentedEndpoint prob x u))
      (𝓝[>] (0 : ℝ)) (𝓝 (g i))) :
    ∃ (q : (ℝ × X) →L[ℝ] ℝ) (α : ℝ),
      q ≠ 0 ∧ 0 < α ∧ (∀ y ∈ endpointVariationCone g, 0 ≤ q y) ∧
      q (1, 0) = α ∧ α⁻¹ • q = _root_.bolzaTerminalDifferential DK := by
  apply exists_normalized_terminal_covector_on_generators
    (_root_.bolzaTerminalDifferential DK) (1, 0) (by simp) g
  intro i
  exact integralOptimal_endpointGenerator_nonneg prob x₀ x u hopt DK hK
    (xε i) (uε i) (hfeasible i) (g i) (htangent i)

/-- A cost-slope interface to the same constructed cone and genuine Hahn–Banach
extraction. It is useful when a direct adjoint identity proves the actual cost
slope before a full augmented endpoint tangent has been established. -/
theorem integralOptimal_normal_covector_of_costSlopes
    (prob : ContinuousOCP X U) (x₀ : X) (x : ℝ → X) (u : ℝ → U)
    (hopt : NeedleIntegralModel.IsIntegralOptimalPair prob x₀ x u)
    (DK : X →L[ℝ] ℝ)
    (xε : ι → ℝ → ℝ → X) (uε : ι → ℝ → ℝ → U)
    (hfeasible : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      NeedleIntegralModel.IsIntegralAdmissiblePair prob x₀ (xε i ε) (uε i ε))
    (g : ι → ℝ × X)
    (hslope : ∀ i, Tendsto
      (fun ε => ε⁻¹ *
        (continuousTotalCost prob (xε i ε) (uε i ε) - continuousTotalCost prob x u))
      (𝓝[>] (0 : ℝ)) (𝓝 (_root_.bolzaTerminalDifferential DK (g i)))) :
    ∃ (q : (ℝ × X) →L[ℝ] ℝ) (α : ℝ),
      q ≠ 0 ∧ 0 < α ∧ (∀ y ∈ endpointVariationCone g, 0 ≤ q y) ∧
      q (1, 0) = α ∧ α⁻¹ • q = _root_.bolzaTerminalDifferential DK := by
  apply exists_normalized_terminal_covector_on_generators
    (_root_.bolzaTerminalDifferential DK) (1, 0) (by simp) g
  intro i
  exact integralOptimal_costSlope_nonneg prob x₀ x u hopt
    (xε i) (uε i) (hfeasible i) (_root_.bolzaTerminalDifferential DK (g i)) (hslope i)

/-- The Hamiltonian jump inequality is obtained from the extracted and normalized
Hahn–Banach multiplier. Membership of each propagated jump in the cone follows
from the cone definition. Disjointness follows from actual feasible endpoint
tangents and optimality, so neither is a user premise. -/
theorem integralOptimal_hahnBanach_needle_inequality
    (prob : ContinuousOCP X U) (x₀ : X) (x : ℝ → X) (u : ℝ → U)
    (hopt : NeedleIntegralModel.IsIntegralOptimalPair prob x₀ x u)
    (DK : X →L[ℝ] ℝ) (hK : HasFDerivAt prob.K DK (x prob.T))
    (xε : ι → ℝ → ℝ → X) (uε : ι → ℝ → ℝ → U)
    (hfeasible : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      NeedleIntegralModel.IsIntegralAdmissiblePair prob x₀ (xε i ε) (uε i ε))
    (Φ : ι → (ℝ × X) →L[ℝ] (ℝ × X))
    (hcost : ∀ i, Φ i (1, 0) = (1, 0)) (ΔL : ι → ℝ) (Δf : ι → X)
    (htangent : ∀ i, Tendsto
      (fun ε => ε⁻¹ • (costAugmentedEndpoint prob (xε i ε) (uε i ε) -
        costAugmentedEndpoint prob x u))
      (𝓝[>] (0 : ℝ)) (𝓝 (Φ i (ΔL i, Δf i)))) :
    ∀ i, 0 ≤ ΔL i + propagatedStateCovector DK (Φ i) (Δf i) := by
  obtain ⟨q, α, _hq, hα, hnonneg, _hcoefficient, hnormalize⟩ :=
    integralOptimal_normal_covector_of_endpointTangents prob x₀ x u hopt DK hK
      xε uε hfeasible (fun i => Φ i (ΔL i, Δf i)) htangent
  intro i
  have hmem := mem_endpointVariationCone (fun j => Φ j (ΔL j, Δf j)) i
  have hnonneg' : 0 ≤ _root_.bolzaTerminalDifferential DK (Φ i (ΔL i, Δf i)) := by
    rw [← hnormalize]
    simp only [smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr hα.le) (hnonneg _ hmem)
  rwa [augmented_pullback_apply DK (Φ i) (hcost i) (ΔL i) (Δf i)] at hnonneg'

end AugmentedEndpointOptimality

