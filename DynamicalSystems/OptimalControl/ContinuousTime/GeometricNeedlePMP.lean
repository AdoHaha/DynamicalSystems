import DynamicalSystems.OptimalControl.ContinuousTime.BolzaAugmentation
import DynamicalSystems.OptimalControl.ContinuousTime.NeedleTerminalFamily

/-!
# A geometric needle proof from primitive globally regular branch fields

This file constructs feasible needle families for the actual cost-augmented ODE,
proves their endpoint tangents using actual spatial derivatives, and feeds those
tangents into the optimality-to-cone-to-Hahn–Banach argument. Global Lipschitz
hypotheses for both dynamics and running cost make the augmented IVPs available.
-/


open Set Filter MeasureTheory
open scoped Topology NNReal

variable {X U : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Primitive global hypotheses for one prescribed control branch. These are
bounds and regularity of the actual `f` and `L`, not variation or PMP assertions. -/
structure BolzaBranchRegularity (prob : ContinuousOCP X U) (w : ℝ → U) where
  /-- Uniform state Lipschitz constant for the actual dynamics on this branch. -/
  Kf : ℝ≥0
  /-- Uniform state Lipschitz constant for the actual running cost on this branch. -/
  KL : ℝ≥0
  /-- Uniform bound on the norm of the actual dynamics at state zero. -/
  Bf : ℝ
  /-- Uniform bound on the norm of the actual running cost at state zero. -/
  BL : ℝ
  dynamics_lipschitz : ∀ t, LipschitzWith Kf (fun z => prob.f t z (w t))
  cost_lipschitz : ∀ t, LipschitzWith KL (fun z => prob.L t z (w t))
  dynamics_zero_bound : ∀ t, ‖prob.f t 0 (w t)‖ ≤ Bf
  cost_zero_bound : ∀ t, ‖prob.L t 0 (w t)‖ ≤ BL
  dynamics_continuous : Continuous (fun q : ℝ × X => prob.f q.1 q.2 (w q.1))
  cost_continuous : Continuous (fun q : ℝ × X => prob.L q.1 q.2 (w q.1))

namespace BolzaBranchRegularity

variable {prob : ContinuousOCP X U} {w : ℝ → U}

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem augmented_lipschitz (r : BolzaBranchRegularity prob w) (t : ℝ) :
    LipschitzWith (max r.KL r.Kf) (fun y => (_root_.ContinuousOCP.bolzaToMayer prob).f t y (w t)) := by
  simpa only [mul_one, Function.comp_def, _root_.ContinuousOCP.bolzaToMayer] using
    ((r.cost_lipschitz t).prodMk (r.dynamics_lipschitz t)).comp
      (LipschitzWith.prod_snd (α := ℝ))

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem augmented_zero_bound (r : BolzaBranchRegularity prob w) (t : ℝ) :
    ‖(_root_.ContinuousOCP.bolzaToMayer prob).f t 0 (w t)‖ ≤ max r.BL r.Bf := by
  exact max_le_max (r.cost_zero_bound t) (r.dynamics_zero_bound t)

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem augmented_continuous (r : BolzaBranchRegularity prob w) :
    Continuous (fun q : ℝ × (ℝ × X) => (_root_.ContinuousOCP.bolzaToMayer prob).f q.1 q.2 (w q.1)) := by
  have hp : Continuous (fun q : ℝ × (ℝ × X) => (q.1, q.2.2)) :=
    continuous_fst.prodMk continuous_snd.snd
  exact (r.cost_continuous.comp hp).prodMk (r.dynamics_continuous.comp hp)

end BolzaBranchRegularity

/-- A feasible original needle family with its actual cost/state endpoint tangent,
constructed entirely from primitive branch hypotheses and the actual spatial
linearization. The augmented ODE family, O(ε) estimate, local jump, and terminal
tangent are all derived in the proof. -/
theorem exists_needle_endpointTangent_of_primitive_data
    (prob : ContinuousOCP X U) (x_init : X) (x : ℝ → X) (u : ℝ → U)
    (τ : ℝ) (v : U)
    (r₀ : BolzaBranchRegularity prob u)
    (rv : BolzaBranchRegularity prob (fun _ => v))
    (hx : IsIntegralCurve x (fun t z => prob.f t z (u t)))
    (hinit : x 0 = x_init) (hu : ∀ t ∈ Icc 0 prob.T, u t ∈ prob.controlSet)
    (hv : v ∈ prob.controlSet) (hτ₀ : 0 < τ) (hτ : τ ≤ prob.T)
    (DL : ℝ → X → X →L[ℝ] ℝ) (Df : ℝ → X → X →L[ℝ] X)
    (hDL : ∀ t ∈ Icc 0 prob.T, ∀ z,
      HasFDerivAt (fun y => prob.L t y (u t)) (DL t z) z)
    (hDf : ∀ t ∈ Icc 0 prob.T, ∀ z,
      HasFDerivAt (fun y => prob.f t y (u t)) (Df t z) z)
    (hDLc : ∀ t ∈ Icc 0 prob.T,
      ContinuousAt (fun q : ℝ × X => DL q.1 q.2) (t, x t))
    (hDfc : ∀ t ∈ Icc 0 prob.T,
      ContinuousAt (fun q : ℝ × X => Df q.1 q.2) (t, x t))
    (Φ : ℝ → ℝ → (ℝ × X) →L[ℝ] (ℝ × X))
    (hdiag : Φ prob.T prob.T = ContinuousLinearMap.id ℝ (ℝ × X))
    (hback : ∀ t ∈ Icc 0 prob.T, HasDerivAt (fun s => Φ prob.T s)
      (-((Φ prob.T t).comp (augmentedLinearCoefficient (DL t (x t)) (Df t (x t)))) ) t) :
    ∃ xε : ℝ → ℝ → X,
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), NeedleIntegralModel.IsIntegralAdmissiblePair
        prob x_init (xε ε) (needleControl u τ v ε)) ∧
      Tendsto (fun ε => ε⁻¹ •
        (costAugmentedEndpoint prob (xε ε) (needleControl u τ v ε) -
          costAugmentedEndpoint prob x u))
        (𝓝[>] (0 : ℝ))
        (𝓝 (Φ prob.T τ (prob.L τ (x τ) v - prob.L τ (x τ) (u τ),
          prob.f τ (x τ) v - prob.f τ (x τ) (u τ)))) := by
  let Y := _root_.bolzaCostLift prob x u
  let P := _root_.ContinuousOCP.bolzaToMayer prob
  let D : ℝ → (ℝ × X) → (ℝ × X) →L[ℝ] (ℝ × X) :=
    fun t y => augmentedLinearCoefficient (DL t y.2) (Df t y.2)
  have hT : 0 ≤ prob.T := hτ₀.le.trans hτ
  have hY : IsIntegralCurve Y (fun t y => P.f t y (u t)) :=
    _root_.isIntegralCurve_bolzaCostLift prob x u hx r₀.cost_continuous
  have hYinit : Y 0 = (0, x_init) := by simp [Y, _root_.bolzaCostLift, hinit]
  obtain ⟨M, hM, hforcing⟩ := NeedleIntegralModel.exists_frozen_forcing_bound
    P Y u v hY.continuous r₀.augmented_continuous rv.augmented_continuous
  obtain ⟨Yε, hfamily, hjump⟩ := NeedleIntegralModel.exists_feasible_needle_family
    P (0, x_init) Y u τ v r₀.augmented_lipschitz rv.augmented_lipschitz
    r₀.augmented_zero_bound rv.augmented_zero_bound
    r₀.augmented_continuous rv.augmented_continuous
    continuous_const continuous_const hY hYinit hu hv hτ₀ hτ hM hforcing
  have hD : ∀ t ∈ Icc 0 prob.T, ∀ y,
      HasFDerivAt (fun z => P.f t z (u t)) (D t y) y := by
    intro t ht y
    exact hasFDerivAt_augmented_dynamics prob t (u t) y (DL t y.2) (Df t y.2)
      (hDL t ht y.2) (hDf t ht y.2)
  have hDc : ∀ t ∈ Icc 0 prob.T,
      ContinuousAt (fun q : ℝ × (ℝ × X) => D q.1 q.2) (t, Y t) := by
    intro t ht
    exact continuousAt_augmented_spatial_derivative DL Df t (Y t)
      (hDLc t ht) (hDfc t ht)
  have hC : 0 ≤ 2 * M * Real.exp ((max r₀.KL r₀.Kf : ℝ≥0) * prob.T) :=
    mul_nonneg (mul_nonneg (by norm_num) hM) (Real.exp_pos _).le
  have hend := NeedleIntegralModel.terminal_tangent_of_constructed_family
    P (0, x_init) Y u τ v (D := D) (Phi := Φ) hτ₀.le hτ hC
    r₀.augmented_continuous hY hD hDc hdiag
    (fun t ht => hback t ⟨hτ₀.le.trans ht.1, ht.2⟩) hfamily hjump
  refine ⟨fun ε t => (Yε ε t).2, ?_, ?_⟩
  · filter_upwards [hfamily] with ε hε
    exact integralAdmissible_of_augmented prob x_init (Yε ε)
      (needleControl u τ v ε) hT hε.admissible
  · apply hend.congr'
    filter_upwards [hfamily] with ε hε
    rw [costAugmentedEndpoint_eq_terminal_of_admissible prob x_init (Yε ε)
      (needleControl u τ v ε) hT hε.admissible]
    rfl

/-- Needle directions are indexed by a positive insertion time and a feasible
control value. Insertion at zero follows later from continuity. -/
def NeedleIndex (prob : ContinuousOCP X U) :=
  {t : ℝ // t ∈ Ioc 0 prob.T} × {v : U // v ∈ prob.controlSet}

/-- The augmented terminal generator propagated from an actual instantaneous
running-cost/dynamics jump. -/
def needleEndpointGenerator (prob : ContinuousOCP X U) (x : ℝ → X) (u : ℝ → U)
    (Φ : ℝ → ℝ → (ℝ × X) →L[ℝ] (ℝ × X)) (i : NeedleIndex prob) : ℝ × X :=
  Φ prob.T i.1.1 (prob.L i.1.1 (x i.1.1) i.2.1 - prob.L i.1.1 (x i.1.1) (u i.1.1),
    prob.f i.1.1 (x i.1.1) i.2.1 - prob.f i.1.1 (x i.1.1) (u i.1.1))

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] in
/-- A continuous endpoint value inherits the nonnegative needle inequality from
positive times. The positive horizon makes the right-neighborhood filter proper. -/
theorem nonneg_on_Icc_of_nonneg_on_Ioc
    (J : ℝ → ℝ) (T : ℝ) (hT : 0 < T) (hc : ContinuousAt J 0)
    (hpos : ∀ t ∈ Ioc 0 T, 0 ≤ J t) : ∀ t ∈ Icc 0 T, 0 ≤ J t := by
  have hzero : 0 ≤ J 0 := by
    apply ge_of_tendsto (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0)))
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hT)] with t ht htop
    exact hpos t ⟨ht, le_of_lt htop⟩
  intro t ht
  rcases eq_or_lt_of_le ht.1 with hzero' | hpos'
  · simpa only [← hzero'] using hzero
  · exact hpos t ⟨hpos', ht.2⟩

/-- A literal geometric needle proof of the normal free-terminal-state PMP in
covector form, under explicit primitive global branch hypotheses.

No needle family, endpoint tangent, variation inequality, separating functional,
propagator, or adjoint equation is an input. The proof constructs the augmented
propagator and feasible needles, derives their terminal tangents, applies actual
optimality, forms the cone, and invokes geometric Hahn–Banach. Its normalized
functional is then pulled back to obtain the full normal Bolza adjoint.

The running-cost global Lipschitz hypothesis is used to apply the existing IVP
construction to the augmented state. The direct normal-adjoint proof can work
under weaker running-cost assumptions. -/
theorem exists_geometricNormalPMP_of_primitive_data [FiniteDimensional ℝ X]
    (prob : ContinuousOCP X U) (x_init : X) (x : ℝ → X) (u : ℝ → U)
    (hT : 0 < prob.T)
    (hopt : NeedleIntegralModel.IsIntegralOptimalPair prob x_init x u)
    (r₀ : BolzaBranchRegularity prob u)
    (rtest : ∀ v ∈ prob.controlSet, BolzaBranchRegularity prob (fun _ => v))
    (hx : IsIntegralCurve x (fun t z => prob.f t z (u t)))
    (DL : ℝ → X → X →L[ℝ] ℝ) (Df : ℝ → X → X →L[ℝ] X)
    (hDL : ∀ t ∈ Icc 0 prob.T, ∀ z,
      HasFDerivAt (fun y => prob.L t y (u t)) (DL t z) z)
    (hDf : ∀ t ∈ Icc 0 prob.T, ∀ z,
      HasFDerivAt (fun y => prob.f t y (u t)) (Df t z) z)
    (hDLc : ∀ t ∈ Icc 0 prob.T,
      ContinuousAt (fun q : ℝ × X => DL q.1 q.2) (t, x t))
    (hDfc : ∀ t ∈ Icc 0 prob.T,
      ContinuousAt (fun q : ℝ × X => Df q.1 q.2) (t, x t))
    (DK : X →L[ℝ] ℝ) (hK : HasFDerivAt prob.K DK (x prob.T)) :
    ∃ (Φ : ℝ → ℝ → (ℝ × X) →L[ℝ] (ℝ × X))
      (q : (ℝ × X) →L[ℝ] ℝ) (α : ℝ),
      q ≠ 0 ∧ 0 < α ∧ q (1, 0) = α ∧ α⁻¹ • q = _root_.bolzaTerminalDifferential DK ∧
      (∀ y ∈ endpointVariationCone (needleEndpointGenerator prob x u Φ), 0 ≤ q y) ∧
      (∀ t ∈ Icc 0 prob.T,
        HasDerivAt (fun s => propagatedStateCovector DK (Φ prob.T s))
          (-(DL t (x t) + (propagatedStateCovector DK (Φ prob.T t)).comp (Df t (x t)))) t) ∧
      propagatedStateCovector DK (Φ prob.T prob.T) = DK ∧
      (∀ t ∈ Icc 0 prob.T, ∀ v ∈ prob.controlSet,
        0 ≤ prob.L t (x t) v - prob.L t (x t) (u t) +
          propagatedStateCovector DK (Φ prob.T t)
            (prob.f t (x t) v - prob.f t (x t) (u t))) := by
  have hgraph : Continuous (fun t => (t, x t)) := continuous_id.prodMk hx.continuous
  have hℓ : ContinuousOn (fun t => DL t (x t)) (Icc 0 prob.T) := by
    intro t ht
    exact ((hDLc t ht).comp_of_eq (hgraph.continuousAt (x := t)) rfl).continuousWithinAt
  have hA : ContinuousOn (fun t => Df t (x t)) (Icc 0 prob.T) := by
    intro t ht
    exact ((hDfc t ht).comp_of_eq (hgraph.continuousAt (x := t)) rfl).continuousWithinAt
  obtain ⟨Φ, hdiag, _hforward, hback, _hcomp, hcost, hpd, hpT⟩ :=
    exists_augmented_stateTransitionOn_Icc (fun t => DL t (x t))
      (fun t => Df t (x t)) 0 prob.T hT.le hℓ hA DK
  have hfamilies : ∀ i : NeedleIndex prob, ∃ xε : ℝ → ℝ → X,
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), NeedleIntegralModel.IsIntegralAdmissiblePair
        prob x_init (xε ε) (needleControl u i.1.1 i.2.1 ε)) ∧
      Tendsto (fun ε => ε⁻¹ •
        (costAugmentedEndpoint prob (xε ε) (needleControl u i.1.1 i.2.1 ε) -
          costAugmentedEndpoint prob x u))
        (𝓝[>] (0 : ℝ)) (𝓝 (needleEndpointGenerator prob x u Φ i)) := by
    intro i
    exact exists_needle_endpointTangent_of_primitive_data prob x_init x u i.1.1 i.2.1
      r₀ (rtest i.2.1 i.2.2) hx hopt.1.1 hopt.1.2.1 i.2.2 i.1.2.1 i.1.2.2
      DL Df hDL hDf hDLc hDfc Φ (hdiag prob.T) (hback prob.T)
  choose xε hfeasible htangent using hfamilies
  obtain ⟨q, α, hq, hα, hcone, hqα, hnormalize⟩ :=
    integralOptimal_normal_covector_of_endpointTangents prob x_init x u hopt DK hK
      xε (fun i ε => needleControl u i.1.1 i.2.1 ε) hfeasible
      (needleEndpointGenerator prob x u Φ) htangent
  have hpositive : ∀ t ∈ Ioc 0 prob.T, ∀ v ∈ prob.controlSet,
      0 ≤ prob.L t (x t) v - prob.L t (x t) (u t) +
        propagatedStateCovector DK (Φ prob.T t)
          (prob.f t (x t) v - prob.f t (x t) (u t)) := by
    intro t ht v hv
    let i : NeedleIndex prob := (⟨t, ht⟩, ⟨v, hv⟩)
    have hmem := mem_endpointVariationCone (needleEndpointGenerator prob x u Φ) i
    have hc : 0 ≤ _root_.bolzaTerminalDifferential DK (needleEndpointGenerator prob x u Φ i) := by
      rw [← hnormalize]
      simp only [smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr hα.le) (hcone _ hmem)
    change 0 ≤ _root_.bolzaTerminalDifferential DK (Φ prob.T t
      (prob.L t (x t) v - prob.L t (x t) (u t),
        prob.f t (x t) v - prob.f t (x t) (u t))) at hc
    rwa [augmented_pullback_apply DK (Φ prob.T t) (hcost t ⟨ht.1.le, ht.2⟩)] at hc
  refine ⟨Φ, q, α, hq, hα, hqα, hnormalize, hcone, hpd, hpT, ?_⟩
  intro t ht v hv
  let rv := rtest v hv
  have hpc : ContinuousAt (fun s => propagatedStateCovector DK (Φ prob.T s)) 0 :=
    (hpd 0 ⟨le_rfl, hT.le⟩).continuousAt
  have hJ : ContinuousAt (fun s => prob.L s (x s) v - prob.L s (x s) (u s) +
      propagatedStateCovector DK (Φ prob.T s)
        (prob.f s (x s) v - prob.f s (x s) (u s))) 0 :=
    ((rv.cost_continuous.comp hgraph).continuousAt.sub
      (r₀.cost_continuous.comp hgraph).continuousAt).add
      (hpc.clm_apply ((rv.dynamics_continuous.comp hgraph).continuousAt.sub
        (r₀.dynamics_continuous.comp hgraph).continuousAt))
  exact nonneg_on_Icc_of_nonneg_on_Ioc _ prob.T hT hJ
    (fun s hs => hpositive s hs v hv) t ht

