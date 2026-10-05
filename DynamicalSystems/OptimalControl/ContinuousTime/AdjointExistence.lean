import DynamicalSystems.OptimalControl.ContinuousTime.MinimumPrinciple
import DynamicalSystems.OptimalControl.ContinuousTime.AdjointPairing
import DynamicalSystems.Mathlib.Analysis.ODE.StateTransitionExistence

/-!
# Adjoint existence from continuous coefficients on the control horizon

The adjoint is constructed by the existing global ODE existence theorem after
clamping the two actual linearized coefficients to the compact time interval.
Neither a costate nor its derivative is supplied as an input.  The final bridge
identifies this constructed linear adjoint with the project's Hamiltonian-gradient
predicate using actual spatial derivatives of the dynamics and running cost.
-/


open Set
open scoped NNReal

variable {E U : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

theorem exists_adjointOn_Icc
    {A : ℝ → E →L[ℝ] E} {ell : ℝ → E} {T : ℝ}
    (hT : 0 ≤ T) (hA : ContinuousOn A (Icc 0 T))
    (hell : ContinuousOn ell (Icc 0 T)) (k : E) :
    ∃ p : ℝ → E, Continuous p ∧ p T = k ∧
      ∀ t ∈ Icc 0 T, HasDerivAt p (-(A t).adjoint (p t) - ell t) t := by
  let Aext : ℝ → E →L[ℝ] E := fun t => A (projIcc 0 T hT t)
  let lext : ℝ → E := fun t => ell (projIcc 0 T hT t)
  have hAc : Continuous Aext := hA.domRestrict.comp continuous_projIcc
  have hlc : Continuous lext := hell.domRestrict.comp continuous_projIcc
  let B : ℝ → E →L[ℝ] E := fun t => -(Aext t).adjoint
  have hBc : Continuous B :=
    (ContinuousLinearMap.adjoint.continuous.comp hAc).neg
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  obtain ⟨N, hN⟩ := isCompact_Icc.exists_bound_of_continuousOn hell
  let K : ℝ≥0 := ⟨max M 0, le_max_right _ _⟩
  have hBbound : ∀ t, ‖B t‖ ≤ (K : ℝ) := by
    intro t
    dsimp [B]
    rw [norm_neg, ContinuousLinearMap.adjoint.norm_map]
    exact (hM (projIcc 0 T hT t) (projIcc 0 T hT t).property).trans
      (le_max_left _ _)
  have hll : ∀ t, LipschitzWith K (fun y : E => B t y - lext t) := by
    intro t
    apply LipschitzWith.of_dist_le_mul
    intro y z
    rw [dist_sub_right]
    exact (ContinuousLinearMap.lipschitzWith_of_opNorm_le (hBbound t)).dist_le_mul y z
  have hzero : ∀ t, ‖B t 0 - lext t‖ ≤ N := by
    intro t
    simp only [map_zero, zero_sub, norm_neg]
    exact hN (projIcc 0 T hT t) (projIcc 0 T hT t).property
  have hV : Continuous (fun z : ℝ × E => B z.1 z.2 - lext z.1) :=
    ((hBc.comp continuous_fst).clm_apply continuous_snd).sub
      (hlc.comp continuous_fst)
  obtain ⟨F, hF⟩ := global_existence (f := fun t y => B t y - lext t)
    hll hzero hV
  let p := F T k
  have hp : ∀ t, HasDerivAt p (B t (p t) - lext t) t := (hF T k).1
  refine ⟨p, continuous_iff_continuousAt.mpr (fun t => (hp t).continuousAt),
    (hF T k).2, ?_⟩
  intro t ht
  simpa only [B, Aext, lext, projIcc_of_mem hT ht,
    neg_apply] using hp t

theorem _root_.exists_costate_of_spatial_derivatives
    (prob : ContinuousOCP E U) (x : ℝ → E) (u : ℝ → U)
    (A : ℝ → E →L[ℝ] E) (ell : ℝ → E)
    (hT : 0 ≤ prob.T)
    (hA : ContinuousOn A (Icc 0 prob.T))
    (hell : ContinuousOn ell (Icc 0 prob.T))
    (hf : ∀ t ∈ Icc 0 prob.T,
      HasFDerivAt (fun y => prob.f t y (u t)) (A t) (x t))
    (hL : ∀ t ∈ Icc 0 prob.T,
      HasGradientAt (fun y => prob.L t y (u t)) (ell t) (x t)) :
    ∃ p : ℝ → E, Continuous p ∧
      (∀ t ∈ Icc 0 prob.T,
        HasDerivAt p (-(A t).adjoint (p t) - ell t) t) ∧
      costateEquation prob.L prob.f prob.T x u p ∧
      transversalityCondition prob.K prob.T x p := by
  obtain ⟨p, hpc, hpT, hpd⟩ := exists_adjointOn_Icc hT hA hell
    (gradient prob.K (x prob.T))
  refine ⟨p, hpc, hpd, ?_, hpT⟩
  intro t ht
  have hgrad := hasGradientAt_hamiltonian
    (p := p t) (hL t ht) (hf t ht)
  change HasDerivAt p
    (-gradient (fun y => prob.L t y (u t) + inner ℝ (p t) (prob.f t y (u t)))
      (x t)) t
  rw [hgrad.gradient]
  convert hpd t ht using 1
  abel

