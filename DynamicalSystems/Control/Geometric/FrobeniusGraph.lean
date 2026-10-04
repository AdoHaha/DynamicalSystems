/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.Frobenius
public import DynamicalSystems.Control.Geometric.MultiFlow
public import Mathlib.Analysis.Convex.Topology

/-! # Local solutions of the compatible graph equation

For a continuously differentiable, flat graph connection, the finite flow construction underlying
simultaneous rectification gives an integral parametrization. Its horizontal derivative is the
identity, so its horizontal projection is an affine translation on a sufficiently small ball.
The vertical projection then solves the prescribed first-order graph equation.

This is the classical graph form of Frobenius integrability. The graph-compatibility formulation
follows Khavkine and Růžička's `lean-dg-frobenius` project. See also Krener,
*Differential Geometric Methods in Nonlinear Control*, Encyclopedia of Systems and Control,
2nd ed., and Sontag,
*Mathematical Control Theory*, 2nd ed., Ch. 4 §4.2–§4.4.
-/

@[expose] public section

open Set Filter Metric
open scoped Topology

/-- A map with identity derivative throughout a ball is the corresponding affine translation. -/
theorem affine_on_ball_of_hasFDerivAt_id
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Q : E → E} {x₀ : E} {r : ℝ} (hr : 0 < r) (hQ₀ : Q 0 = x₀)
    (hQ : ∀ t ∈ ball (0 : E) r, HasFDerivAt Q (ContinuousLinearMap.id ℝ E) t) :
    ∀ t ∈ ball (0 : E) r, Q t = x₀ + t := by
  have hA : ∀ t : E, HasFDerivAt (fun u : E => x₀ + u)
      (ContinuousLinearMap.id ℝ E) t := fun t => (hasFDerivAt_id t).const_add x₀
  exact isOpen_ball.eqOn_of_fderiv_eq (convex_ball (0 : E) r).isPreconnected
    (fun t ht => (hQ t ht).differentiableAt.differentiableWithinAt)
    (fun t _ => (hA t).differentiableAt.differentiableWithinAt)
    (fun t ht => (hQ t ht).fderiv.trans (hA t).fderiv.symm)
    (mem_ball_self hr) (by simpa using hQ₀)

variable {k : ℕ} {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [CompleteSpace Y] [FiniteDimensional ℝ Y]

/-- The finite flow construction supplies a local integral parametrization of a compatible
graph connection. Its differential is the graph inclusion at its image. -/
theorem exists_local_graph_parametrization
    (g : (Fin k → ℝ) × Y → (Fin k → ℝ) →L[ℝ] Y)
    (hg : ContDiff ℝ 1 g) (hcompat : TotalFderivCompat g Set.univ)
    (x₀ : Fin k → ℝ) (z : Y) :
    ∃ L : (Fin k → ℝ) → (Fin k → ℝ) × Y,
      L 0 = (x₀, z) ∧ ∀ᶠ t in 𝓝 0,
        HasFDerivAt L ((ContinuousLinearMap.id ℝ (Fin k → ℝ)).prod (g (L t))) t := by
  have hf : ∀ i, ContDiffAt ℝ 1 (graphFrame g i) (x₀, z) := by
    intro i
    exact contDiffAt_const.prodMk
      ((ContinuousLinearMap.apply ℝ Y (Pi.single i (1 : ℝ) : Fin k → ℝ)).contDiff.contDiffAt
        |>.comp (x₀, z) hg.contDiffAt)
  have hcomm : ∀ i j, ∀ᶠ p in 𝓝 (x₀, z),
      lieBracket (graphFrame g i) (graphFrame g j) p = 0 := by
    intro i j
    apply Filter.Eventually.of_forall
    intro p
    change lieBracket (graphField g (Pi.single i 1)) (graphField g (Pi.single j 1)) p = 0
    rw [bracket_graphField g _ _ p (hg.differentiable (by simp) p),
      hcompat p (mem_univ p)]
    rfl
  let C := frameComplement (fun i => graphFrame g i (x₀, z))
  let ι : (Fin k → ℝ) →L[ℝ] ((Fin k → ℝ) × ↥C) :=
    (ContinuousLinearMap.id ℝ (Fin k → ℝ)).prod 0
  let F := simultaneousRectifyingMap hf
  let L := F ∘ ι
  have hL₀ : L 0 = (x₀, z) := by
    simp only [L, Function.comp_apply, map_zero, F, simultaneousRectifyingMap_zero]
  refine ⟨L, hL₀, ?_⟩
  have hι : Tendsto ι (𝓝 0) (𝓝 0) := by
    have h := ι.continuous.tendsto (0 : Fin k → ℝ)
    rw [map_zero] at h
    exact h
  filter_upwards [hι (eventually_simultaneousRectifyingMap_fderiv hf hcomm)] with t ht
  have hder := ht.1.hasFDerivAt.comp t ι.hasFDerivAt
  apply hder.congr_fderiv
  apply ContinuousLinearMap.coe_injective
  apply (Pi.basisFun ℝ (Fin k)).ext
  intro i
  rw [Pi.basisFun_apply]
  change fderiv ℝ F (ι t) (Pi.single i 1, 0) = graphFrame g i (F (ι t))
  exact ht.2 i

/-- A continuously differentiable compatible graph connection has a local graph solution through
every prescribed point, on an open neighborhood of the initial horizontal coordinate. -/
theorem exists_local_graph_solution
    (g : (Fin k → ℝ) × Y → (Fin k → ℝ) →L[ℝ] Y)
    (hg : ContDiff ℝ 1 g) (hcompat : TotalFderivCompat g Set.univ)
    (x₀ : Fin k → ℝ) (z : Y) :
    ∃ U : Set (Fin k → ℝ), IsOpen U ∧ x₀ ∈ U ∧
      ∃ w : (Fin k → ℝ) → Y, w x₀ = z ∧
        ∀ x ∈ U, HasFDerivAt w (g (x, w x)) x := by
  obtain ⟨L, hL₀, hL⟩ := exists_local_graph_parametrization g hg hcompat x₀ z
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hL
  have hfirst : ∀ t ∈ ball (0 : Fin k → ℝ) r, (L t).1 = x₀ + t := by
    apply affine_on_ball_of_hasFDerivAt_id hr
    · exact congrArg Prod.fst hL₀
    · intro t ht
      simpa only [ContinuousLinearMap.fst_comp_prod] using (hball ht).fst
  let w : (Fin k → ℝ) → Y := fun x => (L (x - x₀)).2
  refine ⟨ball x₀ r, isOpen_ball, mem_ball_self hr, w, ?_, ?_⟩
  · simp only [w, sub_self, hL₀]
  · intro x hx
    have ht : x - x₀ ∈ ball (0 : Fin k → ℝ) r := by
      simpa only [mem_ball, dist_zero_right, dist_eq_norm, sub_zero] using hx
    have hpoint : L (x - x₀) = (x, w x) := by
      apply Prod.ext
      · simpa only [add_sub_cancel] using hfirst (x - x₀) ht
      · rfl
    have hder := (hball ht).snd.comp x ((hasFDerivAt_id x).sub_const x₀)
    have hw : HasFDerivAt w (g (L (x - x₀))) x := by
      simpa only [ContinuousLinearMap.snd_comp_prod, ContinuousLinearMap.comp_id,
        Function.comp_def, id_eq] using hder
    rw [hpoint] at hw
    exact hw

end
