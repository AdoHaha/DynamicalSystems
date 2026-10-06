/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.ControlHorizon
public import DynamicalSystems.OptimalControl.ContinuousTime.VelocityTrajectories
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
public import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Weak-to-uniform continuity of the primitive of an `L²` velocity

For `v ∈ L²(0,T; E)` the primitive `t ↦ i + ∫₀ᵗ v` is a continuous path.  Berkovitz &
Medhin's penalty `F_K` (11.3.6) evaluates the running cost, the Volterra residual and the
endpoint term on this path while the velocity `v` ranges over a **weakly** compact `L²`
energy ball.  This file shows that the primitive depends continuously on `v`:

* `setIntegralCLM`: `v ↦ ∫_S v` is a continuous linear map `L²(μ) → E` (Cauchy–Schwarz).
* `continuous_comp_weakSpace_of_finiteDimensional`: a continuous linear map from a normed
  space into a finite-dimensional space is continuous for the weak topology on the source.
  In particular `v ↦ ∫₀ᵗ v` is weakly continuous (pointwise weak continuity).
* `dist_primitivePath_le`: the `√`-Hölder modulus
  `‖(∫₀ˢ − ∫₀ʳ) v‖ ≤ √|s − r| ‖v‖`, hence equicontinuity on norm-bounded sets
  (`equicontinuous_primitivePath`).
* `continuousOn_primitiveBoundedPath_weakSpace`: **weak-to-uniform continuity** — on every
  norm-bounded set of `L²` the map into `C(ControlTime T, E)` with the sup norm is continuous
  for the weak topology.  The upgrade from pointwise to uniform convergence is Mathlib's
  Ascoli statement `Equicontinuous.tendsto_uniformFun_iff_pi`.

The restriction to norm-bounded sets is necessary: on the whole weak space the primitive is
not continuous into the sup norm (an infinite-dimensional `L²` has weak neighbourhoods of
every point containing unbounded vectors).

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), §11.3,
Lemma 11.3.4 and (11.3.6).  Names are concept names; the citation lives in docstrings.
-/

@[expose] public section

open Set MeasureTheory Filter Metric
open scoped Topology BoundedContinuousFunction ENNReal

namespace OptimalControl.BoundedState

section SetIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E] [IsFiniteMeasure μ] in
/-- The squared `L²` norm is the integral of the squared pointwise norm (any normed
target space). -/
theorem Lp_two_norm_sq_eq_integral_norm_sq (v : Lp E 2 μ) :
    ‖v‖ ^ 2 = ∫ a, ‖v a‖ ^ 2 ∂μ := by
  have h := (Lp.memLp v).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  rw [Lp.norm_def, h]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2, ENNReal.toReal_ofReal (by positivity)]
  have h0 : 0 ≤ ∫ a, ‖v a‖ ^ (2 : ℝ) ∂μ := integral_nonneg fun _ => by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
  simp

/-- Cauchy–Schwarz bound for the set integral of an `L²` class.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2). -/
theorem norm_setIntegral_le (S : Set α) (v : Lp E 2 μ) :
    ‖∫ x in S, v x ∂μ‖ ≤ Real.sqrt (μ.real S) * ‖v‖ := by
  have hv : Integrable v μ := (Lp.memLp v).integrable (by norm_num)
  have hsq : Integrable (fun x => ‖v x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).1 (Lp.memLp v)
  have h1 := integral_norm_le_sqrt_mass_mul_sqrt_sq (μ := μ.restrict S)
    hv.integrableOn.aestronglyMeasurable hsq.restrict
  have h2 : ∫ x, ‖v x‖ ^ 2 ∂(μ.restrict S) ≤ ‖v‖ ^ 2 := by
    rw [Lp_two_norm_sq_eq_integral_norm_sq]
    exact setIntegral_le_integral hsq (Eventually.of_forall fun _ => by positivity)
  have h3 : (μ.restrict S).real univ ≤ μ.real S := by
    simp [Measure.real]
  calc ‖∫ x in S, v x ∂μ‖ ≤ ∫ x in S, ‖v x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ Real.sqrt ((μ.restrict S).real univ) * Real.sqrt (∫ x, ‖v x‖ ^ 2 ∂(μ.restrict S)) := h1
    _ ≤ Real.sqrt (μ.real S) * ‖v‖ := by
      refine mul_le_mul (Real.sqrt_le_sqrt h3) ?_ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      calc Real.sqrt (∫ x, ‖v x‖ ^ 2 ∂(μ.restrict S)) ≤ Real.sqrt (‖v‖ ^ 2) :=
            Real.sqrt_le_sqrt h2
        _ = ‖v‖ := Real.sqrt_sq (norm_nonneg _)

/-- The set integral `v ↦ ∫_S v ∂μ` as a continuous linear map on `L²(μ)`: its operator norm
is at most `√(μ S)` (Cauchy–Schwarz).

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2). -/
noncomputable def setIntegralCLM (μ : Measure α) [IsFiniteMeasure μ] (S : Set α) :
    Lp E 2 μ →L[ℝ] E :=
  LinearMap.mkContinuous
    { toFun := fun v => ∫ x in S, v x ∂μ
      map_add' := fun v w => by
        have hv : Integrable v μ := (Lp.memLp v).integrable (by norm_num)
        have hw : Integrable w μ := (Lp.memLp w).integrable (by norm_num)
        rw [← integral_add hv.integrableOn hw.integrableOn]
        exact integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_add v w))
      map_smul' := fun c v => by
        rw [RingHom.id_apply, ← integral_smul]
        exact integral_congr_ae (ae_restrict_of_ae (Lp.coeFn_smul c v)) }
    (Real.sqrt (μ.real S)) (norm_setIntegral_le S)

theorem setIntegralCLM_apply (S : Set α) (v : Lp E 2 μ) :
    setIntegralCLM μ S v = ∫ x in S, v x ∂μ := rfl

end SetIntegral

section WeakContinuity

variable {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Pointwise weak continuity.** A continuous linear map into a finite-dimensional space is
continuous for the weak topology of the source (each coordinate is a continuous linear
functional, and the weak topology is the coarsest making these continuous).

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.4. -/
theorem continuous_comp_weakSpace_of_finiteDimensional (A : X →L[ℝ] F) :
    Continuous fun x : WeakSpace ℝ X => A ((toWeakSpace ℝ X).symm x) := by
  let e : F ≃L[ℝ] (Fin (Module.finrank ℝ F) → ℝ) :=
    (Module.finBasis ℝ F).equivFun.toContinuousLinearEquiv
  have hcoord : Continuous fun x : WeakSpace ℝ X => e (A ((toWeakSpace ℝ X).symm x)) := by
    refine continuous_pi fun k => ?_
    let ℓ : StrongDual ℝ X :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (Module.finrank ℝ F) => ℝ) k).comp
        ((e : F →L[ℝ] (Fin (Module.finrank ℝ F) → ℝ)).comp A)
    exact WeakBilin.eval_continuous (topDualPairing ℝ X).flip ℓ
  convert e.symm.continuous.comp hcoord using 1
  ext x
  simp

end WeakContinuity

section Primitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

variable (T : ℝ)

/-- The horizon measure `λ|(0,T]` on which the velocity lives. -/
noncomputable abbrev horizonMeasure : Measure ℝ := volume.restrict (Ioc (0 : ℝ) T)

/-- The primitive evaluation `v ↦ ∫₀ᵗ v` as a continuous linear map on `L²(0,T; E)`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.1). -/
noncomputable def primitiveValue (t : ℝ) : Lp E 2 (horizonMeasure T) →L[ℝ] E :=
  setIntegralCLM (horizonMeasure T) (Ioc (0 : ℝ) t)

variable {T}

/-- **Hölder modulus of the primitive.**  `‖∫₀ˢ v − ∫₀ʳ v‖ ≤ √(s − r) ‖v‖_{L²}`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.2). -/
theorem norm_primitiveValue_sub_le (v : Lp E 2 (horizonMeasure T)) {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) :
    ‖primitiveValue T s v - primitiveValue T r v‖ ≤ Real.sqrt (s - r) * ‖v‖ := by
  have hv : Integrable v (horizonMeasure T) := (Lp.memLp v).integrable (by norm_num)
  have hsplit : primitiveValue T s v - primitiveValue T r v =
      setIntegralCLM (horizonMeasure T) (Ioc r s) v := by
    simp only [primitiveValue, setIntegralCLM_apply]
    rw [← Ioc_union_Ioc_eq_Ioc hr hrs, setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl)
      measurableSet_Ioc hv.integrableOn hv.integrableOn]
    abel
  rw [hsplit]
  refine (norm_setIntegral_le _ v).trans ?_
  refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (norm_nonneg _)
  have : (horizonMeasure T).real (Ioc r s) ≤ volume.real (Ioc r s) := by
    refine ENNReal.toReal_mono measure_Ioc_lt_top.ne (Measure.restrict_apply_le _ _)
  simpa [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 hrs)] using this

variable (T)

/-- The primitive path `t ↦ i + ∫₀ᵗ v` on the control horizon.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.1). -/
noncomputable def primitivePath (i : E) (v : Lp E 2 (horizonMeasure T)) (t : ControlTime T) : E :=
  i + primitiveValue T t v

variable {T}

/-- `√`-Hölder bound for the primitive path on the horizon. -/
theorem dist_primitivePath_le (i : E) (v : Lp E 2 (horizonMeasure T)) (r s : ControlTime T) :
    dist (primitivePath T i v r) (primitivePath T i v s) ≤ Real.sqrt (dist r s) * ‖v‖ := by
  have key : ∀ r s : ControlTime T, (r : ℝ) ≤ s →
      dist (primitivePath T i v r) (primitivePath T i v s) ≤ Real.sqrt (dist r s) * ‖v‖ := by
    intro r s hrs
    have h := norm_primitiveValue_sub_le v r.2.1 hrs
    rw [dist_eq_norm, norm_sub_rev, primitivePath, primitivePath, add_sub_add_left_eq_sub]
    have hd : dist r s = s - r := by
      rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hrs)]
    rwa [hd]
  rcases le_total (r : ℝ) s with h | h
  · exact key r s h
  · rw [dist_comm, dist_comm r s]
    exact key s r h

/-- **Equicontinuity of the primitives on norm-bounded sets of velocities**: the `√`-Hölder
modulus is uniform over `‖v‖ ≤ C`.  This is the Ascoli hypothesis (book Lemma 11.3.5 / M1).

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.5. -/
theorem uniformEquicontinuous_primitivePath {ι : Type*} (i : E) (ψ : ι → Lp E 2 (horizonMeasure T))
    {C : ℝ} (hC : ∀ j, ‖ψ j‖ ≤ C) :
    UniformEquicontinuous fun j : ι => primitivePath T i (ψ j) := by
  have hC0 : ∀ j, 0 ≤ C := fun j => (norm_nonneg _).trans (hC j)
  rw [Metric.uniformEquicontinuous_iff]
  intro ε hε
  have hCp : 0 < |C| + 1 := by positivity
  refine ⟨(ε / (|C| + 1)) ^ 2, by positivity, ?_⟩
  intro r s hrs j
  have hb : 0 < ε / (|C| + 1) := by positivity
  have hsqrt_lt : Real.sqrt (dist r s) < ε / (|C| + 1) := by
    rw [← Real.sqrt_sq hb.le]
    exact (Real.sqrt_lt_sqrt_iff dist_nonneg).2 hrs
  have hle := dist_primitivePath_le i (ψ j) r s
  have hn : ‖ψ j‖ ≤ |C| := (hC j).trans (le_abs_self C)
  have hn0 := norm_nonneg (ψ j)
  calc dist (primitivePath T i (ψ j) r) (primitivePath T i (ψ j) s)
      ≤ Real.sqrt (dist r s) * ‖ψ j‖ := hle
    _ ≤ Real.sqrt (dist r s) * |C| := mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _)
    _ ≤ (ε / (|C| + 1)) * |C| := by
        exact mul_le_mul_of_nonneg_right hsqrt_lt.le (abs_nonneg _)
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hCp]
        nlinarith [abs_nonneg C]

/-- Each primitive path is continuous on the horizon. -/
theorem continuous_primitivePath (i : E) (v : Lp E 2 (horizonMeasure T)) :
    Continuous (primitivePath T i v) :=
  (uniformEquicontinuous_primitivePath (T := T) i (fun _ : Unit => v)
    (C := ‖v‖) fun _ => le_rfl).equicontinuous.continuous ()

variable (T)

/-- The primitive path packaged as a bounded continuous function on the compact horizon.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), (11.3.1). -/
noncomputable def primitiveBoundedPath (i : E) (v : Lp E 2 (horizonMeasure T)) :
    ControlTime T →ᵇ E :=
  BoundedContinuousFunction.mkOfCompact ⟨primitivePath T i v, continuous_primitivePath i v⟩

variable {T}

@[simp] theorem primitiveBoundedPath_apply (i : E) (v : Lp E 2 (horizonMeasure T))
    (t : ControlTime T) : primitiveBoundedPath T i v t = i + primitiveValue T t v := rfl

/-- **Pointwise weak continuity of the primitive** (the `∫₀ᵗ` functional is weakly
continuous because `E` is finite dimensional). -/
theorem continuous_primitivePath_weakSpace (i : E) (t : ControlTime T) :
    Continuous fun x : WeakSpace ℝ (Lp E 2 (horizonMeasure T)) =>
      primitivePath T i ((toWeakSpace ℝ _).symm x) t :=
  continuous_const.add (continuous_comp_weakSpace_of_finiteDimensional
    (X := Lp E 2 (horizonMeasure T)) (primitiveValue T t))

/-- **KEY LEMMA 1: weak-to-uniform continuity of the primitive.**  On every norm-bounded set
`S ⊆ L²(0,T; E)` of velocities, the map `v ↦ (t ↦ i + ∫₀ᵗ v) ∈ C(horizon, E)` (sup norm) is
continuous for the *weak* topology on `S`.  Pointwise weak continuity is
`continuous_primitivePath_weakSpace`; the upgrade to uniform convergence uses the equicontinuity
`uniformEquicontinuous_primitivePath` and Mathlib's
`Equicontinuous.tendsto_uniformFun_iff_pi`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.4 and (11.3.6). -/
theorem continuousOn_primitiveBoundedPath_weakSpace (i : E) {C : ℝ}
    (S : Set (Lp E 2 (horizonMeasure T))) (hS : ∀ v ∈ S, ‖v‖ ≤ C) :
    ContinuousOn (fun x : WeakSpace ℝ (Lp E 2 (horizonMeasure T)) =>
      primitiveBoundedPath T i ((toWeakSpace ℝ _).symm x)) (toWeakSpace ℝ _ '' S) := by
  rw [continuousOn_iff_continuous_domRestrict]
  let ψ : (toWeakSpace ℝ (Lp E 2 (horizonMeasure T)) '' S) → Lp E 2 (horizonMeasure T) :=
    fun y => (toWeakSpace ℝ _).symm y.1
  have hψ : ∀ y, ‖ψ y‖ ≤ C := by
    rintro ⟨_, v, hv, rfl⟩
    simpa [ψ] using hS v hv
  have heq : Equicontinuous fun y => primitivePath T i (ψ y) :=
    (uniformEquicontinuous_primitivePath i ψ hψ).equicontinuous
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  change Tendsto _ (𝓝 y₀) _
  rw [BoundedContinuousFunction.tendsto_iff_tendstoUniformly]
  have hpt : Tendsto (fun y => primitivePath T i (ψ y)) (𝓝 y₀) (𝓝 (primitivePath T i (ψ y₀))) :=
    tendsto_pi_nhds.2 fun t =>
      ((continuous_primitivePath_weakSpace i t).comp continuous_subtype_val).continuousAt
  exact UniformFun.tendsto_iff_tendstoUniformly.1
    ((heq.tendsto_uniformFun_iff_pi (𝓝 y₀) (primitivePath T i (ψ y₀))).2 hpt)

/-- The primitive path with initial value `i` is the constant path `i` plus the primitive from
zero. -/
theorem primitiveBoundedPath_eq_const_add (i : E) (v : Lp E 2 (horizonMeasure T)) :
    primitiveBoundedPath T i v =
      BoundedContinuousFunction.const (ControlTime T) i + primitiveBoundedPath T 0 v := by
  ext t
  simp

/-- **Joint weak-to-uniform continuity in the initial value and the velocity.**  On
`E × S` (`S` norm-bounded) the map `(i, v) ↦ (t ↦ i + ∫₀ᵗ v)` is continuous for the norm
topology on `E` and the weak topology on `S`.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.4 and (11.3.6). -/
theorem continuousOn_primitiveBoundedPath_weakSpace_prod {C : ℝ}
    (S : Set (Lp E 2 (horizonMeasure T))) (hS : ∀ v ∈ S, ‖v‖ ≤ C) :
    ContinuousOn (fun p : E × WeakSpace ℝ (Lp E 2 (horizonMeasure T)) =>
      primitiveBoundedPath T p.1 ((toWeakSpace ℝ _).symm p.2))
      (univ ×ˢ (toWeakSpace ℝ _ '' S)) := by
  have hconst : Continuous fun i : E => BoundedContinuousFunction.const (ControlTime T) i :=
    (LipschitzWith.of_dist_le_mul (K := 1) fun a b => by
      rw [NNReal.coe_one, one_mul]
      exact (BoundedContinuousFunction.dist_le dist_nonneg).2 fun _ => le_rfl).continuous
  have h0 := continuousOn_primitiveBoundedPath_weakSpace (T := T) (0 : E) S hS
  have hfun : (fun p : E × WeakSpace ℝ (Lp E 2 (horizonMeasure T)) =>
      primitiveBoundedPath T p.1 ((toWeakSpace ℝ _).symm p.2)) = fun p =>
      BoundedContinuousFunction.const (ControlTime T) p.1 +
        primitiveBoundedPath T 0 ((toWeakSpace ℝ _).symm p.2) :=
    funext fun p => primitiveBoundedPath_eq_const_add _ _
  rw [hfun]
  exact (hconst.comp continuous_fst).continuousOn.add
    (h0.comp continuous_snd.continuousOn (fun p hp => hp.2))

/-- **Residue 3: weak closedness of a pointwise state constraint.**  If each slice
`G t` is continuous, `{v | ∀ t, G t (i + ∫₀ᵗ v) ≤ 0}` is closed in the weak topology; only
pointwise weak continuity of the primitive is used.

Book citation: Berkovitz & Medhin, *Nonlinear Optimal Control Theory*
(CRC 2012), Lemma 11.3.4 (state constraint set). -/
theorem isClosed_stateConstraint_weakSpace (i : E) (G : ControlTime T → E → ℝ)
    (hG : ∀ t, Continuous (G t)) :
    IsClosed {x : WeakSpace ℝ (Lp E 2 (horizonMeasure T)) |
      ∀ t, G t (primitivePath T i ((toWeakSpace ℝ _).symm x) t) ≤ 0} := by
  simp only [ofPred_forall]
  exact isClosed_iInter fun t =>
    isClosed_le ((hG t).comp (continuous_primitivePath_weakSpace i t)) continuous_const

end Primitive

end OptimalControl.BoundedState
