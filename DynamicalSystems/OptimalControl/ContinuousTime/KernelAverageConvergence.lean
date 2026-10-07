/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.RelaxedKernelDistance
public import DynamicalSystems.OptimalControl.ContinuousTime.VelocityPointwiseBoundaryPositivity

/-!
# Convergence of control-averaged data under the kernel-wise control distance

Berkovitz & Medhin, *Nonlinear Optimal Control Theory* (CRC 2012), §11.4: as `ε → 0`,
`‖ν^ε − ν₀‖_L ≤ ε` makes the control-averaged data `∫ g(t,y,u) dν^ε_t(u)` converge in `L¹(0,T)`
to the data of `ν₀`.

* `Problem.tendsto_integral_norm_kernelAverage_sub`: for a jointly continuous integrand
  `g(t,y,u)` (e.g. `f`, `f⁰`, `fₓ`, `f⁰ₓ`), uniformly convergent paths `x_k → x₀` and relaxed
  controls `ρ_k → ρ₀` in the kernel-wise distance,
  `∫₀ᵀ ‖∫ g(t,x_k(t),u) dρ_k,t − ∫ g(t,x₀(t),u) dρ₀,t‖ dt → 0`.

Book citations live in docstrings only.
-/

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology Interval

namespace OptimalControl.BoundedState

variable {E V W : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [MeasurableSpace V] [BorelSpace V]

namespace Problem

/-- Vector-valued kernel comparison: two probability measures that differ by at most `ε` on every
measurable set have integrals of a strongly measurable integrand bounded by `C` differing in norm by
at most `2 ε C` (dual-vector reduction to the real layer-cake bound). -/
theorem norm_integral_sub_le_of_forall_abs_measureReal_sub_le {α : Type*} [MeasurableSpace α]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    (μ μ' : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] {ε C : ℝ}
    (h : ∀ B : Set α, MeasurableSet B → |μ.real B - μ'.real B| ≤ ε) {f : α → Z}
    (hf : StronglyMeasurable f) (hC : ∀ u, ‖f u‖ ≤ C) (hC0 : 0 ≤ C) :
    ‖∫ u, f u ∂μ - ∫ u, f u ∂μ'‖ ≤ 2 * ε * C := by
  obtain ⟨ℓ, hℓ, hℓv⟩ := exists_dual_vector'' ℝ (∫ u, f u ∂μ - ∫ u, f u ∂μ')
  have hfi : ∀ m : Measure α, IsFiniteMeasure m → Integrable f m := fun m _ =>
    Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall hC)
  have hℓf : Measurable fun u => ℓ (f u) := (ℓ.continuous.comp_stronglyMeasurable hf).measurable
  have hℓC : ∀ u, |ℓ (f u)| ≤ C := fun u => by
    rw [← Real.norm_eq_abs]
    calc ‖ℓ (f u)‖ ≤ ‖ℓ‖ * ‖f u‖ := ℓ.le_opNorm _
      _ ≤ 1 * C := mul_le_mul hℓ (hC u) (norm_nonneg _) zero_le_one
      _ = C := one_mul C
  have hreal := RelaxedControl.abs_integral_sub_le_of_forall_abs_measureReal_sub_le μ μ' h hℓf
    hℓC hC0
  rw [ℓ.integral_comp_comm (hfi μ inferInstance), ℓ.integral_comp_comm (hfi μ' inferInstance),
    ← map_sub, hℓv] at hreal
  simpa using hreal

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
/-- A path-composed integrand averaged against a relaxed kernel is strongly measurable in time. -/
theorem stronglyMeasurable_kernelAverage_path (P : Problem E V W)
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (g : P.Time → E → V → Z)
    (hg : Continuous fun z : (P.Time × E) × V => g z.1.1 z.1.2 z.2)
    (y : P.Trajectory) (ρ : P.Relaxed) :
    StronglyMeasurable (fun t : P.Time => ∫ u : P.Control, g t (y t) (u : V) ∂ρ.kernel t) := by
  have hc : Continuous fun p : P.Time × P.Control => g p.1 (y p.1) (p.2 : V) :=
    hg.comp ((continuous_fst.prodMk (y.continuous.comp continuous_fst)).prodMk
      (continuous_subtype_val.comp continuous_snd))
  exact RelaxedControl.stronglyMeasurable_average ρ
    (f := fun p : P.Time × P.Control => g p.1 (y p.1) (p.2 : V)) hc.stronglyMeasurable

omit [CompleteSpace E] in
/-- **`L¹` convergence of control-averaged data.** -/
theorem tendsto_integral_norm_kernelAverage_sub (P : Problem E V W)
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
    (g : P.Time → E → V → Z)
    (hg : Continuous fun z : (P.Time × E) × V => g z.1.1 z.1.2 z.2)
    {x : ℕ → P.Trajectory} {x₀ : P.Trajectory} (hx : Tendsto x atTop (nhds x₀))
    {ρ : ℕ → P.Relaxed} {ρ₀ : P.Relaxed}
    (hρ : Tendsto (fun k => relaxedControlDistance P (ρ k) ρ₀) atTop (nhds 0)) :
    (∀ k, Integrable (fun t : P.Time => ‖∫ u : P.Control, g t (x k t) (u : V) ∂(ρ k).kernel t
        - ∫ u : P.Control, g t (x₀ t) (u : V) ∂ρ₀.kernel t‖)
      (horizonProbability P.horizon P.horizon_pos).toMeasure) ∧
    Tendsto (fun k => ∫ t : P.Time, ‖∫ u : P.Control, g t (x k t) (u : V) ∂(ρ k).kernel t
        - ∫ u : P.Control, g t (x₀ t) (u : V) ∂ρ₀.kernel t‖
      ∂(horizonProbability P.horizon P.horizon_pos).toMeasure) atTop (nhds 0) := by
  have : CompleteSpace Z := FiniteDimensional.complete ℝ Z
  set ν := horizonProbability P.horizon P.horizon_pos with hν
  -- a common bound `R` for the paths
  obtain ⟨R₁, hR₁⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto x hx)
  set R : ℝ := max R₁ ‖x₀‖ with hRdef
  have hxR : ∀ k t, ‖x k t‖ ≤ R := fun k t =>
    ((x k).norm_coe_le_norm t).trans ((hR₁ _ ⟨k, rfl⟩).trans (le_max_left _ _))
  have hx₀R : ∀ t, ‖x₀ t‖ ≤ R := fun t => (x₀.norm_coe_le_norm t).trans (le_max_right _ _)
  -- the compact tube and the bound `Cg`
  set K : Set ((P.Time × E) × V) :=
    ((univ : Set P.Time) ×ˢ Metric.closedBall (0 : E) R) ×ˢ P.controlSet with hKdef
  have hK : IsCompact K :=
    (isCompact_univ.prod (isCompact_closedBall (0 : E) R)).prod P.controlSet_compact
  have hmem : ∀ (t : P.Time) (y : E) (u : P.Control), ‖y‖ ≤ R → ((t, y), (u : V)) ∈ K :=
    fun t y u hy => ⟨⟨mem_univ _, Metric.mem_closedBall.mpr (by simpa [dist_eq_norm] using hy)⟩,
      u.2⟩
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  set Cg : ℝ := max C₁ 0 with hCg
  have hCg0 : 0 ≤ Cg := le_max_right _ _
  have hbd : ∀ (t : P.Time) (y : E) (u : P.Control), ‖y‖ ≤ R → ‖g t y (u : V)‖ ≤ Cg :=
    fun t y u hy => (hC₁ _ (hmem t y u hy)).trans (le_max_left _ _)
  -- measurability, integrability and bounds of the averages
  have hcont : ∀ (y : P.Trajectory) (t : P.Time),
      Continuous fun u : P.Control => g t (y t) (u : V) :=
    fun y t => hg.comp (f := fun u : P.Control => ((t, y t), (u : V)))
      (continuous_const.prodMk continuous_subtype_val)
  have hint : ∀ (y : P.Trajectory) (σ : P.Relaxed) (t : P.Time), (∀ s, ‖y s‖ ≤ R) →
      Integrable (fun u : P.Control => g t (y t) (u : V)) (σ.kernel t) := fun y σ t hy =>
    Integrable.of_bound (hcont y t).aestronglyMeasurable Cg
      (Eventually.of_forall fun u => hbd t _ u (hy t))
  have havg : ∀ (y : P.Trajectory) (σ : P.Relaxed) (t : P.Time), (∀ s, ‖y s‖ ≤ R) →
      ‖∫ u : P.Control, g t (y t) (u : V) ∂σ.kernel t‖ ≤ Cg := fun y σ t hy => by
    have := norm_integral_le_of_norm_le_const (μ := σ.kernel t)
      (Eventually.of_forall fun u : P.Control => hbd t _ u (hy t))
    simpa using this
  refine ⟨fun k => ?_, ?_⟩
  · refine Integrable.of_bound (((P.stronglyMeasurable_kernelAverage_path g hg (x k) (ρ k)).sub
      (P.stronglyMeasurable_kernelAverage_path g hg x₀ ρ₀)).norm.aestronglyMeasurable) (Cg + Cg)
      (Eventually.of_forall fun t => ?_)
    rw [norm_norm]
    exact (norm_sub_le _ _).trans (add_le_add (havg _ _ t (hxR k)) (havg _ _ t hx₀R))
  -- uniform continuity on the tube
  have huc := (hK.uniformContinuousOn_of_continuous hg.continuousOn)
  rw [Metric.uniformContinuousOn_iff] at huc
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := huc (ε / 4) (by positivity)
  have hη : 0 < ε / (8 * (Cg + 1)) := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 hx δ hδ).and
    (Metric.tendsto_nhds.1 hρ _ hη))
  refine ⟨N, fun k hk => ?_⟩
  obtain ⟨hxk, hρk⟩ := hN k hk
  set d : ℝ := relaxedControlDistance P (ρ k) ρ₀ with hd
  have hd0 : 0 ≤ d := RelaxedControl.kernelDistance_nonneg _ _
  have hdη : d < ε / (8 * (Cg + 1)) := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hd0] at hρk
    exact hρk
  have hpt : ∀ᵐ t ∂ν.toMeasure, ‖‖∫ u : P.Control, g t (x k t) (u : V) ∂(ρ k).kernel t
      - ∫ u : P.Control, g t (x₀ t) (u : V) ∂ρ₀.kernel t‖‖ ≤ 2 * d * Cg + ε / 4 := by
    filter_upwards [(RelaxedControl.kernelDistance_le_iff_ae (ρ k) ρ₀ hd0).1 le_rfl] with t ht
    rw [norm_norm]
    have hsplit : ∫ u : P.Control, g t (x k t) (u : V) ∂(ρ k).kernel t
        - ∫ u : P.Control, g t (x₀ t) (u : V) ∂ρ₀.kernel t =
        (∫ u : P.Control, g t (x k t) (u : V) ∂(ρ k).kernel t
          - ∫ u : P.Control, g t (x k t) (u : V) ∂ρ₀.kernel t) +
        ∫ u : P.Control, (g t (x k t) (u : V) - g t (x₀ t) (u : V)) ∂ρ₀.kernel t := by
      rw [integral_sub (hint _ _ t (hxR k)) (hint _ _ t hx₀R)]
      abel
    rw [hsplit]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact norm_integral_sub_le_of_forall_abs_measureReal_sub_le _ _ ht
        (hcont (x k) t).stronglyMeasurable (fun u => hbd t _ u (hxR k t)) hCg0
    · have hb : ∀ u : P.Control, ‖g t (x k t) (u : V) - g t (x₀ t) (u : V)‖ ≤ ε / 4 := by
        intro u
        rw [← dist_eq_norm]
        refine (hδε _ (hmem t _ u (hxR k t)) _ (hmem t _ u (hx₀R t)) ?_).le
        have hdt : dist (x k t) (x₀ t) < δ :=
          ((x k).dist_coe_le_dist t).trans_lt hxk
        simpa [Prod.dist_eq] using hdt
      have := norm_integral_le_of_norm_le_const (μ := ρ₀.kernel t) (Eventually.of_forall hb)
      simpa using this
  have hI := norm_integral_le_of_norm_le_const (μ := ν.toMeasure) hpt
  simp only [probReal_univ, mul_one] at hI
  rw [Real.dist_eq, sub_zero]
  have h2 : 2 * d * Cg ≤ ε / 4 := by
    have h3 : d * (8 * (Cg + 1)) < ε := (lt_div_iff₀ (by positivity)).1 hdη
    nlinarith
  calc _ ≤ 2 * d * Cg + ε / 4 := hI
    _ < ε := by linarith

end Problem

end OptimalControl.BoundedState
