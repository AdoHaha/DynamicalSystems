/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Mathlib.Analysis.Convex.AbnormalSeparation
public import DynamicalSystems.OptimalControl.ContinuousTime.MeasurableHamiltonian
public import Mathlib.Analysis.Convex.Function
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Tactic.Linarith
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Tactic.Abel

/-!
# Necessary endpoint multipliers, including the abnormal case

Convexity of the primal candidate set and objective, and affinity of the endpoint map,
produce a nontrivial endpoint/cost multiplier from actual fixed-endpoint optimality.
The cost multiplier is nonnegative, and is never assumed positive or divided out.
-/

@[expose] public section

open Set MeasureTheory TopologicalSpace
namespace OptimalControl

variable {X E : Type*} [AddCommGroup X] [Module ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Actual convex fixed-endpoint optimality yields nontrivial endpoint and cost multipliers.
Affinity is needed only on the candidate domain. No multiplier, supporting cone, or
Lagrangian inequality is supplied as a hypothesis. -/
theorem exists_endpoint_multipliers
    (S : Set X) (J : X → ℝ) (F : X → E) (xStar : X)
    (hJ : ConvexOn ℝ S J)
    (hF : ∀ x ∈ S, ∀ y ∈ S, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      F (a • x + b • y) = a • F x + b • F y)
    (hxStar : xStar ∈ S)
    (hopt : ∀ x ∈ S, F x = F xStar → J xStar ≤ J x) :
    ∃ (q : E →L[ℝ] ℝ) (α : ℝ), 0 ≤ α ∧ (q ≠ 0 ∨ α ≠ 0) ∧
      ∀ x ∈ S, 0 ≤ q (F x - F xStar) + α * (J x - J xStar) := by
  let C : Set (E × ℝ) := {z | ∃ x ∈ S, z.1 = F x - F xStar ∧ J x - J xStar ≤ z.2}
  have hC : Convex ℝ C := by
    rintro p ⟨x, hx, hxp, hjx⟩ z ⟨y, hy, hyz, hjy⟩ a b ha hb hab
    refine ⟨a • x + b • y, hJ.1 hx hy ha hb hab, ?_, ?_⟩
    · change a • p.1 + b • z.1 = F (a • x + b • y) - F xStar
      rw [hF x hx y hy a b ha hb hab, hxp, hyz, smul_sub, smul_sub]
      have hbase : a • F xStar + b • F xStar = F xStar := by
        rw [← add_smul, hab, one_smul]
      conv_rhs => rw [← hbase]
      abel
    · change J (a • x + b • y) - J xStar ≤ a * p.2 + b * z.2
      have hj := hJ.2 hx hy ha hb hab
      simp only [smul_eq_mul] at hj
      have hbase : a * J xStar + b * J xStar = J xStar := by
        rw [← add_mul, hab, one_mul]
      nlinarith [mul_nonneg ha (sub_nonneg.mpr hjx),
        mul_nonneg hb (sub_nonneg.mpr hjy)]
  have hzero : (0 : E × ℝ) ∈ C := ⟨xStar, hxStar, by simp, by simp⟩
  have hboundary : (0 : E × ℝ) ∉ interior C := by
    intro hz
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
    have hp : ((0 : E), -(ε / 2)) ∈ Metric.ball 0 ε := by
      rw [Metric.mem_ball, dist_zero_right]
      change max ‖(0 : E)‖ ‖-(ε / 2)‖ < ε
      rw [norm_zero, norm_neg, Real.norm_of_nonneg (half_pos hε).le]
      exact max_lt_iff.mpr ⟨hε, by linarith⟩
    obtain ⟨x, hx, hFx, hJx⟩ := hball hp
    have hFxeq : F x = F xStar := sub_eq_zero.mp hFx.symm
    have hm := hopt x hx hFxeq
    change J x - J xStar ≤ -(ε / 2) at hJx
    linarith
  obtain ⟨ell, hell, hnonneg⟩ := exists_nonzero_supporting_covector C hC hzero hboundary
  let q : E →L[ℝ] ℝ := ell.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let α : ℝ := ell (0, 1)
  have hsplit (y : E) (r : ℝ) : ell (y, r) = q y + α * r := by
    have heq : (y, r) = (y, 0) + r • ((0, 1) : E × ℝ) := by ext <;> simp
    rw [heq, map_add, map_smul]
    change ell (y, 0) + r * ell (0, 1) = ell (y, 0) + ell (0, 1) * r
    rw [mul_comm r]
  have hα : 0 ≤ α := hnonneg (0, 1) ⟨xStar, hxStar, by simp, by simp⟩
  have hne : q ≠ 0 ∨ α ≠ 0 := by
    by_cases hq : q = 0
    · right
      intro hαzero
      apply hell
      apply ContinuousLinearMap.ext
      intro p
      obtain ⟨y, r⟩ := p
      change ell (y, r) = 0
      rw [hsplit, hq, hαzero]
      simp
    · exact Or.inl hq
  refine ⟨q, α, hα, hne, ?_⟩
  intro x hx
  rw [← hsplit]
  exact hnonneg _ ⟨x, hx, rfl, le_rfl⟩

section IntegralControls

variable {Ω W : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
  [BorelSpace W] [SecondCountableTopology W]
  {μ : Measure Ω}

/-- Necessary measurable Hamiltonian minimum for a convex endpoint-integral problem.
The endpoint is the actual integral of the linear response kernel `K`; the objective is the
actual integral of the convex running cost `L`. Integrability is assumed for admissible
controls, but neither multipliers nor an augmented integral minimum are supplied.
The endpoint constraint may be degenerate and the cost multiplier may vanish. -/
theorem exists_ae_hamiltonian_endpoint_multipliers
    (U : Set W) (hU : Convex ℝ U)
    (K : Ω → W →L[ℝ] E) (L : Ω → W → ℝ) (uStar : Ω → W)
    (huStar : Measurable uStar) (hmem : ∀ t, uStar t ∈ U)
    (hKint : ∀ v : Ω → W, Measurable v → (∀ t, v t ∈ U) →
      Integrable (fun t ↦ K t (v t)) μ)
    (hLint : ∀ v : Ω → W, Measurable v → (∀ t, v t ∈ U) →
      Integrable (fun t ↦ L t (v t)) μ)
    (hLconv : ∀ t, ConvexOn ℝ U (L t))
    (hLcont : ∀ᵐ t ∂μ, ContinuousOn (L t) U)
    (hopt : ∀ v : Ω → W, Measurable v → (∀ t, v t ∈ U) →
      (∫ t, K t (v t) ∂μ) = (∫ t, K t (uStar t) ∂μ) →
      (∫ t, L t (uStar t) ∂μ) ≤ ∫ t, L t (v t) ∂μ) :
    ∃ (q : E →L[ℝ] ℝ) (α : ℝ), 0 ≤ α ∧ (q ≠ 0 ∨ α ≠ 0) ∧
      ∀ᵐ t ∂μ, ∀ w ∈ U,
        α * L t (uStar t) + q (K t (uStar t)) ≤ α * L t w + q (K t w) := by
  let S : Set (Ω → W) := {v | Measurable v ∧ ∀ t, v t ∈ U}
  let J : (Ω → W) → ℝ := fun v ↦ ∫ t, L t (v t) ∂μ
  let F : (Ω → W) → E := fun v ↦ ∫ t, K t (v t) ∂μ
  have hSc : Convex ℝ S := by
    intro v hv w hw a b ha hb hab
    exact ⟨(hv.1.const_smul a).add (hw.1.const_smul b),
      fun t ↦ hU (hv.2 t) (hw.2 t) ha hb hab⟩
  have hJ : ConvexOn ℝ S J := by
    refine ⟨hSc, ?_⟩
    intro v hv w hw a b ha hb hab
    change (∫ t, L t (a • v t + b • w t) ∂μ) ≤ a * J v + b * J w
    have hz := hSc hv hw ha hb hab
    calc
      _ ≤ ∫ t, a * L t (v t) + b * L t (w t) ∂μ :=
        integral_mono (hLint _ hz.1 hz.2)
          (((hLint v hv.1 hv.2).const_mul a).add ((hLint w hw.1 hw.2).const_mul b))
          (fun t ↦ (hLconv t).2 (hv.2 t) (hw.2 t) ha hb hab)
      _ = _ := by rw [integral_add ((hLint v hv.1 hv.2).const_mul a)
          ((hLint w hw.1 hw.2).const_mul b), integral_const_mul, integral_const_mul]
  have hF : ∀ v ∈ S, ∀ w ∈ S, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      F (a • v + b • w) = a • F v + b • F w := by
    intro v hv w hw a b _ _ _
    change (∫ t, K t (a • v t + b • w t) ∂μ) = a • F v + b • F w
    simp_rw [map_add, map_smul]
    have he := integral_add ((hKint v hv.1 hv.2).smul a) ((hKint w hw.1 hw.2).smul b)
    simp only [Pi.smul_apply] at he
    rw [he, integral_smul, integral_smul]
  obtain ⟨q, α, hα, hne, hlag⟩ := exists_endpoint_multipliers S J F uStar hJ hF
    ⟨huStar, hmem⟩ (fun v hv ↦ hopt v hv.1 hv.2)
  let H : Ω → U → ℝ := fun t w ↦ α * L t w + q (K t w)
  let us : Ω → U := fun t ↦ ⟨uStar t, hmem t⟩
  have hHi (v : Ω → U) (hv : Measurable v) : Integrable (fun t ↦ H t (v t)) μ := by
    exact ((hLint _ (measurable_subtype_coe.comp hv) (fun t ↦ (v t).property)).const_mul α).add
      (q.integrable_comp (hKint _ (measurable_subtype_coe.comp hv) (fun t ↦ (v t).property)))
  have hHformula (v : Ω → U) (hv : Measurable v) :
      (∫ t, H t (v t) ∂μ) = α * J (fun t ↦ (v t).val) + q (F (fun t ↦ (v t).val)) := by
    change (∫ t, α * L t (v t).val + q (K t (v t).val) ∂μ) = _
    have he := integral_add
      ((hLint _ (measurable_subtype_coe.comp hv) (fun t ↦ (v t).property)).const_mul α)
      (q.integrable_comp (hKint _ (measurable_subtype_coe.comp hv) (fun t ↦ (v t).property)))
    simp only [Function.comp_apply] at he
    have hk : Integrable (fun t ↦ K t (v t).val) μ :=
      hKint _ (measurable_subtype_coe.comp hv) (fun t ↦ (v t).property)
    rw [he, integral_const_mul, q.integral_comp_comm hk]
  have hus : Measurable us := huStar.subtype_mk
  have hHmin : ∀ v : Ω → U, Measurable v →
      (∫ t, H t (us t) ∂μ) ≤ ∫ t, H t (v t) ∂μ := by
    intro v hv
    rw [hHformula us hus, hHformula v hv]
    have hm := hlag (fun t ↦ (v t).val)
      ⟨measurable_subtype_coe.comp hv, fun t ↦ (v t).property⟩
    rw [map_sub] at hm
    change 0 ≤ q (F (fun t ↦ (v t).val)) - q (F uStar) +
      α * (J (fun t ↦ (v t).val) - J uStar) at hm
    change α * J uStar + q (F uStar) ≤ _
    linarith
  have hHcont : ∀ᵐ t ∂μ, Continuous (H t) := by
    filter_upwards [hLcont] with t ht
    exact (continuous_const.mul (continuousOn_iff_continuous_domRestrict.mp ht)).add
      (q.continuous.comp ((K t).continuous.comp continuous_subtype_val))
  have ha := ae_hamiltonian_minimizing_of_integral_minimizing H us hus (hHi us hus)
    (fun w ↦ hHi (fun _ ↦ w) measurable_const) hHcont hHmin
  refine ⟨q, α, hα, hne, ?_⟩
  filter_upwards [ha] with t ht
  intro w hw
  exact ht ⟨w, hw⟩

end IntegralControls

end OptimalControl
