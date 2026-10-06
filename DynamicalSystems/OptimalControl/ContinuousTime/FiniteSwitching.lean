/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.OptimalControl.ContinuousTime.LinearSwitching
public import DynamicalSystems.OptimalControl.ContinuousTime.TimeOptimal
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Finite switching of nondegenerate linear box extremals

`HasFiniteSwitchesOn` says that there is a finite exceptional set and the
control is constant on every interval avoiding that set. Values at switching
instants are not prescribed. For a merely almost-everywhere Hamiltonian law the
correct conclusion is an **AE-equivalent** finite-switch representative; an
arbitrary representative can have infinitely many null-set modifications.

The analytic and per-input rank hypotheses are discharged for LTI switching
functions in `LinearSwitching`. Here the intermediate value theorem and the
existing box-minimizer theorem connect those functions to the actual control.
This is a structure theorem for PMP extremals, not a new necessity theorem.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped Interval

namespace OptimalControl

/-- A control has finitely many switches when it is constant on every closed
interval avoiding one finite exceptional set. This is a partition statement,
not merely a bound on zeros of an auxiliary function. Values at the finitely
many switching instants may be chosen independently. -/
def HasFiniteSwitchesOn {U : Type*} (u : ℝ → U) (a b : ℝ) : Prop :=
  ∃ S : Set ℝ, S.Finite ∧ S ⊆ Icc a b ∧
    ∀ r s, r ∈ Icc a b → s ∈ Icc a b →
      (∀ t ∈ uIcc r s, t ∉ S) → u r = u s

/-- The invariant notion for controls considered modulo equality almost
 everywhere. No assertion is made about an arbitrary pointwise representative. -/
def HasAEFiniteSwitchesOn {U : Type*} (u : ℝ → U) (a b : ℝ) : Prop :=
  ∃ v : ℝ → U, HasFiniteSwitchesOn v a b ∧
    u =ᵐ[volume.restrict (Icc a b)] v

/-- Finite modifications preserve the finite-switch property. -/
theorem HasFiniteSwitchesOn.congr_off_finite {U : Type*} {u v : ℝ → U} {a b : ℝ}
    (hv : HasFiniteSwitchesOn v a b) {D : Set ℝ} (hD : D.Finite)
    (hDsub : D ⊆ Icc a b)
    (heq : ∀ t ∈ Icc a b, t ∉ D → u t = v t) : HasFiniteSwitchesOn u a b := by
  obtain ⟨S, hS, hSsub, hconst⟩ := hv
  refine ⟨S ∪ D, hS.union hD, union_subset hSsub hDsub, ?_⟩
  intro r s hr hs havoid
  rw [heq r hr (fun h => havoid r left_mem_uIcc (Or.inr h)),
    heq s hs (fun h => havoid s right_mem_uIcc (Or.inr h))]
  exact hconst r s hr hs (fun t ht h => havoid t ht (Or.inl h))

/-- A continuous real-valued function that does not vanish between two times
has the same sign at those times. -/
theorem sign_eq_of_continuousOn_no_zero {f : ℝ → ℝ} {r s : ℝ}
    (hf : ContinuousOn f (uIcc r s)) (hn : ∀ t ∈ uIcc r s, f t ≠ 0) :
    Real.sign (f r) = Real.sign (f s) := by
  have hr := hn r left_mem_uIcc
  have hs := hn s right_mem_uIcc
  have hno : ¬ (0 : ℝ) ∈ uIcc (f r) (f s) := by
    intro h
    obtain ⟨t, ht, hft⟩ := intermediate_value_uIcc hf h
    exact hn t ht hft
  rcases lt_or_gt_of_ne hr with hr | hr <;> rcases lt_or_gt_of_ne hs with hs | hs
  · simp [Real.sign_of_neg hr, Real.sign_of_neg hs]
  · exact (hno (mem_uIcc.mpr (Or.inl ⟨hr.le, hs.le⟩))).elim
  · exact (hno (mem_uIcc.mpr (Or.inr ⟨hs.le, hr.le⟩))).elim
  · simp [Real.sign_of_pos hr, Real.sign_of_pos hs]

variable {ι : Type*} [Fintype ι]

/-- Canonical minimizing sign representative. Its value at a zero coefficient
is zero, which remains in the unit box; the zero times will form a finite set. -/
noncomputable def bangBangSelector (σ : ι → ℝ → ℝ) (t : ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => -Real.sign (σ i t))

omit [Fintype ι] in
@[simp] theorem bangBangSelector_apply (σ : ι → ℝ → ℝ) (t : ℝ) (i : ι) :
    bangBangSelector σ t i = -Real.sign (σ i t) := rfl

/-- A finite family of nontrivial analytic coefficients determines a
finite-switch control, constant on every interval avoiding their zeros. -/
theorem hasFiniteSwitchesOn_bangBangSelector (σ : ι → ℝ → ℝ)
    (ha : ∀ i, AnalyticOnNhd ℝ (σ i) univ) (hn : ∀ i, ∃ t, σ i t ≠ 0) (a b : ℝ) :
    HasFiniteSwitchesOn (bangBangSelector σ) a b := by
  let S : Set ℝ := {t | t ∈ Icc a b ∧ ∃ i, σ i t = 0}
  have hS : S.Finite := by
    have h := Set.finite_iUnion (fun i => (ha i).finite_zeroSet_Icc (hn i) a b)
    convert h using 1
    ext t
    simp only [S, mem_ofPred_eq, mem_iUnion]
    aesop
  refine ⟨S, hS, fun _ ht => ht.1, ?_⟩
  intro r s hr hs havoid
  ext i
  simp only [bangBangSelector_apply]
  congr 1
  apply sign_eq_of_continuousOn_no_zero ((ha i).continuous.continuousOn)
  intro t ht hz
  exact havoid t ht ⟨uIcc_subset_Icc hr hs ht, i, hz⟩

/-- If a box control minimizes a nondegenerate analytic linear Hamiltonian at
 every time, it has finitely many switches. -/
theorem hasFiniteSwitchesOn_of_analytic_box_minimizing
    (c u : ℝ → EuclideanSpace ℝ ι) (a b : ℝ)
    (ha : ∀ i, AnalyticOnNhd ℝ (fun t => c t i) univ)
    (hn : ∀ i, ∃ t, c t i ≠ 0)
    (hu : ∀ t ∈ Icc a b, u t ∈ unitBox ι)
    (hmin : ∀ t ∈ Icc a b, ∀ w ∈ unitBox ι, inner ℝ (c t) (u t) ≤ inner ℝ (c t) w) :
    HasFiniteSwitchesOn u a b := by
  let S : Set ℝ := {t | t ∈ Icc a b ∧ ∃ i, c t i = 0}
  have hS : S.Finite := by
    have h := Set.finite_iUnion (fun i => (ha i).finite_zeroSet_Icc (hn i) a b)
    convert h using 1
    ext t
    simp only [S, mem_ofPred_eq, mem_iUnion]
    aesop
  apply (hasFiniteSwitchesOn_bangBangSelector (fun i t => c t i) ha hn a b).congr_off_finite
    hS (fun _ ht => ht.1)
  intro t ht hnot
  ext i
  have hi : c t i ≠ 0 := fun hz => hnot ⟨ht, i, hz⟩
  exact (linearMinimizer_bangBang (c t) (u t) (hu t ht) (hmin t ht)).2.1 i hi

/-- The AE Hamiltonian law gives an AE-equivalent finite-switch representative,
not pointwise regularity of the original control. -/
theorem hasAEFiniteSwitchesOn_of_analytic_box_minimizing
    (c u : ℝ → EuclideanSpace ℝ ι) (a b : ℝ)
    (ha : ∀ i, AnalyticOnNhd ℝ (fun t => c t i) univ)
    (hn : ∀ i, ∃ t, c t i ≠ 0)
    (hu : ∀ᵐ t ∂volume.restrict (Icc a b), u t ∈ unitBox ι)
    (hmin : ∀ᵐ t ∂volume.restrict (Icc a b),
      ∀ w ∈ unitBox ι, inner ℝ (c t) (u t) ≤ inner ℝ (c t) w) :
    HasAEFiniteSwitchesOn u a b := by
  refine ⟨bangBangSelector (fun i t => c t i),
    hasFiniteSwitchesOn_bangBangSelector _ ha hn a b, ?_⟩
  have hnAE : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ i, c t i ≠ 0 := by
    apply ae_all_iff.mpr
    intro i
    have hz := ((ha i).finite_zeroSet_Icc (hn i) a b).countable.ae_notMem
      (volume.restrict (Icc a b))
    filter_upwards [hz, ae_restrict_mem measurableSet_Icc] with t ht hmem
    exact fun heq => ht ⟨hmem, heq⟩
  filter_upwards [hu, hmin, hnAE] with t hut hmint hnt
  ext i
  exact (linearMinimizer_bangBang (c t) (u t) hut hmint).2.1 i (hnt i)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Switching coefficients assembled as a Euclidean control-space vector. -/
noncomputable def linearSwitchingVector (A : E →L[ℝ] E) (q : E →L[ℝ] ℝ)
    (b : ι → E) (T t : ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => linearSwitchingFunction A q (b i) T t)

omit [FiniteDimensional ℝ E] in
/-- The linear Hamiltonian input term is exactly the dot product with the
switching vector. Thus the box-minimization hypothesis below is about the
actual input map, not a separately supplied sign rule. -/
theorem terminalAdjointCovector_input_sum (A : E →L[ℝ] E) (q : E →L[ℝ] ℝ)
    (b : ι → E) (T t : ℝ) (w : EuclideanSpace ℝ ι) :
    terminalAdjointCovector A q T t (∑ i, w i • b i) =
      inner ℝ (linearSwitchingVector A q b T t) w := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, linearSwitchingVector,
    map_sum, map_smul]

/-- **Finite switching of a nondegenerate LTI box extremal.** Per-input finite
Krylov spanning and a nonzero terminal covector replace any assumed
finite-zero/nonvanishing property. Normal and abnormal cost multipliers do not
enter this homogeneous-adjoint structure theorem. -/
theorem hasFiniteSwitchesOn_of_linear_box_minimizing
    (A : E →L[ℝ] E) (q : E →L[ℝ] ℝ) (b : ι → E) (T : ℝ)
    (hb : ∀ i, CyclicInput A (b i)) (hq : q ≠ 0)
    (u : ℝ → EuclideanSpace ℝ ι) (hu : ∀ t ∈ Icc 0 T, u t ∈ unitBox ι)
    (hmin : ∀ t ∈ Icc 0 T, ∀ w ∈ unitBox ι,
      terminalAdjointCovector A q T t (∑ i, u t i • b i) ≤
        terminalAdjointCovector A q T t (∑ i, w i • b i)) :
    HasFiniteSwitchesOn u 0 T := by
  apply hasFiniteSwitchesOn_of_analytic_box_minimizing (linearSwitchingVector A q b T) u 0 T
    (fun i => analytic_linearSwitchingFunction A q (b i) T)
    (fun i => exists_ne_zero_linearSwitchingFunction A q (b i) T (hb i) hq) hu
  intro t ht w hw
  simpa only [terminalAdjointCovector_input_sum] using hmin t ht w hw

/-- AE version of the LTI finite-switch theorem. -/
theorem hasAEFiniteSwitchesOn_of_linear_box_minimizing
    (A : E →L[ℝ] E) (q : E →L[ℝ] ℝ) (b : ι → E) (T : ℝ)
    (hb : ∀ i, CyclicInput A (b i)) (hq : q ≠ 0)
    (u : ℝ → EuclideanSpace ℝ ι)
    (hu : ∀ᵐ t ∂volume.restrict (Icc 0 T), u t ∈ unitBox ι)
    (hmin : ∀ᵐ t ∂volume.restrict (Icc 0 T), ∀ w ∈ unitBox ι,
      terminalAdjointCovector A q T t (∑ i, u t i • b i) ≤
        terminalAdjointCovector A q T t (∑ i, w i • b i)) :
    HasAEFiniteSwitchesOn u 0 T := by
  apply hasAEFiniteSwitchesOn_of_analytic_box_minimizing (linearSwitchingVector A q b T) u 0 T
    (fun i => analytic_linearSwitchingFunction A q (b i) T)
    (fun i => exists_ne_zero_linearSwitchingFunction A q (b i) T (hb i) hq) hu
  filter_upwards [hmin] with t ht w hw
  simpa only [terminalAdjointCovector_input_sum] using ht w hw

end OptimalControl
