/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Measurable selection of a minimiser for a Carathéodory integrand

Let `T` be a measurable space and `U` a compact metric space with its Borel σ-algebra.
For `φ : T → U → ℝ` with `φ t` continuous for every `t` and `φ · u` measurable for every `u`
(a Carathéodory integrand):

* `DynamicalSystems.MeasurableArgmin.measurable_minValue`: the value function
  `t ↦ min_u φ t u` is measurable;
* `DynamicalSystems.MeasurableArgmin.measurableSet_exists_mem_le`: for closed `C ⊆ U`,
  `{t | ∃ u ∈ C, φ t u ≤ min φ t}` is measurable;
* `DynamicalSystems.MeasurableArgmin.exists_measurable_isMinOn`: there is a **measurable**
  `s : T → U` with `φ t (s t) ≤ φ t v` for all `t` and `v` (a measurable selection of the argmin).

The selector is the limit of centres chosen by the "first index that keeps the argmin reachable"
rule on a dense sequence at shrinking radii `2⁻ⁿ` (the Kuratowski–Ryll-Nardzewski scheme specialised
to a compact metric control set). Mathlib has no such measurable-argmin selection theorem.
This is the selection step behind the Hamiltonian minimum for relaxed controls
(Berkovitz & Medhin, *Nonlinear Optimal Control Theory*, CRC 2012, §11.3, §11.6,
equation (11.6.13)); see
`DynamicalSystems.Mathlib.MeasureTheory.RelaxedHamiltonianMinimum`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory Set Filter Topology Metric TopologicalSpace

namespace DynamicalSystems.MeasurableArgmin

section Dense

/-- On a compact space the infimum of a continuous function over a dense sequence is a lower
bound for the function everywhere. -/
lemma iInf_denseRange_le {X : Type*} [TopologicalSpace X] [CompactSpace X] {g : X → ℝ}
    (hg : Continuous g) {d : ℕ → X} (hd : DenseRange d) (x : X) : ⨅ n, g (d n) ≤ g x := by
  have hbdd : BddBelow (Set.range fun n => g (d n)) :=
    (isCompact_range hg).bddBelow.mono (Set.range_comp_subset_range d g)
  refine hd.induction_on x (isClosed_le continuous_const hg) fun n => ?_
  exact ciInf_le hbdd n

end Dense

variable {T U : Type*} [MeasurableSpace T] [MetricSpace U] [CompactSpace U] [Nonempty U]
  [MeasurableSpace U] [BorelSpace U]

/-- The value function `t ↦ inf_u φ t u`. -/
noncomputable def minValue (φ : T → U → ℝ) (t : T) : ℝ := ⨅ u, φ t u

section Basic

variable {φ : T → U → ℝ}

lemma bddBelow_range (hc : ∀ t, Continuous (φ t)) (t : T) : BddBelow (Set.range (φ t)) :=
  (isCompact_range (hc t)).bddBelow

lemma minValue_le (hc : ∀ t, Continuous (φ t)) (t : T) (u : U) : minValue φ t ≤ φ t u :=
  ciInf_le (bddBelow_range hc t) u

lemma exists_eq_minValue (hc : ∀ t, Continuous (φ t)) (t : T) : ∃ u, φ t u = minValue φ t := by
  obtain ⟨u, -, hu⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty (hc t).continuousOn
  refine ⟨u, le_antisymm (le_ciInf fun v => hu (Set.mem_univ v)) (minValue_le hc t u)⟩

/-- The value function of a Carathéodory integrand is measurable. -/
lemma measurable_minValue (hm : ∀ u, Measurable fun t => φ t u)
    (hc : ∀ t, Continuous (φ t)) : Measurable (minValue φ) := by
  have hd : DenseRange (denseSeq U) := denseRange_denseSeq U
  have key : ∀ t, minValue φ t = ⨅ n, φ t (denseSeq U n) := fun t =>
    le_antisymm
      (le_ciInf fun n => minValue_le hc t _)
      (le_ciInf fun u => iInf_denseRange_le (hc t) hd u)
  have : minValue φ = fun t => ⨅ n, φ t (denseSeq U n) := funext key
  rw [this]
  exact Measurable.iInf fun n => hm _

/-- For closed `C`, the set of times at which the argmin meets `C` is measurable. -/
lemma measurableSet_exists_mem_le (hm : ∀ u, Measurable fun t => φ t u)
    (hc : ∀ t, Continuous (φ t)) {C : Set U} (hC : IsClosed C) :
    MeasurableSet {t | ∃ u ∈ C, φ t u ≤ minValue φ t} := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · simp
  have : Nonempty C := hne.to_subtype
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC.isCompact
  have hd : DenseRange (denseSeq C) := denseRange_denseSeq C
  have key : {t | ∃ u ∈ C, φ t u ≤ minValue φ t} =
      {t | ⨅ n, φ t (denseSeq C n) ≤ minValue φ t} := by
    ext t
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨u, hu, h⟩
      exact (iInf_denseRange_le ((hc t).comp continuous_subtype_val) hd ⟨u, hu⟩).trans h
    · intro h
      obtain ⟨u, hu, hmin⟩ := hC.isCompact.exists_isMinOn hne (hc t).continuousOn
      refine ⟨u, hu, le_trans ?_ h⟩
      exact le_ciInf fun n => hmin (denseSeq C n).2
  rw [key]
  exact measurableSet_le (Measurable.iInf fun n => hm _) (measurable_minValue hm hc)

end Basic

/-! ### The selection scheme -/

section Selection

variable (φ : T → U → ℝ)

/-- Radii `2⁻ᵏ` of the selection scheme. -/
noncomputable def radius (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ k

lemma radius_pos (k : ℕ) : 0 < radius k := by unfold radius; positivity

/-- The closed set attached to a list of indices `i :: p` (newest first):
`closedBall (D i) 2⁻ᵖ.ˡᵉⁿᵍᵗʰ ∩ C p`. -/
noncomputable def cell : List ℕ → Set U
  | [] => Set.univ
  | i :: p => closedBall (denseSeq U i) (radius p.length) ∩ cell p

lemma isClosed_cell : ∀ p : List ℕ, IsClosed (cell (U := U) p)
  | [] => isClosed_univ
  | _ :: p => isClosed_closedBall.inter (isClosed_cell p)

lemma cell_cons_subset (i : ℕ) (p : List ℕ) : cell (U := U) (i :: p) ⊆ cell p :=
  Set.inter_subset_right

/-- Times at which the argmin meets the cell of `p`. -/
def good (p : List ℕ) (t : T) : Prop := ∃ u ∈ cell (U := U) p, φ t u ≤ minValue φ t

variable {φ}

lemma measurableSet_good (hm : ∀ u, Measurable fun t => φ t u) (hc : ∀ t, Continuous (φ t))
    (p : List ℕ) : MeasurableSet {t | good φ p t} :=
  measurableSet_exists_mem_le hm hc (isClosed_cell p)

lemma exists_good_cons {p : List ℕ} {t : T} (h : good φ p t) :
    ∃ i, good φ (i :: p) t := by
  obtain ⟨u, hu, hle⟩ := h
  obtain ⟨i, hi⟩ := (denseRange_denseSeq U).exists_dist_lt u (radius_pos p.length)
  refine ⟨i, u, ⟨?_, hu⟩, hle⟩
  rw [mem_closedBall]
  exact hi.le

/-- Guarded predicate making the search total: `i :: p` is good, or `p` is already not good. -/
def step (φ : T → U → ℝ) (p : List ℕ) (i : ℕ) (t : T) : Prop := good φ (i :: p) t ∨ ¬ good φ p t

lemma exists_step (φ : T → U → ℝ) (p : List ℕ) (t : T) : ∃ i, step φ p i t := by
  by_cases h : good φ p t
  · obtain ⟨i, hi⟩ := exists_good_cons h
    exact ⟨i, Or.inl hi⟩
  · exact ⟨0, Or.inr h⟩

open Classical in
/-- The first admissible next index. -/
noncomputable def next (_hc : ∀ t, Continuous (φ t)) (p : List ℕ) (t : T) : ℕ :=
  Nat.find (exists_step φ p t)

open Classical in
lemma good_cons_next (hc : ∀ t, Continuous (φ t)) {p : List ℕ} {t : T} (h : good φ p t) :
    good φ (next hc p t :: p) t := by
  have := Nat.find_spec (exists_step φ p t)
  exact this.resolve_right (not_not.mpr h)

open Classical in
lemma measurable_next (hm : ∀ u, Measurable fun t => φ t u) (hc : ∀ t, Continuous (φ t))
    (p : List ℕ) : Measurable (next hc p) := by
  refine measurable_find (p := fun t i => step φ p i t) (exists_step φ p) fun i => ?_
  exact (measurableSet_good hm hc (i :: p)).union (measurableSet_good hm hc p).compl

/-- The list of chosen indices after `n` steps. -/
noncomputable def path (hc : ∀ t, Continuous (φ t)) : ℕ → T → List ℕ
  | 0, _ => []
  | n + 1, t => next hc (path hc n t) t :: path hc n t

lemma length_path (hc : ∀ t, Continuous (φ t)) (n : ℕ) (t : T) : (path hc n t).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [path, ih]

lemma good_path (hc : ∀ t, Continuous (φ t)) (n : ℕ) (t : T) : good φ (path hc n t) t := by
  induction n with
  | zero =>
    obtain ⟨u, hu⟩ := exists_eq_minValue hc t
    exact ⟨u, Set.mem_univ u, hu.le⟩
  | succ n ih => exact good_cons_next hc ih

/-- The index chosen at step `n`. -/
noncomputable def idx (hc : ∀ t, Continuous (φ t)) (n : ℕ) (t : T) : ℕ :=
  next hc (path hc n t) t

lemma measurableSet_path (hm : ∀ u, Measurable fun t => φ t u) (hc : ∀ t, Continuous (φ t))
    (n : ℕ) (p : List ℕ) : MeasurableSet {t | path hc n t = p} := by
  induction n generalizing p with
  | zero =>
    by_cases hp : p = []
    · subst hp; simp [path]
    · have : {t : T | path hc 0 t = p} = ∅ := by
        ext t; simp [path, Ne.symm hp]
      rw [this]; exact MeasurableSet.empty
  | succ n ih =>
    cases p with
    | nil => simp [path]
    | cons i q =>
      have : {t : T | path hc (n + 1) t = i :: q} =
          {t | path hc n t = q} ∩ {t | next hc q t = i} := by
        ext t
        simp only [path, List.cons.injEq, Set.mem_ofPred_eq, Set.mem_inter_iff]
        constructor
        · rintro ⟨h1, h2⟩; subst h2; exact ⟨rfl, h1⟩
        · rintro ⟨h2, h1⟩; subst h2; exact ⟨h1, rfl⟩
      rw [this]
      exact (ih q).inter (measurable_next hm hc q (measurableSet_singleton i))

lemma measurable_idx (hm : ∀ u, Measurable fun t => φ t u) (hc : ∀ t, Continuous (φ t))
    (n : ℕ) : Measurable (idx hc n) := by
  refine measurable_to_countable' fun i => ?_
  have : idx hc n ⁻¹' {i} = ⋃ p : List ℕ, {t | path hc n t = p} ∩ {t | next hc p t = i} := by
    ext t
    simp only [idx, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨path hc n t, rfl, h⟩, fun ⟨p, hp, hn⟩ => hp ▸ hn⟩
  rw [this]
  exact MeasurableSet.iUnion fun p =>
    (measurableSet_path hm hc n p).inter (measurable_next hm hc p (measurableSet_singleton i))

/-- The `n`-th approximate selector. -/
noncomputable def approx (hc : ∀ t, Continuous (φ t)) (n : ℕ) (t : T) : U :=
  denseSeq U (idx hc n t)

lemma measurable_approx (hm : ∀ u, Measurable fun t => φ t u) (hc : ∀ t, Continuous (φ t))
    (n : ℕ) : Measurable (approx hc n) :=
  (measurable_of_countable (denseSeq U)).comp (measurable_idx hm hc n)

lemma exists_tendsto_approx (hc : ∀ t, Continuous (φ t)) (t : T) :
    ∃ z, (∀ v, φ t z ≤ φ t v) ∧ Tendsto (fun n => approx hc n t) atTop (𝓝 z) := by
  set K : ℕ → Set U := fun n => cell (path hc n t) ∩ {u | φ t u ≤ minValue φ t} with hK
  have hKclosed : ∀ n, IsClosed (K n) := fun n =>
    (isClosed_cell _).inter (isClosed_le (hc t) continuous_const)
  have hKne : ∀ n, (K n).Nonempty := fun n => by
    obtain ⟨u, hu, hle⟩ := good_path hc n t
    exact ⟨u, hu, hle⟩
  have hKanti : ∀ n, K (n + 1) ⊆ K n := fun n =>
    Set.inter_subset_inter_left _ (by simpa [path] using cell_cons_subset _ _)
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hKanti
    hKne (hKclosed 0).isCompact (hKclosed)
  rw [Set.mem_iInter] at hz
  have hzmin : ∀ v, φ t z ≤ φ t v := fun v => ((hz 0).2).trans (minValue_le hc t v)
  refine ⟨z, hzmin, ?_⟩
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num))
  have h1 := (hz (n + 1)).1
  simp only [path, cell, Set.mem_inter_iff, mem_closedBall, length_path] at h1
  rw [dist_comm]
  exact h1.1

/-- **Measurable selection of an argmin** for a Carathéodory integrand on a compact metric
control set: there is a measurable `s : T → U` with `φ t (s t) ≤ φ t v` for all `t`, `v`. -/
theorem exists_measurable_isMinOn {φ : T → U → ℝ} (hm : ∀ u, Measurable fun t => φ t u)
    (hc : ∀ t, Continuous (φ t)) :
    ∃ s : T → U, Measurable s ∧ ∀ t v, φ t (s t) ≤ φ t v := by
  choose z hz hlim using exists_tendsto_approx hc
  refine ⟨z, ?_, hz⟩
  refine measurable_of_tendsto_metrizable (f := fun n => approx hc n)
    (fun n => measurable_approx hm hc n) ?_
  exact tendsto_pi_nhds.2 hlim

end Selection

end DynamicalSystems.MeasurableArgmin
