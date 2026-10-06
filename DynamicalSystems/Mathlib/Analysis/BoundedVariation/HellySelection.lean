/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import Mathlib.Analysis.BoundedVariation
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Order.LiminfLimsup
public import Mathlib.Topology.Compactness.Compact

/-!
# Helly selection theorem

A sequence of functions on `[a, b]` with uniformly bounded total variation and a uniform bound
at one point has a subsequence converging **everywhere** on `[a, b]` to a function of bounded
variation (Helly's selection theorem; used for the limiting operations in the bounded-variation
form of the state-constrained maximum principle).

Proof outline:
* `exists_strictMono_tendsto_of_countable`: diagonal extraction over a countable index set from the
  sequential compactness of a countable product of compact intervals;
* `exists_strictMono_tendsto_of_monotone`: monotone uniformly bounded families have a
  pointwise convergent subsequence (rationals, then the countably many discontinuities of the
  `limsup`);
* Jordan decomposition `f = p - (p - f)` with `p = variationOnFromTo f s a` reduces the bounded
  variation case to the monotone one;
* `eVariationOn_le_of_tendsto`: the total variation is lower semicontinuous for pointwise limits.
-/

@[expose] public section

open Filter Set Topology
open scoped ENNReal NNReal

namespace DynamicalSystems.Helly

/-! ### Diagonal extraction -/

/-- Bounded real sequences indexed by a countable set have a common subsequence converging at
every index. -/
theorem exists_strictMono_tendsto_of_countable {S : Type*} [Countable S] (X : ℕ → S → ℝ)
    {M : ℝ} (hM : ∀ n s, |X n s| ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ s, ∃ l, Tendsto (fun n => X (φ n) s) atTop (𝓝 l) := by
  have hK : IsCompact (Set.pi (univ : Set S) fun _ => Icc (-M) M) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨a, -, φ, hφ, hlim⟩ := hK.tendsto_subseq (x := X) fun n s _ => by
    have := hM n s
    rw [abs_le] at this
    exact this
  exact ⟨φ, hφ, fun s => ⟨a s, tendsto_pi_nhds.1 hlim s⟩⟩

/-! ### Monotone case -/

section Monotone

variable {ι : Type*} [Countable ι]

/-- **Helly selection for monotone functions**: uniformly bounded families of monotone functions
`ℝ → ℝ` have a common subsequence converging at every point. -/
theorem exists_strictMono_tendsto_of_monotone (F : ℕ → ι → ℝ → ℝ)
    (hmono : ∀ n i, Monotone (F n i)) {M : ℝ} (hb : ∀ n i x, |F n i x| ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i x, ∃ l, Tendsto (fun n => F (φ n) i x) atTop (𝓝 l) := by
  -- step 1: convergence at all rationals
  obtain ⟨φ₁, hφ₁, hrat⟩ := exists_strictMono_tendsto_of_countable
    (fun n (s : ι × ℚ) => F n s.1 (s.2 : ℝ)) (M := M) fun n s => hb n _ _
  have hbelow : ∀ (f : ℕ → ℝ) (_ : ∀ n, |f n| ≤ M),
      IsBoundedUnder (· ≥ ·) atTop f ∧ IsBoundedUnder (· ≤ ·) atTop f := fun f hf =>
    ⟨isBoundedUnder_of ⟨-M, fun n => (abs_le.1 (hf n)).1⟩,
      isBoundedUnder_of ⟨M, fun n => (abs_le.1 (hf n)).2⟩⟩
  -- the limsup along the first subsequence
  let G : ι → ℝ → ℝ := fun i x => limsup (fun n => F (φ₁ n) i x) atTop
  have hG : ∀ i, Monotone (G i) := fun i x y hxy => by
    have h1 := hbelow (fun n => F (φ₁ n) i x) fun n => hb _ _ _
    have h2 := hbelow (fun n => F (φ₁ n) i y) fun n => hb _ _ _
    exact limsup_le_limsup (Eventually.of_forall fun n => hmono _ i hxy)
      h1.1.isCoboundedUnder_le h2.2
  -- the convergent points
  have hconv : ∀ i x, ContinuousAt (G i) x →
      Tendsto (fun n => F (φ₁ n) i x) atTop (𝓝 (G i x)) := by
    intro i x hx
    have h1 := hbelow (fun n => F (φ₁ n) i x) fun n => hb _ _ _
    refine tendsto_of_le_liminf_of_limsup_le ?_ le_rfl h1.2 h1.1
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨δ, hδ, hδG⟩ := Metric.continuousAt_iff.1 hx (ε / 2) (half_pos hε)
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (sub_lt_self x hδ)
    obtain ⟨l, hl⟩ := hrat (i, q)
    have hlG : G i q = l := hl.limsup_eq
    have hGq : G i x - ε / 2 < G i q := by
      have := hδG (show dist (q : ℝ) x < δ by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
      rw [Real.dist_eq, abs_lt] at this
      linarith [this.1]
    have hev : ∀ᶠ n in atTop, l - ε / 2 ≤ F (φ₁ n) i x := by
      filter_upwards [hl.eventually (eventually_ge_nhds (show l - ε / 2 < l by linarith))]
        with n hn
      exact hn.trans (hmono _ i hq2.le)
    have : l - ε / 2 ≤ liminf (fun n => F (φ₁ n) i x) atTop :=
      le_liminf_of_le h1.2.isCoboundedUnder_ge hev
    linarith
  -- step 2: the countably many discontinuities
  let S : Set (ι × ℝ) := ⋃ i, (fun x => (i, x)) '' {x | ¬ ContinuousAt (G i) x}
  have hS : S.Countable := Set.countable_iUnion fun i =>
    ((hG i).countable_not_continuousAt).image _
  have : Countable S := hS.to_subtype
  obtain ⟨φ₂, hφ₂, hbad⟩ := exists_strictMono_tendsto_of_countable
    (fun n (s : S) => F (φ₁ n) s.1.1 s.1.2) (M := M) fun n s => hb _ _ _
  refine ⟨φ₁ ∘ φ₂, hφ₁.comp hφ₂, fun i x => ?_⟩
  by_cases hx : ContinuousAt (G i) x
  · exact ⟨G i x, (hconv i x hx).comp hφ₂.tendsto_atTop⟩
  · obtain ⟨l, hl⟩ := hbad ⟨(i, x), mem_iUnion.2 ⟨i, x, hx, rfl⟩⟩
    exact ⟨l, hl⟩

end Monotone

/-! ### Lower semicontinuity of the variation -/

/-- The total variation is lower semicontinuous under pointwise convergence: if `f i → g`
pointwise on `s` along a nontrivial filter and `eVariationOn (f i) s ≤ C` eventually, then
`eVariationOn g s ≤ C`. -/
theorem eVariationOn_le_of_tendsto {α E ι : Type*} [LinearOrder α] [PseudoEMetricSpace E]
    {l : Filter ι} [l.NeBot] {s : Set α} {f : ι → α → E} {g : α → E} {C : ℝ≥0∞}
    (hf : ∀ᶠ i in l, eVariationOn (f i) s ≤ C)
    (hg : ∀ x ∈ s, Tendsto (fun i => f i x) l (𝓝 (g x))) : eVariationOn g s ≤ C := by
  unfold eVariationOn
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, hus⟩ := p
  refine le_of_tendsto (tendsto_finsetSum _ fun i _ =>
    ((hg _ (hus (i + 1))).edist (hg _ (hus i)))) ?_
  filter_upwards [hf] with j hj
  exact (eVariationOn.sum_le hu hus).trans hj

/-! ### Helly selection for bounded variation -/

/-- **Helly selection, countable real-valued families**: if every `c n i` has total variation at
most `C < ⊤` on `[a, b]` and is bounded by `M` there, a common subsequence converges at every
point of `[a, b]`, for all indices `i` at once. The proof uses the Jordan decomposition
`c = p - (p - c)` with `p = variationOnFromTo c (Icc a b) a`. -/
theorem exists_strictMono_tendsto_of_eVariationOn_le {ι : Type*} [Countable ι]
    (c : ℕ → ι → ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) {C : ℝ≥0∞} (hC : C ≠ ⊤) {M : ℝ}
    (hv : ∀ n i, eVariationOn (c n i) (Icc a b) ≤ C)
    (hM : ∀ n i, ∀ x ∈ Icc a b, |c n i x| ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, ∀ x ∈ Icc a b, ∃ l, Tendsto (fun n => c (φ n) i x) atTop (𝓝 l) := by
  set s : Set ℝ := Icc a b with hs
  have has : a ∈ s := ⟨le_rfl, hab⟩
  let cl : ℝ → ℝ := fun x => max a (min x b)
  have hcl_mem : ∀ x, cl x ∈ s := fun x =>
    ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have hcl_mono : Monotone cl := fun x y h => max_le_max le_rfl (min_le_min h le_rfl)
  have hcl_id : ∀ x ∈ s, cl x = x := fun x hx => by
    simp only [cl]
    rw [min_eq_left hx.2, max_eq_right hx.1]
  have hlbv : ∀ n i, LocallyBoundedVariationOn (c n i) s := fun n i =>
    (BoundedVariationOn.locallyBoundedVariationOn
      (ne_top_of_le_ne_top hC (hv n i)) : _)
  let p : ℕ → ι → ℝ → ℝ := fun n i => variationOnFromTo (c n i) s a
  have hp_mono : ∀ n i, MonotoneOn (p n i) s := fun n i =>
    variationOnFromTo.monotoneOn (hlbv n i) has
  have hq_mono : ∀ n i, MonotoneOn (fun y => p n i y - c n i y) s := fun n i =>
    variationOnFromTo.sub_self_monotoneOn (hlbv n i) has
  have hp_bd : ∀ n i, ∀ y ∈ s, |p n i y| ≤ C.toReal := by
    intro n i y hy
    have h1 : p n i y = (eVariationOn (c n i) (s ∩ Icc a y)).toReal :=
      variationOnFromTo.eq_of_le _ _ hy.1
    rw [h1, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_mono hC
      ((eVariationOn.mono _ inter_subset_left).trans (hv n i))
  let F : ℕ → ι ⊕ ι → ℝ → ℝ := fun n j x =>
    Sum.elim (fun i => p n i (cl x)) (fun i => p n i (cl x) - c n i (cl x)) j
  have hF_mono : ∀ n j, Monotone (F n j) := by
    intro n j x y hxy
    rcases j with i | i
    · exact hp_mono n i (hcl_mem x) (hcl_mem y) (hcl_mono hxy)
    · exact hq_mono n i (hcl_mem x) (hcl_mem y) (hcl_mono hxy)
  have hF_bd : ∀ n j x, |F n j x| ≤ C.toReal + |M| := by
    intro n j x
    rcases j with i | i
    · exact (hp_bd n i _ (hcl_mem x)).trans (by linarith [abs_nonneg M])
    · refine (abs_sub _ _).trans ?_
      exact add_le_add (hp_bd n i _ (hcl_mem x)) ((hM n i _ (hcl_mem x)).trans (le_abs_self M))
  obtain ⟨φ, hφ, hlim⟩ := exists_strictMono_tendsto_of_monotone F hF_mono hF_bd
  refine ⟨φ, hφ, fun i x hx => ?_⟩
  obtain ⟨l₁, h₁⟩ := hlim (Sum.inl i) x
  obtain ⟨l₂, h₂⟩ := hlim (Sum.inr i) x
  refine ⟨l₁ - l₂, (h₁.sub h₂).congr fun n => ?_⟩
  simp only [F, Sum.elim_inl, Sum.elim_inr, hcl_id x hx]
  ring

/-- **Helly selection theorem (finite-dimensional target).** Let `f n : ℝ → E` have total
variation at most `C < ⊤` on `[a, b]` and be bounded by `B` at one point `x₀ ∈ [a, b]`. Then a
subsequence converges at **every** point of `[a, b]` to a function `g` of total variation at
most `C`. -/
theorem helly_selection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : ℕ → ℝ → E) {a b : ℝ} (hab : a ≤ b) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc a b) {B : ℝ} (hB : ∀ n, ‖f n x₀‖ ≤ B) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hv : ∀ n, eVariationOn (f n) (Icc a b) ≤ C) :
    ∃ (φ : ℕ → ℕ) (g : ℝ → E), StrictMono φ ∧ eVariationOn g (Icc a b) ≤ C ∧
      ∀ x ∈ Icc a b, Tendsto (fun n => f (φ n) x) atTop (𝓝 (g x)) := by
  let bs := Module.finBasis ℝ E
  let L : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ := fun i =>
    LinearMap.toContinuousLinearMap (bs.coord i)
  let K : ℝ≥0 := ∑ i, ‖L i‖₊
  have hL : ∀ i, LipschitzWith K (L i) := fun i =>
    (L i).lipschitzWith.weaken
      (Finset.single_le_sum (f := fun i => ‖L i‖₊) (fun _ _ => zero_le) (Finset.mem_univ i))
  have hdist : ∀ n, ∀ x ∈ Icc a b, ‖f n x‖ ≤ B + C.toReal := by
    intro n x hx
    have h1 : dist (f n x) (f n x₀) ≤ C.toReal := by
      rw [dist_edist]
      exact ENNReal.toReal_mono hC ((eVariationOn.edist_le _ hx hx₀).trans (hv n))
    have := norm_le_insert' (f n x) (f n x₀)
    rw [← dist_zero_right] at *
    linarith [dist_triangle (f n x) (f n x₀) 0, hB n, dist_zero_right (f n x₀)]
  obtain ⟨φ, hφ, hlim⟩ := exists_strictMono_tendsto_of_eVariationOn_le
    (fun n (i : Fin (Module.finrank ℝ E)) => fun x => L i (f n x)) hab
    (C := K * C) (ENNReal.mul_ne_top ENNReal.coe_ne_top hC) (M := K * |B + C.toReal|)
    (fun n i => (((hL i).lipschitzOnWith (s := univ)).comp_eVariationOn_le
        (g := f n) (s := Icc a b) (mapsTo_univ _ _)).trans
      (mul_le_mul' le_rfl (hv n)))
    (fun n i x hx => by
      have := (hL i).dist_le_mul (f n x) 0
      rw [map_zero, Real.dist_eq, sub_zero, dist_zero_right] at this
      exact this.trans (mul_le_mul_of_nonneg_left ((hdist n x hx).trans (le_abs_self _)) K.2))
  have hrepr : ∀ y : E, ∑ i, L i y • bs i = y := fun y => by
    simp [L]
  let g : ℝ → E := fun x => ∑ i, limUnder atTop (fun n => L i (f (φ n) x)) • bs i
  have hconv : ∀ x ∈ Icc a b, Tendsto (fun n => f (φ n) x) atTop (𝓝 (g x)) := by
    intro x hx
    have h := tendsto_finsetSum Finset.univ fun i _ =>
      (tendsto_nhds_limUnder (hlim i x hx)).smul_const (bs i)
    exact h.congr fun n => hrepr _
  exact ⟨φ, g, hφ, eVariationOn_le_of_tendsto (l := atTop)
    (Eventually.of_forall fun n => hv (φ n)) hconv, hconv⟩

/-- Real-valued Helly selection, with the conclusion in `BoundedVariationOn` form. -/
theorem helly_selection_real (f : ℕ → ℝ → ℝ) {a b : ℝ} (hab : a ≤ b) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Icc a b) {B : ℝ} (hB : ∀ n, |f n x₀| ≤ B) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hv : ∀ n, eVariationOn (f n) (Icc a b) ≤ C) :
    ∃ (φ : ℕ → ℕ) (g : ℝ → ℝ), StrictMono φ ∧ BoundedVariationOn g (Icc a b) ∧
      eVariationOn g (Icc a b) ≤ C ∧
      ∀ x ∈ Icc a b, Tendsto (fun n => f (φ n) x) atTop (𝓝 (g x)) := by
  obtain ⟨φ, g, hφ, hg, hlim⟩ := helly_selection f hab hx₀ (B := B)
    (fun n => by simpa using hB n) hC hv
  exact ⟨φ, g, hφ, ne_top_of_le_ne_top hC hg, hg, hlim⟩

/-- **Filter form** (e.g. `ε → 0⁺`): for a family `f ε` that, eventually along a nontrivial
countably generated filter `l`, has variation `≤ C` on `[a, b]` and is bounded by `B` at `x₀`,
there is a sequence of parameters tending to `l` along which `f` converges pointwise on `[a, b]`
to a function of variation `≤ C`. -/
theorem helly_selection_filter {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {l : Filter α} [l.NeBot] [l.IsCountablyGenerated]
    (f : α → ℝ → E) {a b : ℝ} (hab : a ≤ b) {x₀ : ℝ} (hx₀ : x₀ ∈ Icc a b) {B : ℝ}
    (hB : ∀ᶠ ε in l, ‖f ε x₀‖ ≤ B) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hv : ∀ᶠ ε in l, eVariationOn (f ε) (Icc a b) ≤ C) :
    ∃ (u : ℕ → α) (g : ℝ → E), Tendsto u atTop l ∧ eVariationOn g (Icc a b) ≤ C ∧
      ∀ x ∈ Icc a b, Tendsto (fun n => f (u n) x) atTop (𝓝 (g x)) := by
  obtain ⟨u, hu⟩ := exists_seq_tendsto l
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hu.eventually (hB.and hv))
  obtain ⟨φ, g, hφ, hg, hlim⟩ := helly_selection (fun n => f (u (n + N))) hab hx₀ (B := B)
    (fun n => (hN _ (Nat.le_add_left _ _)).1) hC fun n => (hN _ (Nat.le_add_left _ _)).2
  exact ⟨fun n => u (φ n + N), g,
    hu.comp (tendsto_atTop_mono (fun n => Nat.le_add_right _ _) hφ.tendsto_atTop), hg, hlim⟩

end DynamicalSystems.Helly
