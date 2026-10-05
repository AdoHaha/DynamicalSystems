/-
Copyright (c) 2026 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.ODE.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Order.MonotoneContinuity

/-! # Comparison functions

This file defines the classes `K`, `K∞`, and `KL`, their composition rules, and
inversion of class-`K∞` functions.

## Positive-definite comparison lemmas

* `ComparisonFunction.exists_memKI_bounds_on_closedBall` gives the local norm sandwich
  for a continuous positive-definite function on a closed ball in a proper normed space.
* `ComparisonFunction.exists_memKI_bounds_of_radiallyUnbounded` gives the global norm
  sandwich when the function is also radially unbounded.
* `ComparisonFunction.exists_memKI_sandwich_on_isCompact` compares arbitrary nonnegative
  continuous functions with the same zero set on a compact set.
* `ComparisonFunction.exists_memKI_sandwich_of_coercive` gives the corresponding global
  comparison for two coercive functions.

The comparison functions in all these statements are globally defined class-`K∞` functions.
In the local statements the inequalities hold only on the specified compact set or ball.
Continuity and positive definiteness alone do not imply a global lower class-`K` bound:
`V(x) = x² exp(-x)` on `ℝ` is a smooth counterexample.
-/

@[expose] public noncomputable section

open NNReal Filter Topology

/-- A function of class `K`. -/
@[fun_prop]
structure MemKOn (f : ℝ≥0 → ℝ≥0) (a : ℝ≥0) : Prop where
  /-- The function `f` is continuous on the interval `[0, a]`. -/
  contOn : ContinuousOn f (Set.Icc 0 a)
  /-- The function `f` is strictly increasing on the interval `[0, a]`. -/
  strictMonoOn : StrictMonoOn f (Set.Icc 0 a)
  /-- The function`f` maps `0` to `0`. -/
  zero : f 0 = 0

/-- A function of class `K`. -/
@[fun_prop]
structure MemK (f : ℝ≥0 → ℝ≥0) : Prop where
  /-- The function `f` is continuous. -/
  cont : Continuous f
  /-- The function `f` is strictly increasing. -/
  strictMono : StrictMono f
  /-- The function`f` maps `0` to `0`. -/
  zero : f 0 = 0

/-- A function of class `K_∞`. -/
@[fun_prop]
structure MemKI (f : ℝ≥0 → ℝ≥0) : Prop extends MemK f where
  /-- The function `f x` converges to `∞` as `x → ∞`. -/
  tendsto : Tendsto f atTop atTop

/-- A function of class `KL`. -/
@[fun_prop]
structure MemKL (f : ℝ → ℝ≥0 → ℝ≥0) : Prop where
  cont : Continuous f.uncurry
  strictMono : ∀ x, StrictMono (f x)
  zero : ∀ x, f x 0 = 0
  antitone : ∀ y, Antitone (f · y)
  tendsto : ∀ y, Tendsto (f · y) atTop (𝓝 0)

variable {f : ℝ → ℝ≥0 → ℝ≥0}

theorem MemKL.memK (hf : MemKL f) (x : ℝ) : MemK (f x) := by
  refine ⟨?_, hf.strictMono x, hf.zero x⟩
  have : Continuous f.uncurry := hf.cont
  fun_prop

namespace MemKOn

variable {f g : ℝ≥0 → ℝ≥0} {a₁ a₂ : ℝ≥0}

@[fun_prop]
theorem comp (hf : MemKOn f a₁) (hg : MemKOn g a₂) (ha : g a₂ ≤ a₁) : MemKOn (f ∘ g) a₂ where
  contOn := by
    apply hf.contOn.comp hg.contOn
    intro x hx
    simp only [Set.mem_Icc, zero_le, true_and] at hx ⊢
    apply le_trans _ ha
    apply hg.strictMonoOn.monotoneOn (by simp [hx]) (by simp) hx
  strictMonoOn := by
    apply hf.strictMonoOn.comp hg.strictMonoOn
    intro x hx
    simp only [Set.mem_Icc, zero_le, true_and] at hx ⊢
    apply le_trans _ ha
    apply hg.strictMonoOn.monotoneOn (by simp [hx]) (by simp) hx
  zero := by simp [hf.zero, hg.zero]

end MemKOn

namespace MemK

variable {f g : ℝ≥0 → ℝ≥0}

theorem injective (hf : MemK f) : Function.Injective f :=
  hf.strictMono.injective

@[fun_prop]
theorem comp (hf : MemK f) (hg : MemK g) : MemK (f ∘ g) where
  cont := hf.cont.comp hg.cont
  strictMono := hf.strictMono.comp hg.strictMono
  zero := by simp [hf.zero, hg.zero]

/-- A globally defined class-`K` function is class `K` on every initial interval. -/
@[fun_prop]
theorem memKOn (hf : MemK f) (a : ℝ≥0) : MemKOn f a where
  contOn := hf.cont.continuousOn
  strictMonoOn := hf.strictMono.strictMonoOn _
  zero := hf.zero

/-- A class-`K` function is strictly positive at positive arguments. -/
theorem pos (hf : MemK f) {r : ℝ≥0} (hr : 0 < r) : 0 < f r := by
  simpa only [hf.zero] using hf.strictMono hr

end MemK

namespace MemKI

variable {f : ℝ≥0 → ℝ≥0}

/-- A class-`K∞` function is onto the nonnegative reals. -/
theorem surjective (hf : MemKI f) : Function.Surjective f :=
  hf.cont.surjective hf.tendsto (by simp [OrderBot.atBot_eq, hf.zero])

/-- A class-`K∞` function, bundled as an order isomorphism. -/
noncomputable def orderIso (hf : MemKI f) : ℝ≥0 ≃o ℝ≥0 :=
  StrictMono.orderIsoOfSurjective f hf.strictMono hf.surjective

@[simp]
theorem orderIso_apply (hf : MemKI f) (r : ℝ≥0) : hf.orderIso r = f r := rfl

/-- The inverse of a class-`K∞` function is again class `K∞`. -/
@[fun_prop]
theorem symm (hf : MemKI f) : MemKI hf.orderIso.symm where
  cont := hf.orderIso.symm.continuous
  strictMono := hf.orderIso.symm.strictMono
  zero := hf.orderIso.symm.map_bot
  tendsto := hf.orderIso.symm.tendsto_atTop

end MemKI

namespace ComparisonFunction

/-! ## Constructing comparison functions

For nonnegative continuous `f` and `g`, with `g` coercive and
`g x = 0 → f x = 0`, consider the infimum
`m(r) = inf_x (g x + (r - f x))`, using truncated subtraction on `ℝ≥0`.
The envelope is nondecreasing and 1-Lipschitz. Coercivity gives attainment of the
infimum, positivity for positive `r`, and unboundedness. Multiplication by
`r / (1 + r)` makes it strictly increasing while preserving `α (f x) ≤ g x`.
Swapping `f` and `g` and taking the inverse supplies the upper comparison.
On a compact space coercivity is automatic. No differentiability is needed.
-/

section Coercive

variable {X : Type*}
variable (f g : X → ℝ≥0)

/-- The monotone infimum envelope used to construct class-`K∞` comparison functions. -/
private noncomputable def comparisonEnvelope (r : ℝ≥0) : ℝ≥0 :=
  sInf ((fun x ↦ g x + (r - f x)) '' Set.univ)

private theorem comparisonEnvelope_le (r : ℝ≥0) (x : X) :
    comparisonEnvelope f g r ≤ g x + (r - f x) :=
  csInf_le (OrderBot.bddBelow _) (Set.mem_image_of_mem _ (Set.mem_univ x))

variable [Nonempty X]

private theorem le_comparisonEnvelope {r b : ℝ≥0}
    (h : ∀ x, b ≤ g x + (r - f x)) : b ≤ comparisonEnvelope f g r := by
  apply le_csInf (Set.univ_nonempty.image _)
  rintro _ ⟨x, _, rfl⟩
  exact h x

private theorem comparisonEnvelope_mono : Monotone (comparisonEnvelope f g) := by
  intro r s hrs
  apply le_comparisonEnvelope
  intro x
  exact (comparisonEnvelope_le f g r x).trans
    (add_le_add_right (tsub_le_tsub_right hrs _) _)

private theorem comparisonEnvelope_le_add_nndist (r s : ℝ≥0) :
    comparisonEnvelope f g r ≤ comparisonEnvelope f g s + nndist r s := by
  apply (tsub_le_iff_right).mp
  apply le_comparisonEnvelope
  intro x
  apply (tsub_le_iff_right).mpr
  calc
    comparisonEnvelope f g r ≤ g x + (r - f x) := comparisonEnvelope_le f g r x
    _ ≤ g x + ((s + nndist r s) - f x) :=
      add_le_add_right (tsub_le_tsub_right (NNReal.le_add_nndist r s) _) _
    _ ≤ g x + ((s - f x) + nndist r s) :=
      add_le_add_right add_tsub_le_tsub_add _
    _ = g x + (s - f x) + nndist r s := (add_assoc _ _ _).symm

private theorem continuous_comparisonEnvelope : Continuous (comparisonEnvelope f g) := by
  have hLip : LipschitzWith 1 (fun r ↦ (comparisonEnvelope f g r : ℝ)) := by
    apply LipschitzWith.of_le_add
    intro r s
    exact_mod_cast comparisonEnvelope_le_add_nndist f g r s
  exact hLip.continuous.subtype_mk (fun r ↦ (comparisonEnvelope f g r).property)

variable [TopologicalSpace X]

private theorem comparisonEnvelope_attained (hf : Continuous f) (hg : Continuous g)
    (hg_top : Tendsto g (cocompact X) atTop) (r : ℝ≥0) :
    ∃ x, comparisonEnvelope f g r = g x + (r - f x) := by
  have hcont : Continuous (fun x ↦ g x + (r - f x)) := by fun_prop
  have hlim : Tendsto (fun x ↦ g x + (r - f x)) (cocompact X) atTop :=
    tendsto_atTop_mono (fun x ↦ le_add_of_nonneg_right zero_le) hg_top
  obtain ⟨x, hx⟩ := hcont.exists_forall_le hlim
  exact ⟨x, le_antisymm (comparisonEnvelope_le f g r x) (le_comparisonEnvelope f g hx)⟩

private theorem comparisonEnvelope_pos (hf : Continuous f) (hg : Continuous g)
    (hg_top : Tendsto g (cocompact X) atTop)
    (hzero : ∀ x, g x = 0 → f x = 0) {r : ℝ≥0} (hr : 0 < r) :
    0 < comparisonEnvelope f g r := by
  obtain ⟨x, hx⟩ := comparisonEnvelope_attained f g hf hg hg_top r
  rw [hx]
  by_cases hgx : g x = 0
  · simpa [hgx, hzero x hgx] using hr
  · exact add_pos_of_pos_of_nonneg (pos_iff_ne_zero.mpr hgx) zero_le

/-- A coercive nonnegative continuous function `g` admits a class-`K∞` lower comparison
with every continuous nonnegative function `f` that vanishes at all zeros of `g`.
Here coercive means `g x → ∞` as `x` leaves every compact set. -/
theorem exists_memKI_le_of_coercive (hf : Continuous f) (hg : Continuous g)
    (hg_top : Tendsto g (cocompact X) atTop)
    (hzero : ∀ x, g x = 0 → f x = 0) :
    ∃ α : ℝ≥0 → ℝ≥0, MemKI α ∧ ∀ x, α (f x) ≤ g x := by
  let m := comparisonEnvelope f g
  let q : ℝ≥0 → ℝ≥0 := fun r ↦ r / (1 + r)
  let α : ℝ≥0 → ℝ≥0 := fun r ↦ q r * m r
  have hmmono : Monotone m := comparisonEnvelope_mono f g
  have hmpos : ∀ r, 0 < r → 0 < m r := fun _ hr ↦ comparisonEnvelope_pos f g hf hg hg_top hzero hr
  have hqmono : StrictMono q := by
    intro r s hrs
    dsimp [q]
    apply (div_lt_div_iff₀ (by positivity) (by positivity)).2
    have hrs' : (r : ℝ) < (s : ℝ) := by exact_mod_cast hrs
    exact_mod_cast (show (r : ℝ) * (1 + s) < (s : ℝ) * (1 + r) by nlinarith)
  have hαmono : StrictMono α := by
    intro r s hrs
    calc
      q r * m r ≤ q r * m s := mul_le_mul_of_nonneg_left (hmmono hrs.le) zero_le
      _ < q s * m s := mul_lt_mul_of_pos_right (hqmono hrs)
        (hmpos s ((show (0 : ℝ≥0) ≤ r from zero_le).trans_lt hrs))
  have hα : MemKI α := by
    refine ⟨⟨?_, hαmono, ?_⟩, ?_⟩
    · have hmcont : Continuous m := continuous_comparisonEnvelope f g
      have hqcont : Continuous q := by
        apply Continuous.div₀ continuous_id (continuous_const.add continuous_id)
        intro r
        simp
      exact hqcont.mul hmcont
    · simp [α, q]
    · apply hαmono.monotone.tendsto_atTop_atTop
      intro b
      obtain ⟨K, hK, hout⟩ := hasBasis_cocompact.eventually_iff.mp
        (hg_top.eventually (eventually_ge_atTop (2 * b)))
      obtain ⟨M, hM⟩ := hK.bddAbove_image hf.continuousOn
      let r : ℝ≥0 := 2 * b + M + 1
      have hr : 1 ≤ r := by
        dsimp [r]
        exact le_add_of_nonneg_left (by positivity)
      have hq : (1 / 2 : ℝ≥0) ≤ q r := by
        dsimp [q]
        apply (le_div_iff₀ (by positivity)).2
        have hr' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
        exact_mod_cast (show (1 / 2 : ℝ) * (1 + r) ≤ (r : ℝ) by linarith)
      have hm : 2 * b ≤ m r := by
        apply le_comparisonEnvelope
        intro x
        by_cases hx : x ∈ K
        · apply le_trans _ (le_add_of_nonneg_left zero_le)
          apply le_tsub_of_add_le_right
          have hfx : f x ≤ M := hM (Set.mem_image_of_mem _ hx)
          exact (add_le_add_right hfx (2 * b)).trans (le_add_of_nonneg_right (by positivity))
        · exact (hout hx).trans (le_add_of_nonneg_right zero_le)
      refine ⟨r, ?_⟩
      calc
        b = (1 / 2 : ℝ≥0) * (2 * b) := by ring
        _ ≤ q r * m r := mul_le_mul' hq hm
  refine ⟨α, hα, fun x ↦ ?_⟩
  have hq : q (f x) ≤ 1 := by
    dsimp [q]
    apply (div_le_one (by positivity)).2
    exact le_add_of_nonneg_left (by positivity)
  calc
    α (f x) ≤ m (f x) := by
      dsimp [α]
      exact mul_le_of_le_one_left zero_le hq
    _ ≤ g x := by simpa using comparisonEnvelope_le f g (f x) x

/-- Two coercive nonnegative continuous functions with the same zero set have global
class-`K∞` comparison bounds in both directions. -/
theorem exists_memKI_sandwich_of_coercive (hf : Continuous f) (hg : Continuous g)
    (hf_top : Tendsto f (cocompact X) atTop) (hg_top : Tendsto g (cocompact X) atTop)
    (hzero : ∀ x, g x = 0 ↔ f x = 0) :
    ∃ α₁ α₂ : ℝ≥0 → ℝ≥0, MemKI α₁ ∧ MemKI α₂ ∧
      ∀ x, α₁ (f x) ≤ g x ∧ g x ≤ α₂ (f x) := by
  obtain ⟨α₁, hα₁, hlower⟩ := exists_memKI_le_of_coercive f g hf hg hg_top
    (fun x ↦ (hzero x).mp)
  obtain ⟨β, hβ, hβbound⟩ := exists_memKI_le_of_coercive g f hg hf hf_top
    (fun x ↦ (hzero x).mpr)
  refine ⟨α₁, hβ.orderIso.symm, hα₁, hβ.symm, fun x ↦ ⟨hlower x, ?_⟩⟩
  exact (hβ.orderIso.le_symm_apply).mpr (hβbound x)

/-- Nonnegative continuous functions on a compact space have a class-`K∞` lower comparison
whenever every zero of `g` is a zero of `f`. -/
theorem exists_memKI_le_of_compact [CompactSpace X] (hf : Continuous f) (hg : Continuous g)
    (hzero : ∀ x, g x = 0 → f x = 0) :
    ∃ α : ℝ≥0 → ℝ≥0, MemKI α ∧ ∀ x, α (f x) ≤ g x :=
  exists_memKI_le_of_coercive f g hf hg (by simp) hzero

/-- Two nonnegative continuous functions on a compact space with the same zero set are
bounded above and below by class-`K∞` functions of one another. -/
theorem exists_memKI_sandwich_of_compact [CompactSpace X] (hf : Continuous f) (hg : Continuous g)
    (hzero : ∀ x, g x = 0 ↔ f x = 0) :
    ∃ α₁ α₂ : ℝ≥0 → ℝ≥0, MemKI α₁ ∧ MemKI α₂ ∧
      ∀ x, α₁ (f x) ≤ g x ∧ g x ≤ α₂ (f x) :=
  exists_memKI_sandwich_of_coercive f g hf hg (by simp) (by simp) hzero

end Coercive

/-- Compact-set form of the comparison lemma. Neither the ambient space nor the compact set
needs to be finite-dimensional, and the functions need only be continuous on that set. -/
theorem exists_memKI_sandwich_on_isCompact {X : Type*} [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) (f g : X → ℝ≥0)
    (hf : ContinuousOn f K) (hg : ContinuousOn g K)
    (hzero : ∀ x ∈ K, g x = 0 ↔ f x = 0) :
    ∃ α₁ α₂ : ℝ≥0 → ℝ≥0, MemKI α₁ ∧ MemKI α₂ ∧
      ∀ x ∈ K, α₁ (f x) ≤ g x ∧ g x ≤ α₂ (f x) := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · have hid : MemKI (id : ℝ≥0 → ℝ≥0) :=
      ⟨⟨continuous_id, strictMono_id, rfl⟩, tendsto_id⟩
    exact ⟨id, id, hid, hid, by simp⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : Nonempty K := hne.to_subtype
  obtain ⟨α₁, α₂, hα₁, hα₂, hbound⟩ := exists_memKI_sandwich_of_compact
    (fun x : K ↦ f x) (fun x : K ↦ g x) hf.domRestrict hg.domRestrict
    (fun x ↦ hzero x x.property)
  exact ⟨α₁, α₂, hα₁, hα₂, fun x hx ↦ hbound ⟨x, hx⟩⟩

section PositiveDefiniteFun

variable {E : Type*} [NormedAddCommGroup E]

/-- A continuous positive-definite function has class-`K∞` norm bounds on every compact set.
The inequalities are restricted to the compact set; global positive definiteness alone does
not imply a global lower class-`K` bound. -/
theorem exists_memKI_bounds_of_isCompact (V : E → ℝ) {K : Set E} (hK : IsCompact K)
    (hV : ContinuousOn V K) (hVnonneg : ∀ x ∈ K, 0 ≤ V x)
    (hVzero : ∀ x ∈ K, V x = 0 ↔ x = 0) :
    ∃ α₁ α₂ : ℝ≥0 → ℝ≥0, MemKI α₁ ∧ MemKI α₂ ∧
      ∀ x ∈ K, (α₁ ‖x‖₊ : ℝ) ≤ V x ∧ V x ≤ α₂ ‖x‖₊ := by
  have hzero : ∀ x ∈ K, (V x).toNNReal = 0 ↔ ‖x‖₊ = 0 := by
    intro x hx
    rw [nnnorm_eq_zero]
    constructor
    · intro hz
      apply (hVzero x hx).mp
      exact le_antisymm (Real.toNNReal_eq_zero.mp hz) (hVnonneg x hx)
    · intro hz
      simp [(hVzero x hx).mpr hz]
  obtain ⟨α₁, α₂, hα₁, hα₂, hbound⟩ := exists_memKI_sandwich_on_isCompact hK
    (fun x ↦ ‖x‖₊) (fun x ↦ (V x).toNNReal) (by fun_prop)
    (continuous_real_toNNReal.comp_continuousOn hV) hzero
  refine ⟨α₁, α₂, hα₁, hα₂, fun x hx ↦ ?_⟩
  have h := hbound x hx
  have h₁ : (α₁ ‖x‖₊ : ℝ) ≤ ((V x).toNNReal : ℝ) := by exact_mod_cast h.1
  have h₂ : ((V x).toNNReal : ℝ) ≤ (α₂ ‖x‖₊ : ℝ) := by exact_mod_cast h.2
  simpa only [Real.coe_toNNReal _ (hVnonneg x hx)] using And.intro h₁ h₂

/-- **Local comparison lemma for a positive-definite function** (Khalil, Lemma 4.3).
In a proper normed space (in particular, a finite-dimensional real normed space), continuity
and positive definiteness on a closed ball give class-`K∞` bounds throughout that ball.
The comparison functions are defined globally; their bounds on `V` are local. -/
theorem exists_memKI_bounds_on_closedBall [ProperSpace E] (V : E → ℝ) (r : ℝ)
    (hV : ContinuousOn V (Metric.closedBall 0 r))
    (hVnonneg : ∀ x ∈ Metric.closedBall (0 : E) r, 0 ≤ V x)
    (hVzero : ∀ x ∈ Metric.closedBall (0 : E) r, V x = 0 ↔ x = 0) :
    ∃ α₁ α₂ : ℝ≥0 → ℝ≥0, MemKI α₁ ∧ MemKI α₂ ∧
      ∀ x ∈ Metric.closedBall (0 : E) r,
        (α₁ ‖x‖₊ : ℝ) ≤ V x ∧ V x ≤ α₂ ‖x‖₊ :=
  exists_memKI_bounds_of_isCompact V (isCompact_closedBall _ _) hV hVnonneg hVzero

/-- **Global comparison lemma for a radially unbounded positive-definite function.**
Continuity, positive definiteness, and radial unboundedness yield global class-`K∞` norm
bounds in a proper normed space. Radial unboundedness is expressed by convergence to
`atTop` along the cocompact filter; in a proper normed space this means `V x → ∞` as
`‖x‖ → ∞`. -/
theorem exists_memKI_bounds_of_radiallyUnbounded [ProperSpace E] (V : E → ℝ)
    (hV : Continuous V) (hVnonneg : ∀ x, 0 ≤ V x)
    (hVzero : ∀ x, V x = 0 ↔ x = 0) (hV_top : Tendsto V (cocompact E) atTop) :
    ∃ α₁ α₂ : ℝ≥0 → ℝ≥0, MemKI α₁ ∧ MemKI α₂ ∧
      ∀ x, (α₁ ‖x‖₊ : ℝ) ≤ V x ∧ V x ≤ α₂ ‖x‖₊ := by
  have hzero : ∀ x, (V x).toNNReal = 0 ↔ ‖x‖₊ = 0 := by
    intro x
    rw [nnnorm_eq_zero]
    constructor
    · intro hz
      apply (hVzero x).mp
      exact le_antisymm (Real.toNNReal_eq_zero.mp hz) (hVnonneg x)
    · intro hz
      simp [(hVzero x).mpr hz]
  obtain ⟨α₁, α₂, hα₁, hα₂, hbound⟩ := exists_memKI_sandwich_of_coercive
    (fun x : E ↦ ‖x‖₊) (fun x ↦ (V x).toNNReal) (by fun_prop)
    (continuous_real_toNNReal.comp hV)
    (NNReal.tendsto_coe_atTop.mp tendsto_norm_cocompact_atTop)
    (Real.tendsto_toNNReal_atTop.comp hV_top) hzero
  refine ⟨α₁, α₂, hα₁, hα₂, fun x ↦ ?_⟩
  have h := hbound x
  have h₁ : (α₁ ‖x‖₊ : ℝ) ≤ ((V x).toNNReal : ℝ) := by exact_mod_cast h.1
  have h₂ : ((V x).toNNReal : ℝ) ≤ (α₂ ‖x‖₊ : ℝ) := by exact_mod_cast h.2
  simpa only [Real.coe_toNNReal _ (hVnonneg x)] using And.intro h₁ h₂

end PositiveDefiniteFun

end ComparisonFunction
