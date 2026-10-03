/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.LieBrackets
public import DynamicalSystems.Linear.Kalman
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Lie derivatives and feedback linearization

This file formalises the differential-geometric core of Sontag's
*Mathematical Control Theory*, Ch. 5 §5.3 "Feedback Linearization" (printed
pp. 197–207): the Lie derivative of a scalar function along a vector field and
the notion of feedback equivalence / feedback linearizability for a single-input
control-affine system `ẋ = f x + u g x` (Sontag, display (5.10)).

## Scope fence

Sontag's main result (Theorem 15, printed p. 200) is an *if and only if*
characterisation of feedback linearizability in terms of the involutivity of the
distribution `Δ_{n-1} = Δ(g, ad_f g, …, ad_f^{n-2} g)` and linear independence
of `g(x₀), …, ad_f^{n-1} g(x₀)`. The necessity direction requires Frobenius'
integrability theorem, which is not available in Mathlib (see the scope fence in
`DynamicalSystems.Control.Geometric.LieBrackets`), and the converse direction is
the relative-degree / Brunovsky normal-form computation. Both are out of scope
here.

This file is deliberately scoped to the *definitions* together with one genuine,
unconditional positive instance:

1. `lieDerivative f h`, the directional derivative of a scalar function `h`
   along the vector field `f` (the scalar counterpart of the Lie bracket of
   vector fields developed in `DynamicalSystems.Control.Geometric.LieBrackets`);
2. `feedbackLinearizable f g`, the (global, whole-space) predicate asserting the
   existence of an invertible `C¹` change of coordinates `T` and a nowhere
   vanishing affine feedback `u = α x + β x · v` bringing `ẋ = f x + u g x`
   into a *controllable single-input linear system* `ż = A z + v b` — this is
   Sontag's Definition 5.3.2 with the open neighborhoods `O, Õ` specialised to
   the whole space;
3. `integratorChain_feedbackLinearizable`, the positive instance: the
   `(n+1)`-dimensional chain of integrators `ẋ₁ = x₂, …, ẋ_n = x_{n+1},
   ẋ_{n+1} = u` is feedback linearizable, via the identity coordinate change
   `T = id` and the trivial feedback `u = v` (`α = 0`, `β = 1`). The only real
   content is the controllability of the companion/shift pair
   `(A, b)`, which is proved directly here.

The linear case (a controllable linear system is feedback equivalent to a chain
of integrators) is the honest tractable case of feedback linearization; the
general nonlinear relative-degree theorem is not formalised.

## Main definitions

* `lieDerivative`: `(L_f h)(x) = D h(x) (f x)`.
* `feedbackLinearizable`: existence of a linearising diffeomorphism and affine
  feedback onto a controllable single-input linear system.

## Main results

* `lieDerivative_apply`, `lieDerivative_comp`, `lieDerivative_const`.
* `integratorChain_isControllable`: the companion/shift pair of the chain of
  integrators is controllable.
* `integratorChain_feedbackLinearizable`: the chain of integrators is feedback
  linearizable.

## References

* E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional
  Systems*, 2nd ed., Springer, 1998, Ch. 5 §5.3, printed pp. 197–207.
-/

@[expose] public section

open scoped Topology ContDiff

noncomputable section

/-! ## Lie derivatives of scalar functions -/

section LieDerivative

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The Lie derivative of a scalar function `h : X → ℝ` along the vector field
`f : X → X`, defined by the directional derivative
`(L_f h)(x) = D h(x) (f x)` (Sontag, §5.3; the scalar counterpart of the Lie
bracket of vector fields, cf. display (4.3)). -/
def lieDerivative (f : X → X) (h : X → ℝ) : X → ℝ :=
  fun x ↦ fderiv ℝ h x (f x)

/-- Unfolding of `lieDerivative`: `(L_f h)(x) = D h(x) (f x)`. -/
theorem lieDerivative_apply (f : X → X) (h : X → ℝ) (x : X) :
    lieDerivative f h x = fderiv ℝ h x (f x) :=
  rfl

/-- Chain rule for the Lie derivative: composing the scalar function `h` with a
map `T` precomposes the derivative with `DT`,
`L_f (h ∘ T)(x) = Dh(T x) (DT(x) (f x))`. This is the infinitesimal form of the
conjugation `L_f (h ∘ T) = L_{T_* f} h ∘ T` used when transforming a control
system under a change of coordinates (Sontag, (5.11)–(5.12)). -/
theorem lieDerivative_comp (f T : X → X) (h : X → ℝ) (x : X)
    (hh : DifferentiableAt ℝ h (T x)) (hT : DifferentiableAt ℝ T x) :
    lieDerivative f (h ∘ T) x = fderiv ℝ h (T x) (fderiv ℝ T x (f x)) := by
  rw [lieDerivative_apply, fderiv_comp x hh hT, ContinuousLinearMap.comp_apply]

/-- The Lie derivative of a constant scalar function vanishes. -/
theorem lieDerivative_const (f : X → X) (c : ℝ) :
    lieDerivative f (fun _ : X ↦ c) = 0 := by
  ext x
  rw [lieDerivative_apply, fderiv_const_apply]
  rfl

/-- Additivity of the Lie derivative in the scalar function. -/
theorem lieDerivative_add (f : X → X) (h₁ h₂ : X → ℝ) (x : X)
    (hh₁ : DifferentiableAt ℝ h₁ x) (hh₂ : DifferentiableAt ℝ h₂ x) :
    lieDerivative f (h₁ + h₂) x = lieDerivative f h₁ x + lieDerivative f h₂ x := by
  rw [lieDerivative_apply, lieDerivative_apply, lieDerivative_apply,
    fderiv_add hh₁ hh₂]
  rfl

/-- The Lie derivative of a continuous linear functional `ℓ` along a vector
field `g` is the evaluation `ℓ (g x)`. -/
theorem lieDerivative_linear (g : X → X) (ℓ : X →L[ℝ] ℝ) (x : X) :
    lieDerivative g ℓ x = ℓ (g x) := by
  rw [lieDerivative_apply, ContinuousLinearMap.fderiv]

/-- **The Lie derivative is the scalar counterpart of the Lie bracket.** For a
continuous linear functional `ℓ : X →L[ℝ] ℝ`,
`L_{[f,g]} ℓ = L_f (L_g ℓ) - L_g (L_f ℓ)` at every point where `f` and `g` are
differentiable. This is the scalar case of Sontag's operator identity
`L_{ad_f g} h = L_f L_g h - L_g L_f h` (display (4.3)), and shows that the Lie
derivative is not an independent notion from the bracket
`lieBracket` developed in `DynamicalSystems.Control.Geometric.LieBrackets`. -/
theorem lieDerivative_lieBracket_linear (f g : X → X) (ℓ : X →L[ℝ] ℝ) (x : X)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    lieDerivative (lieBracket f g) ℓ x =
      lieDerivative f (lieDerivative g ℓ) x - lieDerivative g (lieDerivative f ℓ) x := by
  rw [lieDerivative_linear]
  have h₁ : lieDerivative f (lieDerivative g ℓ) x = ℓ (fderiv ℝ g x (f x)) := by
    have hℓ : lieDerivative g ℓ = fun y ↦ ℓ (g y) := by
      ext y; rw [lieDerivative_linear]
    rw [hℓ, lieDerivative_apply]
    change (fderiv ℝ (ℓ ∘ g) x) (f x) = ℓ ((fderiv ℝ g x) (f x))
    rw [fderiv_comp x ℓ.differentiableAt hg, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.fderiv]
  have h₂ : lieDerivative g (lieDerivative f ℓ) x = ℓ (fderiv ℝ f x (g x)) := by
    have hℓ : lieDerivative f ℓ = fun y ↦ ℓ (f y) := by
      ext y; rw [lieDerivative_linear]
    rw [hℓ, lieDerivative_apply]
    change (fderiv ℝ (ℓ ∘ f) x) (g x) = ℓ ((fderiv ℝ f x) (g x))
    rw [fderiv_comp x ℓ.differentiableAt hf, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.fderiv]
  rw [h₁, h₂, lieBracket_apply, map_sub]

end LieDerivative

/-! ## Feedback equivalence and feedback linearizability -/

section FeedbackLinearizable

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- **Feedback linearizability** of the single-input control-affine system
`ẋ = f x + u g x` (Sontag, Definition 5.3.2, printed p. 198).

This is the *global, whole-space* version of Sontag's definition: there exist

* a controllable single-input linear system `ż = A z + v b`, i.e. an endomorphism
  `A : X →L[ℝ] X` and a direction `b : X` with `IsControllable A (· • b)`;
* an invertible `C¹` change of coordinates `T : X → X` with inverse `Tinv`
  (`Tinv ∘ T = id` and `T ∘ Tinv = id`), both `C¹`;
* `C¹` feedback coefficients `α, β : X → ℝ` with `β` nowhere zero,

such that for every `x` the two feedback-equivalence identities
`T_*(x)(f x + α x · g x) = A (T x)` and `β x · T_*(x)(g x) = b` hold
(Sontag, displays (5.11)–(5.12), with the target dynamics `f̃ = A ·`, `g̃ = b`).

Sontag states the local version: `O ⊆ X` and `Õ ⊆ ℝⁿ` are open neighborhoods
and `T : O → Õ` is a local diffeomorphism. Specialising `O = X` and `Õ = X`
gives the predicate below; it is the natural home for the global linear
examples formalised here. The general nonlinear theorem (relative degree /
Brunovsky form, Sontag Theorem 15) is deliberately not asserted. -/
def feedbackLinearizable (f g : X → X) : Prop :=
  ∃ (A : X →L[ℝ] X) (b : X),
    LinearMap.IsControllable A.toLinearMap (LinearMap.toSpanSingleton ℝ X b) ∧
    ∃ (T Tinv : X → X) (α β : X → ℝ),
      Function.LeftInverse Tinv T ∧ Function.RightInverse Tinv T ∧
      ContDiff ℝ 1 T ∧ ContDiff ℝ 1 Tinv ∧ ContDiff ℝ 1 α ∧ ContDiff ℝ 1 β ∧
      (∀ x, β x ≠ 0) ∧
      (∀ x, fderiv ℝ T x (f x + α x • g x) = A (T x)) ∧
      (∀ x, β x • fderiv ℝ T x (g x) = b)

end FeedbackLinearizable

/-! ## The chain of integrators

We model the `(n+1)`-dimensional single-input chain of integrators
`ẋ₁ = x₂, …, ẋ_n = x_{n+1}, ẋ_{n+1} = u` on the coordinate space
`Fin (n+1) → ℝ`. The state map is the companion/shift operator `A` with
`A e_k = e_{k+1}` for `k < n` and `A e_n = 0`, and the input direction is
`b = e_0`. Its controllability is the linear-algebraic content of the feedback
linearization statement. -/

section IntegratorChain

/-- The state map of the `(n+1)`-dimensional chain of integrators, the
companion/shift operator with `(A x) i = x (i - 1)` (with `x (-1) = 0`), i.e.
`A e_k = e_{k+1}` for `k < n` and `A e_n = 0`. -/
def integratorChainA (n : ℕ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun x := fun i ↦ ∑ j : Fin (n + 1),
    (if (i : ℕ) = (j : ℕ) + 1 then (1 : ℝ) else 0) * x j
  map_add' x y := by
    ext i
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- The input direction of the chain of integrators: the first standard basis
vector `b = e_0` of `Fin (n+1) → ℝ`. -/
def integratorChainB (n : ℕ) : ℝ →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
  LinearMap.toSpanSingleton ℝ (Fin (n + 1) → ℝ) (Pi.single 0 1)

/-- Unfolding of `integratorChainA` as a coordinate sum. -/
theorem integratorChainA_apply (n : ℕ) (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    integratorChainA n x i = ∑ j : Fin (n + 1),
      (if (i : ℕ) = (j : ℕ) + 1 then (1 : ℝ) else 0) * x j :=
  rfl

/-- The action of the shift operator on a standard basis vector. -/
theorem integratorChainA_apply_single (n : ℕ) (k : Fin (n + 1)) (c : ℝ)
    (i : Fin (n + 1)) :
    integratorChainA n (Pi.single k c) i =
      (if (i : ℕ) = (k : ℕ) + 1 then c else 0) := by
  rw [integratorChainA_apply, Finset.sum_eq_single k]
  · by_cases hi : (i : ℕ) = (k : ℕ) + 1 <;> simp [hi]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, mul_zero]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- The shift operator moves the `k`-th standard basis vector to the
`(k+1)`-st one. -/
theorem integratorChainA_single_succ (n : ℕ) (k : Fin (n + 1))
    (hk : (k : ℕ) + 1 < n + 1) :
    integratorChainA n (Pi.single k 1) =
      Pi.single (⟨(k : ℕ) + 1, hk⟩ : Fin (n + 1)) 1 := by
  ext i
  rw [integratorChainA_apply_single]
  by_cases hi : (i : ℕ) = (k : ℕ) + 1
  · rw [ite_eq_left hi, show i = (⟨(k : ℕ) + 1, hk⟩ : Fin (n + 1)) from Fin.ext hi,
      Pi.single_eq_same]
  · rw [ite_eq_right hi]
    symm
    rw [Pi.single_eq_of_ne (fun h : i = (⟨(k : ℕ) + 1, hk⟩ : Fin (n + 1)) ↦
      hi (by rw [h]))]

/-- The shift operator annihilates the last standard basis vector. -/
theorem integratorChainA_single_last (n : ℕ) (k : Fin (n + 1))
    (hk : ¬ (k : ℕ) + 1 < n + 1) :
    integratorChainA n (Pi.single k 1) = 0 := by
  ext i
  rw [integratorChainA_apply_single, ite_eq_right (fun hi : (i : ℕ) = (k : ℕ) + 1 ↦
    hk (by rw [← hi]; exact i.2))]
  rfl

/-- The Krylov vectors of the chain of integrators: the `k`-th power of the
shift operator applied to `e₀` is the `k`-th standard basis vector. -/
theorem integratorChainA_pow_single (n : ℕ) (k : ℕ) (hk : k < n + 1) :
    (integratorChainA n ^ k) (Pi.single 0 (1 : ℝ)) = Pi.single ⟨k, hk⟩ 1 := by
  induction k with
  | zero =>
    simp only [pow_zero, Module.End.one_apply]
    rw [show (0 : Fin (n + 1)) = (⟨0, hk⟩ : Fin (n + 1)) from Fin.ext rfl]
  | succ k ih =>
    have hk' : k < n + 1 := Nat.lt_of_succ_lt hk
    rw [pow_succ']
    change integratorChainA n ((integratorChainA n ^ k) (Pi.single 0 (1 : ℝ))) =
      Pi.single (⟨k + 1, hk⟩ : Fin (n + 1)) 1
    rw [ih hk']
    exact integratorChainA_single_succ n ⟨k, hk'⟩ hk

/-- **The chain of integrators is a controllable single-input linear system.**
The reachable subspace is spanned by the standard basis vectors
`e_k = A^k e₀`, hence is the whole state space. -/
theorem integratorChain_isControllable (n : ℕ) :
    LinearMap.IsControllable (integratorChainA n) (integratorChainB n) := by
  rw [LinearMap.isControllable_iff, eq_top_iff]
  intro x _
  have hx : x = ∑ i : Fin (n + 1), x i • Pi.single i (1 : ℝ) := by
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j]
    · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · intro i _ hi
      rw [Pi.smul_apply, Pi.single_eq_of_ne hi.symm, smul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [hx]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  have hi : (integratorChainA n ^ (i : ℕ)) (Pi.single 0 (1 : ℝ)) = Pi.single i 1 :=
    integratorChainA_pow_single n (i : ℕ) i.2
  have hmem : (integratorChainA n ^ (i : ℕ)) (Pi.single 0 (1 : ℝ)) ∈
      LinearMap.reachableSubspace (integratorChainA n) (integratorChainB n) := by
    simpa [integratorChainB, LinearMap.toSpanSingleton_apply_one] using
      LinearMap.mem_reachableSubspace_of_mem (integratorChainA n) (integratorChainB n)
        (i : ℕ) 1
  rw [← hi]
  exact hmem

/-- **The chain of integrators is feedback linearizable.** The identity change
of coordinates `T = id` and the trivial feedback `u = v` (`α = 0`, `β = 1`)
bring the system into the — already linear, controllable — companion form
`ż = A z + v b`. This is the linear case of Sontag's §5.3. -/
theorem integratorChain_feedbackLinearizable (n : ℕ) :
    feedbackLinearizable
      (fun x : Fin (n + 1) → ℝ ↦ integratorChainA n x)
      (fun _ : Fin (n + 1) → ℝ ↦ integratorChainB n 1) := by
  refine ⟨(integratorChainA n).toContinuousLinearMap, Pi.single 0 (1 : ℝ), ?_,
    id, id, (fun _ ↦ (0 : ℝ)), (fun _ ↦ (1 : ℝ)),
    fun _ ↦ rfl, fun _ ↦ rfl, contDiff_id, contDiff_id, contDiff_const, contDiff_const,
    (fun _ ↦ one_ne_zero), ?_, ?_⟩
  · simpa [integratorChainB] using integratorChain_isControllable n
  · intro x
    simp only [fderiv_id, ContinuousLinearMap.id_apply, zero_smul, add_zero]
    rfl
  · intro x
    simp only [one_smul, fderiv_id, ContinuousLinearMap.id_apply]
    simp [integratorChainB]

end IntegratorChain
