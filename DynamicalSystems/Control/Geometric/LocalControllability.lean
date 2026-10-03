/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.Kalman
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # First-order local controllability via linearization

This file formalises the *linearization principle* for continuous-time control
systems `ẋ = f x u`, following Sontag, *Mathematical Control Theory:
Deterministic Finite Dimensional Systems*, 2nd ed., 1998, Ch. 3 §3.7
(printed pp. 122–128; Definition 3.7.5, Remark 3.7.6 and Theorem 7).  This is the
linear precursor of the nonlinear (Lie-theoretic) controllability theory of
Chapter 4.

For a system with equilibrium `f 0 0 = 0` the **linearization** at the origin is
the pair `(A, B)` of Fréchet derivatives

`A = ∂ₓf(0,0) : X →L[ℝ] X`,   `B = ∂ᵤf(0,0) : U →L[ℝ] X`,

see `linearizationA` and `linearizationB`.  The pair is **controllable** when the
Kalman rank condition `rank [B AB ⋯ A^{n-1}B] = n` holds, equivalently when the
Kalman controllability map `LinearMap.kalmanControllabilityMap A B n` is
surjective (`LinearMap.isControllable_iff_surjective_kalmanControllabilityMap`).

Sontag's Theorem 7 (the "linearization principle") says that controllability of
`(A, B)` is *sufficient* for local controllability of the nonlinear system at the
origin.  The proof is the classical open-mapping argument: the end-point map
`Φ(x₀, u) = x(T)` is continuously differentiable and its partial differential
with respect to the control is the Kalman controllability map, which is onto by
controllability; the implicit/open mapping theorem then makes `Φ` locally
surjective, i.e. every sufficiently small target is reachable from every
sufficiently small initial state.

The differentiability of the end-point map and the identification of its control
derivative with the Kalman map are the regularity conclusions of Sontag
Theorem 1 (p. 57), which are not formalised here; they enter
`localControllability_of_linearization` as hypotheses on the end-point map,
exactly as in Sontag's proof.  The genuinely analytic content formalised here is
the open-mapping step: a strictly differentiable map whose derivative is
surjective is locally surjective (`HasStrictFDerivAt.map_nhds_eq_of_surj`).

## Control constraints

Only the unconstrained first-order problem is treated: controls are parameterised
by finitely many free values `Fin n → U` (the piecewise-constant controls used to
state the Kalman rank condition), so no control constraint set is imposed.  This
is the scope of Sontag §3.7; constrained versions belong to Chapter 4.

## Main definitions

* `linearizationA`, `linearizationB`: the Fréchet derivatives of the vector field
  with respect to state and control at the origin.
* `linearizationControllable`: controllability of the linearized pair.
* `LocallyControllableAt`: small-time local controllability at a point, stated
  through an end-point map.

## Main results

* `linearizationA_def`, `linearizationB_def`: the derivatives are definitionally
  the ones displayed above.
* `linearizationControllable_iff`: unfolding of the controllability predicate.
* `localControllability_of_linearization`: Sontag Theorem 7 (2), the
  linearization principle: a controllable linearization implies local
  controllability at the origin.

## References

* E. D. Sontag, *Mathematical Control Theory: Deterministic Finite Dimensional
  Systems*, 2nd ed., Springer, 1998, Ch. 3 §3.7, printed pp. 122–128.
-/

@[expose] public section

open Filter Set
open scoped Topology

variable {X U : Type*}

/-! ### The linearization of a control system -/

section LinearizationA

variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup U]

/-- The state linearization `A = ∂ₓf(0,0) : X →L[ℝ] X` of the control system
`ẋ = f x u` at the origin, i.e. the Fréchet derivative of `x ↦ f x 0` at `0`
(Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 3 §3.7, the
linearization appearing in Theorem 7). -/
noncomputable def linearizationA (f : X → U → X) : X →L[ℝ] X :=
  fderiv ℝ (fun x ↦ f x 0) 0

end LinearizationA

section Linearization

variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U]

omit [NormedSpace ℝ U] in
/-- Unfolding of the state linearization (definitional). -/
theorem linearizationA_def (f : X → U → X) :
    linearizationA f = fderiv ℝ (fun x ↦ f x 0) 0 := rfl

/-- The input linearization `B = ∂ᵤf(0,0) : U →L[ℝ] X` of the control system
`ẋ = f x u` at the origin, i.e. the Fréchet derivative of `u ↦ f 0 u` at `0`
(Sontag, *Mathematical Control Theory*, 2nd ed., 1998, Ch. 3 §3.7, the
linearization appearing in Theorem 7). -/
noncomputable def linearizationB (f : X → U → X) : U →L[ℝ] X :=
  fderiv ℝ (fun u ↦ f 0 u) 0

/-- Unfolding of the input linearization (definitional). -/
theorem linearizationB_def (f : X → U → X) :
    linearizationB f = fderiv ℝ (fun u ↦ f 0 u) 0 := rfl

/-- The linearization of `ẋ = f x u` at the origin is controllable: the Kalman
rank condition `rank [B AB ⋯ A^{n-1}B] = n` holds for
`A = ∂ₓf(0,0)` and `B = ∂ᵤf(0,0)` (Sontag, *Mathematical Control Theory*, 2nd
ed., 1998, Ch. 3 §3.7). -/
def linearizationControllable (f : X → U → X) : Prop :=
  LinearMap.IsControllable (linearizationA f).toLinearMap (linearizationB f).toLinearMap

/-- Unfolding of `linearizationControllable` in terms of the displayed Fréchet
derivatives. -/
theorem linearizationControllable_iff (f : X → U → X) :
    linearizationControllable f ↔
      LinearMap.IsControllable (fderiv ℝ (fun x ↦ f x 0) 0).toLinearMap
        (fderiv ℝ (fun u ↦ f 0 u) 0).toLinearMap :=
  Iff.rfl

end Linearization

/-! ### Local controllability -/

section Local

variable {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]

/-- **Small-time local controllability at a point.**  For a control system whose
end-point map is `Φ` (for the state/control data `p` near an equilibrium), this
says that `Φ` maps every neighbourhood of `p` onto a neighbourhood of `Φ p`.

Concretely, when `Φ(x₀, u) = x(T)` is the end-point map of `ẋ = f x u` and
`p = (0,0)`, `Φ p = 0`, the condition `map Φ (𝓝 p) = 𝓝 (Φ p)` asks that every
target `y` sufficiently close to `0` be attained as `Φ(x₀, u) = y` for some
`(x₀, u)` close to `(0,0)`.  Taking `y = 0` recovers Sontag's local
controllability at an equilibrium (Sontag, *Mathematical Control Theory*, 2nd
ed., 1998, Ch. 3 §3.7, Definition 3.7.5 and Remark 3.7.6): every nearby initial
state can be controlled to `0`, and the stronger formulation also reaches nearby
targets, all without leaving a neighbourhood of the origin. -/
def LocallyControllableAt (Φ : E → F) (p : E) : Prop :=
  map Φ (𝓝 p) = 𝓝 (Φ p)

/-- The continuity half of local controllability: `Φ` is continuous at `p`. -/
theorem LocallyControllableAt.tendsto {Φ : E → F} {p : E}
    (h : LocallyControllableAt Φ p) : Tendsto Φ (𝓝 p) (𝓝 (Φ p)) :=
  h.le

/-- The local-surjectivity half of local controllability: every neighbourhood of
`Φ p` is the image of a neighbourhood of `p`.  In control terms, every
sufficiently small target is reachable by a nearby choice of initial state and
control. -/
theorem LocallyControllableAt.exists_image_subset {Φ : E → F} {p : E}
    (h : LocallyControllableAt Φ p) {V : Set F} (hV : V ∈ 𝓝 (Φ p)) :
    ∃ W ∈ 𝓝 p, Φ '' W ⊆ V :=
  ⟨Φ ⁻¹' V, Filter.mem_map.mp (h.le hV), image_preimage_subset Φ V⟩

end Local

/-! ### The linearization principle -/

section Principle

variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]

/-- **First-order local controllability (Sontag Theorem 7, part 2).**  Let
`ẋ = f x u` be a control system with `f 0 0 = 0`, and let `Φ` be its end-point
map on the finitely many free control values `Fin n → U` with
`n = Module.finrank ℝ X`.  Assume `Φ` is strictly differentiable at `(0,0)` with
derivative `L`, and that the control component of `L` is the Kalman
controllability map of the linearization `(A, B) = (∂ₓf(0,0), ∂ᵤf(0,0))`:
`L (0, u) = kalmanControllabilityMap A B n u` for every `u`.

If the linearization is controllable, then the system is locally controllable at
the origin: `Φ` is locally surjective there, so every sufficiently small initial
state can be steered to `0` (indeed to any sufficiently small target).

The proof is Sontag's open-mapping argument: controllability makes the Kalman
map surjective, hence the derivative `L` — whose range already contains the
range of the Kalman map — is surjective, and
`HasStrictFDerivAt.map_nhds_eq_of_surj` converts a surjective strict derivative
into local surjectivity (Sontag, *Mathematical Control Theory*, 2nd ed., 1998,
Ch. 3 §3.7, Theorem 7). -/
theorem localControllability_of_linearization
    (f : X → U → X)
    (Φ : X × (Fin (Module.finrank ℝ X) → U) → X)
    (L : (X × (Fin (Module.finrank ℝ X) → U)) →L[ℝ] X)
    (hΦ : HasStrictFDerivAt Φ L (0, 0))
    (hderiv : ∀ u : Fin (Module.finrank ℝ X) → U,
      L (0, u) =
        LinearMap.kalmanControllabilityMap (linearizationA f).toLinearMap
          (linearizationB f).toLinearMap
          (Module.finrank ℝ X) u)
    (hcont : linearizationControllable f) :
    LocallyControllableAt Φ (0, 0) := by
  rw [LocallyControllableAt]
  have hsurj : Function.Surjective
      (LinearMap.kalmanControllabilityMap (linearizationA f).toLinearMap
        (linearizationB f).toLinearMap
        (Module.finrank ℝ X)) :=
    (LinearMap.isControllable_iff_surjective_kalmanControllabilityMap _ _).mp hcont
  have hrange : L.range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro x
    obtain ⟨u, hu⟩ := hsurj x
    exact ⟨(0, u), Eq.trans (hderiv u) hu⟩
  exact hΦ.map_nhds_eq_of_surj hrange

end Principle
