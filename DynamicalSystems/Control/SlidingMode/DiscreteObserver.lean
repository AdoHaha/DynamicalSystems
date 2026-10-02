/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.SlidingMode.LMI
public import DynamicalSystems.DiscreteTime.Basic

/-! # Observer-based output-feedback discrete-time sliding-mode control

This file formalizes the *observer-based* output-feedback DSMC of A. Argha,
S. W. Su, L. Li and H. T. Nguyen, *Advances in Discrete-Time Sliding Mode
Control: Theory and Applications*, CRC Press 2018, Chapter 3, §3.2–3.3
(printed pp. 53–60). The plant is the uncertain discrete-time system

`x(k + 1) = [A + ΔA(k)] x(k) + B [u(k) + f(k)]`,  `y(k) = C x(k)`

of eq. (3.1), printed p. 53, with `x(k) ∈ ℝⁿ`, `u(k) ∈ ℝᵐ` and `y(k) ∈ ℝᵖ`
(`m ≤ p ≤ n`). Only the *nominal, disturbance-free* linear part is treated here;
the Lipschitz disturbance assumption 3.1 and the uncertainty `ΔA = M F N` are
part of the LMI input and are not formalized.

The state and disturbance observer of eq. (3.3), printed p. 53, is

`x̂(k + 1) = A x̂(k) + B u(k) + L₁ [y(k) - ŷ(k)] + B f̂(k)`,

`f̂(k + 1) = f̂(k) + L₂ [y(k) - ŷ(k)]`,  `ŷ(k) = C x̂(k)`.

Following the task statement (and the disturbance-free reduction of the book),
this slice keeps only the state part with a single output-injection gain `L`, so
the observer becomes the discrete Luenberger observer

`x̂(k + 1) = A x̂(k) + B u(k) + L (y(k) - C x̂(k))`,

the `L = L₁`, `f̂ = 0` instance of (3.3). The *observation error*
`e(k) = x̂(k) - x(k)` obeys the homogeneous recursion `e(k + 1) = (A - L C) e(k)`
— the discrete counterpart of `LinearSystem.observerError_dynamics` in
`DynamicalSystems.Linear.Observer`. As in the continuous theory, the error
recursion is independent of the input `u` and of any state feedback built on the
estimate (the *separation* structure).

The sliding function of §3.3 is the linear state-space function

`σ(k) = S x(k)`,  `S = Bᵀ P₁`  (eq. (3.6), printed p. 54),

associated with the surface `{x | S x = 0}` (`dsmcOutputFeedbackSurface`). In
the output-feedback setting the controller (3.9)–(3.10), printed p. 55, uses the
*estimate* `x̂` and drives `σ` to zero in one step up to the stable factor
`Φ = λ I`; unlike the continuous-time case the equivalent controller already
forces the state onto the surface and keeps it there (the observation of [67]
recalled on printed p. 55).

## Main results

* `dsmcObserver`: the discrete Luenberger observer one-step map.
* `dsmcObserverError`: the observation error `e = x̂ - x`.
* `dsmcObserverError_dynamics`: the algebraic error recursion
  `e(k + 1) = (A - L C) e(k)`; `B u` and the measured output cancel exactly.
* `dsmcObserverError_separation`: the error recursion is the same for every
  input (separation of the observer and the control design).
* `dsmcDiscreteFlow_mulVec`, `dsmcObserverError_solution` and
  `dsmcObserverError_flow`: the error solution `e(k) = (A - L C)^k e(0)`, with the
  `discreteFlow` bridge (no new flow is introduced).
* `dsmcOutputFeedbackSurface`: the sliding surface `{x | Bᵀ P₁ x = 0}`.
* `dsmcOutputFeedbackClosedLoop`, `dsmcOutputFeedbackLyapunov` and
  `dsmcOutputFeedbackLMI`: the augmented state/error closed loop, its
  block-diagonal Lyapunov matrix and the LMI-coupled matrix inequality.
* `dsmc_outputFeedback_stability_of_lmi`: **the implication** "the coupled LMI
  holds `⇒` the output-feedback closed loop is quadratically stable", i.e. the
  block-diagonal quadratic Lyapunov function decays geometrically; the one-step
  core is `dsmc_outputFeedback_decrease_of_lmi`. As in the whole campaign,
  feasibility of the LMI is *assumed*, not proved.

## Implementation notes and boundaries

The book's Theorem 3.1 (LMI (3.14), printed p. 56) is a seven-block-row LMI in
`P₁ ≻ 0`, `Q₂ ≻ 0`, the free matrices `X₁, X₂, X₃`, the scalars `ε, ρ` and the
uncertainty factors `M, N`. This file encodes its *Schur-complement core*: the
matrix inequality `P - A_clᵀ P A_cl ≻ 0` on the augmented output-feedback closed
loop `A_cl`, with the block-diagonal Lyapunov matrix `P = diag(P₁, Q₂)`. The
free variables `X₁, X₂, X₃`, the scalars `ε, ρ`, the uncertainty `ΔA = M F N`
and the disturbance estimator `f̂` are not encoded. The inequality is the
coupling obtained from the book after its repeated Schur reductions
(3.22)–(3.27), printed pp. 58–59, and it is a *hypothesis*; neither the
feasibility of the literal (3.14) nor the observer-gain formula
`[L₁; L₂] = Q₂⁻¹ X₃` of (3.15), printed p. 56, is claimed.

The book defines the estimation error in the opposite sign, `e(k) = x(k) - x̂(k)`
(printed p. 55, after eq. (3.11)); the task statement and this file use
`e(k) = x̂(k) - x(k)`. Since `A - L C` is linear, both conventions lead to the
same error map `(A - L C)`, so this is a sign convention and not a mathematical
correction.

The book's hypotheses that `(A, B)` is controllable and `(A, C)` is observable
(printed p. 53) and its Assumption 3.2 (no transmission zero at `1`) are *not*
used as Lean hypotheses: at the matrix level the existence of the coupled LMI
feasible solution is the formal substitute, exactly as the existence of a
Lyapunov matrix substitutes for a spectral Schur condition. In particular the
continuous-time `Linear.LyapunovEquation.IsHurwitz` / `Linear.Stabilization`
detectability predicates are **not** reused: they are `Re λ < 0` notions,
whereas discrete-time stability is the Schur condition `|λ| < 1`. The
observability/detectability vocabulary of `DynamicalSystems.Linear.Observer` is
mirrored conceptually, but the discrete formalization works with the matrix
inequality above.
-/

@[expose] public section

open Matrix

variable {n m p : ℕ}

/-! ## The discrete Luenberger observer and its error -/

/-- The **discrete Luenberger observer** one-step map
`x̂ ↦ A x̂ + B u + L (y - C x̂)` of A. Argha, S. W. Su, L. Li and H. T. Nguyen,
*Advances in Discrete-Time Sliding Mode Control: Theory and Applications*,
CRC Press 2018, eq. (3.3), printed p. 53, reduced to its state part
(`f̂ = 0`, single gain `L = L₁`). -/
noncomputable def dsmcObserver (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (L : Matrix (Fin n) (Fin p) ℝ) (C : Matrix (Fin p) (Fin n) ℝ)
    (u : Fin m → ℝ) (y : Fin p → ℝ) (xhat : Fin n → ℝ) : Fin n → ℝ :=
  A *ᵥ xhat + B *ᵥ u + L *ᵥ (y - C *ᵥ xhat)

/-- The **observation error** `e = x̂ - x` between the observer estimate `x̂` and
the plant state `x` (A. Argha, S. W. Su, L. Li and H. T. Nguyen, *Advances in
Discrete-Time Sliding Mode Control: Theory and Applications*, CRC Press 2018,
§3.3, printed p. 55). The book writes `e = x - x̂`; see the module docstring for
the sign convention. -/
def dsmcObserverError (xhat x : Fin n → ℝ) : Fin n → ℝ := xhat - x

/-- **Discrete observer error dynamics.** If the plant reads
`x' = A x + B u` and the output is exact, `y = C x`, then the observer error
`e = x̂ - x` of `dsmcObserver` satisfies the homogeneous recursion

`e' = (A - L C) e`.

Both the input term `B u` and the measured output `C x` cancel exactly, so the
error is driven only by the output injection `L`. This is the discrete
counterpart of the pointwise identity `LinearSystem.observerError_dynamics` of
`DynamicalSystems.Linear.Observer` and the matrix form of the observation-error
block `e_a(k + 1) = (A_a - L_a C_a) e_a(k)` of A. Argha, S. W. Su, L. Li and
H. T. Nguyen, *Advances in Discrete-Time Sliding Mode Control: Theory and
Applications*, CRC Press 2018, eq. (3.12), printed p. 55. -/
theorem dsmcObserverError_dynamics (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (L : Matrix (Fin n) (Fin p) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (u : Fin m → ℝ) (xhat x : Fin n → ℝ) :
    dsmcObserverError (dsmcObserver A B L C u (C *ᵥ x) xhat) (A *ᵥ x + B *ᵥ u)
      = (A - L * C) *ᵥ dsmcObserverError xhat x := by
  unfold dsmcObserverError dsmcObserver
  simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec]
  abel

/-- **Observer error dynamics under estimate feedback.** When the observer-based
controller applies `u = K x̂` from the estimate, the error still obeys
`e' = (A - L C) e` with no residual dependence on the feedback gain `K`. This
is the discrete counterpart of
`LinearSystem.observerError_dynamics_stateFeedback` and the algebraic content of
the separation principle recalled in A. Argha, S. W. Su, L. Li and H. T. Nguyen,
*Advances in Discrete-Time Sliding Mode Control: Theory and Applications*,
CRC Press 2018, §3.3, printed p. 55. -/
theorem dsmcObserverError_dynamics_stateFeedback (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (L : Matrix (Fin n) (Fin p) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (K : Matrix (Fin m) (Fin n) ℝ) (xhat x : Fin n → ℝ) :
    dsmcObserverError (dsmcObserver A B L C (K *ᵥ xhat) (C *ᵥ x) xhat)
        (A *ᵥ x + B *ᵥ (K *ᵥ xhat))
      = (A - L * C) *ᵥ dsmcObserverError xhat x :=
  dsmcObserverError_dynamics A B L C (K *ᵥ xhat) xhat x

/-- **Separation of the observer and the control design.** The observer error at
the next step is the same for *any* two input histories: the estimate-feedback
design and the output-injection design do not interact. This restates the
discrete separation principle and mirrors
`LinearSystem.separation_error_independent_of_feedback` of
`DynamicalSystems.Linear.Observer`; it is the error-dynamics observation behind
A. Argha, S. W. Su, L. Li and H. T. Nguyen, *Advances in Discrete-Time Sliding
Mode Control: Theory and Applications*, CRC Press 2018, eq. (3.12), printed
p. 55. -/
theorem dsmcObserverError_separation (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (L : Matrix (Fin n) (Fin p) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (u₁ u₂ : Fin m → ℝ) (xhat x : Fin n → ℝ) :
    dsmcObserverError (dsmcObserver A B L C u₁ (C *ᵥ x) xhat) (A *ᵥ x + B *ᵥ u₁)
      = dsmcObserverError (dsmcObserver A B L C u₂ (C *ᵥ x) xhat) (A *ᵥ x + B *ᵥ u₂) := by
  rw [dsmcObserverError_dynamics, dsmcObserverError_dynamics]

/-! ## The error solution by discrete iteration

The error recursion is a linear map `e ↦ M *ᵥ e` with `M = A - L C`. Its solution
is the matrix power `Mᵏ` applied to the initial error; the iterate is Mathlib's
`discreteFlow` of `DynamicalSystems.DiscreteTime.Basic`, which is not
redefined. -/

/-- **Matrix powers are the discrete flow of the multiplication map.** The `k`-th
iterate of `e ↦ M *ᵥ e` is `e ↦ (M ^ k) *ᵥ e`. This records the bridge between
`DynamicalSystems.DiscreteTime.Basic.discreteFlow` and matrix powers used for
the observer error solution of eq. (3.12), printed p. 55; no new flow is
introduced. -/
theorem dsmcDiscreteFlow_mulVec (M : Matrix (Fin n) (Fin n) ℝ) (k : ℕ) (x : Fin n → ℝ) :
    discreteFlow (fun x ↦ M *ᵥ x) k x = (M ^ k) *ᵥ x := by
  have h : (fun x ↦ M *ᵥ x)^[k] x = (M ^ k) *ᵥ x := by
    induction k generalizing x with
    | zero => simp
    | succ k ih =>
        rw [Function.iterate_succ_apply', ih, Matrix.mulVec_mulVec, pow_succ']
  simpa only [discreteFlow] using h

/-- **Solution of the discrete observer error recursion.** If a sequence
`e : ℕ → ℝⁿ` satisfies `e (k + 1) = M *ᵥ e k`, then `e k = Mᵏ *ᵥ e 0`. For the
observer error of `dsmcObserverError_dynamics` the matrix is `M = A - L C`. This
is the discrete counterpart of the exponential error flow `e^{t(A - LC)} e(0)` of
the continuous Luenberger observer and the solution form of the error block
`e_a(k + 1) = (A_a - L_a C_a) e_a(k)` of A. Argha, S. W. Su, L. Li and
H. T. Nguyen, *Advances in Discrete-Time Sliding Mode Control: Theory and
Applications*, CRC Press 2018, eq. (3.12), printed p. 55. -/
theorem dsmcObserverError_solution (M : Matrix (Fin n) (Fin n) ℝ) (e : ℕ → Fin n → ℝ)
    (h : ∀ k, e (k + 1) = M *ᵥ e k) (k : ℕ) :
    e k = (M ^ k) *ᵥ e 0 := by
  induction k with
  | zero => simp
  | succ k ih => rw [h k, ih, Matrix.mulVec_mulVec, pow_succ']

/-- **Solution of the discrete observer error recursion, flow form.** The error
solution is the `k`-th iterate of the linear map `e ↦ M *ᵥ e` applied to the
initial error, i.e. `discreteFlow (fun x ↦ M *ᵥ x) k (e 0)`. This restates
`dsmcObserverError_solution` through the `discreteFlow` bridge
`dsmcDiscreteFlow_mulVec` of `DynamicalSystems.DiscreteTime.Basic` and is the
iterated form of the error block of eq. (3.12), printed p. 55. -/
theorem dsmcObserverError_flow (M : Matrix (Fin n) (Fin n) ℝ) (e : ℕ → Fin n → ℝ)
    (h : ∀ k, e (k + 1) = M *ᵥ e k) (k : ℕ) :
    e k = discreteFlow (fun x ↦ M *ᵥ x) k (e 0) := by
  rw [dsmcObserverError_solution M e h k, dsmcDiscreteFlow_mulVec]

/-- The error solution specialised to the observer error matrix `A - L C` of
`dsmcObserverError_dynamics`: `e k = (A - L C)ᵏ *ᵥ e 0`, the matrix-power form of
the observation-error block of eq. (3.12), printed p. 55. -/
theorem dsmcObserverError_solution_dynamics (A : Matrix (Fin n) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin p) ℝ) (C : Matrix (Fin p) (Fin n) ℝ) (e : ℕ → Fin n → ℝ)
    (h : ∀ k, e (k + 1) = (A - L * C) *ᵥ e k) (k : ℕ) :
    e k = ((A - L * C) ^ k) *ᵥ e 0 :=
  dsmcObserverError_solution (A - L * C) e h k

/-- **Geometric decay of the observer error.** If the observer-error matrix
`A - L C` admits a positive-definite Lyapunov matrix `Q₂` with
`Q₂ - (A - L C)ᵀ Q₂ (A - L C) ≻ 0`, then the observer error quadratic form decays
geometrically, `quadForm Q₂ ((A - L C)ᵏ e₀) ≤ cᵏ quadForm Q₂ e₀` with
`c ∈ [0, 1)`. This is the observer-specific instance of the discrete Lyapunov
LMI implication `dsmc_lmi_geometric_decay` of
`DynamicalSystems.Control.SlidingMode.LMI`, and it is the `e_a`-block content of
the stability analysis of A. Argha, S. W. Su, L. Li and H. T. Nguyen, *Advances
in Discrete-Time Sliding Mode Control: Theory and Applications*, CRC Press 2018,
Theorem 3.1, printed p. 56. As elsewhere, the LMI is an assumption and no
feasibility is proved. -/
theorem dsmcObserverError_decay (A : Matrix (Fin n) (Fin n) ℝ)
    (L : Matrix (Fin n) (Fin p) ℝ) (C : Matrix (Fin p) (Fin n) ℝ)
    {Q₂ : Matrix (Fin n) (Fin n) ℝ} (hQ₂ : Q₂.PosDef)
    (hLMI : (Q₂ - (A - L * C)ᵀ * Q₂ * (A - L * C)).PosDef) (hne : Nonempty (Fin n)) :
    ∃ c, 0 ≤ c ∧ c < 1 ∧ ∀ (k : ℕ) (e₀ : Fin n → ℝ),
      quadForm Q₂ (((A - L * C) ^ k) *ᵥ e₀) ≤ c ^ k * quadForm Q₂ e₀ :=
  dsmc_lmi_geometric_decay hQ₂ hLMI hne

/-! ## The output-feedback sliding surface

The book's sliding function is `σ(k) = S x(k)` with `S = Bᵀ P₁` (eq. (3.6),
printed p. 54). Its zero set is the state-space sliding surface of the
output-feedback DSMC. It reuses the sliding-variable vocabulary
`dsmcSlidingVariable` of `DynamicalSystems.Control.SlidingMode.DiscreteMatrix`. -/

/-- The **output-feedback discrete sliding surface** `{x | Bᵀ P₁ x = 0}` of
A. Argha, S. W. Su, L. Li and H. T. Nguyen, *Advances in Discrete-Time Sliding
Mode Control: Theory and Applications*, CRC Press 2018, eq. (3.6), printed p. 54,
with the surface matrix `S = Bᵀ P₁` and `P₁ ≻ 0` the Lyapunov matrix designed by
the LMI (3.14). Remark 3.1 (printed p. 54) stresses that, for the
output-feedback DSMC, the sliding function need not be known in the output space;
it is a surface in the state space. -/
def dsmcOutputFeedbackSurface (B : Matrix (Fin n) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {x | (Bᵀ * P) *ᵥ x = 0}

/-- Membership in the output-feedback surface is the vanishing of the sliding
variable `dsmcSlidingVariable (Bᵀ P) x` of
`DynamicalSystems.Control.SlidingMode.DiscreteMatrix`. Thus `dsmcOutputFeedbackSurface B P`
is exactly the zero set `{x | dsmcSlidingVariable (Bᵀ P) x = 0}` of the surface
of eq. (3.6), printed p. 54. -/
theorem mem_dsmcOutputFeedbackSurface (B : Matrix (Fin n) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    x ∈ dsmcOutputFeedbackSurface B P ↔ dsmcSlidingVariable (Bᵀ * P) x = 0 :=
  Iff.rfl

/-- **Invariance of the output-feedback surface under the equivalent closed
loop.** Let `S = Bᵀ P` be the sliding surface matrix and suppose `S B` is
invertible. Then the equivalent closed loop
`dsmcEquivalentClosedLoop A B S = A - B (S B)⁻¹ S A` of
`DynamicalSystems.Control.SlidingMode.DiscreteMatrix` maps the surface
`dsmcOutputFeedbackSurface B P` into itself. This reuses
`dsmcEquivalentClosedLoop_slidingVariable` and exhibits the surface of eq. (3.6),
printed p. 54, as the invariant ideal-sliding manifold of A. Argha, S. W. Su,
L. Li and H. T. Nguyen, *Advances in Discrete-Time Sliding Mode Control: Theory
and Applications*, CRC Press 2018, §3.3, eq. (3.7), printed p. 54. -/
theorem dsmcOutputFeedbackSurface_invariant (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hb : IsUnit ((Bᵀ * P) * B).det) (x : Fin n → ℝ) :
    dsmcEquivalentClosedLoop A B (Bᵀ * P) *ᵥ x ∈ dsmcOutputFeedbackSurface B P := by
  rw [mem_dsmcOutputFeedbackSurface]
  exact dsmcEquivalentClosedLoop_slidingVariable A B (Bᵀ * P) hb x

/-! ## The LMI-coupled output-feedback closed loop

In the coordinates `(x, e)` with `e = x̂ - x`, the estimate-feedback plant
`x' = A x + B K x̂` together with the observer error `e' = (A - L C) e` becomes
the *block lower-triangular* coupled system

`[x'; e'] = [[A + B K, B K], [0, A - L C]] [x; e]`,

which is eq. (3.12), printed p. 55, in its disturbance-free linear part. The
`(1,1)` block collects the state feedback and the `(1,2)` block is the coupling
of the state dynamics to the estimation error; the `(2,1)` block vanishes — the
separation structure. The LMI of Theorem 3.1 (printed p. 56) is a coupled
condition on exactly this augmented closed loop. -/

/-- The **augmented output-feedback closed loop** of the observer-based DSMC in
the `(x, e)` coordinates, `[[A + B K, B K], [0, A - L C]]`, reindexed from the
sum type `Fin n ⊕ Fin n` to `Fin (n + n)` so that the quadratic-form machinery
of `DynamicalSystems.DiscreteTime.MatrixLyapunov` applies. Its `(2,1)` block
vanishes (the separation structure of A. Argha, S. W. Su, L. Li and H. T. Nguyen,
*Advances in Discrete-Time Sliding Mode Control: Theory and Applications*,
CRC Press 2018, eq. (3.12), printed p. 55); `K` is the estimate-feedback gain of
the control law (3.10) built from the sliding surface `S = Bᵀ P₁`. -/
noncomputable def dsmcOutputFeedbackClosedLoop (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (L : Matrix (Fin n) (Fin p) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (K : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  (fromBlocks (A + B * K) (B * K) 0 (A - L * C)).submatrix finSumFinEquiv.symm
    finSumFinEquiv.symm

/-- The action of the augmented closed loop on a paired state `(x, e)` reproduces
the coupled recursion `x' = (A + B K) x + B K e`, `e' = (A - L C) e` of
A. Argha, S. W. Su, L. Li and H. T. Nguyen, *Advances in Discrete-Time Sliding
Mode Control: Theory and Applications*, CRC Press 2018, eq. (3.12), printed
p. 55. This is the block form of `dsmcOutputFeedbackClosedLoop`, stated before
the reindexing so that the two coordinates remain visible. -/
theorem dsmcOutputFeedbackClosedLoop_fromBlocks (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (L : Matrix (Fin n) (Fin p) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (K : Matrix (Fin m) (Fin n) ℝ) (x e : Fin n → ℝ) :
    fromBlocks (A + B * K) (B * K) 0 (A - L * C) *ᵥ (x ⊕ᵥ e)
      = ((A + B * K) *ᵥ x + (B * K) *ᵥ e) ⊕ᵥ ((A - L * C) *ᵥ e) := by
  rw [Matrix.fromBlocks_mulVec]
  simp

/-- The **block-diagonal Lyapunov matrix** `P = diag(P₁, Q₂)` of the
output-feedback closed loop, reindexed to `Fin (n + n)`. It weighs the state
`x` by `P₁ ≻ 0` and the estimation error `e` by `Q₂ ≻ 0`, matching the Lyapunov
function `V(ϖ) = xᵀ P₁ x + e_aᵀ Q₂ e_a + σᵀ (S B)⁻¹ σ` of eq. (3.16), printed
p. 56 (the sliding-function term is omitted here; see the module docstring). -/
noncomputable def dsmcOutputFeedbackLyapunov (P₁ Q₂ : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (n + n)) (Fin (n + n)) ℝ :=
  (fromBlocks P₁ 0 0 Q₂).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

/-- **Positive definiteness of the block-diagonal Lyapunov matrix.** If `P₁` and
`Q₂` are positive definite then so is `diag(P₁, Q₂)`, and hence its reindexed
form `dsmcOutputFeedbackLyapunov P₁ Q₂`. This is the `P₁ ≻ 0`, `Q₂ ≻ 0` part of
the LMI (3.14) of A. Argha, S. W. Su, L. Li and H. T. Nguyen, *Advances in
Discrete-Time Sliding Mode Control: Theory and Applications*, CRC Press 2018,
printed p. 56, and it certifies the Lyapunov function (3.16), printed p. 56. It
reuses the strict block `PosDef` lemma `Matrix.posDef_fromBlocks_zero` of
`DynamicalSystems.Mathlib.LinearAlgebra.Matrix.SchurComplement`. -/
theorem dsmcOutputFeedbackLyapunov_posDef {P₁ Q₂ : Matrix (Fin n) (Fin n) ℝ}
    (hP₁ : P₁.PosDef) (hQ₂ : Q₂.PosDef) :
    (dsmcOutputFeedbackLyapunov P₁ Q₂).PosDef := by
  unfold dsmcOutputFeedbackLyapunov
  exact (posDef_fromBlocks_zero P₁ Q₂ hP₁ hQ₂).submatrix finSumFinEquiv.symm.injective

/-- **Split of the block-diagonal Lyapunov form.** For an augmented vector `z` on
`Fin (n + n)`, the quadratic form of `dsmcOutputFeedbackLyapunov P₁ Q₂` is the
sum of the state quadratic form and the error quadratic form,

`quadForm (diag(P₁, Q₂)) z = quadForm P₁ x + quadForm Q₂ e`,

where `x = z ∘ Fin.castAdd n` is the state block and `e = z ∘ Fin.natAdd n` is
the estimation-error block. This makes the Lyapunov function
`V = xᵀ P₁ x + eᵀ Q₂ e` of eq. (3.16) (printed p. 56) explicit in the augmented
coordinates; the sliding-function term `σᵀ (S B)⁻¹ σ` of the book is omitted (see
the module docstring). -/
theorem dsmcOutputFeedbackLyapunov_quadForm (P₁ Q₂ : Matrix (Fin n) (Fin n) ℝ)
    (z : Fin (n + n) → ℝ) :
    quadForm (dsmcOutputFeedbackLyapunov P₁ Q₂) z
      = quadForm P₁ (z ∘ Fin.castAdd n) + quadForm Q₂ (z ∘ Fin.natAdd n) := by
  unfold dsmcOutputFeedbackLyapunov quadForm
  rw [Matrix.submatrix_mulVec_equiv]
  rw [← comp_equiv_symm_dotProduct z _ finSumFinEquiv.symm]
  simp only [Equiv.symm_symm]
  have hleft : (z ∘ ⇑finSumFinEquiv) ∘ Sum.inl = z ∘ Fin.castAdd n := by
    funext j
    exact congrArg z (finSumFinEquiv_apply_left j)
  have hright : (z ∘ ⇑finSumFinEquiv) ∘ Sum.inr = z ∘ Fin.natAdd n := by
    funext j
    exact congrArg z (finSumFinEquiv_apply_right j)
  have hM : fromBlocks P₁ 0 0 Q₂ *ᵥ (z ∘ ⇑finSumFinEquiv) =
      (P₁ *ᵥ (z ∘ Fin.castAdd n)) ⊕ᵥ (Q₂ *ᵥ (z ∘ Fin.natAdd n)) := by
    rw [Matrix.fromBlocks_mulVec, hleft, hright]
    simp only [zero_mulVec, add_zero, zero_add]
  have hsplit : (z ∘ ⇑finSumFinEquiv) =
      (z ∘ Fin.castAdd n) ⊕ᵥ (z ∘ Fin.natAdd n) := by
    funext i
    cases i with
    | inl j => exact congrArg z (finSumFinEquiv_apply_left j)
    | inr j => exact congrArg z (finSumFinEquiv_apply_right j)
  rw [hM, hsplit, dotProduct, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [dotProduct, dotProduct]

/-- The **LMI-coupled output-feedback matrix inequality** of the augmented closed
loop: the block-diagonal Lyapunov matrix `P = diag(P₁, Q₂)` satisfies
`P - A_clᵀ P A_cl ≻ 0` for `A_cl = dsmcOutputFeedbackClosedLoop A B L C K`. This
is the Schur-complement core of the LMI (3.14) of A. Argha, S. W. Su, L. Li and
H. T. Nguyen, *Advances in Discrete-Time Sliding Mode Control: Theory and
Applications*, CRC Press 2018, Theorem 3.1, printed p. 56, after the reductions
(3.22)–(3.27), printed pp. 58–59. It *couples* the state block `P₁` and the
observer-error block `Q₂` through the off-diagonal block `B K` of `A_cl`; it is
an assumption, and no feasibility of the literal LMI (3.14) is claimed. -/
def dsmcOutputFeedbackLMI (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (L : Matrix (Fin n) (Fin p) ℝ) (C : Matrix (Fin p) (Fin n) ℝ)
    (K : Matrix (Fin m) (Fin n) ℝ) (P₁ Q₂ : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (dsmcOutputFeedbackLyapunov P₁ Q₂ -
    (dsmcOutputFeedbackClosedLoop A B L C K)ᵀ * dsmcOutputFeedbackLyapunov P₁ Q₂ *
    dsmcOutputFeedbackClosedLoop A B L C K).PosDef

/-- **One-step quadratic decrease of the output-feedback closed loop.** Under the
LMI-coupled condition `P - A_clᵀ P A_cl ≻ 0` with `P = diag(P₁, Q₂)` and
`A_cl = dsmcOutputFeedbackClosedLoop A B L C K`, one step of the augmented closed
loop strictly decreases the quadratic Lyapunov form on every non-zero vector:

`quadForm P (A_cl z) < quadForm P z`  for `z ≠ 0`.

This is the one-step core of the stability implication and directly feeds
`quadForm_mulVec_lt` of `DynamicalSystems.DiscreteTime.MatrixLyapunov` (with
`Q = P`, `M = A_cl`). It is the output-feedback instance of the discrete
Lyapunov decrease of A. Argha, S. W. Su, L. Li and H. T. Nguyen, *Advances in
Discrete-Time Sliding Mode Control: Theory and Applications*, CRC Press 2018,
Theorem 3.1 and the decrease (3.21), printed pp. 56–58. No positive definiteness
of `P₁` or `Q₂` is needed for the one-step inequality; it is needed only for the
iteration and coercivity of the Lyapunov function. -/
theorem dsmc_outputFeedback_decrease_of_lmi (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (L : Matrix (Fin n) (Fin p) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (K : Matrix (Fin m) (Fin n) ℝ)
    {P₁ Q₂ : Matrix (Fin n) (Fin n) ℝ} (hLMI : dsmcOutputFeedbackLMI A B L C K P₁ Q₂)
    {z : Fin (n + n) → ℝ} (hz : z ≠ 0) :
    quadForm (dsmcOutputFeedbackLyapunov P₁ Q₂)
        (dsmcOutputFeedbackClosedLoop A B L C K *ᵥ z)
      < quadForm (dsmcOutputFeedbackLyapunov P₁ Q₂) z :=
  quadForm_mulVec_lt hLMI hz

/-- **The LMI-coupled output-feedback closed loop is quadratically stable**
(A. Argha, S. W. Su, L. Li and H. T. Nguyen, *Advances in Discrete-Time Sliding
Mode Control: Theory and Applications*, CRC Press 2018, Theorem 3.1, LMI (3.14)
and the Lyapunov function (3.16), printed p. 56). If `P₁ ≻ 0` and `Q₂ ≻ 0` and
the coupled LMI `P - A_clᵀ P A_cl ≻ 0` holds for the augmented output-feedback
closed loop `A_cl` of `dsmcOutputFeedbackClosedLoop` with the block-diagonal
Lyapunov matrix `P = diag(P₁, Q₂)`, then there is a contraction factor `c ∈ [0, 1)`
such that the quadratic Lyapunov function `quadForm P` decays geometrically
along the closed loop:

`quadForm P (A_clᵏ z) ≤ cᵏ quadForm P z`  for all `k` and `z`.

This is the discrete quadratic-stability conclusion of the book's Theorem 3.1;
the Schur-complement reduction of the block LMI is the hypothesis and the
geometric decay is obtained from `exists_factor` and `quadForm_pow_mulVec_le` of
`DynamicalSystems.DiscreteTime.MatrixLyapunov`. As throughout the campaign, only
the implication "the LMI holds `⇒` the closed loop is quadratically stable" is
proved; feasibility of the LMI (3.14) is **not** proved. The hypothesis
`Nonempty (Fin n)` is the non-degeneracy needed by the compactness argument of
`exists_factor`. -/
theorem dsmc_outputFeedback_stability_of_lmi (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin m) ℝ) (L : Matrix (Fin n) (Fin p) ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (K : Matrix (Fin m) (Fin n) ℝ)
    {P₁ Q₂ : Matrix (Fin n) (Fin n) ℝ} (hP₁ : P₁.PosDef) (hQ₂ : Q₂.PosDef)
    (hLMI : dsmcOutputFeedbackLMI A B L C K P₁ Q₂) (hne : Nonempty (Fin n)) :
    ∃ c, 0 ≤ c ∧ c < 1 ∧ ∀ (k : ℕ) (z : Fin (n + n) → ℝ),
      quadForm (dsmcOutputFeedbackLyapunov P₁ Q₂)
          ((dsmcOutputFeedbackClosedLoop A B L C K ^ k) *ᵥ z)
        ≤ c ^ k * quadForm (dsmcOutputFeedbackLyapunov P₁ Q₂) z := by
  have hP : (dsmcOutputFeedbackLyapunov P₁ Q₂).PosDef :=
    dsmcOutputFeedbackLyapunov_posDef hP₁ hQ₂
  have hne' : Nonempty (Fin (n + n)) := hne.elim fun i => ⟨Fin.castAdd n i⟩
  obtain ⟨c, hc0, hc1, hstep⟩ := exists_factor hP hP hLMI hne'
  exact ⟨c, hc0, hc1, fun k z ↦ quadForm_pow_mulVec_le hc0 hstep k z⟩
