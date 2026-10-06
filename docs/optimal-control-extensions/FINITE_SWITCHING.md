# Finite switching of nondegenerate LTI box extremals

Date: 2026-10-06. Baseline: `dev` at `7b9037fb57f826650e8f7b372102b1decb2be1ea`.

## Result and exact scope

The new public namespace is `OptimalControl`; filenames follow concepts, not campaign labels.

`hasFiniteSwitchesOn_of_linear_box_minimizing` and
`hasAEFiniteSwitchesOn_of_linear_box_minimizing` prove the K7 structural result for
finite-dimensional real LTI systems with finitely many box-constrained inputs.
Every input column must satisfy the **finite per-input Krylov spanning condition**
`CyclicInput A (b i)`. A nonzero terminal covector is required.

The theorem constructs the backward adjoint `p(t) = q ∘ exp((T-t)A)` and proves its
actual differential equation and terminal value. It derives analyticity and
nontriviality of every switching coefficient, then a finite common zero set, then
constancy of the control on every interval avoiding that set. It does not assume
finite zeros, a sign law, or nontrivial switching functions under another name.

For an everywhere Hamiltonian-minimization law, the actual control has finitely
many switches, allowing arbitrary values at the finitely many exceptional times.
For an AE law, the conclusion is an **AE-equivalent finite-switch representative**.
An arbitrary pointwise representative may have infinitely many null-set changes.

This is a structure theorem for a PMP extremal. It is not itself an
optimality-to-PMP necessity theorem, nor an existence-of-optimal-controls result.
The minimum-time running-cost constant cancels in the input comparison; no cost
multiplier is divided by or assumed strictly positive. No universal numerical
switch-count bound is asserted.

## Proof chain

1. `AnalyticOnNhd.finite_zeroSet_Icc` and its compact-connected variant: analytic
   identity theorem plus compactness of a codiscrete zero set. Analyticity includes
   neighbourhoods of the horizon endpoints.
2. `hasDerivAt_terminalAdjointCovector`: differentiates the actual exponential
   propagator to obtain `p' = -p ∘ A`.
3. `exists_ne_zero_linearSwitchingFunction`: if a coefficient vanished identically,
   the existing exponential-output observability theorem would annihilate its
   Krylov family; the spanning hypothesis would then force `q = 0`.
4. `finite_all_switching_zeros`: finite union over input channels.
5. `sign_eq_of_continuousOn_no_zero`: intermediate value theorem excludes a sign
   change without a zero.
6. Existing `linearMinimizer_bangBang` turns Hamiltonian minimization into the sign
   selector off that finite set. A finite-modification lemma handles zero times;
   the AE theorem explicitly removes them as a null set.

## Validation

All three new production modules and `DynamicalSystemsTest/FiniteSwitching.lean`
were checked locally with the exact pinned Lean 4.35.0-rc2 compiler and Mathlib cache.
The test file prints the axioms of the adjoint, nontriviality, common finite-zero,
and both final finite-switch results: only `propext`, `Classical.choice`, and
`Quot.sound` occur. There is no new axiom or placeholder.

Regression examples include a scalar nonzero channel and the standard double
integrator. A genuinely controllable pair with a zero input column demonstrates
why combined `(A,B)` controllability cannot replace the per-input hypothesis.

Reproduce in a normal checkout:

```sh
bash scripts/check_optimal_control_extensions.sh
```

The branch CI runs that script in addition to its library build and axiom audit.
The earlier baseline CI run `37423731092` passed at commit `051c55e`; that result
predates the new structural modules and must not be cited as their build evidence.
