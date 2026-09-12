# Linear control foundations

This development follows Trentelman, Stoorvogel and Hautus, *Control Theory for
Linear Systems* (2001), using the existing DynamicalSystems and Mathlib APIs.
It is an incremental formalization, not yet a formalization of the full book.

## Available

Import `DynamicalSystems.Linear.Basic` for `LinearSystem 𝕜 X U Y`, a quadruple
of linear maps over a field. Its equations are `x' = A x + B u` and
`y = C x + D u`. The algebraic API does not impose finite dimension.

`sys.stateFeedback F` implements `u = F x + v`; it transforms both the dynamics
and the output when feedthrough `D` is nonzero. `changeState`, `changeInput`, and
`changeOutput` transport the system between equivalent space types. Their
evaluation lemmas state how the new equations relate to the original ones.

Import `DynamicalSystems.Linear.Subspaces` for:

| Declaration | Meaning |
|---|---|
| `LinearMap.reachableSubspace A B` | Supremum of the ranges of `A^k ∘ B` |
| `LinearMap.unobservableSubspace C A` | Infimum of the kernels of `C ∘ A^k` |
| `LinearMap.IsControllable A B` | Reachable subspace equals the state space |
| `LinearMap.IsObservable C A` | Unobservable subspace equals zero |
| `LinearMap.reachableSubspace_le` | Least invariant subspace containing `range B` |
| `LinearMap.le_unobservableSubspace` | Greatest invariant subspace inside `ker C` |

The containment and invariance directions are separate reusable lemmas.
Both subspaces are connected to Mathlib's `Module.End.invtSubmodule` lattice.
These are algebraic results; equivalence to continuous-time steering and output
distinguishability is a later, separately tracked obligation.

Import `DynamicalSystems.Linear.Kalman` for finite Krylov descriptions using
the first `Module.finrank 𝕜 X` powers, including zero-dimensional state spaces.
`kalmanControllabilityMap` and `kalmanObservabilityMap` give coordinate-free
range/kernel descriptions, surjectivity/injectivity criteria, and dimension
criteria. Their basis representations give the usual full matrix-rank tests.
The finite reduction reuses Mathlib's Cayley–Hamilton remainder theorem.

## Conventions

- Pair order: `(A, B)` for controllability; `(C, A)` for observability.
- State coordinates: `x = e x_new`; output coordinates: `y_new = e y`.
- Feedback: `u = F x + v`; observer error: `x - xhat`.
- Observer innovation must retain known feedthrough: `y - C xhat - D u`.
- Matrix APIs should be obtained from chosen bases of these spaces.
- Integral and almost-everywhere trajectory semantics should use the existing
  Carathéodory and input/output relation definitions.

## Roadmap

Next are duality and decomposition, trajectory
equivalences, Gramians, stabilization and observers, and geometric disturbance
decoupling. Each addition requires source/statement review, actual Lean proofs,
and the standard-axiom audit. Missing results are not available assumptions.

The surrounding research workspace contains the restartable Pi campaign at
`automation/linear_control/`; the formal library does not depend on that harness
or on the locally cached books. The nonlinear-control book is indexed for
future work, not part of the implemented theorem set.
