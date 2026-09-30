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
These are algebraic results; strictly positive-horizon steering and output
distinguishability equivalences are supplied by `Linear.Reachability`.

Import `DynamicalSystems.Linear.Kalman` for finite Krylov descriptions using
the first `Module.finrank 𝕜 X` powers, including zero-dimensional state spaces.
`kalmanControllabilityMap` and `kalmanObservabilityMap` give coordinate-free
range/kernel descriptions, surjectivity/injectivity criteria, and dimension
criteria. Their basis representations give the usual full matrix-rank tests.
The finite reduction reuses Mathlib's Cayley–Hamilton remainder theorem.

Import `DynamicalSystems.Linear.Duality` for algebraic transpose/annihilator
duality, pair invariance under `changeState`, and the two-block decompositions.
The restricted reachable pair is proved controllable; the quotient by the
unobservable subspace is proved observable. The quotient input and restricted
unobservable readout vanish. Complement zero-block identities are proved without
assuming the complement is invariant.

Import `DynamicalSystems.Linear.KalmanDecomposition` for the combined four-block
form: a genuine coordinate equivalence, seven zero A blocks, two zero B rows and
two zero C columns. The controllable–observable quotient is constructed from the
reachable restriction and its unobservable subspace; both pair properties and
preservation of D and every Markov parameter `C A^k B` are proved. The later
realization and transfer modules supply minimal-dimension results and equality
of the original and reduced rational transfer matrices.

Import `DynamicalSystems.Linear.Hautus` for PBH eigenvector, kernel/range and
matrix-rank criteria over algebraically closed fields. Both real-matrix
controllability and observability are proved equivalent to their complexified
pairs, and the real PBH corollaries quantify over complex eigenvalues. The
Hautus maps use the sign convention `A - μI`. This module adapts an attributed
LeanForControl eigenvector argument and uses no custom axioms from that project.

Import `DynamicalSystems.Linear.Examples.Algebra` for checked double-integrator
examples, uncontrollable/unobservable variants, coordinate swapping, empty-state
Kalman tests, and a real rotation whose PBH obstruction uses the eigenvalue `i`.

Import `DynamicalSystems.Linear.Trajectory` for finite-dimensional real LTI
solutions with locally integrable inputs. The operator exponential has derivative,
semigroup and inverse laws. The variation-of-constants curve is continuous,
absolutely continuous on every compact interval, solves the differential equation
almost everywhere, and satisfies the integral equation. Existence and uniqueness
are proved, not assumed. Exact adapters identify the admissible LTI relations with
the existing `stateTrajectoryRel` and `inputOutputRel`, and the solution satisfies
`IsCaratheodorySolutionOn`. Feedthrough is retained: AE-equal inputs need not have
pointwise-equal outputs. The general vector-primitive and operator-evaluation
absolute-continuity helpers are also reusable outside LTI theory.

Import `DynamicalSystems.Linear.ControlledInvariant` and
`DynamicalSystems.Linear.ConditionedInvariant` for algebraic controlled/conditioned
invariance, existence of feedback/injection gains, both algebraic dualities, and
the ISA/CISA subspace algorithms. Finite termination and largest/smallest universal
properties are proved. The book's trajectory/observer characterizations and sharp
dimension bounds on the stationary index are not yet asserted.

Import `DynamicalSystems.Linear.Reachability` for finite-horizon reachable sets,
output indistinguishability, and their positive-horizon equivalences with the
algebraic reachable and unobservable subspaces. Import
`DynamicalSystems.Linear.Gramian` for real inner-product controllability and
observability Gramians, energy identities, nonnegativity, reachable-set equality,
and positive-definiteness criteria. These results require strictly positive
horizons; sharper dimension and matrix basis-change refinements remain future work.

Pole placement, stabilization, observers, spectral decay, and geometric
disturbance decoupling are also available. `Linear.PolePlacement` supplies
constructive single- and multi-input pole assignment; `Linear.Stabilization`
and `Linear.Observer` connect feedback and output injection to stable dynamics.
See `Linear.Documentation` for the module-by-module API map and book references.

The dynamic-controller development proves the book's Corollary 6.22 geometric
existence equivalence for strictly proper plant and measurement channels.
`Linear.GeneralStabilityDomain` and `Linear.GeneralDomainControllerCriterion`
with their supporting modules treat arbitrary conjugation-invariant stability
domains containing a real point. Controller
state dimension is not fixed in advance. `Linear.ArbitraryControllerCriterion`
supplies the Hurwitz external-response criterion; the general-domain necessity
proof does not restrict the original plant's forcing to finite Bohl signals.
Some intermediate output-stabilizability APIs do explicitly impose that
restriction, and should not be confused with the final controller-existence iff.

The transfer modules connect minimal-realization spectral stability to poles of
the reduced rational transfer entries and, in the Hurwitz case, impulse-response
decay. `Linear.TransferRealizationEquality` proves equality with the original
channel transfer matrix, so this is not merely a criterion for a replacement
system. `Linear.TransferPoleFeedthrough` separately handles feedthrough for the
pole/decay bridge; it does not extend the geometric Corollary 6.22 iff to
nonzero plant or measurement feedthrough.

The generated Verso manual includes a **Linear systems** chapter with these
conventions and linked theorem statements. Run `lake exe generate-docs` to build it.

## Conventions

- Pair order: `(A, B)` for controllability; `(C, A)` for observability.
- State coordinates: `x = e x_new`; output coordinates: `y_new = e y`.
- Feedback: `u = F x + v`; observer error: `x - xhat`.
- Observer innovation must retain known feedthrough: `y - C xhat - D u`.
- Matrix APIs should be obtained from chosen bases of these spaces.
- Integral and almost-everywhere trajectory semantics should use the existing
  Carathéodory and input/output relation definitions.

## Scope and further work

The linear-control foundations and geometric controller-existence campaign are
complete within the hypotheses documented above. This is not the full book:
later chapters, nonlinear control, and a feedthrough-generalized geometric iff
are separate extensions. Each addition requires source/statement review, actual
Lean proofs, and the standard-axiom audit. Missing results are not assumptions.

The surrounding research workspace contains the restartable Pi campaign at
`automation/linear_control/`; the formal library does not depend on that harness
or on the locally cached books. The nonlinear-control book is indexed for
future work, not part of the implemented theorem set.
