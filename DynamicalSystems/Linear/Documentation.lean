import VersoManual
import DynamicalSystems.Linear.Hautus

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option linter.hashCommand false
set_option linter.missingDocs false

-- Verso generates this declaration from `#doc`; give that generated object a docstring too.
run_cmd do
  Lean.addDocStringCore
    `DynamicalSystems.Linear.Documentation.«the canonical document object name»
    "Manual chapter for the checked algebraic linear-control APIs."

#doc (Manual) "Linear systems" =>
%%%
tag := "linear-systems"
htmlSplit := .never
%%%

This chapter describes the algebraic foundations currently available for finite-dimensional linear
control. The state, input, and output spaces are separate vector spaces. Coordinates and topology
are introduced only where needed; the basic subspace definitions do not require finite dimension.

# Systems and conventions

{docstring LinearSystem}

The dynamics are `Ax + Bu` and the readout is `Cx + Du`. Controllability takes the pair `(A, B)`;
observability takes `(C, A)`. State feedback uses `u = Fx + v`, so it changes both `A` to `A + BF`
and `C` to `C + DF`. In a state coordinate change `e : X' ≃ₗ[𝕜] X`, the old state is `e x'`.

{docstring LinearSystem.stateFeedback}
{docstring LinearSystem.changeState}

# Reachability and observability

{docstring LinearMap.reachableSubspace}
{docstring LinearMap.unobservableSubspace}
{docstring LinearMap.IsControllable}
{docstring LinearMap.IsObservable}

These are algebraic predicates. Their equivalence with finite-time trajectory properties is a
separate analytic obligation, not an assumption hidden in the definitions. The reachable subspace
is the least invariant subspace containing the input range; the unobservable subspace is the
greatest invariant subspace contained in the output kernel.

{docstring LinearMap.reachableSubspace_le}
{docstring LinearMap.le_unobservableSubspace}

# Finite Kalman tests

Cayley–Hamilton reduces all powers to the first `finrank 𝕜 X` powers, including the
zero-dimensional case. The finite maps precede their matrix representations, so downstream proofs
need not choose bases.

{docstring LinearMap.kalmanControllabilityMap}
{docstring LinearMap.kalmanObservabilityMap}
{docstring LinearMap.isControllable_iff_surjective_kalmanControllabilityMap}
{docstring LinearMap.isObservable_iff_injective_kalmanObservabilityMap}

# Duality, coordinates, restrictions, and quotients

Duality here means the algebraic dual and its annihilators, not a Hilbert-space adjoint. Coordinate
invariance is proved for arbitrary linear equivalences. The reachable restriction is controllable;
the quotient by the unobservable subspace is observable. Complement subspaces are not assumed
invariant.

{docstring LinearMap.isControllable_iff_isObservable_dualMap}
{docstring LinearMap.isObservable_iff_isControllable_dualMap}
{docstring LinearMap.isControllable_reachableRestriction}
{docstring LinearMap.isObservable_quotientUnobservable}

# PBH / Hautus tests

The abstract eigenvalue criteria require an algebraically closed field. For real matrices, use the
complexification corollaries: checking only real eigenvalues would miss, for example, a planar
rotation. Both controllability and observability are preserved by complexification.

{docstring LinearMap.isControllable_iff_hautus}
{docstring LinearMap.isObservable_iff_hautus}
{docstring LinearMap.isControllable_complexify_iff}
{docstring LinearMap.isObservable_complexify_iff}
{docstring LinearMap.isControllable_iff_hautus_complex}
{docstring LinearMap.isObservable_iff_hautus_complex}

# Sources and scope

The organizing reference is Trentelman, Stoorvogel, and Hautus, *Control Theory for Linear Systems*,
especially the structural material of Chapter 3. Proofs reuse mathlib's linear algebra and
Cayley–Hamilton infrastructure. The Hautus module records its additional proof-development
reference to Gokhale and Bullo's *LeanForControl*.

This chapter does not yet assert a completed continuous-time trajectory theory, Gramian criteria,
pole placement, or disturbance-decoupling synthesis. Those require their own checked bridges and
are tracked separately from the algebraic results above.
