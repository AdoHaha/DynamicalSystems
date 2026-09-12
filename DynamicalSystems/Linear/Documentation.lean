import VersoManual
import DynamicalSystems.Linear.Hautus
import DynamicalSystems.Linear.KalmanDecomposition
import DynamicalSystems.Linear.Trajectory
import DynamicalSystems.Linear.ConditionedInvariant
import DynamicalSystems.Linear.Reachability
import DynamicalSystems.Linear.Gramian
import DynamicalSystems.Linear.PolePlacement

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option linter.hashCommand false
set_option linter.missingDocs false

-- Verso generates this declaration from `#doc`; give that generated object a docstring too.
run_cmd do
  Lean.addDocStringCore
    `DynamicalSystems.Linear.Documentation.«the canonical document object name»
    "Manual chapter for the checked linear-control APIs."

#doc (Manual) "Linear systems" =>
%%%
tag := "linear-systems"
htmlSplit := .never
%%%

This chapter describes the algebraic and trajectory foundations currently available for linear
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

# Four-block Kalman decomposition

The four-component coordinates are adapted to the reachable space `W`, the unobservable space `N`,
and their intersection. The forward coordinate map is their sum in the original state space.
Seven off-diagonal state-map blocks, two input blocks, and two output blocks vanish. The
controllable–observable quotient of the reachable space preserves `D` and every `C A^k B`.
This is not yet a proof of continuous-time behavior equivalence or minimal state dimension.

{docstring LinearMap.kalmanEquiv}
{docstring LinearMap.kalmanEquiv_apply}
{docstring LinearMap.controllableObservableRealization}
{docstring LinearMap.isControllable_controllableObservableRealization}
{docstring LinearMap.isObservable_controllableObservableRealization}
{docstring LinearMap.controllableObservableRealization_markov}

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

# Real LTI trajectories

For finite-dimensional real state and input spaces, locally integrable inputs have unique
continuous integral-solution trajectories. The variation-of-constants curve is absolutely
continuous on every compact time interval and satisfies the differential equation almost
everywhere. These are proved results, not premises of the relation adapters.

{docstring LinearSystem.variationOfConstants}
{docstring LinearSystem.variationOfConstants_absolutelyContinuousOnInterval}
{docstring LinearSystem.variationOfConstants_ae_hasDerivAt}
{docstring LinearSystem.variationOfConstants_integral}
{docstring LinearSystem.integralSolution_unique}
{docstring LinearSystem.variationOfConstants_isCaratheodorySolutionOn}

The admissible-input relations are exactly restrictions of the existing project relations.
The readout retains feedthrough, so pointwise output equality is not asserted merely from
almost-everywhere equality of inputs.

{docstring LinearSystem.mem_ltiStateTrajectoryRel_iff}
{docstring LinearSystem.mem_ltiInputOutputRel_iff}
{docstring LinearSystem.ltiStateTrajectoryRel_existsUnique}
{docstring LinearSystem.ltiInputOutputRel_existsUnique}

# Geometric invariance

Controlled invariance means `AV ≤ V + range B`; conditioned invariance means
`A(S ∩ ker C) ≤ S`. Feedback and output-injection witnesses are proved to exist,
using linear-map lifting and extension. Duality uses algebraic annihilators.

{docstring LinearMap.isControlledInvariant_iff_exists_stateFeedback}
{docstring LinearMap.isConditionedInvariant_iff_exists_outputInjection}
{docstring LinearMap.isConditionedInvariant_iff_isControlledInvariant_dualMap}
{docstring LinearMap.isControlledInvariant_iff_isConditionedInvariant_dualMap}

The decreasing ISA and increasing CISA stabilize in finite dimension, giving the
largest controlled-invariant subspace inside a constraint and the smallest
conditioned-invariant subspace containing a prescribed subspace.

{docstring LinearMap.controlledInvariantSeq}
{docstring LinearMap.isGreatest_controlledInvariantSubspace}
{docstring LinearMap.conditionedInvariantSeq}
{docstring LinearMap.isLeast_conditionedInvariantSubspace}

These algebraic results do not yet establish the corresponding trajectory/observer
characterizations or the book's sharp dimension bounds for the stationary index.

# Reachability and Gramians

For a strictly positive finite horizon, locally integrable inputs reach exactly the
algebraic reachable subspace. Two initial states are indistinguishable for every
admissible input exactly when their difference lies in the algebraic unobservable
subspace. On real inner-product spaces, the controllability and observability
Gramians have the expected energy identities and are positive definite exactly for
controllable and observable pairs.

{docstring LinearSystem.reachableSetAt_eq_reachableSubspace}
{docstring LinearSystem.indistinguishableOn_iff_mem_unobservableSubspace}
{docstring LinearSystem.inner_controllabilityGramian}
{docstring LinearSystem.inner_observabilityGramian}
{docstring LinearSystem.controllabilityGramian_posDef_iff_isControllable}
{docstring LinearSystem.observabilityGramian_posDef_iff_isObservable}

# Pole-placement foundations

The accepted pole-placement foundation records feedback invariance, a real
quotient obstruction for the converse direction, companion characteristic-polynomial
infrastructure, the zero-dimensional case, and reusable nonzero/Krylov and
controlled-span lemmas. The full constructive feedback assignment theorem remains
an explicitly tracked follow-up obligation.

{docstring LinearMap.reachableSubspace_add_comp}
{docstring LinearMap.isControllable_add_comp}
{docstring LinearMap.charpoly_eq_of_companion}
{docstring LinearMap.exists_feedback_charpoly_of_finrank_zero}
{docstring LinearMap.isControllable_of_forall_exists_feedback_charpoly}
{docstring LinearMap.isControllable_iff_bijective_kalmanControllabilityMap_single}
{docstring LinearMap.linearIndependent_krylov_of_isControllable_single}
{docstring LinearMap.eq_top_of_isControllable_of_map_le}

# Sources and scope

The organizing reference is Trentelman, Stoorvogel, and Hautus, *Control Theory for Linear Systems*,
especially the structural material of Chapter 3. Proofs reuse mathlib's linear algebra and
Cayley–Hamilton infrastructure. The Hautus module records its additional proof-development
reference to Gokhale and Bullo's *LeanForControl*.

Pole placement, stabilization/observers, and disturbance-decoupling synthesis are not yet
asserted. Those require their own checked bridges and are tracked separately from the results above.
