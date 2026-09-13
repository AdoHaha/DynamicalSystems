import VersoManual
import DynamicalSystems.Linear.Hautus
import DynamicalSystems.Linear.KalmanDecomposition
import DynamicalSystems.Linear.Trajectory
import DynamicalSystems.Linear.ConditionedInvariant
import DynamicalSystems.Linear.Reachability
import DynamicalSystems.Linear.Gramian
import DynamicalSystems.Linear.PolePlacement
import DynamicalSystems.Linear.Stabilization
import DynamicalSystems.Linear.Observer
import DynamicalSystems.Linear.DisturbanceDecoupling
import DynamicalSystems.Linear.DynamicFeedback
import DynamicalSystems.Linear.Examples.Algebra

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

The accepted pole-placement material records feedback invariance, a real quotient
obstruction for the converse direction, companion characteristic-polynomial
infrastructure, and reusable nonzero/Krylov and controlled-span lemmas. It
constructively assigns any monic real polynomial to controllable single-input and
multi-input pairs, including the zero-dimensional case, via the controlled-chain
reduction.

{docstring LinearMap.reachableSubspace_add_comp}
{docstring LinearMap.isControllable_add_comp}
{docstring LinearMap.charpoly_eq_of_companion}
{docstring LinearMap.exists_feedback_charpoly_of_finrank_zero}
{docstring LinearMap.isControllable_of_forall_exists_feedback_charpoly}
{docstring LinearMap.isControllable_iff_bijective_kalmanControllabilityMap_single}
{docstring LinearMap.linearIndependent_krylov_of_isControllable_single}
{docstring LinearMap.eq_top_of_isControllable_of_map_le}
{docstring LinearMap.exists_feedback_charpoly_single}
{docstring LinearMap.exists_controlled_chain}
{docstring LinearMap.exists_feedback_charpoly_of_isControllable}

# Stabilization, observers, and the Hurwitz bridge

For a real endomorphism the *Hurwitz* predicate records that every complex root of its
characteristic polynomial has negative real part. Gain existence is a theorem, not a
hypothesis: controllability produces a stabilizing state feedback and observability produces a
stabilizing output injection, both by pole placement on the target `(X + 1)^n`. The general
Hurwitz-to-decay bridge is proved by a complex generalized-eigenspace argument followed by a
real-coordinate reduction, and connects the spectral predicate to `Filter.IsAttractive` and
`Filter.IsStableOn`.

{docstring LinearMap.IsHurwitz}
{docstring LinearMap.IsStabilizable}
{docstring LinearMap.IsDetectable}
{docstring LinearMap.isStabilizable_of_isControllable}
{docstring LinearMap.isDetectable_of_isObservable}
{docstring LinearMap.tendsto_exp_of_isHurwitz}
{docstring LinearMap.isStableOn_expFlow_of_isHurwitz}
{docstring LinearMap.exists_stabilizing_feedback_stable_attractive}
{docstring LinearMap.isStabilizable_of_uncontrollableEigenvalues_hurwitz}
{docstring LinearMap.isDetectable_of_unobservableEigenvalues_hurwitz}

The separation principle is the block-operator statement for the observer-based controller,
combining a stabilizing state feedback with a convergent observer.

{docstring LinearMap.charpoly_blockOperator}
{docstring LinearMap.exists_separation_block_hurwitz}

The Luenberger observer uses the feedthrough-aware innovation `y - C ξ - D u`, so the error
dynamics `e' = (A - L C) e` is independent of the input and of the state-feedback gain.
Observability yields a convergent observer, again with the gain constructed rather than
assumed.

{docstring LinearSystem.innovation}
{docstring LinearSystem.observerError_dynamics}
{docstring LinearMap.exists_observer_stable_attractive_of_isObservable}
{docstring LinearMap.separation_principle_observer}

# Disturbance decoupling and dynamic measurement feedback

A disturbance channel is decoupled when every Markov parameter `H A^k E` vanishes. This is
characterised by invariant subspaces and by the analytic impulse response, and, through the
variation-of-constants formula, by the vanishing of the disturbance contribution for every
locally integrable input.

{docstring LinearMap.disturbanceResponse}
{docstring LinearMap.IsDisturbanceDecoupled}
{docstring LinearMap.isDisturbanceDecoupled_iff_exists_invariant}
{docstring LinearMap.exists_isCABPairBetween_iff}
{docstring LinearMap.isDisturbanceDecoupled_iff_forall_expFlow}
{docstring LinearMap.forcedOutput_eq_convolution}
{docstring LinearMap.isDisturbanceDecoupled_iff_forall_disturbanceContribution_eq_zero}

The Chapter 6 synthesis layer constructs a dynamic controller from a `(C, A, B)`-pair
certificate and proves the closed loop decoupled. Well-posedness of the algebraic loop is the
invertibility of `1 - D N`.

{docstring LinearSystem.DynamicController}
{docstring LinearSystem.DynamicInterconnection.IsWellPosed}
{docstring LinearSystem.DynamicInterconnection.closedLoopSystem}
{docstring LinearSystem.exists_dynamicController_of_isCABPairBetween}
{docstring LinearSystem.isClosedLoopDisturbanceDecoupled_of_isCABPairBetween}

The converse extraction of a `(C, A, B)`-pair from a decoupled closed loop, the
transfer-function form `H (s I - A)⁻¹ E = 0`, a measurement disturbance channel `F`, and the
spectrum/internal-stability layers remain deferred obligations.

# Algebraic examples

These concrete algebraic examples exercise the pair API. In particular the planar rotation with
zero readout is not observable, and the failure is witnessed at the non-real complex
eigenvalue `I`, which is why the PBH bridge must complexify.

{docstring DynamicalSystems.Linear.Examples.doubleIntegrator_controllable}
{docstring DynamicalSystems.Linear.Examples.uncontrollable_not_controllable}
{docstring DynamicalSystems.Linear.Examples.unobservable_not_observable}
{docstring DynamicalSystems.Linear.Examples.rotation_complex_not_observable}
{docstring DynamicalSystems.Linear.Examples.rotation_real_not_observable}

# Sources and scope

The organizing reference is Trentelman, Stoorvogel, and Hautus, *Control Theory for Linear Systems*,
especially the structural material of Chapters 3–6. Proofs reuse mathlib's linear algebra and
Cayley–Hamilton infrastructure. The Hautus module records its additional proof-development
reference to Gokhale and Bullo's *LeanForControl*.

Constructive pole placement is complete in both directions, for single- and multi-input
finite-dimensional real pairs. The stabilization layer proves gain existence from
controllability (and, dually, from observability), the explicit-target decay bridge, the general
Hurwitz-to-decay and Lyapunov-stability theorem, the PBH converse criteria for uncontrollable
and unobservable eigenvalues, and the observer-based separation principle. The Luenberger
observer uses the feedthrough-aware innovation and its error dynamics is independent of the
input and the state-feedback gain.

Disturbance decoupling is characterised algebraically, geometrically, and by the analytic
impulse response, and the variation-of-constants/convolution bridge proves that exact decoupling
is equivalent to zero disturbance contribution for every locally integrable input. The Chapter 6
synthesis layer constructs a dynamic measurement-feedback controller from an `IsCABPairBetween`
certificate and proves the closed loop decoupled.

The documented deferred obligations are: the transfer-function/resolvent form
`H (s I - A)⁻¹ E = 0`; the converse extraction of a `(C, A, B)`-pair from a decoupled closed
loop; a measurement disturbance channel `F` in the readout; the spectrum factorization and the
internal/external stabilization layers; and the final examples/release bridge to a local
actuator or filter result.
