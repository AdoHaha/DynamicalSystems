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
import DynamicalSystems.Linear.RealBohlTransport
import DynamicalSystems.Linear.DynamicFeedbackNecessity
import DynamicalSystems.Linear.GenericControllerNecessity
import DynamicalSystems.Linear.ArbitraryControllerResponse
import DynamicalSystems.Linear.GenericControllerDuality
import DynamicalSystems.Linear.GenericControllerDualResponse
import DynamicalSystems.Linear.ArbitraryControllerCriterion
import DynamicalSystems.Linear.TransferPoleStability
import DynamicalSystems.Linear.MinimalPoleCancellation
import DynamicalSystems.Linear.TransferNumeratorDegree
import DynamicalSystems.Linear.TransferDenominatorRecurrence
import DynamicalSystems.Linear.MinimalTransferPoles
import DynamicalSystems.Linear.TransferCoordinateBridge
import DynamicalSystems.Linear.TransferPoleDecay
import DynamicalSystems.Linear.TransferPoleControllerCriterion
import DynamicalSystems.Linear.TransferPoleDomains
import DynamicalSystems.Linear.TransferPoleFeedthrough
import DynamicalSystems.Linear.Examples.Algebra

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option linter.hashCommand false
set_option linter.missingDocs false
set_option linter.style.longLine false

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
explicit-hypothesis transfer-function bridge, the measurement-disturbance bookkeeping, the
spectrum/internal-stability layer, and the Hurwitz-to-external-impulse-response stability
sufficient direction and its BIBO/integrability consequence are formalized. Nonzero-`F` synthesis
is formalized under an explicit factorization hypothesis. The exact-zero response converse
`LinearSystem.externalStability_iff_geometricCertificate` (TST Theorem 6.6 / Corollary 6.7), the
state-feedback construction `LinearSystem.exists_feedback_tendsto_readout_of_corollary622` for the
Corollary 6.22 subspace condition, and the observer-error decay
`LinearSystem.exists_observerError_readout_tendsto_of_externalStabilizationConditions` are
formalized with their explicit finite-dimensional and admissibility hypotheses. For
controllers whose state space is the plant state space `X`, the *stable-nonzero*
Corollary 6.22 geometric equivalence is proved by
`LinearSystem.stableNonzeroExternalResponse_iff_externalStabilizationConditions`.
The arbitrary finite-dimensional controller-state *time-domain decay* version
is proved by
`LinearSystem.anyStateStableExternalResponse_iff_externalStabilizationConditions`.
It uses Hurwitz (left-half-plane) stability. Equivalence with the book's
reduced transfer-pole formulation for that domain is proved by
`LinearSystem.anyStatePoleStableExternalResponse_iff_externalStabilizationConditions`.
For arbitrary stability domains, only the minimal-realization pole/spectrum
bridge is asserted; the geometric controller-existence iff remains separate.
The controllable/observable special case is
`LinearSystem.exists_externallyStabilizing_cabPair_gains`.

# Stabilizable and detectable spectral subspaces

The *stable* (Hurwitz) subspace `hurwitzSubspace A` is the real form of the direct sum of the
generalized eigenspaces of `A` at eigenvalues with negative real part; the *antistable*
subspace `unstableSubspace A` collects the complement, at eigenvalues with nonnegative real
part. Both are `A`-invariant, and together they form the spectral decomposition
`X = X_g(A) ⊕ X_b(A)`.

{docstring LinearMap.hurwitzSubspace}
{docstring LinearMap.unstableSubspace}
{docstring LinearMap.map_hurwitzSubspace_le}
{docstring LinearMap.map_unstableSubspace_le}
{docstring LinearMap.isCompl_hurwitzSubspace_unstableSubspace}
{docstring LinearMap.hurwitzSubspace_sup_unstableSubspace_eq_top}

The stabilizable subspace `Xstab(A, B) = X_g(A) ⊔ ⟨A | im B⟩` and the detectable subspace
`Xdet(C, A) = ⟨ker C | A⟩ ⊓ X_b(A)` are the ambient geometric objects behind stabilizability and
detectability: a pair is stabilizable exactly when `Xstab = ⊤` and detectable exactly when
`Xdet = ⊥`. The induced maps on the unreachable quotient and the unobservable restriction are
Hurwitz.

{docstring LinearMap.stabilizableSubspace}
{docstring LinearMap.detectableSubspace}
{docstring LinearMap.map_stabilizableSubspace_le}
{docstring LinearMap.map_detectableSubspace_le}
{docstring LinearMap.isStabilizable_iff_stabilizableSubspace_eq_top}
{docstring LinearMap.isDetectable_iff_detectableSubspace_eq_bot}
{docstring LinearMap.isHurwitz_on_stabilizableComplement}
{docstring LinearMap.isHurwitz_on_detectableComplement}

The basis-independent API (`stableSubspaceOfBasis`, `unstableSubspaceOfBasis`) computes the same
subspaces from any finite basis. This is what makes the spectral split well defined on the
algebraic dual `Module.Dual ℝ X`, where the ambient space carries no canonical norm.

{docstring LinearMap.stableSubspaceOfBasis}
{docstring LinearMap.unstableSubspaceOfBasis}
{docstring LinearMap.stableSubspaceOfBasis_finBasis_eq_hurwitzSubspace}
{docstring LinearMap.stableSubspaceOfBasis_eq_of_basis}
{docstring LinearMap.mem_stableSubspaceOfBasis_iff}

The annihilator of the antistable subspace is the stable subspace of the algebraic transpose.
This is the algebraic input to the Corollary 6.22 observer half below.

{docstring LinearMap.dualAnnihilator_unstableSubspace_eq_stableSubspace_dualMap}

# Geometric external stability

The Lean predicate `LinearSystem.ExternalStability` is the *exact-zero* (disturbance-decoupling)
reading of external stability, not the source's stable-nonzero property: its defining docstring
records that it is "explicitly the zero-response predicate, not BIBO stability". The
stable-nonzero property of TST Corollary 6.22 is carried separately by
`LinearSystem.ExternalStabilizationConditions` together with the BIBO predicate
`LinearSystem.DynamicInterconnection.IsBIBOStable`. The two are never conflated.

A strictly proper plant (`D = 0`) admits an externally zero-responding dynamic
measurement-feedback controller exactly when it carries a `(C, A, B)`-pair between `im E` and
`ker H`; this is the externally stated form of the Chapter 6 exact-decoupling criterion (TST
Theorem 6.6 and Corollary 6.7). The Corollary 6.22 subspace conditions --- `im E ≤ V*(ker H) +
Xstab` and `S*(im E) ∩ Xdet ≤ ker H` --- are recovered as part of the certificate.

{docstring LinearSystem.GeometricCertificate}
{docstring LinearSystem.ExternalStability}
{docstring LinearSystem.ExternalStabilizationConditions}
{docstring LinearSystem.externalStability_iff_geometricCertificate}
{docstring LinearSystem.externalStabilizationConditions_of_externalStability}
{docstring LinearSystem.externalStability_iff_geometricCertificate_and_conditions}

BIBO stability is the genuinely nonzero-response property: it needs the extra Hurwitz gain data
(`A + B F` and `A + G C` Hurwitz) on top of the geometric pair, so the zero-response and BIBO
conclusions are stated together but never identified.

{docstring LinearSystem.bibo_and_externalZeroResponse_of_geometricCertificate_hurwitz}

The analytic half of the source's external-stabilization proof (TST Lemma 4.35 and Theorem 4.37)
is the quotient-spectrum decay bridge: if a readout vanishes on an invariant subspace and the
induced quotient map is Hurwitz, the readout trajectory decays. The geometric feedback
construction of Lemma 4.38 is proved as `exists_feedback_tendsto_readout_of_corollary622`.

{docstring LinearSystem.tendsto_readout_exp_of_isHurwitz_mapQ}
{docstring LinearSystem.tendsto_readout_exp_of_isHurwitz_quotient_on}
{docstring LinearSystem.exists_feedback_tendsto_readout_of_corollary622}

For TST Theorem 4.37, the finite-Bohl *forcing-image* formulation is proved in both
directions: a finite-Bohl forcing image with decaying readout has initial state in
`V*(ker H) + Xstab(A,B)`, and every state in that sum has such an input. The
necessity proof uses a stable/antistable state split, a pointwise state ODE,
quotient non-cancellation for the two ODE residuals, and a real controlled-invariant
span of the antistable trajectory. This is not the unrestricted locally-integrable
input theorem, nor yet the book's Bohl-*input* formulation: lifting a Bohl forcing
image to a Bohl input remains separate.

{docstring LinearSystem.finiteBohlWBridge}
{docstring LinearSystem.finiteBohlSynthesis}
{docstring LinearSystem.isBohlOutputStabilizable_iff_mem_outputStabilizableSubspace_complete}

For arbitrary finite-dimensional real state and input spaces, the same
finite-Bohl necessity is available by complexifying real coordinates and
projecting the stable/antistable decomposition back to the original spaces.
This removes the complex-module hypothesis from the open-loop `W_g` bridge.

{docstring LinearSystem.finiteBohlWBridge_real}

The plant component of an arbitrary stable dynamic closed-loop orbit is a
variation-of-constants trajectory driven by the controller's resolved input.
Combined with the real-coordinate finite-Bohl bridge, this proves the first
Corollary 6.22 necessity inclusion `im E ≤ W_g(ker H)` for arbitrary
finite-dimensional real plant and input spaces, with controller state `X`.
Transposing the closed-loop response gives the corresponding dual inclusion,
and together with the existing observer construction proves the equivalence
for that controller class.

{docstring LinearSystem.range_E_le_outputStabilizableSubspace_of_stableNonzeroExternalResponse}
{docstring LinearSystem.stableNonzeroExternalResponse_dual}
{docstring LinearSystem.stableNonzeroExternalResponse_iff_externalStabilizationConditions}

The first inclusion also holds when the controller state is an arbitrary
finite-dimensional real space `W`; the generic proof extracts the plant
trajectory from a closed-loop state in `X × W`.

{docstring LinearSystem.range_E_le_outputStabilizableSubspace_of_genericStableResponse}

For the book's quantifier over controller order, the controller state space is
existentially quantified in `AnyStateStableExternalResponse`. The existing
observer construction gives sufficiency. The generic first-inclusion theorem
and its transposed application give both necessity inclusions for time-domain
decay. The Hurwitz-domain transfer-pole stability-to-decay bridge is now
provided by `TransferPoleDecay.lean` and lifted to this arbitrary-controller
quantifier in `TransferPoleControllerCriterion.lean`.

{docstring LinearSystem.AnyStateStableExternalResponse}
{docstring LinearSystem.anyStateStableExternalResponse_of_externalStabilizationConditions}
{docstring LinearSystem.first_inclusion_of_anyStateStableExternalResponse}

For a generic controller state `W`, the closed-loop operator and its
exponential are conjugate to the primal transposes under the product-dual
equivalence. The pointwise dual readout identity is also proved in explicit
channel form, avoiding an elaboration bottleneck in `externalResponse` over
dual spaces. Transposed channel decay then gives the second inclusion and the
arbitrary-state time-domain equivalence.

{docstring LinearSystem.genericW_closedLoopMap_apply}
{docstring LinearSystem.genericW_closedLoop_exp_apply}
{docstring LinearSystem.genericW_dualExplicitResponse}
{docstring LinearSystem.firstInclusion_of_explicitReadout}
{docstring LinearSystem.externalStabilizationConditions_of_anyStateStableExternalResponse}
{docstring LinearSystem.anyStateStableExternalResponse_iff_externalStabilizationConditions}

The channel-level spectral criterion identifies decay with the input range
lying in the sum of the unobservable and Hurwitz subspaces. It accounts for
unobservable non-Hurwitz modes, but does not itself formalize cancellation of
poles in a rational transfer function. A Hurwitz controllable–observable
realization is equivalent to channel decay: the converse uses observability
to exclude antistable modes of the reduced realization.

{docstring LinearSystem.channelReadout_tendsto_iff_range_le_unobservable_sup_hurwitz}
{docstring LinearSystem.channelReadout_tendsto_of_isHurwitz_minimalRealization}
{docstring LinearSystem.isHurwitz_minimalRealization_of_channelReadout_tendsto}
{docstring LinearSystem.isHurwitz_minimalRealization_iff_channelReadout_tendsto}

# Observer duality

The observation half of Corollary 6.22 follows from the state-feedback half by algebraic duality.
The annihilator of the smallest conditioned-invariant subspace `S*(im E)` is the largest
controlled-invariant subspace of the transposed pair, and the annihilator of the detectable
subspace is a reachable-plus-stable subspace of the transpose.

{docstring LinearMap.dualAnnihilator_conditionedInvariantSubspace}
{docstring LinearMap.dualAnnihilator_detectableSubspace}
{docstring LinearMap.conditionedInvariant_inf_detectable_le_ker_iff_dualStableCondition}

The transpose of the exponential is the exponential of the transpose, which converts the dual
observer readout into the primal one.

{docstring LinearMap.exp_smul_dualMap_eq}
{docstring LinearMap.exp_smul_dualMap_apply}

Running the state-feedback construction on the transposed pair and transporting the gain back with
`dualMap_surjective` produces the observer-error decay of TST Lemmas 6.20–6.21 under the Corollary
6.22 output-injection condition, in both the `A + G C` and the contract's `A - L C` conventions,
and finally in primal norm form.

{docstring LinearSystem.exists_outputInjection_dualReadout_tendsto_of_dualCondition}
{docstring LinearSystem.exists_observerError_dualReadout_tendsto_of_dualCondition}
{docstring LinearSystem.exists_observerError_readout_tendsto_of_dualCondition}
{docstring LinearSystem.exists_observerError_readout_tendsto_of_externalStabilizationConditions}

# Stable external response from the geometric conditions

The sufficiency direction of TST Corollary 6.22 is assembled from the feedback
quotient on `W_g/V*`, the observer quotient on `S*/T_g`, and the Hurwitz
triangular-product quotient for the observer-based dynamic controller. The
extended disturbance image lies in the invariant window, and the external
readout vanishes on its invariant denominator. Quotient decay therefore gives
a stable, possibly nonzero, external impulse response. The reverse implication
is also proved for arbitrary finite-dimensional controller state spaces by the
real-coordinate Bohl bridge and generic closed-loop duality. This is the
time-domain decay form; the Hurwitz-domain transfer-pole form is identified
with it in `TransferPoleControllerCriterion.lean`.

{docstring LinearSystem.stableNonzeroExternalResponse_of_externalStabilizationConditions}

For the converse, the closed-loop operator of the transposed plant and
controller is the algebraic transpose of the original closed-loop operator,
under the product-dual equivalence. A separate finite-dimensional theorem
transfers decay of a readout channel to its transpose. Together with the
real-space first-inclusion bridge, they prove both Corollary 6.22 subspace
inclusions for any stable controller in the fixed-state class.

{docstring LinearSystem.prodDualEquiv_closedLoopMap_apply}
{docstring LinearSystem.dualReadout_tendsto_of_readout_tendsto}

# Algebraic examples

These concrete algebraic examples exercise the pair API. In particular the planar rotation with
zero readout is not observable, and the failure is witnessed at the non-real complex
eigenvalue `I`, which is why the PBH bridge must complexify.

{docstring DynamicalSystems.Linear.Examples.doubleIntegrator_controllable}
{docstring DynamicalSystems.Linear.Examples.uncontrollable_not_controllable}
{docstring DynamicalSystems.Linear.Examples.unobservable_not_observable}
{docstring DynamicalSystems.Linear.Examples.rotation_complex_not_observable}
{docstring DynamicalSystems.Linear.Examples.rotation_real_not_observable}

The nonzero-feedthrough plant has `D = 1`. The innovation subtracts the direct input term, the
observer error dynamics is independent of `D`, and observability still yields a convergent
observer.

{docstring DynamicalSystems.Linear.Examples.feedthroughSystem}
{docstring DynamicalSystems.Linear.Examples.feedthroughSystem_innovation_readout}
{docstring DynamicalSystems.Linear.Examples.feedthroughSystem_naive_innovation_readout}
{docstring DynamicalSystems.Linear.Examples.feedthroughSystem_observerError_dynamics}
{docstring DynamicalSystems.Linear.Examples.feedthroughSystem_exists_stable_observer}

Disturbance decoupling by state feedback is demonstrated in both directions on the double
integrator, together with the static obstruction that no feedback can remove a direct
instantaneous term.

{docstring DynamicalSystems.Linear.Examples.not_isStateFeedbackDisturbanceDecoupled_of_apply_ne_zero}
{docstring DynamicalSystems.Linear.Examples.decoupling_possible_velocity}
{docstring DynamicalSystems.Linear.Examples.decoupling_impossible_position}
{docstring DynamicalSystems.Linear.Examples.decoupling_impossible_velocity}

The scalar output filter of the local switching-limited-tracking development is ported and
connected to the abstract trajectory API by a proved representation bridge.

{docstring DynamicalSystems.Linear.Examples.filterOutput}
{docstring DynamicalSystems.Linear.Examples.filterOutput_derivative}
{docstring DynamicalSystems.Linear.Examples.filterSystem}
{docstring DynamicalSystems.Linear.Examples.filterOutput_eq_variationOfConstants}

# Which API should I use?

A short decision guide for future proofs. Prefer the named `_iff` lemmas to unfolding
definitions.

* *Is this pair controllable or observable?* Start from `LinearMap.IsControllable` and
  `LinearMap.IsObservable`. For a finite-dimensional rank test use
  `LinearMap.isControllable_iff_surjective_kalmanControllabilityMap` and
  `LinearMap.isObservable_iff_injective_kalmanObservabilityMap`; for a spectral test use
  `LinearMap.isControllable_iff_hautus` and `LinearMap.isObservable_iff_hautus`.
* *The field is real and non-real eigenvalues are possible.* Complexify before applying PBH:
  `LinearMap.isControllable_iff_hautus_complex` and `LinearMap.isObservable_iff_hautus_complex`.
  The planar-rotation regression `DynamicalSystems.Linear.Examples.rotation_real_not_observable`
  is why the complexification bridge is substantive, not a renaming.
* *You need the reachable or unobservable subspace.* Use `LinearMap.reachableSubspace` and
  `LinearMap.unobservableSubspace` with the extremal properties `LinearMap.reachableSubspace_le`
  and `LinearMap.le_unobservableSubspace`. These are purely algebraic and need no dimension bound.
* *You have a trajectory question.* Use `LinearSystem.variationOfConstants` for the explicit
  curve, `LinearSystem.variationOfConstants_integral` and
  `LinearSystem.variationOfConstants_ae_hasDerivAt` for the identities, and
  `LinearSystem.ltiStateTrajectoryRel_existsUnique` for existence and uniqueness of the locally
  integrable trajectory. For reachability use `LinearSystem.reachableSetAt_eq_reachableSubspace`;
  for indistinguishability use `LinearSystem.indistinguishableOn_iff_mem_unobservableSubspace`. To
  push a flow through a continuous linear map intertwining the two generators use
  `LinearSystem.clm_map_exp_smul` (see F9 below).
* *You need an energy or Gramian argument.* Use `LinearSystem.inner_controllabilityGramian` and
  `LinearSystem.inner_observabilityGramian` with the positive-definiteness criteria
  `LinearSystem.controllabilityGramian_posDef_iff_isControllable` and
  `LinearSystem.observabilityGramian_posDef_iff_isObservable`. These require real inner-product
  spaces and a strictly positive horizon.
* *You want a gain, not just an existence statement.* Pole placement gives
  `LinearMap.exists_feedback_charpoly_of_isControllable`; the stabilization layer gives
  `LinearMap.isStabilizable_of_isControllable`,
  `LinearMap.exists_stabilizing_feedback_stable_attractive`, and dually
  `LinearMap.isDetectable_of_isObservable`,
  `LinearMap.exists_observer_stable_attractive_of_isObservable`. Never assume the gain exists: it
  is constructed.
* *You want decay from a spectral hypothesis.* Use `LinearMap.tendsto_exp_of_isHurwitz` for the
  homogeneous flow and `LinearMap.isStableOn_expFlow_of_isHurwitz` for the filter predicate. For a
  readout that vanishes on an invariant subspace use
  `LinearSystem.tendsto_readout_exp_of_isHurwitz_mapQ`; its state-feedback quotient form is
  `LinearSystem.tendsto_readout_exp_of_isHurwitz_quotient_on`.
* *You want to preserve a controlled- or conditioned-invariant subspace.* Use
  `LinearMap.isControlledInvariant_iff_exists_stateFeedback` and
  `LinearMap.isConditionedInvariant_iff_exists_outputInjection` to extract the witness, and
  `LinearMap.controlledInvariantSubspace` / `LinearMap.conditionedInvariantSubspace` for the
  extremal subspaces.
* *You want a dynamic measurement-feedback controller.* From a `(C, A, B)`-pair use
  `LinearSystem.exists_dynamicController_of_isCABPairBetween` and
  `LinearSystem.isClosedLoopDisturbanceDecoupled_of_isCABPairBetween`; well-posedness is
  `LinearSystem.DynamicInterconnection.IsWellPosed` (invertibility of `1 - D N`, automatic when
  `D = 0`). From the geometric condition use
  `LinearSystem.exists_feedback_tendsto_readout_of_corollary622`.
* *You want external stability.* Use `LinearSystem.externalStability_iff_geometricCertificate`
  for the exact-zero response, `LinearSystem.ExternalStabilizationConditions` for the Corollary
  6.22 subspace data, and
  `LinearSystem.bibo_and_externalZeroResponse_of_geometricCertificate_hurwitz` when the Hurwitz
  gains are available. The observer half is
  `LinearSystem.exists_observerError_readout_tendsto_of_externalStabilizationConditions`.
* *You are checking duality.* Use `LinearMap.isControllable_iff_isObservable_dualMap`,
  `LinearMap.dualAnnihilator_conditionedInvariantSubspace`, and
  `LinearMap.dualAnnihilator_unstableSubspace_eq_stableSubspace_dualMap`; the transpose of the
  exponential is `LinearMap.exp_smul_dualMap_eq`, with pointwise form
  `LinearMap.exp_smul_dualMap_apply`.

# Proof-reuse and redundancy audit

This section records a read-only audit of the completed linear-control corpus against the pinned
Mathlib `4.34.0-rc2`. It covers every declaration in `DynamicalSystems/Linear/*.lean` and
`DynamicalSystems/Linear/Examples/Algebra.lean` (roughly 940 named declarations) and looks for
(a) duplicated constructions, (b) repeated coordinate/base-change arguments, (c) recurring
finite-dimensional and zero-dimensional hypotheses, (d) repeated exponential/decay and
convolution reasoning, and (e) local lemmas that a checked common API already supplies.

Scope note. The audit task owns only this documentation file, so no module outside it was
modified. Every item below is a recorded recommendation rather than an applied change. Each
entry names the file and declarations, gives the reuse recommendation, states the risk of acting
on it, and says whether a follow-up task is justified. *Demonstrable* means the duplication is
textually present and a shared helper would remove it without changing a public signature;
*speculative* means the benefit is plausible but not yet established. The two cross-file refactors
with the best benefit-to-risk ratio are F1 and F8; the remaining items are either guidance or
deliberate design choices that should not be deduplicated.

## Reuse inventory: what is actually consumed

The verified reuse inventory listed in the source contract is largely consumed by the corpus:

* `Module.End.invtSubmodule` and `Module.End.mem_invtSubmodule_iff_map_le` are used by
  `LinearMap.reachableSubspace_mem_invtSubmodule` and
  `LinearMap.unobservableSubspace_mem_invtSubmodule` (`Subspaces.lean`).
* `LinearMap.pow_eq_aeval_mod_charpoly`, `Polynomial.aeval_eq_sum_range'` and
  `LinearMap.charpoly_natDegree` drive `LinearMap.exists_pow_eq_sum_finrank` (`Kalman.lean`).
* The duality lemmas `Submodule.dualAnnihilator_iSup_eq`,
  `LinearMap.ker_dualMap_eq_dualAnnihilator_range` and `Submodule.dualAnnihilator_eq_bot_iff`
  are used throughout `ConditionedInvariant.lean`, `DynamicFeedback.lean` and
  `Stabilization.lean`.
* `LinearMap.toContinuousLinearMap`, `Filter.IsStableOn`, `Filter.IsAttractive`,
  `stateTrajectoryRel` and `inputOutputRel` are used by the trajectory, stability and relation
  adapters.
* Conversely, `LinearEquiv.map_mem_invtSubmodule_conj_iff`,
  `Subspace.dualAnnihilator_dualCoannihilator_eq`, `Subspace.comap_dualAnnihilator_dualAnnihilator`,
  `isCaratheodoryLinear`, `isCaratheodoryLipschitz_linear`, `intervalIntegrable_linear` and
  `exists_unique_caratheodory_solution_global` have zero references in the Linear corpus. These
  are addressed in F2 and F18 below.

## Coordinate and base-change arguments

*F1. Repeated `conj`-power helper — implemented.* `LinearMap.reachableSubspace_changeState` and
`LinearMap.unobservableSubspace_changeState` in `Duality.lean`, and
`LinearMap.disturbanceResponse_changeState` in `DisturbanceDecoupling.lean`, each open with the
same anonymous local fact
`have hpow : ∀ k, (e.symm.conj A)^k = e.symm.conj (A^k) := fun k => (map_pow (LinearEquiv.conjRingEquiv e.symm) A k).symm`.
The underlying accepted API is `map_pow` applied to `LinearEquiv.conjRingEquiv`, but the pinned
Mathlib exposes no named `LinearEquiv.conj_pow` (searched), so the closed form is re-derived three
times. The shared `LinearEquiv.conj_pow` helper now packages this proof and all three sites use it
(commit `9c6ecc4`).

*F2. State-coordinate invariance for controlled and conditioned invariance — implemented.*
`ControlledInvariant.lean` proves input-coordinate invariance
(`LinearMap.isControlledInvariant_changeInput_iff`) but has no state-coordinate lemma, and
`ConditionedInvariant.lean` proves output-space invariance
(`LinearMap.isConditionedInvariant_changeOutput_iff`) but likewise has no state-coordinate
lemma. Mathlib provides the key ingredient,
`LinearEquiv.map_mem_invtSubmodule_conj_iff`. The reusable coordinate-transport lemmas
`LinearMap.isControlledInvariant_changeState_iff` and
`LinearMap.isConditionedInvariant_changeState_iff` now provide this result (commit `d673598`).
The former recommendation to add them is therefore complete. *Recommendation:* keep these APIs
central for future coordinate proofs. *Risk:* none.
*F3. `disturbanceResponse_changeState` is a special case of subspace transport.*
`LinearMap.disturbanceResponse_changeState` (`DisturbanceDecoupling.lean`) and
`LinearMap.reachableSubspace_changeState` (`Duality.lean`) both prove that an `iSup` of ranges is
carried along a conjugation; `reachableSubspace` is the `iSup` of `range ((A^k).comp B)`, and the
decoupled Markov data is `H.comp ((A^k).comp E)`. *Recommendation:* once F1 exists, derive
`disturbanceResponse_changeState` from the shared conjugation lemma plus
`LinearEquiv.conj_apply`, and consider a general `LinearMap.range_conj_pow_comp`. *Risk:* low.
*Follow-up:* optional; F1 already captures most of the value.

*F4. State/input/output coordinate boilerplate in `Basic.lean`.* The three coordinate changes
`LinearSystem.changeState`, `LinearSystem.changeInput` and `LinearSystem.changeOutput` are each
given four `rfl` projection lemmas (`_A`, `_B`, `_C`, `_D`) plus one or two evaluation lemmas
(`changeState_dynamics`, `changeState_readout`, `changeInput_dynamics`, `changeInput_readout`,
`changeOutput_readout`), about eighteen near-identical declarations. `changeOutput` is the only
one without a `changeOutput_dynamics` companion. *Recommendation:* keep as is; the public names
are part of the API and a single `changeCoordinates` record would be a breaking change. Record
only. *Risk:* high (API break). *Follow-up:* not justified for the available benefit.

## Finite-dimensional and zero-dimensional hypotheses

*F5. Two zero-dimensional dispatch styles.* `LinearMap.exists_feedback_charpoly_of_finrank_zero`
(`PolePlacement.lean`) branches on `Module.finrank ℝ X = 0` and converts with
`Module.finrank_zero_iff.mp`; the three `Stabilization.lean` corner lemmas
`LinearMap.hurwitzSubspace_eq_top_of_subsingleton`,
`LinearMap.stabilizableSubspace_eq_top_of_subsingleton` and
`LinearMap.detectableSubspace_eq_top_of_subsingleton` take `[Subsingleton X]` directly, as do the
`Examples/Algebra.lean` regressions `DynamicalSystems.Linear.Examples.zeroDim_controllable`,
`DynamicalSystems.Linear.Examples.zeroDim_observable`,
`DynamicalSystems.Linear.Examples.zeroDim_kalman_surjective` and
`DynamicalSystems.Linear.Examples.zeroDim_kalman_injective`. *Recommendation:* standardize the `finrank = 0` to `Subsingleton X`
conversion on `Module.finrank_zero_iff` / `finrank_zero_iff_forall_zero` and add a single
named dispatch lemma so the recurring `by_cases hzero : Module.finrank ℝ X = 0` is written once.
*Risk:* low. *Follow-up:* optional.

*F6. The `Subsingleton`-based `_eq_top` corner lemmas are load-bearing.*
`LinearMap.hurwitzSubspace_eq_top_of_subsingleton`,
`stabilizableSubspace_eq_top_of_subsingleton`,
`detectableSubspace_eq_top_of_subsingleton`, together with
`LinearMap.hurwitzSubspace_zero` and
`LinearMap.stabilizableSubspace_eq_top_of_isStabilizable`, all reduce to `Subsingleton.elim` or
the main characterisation. *Recommendation:* keep; they are the zero-dimensional branch used by
the main theorems, not incidental duplicates. *Risk:* low. *Follow-up:* not justified.

*F7. Adjoint/exponential reachable-subspace machinery already reuses Mathlib.*
`Gramian.lean` builds `LinearSystem.controllabilityGramian` and
`LinearSystem.observabilityGramian` on `ContinuousLinearMap.adjoint`, and the energy and
positive-definiteness proofs use
`ContinuousLinearMap.intervalIntegral_apply`, `ContinuousLinearMap.intervalIntegral_comp_comm`,
`ContinuousLinearMap.adjoint_inner_left`/`adjoint_inner_right` and `real_inner_self_eq_norm_sq`.
No local re-derivation of these adjoint facts was found. *Recommendation:* keep. *Risk:* none.
*Follow-up:* not justified.

## Exponential, decay and convolution reasoning

*F8. Repeated exponential power-series expansion — implemented.*
`LinearSystem.clm_map_exp_smul` (`DynamicFeedback.lean`, the only `maxHeartbeats 800000` site)
formerly contained two nearly identical blocks, `hAtsum` and `hBtsum`, that expand
`NormedSpace.exp (t • A) x` and `NormedSpace.exp (t • B) (L x)` as a `tsum` and then move the
continuous linear map through it with `ContinuousLinearMap.map_tsum` and `tsum_congr`.
`Stabilization.lean` has the same expansion pattern twice more in
`LinearMap.exp_nilpotent_eq_sum` and `LinearMap.exp_nilpotent_apply_eq_sum`. *Recommendation:*
extract `exp_smul_apply_eq_tsum`, a single rewrite of `NormedSpace.exp (t • A) x` to its factorial
series. `LinearMap.exp_smul_apply_eq_tsum` now provides the common rewrite and is used by
`clm_map_exp_smul` and the nilpotent pointwise proof (commit `1c62ffe`).

*F9. `LinearSystem.clm_map_exp_smul` is a reusable general lemma that the guide does not expose.*
`LinearSystem.clm_map_exp_smul` is the intertwining statement
`L (exp (t • A) x) = exp (t • B) (L x)` for `L ∘ A = B ∘ L`, and it is the engine behind
`LinearSystem.tendsto_readout_exp_of_isHurwitz_mapQ` and
`LinearSystem.tendsto_readout_exp_of_isHurwitz_quotient_on`. It is public but was absent from the
"Which API should I use?" decision guide and from the trajectory narrative; this audit adds the
decision-guide cross-reference. *Recommendation:* also mention it in the trajectory narrative.
*Risk:* none (documentation only). *Follow-up:* optional, as a one-line documentation change.

*F10. Convolution API is split across two modules but already factored.* The convolution
statements `LinearMap.forcedOutput_eq_convolution`,
`LinearMap.disturbanceContribution_eq_convolution` and
`LinearMap.isDisturbanceDecoupled_convolution_integral_eq_zero` live in
`DisturbanceDecoupling.lean`; the closed-loop specializations
`LinearSystem.DynamicInterconnection.externalResponse_eq_disturbanceImpulseResponse` and
`LinearSystem.DynamicInterconnection.disturbanceContribution_eq_convolution_externalResponse`
live in
`DynamicFeedback.lean` and reuse the former through
`LinearMap.disturbanceContribution_eq_convolution`. *Recommendation:* keep the split; there is no
second copy of the integral identity. *Risk:* low. *Follow-up:* not justified.

*F11. Gramian energy identities repeat the same integration skeleton.*
`LinearSystem.inner_controllabilityGramian` and `LinearSystem.inner_observabilityGramian`
(`Gramian.lean`) each define the integrand `L`, obtain continuity from
`LinearSystem.continuous_controllabilityIntegrand`/`LinearSystem.continuous_observabilityIntegrand`,
apply
`ContinuousLinearMap.intervalIntegral_apply`, move `innerSL` through the interval integral with
`ContinuousLinearMap.intervalIntegral_comp_comm`, and finish with `integral_congr` and the
adjoint identities. *Recommendation:* extract an `inner_intervalIntegral_apply` skeleton
parameterized by the continuity lemma, leaving only the adjoint bookkeeping in the two callers.
*Risk:* low to moderate. *Follow-up:* optional.

*F12. Scalar filter derivation already delegates to the common API.* In
`Examples/Algebra.lean`, `DynamicalSystems.Linear.Examples.filterOutput_derivative` uses
`intervalIntegral.integral_hasDerivAt_right`,
`DynamicalSystems.Linear.Examples.filterOutput_integral` uses
`intervalIntegral.integral_eq_sub_of_hasDerivAt`, and
`DynamicalSystems.Linear.Examples.filterOutput_eq_variationOfConstants` routes through
`LinearSystem.integralSolution_unique` and the variation-of-constants identities. The local
`DynamicalSystems.Linear.Examples.exp_cancel` is the only bespoke scalar fact and
is a two-line consequence of `Real.exp_add` and `Real.exp_zero`. *Recommendation:* keep; no
duplication of the abstract API. *Risk:* low. *Follow-up:* not justified.

## Positivity, duality and complexification

*F13. Local `IsPositiveDefinite` versus Mathlib `LinearMap.IsPositive`.*
`LinearSystem.IsPositiveDefinite` (`Gramian.lean`) is the strict predicate
`∀ x ≠ 0, 0 < inner ℝ x (T x)` and is used only by
`LinearSystem.controllabilityGramian_posDef_iff_isControllable` and
`LinearSystem.observabilityGramian_posDef_iff_isObservable`. Mathlib's
`LinearMap.IsPositive` (`Mathlib/Analysis/InnerProductSpace/Positive.lean`) is the
semidefinite, self-adjoint notion, and `QuadraticMap.PosDef` is a second candidate.
*Recommendation:* add a bridge
`IsPositiveDefinite T ↔ T.IsPositive ∧ Function.Injective T` (under self-adjointness and finite
dimension) so downstream reasoning can use Mathlib's positivity closure and eigenvalue API;
do not change the existing predicate, which is referenced by public signatures. *Risk:* moderate.
*Follow-up:* optional; only the bridge is recommended.

*F14. Double-annihilator API is available but unused.* `Subspace.dualAnnihilator_dualCoannihilator_eq`
and `Subspace.comap_dualAnnihilator_dualAnnihilator` from the verified inventory have zero
references,
whereas the corpus already avoids bases in its duality proofs. *Recommendation:* when adding
future `S*(E)`/`Xdet` duality lemmas, prefer the double-annihilator API over a fresh coordinate
construction. *Risk:* low. *Follow-up:* not justified as a standalone task; guidance only.

*F15. Hautus complexification uses entrywise real/imaginary maps, not `LinearMap.baseChange`.*
`Hautus.lean` defines `LinearMap.reFun`, `LinearMap.imFun`, `LinearMap.ofRealFun` and the
matrix-level bridges `LinearMap.mulVecLin_complexify_re`/`_im`/`_ofReal` and
`LinearMap.re_complex_pow`/`im_complex_pow`/`ofReal_complex_pow`. Mathlib has `LinearMap.baseChange`, but the Hautus statements are phrased for
`Matrix.mulVecLin` with `Matrix.map (algebraMap ℝ ℂ)`, so a `baseChange` rewrite would change the
ambient formulation, not merely the proof. *Recommendation:* keep the matrix formulation and reuse
Mathlib's `Complex` linear maps (`Complex.ofReal`, real/imaginary projections) only where the
entrywise definitions are unfolded. *Risk:* high if rewritten. *Follow-up:* not justified; a future
spec task could state a `baseChange` version separately.

*F16. `isDisturbanceDecoupled_iff_range_le_unobservableSubspace'` packages, not duplicates.*
The primed statement in `DisturbanceDecoupling.lean` adds the invariance and `≤ ker H` conjuncts to
the base `_iff` and is a two-line consequence of it. *Recommendation:* keep; it is the
"greatest invariant witness" packaging used downstream. *Risk:* low. *Follow-up:* not justified.

## Naming and hygiene observations

*F17. Intentional `_zero_input`/`_zero_state` name twins across namespaces.*
`LinearSystem.dynamics_zero_input`/`dynamics_zero_state` (`Basic.lean`) and
`LinearSystem.DynamicController.dynamics_zero_input`/`dynamics_zero_state` (`DynamicFeedback.lean`) share a
name but concern different structures and different `dynamics` definitions, and each is proved by
its own `simp [dynamics]`. *Recommendation:* keep; an automated deduplication must not merge them.
*Risk:* low. *Follow-up:* not justified.

*F18. The analysis-regularity inventory entries are deliberately not used.*
`isCaratheodoryLinear`, `isCaratheodoryLipschitz_linear`, `intervalIntegrable_linear` and
`exists_unique_caratheodory_solution_global` have zero references in the Linear corpus.
`Trajectory.lean` instead proves `LinearSystem.integralSolution_unique` directly through the
integrating-factor/`integral_hasDerivAt_right` argument, which is what the source contract's
analysis hints recommend for locally integrable forcing; the global Caratheodory theorem would
require compact-interval existence and uniqueness hypotheses that the direct proof does not need.
*Recommendation:* keep the direct proof and treat the global theorem as an alternative for future
nonlinear or non-autonomous extensions, not as a replacement. *Risk:* n/a. *Follow-up:* not
justified.

*F19. Warning/deprecation cleanup — implemented.* The corpus formerly reported 78 warnings, all in
`Gramian.lean` (13), `PolePlacement.lean` (36) and
`Stabilization.lean` (29); `Documentation.lean` itself reports none. The actionable categories are
22 over-long lines, 18 `show` tactic uses, 13 `if_neg`, 9 `if_pos`, 8 `Try this` suggestions, 6
`simpa` that should be `simp`, 5 unused `simp` arguments, 3 `dif_pos`, 2 `push_neg`, 2
`ContinuousLinearMap.mul_apply`, 2 `ContinuousLinearMap.smul_apply`, 1 `dif_neg`, 1 unconsumed
`ext` pattern, and 2 missing-space strings. These are exactly the "replace a local or deprecated
name with the accepted common API" opportunities (`if_pos`/`if_neg` to `ite_eq_left`/`ite_eq_right`,
`dif_pos`/`dif_neg` to `dite_eq_left`/`dite_eq_right`, `push_neg` to `push Not`,
`ContinuousLinearMap.mul_apply`/`smul_apply` to `mul_apply_eq_comp`/`_root_.smul_apply`).
The dedicated hygiene task cleaned these without declaration changes (commit `7c60d08`); only
three non-blocking `abel_nf` information hints remain.

## Duplication that was checked and deliberately retained

The following apparent duplications are correct as written and should not be refactored:

* `LinearMap.isControllable_changeState`/`isObservable_changeState` (`Duality.lean`) versus the
  `LinearSystem.isControllable_changeState`/`isObservable_changeState` wrappers: the wrappers are
  one-line delegations through `changeState_A`/`changeState_C`, exactly the intended layer.
* `LinearMap.map_hurwitzSubspace_restrict_le`/`LinearMap.map_unstableSubspace_restrict_le`
  versus `LinearMap.map_iSup_maxGenEigenspace_restrict_le` (`Stabilization.lean`): the common transport lemma is
  already extracted, and the two wrappers differ only in the predicate `μ.re < 0` versus
  `¬ μ.re < 0`.
* `LinearMap.hautusObservabilityMatrix`/`LinearMap.hautusControllabilityMatrix` versus the
  Kalman matrices in
  `Kalman.lean`: the Hautus matrices are given directly by `LinearMap.toMatrix` of the
  `[A - μI; C]`/`[A - μI | B]` maps, whereas the Kalman matrices assemble the power block; they
  characterize the same pair but by different statements (per-`μ` PBH versus all-powers Krylov)
  and both are part of the source ledger.

## Residual risk and summary

No declaration was found to be a vacuous duplicate of another, and no local lemma was found that a
single existing checked Mathlib declaration replaces verbatim. The genuine, low-risk reuse
reductions F1, F2, F8, and F19 are now implemented. F5, F11 and F13 are
optional clean-ups; F15 and F4 should not be attempted without a dedicated API-change task. The
corpus is free of placeholder or trust-basis proof tokens (the standard forbidden-tactic scan over
`DynamicalSystems/Linear/` returns no match), and the only heartbeat override is the justified
`set_option maxHeartbeats 800000 in` guarding `clm_map_exp_smul`.

# Theorem-to-source-page table

A compact index from the conceptual layers to representative Lean declarations and their
Trentelman–Stoorvogel–Hautus ("TST") source location. "PDF" is the one-based physical page of
the supplied book; where a chapter or section is more useful than a single page it is given
directly.

:::table +header
*
  * Layer
  * Representative Lean declarations
  * TST source
  * PDF / printed
*
  * Algebraic subspaces
  * `LinearMap.reachableSubspace`, `LinearMap.unobservableSubspace`
  * Corollary 3.3; §3.3 (3.7)
  * 54 / 40
*
  * Kalman tests
  * `LinearMap.kalmanControllabilityMap`, `..._iff_surjective_...`
  * Corollaries 3.2–3.4; Theorem 3.8
  * §3.2–3.3
*
  * Duality and four-block
  * `LinearMap.isControllable_iff_isObservable_dualMap`, `LinearMap.kalmanEquiv`
  * Theorems 3.10–3.11; Exercise 3.7
  * 57–59 / 43–45
*
  * PBH / Hautus
  * `LinearMap.isControllable_iff_hautus`, `..._iff_hautus_complex`
  * Theorem 3.13; §3.5
  * §3.5
*
  * Trajectories
  * `LinearSystem.variationOfConstants`, `..._integral`
  * equation (2.19); §3.1
  * 41 / 27
*
  * Gramians
  * `LinearSystem.controllabilityGramian`, `..._posDef_iff_isControllable`
  * §5.2–5.3
  * §5.2–5.3
*
  * Geometric invariance
  * `LinearMap.IsControlledInvariant`, `LinearMap.IsConditionedInvariant`
  * Theorem 4.2; Theorem 5.5
  * 90 / 76; 123 / 109
*
  * ISA / CISA
  * `LinearMap.controlledInvariantSubspace`, `LinearMap.conditionedInvariantSubspace`
  * Theorems 4.5, 4.10, 5.6–5.8
  * §4.3; §5.1
*
  * Pole placement
  * `LinearMap.exists_feedback_charpoly_of_isControllable`
  * Theorem 3.29
  * 72–74 / 58–60
*
  * Spectral subspaces
  * `LinearMap.stabilizableSubspace`, `LinearMap.detectableSubspace`
  * Theorems 4.26, 4.30, 5.15, 5.16
  * §4.6; §5.2
*
  * Hurwitz decay
  * `LinearMap.tendsto_exp_of_isHurwitz`
  * Theorem 2.6 region
  * §2.6
*
  * Disturbance decoupling
  * `LinearMap.IsDisturbanceDecoupled`, `..._iff_exists_invariant`
  * Theorems 4.6, 4.8; Corollary 4.9
  * §4.2–4.3
*
  * Dynamic feedback
  * `LinearSystem.exists_dynamicController_of_isCABPairBetween`, `...IsWellPosed`
  * Theorems 6.2, 6.4, 6.6
  * §6.1–6.2
*
  * External stability
  * `LinearSystem.externalStability_iff_geometricCertificate`,
    `LinearSystem.ExternalStabilizationConditions`
  * Theorems 6.6, 4.39; Corollaries 6.7, 6.22
  * 159–160 / 145–146
*
  * Observer duality
  * `LinearSystem.exists_observerError_readout_tendsto_of_dualCondition`
  * Lemmas 4.35, 6.20, 6.21
  * §6.6
:::

In the external-stability row the first declaration is the exact-zero criterion (TST Theorem 6.6 /
Corollary 6.7); the second records the stable-nonzero Corollary 6.22 subspace conditions, whose
geometric equivalence for controllers with state space `X` is proved by
`LinearSystem.stableNonzeroExternalResponse_iff_externalStabilizationConditions`.
The arbitrary-controller-state time-domain version is
`LinearSystem.anyStateStableExternalResponse_iff_externalStabilizationConditions`.

# Source-to-theorem ledger

This ledger maps every source statement used by the release to its checked Lean declaration. It
covers all accepted modules. In the entries, "TST" abbreviates Trentelman, Stoorvogel and
Hautus, *Control Theory for Linear Systems*, and "LF" abbreviates Gokhale and Bullo,
*LeanForControl*, commit `c5cedca904fe7b8168643c428b5cf5fd8b6ebf6d`.

## `DynamicalSystems.Linear.Basic`

* TST equations (2.1)–(2.3) and (3.1): the system data `x' = A x + B u`, `y = C x + D u`;
  Lean `LinearSystem`, `LinearSystem.dynamics`, `LinearSystem.readout`.
* State feedback `u = F x + v` (TST Section 3.2): Lean `LinearSystem.stateFeedback`.
* State equivalence `x = S x̄`, `Ā = S⁻¹ A S`, `B̄ = S⁻¹ B`, `C̄ = C S`, `D̄ = D`
  (TST (3.8)–(3.9)): Lean `LinearSystem.changeState` and its projection lemmas.

## `DynamicalSystems.Linear.Subspaces`

* Reachable subspace `⟨A | im B⟩` (TST Section 3.2): Lean `LinearMap.reachableSubspace`,
  `LinearMap.range_le_reachableSubspace`, `LinearMap.reachableSubspace_le`.
* Unobservable subspace `⟨ker C | A⟩` (TST Section 3.3): Lean
  `LinearMap.unobservableSubspace`, `LinearMap.unobservableSubspace_le_ker`,
  `LinearMap.le_unobservableSubspace`.
* Controllability `⟨A | im B⟩ = X` and observability `⟨ker C | A⟩ = 0`: Lean
  `LinearMap.IsControllable`, `LinearMap.IsObservable`.
* Invariance `A V ≤ V` (TST Section 2.4): Lean `Submodule.map A V ≤ V`, bridged to
  `Module.End.invtSubmodule` by `Module.End.mem_invtSubmodule_iff_map_le`,
  `LinearMap.reachableSubspace_mem_invtSubmodule`,
  `LinearMap.unobservableSubspace_mem_invtSubmodule`.

## `DynamicalSystems.Linear.Kalman`

* Kalman rank tests (TST Corollary 3.4(iii) and Theorem 3.8(v)): Lean
  `LinearMap.kalmanControllabilityMap`, `LinearMap.kalmanObservabilityMap`,
  `LinearMap.isControllable_iff_surjective_kalmanControllabilityMap`,
  `LinearMap.isObservable_iff_injective_kalmanObservabilityMap`.
* Cayley–Hamilton reduction of all powers to the first `dim X` powers (TST Sections 3.2–3.3):
  Lean `LinearMap.reachableSubspace_eq_iSup_finrank`,
  `LinearMap.unobservableSubspace_eq_iInf_finrank`.

## `DynamicalSystems.Linear.KalmanDecomposition`

* Kalman controllable/unobservable decomposition and the four-block coordinate change
  (TST Theorem 3.11 and Exercise 3.7): Lean `LinearMap.kalmanEquiv`,
  `LinearMap.controllableObservableRealization`, and the vanishing off-diagonal block lemmas.
* Invariance of the Markov parameters under the realization (TST Theorem 3.10(iii)): Lean
  `LinearMap.controllableObservableRealization_markov`.

## `DynamicalSystems.Linear.Duality`

* Duality `(A, B)` controllable iff `(Aᵀ, Bᵀ)` observable (TST Section 3.3): Lean
  `LinearMap.isControllable_iff_isObservable_dualMap`,
  `LinearMap.isObservable_iff_isControllable_dualMap`.
* Reachable restriction and unobservable quotient (TST Section 3.4): Lean
  `LinearMap.isControllable_reachableRestriction`,
  `LinearMap.isObservable_quotientUnobservable`.

## `DynamicalSystems.Linear.Hautus`

* PBH eigenvalue criteria over an algebraically closed field (TST Theorem 3.13 and
  equations (3.13)–(3.14)): Lean `LinearMap.isControllable_iff_hautus`,
  `LinearMap.isObservable_iff_hautus`, adapting LF `isControllable_iff_hautus` and
  `isObservable_iff_hautus` to the fixed `(C, A)` order.
* Real complexification bridge for the PBH test (TST Section 3.5, planar-rotation warning):
  Lean `LinearMap.isControllable_complexify_iff`, `LinearMap.isObservable_complexify_iff`,
  `LinearMap.isControllable_iff_hautus_complex`, `LinearMap.isObservable_iff_hautus_complex`.

## `DynamicalSystems.Linear.Trajectory`

* Operator exponential and homogeneous solution (TST (2.15)–(2.16)): Lean
  `LinearSystem.expFlow`, `LinearSystem.homogeneousSolution`,
  `LinearSystem.hasDerivAt_expFlow_apply_state`.
* Variation of constants (TST (2.19)): Lean `LinearSystem.variationOfConstants`,
  `LinearSystem.variationOfConstants_integral`,
  `LinearSystem.variationOfConstants_ae_hasDerivAt`,
  `LinearSystem.variationOfConstants_isCaratheodorySolutionOn`.
* Existence and uniqueness for locally integrable inputs: Lean
  `LinearSystem.ltiStateTrajectoryRel_existsUnique`,
  `LinearSystem.ltiInputOutputRel_existsUnique`, with feedthrough retained in
  `LinearSystem.mem_ltiInputOutputRel_iff`.

## `DynamicalSystems.Linear.ControlledInvariant`

* Controlled invariance `A V ≤ V + im B` (TST Theorem 4.2): Lean
  `LinearMap.IsControlledInvariant`,
  `LinearMap.isControlledInvariant_iff_exists_stateFeedback`.
* Invariant subspace algorithm `V₀ = K`, `V_{k+1} = K ∩ A⁻¹(V_k + im B)` (TST (4.9)): Lean
  `LinearMap.controlledInvariantSeq`, `LinearMap.isGreatest_controlledInvariantSubspace`.

## `DynamicalSystems.Linear.ConditionedInvariant`

* Conditioned invariance `A (S ∩ ker C) ≤ S` (TST Definition 5.1): Lean
  `LinearMap.IsConditionedInvariant`,
  `LinearMap.isConditionedInvariant_iff_exists_outputInjection`.
* Duality with controlled invariance (TST Section 4.4): Lean
  `LinearMap.isControlledInvariant_iff_isConditionedInvariant_dualMap` (declared in
  `ConditionedInvariant.lean`).
* Conditioned invariant subspace algorithm `S₀ = E`, `S_{k+1} = E + A(S_k ∩ ker C)`
  (TST (5.5)–(5.6)): Lean `LinearMap.conditionedInvariantSeq`,
  `LinearMap.isLeast_conditionedInvariantSubspace`.

## `DynamicalSystems.Linear.Reachability`

* Indistinguishability `C e^{tA} v = 0` (TST Definition 3.6 and Theorem 3.8(iv)): Lean
  `LinearSystem.indistinguishableOn_iff_mem_unobservableSubspace`.

## `DynamicalSystems.Linear.Gramian`

* Reachable set equals the algebraic reachable subspace for positive horizons (TST
  Theorem 3.1): Lean `LinearSystem.reachableSetAt_eq_reachableSubspace` (declared in
  `Gramian.lean`, not in `Reachability.lean`).
* Controllability and observability Gramians and their energy identities (TST Sections 3.2–3.3):
  Lean `LinearSystem.controllabilityGramian`, `LinearSystem.observabilityGramian`,
  `LinearSystem.inner_controllabilityGramian`, `LinearSystem.inner_observabilityGramian`.
* Positive definiteness exactly for controllable/observable pairs: Lean
  `LinearSystem.controllabilityGramian_posDef_iff_isControllable`,
  `LinearSystem.observabilityGramian_posDef_iff_isObservable`.

## `DynamicalSystems.Linear.PolePlacement`

* Feedback invariance of the reachable subspace and controllability (TST Theorem 3.29): Lean
  `LinearMap.reachableSubspace_add_comp`, `LinearMap.isControllable_add_comp`.
* Companion / characteristic-polynomial infrastructure and the controlled-chain reduction:
  Lean `LinearMap.charpoly_eq_of_companion`, `LinearMap.exists_controlled_chain`.
* Full pole placement for monic real polynomials (TST Theorem 3.29): Lean
  `LinearMap.exists_feedback_charpoly_of_isControllable`,
  `LinearMap.isControllable_of_forall_exists_feedback_charpoly`.

## `DynamicalSystems.Linear.Stabilization`

* Hurwitz spectral predicate and stabilizability/detectability (TST Sections 3.10–3.11): Lean
  `LinearMap.IsHurwitz`, `LinearMap.IsStabilizable`, `LinearMap.IsDetectable`.
* Gain existence from controllability/observability, with the explicit target `(X + 1)^n`: Lean
  `LinearMap.isStabilizable_of_isControllable`, `LinearMap.isDetectable_of_isObservable`.
* Hurwitz-to-decay and Lyapunov stability (TST Theorem 3.13 and Section 3.11): Lean
  `LinearMap.tendsto_exp_of_isHurwitz`, `LinearMap.isStableOn_expFlow_of_isHurwitz`,
  `LinearMap.exists_stabilizing_feedback_stable_attractive`.
* PBH converse criteria for uncontrollable/unobservable eigenvalues: Lean
  `LinearMap.isStabilizable_of_uncontrollableEigenvalues_hurwitz`,
  `LinearMap.isDetectable_of_unobservableEigenvalues_hurwitz`.
* Separation-principle block spectrum: Lean `LinearMap.charpoly_blockOperator`,
  `LinearMap.exists_separation_block_hurwitz`.
* Stable/antistable spectral subspaces and their complementarity (TST Theorem 2.6 and
  Section 4.6): Lean `LinearMap.hurwitzSubspace`, `LinearMap.unstableSubspace`,
  `LinearMap.isCompl_hurwitzSubspace_unstableSubspace`,
  `LinearMap.hurwitzSubspace_sup_unstableSubspace_eq_top`.
* Stabilizable/detectable subspaces and the stabilizability/detectability characterisations
  (TST Theorems 4.26, 4.30, 5.15, 5.16): Lean `LinearMap.stabilizableSubspace`,
  `LinearMap.detectableSubspace`, `LinearMap.isStabilizable_iff_stabilizableSubspace_eq_top`,
  `LinearMap.isDetectable_iff_detectableSubspace_eq_bot`,
  `LinearMap.isHurwitz_on_stabilizableComplement`,
  `LinearMap.isHurwitz_on_detectableComplement`.
* Basis-independent spectral API and the transpose stable/antistable duality: Lean
  `LinearMap.stableSubspaceOfBasis`, `LinearMap.unstableSubspaceOfBasis`,
  `LinearMap.stableSubspaceOfBasis_eq_of_basis`,
  `LinearMap.dualAnnihilator_unstableSubspace_eq_stableSubspace_dualMap`.

## `DynamicalSystems.Linear.Observer`

* Feedthrough-aware innovation `y - C ξ - D u` (TST Section 3.11, equations (3.40)–(3.43)):
  Lean `LinearSystem.innovation`, `LinearSystem.innovation_readout`.
* Observer error dynamics `e' = (A - L C) e`, independent of the input and of `D`: Lean
  `LinearSystem.observerVectorField`, `LinearSystem.observerError_dynamics`,
  `LinearSystem.observerError_dynamics_stateFeedback`,
  `LinearSystem.separation_error_independent_of_feedback`.
* Convergent observer from observability, with a constructed gain: Lean
  `LinearMap.exists_observer_attractive_of_isObservable`,
  `LinearMap.exists_observer_stable_attractive_of_isObservable`.
* Observer-based separation principle: Lean `LinearMap.separation_principle_observer`,
  `LinearMap.not_unobservableEigenvalue_of_isDetectable`.

## `DynamicalSystems.Linear.DisturbanceDecoupling`

* Markov parameters `H A^k E` and exact decoupling `T = 0` (TST (4.4)): Lean
  `LinearMap.disturbanceResponse`, `LinearMap.IsDisturbanceDecoupled`.
* Invariant-subspace characterisation `im E ≤ V ≤ ker H` (TST Theorem 4.6): Lean
  `LinearMap.isDisturbanceDecoupled_iff_exists_invariant`.
* State-feedback decoupling and the compact criterion `im E ≤ V*(ker H)` (TST Theorem 4.8
  and Corollary 4.9): Lean
  `LinearMap.isStateFeedbackDisturbanceDecoupled_iff_exists_controlledInvariant`,
  `LinearMap.isStateFeedbackDisturbanceDecoupled_iff_range_le_controlledInvariantSubspace`.
* `(C, A, B)`-pairs and the algebraic core of Corollary 6.7: Lean
  `LinearMap.IsCABPairBetween`, `LinearMap.exists_isCABPairBetween_iff`.
* Analytic impulse response and the variation-of-constants/convolution bridge (TST (3.2)–(3.3)):
  Lean `LinearMap.isDisturbanceDecoupled_iff_forall_expFlow`,
  `LinearMap.forcedOutput_eq_convolution`,
  `LinearMap.isDisturbanceDecoupled_iff_forall_disturbanceContribution_eq_zero`.
* Transfer-function/resolvent form under `s > ‖A‖`: Lean
  `LinearMap.disturbanceTransferFunction_eq_resolvent`,
  `LinearMap.isDisturbanceDecoupled_of_forall_resolventTransferFunction_eq_zero`.

## `DynamicalSystems.Linear.TransferPoleStability`

For a scalar finite-dimensional matrix channel, the adjugate formula defines a
complex rational transfer function. Its reduced denominator divides the state
characteristic polynomial, so Hurwitz state spectrum implies stable transfer
poles. The numerator agrees with determinant times the resolvent channel value
at nonsingular points, and evaluation of the reduced rational function agrees
with the resolvent there. A zero-output lemma illustrates why the converse requires
controllability and observability. For the controllable–observable realization,
Hurwitz stability implies pole stability of every complexified transfer-matrix entry.

{docstring RatFunc.IsPoleStable}
{docstring RatFunc.eval_mk_of_eval_ne_zero}
{docstring Matrix.channelTransferRatFunc}
{docstring Matrix.channelTransferRatFunc_denom_dvd_charpoly}
{docstring Matrix.channelTransferRatFunc_isPoleStable_of_spectrum}
{docstring Matrix.channelTransferNumerator_eval_eq_det_mul_resolvent}
{docstring Matrix.channelTransferRatFunc_eval_eq_resolvent}
{docstring LinearSystem.charpoly_complexified_realMatrix}
{docstring LinearSystem.controllableObservableRealization_entry_transfer_poleStable}

## `DynamicalSystems.Linear.MinimalPoleCancellation`

For a controllable and observable complex realization, a characteristic root
with nonzero evaluated adjugate survives cancellation in at least one scalar
transfer entry. This uses local Hautus reachability and observability to show
the Cramer numerator is nonzero. A separate minimal-realization lemma shows
that if all Markov parameters vanish after applying a polynomial `q` to the
state map, then `q(A) = 0`.

{docstring Matrix.exists_scalar_transfer_pole_of_minimal_rank_one_root}
{docstring LinearMap.aeval_eq_zero_of_markov_annihilation}

## `DynamicalSystems.Linear.TransferNumeratorDegree`

The scalar Cramer numerator has degree strictly below the state characteristic
polynomial, including a separate zero-dimensional case. Hence divisibility by
the characteristic polynomial forces the numerator to vanish.

{docstring Matrix.channelTransferNumerator_natDegree_lt}
{docstring Matrix.channelTransferNumerator_eq_zero_of_charpoly_dvd}

## `DynamicalSystems.Linear.TransferDenominatorRecurrence`

A polynomial multiple of a reduced scalar transfer denominator annihilates
every Markov parameter after evaluation at the state matrix. This is proved
with a finite adjugate recurrence, without an expansion at infinity.

{docstring Matrix.channel_markov_annihilation_of_denom_dvd}

## `DynamicalSystems.Linear.MinimalTransferPoles`

For a controllable and observable complex matrix realization, every
characteristic root is a pole of at least one reduced transfer-matrix entry,
including repeated roots (setwise, without a multiplicity assertion).
Consequently, all entry poles are left-half-plane exactly when the
realization's characteristic roots are left-half-plane; the same equivalence
is proved for a complexified real matrix realization.

{docstring Matrix.exists_scalar_transfer_pole_of_minimal}
{docstring Matrix.all_channels_pole_stable_iff_charpoly_hurwitz_of_minimal}
{docstring Matrix.real_all_channels_pole_stable_iff_charpoly_hurwitz_of_minimal}

## `DynamicalSystems.Linear.TransferCoordinateBridge`

Finite-basis matrix representations preserve controllability and
observability. For the controllable–observable realization, every complexified
transfer entry has left-half-plane poles exactly when its state map is Hurwitz.

{docstring LinearSystem.minimalRealizationAllChannelsPoleStable}
{docstring LinearSystem.controllableObservableRealization_all_channels_poleStable_iff_hurwitz}

## `DynamicalSystems.Linear.TransferPoleDecay`

For a real finite-dimensional channel, pole stability of the reduced minimal
realization transfer matrix is equivalent to decay of every impulse-response
direction. This is the Hurwitz (open left-half-plane) choice only.

{docstring LinearSystem.controllableObservableRealization_all_channels_poleStable_iff_channelReadout_tendsto}

## `DynamicalSystems.Linear.TransferPoleControllerCriterion`

With arbitrary finite-dimensional controller state and a strictly proper
plant, the closed-loop external transfer-pole predicate is equivalent to the
time-domain response predicate and to the two Corollary 6.22 geometric
conditions, for Hurwitz stability.

{docstring LinearSystem.AnyStatePoleStableExternalResponse}
{docstring LinearSystem.anyStatePoleStableExternalResponse_iff_anyStateStableExternalResponse}
{docstring LinearSystem.anyStatePoleStableExternalResponse_iff_externalStabilizationConditions}

## `DynamicalSystems.Linear.TransferPoleDomains`

The minimal-realization pole/spectrum equivalence works for any chosen set of
complex numbers `Cg`. No decay or geometric-stabilization equivalence is
asserted for an arbitrary domain.

{docstring RatFunc.HasPolesIn}
{docstring Matrix.all_channels_poles_in_iff_charpoly_roots_in_of_minimal}
{docstring Matrix.real_all_channels_poles_in_iff_charpoly_roots_in_of_minimal}
{docstring LinearSystem.MinimalRealizationAllChannelsPolesIn}
{docstring LinearSystem.minimalRealizationAllChannelsPolesIn_iff_spectrum}

## `DynamicalSystems.Linear.TransferPoleFeedthrough`

For a well-posed dynamic interconnection, including nonzero plant feedthrough
`D` and measurement disturbance feedthrough `F`, the total disturbance map
determines the external transfer poles. Its Hurwitz pole criterion is equivalent
to impulse-response decay. This is not a feedthrough-generalized version of the
Corollary 6.22 geometric iff. Setting both feedthrough maps to zero recovers the
previous transfer-pole criterion.

{docstring LinearSystem.DynamicInterconnection.externalPolesIn_iff_minimalSpectrum}
{docstring LinearSystem.DynamicInterconnection.externalPolesIn_leftHalfPlane_iff_response_tendsto}
{docstring LinearSystem.AnyStateWellPosedExternalPolesIn}
{docstring LinearSystem.AnyStateWellPosedStableExternalResponse}
{docstring LinearSystem.anyStateWellPosedExternalPolesIn_leftHalfPlane_iff_stableExternalResponse}
{docstring LinearSystem.anyStateWellPosedExternalPolesIn_zero_iff_anyStatePoleStableExternalResponse}

## `DynamicalSystems.Linear.DynamicFeedback`

* Dynamic measurement-feedback controller from a `(C, A, B)`-pair (TST Theorem 6.4): Lean
  `LinearSystem.DynamicController`, `LinearSystem.exists_dynamicController_of_isCABPairBetween`.
* Well-posedness of the algebraic loop as invertibility of `1 - D N` (TST Section 6.2): Lean
  `LinearSystem.DynamicInterconnection.IsWellPosed`.
* Closed-loop disturbance decoupling (TST Theorem 6.4): Lean
  `LinearSystem.isClosedLoopDisturbanceDecoupled_of_isCABPairBetween`.
* Geometric external zero-response criterion (TST Theorem 6.6 and Corollary 6.7): Lean
  `LinearSystem.GeometricCertificate`, `LinearSystem.ExternalStability`,
  `LinearSystem.externalStability_iff_geometricCertificate`.
* Corollary 6.22 subspace conditions and BIBO/zero-response combination: Lean
  `LinearSystem.ExternalStabilizationConditions`,
  `LinearSystem.externalStabilizationConditions_of_externalStability`,
  `LinearSystem.bibo_and_externalZeroResponse_of_geometricCertificate_hurwitz`.
* Quotient-spectrum decay and the Lemma 4.38 feedback construction (TST Lemma 4.35, Theorem
  4.37, Lemma 4.38): Lean `LinearSystem.tendsto_readout_exp_of_isHurwitz_mapQ`,
  `LinearSystem.tendsto_readout_exp_of_isHurwitz_quotient_on`,
  `LinearSystem.exists_feedback_tendsto_readout_of_corollary622`.
* Finite-Bohl forcing-image output-stabilization identity (TST Theorem 4.37 variant): Lean
  `LinearSystem.finiteBohlWBridge`, `LinearSystem.finiteBohlSynthesis`,
  `LinearSystem.isBohlOutputStabilizable_iff_mem_outputStabilizableSubspace_complete`.
* Observer/output-injection duality (TST Lemmas 6.20–6.21): Lean
  `LinearMap.dualAnnihilator_conditionedInvariantSubspace`,
  `LinearMap.conditionedInvariant_inf_detectable_le_ker_iff_dualStableCondition`,
  `LinearMap.exp_smul_dualMap_eq`, `LinearMap.exp_smul_dualMap_apply`,
  `LinearSystem.exists_observerError_readout_tendsto_of_externalStabilizationConditions`.

## `DynamicalSystems.Linear.Examples.Algebra`

* Double integrator controllability and observability (TST Example 3.9 pattern): Lean
  `DynamicalSystems.Linear.Examples.doubleIntegrator_controllable`,
  `DynamicalSystems.Linear.Examples.doubleIntegrator_observable`.
* Non-controllable and non-observable pairs (TST Example 3.5 and Example 3.9): Lean
  `DynamicalSystems.Linear.Examples.uncontrollable_not_controllable`,
  `DynamicalSystems.Linear.Examples.unobservable_not_observable`.
* Real rotation with zero readout: non-real PBH witness (TST Section 3.5): Lean
  `DynamicalSystems.Linear.Examples.rotation_real_not_observable_hautus`.
* Nonzero-feedthrough observer (TST Section 3.11): Lean
  `DynamicalSystems.Linear.Examples.feedthroughSystem_exists_stable_observer`.
* Possible/impossible disturbance decoupling (TST Theorems 4.6 and 4.8): Lean
  `DynamicalSystems.Linear.Examples.decoupling_possible_velocity`,
  `DynamicalSystems.Linear.Examples.decoupling_impossible_position`,
  `DynamicalSystems.Linear.Examples.decoupling_impossible_velocity`.
* Scalar filter representation bridge (local switching-limited-tracking project): Lean
  `DynamicalSystems.Linear.Examples.filterOutput_eq_variationOfConstants`.

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

The resolvent transfer-function form `H (s I - A)⁻¹ E = 0` is proved in both directions under the
explicit hypothesis `s > ‖A‖`; the unqualified all-`s` rational-function statement is not claimed.

Exact-zero external response is characterised geometrically by a `(C, A, B)`-pair. A stable (possibly nonzero) external
impulse response is equivalent to the two Corollary 6.22 subspace conditions
even when the finite-dimensional controller state is arbitrary, using the
observer-based construction and the real-space dual necessity proof. Reduced
rational transfer-pole stability is now identified with that decay criterion
for the left-half-plane stability domain. Arbitrary stability domains `C_g`
have a minimal-realization pole/spectrum bridge but no general geometric iff.
The stabilizable/detectable spectral subspaces, state-feedback and output-injection constructions,
and transpose-exponential pairing are formalized with explicit finite-dimensional and
admissibility hypotheses. The Corollary 6.22 geometric iff assumes a strictly proper plant
(`D = 0`). For nonzero `D` or measurement disturbance feedthrough `F`, the well-posed
transfer-pole/response-decay bridge is formalized separately, without claiming the geometric iff.

Out of scope: the nonlinear theory of Trentelman–Stoorvogel–Hautus Chapters 7–15 (system zeros and
strong observability, distributions and system invertibility, tracking and regulation, and the
LQ, H₂ and H∞ chapters) and the nonlinear algebraic-methods reference of Conte, Moog and Perdon.
Those chapters are not formalized and no linear declaration is claimed to represent them. Optional
refinements not yet claimed include the sharp dimension bound for the ISA/CISA stationary index,
the trajectory/observer reading (i) of the geometric invariance definitions as a separate bridge,
and continuous-time minimal-realization statements. The examples module supplies the
nonzero-feedthrough observer, the possible/impossible decoupling instances, the planar-rotation
PBH regression, and the proved scalar-filter representation bridge.

# Consistency and fullness review

This is a read-only cross-check of the completed corpus against its own declarations and against
the supplied Trentelman–Stoorvogel–Hautus text. Every `{docstring ...}` target and every
backticked API name in the ledger was resolved with `#check`; each ledger name was matched to its
declaring module with `rg`; the theorem-map PDF pages were spot-checked against the supplied PDF.
No proof declaration, statement, or declaration docstring outside this manual was changed. The
severity ranking is High, Medium, Low; "non-owned" marks a defect in a proof module that this
documentation-only review records but cannot edit.

:::table +header
*
  * Severity
  * Area
  * Finding and evidence
  * Status
*
  * Medium
  * Nomenclature
  * `LinearSystem.ExternalStability` is the exact-zero (decoupling) response, but the manual
    called external stability "stable-nonzero"; the source's Corollary 6.22 stable-nonzero
    property is separate (`DynamicFeedback.lean`, `def ExternalStability`).
  * Corrected in the prose above.
*
  * Medium
  * Fullness overclaim
  * The fixed-state stable-nonzero criterion must not be presented as the book's
    arbitrary-controller-state version of Corollary 6.22.
  * The fixed-state and arbitrary-state iff declarations are distinguished above.
*
  * Medium
  * Stale handoff (non-owned)
  * `DynamicFeedback.lean` module notes still call the Lemma 4.38 feedback construction, the
    Lemma 4.35 quotient bridge, and the transpose-stable transport unformalised or unavailable
    (lines 229, 2942, 4013–4135), contradicting
    `tendsto_readout_exp_of_isHurwitz_mapQ`, `exists_feedback_tendsto_readout_of_corollary622`,
    `dualAnnihilator_unstableSubspace_eq_stableSubspace_dualMap`, and
    `exists_observerError_readout_tendsto_of_externalStabilizationConditions`.
  * Follow-up cleanup needed in `DynamicFeedback.lean` (non-owned).
*
  * Low
  * Source attribution
  * The theorem-map row attributed `externalStability_iff_geometricCertificate` to TST Theorems
    6.6 and 4.39 and Corollaries 6.7 and 6.22; that declaration is the exact-zero criterion alone
    (Theorem 6.6 / Corollary 6.7).
  * Corrected in the table row.
*
  * Low
  * Ledger module attribution
  * `LinearSystem.reachableSetAt_eq_reachableSubspace` was listed under `Reachability` but is
    declared in `Gramian.lean` (line 531);
    `LinearMap.isControlledInvariant_iff_isConditionedInvariant_dualMap` was listed under
    `ControlledInvariant` but is declared in `ConditionedInvariant.lean` (line 321).
  * Corrected in the ledger.
*
  * Low
  * Reference names
  * The reuse audit cited `Module.finrank_zero_iff_forall_zero` (actual root name
    `finrank_zero_iff_forall_zero`) and `DynamicController.dynamics_zero_input` (actual
    `LinearSystem.DynamicController.dynamics_zero_input`); `LinearMap.range_conj_pow_comp` (F3) is
    a proposed name, not a declaration.
  * Corrected in the audit text; F3 remains a recommendation only.
*
  * Low
  * Observer sign convention
  * The Lean error is `ξ - x` (estimate minus true state; `Observer.lean` header), while the
    source contract writes `x - xhat`; both satisfy `e' = (A - L C) e`
    (`LinearSystem.observerError_dynamics`).
  * Recorded here; no code change.
*
  * Low
  * Accepted synonyms
  * The stable subspace appears as `hurwitzSubspace` and `stableSubspaceOfBasis` (bridged by
    `stableSubspaceOfBasis_finBasis_eq_hurwitzSubspace`), and the source's "antistable" is Lean
    `unstableSubspace`. These are deliberate, documented synonyms.
  * Accepted.
*
  * Info
  * Source pages
  * Every theorem-map PDF/printed pair satisfies the linear book's constant offset 14, spot-checked
    against the PDF (PDF 54 = printed 40, PDF 73 = printed 59, PDF 160 = printed 146).
  * Verified; no change.
:::

Positive checks that passed: all `{docstring ...}` targets and all ledger names resolve; every
ledger name is declared in or re-exported through its stated module; no forbidden proof placeholder
or trust-basis construct occurs in `DynamicalSystems/Linear`; and the standard audit reports
only the three standard axioms.
