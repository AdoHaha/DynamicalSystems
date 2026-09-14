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
is formalized under an explicit factorization hypothesis; the geometric necessary-and-
sufficient external-stability converse and observer dual are now formalized with
explicit finite-dimensional and admissibility hypotheses.

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

External stability is a *stable-nonzero* notion, distinct from exact disturbance decoupling. The
exact-zero response property is captured separately from BIBO stability, so the two are never
conflated.

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
  for indistinguishability use `LinearSystem.indistinguishableOn_iff_mem_unobservableSubspace`.
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
  * `LinearSystem.externalStability_iff_geometricCertificate`
  * Theorems 6.6, 4.39; Corollaries 6.7, 6.22
  * 159–160 / 145–146
*
  * Observer duality
  * `LinearSystem.exists_observerError_readout_tendsto_of_dualCondition`
  * Lemmas 4.35, 6.20, 6.21
  * §6.6
:::

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
* Duality with conditioned invariance (TST Section 4.4): Lean
  `LinearMap.isControlledInvariant_iff_isConditionedInvariant_dualMap`.

## `DynamicalSystems.Linear.ConditionedInvariant`

* Conditioned invariance `A (S ∩ ker C) ≤ S` (TST Definition 5.1): Lean
  `LinearMap.IsConditionedInvariant`,
  `LinearMap.isConditionedInvariant_iff_exists_outputInjection`.
* Conditioned invariant subspace algorithm `S₀ = E`, `S_{k+1} = E + A(S_k ∩ ker C)`
  (TST (5.5)–(5.6)): Lean `LinearMap.conditionedInvariantSeq`,
  `LinearMap.isLeast_conditionedInvariantSubspace`.

## `DynamicalSystems.Linear.Reachability`

* Reachable set equals the algebraic reachable subspace for positive horizons (TST
  Theorem 3.1): Lean `LinearSystem.reachableSetAt_eq_reachableSubspace`.
* Indistinguishability `C e^{tA} v = 0` (TST Definition 3.6 and Theorem 3.8(iv)): Lean
  `LinearSystem.indistinguishableOn_iff_mem_unobservableSubspace`.

## `DynamicalSystems.Linear.Gramian`

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

External stability is recorded in two distinct forms and they are never identified. The exact-zero
response is characterised geometrically by a `(C, A, B)`-pair; the stable-nonzero (BIBO) property
additionally requires the Hurwitz gain data. The stabilizable/detectable spectral subspaces, the
Corollary 6.22 conditions, the state-feedback and output-injection constructions, the
transpose-exponential pairing, and the primal observer-error readout decay are formalized with
their explicit finite-dimensional and admissibility hypotheses. The external-stability statements
assume a strictly proper plant (`D = 0`); the general feedthrough-well-posedness case is left to
the hypotheses of `LinearSystem.DynamicInterconnection.IsWellPosed`.

Out of scope: the nonlinear theory of Trentelman–Stoorvogel–Hautus Chapters 7–15 (system zeros and
strong observability, distributions and system invertibility, tracking and regulation, and the
LQ, H₂ and H∞ chapters) and the nonlinear algebraic-methods reference of Conte, Moog and Perdon.
Those chapters are not formalized and no linear declaration is claimed to represent them. Optional
refinements not yet claimed include the sharp dimension bound for the ISA/CISA stationary index,
the trajectory/observer reading (i) of the geometric invariance definitions as a separate bridge,
and continuous-time minimal-realization statements. The examples module supplies the
nonzero-feedthrough observer, the possible/impossible decoupling instances, the planar-rotation
PBH regression, and the proved scalar-filter representation bridge.
