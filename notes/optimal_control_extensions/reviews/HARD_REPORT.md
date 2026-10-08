# Hard optimal-control proof report

Worktree: `/home/igor/zabawy/auto_automatyk/.worktrees/hard-worker`
Branch: `remaining-optimal-control-hard-worker`; base: `96dfa29`.
Continuation of WIP commit `8a48c9d`; this report records the validated scope, not
completion of the deferred book theorems. A matching `HARD_REPORT.md` snapshot is
included in the worktree commit; this main-workspace file is the campaign report.

## H1 — analytic Cesari argument proved; full existence remains open

Book anchor: BM Theorem 5.4.4; proof §5.4, Step 3,
equations (5.4.29)–(5.4.32), using Lemmas 5.3.6–5.3.7.

Module: `OptimalControl/ContinuousTime/CesariExistenceArgument.lean`.
Proved declarations:

- `sum_mem_convexHull_tail`, `exists_weights_of_mem_convexHull_tail`;
- `exists_tendsto_tail_convex_combinations_of_weak_tendsto`,
  `tendsto_tail_convex_combinations`;
- `exists_ae_tendsto_tail_convex_combinations_of_weak_Lp_tendsto`,
  `exists_weights_ae_tendsto_of_weak_Lp_tendsto`;
- `mem_of_weakCesariProperty_of_tail_combinations`,
  `velocityCost_liminf_mem_of_weakCesariProperty`;
- `ae_velocityCost_liminf_mem_and_lintegral_le`;
- `exists_integrable_cost_epigraph_of_cesari_combinations`;
- `exists_integrable_cost_epigraph_of_weak_Lp_tendsto`.

The last theorem constructs common finite tail weights from weak Lp velocity
convergence, extracts a.e. strong velocity convergence, then constructs an
integrable real cost majorant with feasible limiting epigraph point and integral
at most the limiting sequence cost. It does not assume convexity of the epigraph.
`hcesari` is consumed by the pointwise lower-closure lemma after taking a
cost-dependent subsequence; Fatou proves the integral bound and a.e. finite liminf.

Load-bearing headline inputs: property (Q) recovers feasibility; state convergence
locates the fiber; original epigraph membership supplies tail feasibility;
nonnegative integrable costs permit Fatou and integrable convex combinations;
convergence of cost integrals bounds their liminf; weak velocity convergence
constructs Mazur weights. The version with supplied combinations uses the weight
positivity, normalization, escaping support, and a.e. convergence explicitly.
Reuse: merged `CesariExistence` lower closure, mathlib equality of weak/norm
closures for convex sets, Lp convergence in measure and its a.e. subsequence,
Fatou, and Bochner integral identities.

Additional Step 4 infrastructure in
`Mathlib/MeasureTheory/MeasurableSigmaCompactLift.lean`:
`DynamicalSystems.MeasurableLift.exists_measurable_lift_of_continuous_sigmaCompact`.
A continuous map from a nonempty sigma-compact metric space to a second-countable
metric space has a measurable lift of every measurable attainable target.
Compact covers, compact measurable argmin, and a measurable first attainable
cover index construct the lift. Continuity supplies closed compact images and
zero-distance recovery; sigma-compactness and attainability supply an index;
measurability supplies the selected map. Reuses `MeasurableArgmin`.

**Exact remaining H1 work:**

1. Encode the noncompact, state-dependent control constraint and relaxed
   epigraph of Assumption 5.4.1, including variable endpoint times and the
   lower cost bound/shift. Existing compact-control, fixed-horizon problem APIs
   do not express this full statement.
2. Extract uniform trajectory convergence and weak **L1** derivative convergence
   from the compact/equi-absolutely-continuous minimizing sequence. The existing
   `WeakL2Compactness` gives Hilbert-space energy-ball compactness; equi-absolute
   continuity alone supplies no L2 energy bound. A weak L1 compactness result
   (Dunford–Pettis or the corresponding equi-AC trajectory theorem) is missing.
3. Prove that the limiting derivative satisfies the limiting trajectory integral
   law, endpoints remain admissible, and terminal cost passes to the limit.
4. Construct the book's sigma-compact relaxed epigraph domain and apply the lift
   theorem to obtain measurable finite atomic relaxed controls, with the actual
   dynamics and cost identities. A generic lift is not yet that realization.
5. Assemble comparison with the minimizing infimum into admissible optimality.

`exists_relaxedMinimizer_of_weakCesariProperty` is **not declared**. Assuming weak
compactness, feasible recovery, or optimality as an extra certificate would leave
these steps unproved and would not establish the requested full BM headline.

## H2 — normality/extreme controls proved; horizontal variation remains open

Module: `OptimalControl/ContinuousTime/MinimumTimeTransversality.lean`.
Book anchors: Definition 6.7.4, Corollary 6.7.5, Theorems 6.7.9/6.7.14/6.8.1.
Declarations: `mem_extremePoints_of_unique_linear_minimum`,
`HasLinearControlNormality`, `ae_mem_extremePoints_of_linearControlNormality`,
`ae_mem_extremePoints_of_cyclic_box_minimizing`.

Unique linear minimizers are exposed and hence extreme. For a general control
set, system normality, nonzero terminal covector, admissibility, and the a.e.
Hamiltonian minimum each enter the proof. For a box, the per-input cyclic/Krylov
rank condition and nonzero covector give a.e. nonzero switching coefficients;
the minimum fixes each coordinate, hence gives uniqueness and extreme values.
Reuse: merged analytic switching-zero and box minimizer results, mathlib exposed
points. This is conditional on an actual Hamiltonian minimum, not a new complete
time-optimal maximum principle. Combined Kalman controllability must not be
substituted for the stronger per-input rank condition.

**Exact remaining H2(a) work:** BM Theorem 6.3.22, equations (6.3.24)–(6.3.26),
proof §7.11, requires the clock/duration augmentation
`t = t0 + s (t1 - t0)`, `t' = w`, `w' = 0`, `x' = w f` and running cost `w f0`.
Prove the variable-time/augmented fixed-time admissibility correspondence and
integral cost equality, transfer optimality, check augmented regularity, apply
necessity, and translate the extra costates and endpoint tangent conditions.
The present `Problem.IsRelaxedMinimum` compares only competitors at its fixed
`P.horizon`; it provides no optimality against horizontal variations.
`FreeTerminalTimeTransversality` remains an assumed predicate in the merged module.
No theorem here derives it from fixed-horizon optimality. General 6.3.22 is the
extended endpoint orthogonality statement; `H(T)=0` is its free-terminal-time
specialization with suitable endpoint/terminal-cost independence.

## H3 — not closed

Book anchor: Theorem 6.3.9, growth condition (6.3.13).
No unbounded-control maximum-principle theorem is added. Remaining work is an
unbounded-control problem API, compact truncations compatible with the reference
pair and variations, growth-based uniform estimates, normalized multiplier
subsequence extraction with nontrivial limiting multipliers, and passage of
adjoint/transversality/Hamiltonian inequalities through the exhaustion. Proving
separate compact-control principles does not supply coherent limiting multipliers.

## H4 — complementarity and integrability proved; full R1 ⇒ R6b remains open

Module: `OptimalControl/ContinuousTime/StateConstraintComplementarity.lean`.
Book anchors: necessary multiplier data in Theorem 11.6.3; sufficiency in
Theorem 11.8.4. Proved:

- `multiplierMeasure_Ioi_eq_zero_of_terminal_collar`;
- `ae_constraint_eq_zero_of_const_on_slack`;
- `integral_constraint_eq_zero_of_const_on_slack`;
- `integral_stateConstraint_eq_zero_of_multiplier_const_on_slack`;
- `integrableOn_stateConstraint_of_regularity`;
- `intervalIntegrable_stateGradient_velocity_of_regularity`;
- `intervalIntegrable_multiplier_stateGradient_velocity_of_regularity`.

The contextual complementarity theorem accepts the interval constancy and positive
terminal collar returned by R1 and an admissible reference path. It proves
`integral G d(multiplierMeasure) = 0`, hence the sufficiency inequality. It does
not assume complementarity. Anti-monotonicity defines the Stieltjes measure;
slack constancy excludes support in the strict-slack region; the collar removes
terminal support; continuity and admissibility locate support in the contact set.
The collar is shrunk internally, so R1 need not provide an extra radius bound.

Regularity supplies measurable bounded G/Gx on the compact trajectory image;
velocity integrability and operator norm bounds supply gradient/velocity
integrability; multiplier monotonicity supplies its measurability and boundedness.
Reuse: `StateMultiplierStieltjes`, `EpsilonLevelBridge` composition integrability,
and mathlib measure-support and bounded-integrability lemmas.

**Exact remaining H4 work:** apply these lemmas to the complete R1 output and
derive the sufficiency Hamiltonian/costate identity with compatible ordinary
reference control and the required normality/convexity/endpoint assumptions.
In particular R1 has the total-gradient term `Gxd(t,x)(1,x')`; sufficiency requires
the derivative of its Hamiltonian in x. A proof needs the corresponding
time-gradient and spatial derivative identities, not a renamed input certificate.
Moreover `hG_prim` in `StateConstrainedSufficiency` assumes
`G(s,x(s)) = G(0,x(0)) + integral Gx(r,x(r)) x'(r)`.
`StateConstraintRegularity` only differentiates in x and permits time-dependent G,
so it cannot imply this formula: `G(t,x) = sin t + x` along a constant scalar path
already has a nonzero time contribution. This is a mathematical mismatch, not
an integrability obligation; restrict to autonomous G or establish a sufficiency
version containing the time derivative before claiming the full bridge.

## Wiring and validation

All four new modules are imported alphabetically by `DynamicalSystems.lean` and
included in `scripts/check_remaining_optimal_control.sh`.
`DynamicalSystemsTest/HardOptimalControl.lean` audits all 22 new theorem declarations.

Final validation (2026-10-09, Lean v4.35.0-rc2):

- `lake env lean` on each of the four new modules: exit 0, zero output and zero
  warnings. The check script now enforces the zero-warning gate for these modules.
- `lake build DynamicalSystems`, via the check script: successful, 4247 jobs.
  Existing unchanged dependencies emit replayed baseline warnings; the new modules
  emit none. No dependency linter settings were changed.
- `bash scripts/check_remaining_optimal_control.sh`: exit 0, including all existing
  extension audit files and the new hard-item audit file.
- Forbidden proof-token and linter-suppression search on the four new modules and
  audit file: empty. The script also rejects linter suppressions in the new modules.
- Every new theorem's printed dependencies are subsets of
  `{propext, Classical.choice, Quot.sound}`; no proof-escape axioms appear.
- `git diff --check`: clean.

Full H1 existence, H2(a) horizontal transversality, H3, and the full H4 costate/
primitive bridge remain open as itemized above. No full headline is claimed merely
because the partial modules build.
