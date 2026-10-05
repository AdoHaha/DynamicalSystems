# Kirk–Medhin proof handoff v2

This branch contains the cumulative Lean implementation and regression checks for the second Kirk–Medhin handoff. The companion campaign changes and original verification archive are published in `auto_automatyk`. Both sets of changes are on dedicated review branches; they have not been merged into `DynamicalSystems/kirk_medhin-ralph` or `auto_automatyk/master`.

| Resource | Location |
| --- | --- |
| Lean implementation branch | [AdoHaha/DynamicalSystems — codex/kirk-medhin-proof-handoff-v2](https://github.com/AdoHaha/DynamicalSystems/tree/codex/kirk-medhin-proof-handoff-v2) |
| Campaign branch | [LiderMyHand/auto_automatyk — codex/kirk-medhin-proof-handoff-v2](https://github.com/LiderMyHand/auto_automatyk/tree/codex/kirk-medhin-proof-handoff-v2) |
| Handoff guide and evidence | [Published handoff directory](https://github.com/LiderMyHand/auto_automatyk/tree/codex/kirk-medhin-proof-handoff-v2/notes/kirk_medhin/handoffs/2026-10-05-v2) |
| Original verified archive | [kirk_medhin_proof_handoff.zip](https://github.com/LiderMyHand/auto_automatyk/blob/codex/kirk-medhin-proof-handoff-v2/notes/kirk_medhin/handoffs/2026-10-05-v2/kirk_medhin_proof_handoff.zip?raw=true) |

The source baseline is `5dc581d52ba95cac849321e7d0c26ba3574310b3` on `kirk_medhin-ralph`. The companion campaign baseline is `94632e8e561e4674aa3e36e491e184980b758e26` on `master`. Lean is pinned to `4.35.0-rc2` (`11acb17ec6b07a8f9e9173e6845197929540936b`), with Mathlib at `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

## Get the implementation

For a new checkout:

```bash
git clone --branch codex/kirk-medhin-proof-handoff-v2 \
  https://github.com/AdoHaha/DynamicalSystems.git
git clone --branch codex/kirk-medhin-proof-handoff-v2 \
  https://github.com/LiderMyHand/auto_automatyk.git
```

For an existing clean checkout, fetch the relevant remote and switch to `codex/kirk-medhin-proof-handoff-v2`. Record the resulting commit with `git rev-parse HEAD` when assigning agent work. The branch already contains all 45 native Lean files in the cumulative handoff: 34 library modules, 7 regression modules and 4 audit documents. Do not apply either archive patch again on top of this branch.

Use both review branches together. Before dispatching a campaign worker, inspect `automation/kirk_medhin/campaign.json` and verify that its integration/worker worktrees contain this Lean implementation. The configuration retains the existing `kirk_medhin-ralph` integration branch name; publication of a separate branch does not automatically update those worktrees.

## Import the existing results

The main direct endpoint is:

```lean
import DynamicalSystems.OptimalControl.ContinuousTime.NeedlePMPOnHorizon

#check K1NeedlePMPOnHorizon.needleCostate_of_integralOptimality_onHorizon
```

| Scope | Module after `DynamicalSystems.OptimalControl.ContinuousTime.` | Declaration |
| --- | --- | --- |
| K0: smooth HJB implies PMP | `DynamicProgrammingMinPrincipleFromHJB` | `hjbPMPAssembly_of_residual` |
| K1: direct normal PMP on a finite horizon | `NeedlePMPOnHorizon` | `K1NeedlePMPOnHorizon.needleCostate_of_integralOptimality_onHorizon` |
| K1: companion direct theorem | `NeedlePMP` | `K1NeedlePMP.needleCostate_of_integralOptimality_smooth` |
| K1: literal augmented Hahn–Banach route | `GeometricMinimumPrinciple` | `KirkMedhin.K1.integralOptimal_implies_PMP_via_hahnBanach_of_integral_reference` |
| K3: partial multiplier interface | `ConstrainedCoVMultipliers` | `IsoperimetricVariation.exists_firstVariation_multiplier_of_curve_family` |
| K4: two smooth autonomous arcs | `TimeReparametrizationFamily` | `KirkMedhin.TimeReparametrization.corner_energy_eq_of_cvFunctional_min` |
| K5: minimum-fuel Hamiltonian minimizers | `MinimumFuel` | `MinimumFuel.hamiltonianMinimizing_iff_switchingLaw` |

Both K1 routes start from actual integral optimality and conclude the existing costate, transversality and Hamiltonian-minimum predicates. The direct horizon theorem requires continuous nominal/test branches, uniform state-Lipschitz dynamics on the horizon, actual nominal spatial derivatives jointly continuous on the horizon/state product, terminal differentiability and a positive horizon. Its companion allows derivative continuity at reference-graph points with explicit global-time branch extensions. The Hahn–Banach route is finite-dimensional and uses stronger global branch hypotheses for both dynamics and running cost. Consult the actual statements and `PROOF_NOTES.txt` before choosing a theorem.

Do not replace integral optimality by the old everywhere-differentiable competitor class: an exact-project counterexample is included. The branch also repairs nonautonomous flow composition and supplies a genuinely time-dependent regression. A separate counterexample rules out unrestricted PMP-to-optimality and DP-iff-PMP claims.

Full **K3 remains pending** beyond the proved multiplier interface: actual parameterized-integral differentiation, first-variation identification, a sufficiently rich family and the augmented Euler–Lagrange argument are still obligations. Full **general weak K4 remains pending**: the proved corner theorem assumes two smooth autonomous arcs and actual arcwise Euler–Lagrange equations. General measurable/switching-control PMP, endpoint constraints and abnormal multipliers are separate extensions. K5 classifies minimizers; it does not prove trajectory optimality. Read the companion `NEXT_STEPS.txt` before assigning new proof work.

## Verification and reproduction

The recorded targeted verification passed with:

- **57** freshly built project modules in the delivered/dependency/affected-caller closure; **0 warnings and 0 errors**.
- **173** transitive axiom audits allowing only `propext`, `Classical.choice` and `Quot.sound`.
- **19** required declarations across **6** compiled campaign scopes, plus **46** actual proof-term dependency checks.
- **41** exact-module declaration lint results using all **15** default Batteries linters: **480** declarations and **269** generated declarations; no suppressions or lint errors.
- **212** pinned upstream Lean sources checked against Git blob hashes and **3** successful patch round trips.
- Companion campaign validation: **10** regression tests passed; **7** manifest tasks validated with **0 errors and 0 warnings**.

The archive contains the source hashes, complete logs, semantic reviews and portable verifier. Extract it, set `HANDOFF` to the directory containing its `SOURCE_MANIFEST.json`, then run from this Lean checkout:

```bash
bash "$HANDOFF/dynamical_systems/verify.sh"
```

The verifier checks source hashes and pins, rebuilds the 50 library modules in the targeted closure through normal Lake, explicitly compiles the 7 regression modules and runs the 4 audit documents. It retains fresh logs and rejects warnings, errors, incomplete audit output and nonstandard axioms.

The recorded Lean checks were executed using an isolated pinned Lean environment. The portable normal-Lake script was syntax checked and reviewed with actual-log parsing, injected failures and mocked orchestration; it was **not fully executed in an ordinary Lake checkout** during handoff preparation. No full-repository or Verso-site build is claimed. The original archive is preserved unchanged, so its `remote_changes: false` and local-only wording describe the verification phase before GitHub publication.

Mechanical success does not change campaign acceptance state. A reviewing coordinator should inspect the precise theorem contracts and discharged premises before accepting a scoped task. Agents should extend the pending obligations from this branch instead of reimplementing the completed K1 constructions or dispatching the obsolete false targets.
