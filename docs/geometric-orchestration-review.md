# Review of geometric-control orchestration and the Krener handoff

Reviewed `LiderMyHand/auto_automatyk` at
`a24af23362101d31bf55e703292272251aee65ff` (also the observed head of
`linear-control-ralph`) and the relevant interfaces in `AdoHaha/DynamicalSystems`
at `451db05eff60098a4074dd50af51e06f3f283314` (`geometric-ralph`). This note reviews
the handoff and workflow; it does not replace the separate proof audit.

## Current contribution status: G13 and G14

The user extended the work to the full recorded Frobenius target. Its locally
compiled solution is tracked as the separate task `g14-smooth-frobenius`, with four
new modules and the exact consumer `docs/frobenius-check.lean`. G13 is confirmed
published at `5363557a03de3bf47d34978082432b8332fbba57` on
`prove-geometric-frobenius` from baseline `451db05`. A separate locally validated
G14 commit is being packaged on that same branch; integration will record its
exact final source SHA and publication outcome.

| Claim | Current mathematical status | Integration record |
|---|---|---|
| `krenerLemma` and both `C¹` chart statements | Proved and published | Verified G13 commit above on `prove-geometric-frobenius` |
| `exists_sol_of_fderiv_compat` | Locally validated: smooth local graph solution on an open domain, with actual derivatives | Separate G14 commit being packaged on the same branch |
| `frobeniusTheorem_holds : frobeniusTheorem` | Locally validated proof of the full corrected smooth target | Exact final G14 source SHA to be recorded by integration |
| General involutive-frame normalization | Open extension beyond the graph-connection target | Future task |
| Chow flow-word and reachable-endpoint bridges | Open | Future task |

G14 is local and finite-dimensional. Its input is a smooth compatible graph
connection; its solution passes through every prescribed point and is smooth on
one open neighborhood. It does not assert a manifold-level global foliation.
The remaining frame-normalization task is not a hidden premise of the proved
compatible-PDE theorem.

## Campaign repairs implemented after this review

The accompanying patch fixes the executable gap-ledger and ownership defects
described below. It adds schema validation with clear CLI failures, restores the
geometric ledger as an object with explicit baseline-open mathematical tasks, and
makes both loops stop on a failed preflight or post-acceptance gap report.

G13 now owns the seven new modules, the scoped existing-file integration repairs,
coordinator-reviewed root imports, and exact supporting documentation paths.
The additive `support_files` field is backward-compatible: these files participate
in ownership and acceptance hashes without being mistaken for Lean proof source.
The requested umbrella module is built, so root imports cannot be accepted solely
against an old compiled artifact. Acceptance stages the actual changed owned paths,
without requiring every listed support artifact to exist.
An explicit `lean_checks` entry makes `docs/krener-check.lean` mandatory and compiles
it after the module build, so the exact-type consumer is part of acceptance.
The separate G14 entry checks `docs/frobenius-check.lean` and reruns the Krener
consumer; its own files and support artifacts are not folded into G13's scope.
G14 also owns the narrow helper repairs found by the full `lake lint --` gate:
two redundant `@[simp]` registrations are removed from `FrameComplement`, and
the unused dimension parameter is removed from `simultaneousRectifyingMap` and
its zero lemma in `MultiFlow`. These changes preserve the exact Krener and
Frobenius endpoint types and are recorded after the published G13 checkpoint.

Validation: 15 focused regression tests pass, including the original bare-array
failure, empty and malformed JSON, a valid empty ledger, missing gap actions,
both loop failure paths, missing/failing exact-type consumers, umbrella-module gate
coverage, and real temporary Git
worktree acceptance of root/support changes with another support path absent. Changes
to support documents after verification still invalidate acceptance, and unrelated
files remain rejected. `campaign.py gaps --harvest`, `campaign.py validate
--strict`, and `git diff --check` also pass. The tests do not claim to recheck Lean
mathematics or run a model campaign.

The review's mathematical findings below are pinned historical observations.
After the local G13 theorem compiled, its exact source was inspected and both
authoring requests were replaced by one explicit integration contract: `krenerLemma`
takes `hf`, `hind`, and local bracket vanishing `hcomm`, and proves the existing
`SimultaneouslyRectifiable` target. The forward and inverse chart are `C¹`, and
trajectory rectification needs only chart-source membership. The ledger records
the verified published G13 resolutions and the locally validated G14 result being
packaged as a separate commit on the same branch.
The later G14 request records the now-proved smooth compatible-PDE theorem and
the proof inhabiting the original target. The historical findings below explain
the starting point and are not a claim that those completed proofs remain missing.

## What worked

The variational contribution received a substantial independent review pinned to
its actual commit and toolchain. `PI_REVIEW_VAR.md` distinguishes the proved
spatial derivative, operator ODE, and fixed-base-point transport from the still
missing uniform hypotheses. The G10/G11 correction tasks preserve those
distinctions, and `PI_REVIEW_G12.md` examines the quantifier order and the actual
discharge of the residual premises. These are meaningful semantic reviews, not
only build reports. The worker/integration separation and acceptance hash checks
also protect the reviewed changes from unrelated edits.

The problem is that the conclusions of these reviews are compressed too far in
the next authoring prompt and are not reconciled into a reliable current status.

## Findings and concrete repairs

### 1. The G13 prompt advertises a stronger commutation interface than exists

`PROMPT_GPT_PRO_KRENER.md`, lines 15–17, writes commutation at a variable `y`.
The actual `flowsCommute_unconditional_onBox` at `FlowTransport.lean:821–827`
concludes commutation **at the one base point `x₀`**. The uniform variational
ingredients quantify over nearby points, but the final commutation theorem
does not export that quantifier. `PI_REVIEW_G12.md` itself explicitly recognizes
this at lines 137–138.

The proposed joint-flow chart starts at `x₀ + ι z`, and its nested flow tails move
the starting point further. Reapplying the theorem centered at each such point
would use separately chosen local flows; agreement with the original base flows
and the common time domain must then be justified. Thus “order is immaterial
because G12” omits real integration work.

Repair: put the **actual printed type** in the next prompt and make the missing
consumer interface its own task. One route is uniform commutation of the same
chosen flows on a smaller neighborhood. Another is to expose the uniform
pushforward identity `DΦ_t(y) (g y) = g (Φ_t y)` from the existing transport
proof, then differentiate the finite composition directly. The latter need not
reorder all the flows.

Sources: [G13 prompt](https://github.com/LiderMyHand/auto_automatyk/blob/a24af23362101d31bf55e703292272251aee65ff/notes/geometric_control/reviews/PROMPT_GPT_PRO_KRENER.md),
[actual commutation theorem](https://github.com/AdoHaha/DynamicalSystems/blob/451db05eff60098a4074dd50af51e06f3f283314/DynamicalSystems/Control/Geometric/FlowTransport.lean),
[G12 review](https://github.com/LiderMyHand/auto_automatyk/blob/a24af23362101d31bf55e703292272251aee65ff/notes/geometric_control/reviews/PI_REVIEW_G12.md).

### 2. A permitted G13 solution can fail the ownership gate

`REQUEST_G13_PROOF.md:7–9` permits a new sibling
`SimultaneousRectification.lean`, as does the external prompt. However,
`tasks.json:604–615` lists only `Frobenius.lean` and its module. The acceptance
routine rejects any changed file outside `task.files`
(`campaign_runner.py:430–431`), and the declaration probe imports only the listed
modules. A worker following the modular option would therefore fail the gate.

Repair: before dispatch, reconcile the permitted file/module set in the prompt
and manifest. If the new module is chosen, list it in both and leave umbrella
imports to the coordinator as usual. Avoid enforcing append-only changes when a
small refactor is needed to expose a previously internal lemma.

Sources: [G13 request](https://github.com/LiderMyHand/auto_automatyk/blob/a24af23362101d31bf55e703292272251aee65ff/notes/geometric_control/reviews/REQUEST_G13_PROOF.md),
[task manifest](https://github.com/LiderMyHand/auto_automatyk/blob/a24af23362101d31bf55e703292272251aee65ff/automation/geometric_control/tasks.json),
[runner](https://github.com/LiderMyHand/auto_automatyk/blob/a24af23362101d31bf55e703292272251aee65ff/automation/campaign_runner.py).

### 3. The gap ledger is broken, and the loop ignores its failure

`automation/geometric_control/gaps.json` is the JSON array `[]`. The generic
runner expects an object with `status_values`, `baseline`, and `gaps`.
Using the exact pinned files, both commands fail:

```text
campaign.py gaps
  campaign_runner.py:499
  AttributeError: 'list' object has no attribute 'get'

campaign.py gaps --harvest
  campaign_runner.py:465
  TypeError: list indices must be integers or slices, not str
```

The reproduction invoked `campaign_runner.py` directly with `CAMPAIGN_DIR`
pointing to the downloaded geometric-control directory; the wrapper's role is
only to supply that directory. No Lean environment or worker state is required
to trigger these failures. `supervise.py:76` and `ralph_loop.py:118` ignore the
gap command's exit code, so this loses the ledger without stopping the loop.

Repair: restore the expected object schema, enter the actual residual mathematical
tasks, validate it before dispatch, and propagate a failed harvest/report command.
A schema-only empty object is a valid emergency repair:

```json
{"schema": 1, "baseline": {}, "status_values": [], "gaps": []}
```

It should then be populated with the current chart construction, graph-frame
normalization, compatible-PDE integration, and separate Chow bridge tasks.

Sources: [gap file](https://github.com/LiderMyHand/auto_automatyk/blob/a24af23362101d31bf55e703292272251aee65ff/automation/geometric_control/gaps.json),
[runner](https://github.com/LiderMyHand/auto_automatyk/blob/a24af23362101d31bf55e703292272251aee65ff/automation/campaign_runner.py),
[supervisor](https://github.com/LiderMyHand/auto_automatyk/blob/a24af23362101d31bf55e703292272251aee65ff/automation/geometric_control/supervise.py).

### 4. Required names do not freeze the mathematical acceptance target

`campaign_runner.check_task` generates only `#check <name>` commands for required
declarations (`:319–322`). This establishes availability, not that a theorem has
the intended hypotheses, quantifiers, or conclusion. The earlier task list could
accept a `Prop`-valued target definition or a conditional reduction, with semantic
reviews later repairing the framing. The repeated G2/G6/G9/G10/G11 trim tasks
show the resulting cost.

Repair: keep the existing build and dependency audit, but add a short compiling
consumer example for each mathematical acceptance target. For Krener it should
end in the canonical `SimultaneouslyRectifiable f x₀` under the agreed C¹,
independence, and local bracket hypotheses. Keep the allowed assumptions explicit.
Record the printed type, dependency audit, source commit, and review artifact
together. A declaration's existence and a completed mathematical claim should
have separate status fields.

The regularity target also needs precision. An `OpenPartialHomeomorph` is a
topological chart, and a strict derivative at its center alone does not establish
a C¹ diffeomorphism throughout its source. The existing target includes directional
`fderiv` equalities but does not explicitly require an invertible derivative on the
whole source or C¹ regularity of the inverse. Decide whether the accepted result
is that exact target, a differentiable rectifying chart, or a C¹ local diffeomorphism,
and state the additional regularity separately if it is proved.

Sources: [runner](https://github.com/LiderMyHand/auto_automatyk/blob/a24af23362101d31bf55e703292272251aee65ff/automation/campaign_runner.py),
[canonical target](https://github.com/AdoHaha/DynamicalSystems/blob/451db05eff60098a4074dd50af51e06f3f283314/DynamicalSystems/Control/Geometric/Frobenius.lean).

### 5. Current status is scattered among contradictory historical snapshots

`FINAL_REPORT.md:24–27` still calls the variational equation the one remaining
crux. `NEEDS_MAP.md` has an old upstream “empty scaffold” conclusion, later adds
the corrective `ode`-branch finding, and ends at G10 even though the manifest
includes G11–G13. `RESPONSE_VAR.md:12–14` calls the common-box argument “ONE final
step” despite the accompanying detailed review also listing geometric construction
and graph-form gaps. These are misleading entry points for the next agent.

Repair: give the campaign one current, commit-pinned claim table, with columns for
the exact statement, proved/deferred status, residual assumptions, next consumer,
and review link. Preserve the existing narratives as historical snapshots with a
clear superseded notice. Avoid “one final step” until an actual dependency list
has a single open leaf. Keep `frobeniusTheorem` as a target definition until a
theorem inhabits it; do not infer the Chow result from a partial bracket calculation.

Sources: [final report](https://github.com/LiderMyHand/auto_automatyk/blob/a24af23362101d31bf55e703292272251aee65ff/notes/geometric_control/FINAL_REPORT.md),
[needs map](https://github.com/LiderMyHand/auto_automatyk/blob/a24af23362101d31bf55e703292272251aee65ff/notes/geometric_control/NEEDS_MAP.md),
[variational response](https://github.com/LiderMyHand/auto_automatyk/blob/a24af23362101d31bf55e703292272251aee65ff/notes/geometric_control/reviews/RESPONSE_VAR.md).

### 6. The Frobenius port accidentally requested analytic rather than smooth regularity

In the pinned Mathlib, differentiability orders have type `ℕ∞ω`: the notation
`∞` means smooth order, while its top element is analytic order `ω`.
The upstream `SmoothFunction` and `SmoothFunctionOn` abbreviations use `∞`.
The ported `frobeniusTheorem` instead used `⊤` for both the input field and the
solution, changing the intended regularity of the target.

The local integration repair restores both occurrences to `∞`, corrects the
`contDiff_top_lieBracket` description and exposes `contDiff_infty_lieBracket`.
At the G13 checkpoint this repaired the statement and smooth API, while its
`C¹` Krener chart alone did not prove the compatible-PDE existence target.
G14 has now supplied that graph construction and the higher-regularity argument:
`FrobeniusRegularity` bootstraps the total differential equation, and
`FrobeniusIntegrability` proves both the smooth open-domain theorem and the
original target. The analytic/smooth distinction remains important for preserving
the intended statement in future ports.

Sources: [pinned Mathlib order notation](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/ContDiff/Defs.lean),
[upstream smooth abbreviations and PDE statement](https://github.com/igorkhavkine/lean-dg-frobenius/blob/d762d3d53ad36d5a5f91a8c3280f0a1a279dee06/Frobenius/Basic.lean),
[baseline port](https://github.com/AdoHaha/DynamicalSystems/blob/451db05eff60098a4074dd50af51e06f3f283314/DynamicalSystems/Control/Geometric/Frobenius.lean).

## Proof decomposition used in the G13 contribution

1. Generalize the singleton complement/equivalence to an independent finite family;
   construct the joint flow map and prove its strict derivative at the origin.
   This stage does not use commutation.
2. Export a uniform pushforward identity for the same chosen local flows on a
   smaller box. State all time/space quantifiers and membership requirements.
3. Differentiate the finite composition in each time coordinate, control every
   intermediate point, and restrict the chart source to the resulting neighborhood.
4. Convert product coordinates to the canonical finite coordinate space and prove
   the consumer example for `SimultaneouslyRectifiable`. State any stronger C¹
   diffeomorphism claim separately.

The compiled G13 contribution follows this decomposition and also proves both
`C¹` chart statements. Keeping future tasks at this scale reduces the amount of
domain bookkeeping and finite-index linear algebra one agent must discover at once.

G14 likewise separates graph construction, base-coordinate change, smoothness
bootstrap and final target assembly into four modules. Its task depends on G13
and has its own exact consumer and review contract. This is the intended handling
of the user's expanded mathematical scope.
