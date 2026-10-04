# The smooth Frobenius target is proved

## Exact result

`DynamicalSystems/Control/Geometric/FrobeniusIntegrability.lean` now contains

```lean
theorem frobeniusTheorem_holds : frobeniusTheorem
```

This proves the entire recorded proposition, including its quantification over the
coefficient, completeness and finite-dimensionality instances, base point, and initial
fiber value. The `Prop`-valued definition is retained as a compatibility interface;
it now has a proof.

The stronger theorem used to prove it is:

```lean
theorem exists_sol_of_fderiv_compat
    (g : X × Y → X →L[ℝ] Y) (hg : ContDiff ℝ ∞ g)
    (hcompat : TotalFderivCompat g Set.univ) (x₀ : X) (z : Y) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ ∃ w : X → Y,
      ContDiffOn ℝ ∞ w U ∧ w x₀ = z ∧
        ∀ x ∈ U, HasFDerivAt w (g (x, w x)) x
```

The ambient spaces are finite-dimensional real normed spaces. The existence theorem
records `[CompleteSpace Y]`; completeness of finite-dimensional `X` is supplied by
its standard instance. The original target's explicit completeness binders are
accepted inside `frobeniusTheorem_holds`.

Thus, for every prescribed `(x₀,z)`, there is one open neighborhood `U` and one
smooth function `w` such that

\[
w(x_0)=z,\qquad Dw(x)=g(x,w(x))\quad(x\in U).
\]

The derivative is an actual `HasFDerivAt`, not merely a value assigned to `fderiv`.
Taking `s = U` proves the original target's conclusion about `fderivWithin` on
`interior s`, since `interior U = U`.

There are no residual flow, variational, transport, or graph-solution premises.
The theorem assumes exactly the smoothness and compatibility data of the intended
upstream target, together with the stated ambient-space conditions.

## Compatibility and the intended regularity

The graph connection is a function

\[
g:X\times Y\longrightarrow\mathcal L(X,Y).
\]

At `(x,y)`, it specifies tangent vectors `(d,g(x,y)d)`. The condition
`TotalFderivCompat g Set.univ` says that its curvature vanishes for every pair
of horizontal directions. In the repository's notation,

\[
\begin{aligned}
\operatorname{Curvature}(g,p,d_1,d_2)
={}&Dg(p)(d_1,0)d_2+Dg(p)(0,g(p)d_1)d_2\\
 &-Dg(p)(d_2,0)d_1-Dg(p)(0,g(p)d_2)d_1.
\end{aligned}
\]

The existing theorem `bracket_graphField` identifies this tensor with the vertical
component of the bracket of two graph fields. It is the bridge from compatibility
to commuting fields used by the proof.

The smooth order is `∞`. The earlier port had written `⊤` in the coefficient and
solution regularity annotations. In the pinned Mathlib, `⊤` is analytic order `ω`,
which differs from smoothness. Both annotations were restored to `∞` to match the
upstream `SmoothFunction` and `SmoothFunctionOn` definitions. This correction is
documented independently of the proof in
[geometric-integration-review.md](geometric-integration-review.md).

Primary references are the pinned
[upstream Frobenius definitions and target](https://github.com/igorkhavkine/lean-dg-frobenius/blob/d762d3d53ad36d5a5f91a8c3280f0a1a279dee06/Frobenius/Basic.lean)
and
[Mathlib's differentiability orders](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean).
The graph-field formulation and construction are classical; see Krener,
*Differential Geometric Methods in Nonlinear Control*, *Encyclopedia of Systems and
Control*, second edition, and Sontag, *Mathematical Control Theory*, second edition,
Chapter 4, §4.4. The ported target is attributed to Igor Khavkine and Jan Růžička,
whose repository is licensed under Apache 2.0.

## Why the proof closes the target

### 1. A differentiable integral graph in finite coordinates

Start with `X = Fin k → ℝ` and the graph fields

\[
f_i(p)=(e_i,g(p)e_i).
\]

They are `C¹` when `g` is `C¹`. Compatibility and `bracket_graphField` show that
their brackets vanish. The finite-flow construction behind the proved Krener lemma
then gives a leaf parametrization

\[
L:\mathbb R^k\longrightarrow\mathbb R^k\times Y,
\qquad L(0)=(x_0,z),
\]

whose derivative satisfies, on a neighborhood of zero,

\[
DL(t)h=(h,g(L(t))h).
\]

The directional identities initially hold on the coordinate basis; linearity
extends them to the displayed operator identity. This is
`exists_local_graph_parametrization` in `FrobeniusGraph.lean`.

The first projection `Q(t) = (L(t)).1` therefore has derivative the identity.
After restricting to a ball, the mean-value constancy theorem gives

\[
Q(t)=x_0+t.
\]

Define

\[
w(x)=(L(x-x_0)).2.
\]

On the translated ball, `L(x-x₀) = (x,w(x))`. The chain rule now directly yields
`Dw(x)=g(x,w(x))` and the prescribed initial value. No second inverse-function
construction is needed. The resulting `exists_local_graph_solution` theorem asks
only for `C¹` regularity of `g` and compatibility.

The graph construction uses the finite-flow map and its derivative theorem
directly. It does not assume an integral leaf, and it does not require a separate
linear-independence premise: the graph frame's horizontal block supplies the
coordinate directions in the derivative calculation.

### 2. Arbitrary finite-dimensional horizontal spaces

Choose a continuous linear equivalence

\[
e:\mathbb R^{\dim X}\simeq_L X.
\]

The connection in those coordinates is

\[
g_e(b,y)d=g(e(b),y)(e(d)).
\]

`FrobeniusCoordinates.lean` proves preservation of regularity and the exact
curvature transformation

\[
\operatorname{Curvature}(g_e,(b,y),d_1,d_2)
=\operatorname{Curvature}(g,(e(b),y),e(d_1),e(d_2)).
\]

Hence the finite-coordinate theorem applies to `g_e`. Composing its solution
with `e.symm` returns a solution on `X`; the derivative compositions cancel
`e` and `e.symm`. The transformed neighborhood is open and contains `x₀`.

These coordinate lemmas are generic real normed-space statements for a given
continuous linear equivalence. Finite-dimensionality is needed when choosing
that equivalence and invoking the finite-flow construction.

### 3. Smoothness on the same open neighborhood

The remaining regularity follows from the equation itself. Derivative existence
first gives continuity of `w` on the constructed open set `U`. Suppose `w` is `Cⁿ`
on `U`. Then

\[
x\longmapsto g(x,w(x))
\]

is `Cⁿ` there, because `g` is smooth. This is the derivative of `w`, so the
successor regularity criterion gives `Cⁿ⁺¹` regularity of `w` on `U`. Induction
gives every finite order on the same set; `contDiffOn_infty` gives smoothness.

The crucial quantifier order is

\[
\exists U\;\exists w\;\forall n,\quad w\text{ is }C^n\text{ on }U.
\]

Neither the solution nor its domain changes with `n`.

The generic theorem `contDiffOn_infty_of_hasFDerivAt_eq` in
`FrobeniusRegularity.lean` records this argument. It requires neither completeness
nor finite-dimensionality. Its local-coefficient variant only needs smoothness of
`g` on a set containing the solution graph.

This bootstrap is why the full smooth Frobenius target can be completed using
the established `C¹` flow theory. All-order smoothness of the flow itself is not
a premise of this proof.

## Files and reuse

| Module | Role |
| --- | --- |
| `FrobeniusGraph` | Finite-coordinate graph parametrization, affine horizontal projection, and differentiable solution. |
| `FrobeniusCoordinates` | Linear coordinate covariance of curvature and transfer of solutions. |
| `FrobeniusRegularity` | Smoothness bootstrap for total differential equations. |
| `FrobeniusIntegrability` | Arbitrary-base solution theorem and proof of the recorded target. |

They build on the Krener contribution described in
[krener-rectification.md](krener-rectification.md). The generic regularity and
coordinate results are useful outside geometric control, as are the earlier
joint-derivative and linear-ODE parameter-continuity helpers.

## Verification and consumption

Use the existing repository toolchain and pins:

```bash
lake build DynamicalSystems.Control.Geometric.FrobeniusIntegrability
lake env lean docs/frobenius-check.lean
```

The consumer file checks the entire `frobeniusTheorem` proposition with no external
completeness or dimension premises, the stronger open-domain result, the exact
original within-derivative conclusion, constant connections, and a zero-dimensional
base. Foundational dependency output and the final compiled signatures are in
[frobenius-validation.txt](frobenius-validation.txt).

The complete repository build `lake build DynamicalSystems` also succeeds
(3993 jobs). `lake lint -- DynamicalSystems` passes for the entire library, as do
the separate geometric endpoint lint runs. The standard `axiom-audit` executable
checks 5069 project declarations with zero violations and reports only
`propext`, `Classical.choice`, and `Quot.sound`. All 78 new declarations also have
individual dependency records in the two validation files.
The final lint pass removed two redundant simplifier registrations from the frame
helpers and an unused dimension parameter from the simultaneous-map definition
and its zero lemma. The endpoint theorem contracts are unchanged. Existing
compiler warnings in older modules remain outside the new proof modules.

For downstream use, import

```lean
import DynamicalSystems.Control.Geometric.FrobeniusIntegrability
```

and call `exists_sol_of_fderiv_compat g hg hcompat x₀ z`. Clients retaining the
recorded proposition can use `frobeniusTheorem_holds` directly. The umbrella
`DynamicalSystems.lean` also imports the result.

## Integration handoff

The contribution branch is
[`prove-geometric-frobenius`](https://github.com/AdoHaha/DynamicalSystems/tree/prove-geometric-frobenius),
based on `geometric-ralph` at `451db05eff60098a4074dd50af51e06f3f283314`.
The first commit, `5363557a03de3bf47d34978082432b8332fbba57`, supplies Krener
rectification and the target-order correction. The following commit supplies
the smooth Frobenius proof and its final handoff. Use the branch's current commit
for the complete source and validation documents.

If the integration branch is still at the reviewed baseline:

```bash
git switch geometric-ralph
git fetch origin prove-geometric-frobenius
git merge --ff-only FETCH_HEAD
lake build DynamicalSystems
lake env lean docs/krener-check.lean
lake env lean docs/frobenius-check.lean
```

If other work has advanced that branch, integrate the two contribution commits
in order and resolve any overlapping edits under the existing review process.
The contribution does not require changing the Lean or Mathlib pin.

The accompanying
[orchestration review](geometric-orchestration-review.md) explains the concrete
handoff and runner defects. Its
[apply-ready campaign patch](geometric-campaign-review.patch) targets
`LiderMyHand/auto_automatyk` at
`a24af23362101d31bf55e703292272251aee65ff`. In a checkout based on that snapshot,
run `git apply --check` on the patch before applying it, then execute the regression
tests and strict validation recorded in the review. The patch is a separate
cross-repository deliverable; it has not been pushed to `auto_automatyk`.

## Remaining separate objectives

The repository's smooth compatible-PDE target is closed. The intrinsic formulation
for an arbitrary involutive distribution still needs its own frame-normalization
and coordinate argument: the present target starts with a graph connection.
That normalization is not a hidden assumption in the proved PDE theorem.

Likewise, the Chow development's four-flow commutator expansion and the subsequent
accessibility/control arguments are separate goals. Their completion does not
follow merely from marking the Frobenius target proved.

For `lean-dg-frobenius`, this supplies the intended mathematical existence result
against the current DynamicalSystems toolchain. Transferring the source to its
older `ode`/`honza` toolchain still requires API adaptation and compilation there;
the proof modules have not been asserted to compile unchanged in that environment.
