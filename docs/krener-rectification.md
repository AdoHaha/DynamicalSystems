# Krener rectification: proof, integration review, and next steps

## Result

The arbitrary finite-family Krener lemma is proved in
`DynamicalSystems/Control/Geometric/SimultaneousRectification.lean`:

```lean
theorem krenerLemma
    (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀)
    (hind : LinearIndependent ℝ (fun i => f i x₀))
    (hcomm : ∀ i j, FlowsCommuteLocally (f i) (f j) x₀) :
    SimultaneouslyRectifiable f x₀
```

The ambient assumptions are `[NormedAddCommGroup X] [NormedSpace ℝ X]
[CompleteSpace X] [FiniteDimensional ℝ X]`, and `f : Fin k → X → X`.
Independence is required only at `x₀`. The regularity and bracket conditions are local.
There is no positivity condition on `k`; the empty family is included.

The explicit product-coordinate chart is

```lean
simultaneousRectifyingChart hf hind hcomm :
  OpenPartialHomeomorph
    ((Fin k → ℝ) × ↥(frameComplement (fun i => f i x₀))) X
```

It maps zero to `x₀`, and zero belongs to its open source. The following companion
theorems record the stronger regularity and trajectory properties:

| Declaration | Contract |
| --- | --- |
| `simultaneousRectifyingChart_contDiffOn` | The chart is `C¹` on its source. |
| `simultaneousRectifyingChart_symm_contDiffOn` | Its inverse is `C¹` on its target. |
| `simultaneousRectifyingChart_fderiv` | Its differential sends `(Pi.single i 1, 0)` to `f i` at the image point. |
| `simultaneousRectifyingChart_rectifies` | Updating coordinate `i` traces an integral curve of `f i` at every source point. |
| `simultaneousRectifyingChart_spec` | Includes the actual composition formula, invertibility of every source derivative, and the inverse derivative formula. |

In particular, the trajectory theorem has just source membership as its domain premise:

```lean
HasDerivAt
  (fun t => simultaneousRectifyingChart hf hind hcomm
    (Function.update p.1 i t, p.2))
  (f i (simultaneousRectifyingChart hf hind hcomm p)) (p.1 i)
```

All intermediate time and state conditions are discharged when the chart source is
chosen. This is an actual local `C¹` diffeomorphism, in addition to proving the existing
`SimultaneouslyRectifiable` interface, whose definition does not itself record that
regularity.

These are classical results. The geometric construction follows Krener,
*Differential Geometric Methods in Nonlinear Control*, *Encyclopedia of Systems and
Control*, second edition, and Sontag, *Mathematical Control Theory*, second edition,
Chapter 4, §4.2. The flow regularity argument is the standard variational-equation
argument described in Hartman, *Ordinary Differential Equations*, Chapter V.

## What the handoff was missing

The input branch was `geometric-ralph` at
`451db05eff60098a4074dd50af51e06f3f283314`. The orchestrator's request was
[`a24af233`](https://github.com/LiderMyHand/auto_automatyk/commit/a24af23362101d31bf55e703292272251aee65ff).

The preceding integration is sound. The merge of the variational contribution has
exactly the same tree as `3615165ef0abc8aca244b3a8f82774e6b4472396`. G12 then proves
uniform variational theory with one time interval and one smaller state ball chosen
before the initial point and before the Taylor tolerance. The proof identifies the
actual spatial derivative of the same chosen local flow at all those initial points.
See [geometric-integration-review.md](geometric-integration-review.md) for the detailed
review and pinned source references.

The Krener prompt nevertheless abbreviated several remaining obligations:

1. `flowsCommute_unconditional_onBox` concludes commutation at `x₀`. The prompt
   displayed a varying initial point `y`. Substituting the transverse slice point
   into that display does not apply the actual theorem, and constructing another
   local flow at that point changes the chosen flow.
2. The existing complement construction splits off one vector. A finite independent
   family needs its own splitting and a conversion back to `Fin n → ℝ` coordinates.
3. Spatial differentiability is not yet joint differentiability in time and state.
4. An inverse-function chart centered at zero does not automatically encode all
   later flow-domain conditions in its source.
5. A local homeomorphism with a strict derivative at its center does not alone
   record continuous differentiability of both directions throughout their domains.

The proof below supplies each of these missing pieces. It uses uniform field
preservation directly, so it does not need the stronger flow-reordering statement
displayed in the prompt.

## Proof architecture

### 1. Keep the chosen flow fixed and export uniform field preservation

`FlowBox.lean` constructs a common spatial regularity box from local `C¹` data and
any additional property holding near `x₀`. Thus the bracket-zero neighborhood can
be included in the box. Its common-domain proof of regularity at `x₀` and the original
proof `hf` define the same `localFlow`, by proof irrelevance.

For commuting fields, transport and invertibility give

\[
D_y\Phi_f(t,y)\,g(y)=g(\Phi_f(t,y))
\]

on one product neighborhood of `(0, x₀)`. The exported theorem is
`eventually_fderiv_localFlow_apply`. Its neighborhood quantifier precedes both time
and state. It follows by differentiating the pullback in time, using bracket
vanishing to make that derivative zero, and evaluating the resulting constant at
time zero.

### 2. Establish full joint `C¹` regularity

`JointFlow.lean` first proves joint continuity using uniform spatial Lipschitz
continuity and time continuity. The time partial derivative is `f(Φ(t,y))`, so it
is jointly continuous. A general partial-derivative lemma combines that continuous
time partial with the existing spatial derivative to obtain

\[
D\Phi(t,y)(a,v)
  =D_y\Phi(t,y)v+a\,f(\Phi(t,y)).
\]

`FlowRegularity.lean` then proves continuity of the spatial derivative itself.
Writing `J(t,y)=D_yΦ(t,y)` and `A(t,y)=Df(Φ(t,y))`, all these operators satisfy

\[
\partial_tJ(t,y)=A(t,y)J(t,y),\qquad J(0,y)=I
\]

on a fixed product box. A first Gronwall estimate bounds `J` uniformly. A second,
applied to `J(t,z)-J(t,y)`, turns a uniform coefficient modulus into a uniform
modulus for `J`. Compactness makes `Df` uniformly continuous on the common closed
box, and the flow's spatial Lipschitz bound transfers that modulus to `A`.

The resulting theorem is:

```lean
contDiffAt_localFlow_joint hf :
  ContDiffAt ℝ 1 (fun p : ℝ × X => localFlow hf p.1 p.2) (0, x₀)
```

No second derivative of the vector field is required. In the generic linear-family
lemma, continuity of the selected family of fundamental solutions is a conclusion,
not an input.

### 3. Construct the finite composition and its invertible linearization

`FrameComplement.lean` constructs a complement `Y` of the span of the frame at
`x₀`, together with the continuous linear equivalence

\[
L(t,z)=\sum_{i=0}^{k-1}t_i f_i(x_0)+\iota z.
\]

`MultiFlow.lean` defines the map

\[
F(t,z)=\Phi_0^{t_0}\circ\cdots\circ\Phi_{k-1}^{t_{k-1}}(x_0+\iota z)
\]

using a list of the coordinate indices. Induction proves both `C¹` regularity near
zero and strict differentiability at zero with derivative `L`. Independence of
the frame makes `L` invertible.

A separate induction over lists without duplicate indices proves the coordinate
derivative formula. For a new index, only the outer flow's time derivative
contributes. For an index already in the tail, the chain rule and uniform field
preservation transport its vector field through the outer flow. An index absent
from the list has zero derivative. For the full list this yields

\[
DF(t,z)(e_i,0)=f_i(F(t,z)).
\]

Finite intersection and continuity of the intermediate compositions pull every
needed flow-domain condition back to one neighborhood of zero.

### 4. Restrict the chart and convert coordinates

`LocalDiffeomorph.lean` packages a general inverse-function argument. An invertible
strict derivative, together with differentiability on a neighborhood, gives
invertible derivatives on a smaller neighborhood. Its chart can be restricted
inside any prescribed neighborhood, while retaining an explicit inverse derivative.

The simultaneous chart is restricted inside the intersection of the `C¹` region
and the region where all coordinate derivative identities hold. Mathlib's
`OpenPartialHomeomorph.contDiffAt_symm` then supplies inverse `C¹` regularity at
every target point.

Finally, `frameCoordinates` replaces the complementary subspace by ordinary finite
coordinates. It preserves the first `k` coordinate vectors exactly. The canonical
dimension is

```text
n = k + Module.finrank ℝ (frameComplement (fun i => f i x₀)).
```

This proves `krenerLemma` with the unchanged `SimultaneouslyRectifiable` conclusion.

## Validation

The implementation uses the repository's existing Lean `4.35.0-rc2` and Mathlib
revision `065356127b1dc0016f66b7283ce0ce2c4055aa55`. The dependency pins were preserved.

The complete geometric target builds:

```bash
lake build DynamicalSystems.Control.Geometric.SimultaneousRectification
lake env lean docs/krener-check.lean
```

The consumer file checks the exact theorem signature, base-point membership,
forward and inverse `C¹` regularity, and the trajectory contract with source
membership alone. It also instantiates an empty family and two independent
constant fields in three dimensions, exercising a nontrivial complement.

All 61 new declarations, including the smooth-bracket alias, were checked for
foundational dependencies. They use only `propext`, `Classical.choice`, and
`Quot.sound`. All seven new source modules are free of compiler and linter warnings
and respect the 100-character line limit. The build replays existing warnings in
older source files. The preserved G10–G12 integration was independently built and
audited before the new work. Detailed compiler evidence is in
[krener-validation.txt](krener-validation.txt).

## Corrected smoothness annotations

The reviewed Frobenius target replaced upstream smoothness with `ContDiff ℝ ⊤`
for the input and `ContDiffOn ℝ ⊤` for the solution. In the pinned Mathlib,
`∞` denotes smoothness while `⊤`, also written `ω`, denotes analyticity. Upstream
explicitly uses `∞`. The two annotations in `frobeniusTheorem` are restored to
`∞`, matching its intended port. The target remains a `Prop`-valued definition.

The existing `contDiff_top_lieBracket` analytic signature is preserved and its
description corrected. The new `contDiff_infty_lieBracket` explicitly records
smooth closure. These are statement/description repairs, separate from the `C¹`
Krener proof. Primary references are the pinned
[upstream definitions](https://github.com/igorkhavkine/lean-dg-frobenius/blob/d762d3d53ad36d5a5f91a8c3280f0a1a279dee06/Frobenius/Basic.lean)
and
[Mathlib differentiability orders](https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/Analysis/Calculus/ContDiff/FTaylorSeries.lean).

## Next mathematical work

G13 itself has no residual analytic or geometric premise. The next Frobenius tasks
should distinguish two goals.

**For the current compatible-PDE target, the distribution is already in graph
form.** Apply the Krener construction to the graph frame. Restrict the chart to
the leaf with transverse coordinate zero. The first-coordinate projection of
this leaf has invertible derivative at the base point, so another local inverse
produces a graph `x ↦ (x,w(x))`. Its tangent identity gives

\[
Dw(x)=g(x,w(x)),\qquad w(x_0)=z.
\]

This first yields a `C¹` solution. Smoothness can then be bootstrapped from the
displayed derivative equation and smooth `g`: if `w` is `Cⁿ`, its derivative is
`Cⁿ`, so `w` is `Cⁿ⁺¹`. This route does not require first proving that the entire
flow is smooth to every order. It is a proposed continuation; the graph solution
and bootstrap are not proved in this contribution.

**For an arbitrary involutive distribution, there is an additional normalization
step.** Choose linear coordinates transverse to the distribution at the base
point, normalize the frame so its first block is the coordinate basis, and prove
that the normalized frame remains in the same involutive distribution. The
existing `commutingBasis_of_involutive` starts after that graph-form hypothesis.

The Chow development also retains its distinct finite-flow-commutator expansion
obligation. A statement about two mixed partial derivatives does not by itself
supply the four-flow asymptotic expansion needed there.

## Reuse outside control

Several new results can be separated from the geometric-control namespace for an
upstream contribution:

- `hasFDerivAt_uncurry_coprod_of_continuous_left`: general real normed-space calculus.
- `continuousOn_linearODE_family`: parameter continuity for operator-valued linear
  ODEs, without a finite-dimensional assumption in the abstract statement.
- The three `HasStrictFDerivAt` results in `LocalDiffeomorph.lean`: general normed
  field results with a complete domain, independent of control theory.
- `contDiffAt_localFlow_joint` and the finite-frame rectification construction:
  analytic and geometric interfaces for the upstream Frobenius project.

The proofs are verified against the pinned DynamicalSystems toolchain. The upstream
`ode`/`honza` snapshots previously reviewed use another toolchain, so a port still
needs its own compilation and API adaptation. The current contribution should be
transferred as small verified layers, retaining the exact hypotheses and source
domains of each theorem.
