# Local variational equation: proved results and integration guide

## Result

The requested theorem is proved for the repository's existing `localFlow`:

```lean
theorem flow_deriv_firstOrder
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [FiniteDimensional ℝ X]
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    HasDerivAt (fun t ↦ fderiv ℝ (localFlow hf t) x₀)
      (fderiv ℝ f x₀) 0
```

Import `DynamicalSystems.Control.Geometric.VariationalEquation` for this theorem.
Import `DynamicalSystems.Control.Geometric.FlowTransport` for the local transported
identity as well. Both are included in the repository's umbrella import.

The only field hypothesis is `ContDiffAt ℝ 1 f x₀`. Spatial differentiability of
the flow is proved in the implementation. There is no remaining regularity or
remainder premise in the public result. The finite-dimensional assumption enters
the uniform Taylor estimate; the construction of the linear tangent ODE and the
Grönwall estimate work on Banach and normed spaces, respectively.

This is the classical differentiable-dependence proof. A standard reference is
Philip Hartman, *Ordinary Differential Equations*, Chapter V. The contribution
is the Lean formalization and integration with this repository's chosen flow.

## Additional proved results

| Declaration | Content | Scope |
| --- | --- | --- |
| `localFlow_hasFDerivAt_of_tangent` | A solution of the tangent ODE starting from the identity is the Fréchet derivative of the original flow. | All sufficiently small times, at the fixed initial point. |
| `eventually_differentiableAt_localFlow` | The spatial derivative exists. | All sufficiently small times, at the fixed initial point. |
| `eventually_hasDerivAt_fderiv_localFlow` | `∂ₜ DΦₜ(x₀) = Df(Φₜ(x₀)) ∘ DΦₜ(x₀)`. | All sufficiently small times, at the fixed initial point. |
| `flow_deriv_firstOrder_isLittleO` | `‖DΦₜ(x₀) − id − t • Df(x₀)‖ = o(t)`. | Operator norm, as `t → 0` from either side. |
| `lieDerivative_along_flow_of_contDiffAt` | The time-zero pullback derivative equals `[f,g](x₀)`. | Discharges the original `hVar` premise. |
| `eventually_isInvertible_fderiv_localFlow` | `DΦₜ(x₀)` is invertible. | All sufficiently small times. |
| `eventually_lieDerivative_along_flow` | `∂ₜ (Φₜ)*g(x₀) = (Φₜ)*[f,g](x₀)`. | All sufficiently small times, at the fixed initial point. |

For example, the earlier Lie-derivative reduction can now be used as follows:

```lean
exact lieDerivative_along_flow f g x₀ hf hg (flow_deriv_firstOrder hf)
```

Equivalently, use the new `lieDerivative_along_flow_of_contDiffAt` directly.
The existing reduction retains its signature for compatibility.

## Proof mechanism

Let `Φ t x = localFlow hf t x`, and put

\[
A(t)=Df(\Phi_t(x_0)).
\]

The existing flow equation gives continuity of the trajectory. Local `C¹`
regularity of `f` gives operator-norm continuity of `A` near zero. Apply
Picard–Lindelöf directly in the space of continuous linear operators to construct

\[
J'(t)=A(t)\circ J(t),\qquad J(0)=I.
\]

This step uses only continuity of the time coefficient. It does not require
`Df` to be Lipschitz in the state and does not strengthen the field to `C²`.

On a sufficiently small fixed ball, finite-dimensional compactness gives a
uniform Taylor estimate. For every `η > 0`, sufficiently close points `v,w` in
that ball satisfy

\[
\|f(v)-f(w)-Df(w)(v-w)\|\le\eta\|v-w\|.
\]

The ball is chosen before `η`. Shrink the time and initial-state neighborhoods
so that both trajectories remain in this ball, and use the given spatial
Lipschitz bound `L` for `Φ`.

For an initial perturbation `y`, define

\[
e_y(t)=\Phi_t(y)-\Phi_t(x_0)-J(t)(y-x_0).
\]

Its derivative is computed using the time ODE and the already constructed
operator curve `J`. The Taylor estimate gives

\[
\|e_y'(t)\|\le K\|e_y(t)\|+\eta L\|y-x_0\|,
\qquad e_y(0)=0.
\]

The symmetric Grönwall estimate therefore yields, on a fixed interval `|t| < T`,

\[
\|e_y(t)\|
\le \frac{e^{KT}-1}{K}\,\eta L\|y-x_0\|.
\]

The horizon `T` is independent of the tolerance in the derivative definition.
Given that tolerance `c > 0`, choose
`η = c / (C * (L + 1))`, where `C = (exp(K*T)-1)/K > 0`.
Then shrink only the initial perturbation radius. The resulting bound proves
`HasFDerivAt (Φ t) (J t) x₀`, so derivative uniqueness identifies `DΦₜ(x₀)` with
`J(t)` on a neighborhood of zero.

The full time variational equation follows by transferring the ODE for `J`
through this neighborhood equality. At zero, `Φ₀(x₀)=x₀` and `J(0)=I` give the
requested derivative immediately.

For transport, continuity of `J` and its identity value at zero give
invertibility nearby. Differentiating the inverse yields

\[
(J^{-1})'=-J^{-1}J'J^{-1}=-J^{-1}Df(\Phi_t(x_0)).
\]

The chain rule for `g(Φₜ(x₀))` then gives the transported bracket, with the
repository's convention `[f,g]=Dg(f)-Df(g)`.

## Source layout

All the following files are under `DynamicalSystems/Control/Geometric/`.

| File | Purpose |
| --- | --- |
| `UniformTaylor.lean` | General local uniform first-order remainder for a `C¹` map on a finite-dimensional domain. The codomain is any real normed space. |
| `FlowGronwall.lean` | General two-sided differential Grönwall estimates and a multiplier independent of the error curve. |
| `TangentSolution.lean` | General local existence for a continuous linear nonautonomous ODE, followed by its operator-valued specialization along the flow. |
| `SpatialVariational.lean` | Identification of the tangent solution with the spatial derivative. |
| `VariationalEquation.lean` | Public variational results, operator-norm remainder, and time-zero Lie-derivative corollary. |
| `FlowTransport.lean` | Local invertibility and the time-dependent transported identity. |
| `FlowIncrement.lean` | Additional Banach-space increment estimate and first-order theorem conditional only on eventual spatial differentiability. The main finite-dimensional closure follows the tangent-ODE path above. |

The full proof is in these files. The short theorem statements in this guide
are usage documentation.

## Reproduction and verification

The development is based on
[`AdoHaha/DynamicalSystems`, `dev`, commit `a4510862c55299d87d6c55c4a0b559c3fe66b06f`](https://github.com/AdoHaha/DynamicalSystems/tree/a4510862c55299d87d6c55c4a0b559c3fe66b06f).
The pinned toolchain and manifest were preserved:

- Lean `4.35.0-rc2`, compiler commit `11acb17ec6b07a8f9e9173e6845197929540936b`.
- Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

From the repository root, with that toolchain available:

```bash
lake build DynamicalSystems.Control.Geometric.FlowTransport
lake env lean docs/variational-check.lean
```

The first command builds the full new dependency chain, including the original
`Rectification` and `FlowCommutator` modules. The second prints the public types
and checks the proof dependencies of all substantive results. Both commands
passed. The new modules emit no warnings; the build replays existing style
warnings from `Rectification`.

Every reported dependency list contains exactly the standard foundations
`propext`, `Classical.choice`, and `Quot.sound`. An independent mathematical and
compiled-module review is recorded in [variational-review.md](variational-review.md).
The verification scope is the new proof dependency chain; it does not establish
unrelated targets in the rest of the repository.

## Remaining Frobenius work

The named `frobeniusTheorem` in the baseline is a `Prop`-valued target definition,
not a proved existence theorem. Its compatible-PDE construction remains to be
provided. The relevant source is
[`Frobenius.lean`](https://github.com/AdoHaha/DynamicalSystems/blob/a4510862c55299d87d6c55c4a0b559c3fe66b06f/DynamicalSystems/Control/Geometric/Frobenius.lean).

The new results are local in time at the fixed initial point. In contrast, the
existing `flowsCommute_of_bracketVanishing` requires `hdiff`, `hinv`, and `hTrans`
at every point and time of the entire original flow box. Local smoothness near
`x₀` does not guarantee smoothness of both fields on that preselected box.
Consequently, that interface needs a smaller common domain before its premises
can be discharged.

The next implementation should proceed in these bounded steps:

1. Expose a common positive time radius and spatial radius on which both fields
   are `C¹` along the relevant trajectories. State transport on that box.
2. Generalize the spatial comparison argument to an arbitrary initial point in
   the box. Choose a common coefficient bound for the linear ODE. The direct
   Picard construction in `TangentSolution.lean` makes the time-radius dependency
   explicit, so it can be made uniform before choosing individual solutions.
3. Apply the proved inverse/transport calculation with those uniform data, then
   reuse the existing ODE-uniqueness argument for commuting flows.
4. Complete the simultaneous-coordinate or compatible-PDE construction. For a
   general involutive frame, the change to graph form is a further stated gap.

For the Chow development, the current difference of differently ordered mixed
partials of two compositions is also distinct from the full four-fold
flow-commutator expansion. That bridge remains a separate task; see the baseline
[`FlowCommutator.lean`](https://github.com/AdoHaha/DynamicalSystems/blob/a4510862c55299d87d6c55c4a0b559c3fe66b06f/DynamicalSystems/Control/Geometric/FlowCommutator.lean).

## Reuse in lean-dg-frobenius

The inspected upstream `ode` branch is
[`d762d3d53ad36d5a5f91a8c3280f0a1a279dee06`](https://github.com/igorkhavkine/lean-dg-frobenius/tree/d762d3d53ad36d5a5f91a8c3280f0a1a279dee06).
Its [`Frobenius/ODE.lean`](https://github.com/igorkhavkine/lean-dg-frobenius/blob/d762d3d53ad36d5a5f91a8c3280f0a1a279dee06/Frobenius/ODE.lean)
contains incomplete `PL_deviation` and `PL_joint_diff` developments. The inspected
`honza` branch has no corresponding completed variational theorem. Those branches
use Lean `4.22.0-rc3` and Mathlib
`c728e645fccf7166c3ac71ce0c1ca1a32c10a268`, so this is a modern-toolchain
contribution requiring a deliberate API port or toolchain update upstream.

The uniform Taylor theorem, symmetric Grönwall estimate, and continuous linear
ODE existence theorem have no control-specific assumptions. They are the first
pieces to extract for upstream reuse. The spatial comparison proof can then be
stated for an arbitrary solution family carrying the original ODE, initial
condition, and local Lipschitz data, and identified with the upstream flow by
uniqueness.

The upstream `PL_deviation` target is time-dependent and Banach-valued, while the
new automatic spatial existence theorem uses finite-dimensional compactness.
Preserve that distinction during porting. In infinite dimension, operator-valued
time differentiation requires operator-norm regularity of the coefficient;
continuity after application to each vector alone does not give that regularity.
The autonomous `C¹` coefficient used here has the required norm continuity.

For a subsequent proof agent, the critical invariant is the order of choices:
fix a genuine common flow domain first, then vary the Taylor tolerance and the
initial perturbation radius. Keep the spatial derivative identification separate
from the already straightforward differentiation of its operator ODE.
