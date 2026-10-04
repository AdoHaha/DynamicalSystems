# Independent review of the local variational equation

Reviewed 2026-10-04 against the development based on commit
`a4510862c55299d87d6c55c4a0b559c3fe66b06f`.

## Verdict

The main tangent-equation argument proves the requested declaration:

```lean
theorem flow_deriv_firstOrder
    {f : X → X} {x₀ : X} (hf : ContDiffAt ℝ 1 f x₀) :
    HasDerivAt (fun t ↦ fderiv ℝ (localFlow hf t) x₀)
      (fderiv ℝ f x₀) 0
```

Its ambient assumptions are a finite-dimensional complete real normed space.
The field hypothesis is continuous differentiability near the initial point.
The theorem concerns the existing `localFlow hf` from `Rectification.lean`.

The main proof also establishes
`eventually_hasDerivAt_fderiv_localFlow`: the full operator-valued equation

\[
\frac{d}{dt}D\Phi_t(x_0)
  = Df(\Phi_t(x_0))\circ D\Phi_t(x_0)
\]

on a sufficiently small two-sided time neighbourhood, at the fixed initial
point. `lieDerivative_along_flow_of_contDiffAt` uses the resulting time-zero
theorem to discharge the previous `hVar` premise.

`FlowTransport.lean` additionally proves eventual invertibility and
`eventually_lieDerivative_along_flow`:

\[
\frac{d}{dt}(\Phi_t)^*g(x_0)=(\Phi_t)^*[f,g](x_0).
\]

This transported identity holds at every sufficiently small time, with the
initial point fixed. Both fields are assumed `C¹` only near that point.

## Checks of the mathematical argument

| Concern | Evidence in the proof |
| --- | --- |
| Regularity of the field | `TangentSolution.lean` obtains continuity of `Df(Φ_t x₀)` from the local `C¹` hypothesis and the original time ODE. It solves a nonautonomous linear equation in operator space. This construction requires continuity of the time coefficient, and does not strengthen the field assumption to `C²`. |
| Relation to the original flow | The tangent candidate `J` is constructed along the original `localFlow hf`. `SpatialVariational.lean` then proves `HasFDerivAt (localFlow hf t) (J t) x₀` by estimating its actual spatial increments. Equality with `fderiv` follows from this derivative statement. |
| Order of neighbourhood choices | `UniformTaylor.lean` chooses a spatial radius before the remainder tolerance. `SpatialVariational.lean` chooses a positive common time radius before the tolerance in the final little-o proof. Only the permitted initial-point perturbation shrinks with that tolerance. |
| Uniform error bound | The flow's given spatial Lipschitz constant controls the separation of both trajectories. They remain in the common Taylor ball. The remainder equation is bounded by a linear term in the error plus a term proportional to the initial-point perturbation. |
| Strength of differentiation | The spatial estimate holds for every sufficiently small perturbation, with its norm as denominator. This proves a Fréchet derivative. The final time derivative takes values in `X →L[ℝ] X`; the remainder theorem uses the operator norm. |
| Negative times | `FlowGronwall.lean` treats negative times by applying the forward estimate to `s ↦ e (-s)`, whose derivative is `-e' (-s)`. The derivative norm bound is preserved. The resulting estimate depends on `|t|`. |
| Nondegeneracy | Every common time radius is explicitly positive. The growth bound is chosen as `‖Df(x₀)‖ + 1`, and the normalizing constants are positive. The construction also applies to a zero-dimensional state space. |
| Passage to arbitrary small times | The final module transfers the tangent equation using equality of `fderiv Φ` and `J` on a neighbourhood of each sufficiently small time. Equality just at the evaluation point would be insufficient; the proof uses the neighbourhood equality. |
| Transport and order of composition | Time continuity of `DΦ_t(x₀)` and its identity value at zero give invertibility near zero. Differentiating the inverse gives `-J⁻¹ (Df(Φ_t x₀) ∘ J) J⁻¹`; cancelling the adjacent `J J⁻¹` produces the correct ordered expression. The derivative of `g(Φ_t x₀)` supplies the remaining bracket term. Local regularity of `g` is used only along the sufficiently short trajectory. |

The key error is

\[
e_y(t)=\Phi_t(y)-\Phi_t(x_0)-J(t)(y-x_0).
\]

It starts at zero and satisfies

\[
\|e_y'(t)\|
\le K\|e_y(t)\|+\eta L\|y-x_0\|.
\]

The two-sided Grönwall estimate has a multiplier depending only on the fixed
time horizon and coefficient bound. Choosing `η = c / (C * (L + 1))` gives the
required bound `‖e_y(t)‖ ≤ c * ‖y - x₀‖`. This identifies the tangent candidate
with the spatial derivative without assuming that derivative in advance.

## Compilation and dependency evidence

The compiled public module was imported in an independent Lean process using
Lean `4.35.0-rc2` and the repository's pinned Mathlib revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55`.

The printed types of `flow_deriv_firstOrder`,
`eventually_hasDerivAt_fderiv_localFlow`, and
`eventually_lieDerivative_along_flow` have the hypotheses described above.
These results, the time-zero Lie-derivative corollary, and
`eventually_isInvertible_fderiv_localFlow` have kernel dependency reports
containing exactly the standard foundations `propext`, `Classical.choice`,
and `Quot.sound`. The final renamed module and the transport extension were
checked together in a fresh import.

The independent review concerns the main path through `TangentSolution`,
`UniformTaylor`, `FlowGronwall`, `SpatialVariational`, and the final
`VariationalEquation` and `FlowTransport` modules. The separately compiled `FlowIncrement` module
contains an additional Banach-space increment estimate and a conditional
first-order theorem. Its author checked that auxiliary argument; the main
closure uses the tangent-equation path reviewed here.

## Scope of the result and subsequent integration

The results give the variational equation, invertibility, and transported
Lie-derivative identity near time zero at a fixed initial point. A common
open box with joint higher regularity in time and initial state requires
further development.

The original `flowsCommute_of_bracketVanishing` expects spatial regularity,
invertibility, and the transported identity throughout its entire preselected
flow box. Its hypotheses should be localized to a smaller common box before
being discharged from the available local regularity assumptions. In
particular, `g` is assumed `C¹` only near `x₀`, while that older transport
premise covers every point of the flow box chosen for `f`.

The general Frobenius construction, simultaneous rectification, and the
four-fold flow-composition bridge remain separate integration tasks. The
present contribution supplies the previously missing local variational
analysis and its local Lie-derivative consequences.
