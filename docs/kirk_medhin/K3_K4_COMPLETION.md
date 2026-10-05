# K3 and weak K4: completed proof chain

This change completes the regular isoperimetric K3 lift and the weak K4 obligations
requested in `PROMPT_GPT_PRO_K3.md`. The proofs start from the actual `cvFunctional`
minimum. The multiplier, endpoint-preserving variations, actual functional
derivatives, interior Euler–Lagrange equations, du Bois–Reymond law, and corner
conditions are derived.

The branch starts at `kirk_medhin-ralph` commit
`8aa45e412647755acdce9dc9d8bba5403388922d`. It preserves the existing variational
functional, first variation, Euler–Lagrange predicate, original piecewise C1
predicate, and energy definition. All new implementation modules are imported by
the main `DynamicalSystems.lean` umbrella.

## Main entry points

| Goal | Declaration | Primitive scope |
| --- | --- | --- |
| Full regular K3 with C1 data | `KirkMedhin.K3.augmentedEulerLagrangeWithin_of_isoperimetric` | Actual constrained fixed-endpoint minimum, jointly C1 `L,G`, C1 `K,x`, positive horizon, and one endpoint-zero C1 direction with nonzero constraint variation. Returns one multiplier, the exact all-differentiable first-variation predicate, and the actual momentum derivative within the closed horizon. |
| Full K3 in the exact existing endpoint-inclusive predicate | `KirkMedhin.K3.augmentedEulerLagrange_of_isoperimetric` | Primitive C2 `L,G,x`, C1 `K`, and the same optimum/regularity data. Returns one multiplier, `HasVanishingFirstVariation`, and the unchanged `eulerLagrange`. |
| Interior Euler–Lagrange from the actual minimum | `KirkMedhin.WeakCoV.eulerLagrange_hasDerivAt_of_fixedEndpoint_min` | Jointly C1 `L`, C1 `K,x`, positive horizon, and the actual fixed-endpoint C1 minimum. Momentum differentiability is a conclusion. |
| Autonomous weak du Bois–Reymond | `KirkMedhin.DuBoisReymond.energy_eq_of_cvFunctional_min` | C1 autonomous `L`, actual global arc derivative `∀ t, HasDerivAt x (v t) t`, continuous velocity, positive horizon, and actual fixed-endpoint piecewise C1 minimum. Energy is constant on the closed horizon. |
| Nonautonomous weak du Bois–Reymond, **one-corner** class | `KirkMedhin.NonautonomousDuBoisReymond.weak_duBoisReymond_of_cvFunctional_min` | Jointly C1 time-dependent `L`, actual global arc derivative `∀ t, HasDerivAt x (v t) t`, continuous velocity, positive horizon, and the actual minimum over the **one-corner** fixed-endpoint class `fixedEndpointPiecewiseC1Curves T (x 0) (x T)` (membership is a single `IsPiecewiseC₁On` with one interior cut and continuous one-sided velocities). Returns the integrated energy law and its actual interior derivative. |
| Nonautonomous weak du Bois–Reymond, **finite-piecewise** class | `KirkMedhin.FinitePiecewise.weak_duBoisReymond_of_finite_cvFunctional_min` | The same C1 data and positive horizon, but the actual minimum is taken over the separate finite-piecewise class `fixedEndpointFinitePiecewiseC1Curves T (x 0) (x T)` (any finite number of matching corners). This is the stronger class used by the finite-corner and original-predicate endpoints below; the one-corner theorem is not a specialization of it. |
| Original-predicate nonautonomous corner theorem | `KirkMedhin.FinitePiecewise.weierstrassErdmann_of_piecewiseC1On_min` | Existing `IsPiecewiseC₁On`, continuous one-sided velocities, jointly C1 `L`, actual minimum over the horizon-only finite-piecewise class, and complete real normed state space. Returns both momentum and energy matching. |
| Original-predicate autonomous specialization | `KirkMedhin.FinitePiecewise.autonomous_weierstrassErdmann_of_piecewiseC1On_min` | The preceding scope for an autonomous C1 Lagrangian, with the existing `energyCurve` in the conclusion. |
| Every represented finite-context corner | `KirkMedhin.FinitePiecewise.nonautonomous_weierstrassErdmann_at_every_represented_corner` | Actual global minimum; any finite time-aware prefix/suffix context around adjacent C1 arcs; representation only needs to agree with the reference on the physical horizon. |

The specifically requested name
`KirkMedhin.FinitePiecewise.corner_energy_eq_of_cvFunctional_min_weak` is also
proved. It is the autonomous two-arc result in the ambient class allowing any
finite number of corners. The original-predicate and nonautonomous theorems above
are stronger convenience endpoints for the completed argument.

The native sources for the two main task endpoints are
[K3IsoperimetricLift.lean](../../DynamicalSystems/OptimalControl/ContinuousTime/K3IsoperimetricLift.lean)
and [PiecewiseC1MinimumPrinciple.lean](../../DynamicalSystems/OptimalControl/ContinuousTime/PiecewiseC1MinimumPrinciple.lean).

## K3: one multiplier before every test direction

Fix the regular constraint direction `ξ` before selecting the arbitrary test `η`.
The actual perturbation is

\[
\Gamma(a,b)(t)=x(t)+a\eta(t)+b\xi(t).
\]

Every parameter value preserves the prescribed endpoints and continuous
differentiability. The isoperimetric constraint is imposed on the parameter level
set `C(a,b)=C(0,0)`; the whole two-parameter family is not claimed to preserve it.
The previously integrated strict integral-differentiation theorems provide the
actual derivatives of the cost and constraint. The genuine constrained minimum gives

\[
\lambda=-\frac{\delta J[\xi]}{\delta C[\xi]},\qquad
\delta J[\eta]+\lambda\delta C[\eta]=0
\]

for every endpoint-zero C1 `η`. The quotient is independent of `η`; the new
`exists_common_isoperimetricMultiplier` theorem has `∃ λ, ∀ η` in that order.
Actual differentiation of the augmented Lagrangian and proved integrability of
the C1 densities identify this with the existing first variation of `L + λG`.
No multiplier or stationarity premise is supplied to either final theorem.

### Momentum regularity is derived

[WeakEulerLagrange.lean](../../DynamicalSystems/OptimalControl/ContinuousTime/WeakEulerLagrange.lean)
proves the weak fundamental lemma for continuous covector-valued `p,q`:

\[
\int_a^b\bigl(q(t)[\eta(t)]+p(t)[\eta'(t)]\bigr)\,dt=0
\quad\Longrightarrow\quad
p(t)=p(a)+\int_a^tq(s)\,ds.
\]

For each fixed state vector, a scalar residual is tested against the primitive
of its difference from its interval average. A zero variance integral forces
that scalar residual to be constant. Extensionality gives the covector identity,
and FTC supplies the derivative. This requires no finite-dimensionality, inner
product, or completeness assumption on the state space.

Applying the lemma to the actual state and velocity derivatives of `L + λG`
produces Euler–Lagrange. The exact existing `HasVanishingFirstVariation` class is
then recovered for **all differentiable** endpoint-zero directions. This respects
the repository's totalized interval integral: FTC handles integrable densities;
the undefined-case integral value handles nonintegrable densities. It does not
assert a cost derivative exists in every merely differentiable test direction.

### The endpoint distinction is necessary

The unchanged `eulerLagrange` predicate requires an ordinary two-sided momentum
derivative at both endpoints. Finite-horizon C1 variational data yield a within-
horizon derivative there and an ordinary derivative in the interior. C2 primitive
data provide the extra endpoint regularity for the exact-predicate corollary.

This is a proved distinction. The regression
[WeakEulerLagrangeEndpoint.lean](../../DynamicalSystemsTest/KirkMedhin/WeakEulerLagrangeEndpoint.lean)
uses `L = v²/2` and `x(t)=t²` on the left of zero, `x(t)=0` on the right. It proves
global C1 regularity, actual kinetic-action optimality on `[0,1]`, the exact
all-differentiable stationarity predicate, and failure of the old two-sided
endpoint conclusion. Both the natural C1 horizon result and the exact existing
API under sufficient primitive regularity are provided.

## K4: weak energy from actual time variations

The weak route avoids differentiating velocity. At every interior cut `a`, two
actual subarcs exchange a small amount of duration while preserving the total
horizon and endpoints. Their actual costs are identified with fixed-reference-
interval integrals before differentiation.

For an autonomous Lagrangian, the derivative at zero gives equality of the average
energies on the two sides of every cut. Thus the primitive of energy is linear;
FTC and endpoint continuity give energy constancy. Euler–Lagrange and acceleration
are not hypotheses of this argument.

For nonautonomous costs the moving density is

\[
rL\bigl(t+(r-1)\alpha,\,x,\,r^{-1}v\bigr).
\]

Its derivative at `r=1` is `α L_t − E`, where `E = L_v[v] − L`. Joint C1
regularity and compactness justify differentiation of the actual integral with
only continuous state and velocity. For the right arc, both its scale and its
physical start time move. The exact cost identity retains
`d₁ + ε + (1 − ε/d₂)t`; dropping the `ε` would give an incorrect theorem.

The resulting affine time weights imply

\[
E(t)+\int_0^t L_t(s,x(s),v(s))\,ds=E(0),\qquad
E'(t)=-L_t(t,x(t),v(t))\quad(0<t<T).
\]

The nonautonomous energy adapter delegates directly to the existing project's
`energyCurve` at the current time slice.

### Corners and finite surrounding arcs

Actual splicing transfers the global minimum to each subarc. The finite-piecewise
competitor class is generated by smooth arcs and finitely many matching joins;
its membership contains no stationarity or optimality identities. Allowing finite
joins is necessary because an interior time variation can add a cut to a curve
that already has a corner.

Spatial perturbations moving the join give momentum matching after the derived
interior Euler–Lagrange equation is integrated. The derived weak energy equation
similarly turns the duration-exchange derivative into the difference of the
one-sided corner energies. Both conditions follow from the actual minimum.

The time-aware finite context records the physical start time of the varied
subarc. The multiple-corner theorem applies to every explicit finite-context
representation of an adjacent pair. This is the supported representation; it
does not advertise automatic extraction of partition indices from an arbitrary
inductive witness.

For the original `IsPiecewiseC₁On` predicate, the final adapter constructs two
global C1 branches as velocity primitives and proves that their concatenation
agrees with the reference on `[0,T]`. `[CompleteSpace E]` supports those primitives
and in particular covers finite-dimensional real state spaces. The horizon-only
ambient class ignores values outside the horizon, and reference membership is
proved from the original predicate. The adapter imposes no additional global
regularity or supplied branch decomposition. The original predicate's half-line
within-derivatives already encode its own endpoint regularity convention; that
existing convention has not been changed.

## Regression examples

| File | What it verifies |
| --- | --- |
| [K3IsoperimetricExample.lean](../../DynamicalSystemsTest/KirkMedhin/K3IsoperimetricExample.lean) | Actual constrained optimum for `L=v²+y`, `G=y`, zero endpoints and zero integral constraint. The general final theorem applies; the multiplier is proved to be `−1`. |
| [WeakEulerLagrangeEndpoint.lean](../../DynamicalSystemsTest/KirkMedhin/WeakEulerLagrangeEndpoint.lean) | The C1 endpoint limitation above, including actual optimality and the exact original stationarity predicate. |
| [WeakDuBoisReymond.lean](../../DynamicalSystemsTest/KirkMedhin/WeakDuBoisReymond.lean) | A nonconstant quadratic Lagrangian and an actual minimizing curve with velocity `(0, abs(t−1/2))`. The weak theorem applies and the velocity is proved nondifferentiable at the interior point `1/2`. |
| [NonautonomousDuBoisReymond.lean](../../DynamicalSystemsTest/KirkMedhin/NonautonomousDuBoisReymond.lean) | The same cusp reference with `L=v₁²−t`: actual optimum of cost `−1/2`, energy `E=t`, time partial `−1`, and the new theorem yielding compensated energy zero and `E'=1`. |

## Validation and reproduction

Run from a normal checkout with the pinned dependencies installed:

```bash
bash docs/kirk_medhin/check_k3_k4.sh
```

The script builds the default library, compiles the four regression modules in
dependency order, then runs:

- [K3K4Audit.lean](K3K4Audit.lean): exhaustive standard-axiom checking of every
  declaration owned by the 20 source modules and 4 test modules (24 modules,
  355 declarations in total, including the existing strict-integral K3 module),
  including private and generated declarations; all 15 default declaration
  linters for every module.
- [K3K4ProofPaths.lean](K3K4ProofPaths.lean): 49 actual proof-term dependency checks
  across the multiplier lift, real functional derivatives, weak fundamental lemma,
  constructed variations, finite splices, and original-predicate endpoint.
- [CampaignTargets.lean](CampaignTargets.lean): all 34 required declarations from
  the eight-task campaign manifest, with their complete axiom dependencies.

The recorded validation uses stock Lean `4.35.0-rc2` at
`11acb17ec6b07a8f9e9173e6845197929540936b` and Mathlib at
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The full default-library and regression
dependency closure is compiled with the repository's Lean options. The machine
record [K3_K4_VALIDATION.json](K3_K4_VALIDATION.json) identifies exact source hashes,
counts, audit results, and the distinction between clean new modules and observed
pre-existing warnings elsewhere. A small host startup shim locates the stock Lean
executable through `/proc/self/exe`; it changes no compiler, elaborator, kernel,
proof, or logical axiom. The shell reproduction script is for a standard checkout;
the recorded local build invokes the pinned native compiler directly.

The existing K3 differentiation file also receives a declaration-lint cleanup:
two redundant specialized `[simp]` attributes are removed because the general
`parameterDerivative_apply` simp theorem already proves the same reductions.
The named lemmas and their statements/proofs remain available.

## Scope and campaign acceptance

The requested regular K3 lift and weak K4 arguments are complete under the
explicit assumptions above. No unresolved mathematical construction is passed as
a premise to the final theorems. The result concerns the stated fixed-endpoint
variational classes. It does not change the previously scoped K1, K2, K5, or K6
theorem contracts or claim a Sobolev/general measurable-control theorem.

### Weak-K4 acceptance is carried by the `_weak` names

Weak-K4 acceptance is carried by the declarations whose names record the weak
route, not by the legacy strong adapter. The relevant endpoints are
`KirkMedhin.NonautonomousDuBoisReymond.weak_duBoisReymond_of_cvFunctional_min`,
`KirkMedhin.FinitePiecewise.weak_duBoisReymond_of_finite_cvFunctional_min`,
`KirkMedhin.FinitePiecewise.weierstrassErdmann_of_cvFunctional_min_weak`, and
`KirkMedhin.FinitePiecewise.corner_energy_eq_of_cvFunctional_min_weak`.
The legacy
`KirkMedhin.TimeReparametrization.corner_energy_eq_of_cvFunctional_min` is **not**
a weak-K4 endpoint: its signature still takes velocity differentiability
(`hvd₁`, `hvd₂`) and interior Euler–Lagrange equations (`hEL₁`, `hEL₂`) as
hypotheses. It is retained only as an auxiliary strong adapter (and listed in
`CampaignTargets.lean` for that purpose), and it must not be read as the evidence
that discharges the weak-K4 obligation.

A proved equivalence is legitimate mathematics. The relevant acceptance failure
is supplying an unresolved object or the desired result under another name as an
input. The dependency audits complement explicit theorem statements and semantic
review; declaration names alone are not acceptance evidence.

These are formalizations of classical variational necessity arguments. References:
Donald E. Kirk, *Optimal Control Theory: An Introduction*, Dover, 2004; Leonard D.
Berkovitz and Negash G. Medhin, *Nonlinear Optimal Control Theory*, Chapman &
Hall/CRC, 2012. No mathematical originality claim is made.
