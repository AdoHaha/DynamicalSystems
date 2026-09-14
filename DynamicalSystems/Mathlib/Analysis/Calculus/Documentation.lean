import VersoManual

import DynamicalSystems.Mathlib.Analysis.Calculus.Barbalat

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option linter.hashCommand false
set_option linter.missingDocs false
set_option verso.docstring.allowMissing true

#doc (Manual) "Barbălat's lemma" =>

This chapter formalizes the results of B. Farkas and S.-A. Wegner,
*Variations on Barbălat's Lemma*, [arXiv:1411.1611](https://arxiv.org/abs/1411.1611).
They concern a classical tool of nonlinear and adaptive control theory: a real function
whose improper integral converges and whose oscillation is controlled must vanish at
infinity.

Barbălat's original statement is qualitative (it asserts convergence, not a rate). The
formalization below keeps the paper's direct "hard analysis" proof, which is quantitative,
and therefore we also obtain explicit rate statements. The results live in
`DynamicalSystems/Mathlib/Analysis/Calculus/Barbalat.lean`, in the `Barbalat` namespace,
as this material is destined for Mathlib.

# Barbălat's lemma

The original statement: a uniformly continuous function $`f : [0, ∞) → ℝ` whose improper
integral $`\int_0^t f` converges must satisfy $`f(t) \to 0`. The formalization gives the
vector-valued version, valid for a function with values in a Banach space.

{docstring Barbalat.tendsto_zero_of_uniformContinuousOn_of_tendsto_intervalIntegral}

The scalar case is a direct corollary.

{docstring Barbalat.tendsto_zero_of_uniformContinuousOn_of_tendsto_intervalIntegral_real}

Note that the hypothesis is *conditional* convergence of the improper integral, not
absolute integrability: it is encoded as `∃ L, Tendsto (fun t ↦ ∫ x in 0..t, f x) atTop (𝓝 L)`.

# The quantitative estimate

The heart of the direct proof is the following scale. It is the supremum of the norms of
the tail integrals of `f` starting at `t`.

{docstring Barbalat.tailSup}

The key estimate is that $`s \cdot \lVert f(t) \rVert \le S(t) + ω(s) \cdot s` for every
`0 < s`, where `ω` is a modulus of continuity for `f`. Optimising in `s` gives the paper's
Lemma 2/3.

{docstring Barbalat.mul_norm_le_tailSup_add_mul_modulus}

{docstring Barbalat.norm_le_sqrt_tail_add_modulus}

The tail supremum is finite, and tends to zero, whenever the improper integral converges.

{docstring Barbalat.exists_bound_primitive}

{docstring Barbalat.bddAbove_range_tailSup}

{docstring Barbalat.tendsto_tailSup_zero}

# An `L^q` derivative gives Hölder regularity

The paper's Lemma 6: when `f` has an `L^q(0, ∞)` derivative, then `f` is Hölder continuous
with exponent `(q - 1) / q`, and Lipschitz in the endpoint case `q = ∞`. This is the
estimate $`\lVert f(y) - f(x) \rVert \le (y - x)^{1/q'} \lVert f' \rVert_q` obtained from
the fundamental theorem of calculus and Hölder's inequality. The paper's class uses the
almost-everywhere derivative; here this is encoded by absolute continuity, and the FTC is
the Lebesgue one for absolutely continuous functions.

{docstring Barbalat.holderOn_of_absolutelyContinuousOnInterval}

{docstring Barbalat.lipschitzOn_of_absolutelyContinuousOnInterval}

For functions differentiable everywhere the same bounds hold under the stronger hypothesis
`∀ x, HasDerivAt f (f' x) x`.

{docstring Barbalat.holderOn_of_memLp_deriv}

{docstring Barbalat.lipschitzOn_of_memLp_deriv}

# The mixed Sobolev space `W^{1,p,q}`

The paper's Theorem 5 unifies several "alternative versions" of Barbălat's lemma that
appeared in the literature: Tao's version (`f ∈ L²`, `f' ∈ L^∞`) and the
Desoer–Vidyasagar/Teel version (`f, f' ∈ L^p`). It states that every `f` in the mixed
Sobolev space `W^{1,p,q}(0, ∞)` tends to zero at infinity. The paper's space uses the
almost-everywhere derivative, encoded here by absolute continuity.

{docstring Barbalat.tendsto_zero_of_absolutelyContinuous_memLp}

The two named alternatives are corollaries.

{docstring Barbalat.tendsto_zero_of_absolutelyContinuous_memLp_two_top}

{docstring Barbalat.tendsto_zero_of_absolutelyContinuous_memLp_self}

For functions that are differentiable everywhere the same conclusion holds under the
stronger hypothesis `∀ x, HasDerivAt f (f' x) x`.

{docstring Barbalat.tendsto_zero_of_memLp_deriv_finite}

{docstring Barbalat.tendsto_zero_of_memLp_deriv_top}

{docstring Barbalat.tendsto_zero_of_memLp_deriv}

The auxiliary boundedness statement used in the proof is the second half of Lemma 6.

{docstring Barbalat.exists_bound_of_uniformContinuousOn_of_integrable_norm_rpow}

{docstring Barbalat.uniformContinuousOn_norm_rpow_of_bounded}

{docstring Barbalat.tendsto_zero_of_uniformContinuousOn_of_integrable_norm_rpow}

# Rates of convergence

Finally, the paper's Section 3 makes the estimate quantitative. For a Hölder continuous
function of order `α`, the exponent `1/2` in Lemma 2/3 improves to `α / (1 + α)`.

{docstring Barbalat.norm_le_rpow_tailSup_of_holder}

{docstring Barbalat.norm_le_rpow_tailSup_of_holder_of_tendsto}

For `f ∈ W^{1,p,q}` this yields the paper's Corollary 9.

{docstring Barbalat.norm_pow_le_tailIntegral_rate}

The endpoint `q = ∞` (the space `W^{1,1,∞}` of the adaptive-control example) has exponent
`1/2`.

{docstring Barbalat.norm_pow_le_tailIntegral_rate_top}

The boundedness half of Lemma 6 is also available in bundled form.

{docstring Barbalat.boundedOn_of_memLp_deriv}

# Relation to the rest of the library

The results above are pure real analysis and are independent of the theory of dynamical
systems. Their control-theoretic use, namely an application to adaptive control, is
formalized in `DynamicalSystems.Stability.Barbalat` and documented in the stability
chapter of this manual.
