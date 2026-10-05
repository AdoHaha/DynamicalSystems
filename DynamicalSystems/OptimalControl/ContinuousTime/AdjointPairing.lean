import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Adjoint cancellation with right derivatives

The linearized state and adjoint equations imply the differentiated pairing
identity. The cancellation is derived, not supplied as a premise. The integral
version requires only continuous trajectories and right derivatives, so it
applies to continuous trajectories with finitely many control switches.

For a needle proof, `d` is the actual finite state difference and `b` is the
frozen-state control jump plus the nonlinear Taylor remainder. Thus the result
does not require parameter differentiability of the nonlinear solution map.
-/

namespace K1AdjointPairing

open Set MeasureTheory
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Spatial differentiation of the control Hamiltonian produces the usual
linear adjoint expression. This bridges the pairing lemmas to the project's
gradient-based `costateEquation`. -/
theorem hasGradientAt_hamiltonian
    {L : E → ℝ} {f : E → E} {x p ell : E} {A : E →L[ℝ] E}
    (hL : HasGradientAt L ell x) (hf : HasFDerivAt f A x) :
    HasGradientAt (fun y => L y + inner ℝ p (f y)) (ell + A.adjoint p) x := by
  have hlin : HasFDerivAt (fun y => inner ℝ p (f y))
      ((InnerProductSpace.toDual ℝ E p).comp A) x :=
    (InnerProductSpace.toDual ℝ E p).hasFDerivAt.comp x hf
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hL.hasFDerivAt.add hlin using 1
  ext v
  change inner ℝ (ell + A.adjoint p) v = inner ℝ ell v + inner ℝ p (A v)
  rw [inner_add_left, ContinuousLinearMap.adjoint_inner_left]

/-- The forward linear term and backward adjoint term cancel in the pairing. -/
theorem hasDerivWithinAt_pairing
    {p d ell b : ℝ → E} {A : ℝ → E →L[ℝ] E} {s : Set ℝ} {t : ℝ}
    (hp : HasDerivWithinAt p (-(A t).adjoint (p t) - ell t) s t)
    (hd : HasDerivWithinAt d ((A t) (d t) + b t) s t) :
    HasDerivWithinAt (fun r => inner ℝ (p r) (d r))
      (inner ℝ (p t) (b t) - inner ℝ (ell t) (d t)) s t := by
  have h := hp.inner ℝ hd
  convert h using 1
  simp only [inner_add_right, inner_sub_left, inner_neg_left,
    ContinuousLinearMap.adjoint_inner_left]
  ring

/-- Integration of the derived pairing identity. At switches, right derivatives
are sufficient; the trajectories themselves remain continuous. -/
theorem integral_adjoint_pairing
    {p d ell b : ℝ → E} {A : ℝ → E →L[ℝ] E} {a z : ℝ}
    (haz : a ≤ z)
    (hpc : ContinuousOn p (Icc a z))
    (hdc : ContinuousOn d (Icc a z))
    (hp : ∀ t ∈ Ioo a z,
      HasDerivWithinAt p (-(A t).adjoint (p t) - ell t) (Ioi t) t)
    (hd : ∀ t ∈ Ioo a z,
      HasDerivWithinAt d ((A t) (d t) + b t) (Ioi t) t)
    (hbi : IntervalIntegrable (fun t => inner ℝ (p t) (b t)) volume a z)
    (hli : IntervalIntegrable (fun t => inner ℝ (ell t) (d t)) volume a z) :
    inner ℝ (p z) (d z) - inner ℝ (p a) (d a) +
        (∫ t in a..z, inner ℝ (ell t) (d t)) =
      ∫ t in a..z, inner ℝ (p t) (b t) := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le haz
    (hpc.inner hdc)
    (fun t ht => hasDerivWithinAt_pairing (hp t ht) (hd t ht))
    (hbi.sub hli)
  rw [intervalIntegral.integral_sub hbi hli] at hFTC
  linarith

/-- Adding the running-cost expansion gives the exact finite-difference cost
identity. The forcing `b` can contain both the needle jump and its remainder. -/
theorem cost_difference_identity
    {p d ell b : ℝ → E} {c : ℝ → ℝ} {A : ℝ → E →L[ℝ] E} {a z : ℝ}
    (haz : a ≤ z)
    (hpc : ContinuousOn p (Icc a z))
    (hdc : ContinuousOn d (Icc a z))
    (hp : ∀ t ∈ Ioo a z,
      HasDerivWithinAt p (-(A t).adjoint (p t) - ell t) (Ioi t) t)
    (hd : ∀ t ∈ Ioo a z,
      HasDerivWithinAt d ((A t) (d t) + b t) (Ioi t) t)
    (hbi : IntervalIntegrable (fun t => inner ℝ (p t) (b t)) volume a z)
    (hli : IntervalIntegrable (fun t => inner ℝ (ell t) (d t)) volume a z)
    (hci : IntervalIntegrable c volume a z) :
    (∫ t in a..z, inner ℝ (ell t) (d t) + c t) +
        inner ℝ (p z) (d z) - inner ℝ (p a) (d a) =
      ∫ t in a..z, c t + inner ℝ (p t) (b t) := by
  have h := integral_adjoint_pairing haz hpc hdc hp hd hbi hli
  rw [intervalIntegral.integral_add hli hci, intervalIntegral.integral_add hci hbi]
  linarith

end K1AdjointPairing
