import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Adjoint cancellation with right derivatives

The spatial differentiation of the control Hamiltonian produces the usual
linear adjoint expression. This bridges the pairing lemmas to the project's
gradient-based `costateEquation`.
-/


open Set
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
