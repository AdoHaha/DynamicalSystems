import DynamicalSystems.OptimalControl.ContinuousTime.NeedleFamily
import DynamicalSystems.OptimalControl.ContinuousTime.TerminalNeedleSensitivity

/-!
# Terminal tangent of the constructed feasible needle family

This adapter discharges all post-spike trajectory premises of the terminal
sensitivity theorem from the actual constructed family. The only remaining
inputs are primitive differentiability data and the proved backward propagator.
-/

namespace NeedleIntegralModel

open Set Filter MeasureTheory
open scoped Topology

variable {E U : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Propagation of the actual local jump of a constructed feasible family to
its actual terminal state. Applies equally to ordinary and cost-augmented ODEs. -/
theorem terminal_tangent_of_constructed_family
    (prob : ContinuousOCP E U) (x_init : E) (x₀ : ℝ → E) (u₀ : ℝ → U)
    (τ : ℝ) (v : U) {Kv M C : ℝ} {xε : ℝ → ℝ → E}
    {D : ℝ → E → E →L[ℝ] E} {Phi : ℝ → ℝ → E →L[ℝ] E}
    (hτ₀ : 0 ≤ τ) (hτ : τ ≤ prob.T) (hC : 0 ≤ C)
    (hF₀ : Continuous (fun q : ℝ × E => prob.f q.1 q.2 (u₀ q.1)))
    (hx₀ : IsIntegralCurve x₀ (fun t z => prob.f t z (u₀ t)))
    (hD : ∀ t ∈ Icc 0 prob.T, ∀ z,
      HasFDerivAt (fun y => prob.f t y (u₀ t)) (D t z) z)
    (hDc : ∀ t ∈ Icc 0 prob.T,
      ContinuousAt (fun q : ℝ × E => D q.1 q.2) (t, x₀ t))
    (hdiag : Phi prob.T prob.T = ContinuousLinearMap.id ℝ E)
    (hback : ∀ t ∈ Icc τ prob.T, HasDerivAt (fun s => Phi prob.T s)
      (-((Phi prob.T t).comp (D t (x₀ t)))) t)
    (hfamily : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ConstructedNeedle prob x_init x₀ u₀ τ v ε (xε ε) Kv M C)
    (hjump : Tendsto (fun ε : ℝ => ε⁻¹ •
      (xε ε τ - x₀ τ - ε • (prob.f τ (x₀ τ) v - prob.f τ (x₀ τ) (u₀ τ))))
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ε⁻¹ • (xε ε prob.T - x₀ prob.T))
      (𝓝[>] 0)
      (𝓝 (Phi prob.T τ (prob.f τ (x₀ τ) v - prob.f τ (x₀ τ) (u₀ τ)))) := by
  apply KirkMedhin.terminal_tangent_of_right_ODE
    (F := fun t z => prob.f t z (u₀ t)) (D := D) (x := x₀) (y := xε)
    hτ hC hdiag hback hF₀
    hx₀.continuous.continuousOn
    (fun t _ => (hx₀ t).hasDerivWithinAt)
    (fun t ht => hD t ⟨hτ₀.trans ht.1, ht.2⟩)
    (fun t ht => hDc t ⟨hτ₀.trans ht.1, ht.2⟩)
    (hfamily.mono fun _ h => h.continuous.continuousOn) _ _ hjump
  · filter_upwards [hfamily] with ε hε
    intro t ht
    have hn : t ∉ Ico (τ - ε) τ := fun h => (not_lt.mpr ht.1.le) h.2
    simpa only [needleControl, ite_eq_right hn] using hε.right_derivative t
  · filter_upwards [hfamily] with ε hε
    exact fun t ht => hε.displacement_bound t ⟨hτ₀.trans ht.1, ht.2⟩

end NeedleIntegralModel
