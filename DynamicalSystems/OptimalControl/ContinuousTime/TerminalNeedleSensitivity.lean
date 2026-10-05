import DynamicalSystems.OptimalControl.ContinuousTime.UniformTaylorRemainder
import DynamicalSystems.Mathlib.Analysis.ODE.StateTransition

/-!
# Terminal sensitivity of actual needle trajectories

The propagated first-order terminal displacement is derived from the actual
post-needle ODE, uniform `O(ε)` displacement, the local needle jump, and
continuous spatial derivatives. Duhamel cancellation is proved for right
derivatives, allowing corners at the switching times. Only the terminal row
of the state transition is needed; compact-interval propagators suffice.
-/


open Set Filter MeasureTheory
open scoped Interval Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- The backward product cancellation for a right-differentiable trajectory. -/
theorem duhamel_cancellation_right
    {A : ℝ → E →L[ℝ] E} {P : ℝ → E →L[ℝ] E}
    {b x : ℝ → E} {t : ℝ}
    (hP : HasDerivAt P (-(P t).comp (A t)) t)
    (hx : HasDerivWithinAt x (A t (x t) + b t) (Ici t) t) :
    HasDerivWithinAt (fun s => P s (x s)) (P t (b t)) (Ici t) t := by
  simpa [map_add] using hP.hasDerivWithinAt.clm_apply hx

/-- Duhamel's formula using the actual right derivatives and the backward
operator equation. This works at finite switching corners. -/
theorem variationOfConstants_right_of_backward
    {A : ℝ → E →L[ℝ] E} {P : ℝ → E →L[ℝ] E}
    {b x : ℝ → E} {a t : ℝ}
    (hat : a ≤ t) (hPt : P t = ContinuousLinearMap.id ℝ E)
    (hP : ∀ s ∈ Icc a t, HasDerivAt P (-(P s).comp (A s)) s)
    (hxc : ContinuousOn x (Icc a t))
    (hx : ∀ s ∈ Ioo a t, HasDerivWithinAt x (A s (x s) + b s) (Ici s) s)
    (hint : IntervalIntegrable (fun s => P s (b s)) volume a t) :
    x t = P a (x a) + ∫ s in a..t, P s (b s) := by
  have hPc : ContinuousOn P (Icc a t) :=
    fun s hs => (hP s hs).continuousAt.continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    hat (hPc.clm_apply hxc)
    (fun s hs => (duhamel_cancellation_right (hP s ⟨hs.1.le, hs.2.le⟩)
      (hx s hs)).mono Ioi_subset_Ici_self) hint
  simp only [hPt, ContinuousLinearMap.id_apply] at hFTC
  rw [hFTC]
  abel

omit [CompleteSpace E] in
/-- A uniformly bounded operator family preserves uniform first-order smallness. -/
theorem _root_.UniformSmall.clm_apply
    {r : ℝ → ℝ → E} {P : ℝ → E →L[ℝ] E} {s : Set ℝ} {B : ℝ}
    (hr : UniformSmall r s) (hB : 0 ≤ B) (hP : ∀ t ∈ s, ‖P t‖ ≤ B) :
    UniformSmall (fun ε t => P t (r ε t)) s := by
  intro η hη
  have hBp : 0 < B + 1 := by linarith
  filter_upwards [hr (η / (B + 1)) (div_pos hη hBp), self_mem_nhdsWithin]
    with ε hrε hpos
  intro t ht
  have hεpos : 0 < ε := hpos
  calc
    ‖P t (r ε t)‖ ≤ ‖P t‖ * ‖r ε t‖ := (P t).le_opNorm _
    _ ≤ B * (η / (B + 1) * ε) :=
      mul_le_mul (hP t ht) (hrε t ht) (norm_nonneg _) hB
    _ = (η * ε) * (B / (B + 1)) := by ring
    _ ≤ (η * ε) * 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (div_le_one hBp).mpr (by linarith)
    _ = _ := mul_one _

/-- Actual terminal sensitivity from a local needle jump and the actual
post-spike ODE. No flow derivative, sensitivity conclusion, or Duhamel
cancellation is supplied as a premise. -/
theorem terminal_sensitivity_of_right_ODE
    {F : ℝ → E → E} {D : ℝ → E → E →L[ℝ] E}
    {x : ℝ → E} {y : ℝ → ℝ → E} {τ T C : ℝ} {g : E}
    {Phi : ℝ → ℝ → E →L[ℝ] E}
    (hτT : τ ≤ T) (hC : 0 ≤ C)
    (hdiag : Phi T T = ContinuousLinearMap.id ℝ E)
    (hback : ∀ s ∈ Icc τ T,
      HasDerivAt (fun r => Phi T r) (-((Phi T s).comp (D s (x s)))) s)
    (hF : Continuous F.uncurry)
    (hxc : ContinuousOn x (Icc τ T))
    (hx : ∀ t ∈ Ioo τ T, HasDerivWithinAt x (F t (x t)) (Ici t) t)
    (hD : ∀ t ∈ Icc τ T, ∀ z, HasFDerivAt (F t) (D t z) z)
    (hDc : ∀ t ∈ Icc τ T, ContinuousAt (fun q : ℝ × E => D q.1 q.2) (t, x t))
    (hyc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ContinuousOn (y ε) (Icc τ T))
    (hy : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Ioo τ T,
      HasDerivWithinAt (y ε) (F t (y ε t)) (Ici t) t)
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc τ T, ‖y ε t - x t‖ ≤ C * ε)
    (hjump : Tendsto (fun ε : ℝ => ε⁻¹ • (y ε τ - x τ - ε • g))
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ε⁻¹ •
      (y ε T - x T - ε • Phi T τ g)) (𝓝[>] 0) (𝓝 0) := by
  let r : ℝ → ℝ → E := fun ε t => taylorError (F t) (D t (x t)) (x t) (y ε t)
  have hr : UniformSmall r (Icc τ T) :=
    uniformSmall_taylorError hC hxc hD hDc hbound
  have hPc : ContinuousOn (fun s => Phi T s) (Icc τ T) :=
    fun s hs => (hback s hs).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hPc
  have hsmall : UniformSmall (fun ε t => Phi T t (r ε t)) (uIcc τ T) := by
    rw [uIcc_of_le hτT]
    exact _root_.UniformSmall.clm_apply hr (le_max_right B 0)
      (fun t ht => (hB t ht).trans (le_max_left B 0))
  have hrem := hsmall.tendsto_scaled_integral
  have hAc : ContinuousOn (fun t => D t (x t)) (Icc τ T) := by
    intro t ht
    exact (hDc t ht).comp_continuousWithinAt (f := fun s : ℝ => (s, x s))
      (continuousWithinAt_id.prodMk (hxc t ht))
  have hduhamel : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      y ε T - x T = Phi T τ (y ε τ - x τ) + ∫ t in τ..T, Phi T t (r ε t) := by
    filter_upwards [hyc, hy] with ε hycε hyε
    have hec : ContinuousOn (fun t => y ε t - x t) (Icc τ T) := hycε.sub hxc
    have hrc : ContinuousOn (r ε) (Icc τ T) :=
      ((hF.comp_continuousOn (continuousOn_id.prodMk hycε)).sub
        (hF.comp_continuousOn (continuousOn_id.prodMk hxc))).sub (hAc.clm_apply hec)
    have hint : IntervalIntegrable (fun t => Phi T t (r ε t)) volume τ T := by
      apply ContinuousOn.intervalIntegrable
      simpa only [uIcc_of_le hτT] using hPc.clm_apply hrc
    apply variationOfConstants_right_of_backward hτT hdiag hback hec _ hint
    intro t ht
    convert (hyε t ht).sub (hx t ht) using 1
    dsimp [r, taylorError]
    abel
  have hstart : Tendsto (fun ε : ℝ =>
      ε⁻¹ • (Phi T τ (y ε τ - x τ) - ε • Phi T τ g)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Phi T τ).continuous.continuousAt.tendsto.comp hjump
    simpa only [Function.comp_def, map_smul, map_sub, map_zero] using h
  have hsum := hstart.add hrem
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [hduhamel] with ε hε
  rw [hε]
  simp only [← smul_add]
  congr 1
  abel

/-- The uncentered terminal tangent limit, in the form used by endpoint
variation cones and Hahn–Banach separation. -/
theorem terminal_tangent_of_right_ODE
    {F : ℝ → E → E} {D : ℝ → E → E →L[ℝ] E}
    {x : ℝ → E} {y : ℝ → ℝ → E} {τ T C : ℝ} {g : E}
    {Phi : ℝ → ℝ → E →L[ℝ] E}
    (hτT : τ ≤ T) (hC : 0 ≤ C)
    (hdiag : Phi T T = ContinuousLinearMap.id ℝ E)
    (hback : ∀ s ∈ Icc τ T,
      HasDerivAt (fun r => Phi T r) (-((Phi T s).comp (D s (x s)))) s)
    (hF : Continuous F.uncurry)
    (hxc : ContinuousOn x (Icc τ T))
    (hx : ∀ t ∈ Ioo τ T, HasDerivWithinAt x (F t (x t)) (Ici t) t)
    (hD : ∀ t ∈ Icc τ T, ∀ z, HasFDerivAt (F t) (D t z) z)
    (hDc : ∀ t ∈ Icc τ T, ContinuousAt (fun q : ℝ × E => D q.1 q.2) (t, x t))
    (hyc : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ContinuousOn (y ε) (Icc τ T))
    (hy : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Ioo τ T,
      HasDerivWithinAt (y ε) (F t (y ε t)) (Ici t) t)
    (hbound : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ t ∈ Icc τ T, ‖y ε t - x t‖ ≤ C * ε)
    (hjump : Tendsto (fun ε : ℝ => ε⁻¹ • (y ε τ - x τ - ε • g))
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ε⁻¹ • (y ε T - x T))
      (𝓝[>] 0) (𝓝 (Phi T τ g)) := by
  have h := terminal_sensitivity_of_right_ODE hτT hC hdiag hback hF hxc hx
    hD hDc hyc hy hbound hjump
  have hsum := h.add_const (Phi T τ g)
  simp only [zero_add] at hsum
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hpos
  have hε : ε ≠ (0 : ℝ) := ne_of_gt hpos
  simp [smul_sub, smul_smul, hε]

