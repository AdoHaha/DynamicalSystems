import DynamicalSystems.OptimalControl.ContinuousTime.IntegralAdmissibility
import DynamicalSystems.OptimalControl.ContinuousTime.NeedleTrajectory
import DynamicalSystems.Mathlib.Analysis.ODE.GlobalExistenceLinear

/-!
# Actual feasible integral needle trajectories

The trajectories are constructed from the proved global IVP existence theorem,
then glued at the two switching times. The control space is arbitrary: no
convexity, topology, or measurable structure is required on it. Integral
admissibility is essential because the resulting continuous trajectories may
have corners at the switching times.
-/

namespace NeedleIntegralModel

open Set Filter MeasureTheory
open scoped Interval Topology NNReal

variable {X U : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- Glue two curves, choosing the right branch at the switching time. -/
noncomputable def splice (a : ℝ) (x y : ℝ → X) : ℝ → X :=
  fun t => if a ≤ t then y t else x t

omit [NormedSpace ℝ X] [CompleteSpace X] in
theorem splice_continuous {a : ℝ} {x y : ℝ → X}
    (hx : Continuous x) (hy : Continuous y) (hmatch : y a = x a) :
    Continuous (splice a x y) := by
  exact hy.if_le hx continuous_const continuous_id (fun t ht => by
    change a = t at ht
    subst t
    exact hmatch)

omit [CompleteSpace X] in
theorem splice_hasDerivWithinAt {a t : ℝ} {x y : ℝ → X} {dx dy : X}
    (hx : HasDerivWithinAt x dx (Ici t) t)
    (hy : HasDerivWithinAt y dy (Ici t) t) :
    HasDerivWithinAt (splice a x y) (if a ≤ t then dy else dx) (Ici t) t := by
  by_cases hat : a ≤ t
  · simp only [ite_eq_left hat]
    apply hy.congr_of_mem _ (mem_Ici.mpr le_rfl)
    intro s hs
    simp [splice, hat.trans hs]
  · simp only [ite_eq_right hat]
    apply hx.congr_of_eventuallyEq _ (by simp [splice, hat])
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_of_not_ge hat))]
      with s hs
    simp [splice, not_le.mpr (show s < a from hs)]

/-- Integrability of arbitrary switching between two continuous branches.
The branches need not agree at the switch. -/
theorem intervalIntegrable_needle_branches {Y : Type*} [NormedAddCommGroup Y]
    (g₀ gv : ℝ → Y) (hg₀ : Continuous g₀) (hgv : Continuous gv)
    (a b c d : ℝ) :
    IntervalIntegrable (fun t => if t ∈ Ico a b then gv t else g₀ t) volume c d := by
  have h₀ : Integrable g₀ (volume.restrict (uIoc c d)) :=
    intervalIntegrable_iff.mp (hg₀.intervalIntegrable c d)
  have hv : Integrable gv (volume.restrict (uIoc c d)) :=
    intervalIntegrable_iff.mp (hgv.intervalIntegrable c d)
  exact intervalIntegrable_iff.mpr
    (Integrable.piecewise measurableSet_Ico hv.integrableOn h₀.integrableOn)

/-- Existence of a nominal/test/nominal glued solution, obtained from actual IVPs.
The entire derivative assertion is proved, including right derivatives at both
switching times. -/
theorem exists_spliced_solution
    (F₀ Fv : ℝ → X → X) (x₀ : ℝ → X)
    {K₀ Kv : ℝ≥0} {B₀ Bv : ℝ}
    (hLip₀ : ∀ t, LipschitzWith K₀ (F₀ t))
    (hLipv : ∀ t, LipschitzWith Kv (Fv t))
    (hB₀ : ∀ t, ‖F₀ t 0‖ ≤ B₀) (hBv : ∀ t, ‖Fv t 0‖ ≤ Bv)
    (hF₀ : Continuous F₀.uncurry) (hFv : Continuous Fv.uncurry)
    (hx₀ : IsIntegralCurve x₀ F₀) (a b : ℝ) (hab : a ≤ b) :
    ∃ x : ℝ → X,
      Continuous x ∧
      (∀ t, t ≤ a → x t = x₀ t) ∧
      (∀ t, HasDerivWithinAt x
        ((if t ∈ Ico a b then Fv t else F₀ t) (x t)) (Ici t) t) ∧
      (∀ t ∈ Icc a b, x t = x a + ∫ s in a..t, Fv s (x s)) := by
  obtain ⟨Φ₀, hΦ₀⟩ := global_existence hLip₀ hB₀ hF₀
  obtain ⟨Φv, hΦv⟩ := global_existence hLipv hBv hFv
  let y := Φv a (x₀ a)
  let z := Φ₀ b (y b)
  have hy : IsIntegralCurve y Fv := (hΦv a (x₀ a)).1
  have hz : IsIntegralCurve z F₀ := (hΦ₀ b (y b)).1
  have hya : y a = x₀ a := (hΦv a (x₀ a)).2
  have hzb : z b = y b := (hΦ₀ b (y b)).2
  let w := splice a x₀ y
  let x := splice b w z
  have hw : Continuous w := splice_continuous hx₀.continuous hy.continuous hya
  have hxb : z b = w b := by simpa [w, splice, hab] using hzb
  have hx : Continuous x := splice_continuous hw hz.continuous hxb
  have hxy : ∀ t ∈ Icc a b, x t = y t := by
    intro t ht
    by_cases hbt : b ≤ t
    · have htb : t = b := le_antisymm ht.2 hbt
      subst t
      simp [x, splice, hzb]
    · simp [x, w, splice, hbt, ht.1]
  refine ⟨x, hx, ?_, ?_, ?_⟩
  · intro t ht
    by_cases hta : t = a
    · subst t
      exact (hxy a (left_mem_Icc.mpr hab)).trans hya
    · have hta' : t < a := lt_of_le_of_ne ht hta
      have htb : ¬ b ≤ t := not_le.mpr (hta'.trans_le hab)
      simp [x, w, splice, htb, not_le.mpr hta']
  · intro t
    have hwd := splice_hasDerivWithinAt (a := a)
      (hx₀ t).hasDerivWithinAt (hy t).hasDerivWithinAt
    have hxd := splice_hasDerivWithinAt (a := b) hwd (hz t).hasDerivWithinAt
    by_cases hbt : b ≤ t
    · have hn : t ∉ Ico a b := fun h => (not_lt.mpr hbt) h.2
      simpa [x, splice, hbt, hn] using hxd
    · by_cases hat : a ≤ t
      · have hin : t ∈ Ico a b := ⟨hat, lt_of_not_ge hbt⟩
        simpa [x, w, splice, hbt, hat, hin] using hxd
      · have hn : t ∉ Ico a b := fun h => hat h.1
        simpa [x, w, splice, hbt, hat, hn] using hxd
  · intro t ht
    have hint : IntervalIntegrable (fun s => Fv s (y s)) volume a t :=
      (hFv.comp (continuous_id.prodMk hy.continuous)).intervalIntegrable a t
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s (_ : s ∈ uIcc a t) => hy s) hint
    have hEqInt : (∫ s in a..t, Fv s (x s)) = ∫ s in a..t, Fv s (y s) := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le ht.1] at hs
      change Fv s (x s) = Fv s (y s)
      rw [hxy s ⟨hs.1, hs.2.trans ht.2⟩]
    rw [hEqInt, hxy t ht, hxy a (left_mem_Icc.mpr hab), hFTC]
    abel

/-- Properties of an actual feasible needle arc. All of these are conclusions
of `exists_feasible_needle`, not an assumed family-existence residual. -/
structure ConstructedNeedle (prob : ContinuousOCP X U) (x_init : X)
    (x₀ : ℝ → X) (u₀ : ℝ → U) (τ : ℝ) (v : U) (ε : ℝ)
    (x : ℝ → X) (Kv M C : ℝ) : Prop where
  continuous : Continuous x
  before : ∀ t, t ≤ τ - ε → x t = x₀ t
  right_derivative : ∀ t, HasDerivWithinAt x
    (prob.f t (x t) (needleControl u₀ τ v ε t)) (Ici t) t
  dynamics_integrable : ∀ a b, IntervalIntegrable
    (fun t => prob.f t (x t) (needleControl u₀ τ v ε t)) volume a b
  running_integrable : ∀ a b, IntervalIntegrable
    (fun t => prob.L t (x t) (needleControl u₀ τ v ε t)) volume a b
  admissible : IsIntegralAdmissiblePair prob x_init x (needleControl u₀ τ v ε)
  interval_data : NeedleIntervalData x x₀ (fun t z => prob.f t z v)
    (fun t => prob.f t (x₀ t) (u₀ t)) (τ - ε) τ Kv M
  displacement_bound : ∀ t ∈ Icc 0 prob.T, ‖x t - x₀ t‖ ≤ C * ε

/-- One feasible needle and its uniform displacement bound, constructed from
primitive globally Lipschitz branch fields and actual IVPs. -/
theorem exists_feasible_needle
    (prob : ContinuousOCP X U) (x_init : X) (x₀ : ℝ → X) (u₀ : ℝ → U)
    (τ : ℝ) (v : U) {K₀ Kv : ℝ≥0} {B₀ Bv M : ℝ}
    (hLip₀ : ∀ t, LipschitzWith K₀ (fun z => prob.f t z (u₀ t)))
    (hLipv : ∀ t, LipschitzWith Kv (fun z => prob.f t z v))
    (hB₀ : ∀ t, ‖prob.f t 0 (u₀ t)‖ ≤ B₀)
    (hBv : ∀ t, ‖prob.f t 0 v‖ ≤ Bv)
    (hF₀ : Continuous (fun q : ℝ × X => prob.f q.1 q.2 (u₀ q.1)))
    (hFv : Continuous (fun q : ℝ × X => prob.f q.1 q.2 v))
    (hL₀ : Continuous (fun q : ℝ × X => prob.L q.1 q.2 (u₀ q.1)))
    (hLv : Continuous (fun q : ℝ × X => prob.L q.1 q.2 v))
    (hx₀ : IsIntegralCurve x₀ (fun t z => prob.f t z (u₀ t)))
    (hinit : x₀ 0 = x_init)
    (hu₀ : ∀ t ∈ Icc 0 prob.T, u₀ t ∈ prob.controlSet)
    (hv : v ∈ prob.controlSet) (hτ : τ ≤ prob.T)
    (hM : 0 ≤ M)
    (hforcing : ∀ t ∈ Icc 0 prob.T,
      ‖prob.f t (x₀ t) v - prob.f t (x₀ t) (u₀ t)‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (hετ : ε < τ) (hsmall : (Kv : ℝ) * ε ≤ 1 / 2) :
    ∃ x : ℝ → X, ConstructedNeedle prob x_init x₀ u₀ τ v ε x Kv M
      (2 * M * Real.exp ((K₀ : ℝ) * prob.T)) := by
  let a := τ - ε
  have ha : 0 < a := sub_pos.mpr hετ
  have haτ : a ≤ τ := sub_le_self τ hε.le
  have hτ₀ : 0 < τ := hε.trans hετ
  have hT : 0 ≤ prob.T := hτ₀.le.trans hτ
  obtain ⟨x, hx, hbefore, hd, hspike⟩ := exists_spliced_solution
    (fun t z => prob.f t z (u₀ t)) (fun t z => prob.f t z v)
    x₀ hLip₀ hLipv hB₀ hBv hF₀ hFv hx₀ a τ haτ
  have hd' : ∀ t, HasDerivWithinAt x
      (prob.f t (x t) (needleControl u₀ τ v ε t)) (Ici t) t := by
    intro t
    simpa only [needleControl, a, apply_ite, ite_apply] using hd t
  have hfi : ∀ c d, IntervalIntegrable
      (fun t => prob.f t (x t) (needleControl u₀ τ v ε t)) volume c d := by
    intro c d
    have := intervalIntegrable_needle_branches
      (fun t => prob.f t (x t) (u₀ t)) (fun t => prob.f t (x t) v)
      (hF₀.comp (continuous_id.prodMk hx)) (hFv.comp (continuous_id.prodMk hx)) a τ c d
    simpa only [needleControl, a, apply_ite] using this
  have hLi : ∀ c d, IntervalIntegrable
      (fun t => prob.L t (x t) (needleControl u₀ τ v ε t)) volume c d := by
    intro c d
    have := intervalIntegrable_needle_branches
      (fun t => prob.L t (x t) (u₀ t)) (fun t => prob.L t (x t) v)
      (hL₀.comp (continuous_id.prodMk hx)) (hLv.comp (continuous_id.prodMk hx)) a τ c d
    simpa only [needleControl, a, apply_ite] using this
  have hcontrols : ∀ t ∈ Icc 0 prob.T,
      needleControl u₀ τ v ε t ∈ prob.controlSet := by
    intro t ht
    by_cases hmem : t ∈ Ico (τ - ε) τ
    · simpa [needleControl, hmem] using hv
    · simpa [needleControl, hmem] using hu₀ t ht
  have hadm : IsIntegralAdmissiblePair prob x_init x (needleControl u₀ τ v ε) :=
    of_right_derivative prob x_init x (needleControl u₀ τ v ε) hT
      ((hbefore 0 ha.le).trans hinit) hcontrols hx.continuousOn
      (fun t _ => (hd' t).mono Ioi_subset_Ici_self) (hfi 0 prob.T) (hLi 0 prob.T)
  have hstart : x a = x₀ a := hbefore a le_rfl
  have href_integral : ∀ t ∈ Icc a τ,
      x₀ t = x₀ a + ∫ s in a..t, prob.f s (x₀ s) (u₀ s) := by
    intro t _
    have hi : IntervalIntegrable (fun s => prob.f s (x₀ s) (u₀ s)) volume a t :=
      (hF₀.comp (continuous_id.prodMk hx₀.continuous)).intervalIntegrable a t
    have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s (_ : s ∈ uIcc a t) => hx₀ s) hi
    rw [heq]
    abel
  have hdata : NeedleIntervalData x x₀ (fun t z => prob.f t z v)
      (fun t => prob.f t (x₀ t) (u₀ t)) a τ Kv M := {
    perturbed_continuous := hx.continuousOn
    reference_continuous := hx₀.continuous.continuousOn
    initial_eq := hstart
    perturbed_integral_eq := hspike
    reference_integral_eq := href_integral
    perturbed_integrable := (hFv.comp (continuous_id.prodMk hx)).intervalIntegrable a τ
    frozen_integrable := (hFv.comp (continuous_id.prodMk hx₀.continuous)).intervalIntegrable a τ
    reference_integrable := (hF₀.comp (continuous_id.prodMk hx₀.continuous)).intervalIntegrable a τ
    forcing_bound := fun t ht => hforcing t ⟨ha.le.trans ht.1, ht.2.trans hτ⟩
    lipschitz_bound := fun t _ => (hLipv t).norm_sub_le (x t) (x₀ t) }
  have hlength : τ - a = ε := by dsimp [a]; ring
  have hlocal := (needle_displacement_bound_of_integral_eq
    (x := x) (y := x₀) (F := fun t z => prob.f t z v)
    (f₀ := fun t => prob.f t (x₀ t) (u₀ t)) haτ Kv.coe_nonneg hM
    (by simpa only [hlength] using hsmall) hdata.perturbed_continuous
    hdata.reference_continuous hdata.initial_eq hdata.perturbed_integral_eq
    hdata.reference_integral_eq hdata.perturbed_integrable hdata.frozen_integrable
    hdata.reference_integrable hdata.forcing_bound hdata.lipschitz_bound).1
  have hend : ‖x τ - x₀ τ‖ ≤ (2 * M) * ε := by
    simpa only [hlength] using hlocal τ (right_mem_Icc.mpr haτ)
  have hafter : ∀ t ∈ Icc τ prob.T,
      ‖x t - x₀ t‖ ≤ (2 * M * Real.exp ((K₀ : ℝ) * (prob.T - τ))) * ε := by
    apply needle_displacement_bound_after_spike (C := 2 * M) (K := K₀)
      (V := fun t z => prob.f t z (u₀ t)) (tube := fun _ => univ)
      (by positivity) hε.le (fun t _ => (hLip₀ t).lipschitzOnWith) hx.continuousOn
      _ (by simp) hx₀.continuous.continuousOn
      (fun t _ => (hx₀ t).hasDerivWithinAt) (by simp) hend
    intro t ht
    have hn : t ∉ Ico (τ - ε) τ := fun h => (not_lt.mpr ht.1) h.2
    simpa [needleControl, hn] using hd' t
  refine ⟨x, ⟨hx, hbefore, hd', hfi, hLi, hadm, hdata, ?_⟩⟩
  intro t ht
  have hexp : 1 ≤ Real.exp ((K₀ : ℝ) * prob.T) :=
    Real.one_le_exp_iff.mpr (mul_nonneg K₀.coe_nonneg hT)
  by_cases hta : t ≤ a
  · rw [hbefore t hta, sub_self, norm_zero]
    positivity
  · by_cases htτ : t ≤ τ
    · have hlt := hlocal t ⟨(lt_of_not_ge hta).le, htτ⟩
      rw [hlength] at hlt
      exact hlt.trans (by nlinarith [mul_nonneg hM hε.le])
    · have htpost : t ∈ Icc τ prob.T := ⟨(lt_of_not_ge htτ).le, ht.2⟩
      have he : Real.exp ((K₀ : ℝ) * (prob.T - τ)) ≤
          Real.exp ((K₀ : ℝ) * prob.T) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (sub_le_self _ hτ₀.le) K₀.coe_nonneg)
      exact (hafter t htpost).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) hε.le)

/-- An actual family of feasible needle trajectories exists for all sufficiently
small positive widths. The uniform displacement estimate and the first-order
jump are consequences of primitive ODE and continuity hypotheses. -/
theorem exists_feasible_needle_family
    (prob : ContinuousOCP X U) (x_init : X) (x₀ : ℝ → X) (u₀ : ℝ → U)
    (τ : ℝ) (v : U) {K₀ Kv : ℝ≥0} {B₀ Bv M : ℝ}
    (hLip₀ : ∀ t, LipschitzWith K₀ (fun z => prob.f t z (u₀ t)))
    (hLipv : ∀ t, LipschitzWith Kv (fun z => prob.f t z v))
    (hB₀ : ∀ t, ‖prob.f t 0 (u₀ t)‖ ≤ B₀)
    (hBv : ∀ t, ‖prob.f t 0 v‖ ≤ Bv)
    (hF₀ : Continuous (fun q : ℝ × X => prob.f q.1 q.2 (u₀ q.1)))
    (hFv : Continuous (fun q : ℝ × X => prob.f q.1 q.2 v))
    (hL₀ : Continuous (fun q : ℝ × X => prob.L q.1 q.2 (u₀ q.1)))
    (hLv : Continuous (fun q : ℝ × X => prob.L q.1 q.2 v))
    (hx₀ : IsIntegralCurve x₀ (fun t z => prob.f t z (u₀ t)))
    (hinit : x₀ 0 = x_init)
    (hu₀ : ∀ t ∈ Icc 0 prob.T, u₀ t ∈ prob.controlSet)
    (hv : v ∈ prob.controlSet) (hτ₀ : 0 < τ) (hτ : τ ≤ prob.T)
    (hM : 0 ≤ M)
    (hforcing : ∀ t ∈ Icc 0 prob.T,
      ‖prob.f t (x₀ t) v - prob.f t (x₀ t) (u₀ t)‖ ≤ M) :
    ∃ xε : ℝ → ℝ → X,
      (∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ConstructedNeedle prob x_init x₀ u₀ τ v ε (xε ε) Kv M
          (2 * M * Real.exp ((K₀ : ℝ) * prob.T))) ∧
      Tendsto (fun ε : ℝ => ε⁻¹ •
        (xε ε τ - x₀ τ - ε • (prob.f τ (x₀ τ) v - prob.f τ (x₀ τ) (u₀ τ))))
        (𝓝[>] 0) (𝓝 0) := by
  have hex : ∀ ε : ℝ, ∃ x : ℝ → X,
      (0 < ε ∧ ε < τ ∧ (Kv : ℝ) * ε ≤ 1 / 2) →
      ConstructedNeedle prob x_init x₀ u₀ τ v ε x Kv M
        (2 * M * Real.exp ((K₀ : ℝ) * prob.T)) := by
    intro ε
    by_cases hε : 0 < ε ∧ ε < τ ∧ (Kv : ℝ) * ε ≤ 1 / 2
    · obtain ⟨x, hx⟩ := exists_feasible_needle prob x_init x₀ u₀ τ v
        hLip₀ hLipv hB₀ hBv hF₀ hFv hL₀ hLv hx₀ hinit hu₀ hv hτ hM hforcing
        ε hε.1 hε.2.1 hε.2.2
      exact ⟨x, fun _ => hx⟩
    · exact ⟨x₀, fun h => False.elim (hε h)⟩
  choose xε hxε using hex
  have hid : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlinear : Tendsto (fun ε : ℝ => (Kv : ℝ) * ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hid
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (Kv : ℝ) * ε < 1 / 2 :=
    hlinear.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hshort : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < τ :=
    hid.eventually (gt_mem_nhds hτ₀)
  have hfamily : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ConstructedNeedle prob x_init x₀ u₀ τ v ε (xε ε) Kv M
        (2 * M * Real.exp ((K₀ : ℝ) * prob.T)) := by
    filter_upwards [hsmall, hshort, self_mem_nhdsWithin] with ε hsmallε hshortε hposε
    exact hxε ε ⟨hposε, hshortε, hsmallε.le⟩
  refine ⟨xε, hfamily, ?_⟩
  exact needleTrajectoryFirstOrder prob.f x₀ u₀ xε τ v Kv.coe_nonneg hM
    (hfamily.mono fun _ h => h.interval_data)
    (hFv.comp (continuous_id.prodMk hx₀.continuous))
    (hF₀.comp (continuous_id.prodMk hx₀.continuous))

omit [NormedSpace ℝ X] [CompleteSpace X] in
/-- The frozen forcing bound required by the family theorem follows from
continuity and compactness of the actual reference arc. -/
theorem exists_frozen_forcing_bound
    (prob : ContinuousOCP X U) (x₀ : ℝ → X) (u₀ : ℝ → U) (v : U)
    (hx₀ : Continuous x₀)
    (hF₀ : Continuous (fun q : ℝ × X => prob.f q.1 q.2 (u₀ q.1)))
    (hFv : Continuous (fun q : ℝ × X => prob.f q.1 q.2 v)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 prob.T,
      ‖prob.f t (x₀ t) v - prob.f t (x₀ t) (u₀ t)‖ ≤ M := by
  let g : ℝ → X := fun t => prob.f t (x₀ t) v - prob.f t (x₀ t) (u₀ t)
  have hg : Continuous g :=
    (hFv.comp (continuous_id.prodMk hx₀)).sub (hF₀.comp (continuous_id.prodMk hx₀))
  by_cases hT : 0 ≤ prob.T
  · obtain ⟨t, _, hmax⟩ := isCompact_Icc.exists_isMaxOn
      (nonempty_Icc.mpr hT) hg.norm.continuousOn
    exact ⟨‖g t‖, norm_nonneg _, fun s hs => hmax hs⟩
  · refine ⟨0, le_rfl, ?_⟩
    intro t ht
    exact False.elim (hT (ht.1.trans ht.2))

end NeedleIntegralModel
