import DynamicalSystems.OptimalControl.ContinuousTime.AdjointPairing
import DynamicalSystems.OptimalControl.ContinuousTime.NeedleCostRemainder
import DynamicalSystems.OptimalControl.ContinuousTime.NeedleVariation

/-!
# The exact cost difference of an actual needle trajectory

The trajectory equations and adjoint equation imply the cost expansion with
explicit nonlinear finite-difference errors. In particular, the Hamiltonian
term is derived by integration and algebra, rather than supplied as a first
variation hypothesis.
-/


open Set Filter MeasureTheory
open scoped Interval Topology

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem intervalIntegrable_indicator_Ico
    {g : ℝ → E} {a b c d : ℝ}
    (hg : IntervalIntegrable g volume c d) :
    IntervalIntegrable ((Ico a b).indicator g) volume c d :=
  ⟨hg.1.indicator measurableSet_Ico, hg.2.indicator measurableSet_Ico⟩

omit [NormedSpace ℝ E] in
theorem intervalIntegrable_ite_Ico
    {g₀ gv : ℝ → E} {a b c d : ℝ}
    (h₀ : IntervalIntegrable g₀ volume c d)
    (hv : IntervalIntegrable gv volume c d) :
    IntervalIntegrable (fun t => if t ∈ Ico a b then gv t else g₀ t) volume c d := by
  have h := h₀.add (intervalIntegrable_indicator_Ico (a := a) (b := b) (hv.sub h₀))
  convert h using 1
  funext t
  by_cases ht : t ∈ Ico a b <;> simp [ht]

theorem integral_indicator_Ico
    {g : ℝ → E} {a b T : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    (∫ t in 0..T, (Ico a b).indicator g t) = ∫ t in a..b, g t := by
  have hT : 0 ≤ T := ha.trans (hab.trans hb)
  have heq : (Ico a b).indicator g =ᵐ[volume] (Ioc a b).indicator g :=
    indicator_ae_eq_of_ae_eq_set Ico_ae_eq_Ioc
  calc
    (∫ t in 0..T, (Ico a b).indicator g t) =
        ∫ t in 0..T, (Ioc a b).indicator g t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [heq] with t ht _
      exact ht
    _ = ∫ t in a..b, g t := by
      rw [intervalIntegral.integral_of_le hT,
        MeasureTheory.integral_indicator measurableSet_Ioc,
        Measure.restrict_restrict measurableSet_Ioc,
        Set.inter_eq_left.mpr (Ioc_subset_Ioc ha hb),
        intervalIntegral.integral_of_le hab]

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The actual nonlinear errors for one perturbed trajectory, in exactly the
form estimated by `_root_.norm_needleCostRemainder_le_quadratic`. -/
noncomputable def _root_.actualNeedleCostRemainder
    (F₀ Fv : ℝ → E → E) (L₀ Lv : ℝ → E → ℝ) (K : E → ℝ)
    (A : ℝ → E →L[ℝ] E) (ell : ℝ → E) (k : E)
    (x y p : ℝ → E) (T τ ε : ℝ) : ℝ :=
  _root_.needleCostRemainder
    (fun _ => taylorError K (InnerProductSpace.toDual ℝ E k) (x T) (y T))
    (fun _ t => taylorError (L₀ t) (InnerProductSpace.toDual ℝ E (ell t)) (x t) (y t))
    (fun _ t => controlIncrementError (Lv t) (L₀ t) (x t) (y t))
    (fun _ t => taylorError (F₀ t) (A t) (x t) (y t))
    (fun _ t => controlIncrementError (Fv t) (F₀ t) (x t) (y t)) p T τ ε

/-- Exact cost expansion from actual nominal and switched trajectory equations.
No Taylor bound or first-order cost formula is a premise of this identity. -/
theorem _root_.cost_difference_eq_impulse_add_actualNeedleCostRemainder
    (F₀ Fv : ℝ → E → E) (L₀ Lv : ℝ → E → ℝ) (K : E → ℝ)
    (A : ℝ → E →L[ℝ] E) (ell : ℝ → E) (k : E)
    (x y p : ℝ → E) (T τ ε : ℝ)
    (hε : 0 ≤ ε) (ha : 0 ≤ τ - ε) (hτ : τ ≤ T)
    (hF₀ : Continuous (fun z : ℝ × E => F₀ z.1 z.2))
    (hFv : Continuous (fun z : ℝ × E => Fv z.1 z.2))
    (hL₀ : Continuous (fun z : ℝ × E => L₀ z.1 z.2))
    (hLv : Continuous (fun z : ℝ × E => Lv z.1 z.2))
    (hxc : Continuous x) (hyc : Continuous y) (hpc : Continuous p)
    (hAc : ContinuousOn A (Icc 0 T)) (hellc : ContinuousOn ell (Icc 0 T))
    (hstart : y 0 = x 0) (hpT : p T = k)
    (hx : ∀ t ∈ Ioo 0 T, HasDerivWithinAt x (F₀ t (x t)) (Ioi t) t)
    (hy : ∀ t ∈ Ioo 0 T, HasDerivWithinAt y
      (if t ∈ Ico (τ - ε) τ then Fv t (y t) else F₀ t (y t)) (Ioi t) t)
    (hp : ∀ t ∈ Ioo 0 T,
      HasDerivWithinAt p (-(A t).adjoint (p t) - ell t) (Ioi t) t) :
    ((∫ t in 0..T, if t ∈ Ico (τ - ε) τ then Lv t (y t) else L₀ t (y t)) + K (y T)) -
        ((∫ t in 0..T, L₀ t (x t)) + K (x T)) =
      (∫ t in (τ - ε)..τ,
        (Lv t (x t) - L₀ t (x t)) + inner ℝ (p t) (Fv t (x t) - F₀ t (x t))) +
      _root_.actualNeedleCostRemainder F₀ Fv L₀ Lv K A ell k x y p T τ ε := by
  have hab : τ - ε ≤ τ := sub_le_self τ hε
  have hT : 0 ≤ T := ha.trans (hab.trans hτ)
  let S := Ico (τ - ε) τ
  let d : ℝ → E := fun t => y t - x t
  let b₀ : ℝ → E := fun t => F₀ t (y t) - F₀ t (x t) - A t (d t)
  let bv : ℝ → E := fun t => Fv t (y t) - F₀ t (x t) - A t (d t)
  let b : ℝ → E := fun t => if t ∈ S then bv t else b₀ t
  let c₀ : ℝ → ℝ := fun t => L₀ t (y t) - L₀ t (x t) - inner ℝ (ell t) (d t)
  let cv : ℝ → ℝ := fun t => Lv t (y t) - L₀ t (x t) - inner ℝ (ell t) (d t)
  let c : ℝ → ℝ := fun t => if t ∈ S then cv t else c₀ t
  let n : ℝ → ℝ := fun t => c₀ t + inner ℝ (p t) (b₀ t)
  let j : ℝ → ℝ := fun t => Lv t (x t) - L₀ t (x t) +
    inner ℝ (p t) (Fv t (x t) - F₀ t (x t))
  let q : ℝ → ℝ := fun t => controlIncrementError (Lv t) (L₀ t) (x t) (y t) +
    inner ℝ (p t) (controlIncrementError (Fv t) (F₀ t) (x t) (y t))
  have hdc : Continuous d := hyc.sub hxc
  have hf₀y : Continuous (fun t => F₀ t (y t)) := hF₀.comp (continuous_id.prodMk hyc)
  have hf₀x : Continuous (fun t => F₀ t (x t)) := hF₀.comp (continuous_id.prodMk hxc)
  have hfvy : Continuous (fun t => Fv t (y t)) := hFv.comp (continuous_id.prodMk hyc)
  have hfvx : Continuous (fun t => Fv t (x t)) := hFv.comp (continuous_id.prodMk hxc)
  have hl₀y : Continuous (fun t => L₀ t (y t)) := hL₀.comp (continuous_id.prodMk hyc)
  have hl₀x : Continuous (fun t => L₀ t (x t)) := hL₀.comp (continuous_id.prodMk hxc)
  have hlvy : Continuous (fun t => Lv t (y t)) := hLv.comp (continuous_id.prodMk hyc)
  have hlvx : Continuous (fun t => Lv t (x t)) := hLv.comp (continuous_id.prodMk hxc)
  have hb₀c : ContinuousOn b₀ (Icc 0 T) :=
    (hf₀y.sub hf₀x).continuousOn.sub (hAc.clm_apply hdc.continuousOn)
  have hbvc : ContinuousOn bv (Icc 0 T) :=
    (hfvy.sub hf₀x).continuousOn.sub (hAc.clm_apply hdc.continuousOn)
  have hc₀c : ContinuousOn c₀ (Icc 0 T) :=
    (hl₀y.sub hl₀x).continuousOn.sub (hellc.inner hdc.continuousOn)
  have hcvc : ContinuousOn cv (Icc 0 T) :=
    (hlvy.sub hl₀x).continuousOn.sub (hellc.inner hdc.continuousOn)
  have hbi : IntervalIntegrable (fun t => inner ℝ (p t) (b t)) volume 0 T := by
    have hb₀pc : ContinuousOn (fun t => inner ℝ (p t) (b₀ t)) (Icc 0 T) :=
      hpc.continuousOn.inner hb₀c
    have hbvpc : ContinuousOn (fun t => inner ℝ (p t) (bv t)) (Icc 0 T) :=
      hpc.continuousOn.inner hbvc
    have h := intervalIntegrable_ite_Ico
      (hb₀pc.intervalIntegrable_of_Icc hT)
      (hbvpc.intervalIntegrable_of_Icc hT)
      (a := τ - ε) (b := τ)
    convert h using 1
    funext t
    dsimp [b, S]
    split_ifs <;> rfl
  have hci : IntervalIntegrable c volume 0 T :=
    intervalIntegrable_ite_Ico (hc₀c.intervalIntegrable_of_Icc hT)
      (hcvc.intervalIntegrable_of_Icc hT)
  have hli : IntervalIntegrable (fun t => inner ℝ (ell t) (d t)) volume 0 T :=
    (hellc.inner hdc.continuousOn).intervalIntegrable_of_Icc hT
  have hd : ∀ t ∈ Ioo 0 T,
      HasDerivWithinAt d (A t (d t) + b t) (Ioi t) t := by
    intro t ht
    have h := (hy t ht).sub (hx t ht)
    convert h using 1
    dsimp [b, b₀, bv, S]
    split_ifs <;> abel
  have hpair := integral_adjoint_pairing_with_running_term hT hpc.continuousOn
    hdc.continuousOn hp hd hbi hli hci
  have hn : ContinuousOn n (Icc 0 T) := hc₀c.add (hpc.continuousOn.inner hb₀c)
  have hj : Continuous j := (hlvx.sub hl₀x).add (hpc.inner (hfvx.sub hf₀x))
  have hq : Continuous q := ((hlvy.sub hlvx).sub (hl₀y.sub hl₀x)).add
    (hpc.inner ((hfvy.sub hfvx).sub (hf₀y.sub hf₀x)))
  have halgebra : ∀ t, c t + inner ℝ (p t) (b t) = n t + S.indicator (fun s => j s + q s) t := by
    intro t
    by_cases ht : t ∈ S
    · simp only [c, b, ite_eq_left ht, indicator_of_mem ht, n, c₀, cv, b₀, bv, j, q,
        controlIncrementError, inner_sub_right]
      ring
    · simp [c, b, ht, n]
  have hRHS : (∫ t in 0..T, c t + inner ℝ (p t) (b t)) =
      (∫ t in 0..T, n t) + (∫ t in (τ - ε)..τ, j t) +
        ∫ t in (τ - ε)..τ, q t := by
    simp_rw [halgebra]
    dsimp only [S]
    rw [intervalIntegral.integral_add (hn.intervalIntegrable_of_Icc hT)
      (intervalIntegrable_indicator_Ico (a := τ - ε) (b := τ)
        ((show Continuous (fun t => j t + q t) from hj.add hq).intervalIntegrable 0 T)),
      integral_indicator_Ico ha hab hτ,
      intervalIntegral.integral_add (hj.intervalIntegrable _ _) (hq.intervalIntegrable _ _)]
    ring
  have hactual : IntervalIntegrable
      (fun t => if t ∈ S then Lv t (y t) else L₀ t (y t)) volume 0 T :=
    intervalIntegrable_ite_Ico (hl₀y.intervalIntegrable _ _) (hlvy.intervalIntegrable _ _)
  have hLHS : (∫ t in 0..T, inner ℝ (ell t) (d t) + c t) =
      (∫ t in 0..T, if t ∈ S then Lv t (y t) else L₀ t (y t)) -
        ∫ t in 0..T, L₀ t (x t) := by
    rw [← intervalIntegral.integral_sub hactual (hl₀x.intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp [c, c₀, cv]
    split_ifs <;> ring
  rw [hLHS, hRHS] at hpair
  have hd₀ : d 0 = 0 := by simp [d, hstart]
  rw [hd₀, inner_zero_right, hpT] at hpair
  have hrem : _root_.actualNeedleCostRemainder F₀ Fv L₀ Lv K A ell k x y p T τ ε =
      (K (y T) - K (x T) - inner ℝ k (d T)) +
        (∫ t in 0..T, n t) + ∫ t in (τ - ε)..τ, q t := by
    rfl
  rw [hrem]
  change _ = (∫ t in (τ - ε)..τ, j t) + _
  change (∫ t in 0..T, if t ∈ S then Lv t (y t) else L₀ t (y t)) + K (y T) -
    ((∫ t in 0..T, L₀ t (x t)) + K (x T)) = _
  linarith

end InnerProduct

