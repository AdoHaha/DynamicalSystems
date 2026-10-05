import DynamicalSystems.OptimalControl.ContinuousTime.OptimalityGeometry
import DynamicalSystems.OptimalControl.ContinuousTime.AugmentedCostate
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Exact Bolza-to-Mayer augmentation for integral competitors

The augmented state is `(z,x)` with `z' = L(t,x,u)` and zero running cost.
Projection maps every integral-admissible augmented competitor to an original
competitor with exactly the same total cost. Conversely, accumulating the actual
running integral lifts every original integral-admissible competitor. Therefore
original integral optimality implies augmented integral optimality.
-/


open Set Filter MeasureTheory
open scoped Interval Topology

variable {X U : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The Mayer problem obtained by adjoining actual accumulated running cost. -/
def _root_.ContinuousOCP.bolzaToMayer (prob : ContinuousOCP X U) : ContinuousOCP (ℝ × X) U where
  T := prob.T
  f t y v := (prob.L t y.2 v, prob.f t y.2 v)
  L _ _ _ := 0
  K := _root_.bolzaTerminalCost prob.K
  controlSet := prob.controlSet

/-- Lift a trajectory by accumulating its actual running cost from time zero. -/
noncomputable def _root_.bolzaCostLift (prob : ContinuousOCP X U) (x : ℝ → X) (u : ℝ → U)
    (t : ℝ) : ℝ × X := (∫ s in 0..t, prob.L s (x s) (u s), x t)

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] in
@[simp]
theorem _root_.bolzaCostLift_terminal (prob : ContinuousOCP X U) (x : ℝ → X) (u : ℝ → U) :
    _root_.bolzaCostLift prob x u prob.T = costAugmentedEndpoint prob x u := rfl

omit [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] in
@[simp]
theorem _root_.bolzaCostLift_totalCost (prob : ContinuousOCP X U) (x : ℝ → X) (u : ℝ → U) :
    continuousTotalCost (_root_.ContinuousOCP.bolzaToMayer prob) (_root_.bolzaCostLift prob x u) u =
      continuousTotalCost prob x u := by
  simp [continuousTotalCost, _root_.ContinuousOCP.bolzaToMayer, _root_.bolzaTerminalCost, _root_.bolzaCostLift]

omit [NormedSpace ℝ X] [CompleteSpace X] in
/-- Interval integrability of vector pairs from the two primitive components. -/
theorem intervalIntegrable_pair {f : ℝ → ℝ} {g : ℝ → X} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b) :
    IntervalIntegrable (fun t => (f t, g t)) volume a b :=
  ⟨hf.1.prodMk hg.1, hf.2.prodMk hg.2⟩

/-- Every original integral-admissible trajectory has a genuinely admissible
cost lift in the augmented Mayer problem. -/
theorem _root_.integralAdmissible_bolzaCostLift
    (prob : ContinuousOCP X U) (x₀ : X) (x : ℝ → X) (u : ℝ → U)
    (hT : 0 ≤ prob.T)
    (hadm : NeedleIntegralModel.IsIntegralAdmissiblePair prob x₀ x u) :
    NeedleIntegralModel.IsIntegralAdmissiblePair
      (_root_.ContinuousOCP.bolzaToMayer prob) (0, x₀) (_root_.bolzaCostLift prob x u) u := by
  rcases hadm with ⟨hinit, hctrl, hfi, hint, hLi⟩
  have hpair := intervalIntegrable_pair hLi hfi
  refine ⟨?_, hctrl, hpair, ?_, ?_⟩
  · simp [_root_.bolzaCostLift, hinit]
  · intro t ht
    have ht' : t ∈ Icc 0 prob.T := ht
    have hsub : uIcc 0 t ⊆ uIcc 0 prob.T := by
      simpa only [uIcc_of_le ht'.1, uIcc_of_le hT] using
        (Icc_subset_Icc le_rfl ht'.2 : Icc (0 : ℝ) t ⊆ Icc 0 prob.T)
    have hpi := hpair.mono_set hsub
    have hz := (ContinuousLinearMap.fst ℝ ℝ X).intervalIntegral_comp_comm hpi
    have hx := (ContinuousLinearMap.snd ℝ ℝ X).intervalIntegral_comp_comm hpi
    change (∫ s in 0..t, prob.L s (x s) (u s)) =
      (∫ s in 0..t, (prob.L s (x s) (u s), prob.f s (x s) (u s))).1 at hz
    change (∫ s in 0..t, prob.f s (x s) (u s)) =
      (∫ s in 0..t, (prob.L s (x s) (u s), prob.f s (x s) (u s))).2 at hx
    apply Prod.ext
    · change (∫ s in 0..t, prob.L s (x s) (u s)) =
        0 + (∫ s in 0..t, (prob.L s (x s) (u s), prob.f s (x s) (u s))).1
      simpa only [zero_add] using hz
    · change x t = x₀ +
        (∫ s in 0..t, (prob.L s (x s) (u s), prob.f s (x s) (u s))).2
      rw [← hx]
      exact hint t ht'
  · exact intervalIntegrable_const

/-- Projection of any admissible augmented competitor is admissible for the
original problem. Its cost coordinate supplies the original running integrability. -/
theorem integralAdmissible_of_augmented
    (prob : ContinuousOCP X U) (x₀ : X) (y : ℝ → ℝ × X) (u : ℝ → U)
    (hT : 0 ≤ prob.T)
    (hadm : NeedleIntegralModel.IsIntegralAdmissiblePair
      (_root_.ContinuousOCP.bolzaToMayer prob) (0, x₀) y u) :
    NeedleIntegralModel.IsIntegralAdmissiblePair prob x₀ (fun t => (y t).2) u := by
  rcases hadm with ⟨hinit, hctrl, hfi, hint, _hLi⟩
  have hstate : IntervalIntegrable (fun t => prob.f t (y t).2 (u t)) volume 0 prob.T :=
    ⟨hfi.1.snd, hfi.2.snd⟩
  have hcost : IntervalIntegrable (fun t => prob.L t (y t).2 (u t)) volume 0 prob.T :=
    ⟨hfi.1.fst, hfi.2.fst⟩
  refine ⟨congrArg Prod.snd hinit, hctrl, hstate, ?_, hcost⟩
  intro t ht
  have hsub : uIcc 0 t ⊆ uIcc 0 prob.T := by
    simpa only [uIcc_of_le ht.1, uIcc_of_le hT] using
      (Icc_subset_Icc le_rfl ht.2 : Icc (0 : ℝ) t ⊆ Icc 0 prob.T)
  have hpi := hfi.mono_set hsub
  have hx := (ContinuousLinearMap.snd ℝ ℝ X).intervalIntegral_comp_comm hpi
  change (∫ s in 0..t, prob.f s (y s).2 (u s)) =
    (∫ s in 0..t, (prob.L s (y s).2 (u s), prob.f s (y s).2 (u s))).2 at hx
  have heq := congrArg Prod.snd (hint t ht)
  change (y t).2 = x₀ +
    (∫ s in 0..t, (prob.L s (y s).2 (u s), prob.f s (y s).2 (u s))).2 at heq
  rw [← hx] at heq
  exact heq

/-- The augmented dynamics force the terminal cost coordinate to be the actual
running integral. The augmented and original total costs are exactly equal. -/
theorem augmented_totalCost_eq_of_admissible
    (prob : ContinuousOCP X U) (x₀ : X) (y : ℝ → ℝ × X) (u : ℝ → U)
    (hT : 0 ≤ prob.T)
    (hadm : NeedleIntegralModel.IsIntegralAdmissiblePair
      (_root_.ContinuousOCP.bolzaToMayer prob) (0, x₀) y u) :
    continuousTotalCost (_root_.ContinuousOCP.bolzaToMayer prob) y u =
      continuousTotalCost prob (fun t => (y t).2) u := by
  have hz := (ContinuousLinearMap.fst ℝ ℝ X).intervalIntegral_comp_comm hadm.2.2.1
  change (∫ s in 0..prob.T, prob.L s (y s).2 (u s)) =
    (∫ s in 0..prob.T, (prob.L s (y s).2 (u s), prob.f s (y s).2 (u s))).1 at hz
  have heq := congrArg Prod.fst (hadm.2.2.2.1 prob.T ⟨hT, le_rfl⟩)
  change (y prob.T).1 = 0 +
    (∫ s in 0..prob.T, (prob.L s (y s).2 (u s), prob.f s (y s).2 (u s))).1 at heq
  rw [zero_add, ← hz] at heq
  simp [continuousTotalCost, _root_.ContinuousOCP.bolzaToMayer, _root_.bolzaTerminalCost, heq]

/-- Integral optimality transfers to the augmented Mayer problem by comparing
with every augmented competitor through its original admissible projection. -/
theorem _root_.integralOptimal_bolzaCostLift
    (prob : ContinuousOCP X U) (x₀ : X) (x : ℝ → X) (u : ℝ → U)
    (hT : 0 ≤ prob.T)
    (hopt : NeedleIntegralModel.IsIntegralOptimalPair prob x₀ x u) :
    NeedleIntegralModel.IsIntegralOptimalPair
      (_root_.ContinuousOCP.bolzaToMayer prob) (0, x₀) (_root_.bolzaCostLift prob x u) u := by
  refine ⟨_root_.integralAdmissible_bolzaCostLift prob x₀ x u hT hopt.1, ?_⟩
  intro y v hy
  rw [_root_.bolzaCostLift_totalCost, augmented_totalCost_eq_of_admissible prob x₀ y v hT hy]
  exact hopt.2 (fun t => (y t).2) v
    (integralAdmissible_of_augmented prob x₀ y v hT hy)

/-- The actual augmented endpoint of a projected competitor equals its terminal
augmented state. This identifies the tangent produced by the ODE sensitivity
theorem with the cost/state endpoint tangent used by geometric separation. -/
theorem costAugmentedEndpoint_eq_terminal_of_admissible
    (prob : ContinuousOCP X U) (x₀ : X) (y : ℝ → ℝ × X) (u : ℝ → U)
    (hT : 0 ≤ prob.T)
    (hadm : NeedleIntegralModel.IsIntegralAdmissiblePair
      (_root_.ContinuousOCP.bolzaToMayer prob) (0, x₀) y u) :
    costAugmentedEndpoint prob (fun t => (y t).2) u = y prob.T := by
  have hz := (ContinuousLinearMap.fst ℝ ℝ X).intervalIntegral_comp_comm hadm.2.2.1
  change (∫ s in 0..prob.T, prob.L s (y s).2 (u s)) =
    (∫ s in 0..prob.T, (prob.L s (y s).2 (u s), prob.f s (y s).2 (u s))).1 at hz
  have heq := congrArg Prod.fst (hadm.2.2.2.1 prob.T ⟨hT, le_rfl⟩)
  change (y prob.T).1 = 0 +
    (∫ s in 0..prob.T, (prob.L s (y s).2 (u s), prob.f s (y s).2 (u s))).1 at heq
  rw [zero_add, ← hz] at heq
  exact Prod.ext heq.symm rfl

omit [CompleteSpace X] in
/-- A classical nominal solution lifts to a classical nominal augmented solution
when the actual running-cost trajectory is continuous. -/
theorem _root_.isIntegralCurve_bolzaCostLift
    (prob : ContinuousOCP X U) (x : ℝ → X) (u : ℝ → U)
    (hx : IsIntegralCurve x (fun t z => prob.f t z (u t)))
    (hL : Continuous (fun q : ℝ × X => prob.L q.1 q.2 (u q.1))) :
    IsIntegralCurve (_root_.bolzaCostLift prob x u)
      (fun t y => (_root_.ContinuousOCP.bolzaToMayer prob).f t y (u t)) := by
  have hc : Continuous (fun t => prob.L t (x t) (u t)) :=
    hL.comp (continuous_id.prodMk hx.continuous)
  intro t
  exact (hc.integral_hasStrictDerivAt 0 t).hasDerivAt.prodMk (hx t)

omit [CompleteSpace X] in
/-- The actual spatial derivatives of `L` and `f` give the augmented derivative. -/
theorem hasFDerivAt_augmented_dynamics
    (prob : ContinuousOCP X U) (t : ℝ) (v : U) (y : ℝ × X)
    (DL : X →L[ℝ] ℝ) (Df : X →L[ℝ] X)
    (hL : HasFDerivAt (fun z => prob.L t z v) DL y.2)
    (hf : HasFDerivAt (fun z => prob.f t z v) Df y.2) :
    HasFDerivAt (fun z => (_root_.ContinuousOCP.bolzaToMayer prob).f t z v)
      (augmentedLinearCoefficient DL Df) y :=
  (hL.comp y (ContinuousLinearMap.snd ℝ ℝ X).hasFDerivAt).prodMk
    (hf.comp y (ContinuousLinearMap.snd ℝ ℝ X).hasFDerivAt)

omit [CompleteSpace X] in
/-- Continuity of actual spatial derivatives at a physical reference point
passes to the augmented derivative at every value of the cost coordinate. -/
theorem continuousAt_augmented_spatial_derivative
    (DL : ℝ → X → X →L[ℝ] ℝ) (Df : ℝ → X → X →L[ℝ] X)
    (t : ℝ) (y : ℝ × X)
    (hL : ContinuousAt (fun q : ℝ × X => DL q.1 q.2) (t, y.2))
    (hf : ContinuousAt (fun q : ℝ × X => Df q.1 q.2) (t, y.2)) :
    ContinuousAt (fun q : ℝ × (ℝ × X) =>
      augmentedLinearCoefficient (DL q.1 q.2.2) (Df q.1 q.2.2)) (t, y) := by
  have hproj : Continuous (fun q : ℝ × (ℝ × X) => (q.1, q.2.2)) :=
    continuous_fst.prodMk (continuous_snd.snd)
  have hLc := hL.comp_of_eq (hproj.continuousAt (x := (t, y))) rfl
  have hfc := hf.comp_of_eq (hproj.continuousAt (x := (t, y))) rfl
  exact (ContinuousLinearMap.prodL ℝ).continuousAt.comp
    ((hLc.clm_comp continuousAt_const).prodMk (hfc.clm_comp continuousAt_const))

