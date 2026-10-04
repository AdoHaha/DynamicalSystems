import DynamicalSystems.Control.Geometric.SimultaneousRectification

set_option autoImplicit false

open Set
open scoped Topology

section Contract

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [CompleteSpace X] [FiniteDimensional ℝ X]
  {k : ℕ} {f : Fin k → X → X} {x₀ : X}
  (hf : ∀ i, ContDiffAt ℝ 1 (f i) x₀)
  (hind : LinearIndependent ℝ (fun i => f i x₀))
  (hcomm : ∀ i j, FlowsCommuteLocally (f i) (f j) x₀)

-- The exact consumer contract rules out adding an analytic premise to the theorem.
example : SimultaneouslyRectifiable f x₀ := krenerLemma hf hind hcomm

example : simultaneousRectifyingChart hf hind hcomm 0 = x₀ :=
  simultaneousRectifyingChart_zero hf hind hcomm

example : 0 ∈ (simultaneousRectifyingChart hf hind hcomm).source :=
  zero_mem_simultaneousRectifyingChart_source hf hind hcomm

example : ContDiffOn ℝ 1 (simultaneousRectifyingChart hf hind hcomm)
    (simultaneousRectifyingChart hf hind hcomm).source :=
  simultaneousRectifyingChart_contDiffOn hf hind hcomm

example : ContDiffOn ℝ 1 (simultaneousRectifyingChart hf hind hcomm).symm
    (simultaneousRectifyingChart hf hind hcomm).target :=
  simultaneousRectifyingChart_symm_contDiffOn hf hind hcomm

-- Source membership alone suffices; no separate bounds on intermediate flow points.
example (i : Fin k) (p)
    (hp : p ∈ (simultaneousRectifyingChart hf hind hcomm).source) :
    HasDerivAt (fun t => simultaneousRectifyingChart hf hind hcomm
        (Function.update p.1 i t, p.2))
      (f i (simultaneousRectifyingChart hf hind hcomm p)) (p.1 i) :=
  simultaneousRectifyingChart_rectifies hf hind hcomm i p hp

end Contract

-- The empty family does not require a nonsingularity premise or k > 0.
example {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [FiniteDimensional ℝ X] (x₀ : X) :
    SimultaneouslyRectifiable (fun i : Fin 0 => (Fin.elim0 i : X → X)) x₀ := by
  apply krenerLemma
  · intro i
    exact Fin.elim0 i
  · exact linearIndependent_empty_type
  · intro i
    exact Fin.elim0 i

-- Two independent constant fields in three dimensions exercise a nontrivial complement.
example (x₀ : Fin 3 → ℝ) :
    SimultaneouslyRectifiable
      (fun i : Fin 2 => fun _ : Fin 3 → ℝ => Pi.single (Fin.castLE (by decide) i) 1) x₀ := by
  apply krenerLemma
  · intro i
    exact contDiff_const.contDiffAt
  · simpa only [Function.comp_def, Pi.basisFun_apply] using
      (Pi.basisFun ℝ (Fin 3)).linearIndependent.comp
        (Fin.castLE (show 2 ≤ 3 by decide)) (Fin.castLE_injective _)
  · intro i j
    apply flowsCommuteLocally_of_global
    intro x
    simp [lieBracket_apply]

#check @krenerLemma
#check @simultaneousRectifyingChart_rectifies
#check @simultaneousRectifyingChart_contDiffOn
#check @simultaneousRectifyingChart_symm_contDiffOn
