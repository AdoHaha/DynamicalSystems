import DynamicalSystems.Control.Geometric.FrobeniusIntegrability

set_option autoImplicit false

open Set
open scoped Topology ContDiff

-- The entire recorded proposition, including its internal completeness and dimension binders.
example {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] :
    frobeniusTheorem (X := X) (Y := Y) :=
  frobeniusTheorem_holds

section Contract

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [CompleteSpace X] [CompleteSpace Y]
  [FiniteDimensional ℝ X] [FiniteDimensional ℝ Y]

-- Strong open-domain contract, with actual derivatives throughout the domain.
example (g : X × Y → X →L[ℝ] Y) (hg : ContDiff ℝ ∞ g)
    (hc : TotalFderivCompat g univ) (x₀ : X) (z : Y) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ ∃ w : X → Y,
      ContDiffOn ℝ ∞ w U ∧ w x₀ = z ∧
        ∀ x ∈ U, HasFDerivAt w (g (x, w x)) x :=
  exists_sol_of_fderiv_compat g hg hc x₀ z

-- Exact original conclusion, including the within derivative and interior.
example (g : X × Y → X →L[ℝ] Y) (hg : ContDiff ℝ ∞ g)
    (hc : TotalFderivCompat g univ) (x₀ : X) (z : Y) :
    ∃ (s : Set X) (_ : s ∈ 𝓝 x₀) (w : X → Y),
      ContDiffOn ℝ ∞ w (interior s) ∧ w x₀ = z ∧
        ∀ x ∈ s, fderivWithin ℝ w (interior s) x = g (x, w x) :=
  frobeniusTheorem_holds g hg hc x₀ z

-- A nonzero constant connection is compatible in every finite dimension.
example (A : X →L[ℝ] Y) (x₀ : X) (z : Y) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ ∃ w : X → Y,
      ContDiffOn ℝ ∞ w U ∧ w x₀ = z ∧
        ∀ x ∈ U, HasFDerivAt w A x := by
  exact exists_sol_of_fderiv_compat (fun _ => A) contDiff_const
    (by intro p _ d₁ d₂; simp [Curvature]) x₀ z

end Contract

-- The zero-dimensional base is included in the same theorem.
example (z : ℝ) :
    ∃ U : Set (Fin 0 → ℝ), IsOpen U ∧ (0 : Fin 0 → ℝ) ∈ U ∧
      ∃ w : (Fin 0 → ℝ) → ℝ, ContDiffOn ℝ ∞ w U ∧ w 0 = z ∧
        ∀ x ∈ U, HasFDerivAt w (0 : (Fin 0 → ℝ) →L[ℝ] ℝ) x := by
  exact exists_sol_of_fderiv_compat (fun _ => 0) contDiff_const
    (by intro p _ d₁ d₂; simp [Curvature]) 0 z

#check @exists_local_solution_of_totalFderivCompat
#check @exists_sol_of_fderiv_compat
#check @frobeniusTheorem_holds
