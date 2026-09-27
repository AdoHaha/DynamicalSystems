/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.DynamicFeedback

@[expose] public section

/-! # Real-coordinate finite-Bohl transport

The finite-Bohl necessity direction of Trentelman–Stoorvogel–Hautus Theorem 4.37
is transported from complex coordinate space to arbitrary finite-dimensional
real state and input spaces. The public result is `LinearSystem.finiteBohlWBridge_real`.
-/

open Filter Topology Set
open scoped Topology Matrix

namespace LinearSystem

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

/-- The canonical real coordinate equivalence `X ≃L[ℝ] (Fin (finrank ℝ X) → ℝ)`. -/
noncomputable def realCoordEquiv :
    X ≃L[ℝ] (Fin (Module.finrank ℝ X) → ℝ) :=
  (Module.finBasis ℝ X).equivFun.toContinuousLinearEquiv

@[simp]
theorem realCoordEquiv_apply (x : X) :
    realCoordEquiv x = (Module.finBasis ℝ X).equivFun x := rfl

/-- The coordinate complexification inclusion `Ψ : X → (Fin n → ℂ)`. -/
noncomputable def coordComplexify :
    X →ₗ[ℝ] (Fin (Module.finrank ℝ X) → ℂ) :=
  LinearMap.ofRealPi.comp realCoordEquiv.toLinearMap

/-- The coordinate real-part projection `rePi : (Fin n → ℂ) → (Fin n → ℝ)`. -/
noncomputable def rePi :
    (Fin (Module.finrank ℝ X) → ℂ) →ₗ[ℝ] (Fin (Module.finrank ℝ X) → ℝ) where
  toFun z i := (z i).re
  map_add' z w := by ext i; simp
  map_smul' r z := by ext i; simp

/-- The real-linear projection `R : (Fin n → ℂ) → X` complementary to `Ψ`. -/
noncomputable def coordRealify :
    (Fin (Module.finrank ℝ X) → ℂ) →ₗ[ℝ] X :=
  realCoordEquiv.symm.toLinearMap.comp rePi

/-- The continuous-linear-map form of `coordRealify` (finite-dimensional domain). -/
noncomputable def coordRealifyCLM :
    (Fin (Module.finrank ℝ X) → ℂ) →L[ℝ] X :=
  LinearMap.toContinuousLinearMap coordRealify

@[simp]
theorem coordRealify_coordComplexify (x : X) :
    coordRealify (coordComplexify x) = x := by
  simp only [coordRealify, LinearMap.comp_apply, rePi, coordComplexify]
  exact realCoordEquiv.symm_apply_apply x

/-- The complexified coordinate generator. -/
noncomputable def coordComplexA (A : X →ₗ[ℝ] X) :
    (Fin (Module.finrank ℝ X) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℝ X) → ℂ) :=
  Matrix.toLin' ((LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ X) A).map
    (algebraMap ℝ ℂ))

/-- `Ψ` intertwines `A` with its complexified coordinate form. -/
theorem coordComplexify_comp (A : X →ₗ[ℝ] X) :
    (coordComplexA A).restrictScalars ℝ ∘ₗ coordComplexify = coordComplexify ∘ₗ A := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  show coordComplexA A (coordComplexify x) = coordComplexify (A x)
  let M := LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ X) A
  have hMv : M *ᵥ (Module.finBasis ℝ X).equivFun x =
      (Module.finBasis ℝ X).equivFun (A x) := by
    rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
    exact LinearMap.toMatrix_mulVec_repr (Module.finBasis ℝ X) (Module.finBasis ℝ X) A x
  change (coordComplexA A) (LinearMap.ofRealPi ((Module.finBasis ℝ X).equivFun x)) =
    LinearMap.ofRealPi ((Module.finBasis ℝ X).equivFun (A x))
  rw [← hMv]
  change (Matrix.toLin' (M.map (algebraMap ℝ ℂ)))
      (LinearMap.ofRealPi ((Module.finBasis ℝ X).equivFun x)) =
    LinearMap.ofRealPi (M *ᵥ (Module.finBasis ℝ X).equivFun x)
  rw [Matrix.toLin'_apply]
  funext i
  exact (RingHom.map_mulVec (algebraMap ℝ ℂ) M
    ((Module.finBasis ℝ X).equivFun x) i).symm

/-- The inverse coordinate equivalence intertwines the real matrix action.
This is `LinearMap.toMatrix_mulVec_repr` read backwards. -/
theorem realCoordEquiv_symm_mulVec (A : X →ₗ[ℝ] X)
    (y : Fin (Module.finrank ℝ X) → ℝ) :
    realCoordEquiv.symm
        ((LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ X) A) *ᵥ y) =
      A (realCoordEquiv.symm y) := by
  apply realCoordEquiv.injective
  rw [realCoordEquiv.apply_symm_apply]
  have hrepr : (LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ X) A) *ᵥ
        (Module.finBasis ℝ X).equivFun (realCoordEquiv.symm y) =
      (Module.finBasis ℝ X).equivFun (A (realCoordEquiv.symm y)) :=
    LinearMap.toMatrix_mulVec_repr (Module.finBasis ℝ X) (Module.finBasis ℝ X) A
      (realCoordEquiv.symm y)
  have hy : (Module.finBasis ℝ X).equivFun (realCoordEquiv.symm y) = y := by
    change (Module.finBasis ℝ X).equivFun
      ((Module.finBasis ℝ X).equivFun.symm y) = y
    exact (Module.finBasis ℝ X).equivFun.apply_symm_apply y
  rw [hy] at hrepr
  rw [hrepr]
  rfl

/-- Real-part projection of a complexified real matrix-vector product. -/
theorem rePi_map_mulVec (M : Matrix (Fin (Module.finrank ℝ X)) (Fin (Module.finrank ℝ X)) ℝ)
    (z : Fin (Module.finrank ℝ X) → ℂ) :
    rePi ((M.map (algebraMap ℝ ℂ)) *ᵥ z) = M *ᵥ rePi z := by
  funext i
  change (((M.map (algebraMap ℝ ℂ)) *ᵥ z) i).re = (M *ᵥ (fun j => (z j).re)) i
  simp only [Matrix.mulVec, dotProduct]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.mul_re]
  simp

/-- `rePi` intertwines the complexified coordinate generator with the real
coordinate action. -/
theorem rePi_comp_coordComplexA (A : X →ₗ[ℝ] X) :
    rePi.comp ((coordComplexA A).restrictScalars ℝ) =
      (Matrix.toLin' (LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ X) A)).comp
        rePi := by
  apply LinearMap.ext
  intro z
  show rePi ((coordComplexA A) z) =
    (Matrix.toLin' (LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ X) A)) (rePi z)
  change rePi ((Matrix.toLin' ((LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ X) A).map
      (algebraMap ℝ ℂ))) z) = _
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
  exact rePi_map_mulVec (LinearMap.toMatrix (Module.finBasis ℝ X) (Module.finBasis ℝ X) A) z

/-- `R` intertwines the complexified coordinate generator with `A`. -/
theorem coordRealify_comp_coordComplexA (A : X →ₗ[ℝ] X) :
    coordRealify.comp ((coordComplexA A).restrictScalars ℝ) = A.comp coordRealify := by
  apply LinearMap.ext
  intro z
  show coordRealify ((coordComplexA A) z) = A (coordRealify z)
  change realCoordEquiv.symm (rePi (((coordComplexA A).restrictScalars ℝ) z)) =
    A (realCoordEquiv.symm (rePi z))
  have h := congrFun (congrArg DFunLike.coe (rePi_comp_coordComplexA A)) z
  simp only [LinearMap.comp_apply] at h
  rw [h, Matrix.toLin'_apply]
  exact realCoordEquiv_symm_mulVec A (rePi z)

variable {U Z : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- The coordinate complexification of a real system: state space
`Fin (finrank ℝ X) → ℂ`, state map the complexified coordinate matrix, input map
`Ψ ∘ B`, zero readout. -/
noncomputable def coordSystem (sys : LinearSystem ℝ X U Z) :
    LinearSystem ℝ (Fin (Module.finrank ℝ X) → ℂ) U Z where
  A := (coordComplexA sys.A).restrictScalars ℝ
  B := coordComplexify.comp sys.B
  C := 0
  D := 0

@[simp]
theorem coordSystem_A (sys : LinearSystem ℝ X U Z) :
    (coordSystem sys).A = (coordComplexA sys.A).restrictScalars ℝ := rfl

@[simp]
theorem coordSystem_B (sys : LinearSystem ℝ X U Z) :
    (coordSystem sys).B = coordComplexify.comp sys.B := rfl

/-- A real finite Bohl signal is one whose coordinate complexification is a
complex finite exponential polynomial. -/
def IsRealBohl (f : ℝ → X) : Prop :=
  IsExponentialPolynomial (fun t => coordComplexify (f t))

/-- The coordinate complexification of a real variation-of-constants trajectory
is the variation-of-constants trajectory of the coordinate system. -/
theorem coordSystem_variationOfConstants (sys : LinearSystem ℝ X U Z) (x₀ : X)
    (u : ℝ → U) (hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume) :
    (fun t : ℝ => coordComplexify (sys.variationOfConstants 0 x₀ u t)) =
      (coordSystem sys).variationOfConstants 0 (coordComplexify x₀) u := by
  let Ψc : X →L[ℝ] (Fin (Module.finrank ℝ X) → ℂ) :=
    coordComplexify.toContinuousLinearMap
  let x : ℝ → X := sys.variationOfConstants 0 x₀ u
  have hx_cont : Continuous (fun t : ℝ => coordComplexify (x t)) :=
    Ψc.continuous.comp (continuous_variationOfConstants sys 0 x₀ u hu)
  have hx0 : coordComplexify (x 0) = coordComplexify x₀ := by
    simp [x, variationOfConstants]
  have hdyn : ∀ t : ℝ,
      (coordSystem sys).dynamics (coordComplexify (x t)) (u t) =
        coordComplexify (sys.dynamics (x t) (u t)) := by
    intro t
    have hA := congrFun (congrArg DFunLike.coe (coordComplexify_comp sys.A)) (x t)
    simp only [LinearMap.comp_apply] at hA
    simp only [LinearSystem.dynamics_apply, coordSystem, LinearMap.add_apply,
      LinearMap.comp_apply]
    rw [hA, map_add]
  have hx_int : ∀ t : ℝ, coordComplexify (x t) =
      coordComplexify x₀ + ∫ s in (0 : ℝ)..t,
        (coordSystem sys).dynamics (coordComplexify (x s)) (u s) := by
    intro t
    have h := congrArg (fun v : X => coordComplexify v) (variationOfConstants_integral sys 0 x₀ u hu t)
    simp only [map_add] at h
    rw [h]
    congr 1
    have hloc : MeasureTheory.LocallyIntegrable
        (fun s : ℝ => sys.dynamics (x s) (u s)) MeasureTheory.volume :=
      locallyIntegrable_dynamics sys x u
        (continuous_variationOfConstants sys 0 x₀ u hu) hu
    have hInt : IntervalIntegrable (fun s : ℝ => sys.dynamics (x s) (u s))
        MeasureTheory.volume 0 t :=
      intervalIntegrable_iff.mpr <|
        (hloc.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
    rw [show (∫ s in (0 : ℝ)..t,
          (coordSystem sys).dynamics (coordComplexify (x s)) (u s)) =
        ∫ s in (0 : ℝ)..t, coordComplexify (sys.dynamics (x s) (u s)) by
      apply intervalIntegral.integral_congr
      intro s _
      exact hdyn s]
    exact (Ψc.intervalIntegral_comp_comm hInt).symm
  have hy_cont : Continuous ((coordSystem sys).variationOfConstants 0 (coordComplexify x₀) u) :=
    continuous_variationOfConstants (coordSystem sys) 0 (coordComplexify x₀) u hu
  have hy0 : (coordSystem sys).variationOfConstants 0 (coordComplexify x₀) u 0 =
      coordComplexify x₀ := variationOfConstants_self (coordSystem sys) 0 (coordComplexify x₀) u
  have hy_int : ∀ t : ℝ,
      (coordSystem sys).variationOfConstants 0 (coordComplexify x₀) u t =
        coordComplexify x₀ + ∫ s in (0 : ℝ)..t,
          (coordSystem sys).dynamics
            ((coordSystem sys).variationOfConstants 0 (coordComplexify x₀) u s) (u s) :=
    fun t => variationOfConstants_integral (coordSystem sys) 0 (coordComplexify x₀) u hu t
  exact integralSolution_unique (coordSystem sys) 0 (coordComplexify x₀) u hu
    hx_cont (by simpa [x] using hx0) hx_int hy_cont hy0 hy_int

/-! ### The input-space coordinate complexification -/

/-- The canonical real coordinate equivalence of the input space. -/
noncomputable def realCoordEquivU :
    U ≃L[ℝ] (Fin (Module.finrank ℝ U) → ℝ) :=
  (Module.finBasis ℝ U).equivFun.toContinuousLinearEquiv

/-- The input-space coordinate complexification `U → (Fin m → ℂ)`. -/
noncomputable def coordComplexifyU :
    U →ₗ[ℝ] (Fin (Module.finrank ℝ U) → ℂ) :=
  LinearMap.ofRealPi.comp realCoordEquivU.toLinearMap

/-- The complexified coordinate input map. -/
noncomputable def coordComplexB (B : U →ₗ[ℝ] X) :
    (Fin (Module.finrank ℝ U) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℝ X) → ℂ) :=
  Matrix.toLin' ((LinearMap.toMatrix (Module.finBasis ℝ U) (Module.finBasis ℝ X) B).map
    (algebraMap ℝ ℂ))

/-- The complexified coordinate input map intertwines `B` with its real
coordinate complexification. -/
theorem coordComplexB_coordComplexifyU (B : U →ₗ[ℝ] X) (v : U) :
    coordComplexB B (coordComplexifyU v) = coordComplexify (B v) := by
  let M := LinearMap.toMatrix (Module.finBasis ℝ U) (Module.finBasis ℝ X) B
  have hMv : M *ᵥ (Module.finBasis ℝ U).equivFun v =
      (Module.finBasis ℝ X).equivFun (B v) := by
    rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
    exact LinearMap.toMatrix_mulVec_repr (Module.finBasis ℝ U) (Module.finBasis ℝ X) B v
  change (Matrix.toLin' (M.map (algebraMap ℝ ℂ)))
      (LinearMap.ofRealPi ((Module.finBasis ℝ U).equivFun v)) =
    LinearMap.ofRealPi ((Module.finBasis ℝ X).equivFun (B v))
  rw [← hMv]
  change (Matrix.toLin' (M.map (algebraMap ℝ ℂ)))
      (LinearMap.ofRealPi ((Module.finBasis ℝ U).equivFun v)) =
    LinearMap.ofRealPi (M *ᵥ (Module.finBasis ℝ U).equivFun v)
  rw [Matrix.toLin'_apply]
  funext i
  exact (RingHom.map_mulVec (algebraMap ℝ ℂ) M
    ((Module.finBasis ℝ U).equivFun v) i).symm

/-- The inverse input-coordinate equivalence intertwines the rectangular matrix
of `B`. -/
theorem realCoordEquiv_symm_mulVec_B (B : U →ₗ[ℝ] X)
    (y : Fin (Module.finrank ℝ U) → ℝ) :
    realCoordEquiv.symm
        ((LinearMap.toMatrix (Module.finBasis ℝ U) (Module.finBasis ℝ X) B) *ᵥ y) =
      B (realCoordEquivU.symm y) := by
  apply realCoordEquiv.injective
  rw [realCoordEquiv.apply_symm_apply]
  have hrepr : (LinearMap.toMatrix (Module.finBasis ℝ U) (Module.finBasis ℝ X) B) *ᵥ
        (Module.finBasis ℝ U).equivFun (realCoordEquivU.symm y) =
      (Module.finBasis ℝ X).equivFun (B (realCoordEquivU.symm y)) :=
    LinearMap.toMatrix_mulVec_repr (Module.finBasis ℝ U) (Module.finBasis ℝ X) B
      (realCoordEquivU.symm y)
  have hy : (Module.finBasis ℝ U).equivFun (realCoordEquivU.symm y) = y := by
    change (Module.finBasis ℝ U).equivFun
      ((Module.finBasis ℝ U).equivFun.symm y) = y
    exact (Module.finBasis ℝ U).equivFun.apply_symm_apply y
  rw [hy] at hrepr
  rw [hrepr]
  rfl

/-- The real projection of the range of the complexified input map lies in
`range B`. -/
theorem coordRealify_range_coordComplexB_le (B : U →ₗ[ℝ] X) :
    Submodule.map coordRealify ((LinearMap.range (coordComplexB B)).restrictScalars ℝ) ≤
      LinearMap.range B := by
  rintro w ⟨z, hz, rfl⟩
  obtain ⟨y, rfl⟩ := hz
  let M := LinearMap.toMatrix (Module.finBasis ℝ U) (Module.finBasis ℝ X) B
  have hre : rePi (coordComplexB B y) = M *ᵥ (fun j => (y j).re) := by
    rw [coordComplexB, Matrix.toLin'_apply]
    funext i
    change (((M.map (algebraMap ℝ ℂ)) *ᵥ y) i).re = _
    simp only [Matrix.mulVec, dotProduct]
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Complex.mul_re]
    simp
  refine ⟨realCoordEquivU.symm (fun j => (y j).re), ?_⟩
  rw [coordRealify, LinearMap.comp_apply, hre]
  exact (realCoordEquiv_symm_mulVec_B B (fun j => (y j).re)).symm

/-! ### Transport of the spectral subspaces -/

/-- `coordRealify` maps the complex Hurwitz subspace back into the real Hurwitz
subspace.  The complex subspace is conjugation-invariant
(`star_mem_hurwitzComplexSubspace`), so it contains the real-part projection
`(z + star z)/2` of each of its elements. -/
theorem coordRealify_mem_hurwitzSubspace (A : X →ₗ[ℝ] X)
    {z : Fin (Module.finrank ℝ X) → ℂ}
    (hz : z ∈ LinearMap.hurwitzComplexSubspace A) :
    coordRealify z ∈ LinearMap.hurwitzSubspace A := by
  rw [LinearMap.mem_hurwitzSubspace]
  have hz' : star z ∈ LinearMap.hurwitzComplexSubspace A :=
    LinearMap.star_mem_hurwitzComplexSubspace A hz
  have hcomb : (2 : ℂ)⁻¹ • (z + star z) ∈ LinearMap.hurwitzComplexSubspace A :=
    (LinearMap.hurwitzComplexSubspace A).smul_mem _
      ((LinearMap.hurwitzComplexSubspace A).add_mem hz hz')
  have hΨR : coordComplexify (coordRealify z) = (2 : ℂ)⁻¹ • (z + star z) := by
    have h1 : coordComplexify (coordRealify z) = LinearMap.ofRealPi (rePi z) := by
      simp only [coordComplexify, coordRealify, LinearMap.comp_apply]
      congr 1
      exact realCoordEquiv.apply_symm_apply (rePi z)
    rw [h1]
    funext i
    simp only [LinearMap.ofRealPi_apply, rePi, Pi.smul_apply, Pi.add_apply, Pi.star_apply]
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im,
      Complex.inv_re, Complex.inv_im] <;> ring
  change coordComplexify (coordRealify z) ∈ LinearMap.hurwitzComplexSubspace A
  rw [hΨR]
  exact hcomb

/-- `coordRealify` intertwines powers of the complexified coordinate generator
with powers of `A`. -/
theorem coordRealify_pow_coordComplexA (A : X →ₗ[ℝ] X) (k : ℕ)
    (w : Fin (Module.finrank ℝ X) → ℂ) :
    coordRealify (((coordComplexA A) ^ k) w) = (A ^ k) (coordRealify w) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
    have h := congrFun (congrArg DFunLike.coe (coordRealify_comp_coordComplexA A))
      (((coordComplexA A) ^ k) w)
    simp only [LinearMap.comp_apply] at h
    change coordRealify (((coordComplexA A).restrictScalars ℝ)
      (((coordComplexA A) ^ k) w)) = A ((A ^ k) (coordRealify w))
    rw [h, ih]

/-- `coordRealify` maps the reachable subspace of the coordinate system into the
reachable subspace of the original system. -/
theorem coordRealify_map_reachableSubspace_le (sys : LinearSystem ℝ X U Z) :
    Submodule.map coordRealify
      (LinearMap.reachableSubspace (coordSystem sys).A (coordSystem sys).B) ≤
      LinearMap.reachableSubspace sys.A sys.B := by
  rw [LinearMap.reachableSubspace, Submodule.map_iSup]
  refine iSup_le fun k => ?_
  intro w hw
  obtain ⟨v, hv, rfl⟩ := hw
  obtain ⟨u, rfl⟩ := hv
  have hpow : ∀ k : ℕ, ∀ w : Fin (Module.finrank ℝ X) → ℂ,
      (((coordComplexA sys.A).restrictScalars ℝ) ^ k) w = ((coordComplexA sys.A) ^ k) w := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih =>
        intro w
        rw [pow_succ', pow_succ']
        simp only [Module.End.mul_apply, ih]
        rfl
  have hAB : (((sys.coordSystem.A) ^ k) ∘ₗ sys.coordSystem.B) u =
      ((coordComplexA sys.A) ^ k) (coordComplexify (sys.B u)) := by
    change (((coordComplexA sys.A).restrictScalars ℝ) ^ k) (coordComplexify (sys.B u)) = _
    exact hpow k (coordComplexify (sys.B u))
  rw [hAB, coordRealify_pow_coordComplexA, coordRealify_coordComplexify,
    LinearMap.reachableSubspace]
  exact Submodule.mem_iSup_of_mem k ⟨u, rfl⟩

/-! ### Real ODE facts used by the bridge assembly

These are copies of the private helpers `LinearMap.finiteBohl_linear_ode_eq_exp`
and `LinearMap.finiteBohl_quotient_ode_eq_exp`, together with the decay-only
weakening of `LinearMap.stable_forced_component_mem_stabilizableSubspace`.
They carry no complex structure and are used to assemble the real bridge. -/

private theorem realBohl_linear_ode_eq_exp
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (A : Y →L[ℝ] Y) (y : ℝ → Y)
    (hode : ∀ t, HasDerivAt y (A (y t)) t) :
    ∀ t, y t = NormedSpace.exp (t • A) (y 0) := by
  let P : ℝ → Y := fun t => NormedSpace.exp (t • (-A)) (y t)
  have hP : ∀ t, HasDerivAt P 0 t := by
    intro t
    have hexp : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • (-A)))
        (NormedSpace.exp (t • (-A)) * (-A)) t := by
      simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) (-A) t
    have h := hexp.clm_apply (hode t)
    convert h using 1 <;> simp [P, mul_apply_eq_comp]
  have hconst : ∀ t, P t = P 0 := by
    intro t
    exact is_const_of_deriv_eq_zero (fun s => (hP s).differentiableAt)
      (fun s => (hP s).deriv) t 0
  intro t
  let E : Y →L[ℝ] Y := NormedSpace.exp (t • A)
  have headd : E * NormedSpace.exp (t • (-A)) = 1 := by
    have hneg : t • (-A) = (-t) • A := by simp
    have hcomm : Commute (t • A) (t • (-A)) := by
      rw [hneg]
      exact ((Commute.refl A).smul_left t).smul_right (-t)
    have hsum : t • A + t • (-A) = 0 := by rw [hneg, ← add_smul]; simp
    have hmem1 : (t • A) ∈
        Metric.eball (0 : Y →L[ℝ] Y) (NormedSpace.expSeries ℝ (Y →L[ℝ] Y)).radius :=
      (NormedSpace.expSeries_radius_eq_top ℝ (Y →L[ℝ] Y)).symm ▸ edist_lt_top _ _
    have hmem2 : (t • (-A)) ∈
        Metric.eball (0 : Y →L[ℝ] Y) (NormedSpace.expSeries ℝ (Y →L[ℝ] Y)).radius :=
      (NormedSpace.expSeries_radius_eq_top ℝ (Y →L[ℝ] Y)).symm ▸ edist_lt_top _ _
    rw [← NormedSpace.exp_add_of_commute_of_mem_ball hcomm hmem1 hmem2, hsum,
      NormedSpace.exp_zero]
  have hcancel : E (P t) = y t := by
    change (NormedSpace.exp (t • A))
      ((NormedSpace.exp (t • (-A))) (y t)) = y t
    rw [← mul_apply_eq_comp, headd]
    simp
  calc
    y t = E (P t) := hcancel.symm
    _ = E (P 0) := congrArg E (hconst t)
    _ = NormedSpace.exp (t • A) (y 0) := by simp [E, P]

private theorem realBohl_quotient_ode_eq_exp
    {Y V : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : Y →ₗ[ℝ] Y) (B : V →ₗ[ℝ] Y)
    [IsClosed (LinearMap.reachableSubspace A B : Set Y)]
    [IsTopologicalRing
      ((Y ⧸ LinearMap.reachableSubspace A B) →L[ℝ]
        (Y ⧸ LinearMap.reachableSubspace A B))]
    (g : ℝ → Y) (r : ℝ → Y) (x₀ : Y)
    (hg0 : g 0 = x₀)
    (hode : ∀ t, HasDerivAt g (A (g t) + r t) t)
    (hr : ∀ t, r t ∈ LinearMap.reachableSubspace A B) :
    ∀ t, (LinearMap.reachableSubspace A B).mkQ (g t) =
      NormedSpace.exp (t • (LinearMap.quotientReachableA A B).toContinuousLinearMap)
        ((LinearMap.reachableSubspace A B).mkQ x₀) := by
  let R := LinearMap.reachableSubspace A B
  let Aq : (Y ⧸ R) →ₗ[ℝ] (Y ⧸ R) := R.mapQ R A
    ((Submodule.map_le_iff_le_comap).mp (LinearMap.map_reachableSubspace_le A B))
  have hR : R ≤ R.comap A := fun x hx =>
    LinearMap.map_reachableSubspace_le A B ⟨x, hx, rfl⟩
  have hq : R.mkQ.comp A = Aq.comp R.mkQ := by
    ext x
    exact (congrFun (congrArg DFunLike.coe (Submodule.mapQ_mkQ R R A (h := hR))) x).symm
  have hqode : ∀ t, HasDerivAt (fun s : ℝ => R.mkQ (g s))
      (Aq (R.mkQ (g t))) t := by
    intro t
    have hd := (ContinuousLinearMap.hasFDerivAt R.mkQ.toContinuousLinearMap).comp_hasDerivAt
      t (hode t)
    have hderiv : R.mkQ (A (g t) + r t) = Aq (R.mkQ (g t)) := by
      have hr0 : R.mkQ (r t) = 0 :=
        (Submodule.Quotient.mk_eq_zero R).mpr (hr t)
      calc
        R.mkQ (A (g t) + r t) = R.mkQ (A (g t)) + R.mkQ (r t) := map_add _ _ _
        _ = R.mkQ (A (g t)) := by rw [hr0, add_zero]
        _ = Aq (R.mkQ (g t)) := congrFun (congrArg DFunLike.coe hq) (g t)
    exact hd.congr_deriv hderiv
  have hflow := realBohl_linear_ode_eq_exp Aq.toContinuousLinearMap
    (fun t => R.mkQ (g t)) hqode
  intro t
  simpa [Aq, LinearMap.quotientReachableA, R, hg0] using hflow t

/-- **Decay-only stable forced component.** The public
`LinearMap.stable_forced_component_mem_stabilizableSubspace` only uses the decay
of the stable Bohl component; this is the same statement with that decay as the
hypothesis, which lets it apply to real Bohl signals pushed through the
coordinate complexification. -/
theorem realBohl_stable_forced_component_mem_stabilizableSubspace
    {Y V : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [FiniteDimensional ℝ Y] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : Y →ₗ[ℝ] Y) (B : V →ₗ[ℝ] Y)
    (g r : ℝ → Y) (hg : Filter.Tendsto g Filter.atTop (nhds 0))
    (hode : ∀ t, HasDerivAt g (A (g t) + r t) t)
    (hr : ∀ t, r t ∈ LinearMap.reachableSubspace A B) :
    g 0 ∈ LinearMap.hurwitzSubspace A ⊔ LinearMap.reachableSubspace A B := by
  let R := LinearMap.reachableSubspace A B
  haveI : IsClosed (R : Set Y) := R.closed_of_finiteDimensional
  letI : IsTopologicalRing ((Y ⧸ R) →L[ℝ] (Y ⧸ R)) :=
    { continuous_add := continuous_add
      continuous_mul := Continuous.clm_comp continuous_fst continuous_snd
      continuous_neg := continuous_neg }
  have hflow := realBohl_quotient_ode_eq_exp A B g r (g 0) rfl hode hr
  let q : Y →L[ℝ] Y ⧸ R := R.mkQ.toContinuousLinearMap
  have hqdec : Filter.Tendsto (fun t : ℝ => q (g t)) Filter.atTop (nhds 0) := by
    have h := (q.continuous.tendsto 0).comp hg
    simpa only [Function.comp_def, map_zero] using h
  have horbit : Filter.Tendsto
      (fun t : ℝ => NormedSpace.exp
        (t • (LinearMap.quotientReachableA A B).toContinuousLinearMap)
        (R.mkQ (g 0))) Filter.atTop (nhds 0) := by
    refine hqdec.congr' (Filter.Eventually.of_forall fun t => ?_)
    exact hflow t
  have hquot : R.mkQ (g 0) ∈ LinearMap.hurwitzSubspace
      (LinearMap.quotientReachableA A B) :=
    LinearMap.orbit_decay_mem_hurwitz (LinearMap.quotientReachableA A B) horbit
  have hcomap : g 0 ∈ Submodule.comap R.mkQ
      (LinearMap.hurwitzSubspace (LinearMap.quotientReachableA A B)) :=
    Submodule.mem_comap.mpr hquot
  rw [LinearMap.comap_hurwitzSubspace_quotientReachable_eq A B] at hcomap
  simpa [R] using hcomap

/-! ### The real bridge

The finite-Bohl forcing-image `W_g` bridge for an arbitrary finite-dimensional
real state space, with no `NormedSpace ℂ X` hypothesis.  The input hypothesis is
the real Bohl class `IsRealBohl`; the spectral content is transported through
the coordinate complexification `coordComplexify : X → (Fin n → ℂ)` and the
real-linear projection `coordRealify`. -/

def IsRealBohlOutputStabilizable (sys : LinearSystem ℝ X U Z) (H : X →ₗ[ℝ] Z)
    (x : X) : Prop :=
  ∃ u : ℝ → U, MeasureTheory.LocallyIntegrable u MeasureTheory.volume ∧
    IsRealBohl (fun t : ℝ => sys.B (u t)) ∧
    Filter.Tendsto (fun t : ℝ => H (sys.variationOfConstants 0 x u t))
      Filter.atTop (nhds 0)

set_option maxHeartbeats 800000 in
-- Coordinate transport followed by the complex spectral bridge needs extra elaboration time.
/-- For a finite-dimensional real system, an output-decaying trajectory driven
by a real Bohl forcing term starts in the output-stabilizable subspace. The
proof transports the trajectory to complex coordinates, applies the spectral
Bohl bridge there, and projects the resulting geometric inclusion back to the
real state space. -/
theorem finiteBohlWBridge_real (sys : LinearSystem ℝ X U Z) (H : X →ₗ[ℝ] Z) :
    ∀ x : X, IsRealBohlOutputStabilizable sys H x →
      x ∈ outputStabilizableSubspace sys.A sys.B H := by
  intro x hx
  obtain ⟨u, hu, hBu, hdec⟩ := hx
  let sys' : LinearSystem ℝ (Fin (Module.finrank ℝ X) → ℂ) U Z := coordSystem sys
  let H' : (Fin (Module.finrank ℝ X) → ℂ) →ₗ[ℝ] Z := H.comp coordRealify
  have hBu' : IsExponentialPolynomial (fun t : ℝ => sys'.continuousB (u t)) := by
    change IsExponentialPolynomial (fun t : ℝ => coordComplexify (sys.B (u t)))
    exact hBu
  have hdec' : Filter.Tendsto
      (fun t : ℝ => H' (sys'.variationOfConstants 0 (coordComplexify x) u t))
      Filter.atTop (nhds 0) := by
    change Filter.Tendsto
      (fun t : ℝ => H' ((coordSystem sys).variationOfConstants 0 (coordComplexify x) u t))
      Filter.atTop (nhds 0)
    rw [← coordSystem_variationOfConstants sys x u hu]
    apply hdec.congr'
    filter_upwards with t
    simp [H']
  obtain ⟨G, Bc, hsplit, hGstable, hBcantistable, hGdec, hH'Bc⟩ :=
    finiteBohl_state_stable_antistable_decomposition sys' H' (coordComplexify x) u hu hBu' hdec'
  let S : Submodule ℂ (Fin (Module.finrank ℝ X) → ℂ) :=
    LinearMap.range (coordComplexB sys.B)
  have hrange : ∀ t : ℝ, sys'.B (u t) ∈ S := by
    intro t
    refine ⟨coordComplexifyU (u t), ?_⟩
    change coordComplexB sys.B (coordComplexifyU (u t)) = coordComplexify (sys.B (u t))
    exact coordComplexB_coordComplexifyU sys.B (u t)
  have hode := fun t : ℝ => by
    have h := variationOfConstants_hasDerivAt_of_finiteBohl_forcing
      sys' (coordComplexify x) u hu hBu' t
    simpa only [continuousA_apply] using h
  have hres :
      (∀ t, deriv G t - sys'.continuousA (G t) ∈ S) ∧
      (∀ t, deriv Bc t - sys'.continuousA (Bc t) ∈ S) ∧
      (∀ t, HasDerivAt G
        (sys'.continuousA (G t) + (deriv G t - sys'.continuousA (G t))) t) ∧
      (∀ t, HasDerivAt Bc
        (sys'.continuousA (Bc t) + (deriv Bc t - sys'.continuousA (Bc t))) t) :=
    stable_antistable_ode_residuals_mem_submodule
      (X := Fin (Module.finrank ℝ X) → ℂ) sys'.continuousA S
      (f := sys'.variationOfConstants 0 (coordComplexify x) u)
      (r := fun t => sys'.B (u t)) (g := G) (b := Bc)
      hsplit hGstable hBcantistable hode hrange
  let g : ℝ → X := fun t => coordRealify (G t)
  let b : ℝ → X := fun t => coordRealify (Bc t)
  have hsplitR : sys.variationOfConstants 0 x u = g + b := by
    funext t
    have h := congrArg coordRealify (congrFun hsplit t)
    have hvc := congrFun (coordSystem_variationOfConstants sys x u hu) t
    rw [← hvc] at h
    simpa [g, b, map_add, coordRealify_coordComplexify] using h
  have hgdec : Filter.Tendsto g Filter.atTop (nhds 0) := by
    have hc : Continuous coordRealify :=
      (coordRealify : (Fin (Module.finrank ℝ X) → ℂ) →ₗ[ℝ] X).continuous_of_finiteDimensional
    have h := (hc.tendsto 0).comp hGdec
    simpa only [Function.comp_def, map_zero, g] using h
  have hHb : ∀ t, H (b t) = 0 := by
    intro t
    have h := hH'Bc t
    simpa [b, H'] using h
  have hdiffG : ∀ t, HasDerivAt G (deriv G t) t :=
    fun t => (hres.2.2.1 t).congr_deriv (by abel)
  have hdiffB : ∀ t, HasDerivAt Bc (deriv Bc t) t :=
    fun t => (hres.2.2.2 t).congr_deriv (by abel)
  have hderiv_g : ∀ t, deriv g t = coordRealify (deriv G t) := by
    intro t
    have h := coordRealifyCLM.hasFDerivAt.comp_hasDerivAt t (hdiffG t)
    change HasDerivAt g (coordRealify (deriv G t)) t at h
    exact h.deriv
  have hderiv_b : ∀ t, deriv b t = coordRealify (deriv Bc t) := by
    intro t
    have h := coordRealifyCLM.hasFDerivAt.comp_hasDerivAt t (hdiffB t)
    change HasDerivAt b (coordRealify (deriv Bc t)) t at h
    exact h.deriv
  have hAg : ∀ t, sys.A (g t) = coordRealify (sys'.A (G t)) := by
    intro t
    have hc := congrFun (congrArg DFunLike.coe (coordRealify_comp_coordComplexA sys.A)) (G t)
    simp only [LinearMap.comp_apply] at hc
    exact hc.symm
  have hAb : ∀ t, sys.A (b t) = coordRealify (sys'.A (Bc t)) := by
    intro t
    have hc := congrFun (congrArg DFunLike.coe (coordRealify_comp_coordComplexA sys.A)) (Bc t)
    simp only [LinearMap.comp_apply] at hc
    exact hc.symm
  have hode_g : ∀ t, HasDerivAt g (sys.A (g t) + (deriv g t - sys.A (g t))) t := by
    intro t
    have h := coordRealifyCLM.hasFDerivAt.comp_hasDerivAt t (hdiffG t)
    change HasDerivAt g (coordRealify (deriv G t)) t at h
    have hderiv : coordRealify (deriv G t) = sys.A (g t) + (deriv g t - sys.A (g t)) := by
      rw [hderiv_g t, hAg t]; abel
    rwa [hderiv] at h
  have hode_b : ∀ t, HasDerivAt b (sys.A (b t) + (deriv b t - sys.A (b t))) t := by
    intro t
    have h := coordRealifyCLM.hasFDerivAt.comp_hasDerivAt t (hdiffB t)
    change HasDerivAt b (coordRealify (deriv Bc t)) t at h
    have hderiv : coordRealify (deriv Bc t) = sys.A (b t) + (deriv b t - sys.A (b t)) := by
      rw [hderiv_b t, hAb t]; abel
    rwa [hderiv] at h
  have hrg : ∀ t, deriv g t - sys.A (g t) ∈ LinearMap.reachableSubspace sys.A sys.B := by
    intro t
    have hmem : deriv G t - sys'.A (G t) ∈ S := hres.1 t
    have h' : coordRealify (deriv G t - sys'.A (G t)) ∈ LinearMap.range sys.B :=
      coordRealify_range_coordComplexB_le sys.B ⟨deriv G t - sys'.A (G t), hmem, rfl⟩
    have heq : coordRealify (deriv G t - sys'.A (G t)) = deriv g t - sys.A (g t) := by
      rw [map_sub, hderiv_g t, hAg t]
    rw [← heq]
    exact LinearMap.range_le_reachableSubspace sys.A sys.B h'
  have hrb : ∀ t, deriv b t - sys.A (b t) ∈ LinearMap.range sys.B := by
    intro t
    have hmem : deriv Bc t - sys'.A (Bc t) ∈ S := hres.2.1 t
    have h' : coordRealify (deriv Bc t - sys'.A (Bc t)) ∈ LinearMap.range sys.B :=
      coordRealify_range_coordComplexB_le sys.B ⟨deriv Bc t - sys'.A (Bc t), hmem, rfl⟩
    have heq : coordRealify (deriv Bc t - sys'.A (Bc t)) = deriv b t - sys.A (b t) := by
      rw [map_sub, hderiv_b t, hAb t]
    rw [← heq]
    exact h'
  have hg0 : g 0 ∈ LinearMap.stabilizableSubspace sys.A sys.B :=
    realBohl_stable_forced_component_mem_stabilizableSubspace sys.A sys.B g
      (fun t => deriv g t - sys.A (g t)) hgdec hode_g hrg
  have hb0 : b 0 ∈ LinearMap.controlledInvariantSubspace sys.A sys.B (LinearMap.ker H) :=
    LinearMap.forced_curve_initial_mem_controlledInvariantSubspace sys.A sys.B H b
      (fun t => deriv b t - sys.A (b t)) hode_b hrb hHb
  have hxsplit : x = b 0 + g 0 := by
    have h0 := congrFun hsplitR 0
    rw [variationOfConstants_self sys 0 x u] at h0
    simpa [add_comm] using h0
  rw [outputStabilizableSubspace, hxsplit]
  exact Submodule.add_mem_sup hb0 hg0

end

end LinearSystem

/-! ## Real-space first necessity inclusion -/

namespace LinearSystem

section StableDynamicLoop

variable {X U Y D Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [AddCommGroup Y] [Module ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]
variable [NormedAddCommGroup D] [NormedSpace ℝ D]

/-- Every orbit of a finite-dimensional real-linear generator is real Bohl after
coordinate complexification. -/
theorem isRealBohl_expFlow_of_realLinear (A : X →ₗ[ℝ] X) (x : X) :
    IsRealBohl (fun t : ℝ => NormedSpace.exp (t • A.toContinuousLinearMap) x) := by
  let L := (coordComplexify (X := X)).toContinuousLinearMap
  let Ac := ((coordComplexA A).restrictScalars ℝ).toContinuousLinearMap
  have hLA : L.comp A.toContinuousLinearMap = Ac.comp L := by
    apply ContinuousLinearMap.ext
    intro y
    exact congrFun (congrArg DFunLike.coe (coordComplexify_comp A)) y |>.symm
  have hfun : (fun t : ℝ => coordComplexify
      (NormedSpace.exp (t • A.toContinuousLinearMap) x)) =
      fun t : ℝ => NormedSpace.exp (t • Ac) (coordComplexify x) := by
    funext t
    exact clm_map_exp_smul L A.toContinuousLinearMap Ac hLA t x
  change IsExponentialPolynomial
    (fun t : ℝ => coordComplexify (NormedSpace.exp (t • A.toContinuousLinearMap) x))
  rw [hfun]
  exact isExponentialPolynomial_expFlow_of_realLinear
    ((coordComplexA A).restrictScalars ℝ) (coordComplexify x)

/-- First geometric necessity inclusion of Corollary 6.22 for an arbitrary
finite-dimensional real dynamic controller. Its resolved input has real-Bohl
forcing image; `finiteBohlWBridge_real` then identifies the initial plant state
with a member of `W_g(ker H)`. -/
theorem range_E_le_outputStabilizableSubspace_of_stableNonzeroExternalResponse
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : StableNonzeroExternalResponse sys hD E H) :
    LinearMap.range E ≤ outputStabilizableSubspace sys.A sys.B H := by
  classical
  obtain ⟨ctrl, hdec⟩ := h
  let sysZ : LinearSystem ℝ X U Z := ⟨sys.A, sys.B, H, 0⟩
  rintro _ ⟨d, rfl⟩
  let ic := cabPairInterconnection sys ctrl E H
  let hwp := ic.isWellPosed_of_D_eq_zero hD
  let p : ℝ → X × X := fun t => (ic.closedLoopSystem hwp).expFlow t (E d, 0)
  let u : ℝ → U := fun t => ic.solvedInput hwp (p t)
  have hp_cont : Continuous p := by
    rw [continuous_iff_continuousAt]
    intro t
    exact (hasDerivAt_expFlow_apply_state (ic.closedLoopSystem hwp) t (E d, 0)).continuousAt
  have hu_cont : Continuous u :=
    (ic.solvedInput hwp).continuous_of_finiteDimensional.comp hp_cont
  have hu : MeasureTheory.LocallyIntegrable u MeasureTheory.volume := hu_cont.locallyIntegrable
  have hpBohl : IsRealBohl (fun t : ℝ => p t) := by
    have hfun : (fun t : ℝ => p t) =
        fun t : ℝ => NormedSpace.exp (t • (ic.closedLoopMap hwp).toContinuousLinearMap)
          (E d, 0) := by
      funext t
      simp [p, ic.closedLoopSystem_expFlow_eq hwp]
    rw [hfun]
    exact isRealBohl_expFlow_of_realLinear (ic.closedLoopMap hwp) (E d, 0)
  let r : X × X →ₗ[ℝ] (Fin (Module.finrank ℝ X) → ℂ) :=
    (coordComplexify (X := X)).comp (sys.B.comp (ic.solvedInput hwp))
  let rC : (Fin (Module.finrank ℝ (X × X)) → ℂ) →ₗ[ℝ]
      (Fin (Module.finrank ℝ X) → ℂ) := r.comp (coordRealify (X := X × X))
  have hBu : IsRealBohl (fun t : ℝ => sys.B (u t)) := by
    change IsExponentialPolynomial (fun t : ℝ => coordComplexify (sys.B (u t)))
    have hfun : (fun t : ℝ => coordComplexify (sys.B (u t))) =
        fun t : ℝ => rC (coordComplexify (p t)) := by
      funext t
      simp [u, r, rC, LinearMap.comp_apply, coordRealify_coordComplexify]
    rw [hfun]
    exact hpBohl.map_realLinear rC.toContinuousLinearMap
  have hresp_fun : (fun t : ℝ => ic.externalResponse hwp t d) = fun t : ℝ => H (p t).1 := by
    funext t
    rw [ic.externalResponse_apply]
    have hdist : ic.disturbanceMapWithF hwp d = (E d, 0) := by
      rw [ic.disturbanceMapWithF_of_F_eq_zero hwp rfl, ic.disturbanceMap_apply]
      change (E d, 0) = (E d, 0)
      rfl
    rw [hdist, ic.outputMap_apply]
    change H (((ic.closedLoopSystem hwp).expFlow t) (E d, 0)).1 = H (p t).1
    simp [p]
  have hdec_ic : Filter.Tendsto (fun t : ℝ => ic.externalResponse hwp t d)
      Filter.atTop (nhds 0) := by
    simpa [ic, hwp] using hdec d
  have hresp : Filter.Tendsto (fun t : ℝ => H (p t).1) Filter.atTop (nhds 0) := by
    convert hdec_ic using 1
    funext t
    exact (congrFun hresp_fun t).symm
  have htraj : (fun t : ℝ => (p t).1) = sysZ.variationOfConstants 0 (E d) u := by
    simpa [ic, hwp, p, u] using
      (closedLoop_expFlow_fst_eq_variationOfConstants sys sysZ rfl rfl ctrl hD E H d)
  have hdecZ : Filter.Tendsto
      (fun t : ℝ => H (sysZ.variationOfConstants 0 (E d) u t)) Filter.atTop (nhds 0) := by
    have hfun : (fun t : ℝ => H (sysZ.variationOfConstants 0 (E d) u t)) =
        fun t : ℝ => H (p t).1 := by
      funext t
      rw [← congrFun htraj t]
    rw [hfun]
    exact hresp
  have hbohl : IsRealBohlOutputStabilizable sysZ H (E d) := ⟨u, hu, hBu, hdecZ⟩
  simpa [sysZ] using finiteBohlWBridge_real sysZ H (E d) hbohl

end StableDynamicLoop

end LinearSystem

namespace LinearSystem

section DualConditionAssembly

variable {X U Y D Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
variable [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z]

omit [FiniteDimensional ℝ U] in
/-- The transposed `W_g` inclusion implies the second geometric inclusion by
the controlled/conditioned-invariant annihilator duality. -/
theorem secondInclusion_of_dual_range_le
    (sys : LinearSystem ℝ X U Y) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (hdual : LinearMap.range H.dualMap ≤
      outputStabilizableSubspace sys.A.dualMap sys.C.dualMap E.dualMap) :
    LinearMap.conditionedInvariantSubspace sys.C sys.A (LinearMap.range E) ⊓
      LinearMap.detectableSubspace sys.C sys.A ≤ LinearMap.ker H := by
  apply conditionedInvariant_inf_detectable_le_ker_of_dual_mem_outputStabilizableSubspace
    sys.C sys.A E H
  rwa [outputStabilizableSubspace, LinearMap.ker_dualMap_eq_dualAnnihilator_range] at hdual

/-- Conditional converse assembly: the first inclusion follows from the stable
dynamic controller; a transposed `W_g` inclusion supplies the second. -/
theorem externalStabilizationConditions_of_stableNonzeroExternalResponse_of_dualRange
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : StableNonzeroExternalResponse sys hD E H)
    (hdual : LinearMap.range H.dualMap ≤
      outputStabilizableSubspace sys.A.dualMap sys.C.dualMap E.dualMap) :
    ExternalStabilizationConditions sys E H := by
  exact ⟨range_E_le_outputStabilizableSubspace_of_stableNonzeroExternalResponse
      sys hD E H h,
    secondInclusion_of_dual_range_le sys E H hdual⟩

end DualConditionAssembly

end LinearSystem
