/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Control.Geometric.Rectification
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Pi

/-! # Coordinates adapted to a finite independent family

A finite independent family identifies its span with a finite coordinate space. Choosing a
complement gives a continuous linear equivalence from the product of these coordinates and the
complement to the ambient space. These are the linear coordinates used in the classical
simultaneous rectification construction.
-/

@[expose] public section

open scoped BigOperators

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {k : ℕ}

/-- The continuous linear combination map associated with a finite family. -/
noncomputable def frameCombination (v : Fin k → X) : (Fin k → ℝ) →L[ℝ] X :=
  (Fintype.linearCombination ℝ v).toContinuousLinearMap

@[simp] theorem frameCombination_apply (v : Fin k → X) (t : Fin k → ℝ) :
    frameCombination v t = ∑ i, t i • v i := rfl

theorem frameCombination_single (v : Fin k → X) (i : Fin k) (a : ℝ) :
    frameCombination v (Pi.single i a) = a • v i :=
  Fintype.linearCombination_apply_single ℝ v i a

theorem frameCombination_range (v : Fin k → X) :
    (frameCombination v).range = Submodule.span ℝ (Set.range v) :=
  Fintype.range_linearCombination ℝ v

theorem frameCombination_ker (v : Fin k → X) (hv : LinearIndependent ℝ v) :
    (frameCombination v).ker = ⊥ := by
  exact LinearMap.ker_eq_bot.mpr
    (linearIndependent_iff_injective_fintypeLinearCombination.mp hv)

/-- A complementary subspace to the span of a finite family. -/
noncomputable def frameComplement (v : Fin k → X) : Submodule ℝ X :=
  (Submodule.exists_isCompl (Submodule.span ℝ (Set.range v))).choose

theorem isCompl_frameComplement (v : Fin k → X) :
    IsCompl (Submodule.span ℝ (Set.range v)) (frameComplement v) :=
  (Submodule.exists_isCompl (Submodule.span ℝ (Set.range v))).choose_spec

/-- The direct sum of independent frame coordinates and complementary coordinates. -/
noncomputable def frameEquiv [FiniteDimensional ℝ X]
    (v : Fin k → X) (hv : LinearIndependent ℝ v) :
    ((Fin k → ℝ) × ↥(frameComplement v)) ≃L[ℝ] X :=
  ContinuousLinearMap.coprodSubtypeLEquivOfIsCompl (frameCombination v)
    (by rw [frameCombination_range]; exact isCompl_frameComplement v)
    (frameCombination_ker v hv)

@[simp] theorem frameEquiv_apply [FiniteDimensional ℝ X]
    (v : Fin k → X) (hv : LinearIndependent ℝ v)
    (p : (Fin k → ℝ) × ↥(frameComplement v)) :
    frameEquiv v hv p = (∑ i, p.1 i • v i) + (p.2 : X) := by
  rfl

theorem frameEquiv_single [FiniteDimensional ℝ X]
    (v : Fin k → X) (hv : LinearIndependent ℝ v) (i : Fin k) (a : ℝ) :
    frameEquiv v hv (Pi.single i a, 0) = a • v i := by
  change frameCombination v (Pi.single i a) + 0 = a • v i
  simp

/-- Split a finite coordinate vector into its first and last blocks. -/
noncomputable def finCoordinatesSplit (k m : ℕ) :
    (Fin (k + m) → ℝ) ≃L[ℝ] ((Fin k → ℝ) × (Fin m → ℝ)) :=
  ((LinearEquiv.piCongrLeft' ℝ (fun _ : Fin (k + m) => ℝ) finSumFinEquiv.symm).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin k) (Fin m) ℝ ℝ)).toContinuousLinearEquiv

@[simp] theorem finCoordinatesSplit_fst (k m : ℕ) (t : Fin (k + m) → ℝ)
    (i : Fin k) :
    (finCoordinatesSplit k m t).1 i = t (Fin.castAdd m i) := rfl

@[simp] theorem finCoordinatesSplit_snd (k m : ℕ) (t : Fin (k + m) → ℝ)
    (i : Fin m) :
    (finCoordinatesSplit k m t).2 i = t (Fin.natAdd k i) := rfl

/-- Replace the last block of finite coordinates by coordinates in the chosen complement. -/
noncomputable def frameCoordinates [FiniteDimensional ℝ X] (v : Fin k → X) :
    (Fin (k + Module.finrank ℝ ↥(frameComplement v)) → ℝ) ≃L[ℝ]
      ((Fin k → ℝ) × ↥(frameComplement v)) :=
  (finCoordinatesSplit k (Module.finrank ℝ ↥(frameComplement v))).trans
    ((ContinuousLinearEquiv.refl ℝ (Fin k → ℝ)).prodCongr
      (Module.finBasis ℝ ↥(frameComplement v)).equivFunL.symm)

@[simp] theorem frameCoordinates_single [FiniteDimensional ℝ X]
    (v : Fin k → X) (i : Fin k) (a : ℝ) :
    frameCoordinates v (Pi.single (Fin.castLE (Nat.le_add_right k
      (Module.finrank ℝ ↥(frameComplement v))) i) a) = (Pi.single i a, 0) := by
  classical
  let m := Module.finrank ℝ ↥(frameComplement v)
  have hsplit : finCoordinatesSplit k m
      (Pi.single (Fin.castLE (Nat.le_add_right k m) i) a) = (Pi.single i a, 0) := by
    apply Prod.ext
    · ext j
      simp only [finCoordinatesSplit_fst, Pi.single_apply]
      have heq : (Fin.castAdd m j = Fin.castLE (Nat.le_add_right k m) i) ↔ j = i := by
        exact ⟨fun h => Fin.ext (congrArg (fun u : Fin (k + m) => u.val) h),
          fun h => by subst h; rfl⟩
      simp only [heq]
    · ext j
      simp only [finCoordinatesSplit_snd, Pi.single_apply, Pi.zero_apply]
      have hne : Fin.natAdd k j ≠ Fin.castLE (Nat.le_add_right k m) i := by
        intro h
        have heq := congrArg Fin.val h
        simp only [Fin.val_natAdd, Fin.val_castLE] at heq
        omega
      simp only [hne, ↓reduceIte]
  change ((ContinuousLinearEquiv.refl ℝ (Fin k → ℝ)).prodCongr
    (Module.finBasis ℝ ↥(frameComplement v)).equivFunL.symm)
      (finCoordinatesSplit k m _) = _
  rw [hsplit]
  simp

end
