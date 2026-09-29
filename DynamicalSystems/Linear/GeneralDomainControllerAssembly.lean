/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.GeneralDomainInvariantPair
public import DynamicalSystems.Linear.GeneralDomainSpectrum
public import DynamicalSystems.Linear.GeneralDomainQuotientFeedback

/-! # Controller spectral assembly for a general stability domain

The observer-based controller has two diagonal spectral blocks after the
controller-state/error coordinate change. Domain-relative geometric
subspaces identify the block quotients that govern its external transfer.
-/

@[expose] public section

noncomputable section

universe u

namespace LinearSystem

variable {X U Y Z D : Type u}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]
variable [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]

/-- State-feedback spectral block on the geometric quotient `W_Cg / V*`. -/
abbrev stateFeedbackQuotientMapIn (Cg : Set ℂ)
    (sys : LinearSystem ℝ X U Y) (H : X →ₗ[ℝ] Z) (F : X →ₗ[ℝ] U)
    (hF : Submodule.map (sys.A + sys.B.comp F) (Vstar sys H) ≤ Vstar sys H) :
    (WIn Cg sys H) ⧸ (Vstar sys H).comap (WIn Cg sys H).subtype →ₗ[ℝ]
      (WIn Cg sys H) ⧸ (Vstar sys H).comap (WIn Cg sys H).subtype :=
  let W := WIn Cg sys H
  let V := Vstar sys H
  let hW : ∀ x ∈ W, (sys.A + sys.B.comp F) x ∈ W := fun x hx ↦
    LinearMap.map_add_feedback_sup_stabilizableSubspaceIn_le Cg sys.A sys.B F hF
      ⟨x, hx, rfl⟩
  Submodule.mapQ (V.comap W.subtype) (V.comap W.subtype)
    ((sys.A + sys.B.comp F).restrict hW)
    (fun x hx ↦ hF ⟨(x : X), hx, rfl⟩)

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z] in
/-- The geometric controlled-invariant subspace admits a feedback gain
stabilizing its domain-relative quotient. -/
theorem exists_stateFeedbackQuotientMapIn_isStableIn
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (sys : LinearSystem ℝ X U Y) (H : X →ₗ[ℝ] Z) :
    ∃ F : X →ₗ[ℝ] U,
      ∃ hF : Submodule.map (sys.A + sys.B.comp F) (Vstar sys H) ≤ Vstar sys H,
        LinearMap.IsStableIn Cg (stateFeedbackQuotientMapIn Cg sys H F hF) := by
  have hV : Submodule.map sys.A (Vstar sys H) ≤
      Vstar sys H ⊔ LinearMap.range sys.B :=
    LinearMap.isControlledInvariant_controlledInvariantSubspace
      sys.A sys.B (LinearMap.ker H)
  obtain ⟨F, ⟨hF, hQ⟩⟩ :=
    LinearMap.exists_feedback_isStableIn_quotient_of_geometricCondition
      Cg hCg sys.A sys.B (Vstar sys H) hV
  exact ⟨F, hF, hQ⟩

/-- Observer-error spectral block on the geometric quotient `S* / T_Cg`. -/
abbrev observerErrorQuotientMapIn (Cg : Set ℂ)
    (sys : LinearSystem ℝ X U Y) (E : D →ₗ[ℝ] X) (G : Y →ₗ[ℝ] X)
    (hG : Submodule.map (sys.A + G.comp sys.C) (Sstar sys E) ≤ Sstar sys E) :
    (Sstar sys E) ⧸ (TIn Cg sys E).comap (Sstar sys E).subtype →ₗ[ℝ]
      (Sstar sys E) ⧸ (TIn Cg sys E).comap (Sstar sys E).subtype :=
  let S := Sstar sys E
  let T := TIn Cg sys E
  let hTkerC : T ≤ LinearMap.ker sys.C :=
    inf_le_right.trans
      (inf_le_left.trans (LinearMap.unobservableSubspace_le_ker sys.C sys.A))
  let hAT : Submodule.map sys.A T ≤ T :=
    LinearMap.map_conditionedInvariant_inf_detectableSubspaceIn_le Cg sys.C sys.A E
  let hNT : ∀ x ∈ T, (sys.A + G.comp sys.C) x ∈ T := by
    intro x hx
    have hCx : sys.C x = 0 := LinearMap.mem_ker.mp (hTkerC hx)
    simpa [LinearMap.add_apply, LinearMap.comp_apply, hCx] using hAT ⟨x, hx, rfl⟩
  Submodule.mapQ (T.comap S.subtype) (T.comap S.subtype)
    ((sys.A + G.comp sys.C).restrict (fun x hx ↦ hG ⟨x, hx, rfl⟩))
    (fun x hx ↦ hNT (x : X) hx)

/-- The domain-relative extended-pair quotient of the closed-loop state map. -/
abbrev closedLoopPairQuotientMapIn (Cg : Set ℂ)
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : ExternalStabilizationConditionsIn Cg sys E H)
    (F : X →ₗ[ℝ] U) (G : Y →ₗ[ℝ] X)
    (hF : Submodule.map (sys.A + sys.B.comp F) (Vstar sys H) ≤ Vstar sys H)
    (hG : Submodule.map (sys.A + G.comp sys.C) (Sstar sys E) ≤ Sstar sys E)
    (hwp : (cabPairInterconnection sys (cabPairController sys F G 0) E H).IsWellPosed) :
    let Ve := extendedPairSubspace (TIn Cg sys E) (Vstar sys H)
    let We := extendedPairSubspace (Sstar sys E) (WIn Cg sys H)
    We ⧸ Ve.comap We.subtype →ₗ[ℝ] We ⧸ Ve.comap We.subtype :=
  let Ve := extendedPairSubspace (TIn Cg sys E) (Vstar sys H)
  let We := extendedPairSubspace (Sstar sys E) (WIn Cg sys H)
  let ic := cabPairInterconnection sys (cabPairController sys F G 0) E H
  let hmain := extendedPairSubspaces_of_externalStabilizationConditionsIn
    Cg sys hD E H h F G hF hG hwp
  Submodule.mapQ (Ve.comap We.subtype) (Ve.comap We.subtype)
    ((ic.closedLoopMap hwp).restrict (fun x hx ↦ hmain.2.2.1 ⟨x, hx, rfl⟩))
    (fun x hx ↦ hmain.2.1 ⟨(x : X × X), hx, rfl⟩)

set_option maxHeartbeats 1000000 in
-- Elaborating the nested quotient conjugacy unfolds several subtype and mapQ equivalences.
omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ Y]
    [FiniteDimensional ℝ Z] [FiniteDimensional ℝ D] in
/-- The two `Cg`-stable feedback and observer quotients give a `Cg`-stable
quotient of the actual closed-loop map on the extended invariant pair. -/
theorem isStableIn_closedLoopPairQuotientMapIn_of_blocks
    (Cg : Set ℂ) (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : ExternalStabilizationConditionsIn Cg sys E H)
    (F : X →ₗ[ℝ] U) (G : Y →ₗ[ℝ] X)
    (hF : Submodule.map (sys.A + sys.B.comp F) (Vstar sys H) ≤ Vstar sys H)
    (hG : Submodule.map (sys.A + G.comp sys.C) (Sstar sys E) ≤ Sstar sys E)
    (hwp : (cabPairInterconnection sys (cabPairController sys F G 0) E H).IsWellPosed)
    (hFq : LinearMap.IsStableIn Cg (stateFeedbackQuotientMapIn Cg sys H F hF))
    (hGq : LinearMap.IsStableIn Cg (observerErrorQuotientMapIn Cg sys E G hG)) :
    LinearMap.IsStableIn Cg
      (closedLoopPairQuotientMapIn Cg sys hD E H h F G hF hG hwp) := by
  let ic := cabPairInterconnection sys (cabPairController sys F G 0) E H
  let V := Vstar sys H
  let W := WIn Cg sys H
  let S := Sstar sys E
  let T := TIn Cg sys E
  let Ve := extendedPairSubspace T V
  let We := extendedPairSubspace S W
  have hmain := extendedPairSubspaces_of_externalStabilizationConditionsIn
    Cg sys hD E H h F G hF hG hwp
  have hVW : V ≤ W := le_sup_left
  have hTS : T ≤ S := inf_le_left
  have hAW : ∀ x ∈ W, (sys.A + sys.B.comp F) x ∈ W := fun x hx ↦
    LinearMap.map_add_feedback_sup_stabilizableSubspaceIn_le Cg sys.A sys.B F hF
      ⟨x, hx, rfl⟩
  have hAS : ∀ y ∈ S, (sys.A + G.comp sys.C) y ∈ S := fun y hy ↦ hG ⟨y, hy, rfl⟩
  have hSW : S ≤ W := Sstar_le_WIn_of_externalStabilizationConditionsIn Cg sys E H h
  have hAWinv : Submodule.map sys.A W ≤ W :=
    LinearMap.map_sup_stabilizableSubspaceIn_le Cg sys.A sys.B
      (LinearMap.isControlledInvariant_controlledInvariantSubspace
        sys.A sys.B (LinearMap.ker H))
  have hBS : ∀ y ∈ S, (-(G.comp sys.C)) y ∈ W := by
    intro y hy
    have hAy : sys.A y ∈ W := hAWinv ⟨y, hSW hy, rfl⟩
    have hNy : (sys.A + G.comp sys.C) y ∈ W := hSW (hAS y hy)
    have hEq : (-(G.comp sys.C)) y = sys.A y - (sys.A + G.comp sys.C) y := by
      simp [LinearMap.add_apply, LinearMap.comp_apply]
    rw [hEq]
    exact W.sub_mem hAy hNy
  have hAV : ∀ x ∈ V, (sys.A + sys.B.comp F) x ∈ V := fun x hx ↦ hF ⟨x, hx, rfl⟩
  have hAT : Submodule.map sys.A T ≤ T :=
    LinearMap.map_conditionedInvariant_inf_detectableSubspaceIn_le Cg sys.C sys.A E
  have hTker : T ≤ LinearMap.ker sys.C :=
    inf_le_right.trans
      (inf_le_left.trans (LinearMap.unobservableSubspace_le_ker sys.C sys.A))
  have hNT : ∀ y ∈ T, (sys.A + G.comp sys.C) y ∈ T := by
    intro y hy
    have hCy : sys.C y = 0 := LinearMap.mem_ker.mp (hTker hy)
    simpa [LinearMap.add_apply, LinearMap.comp_apply, hCy] using hAT ⟨y, hy, rfl⟩
  have hBT : ∀ y ∈ T, (-(G.comp sys.C)) y ∈ V := by
    intro y hy
    have hCy : sys.C y = 0 := LinearMap.mem_ker.mp (hTker hy)
    simp [LinearMap.comp_apply, hCy]
  have hconj : (controllerStateErrorEquiv (𝕜 := ℝ) X).conj (ic.closedLoopMap hwp) =
      LinearMap.blockOperator₂ (sys.A + sys.B.comp F) (-(G.comp sys.C))
        (sys.A + G.comp sys.C) := by
    rw [cabPairController_closedLoopMap_controllerStateError_conj sys hD E H F G hwp]
    exact (LinearMap.blockOperator₂_self (sys.A + sys.B.comp F) (-(G.comp sys.C))
      (sys.A + G.comp sys.C)).symm
  have hTarget : LinearMap.IsStableIn Cg
      (Submodule.mapQ
        ((V.prod T).comap (W.prod S).subtype)
        ((V.prod T).comap (W.prod S).subtype)
        ((LinearMap.blockOperator₂ (sys.A + sys.B.comp F) (-(G.comp sys.C))
            (sys.A + G.comp sys.C)).restrict
          (LinearMap.prodInvariance (sys.A + sys.B.comp F) (-(G.comp sys.C))
            (sys.A + G.comp sys.C) W S hAW hAS hBS))
        (LinearMap.prodRestrictInvariance (sys.A + sys.B.comp F) (-(G.comp sys.C))
          (sys.A + G.comp sys.C) W S V T hAW hAS hBS hAV hNT hBT)) := by
    apply LinearMap.isStableIn_mapQ_prod_restrict_of_isStableIn
      Cg (sys.A + sys.B.comp F) (-(G.comp sys.C)) (sys.A + G.comp sys.C)
      W S V T hVW hTS hAW hAS hBS hAV hNT hBT
    · simpa only [stateFeedbackQuotientMapIn, W, V] using hFq
    · simpa only [observerErrorQuotientMapIn, S, T] using hGq
  have hPmap : Submodule.map (controllerStateErrorEquiv (𝕜 := ℝ) X :
        (X × X) →ₗ[ℝ] (X × X)) Ve = V.prod T := by
    simpa [Ve] using controllerStateErrorEquiv_map_extendedPairSubspace
      (𝕜 := ℝ) T V
  have hQmap : Submodule.map (controllerStateErrorEquiv (𝕜 := ℝ) X :
        (X × X) →ₗ[ℝ] (X × X)) We = W.prod S := by
    simpa [We] using controllerStateErrorEquiv_map_extendedPairSubspace
      (𝕜 := ℝ) S W
  have hP2Q2 : V.prod T ≤ W.prod S := Submodule.prod_mono hVW hTS
  have hQ2 : ∀ y ∈ W.prod S,
      (LinearMap.blockOperator₂ (sys.A + sys.B.comp F) (-(G.comp sys.C))
        (sys.A + G.comp sys.C)) y ∈ W.prod S :=
    LinearMap.prodInvariance (sys.A + sys.B.comp F) (-(G.comp sys.C))
      (sys.A + G.comp sys.C) W S hAW hAS hBS
  have hP2 : ∀ y ∈ V.prod T,
      (LinearMap.blockOperator₂ (sys.A + sys.B.comp F) (-(G.comp sys.C))
        (sys.A + G.comp sys.C)) y ∈ V.prod T :=
    LinearMap.prodInvariance (sys.A + sys.B.comp F) (-(G.comp sys.C))
      (sys.A + G.comp sys.C) V T hAV hNT hBT
  exact (LinearMap.isStableIn_mapQ_nested_conj Cg
    (ic.closedLoopMap hwp)
    (LinearMap.blockOperator₂ (sys.A + sys.B.comp F) (-(G.comp sys.C))
      (sys.A + G.comp sys.C))
    (controllerStateErrorEquiv (𝕜 := ℝ) X) hconj
    Ve We hmain.1
    (fun x hx ↦ hmain.2.2.1 ⟨x, hx, rfl⟩)
    (fun x hx ↦ hmain.2.1 ⟨x, hx, rfl⟩)
    (V.prod T) (W.prod S) hP2Q2 hQ2 hP2 hPmap hQmap).mpr hTarget

omit [FiniteDimensional ℝ U] [FiniteDimensional ℝ Y] in
/-- Given feedback and observer gains that stabilize the two geometric
quotients in `Cg`, the book's observer-based controller has external transfer
poles only in `Cg`. -/
theorem externalPolesIn_of_geometricQuotientGains
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : ExternalStabilizationConditionsIn Cg sys E H)
    (F : X →ₗ[ℝ] U) (G : Y →ₗ[ℝ] X)
    (hF : Submodule.map (sys.A + sys.B.comp F) (Vstar sys H) ≤ Vstar sys H)
    (hG : Submodule.map (sys.A + G.comp sys.C) (Sstar sys E) ≤ Sstar sys E)
    (hFq : LinearMap.IsStableIn Cg (stateFeedbackQuotientMapIn Cg sys H F hF))
    (hGq : LinearMap.IsStableIn Cg (observerErrorQuotientMapIn Cg sys E G hG)) :
    AnyStateWellPosedExternalPolesIn Cg sys E 0 H := by
  let ctrl : DynamicController ℝ X Y U := cabPairController sys F G 0
  let ic := cabPairInterconnection sys ctrl E H
  have hwp : ic.IsWellPosed := ic.isWellPosed_of_D_eq_zero hD
  let Ve := extendedPairSubspace (TIn Cg sys E) (Vstar sys H)
  let We := extendedPairSubspace (Sstar sys E) (WIn Cg sys H)
  have hmain := extendedPairSubspaces_of_externalStabilizationConditionsIn
    Cg sys hD E H h F G hF hG hwp
  have hSpec : LinearMap.IsStableIn Cg
      (closedLoopPairQuotientMapIn Cg sys hD E H h F G hF hG hwp) :=
    isStableIn_closedLoopPairQuotientMapIn_of_blocks
      Cg sys hD E H h F G hF hG hwp hFq hGq
  have hPole : MinimalRealizationAllChannelsPolesIn Cg
      (ic.closedLoopMap hwp) (ic.disturbanceMapWithF hwp) ic.outputMap := by
    rw [ic.disturbanceMapWithF_of_F_eq_zero hwp rfl]
    exact LinearMap.minimalRealizationAllChannelsPolesIn_of_invariantPair
      Cg hCg (ic.closedLoopMap hwp) ic.disturbanceMap ic.outputMap
      Ve We hmain.1 hmain.2.1 hmain.2.2.1 hmain.2.2.2.1 hmain.2.2.2.2 hSpec
  exact ⟨X, inferInstance, inferInstance, inferInstance, ctrl, hwp, hPole⟩

end LinearSystem
