/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.GeneralDomainNecessity
public import DynamicalSystems.Linear.GeneralDomainExtendedPair

/-! # Transfer poles from an invariant subspace pair

An invariant pair `P ≤ Q` containing the disturbance image in `Q` and
annihilating `P` at the readout gives a stable transfer channel whenever the
intermediate quotient `Q ⧸ P` has spectrum in the selected stability domain.
This is the domain-independent spectral core of the sufficiency half of
Trentelman–Stoorvogel–Hautus Lemma 6.21.
-/

@[expose] public section

noncomputable section

namespace LinearMap

variable {X D Z : Type*}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-- An invariant window with `Cg`-stable quotient has transfer poles only in
`Cg`. The ambient state map need not be stable. -/
theorem minimalRealizationAllChannelsPolesIn_of_invariantPair
    (Cg : Set ℂ) (hCg : IsStabilityDomain Cg)
    (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (P Q : Submodule ℝ X) (_hPQ : P ≤ Q)
    (hP : Submodule.map A P ≤ P) (hQ : Submodule.map A Q ≤ Q)
    (hE : LinearMap.range E ≤ Q) (hH : P ≤ LinearMap.ker H)
    (hSpec : IsStableIn Cg
      (Submodule.mapQ (P.comap Q.subtype) (P.comap Q.subtype)
        (A.restrict (fun x hx ↦ hQ ⟨x, hx, rfl⟩))
        (fun x hx ↦ hP ⟨(x : X), hx, rfl⟩))) :
    LinearSystem.MinimalRealizationAllChannelsPolesIn Cg A E H := by
  have hQinv : ∀ x ∈ Q, A x ∈ Q := fun x hx ↦ hQ ⟨x, hx, rfl⟩
  have hPq : ∀ x ∈ P.comap Q.subtype,
      (A.restrict hQinv) x ∈ P.comap Q.subtype := fun x hx ↦
    hP ⟨(x : X), hx, rfl⟩
  have hR : reachableSubspace A E ≤ Q := reachableSubspace_le A E hE hQ
  have hPobs : P ≤ unobservableSubspace H A := le_unobservableSubspace H A hH hP
  apply (minimalRealizationAllChannelsPolesIn_iff_reachable_inf_antistable_le
    Cg hCg A E H).mpr
  intro x hx
  have hxQ : x ∈ Q := hR hx.1
  obtain ⟨y, hy, hxy⟩ :=
    antistableSubspaceIn_inf_le_map_antistableSubspaceIn_restrict
      Cg hCg A Q hQinv ⟨hx.2, hxQ⟩
  have hyP : y ∈ P.comap Q.subtype :=
    antistableSubspaceIn_le_of_isStableIn_quotient
      Cg (A.restrict hQinv) (P.comap Q.subtype) hPq hSpec hy
  have hxP : x ∈ P := by
    rw [← hxy]
    exact hyP
  exact hPobs hxP

end LinearMap
