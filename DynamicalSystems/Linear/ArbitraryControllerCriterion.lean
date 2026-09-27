/-
Copyright (c) 2026 Igor Zubrycki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Zubrycki
-/
module

public import DynamicalSystems.Linear.GenericControllerDualResponse
public import DynamicalSystems.Linear.KalmanDecomposition

/-! # Stable external response with arbitrary controller state

For a strictly proper finite-dimensional real plant, existence of a dynamic
controller with any finite-dimensional real state space and decaying external
time-domain response is equivalent to the two geometric inclusions of
Corollary 6.22 for the Hurwitz (left-half-plane) stability choice. Equivalence
between this decay predicate and the book's transfer-function stability
predicate, or a formulation for an arbitrary stability domain, is not
established here.
The necessity proof extracts the first inclusion from the plant trajectory
and obtains the second by transposing the explicit closed-loop readout.
-/

@[expose] public section

open Filter
open scoped Topology

universe u

namespace LinearSystem

variable {X U Y D Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
variable [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z]

/-- Any finite-dimensional dynamic controller with a decaying external
time-domain response forces both Corollary 6.22 geometric inclusions. The controller state
space is existentially quantified and need not equal the plant state space. -/
theorem externalStabilizationConditions_of_anyStateStableExternalResponse
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : AnyStateStableExternalResponse sys hD E H) :
    ExternalStabilizationConditions sys E H := by
  have hfirst : LinearMap.range E ≤ outputStabilizableSubspace sys.A sys.B H :=
    first_inclusion_of_anyStateStableExternalResponse sys hD E H h
  obtain ⟨W, hW1, hW2, hW3, ctrl, hdec⟩ := h
  letI : NormedAddCommGroup W := hW1
  letI : NormedSpace ℝ W := hW2
  letI : FiniteDimensional ℝ W := hW3
  let ic : DynamicInterconnection ℝ X U Y W D Z :=
    genericZeroFInterconnection sys ctrl E H
  let icD : DynamicInterconnection ℝ (Module.Dual ℝ X) (Module.Dual ℝ Y)
      (Module.Dual ℝ U) (Module.Dual ℝ W) (Module.Dual ℝ Z) (Module.Dual ℝ D) :=
    genericDualInterconnection sys ctrl E H
  let hwp : ic.IsWellPosed := ic.isWellPosed_of_D_eq_zero hD
  let hwpD : icD.IsWellPosed := icD.isWellPosed_of_D_eq_zero (dual_D_eq_zero sys hD)
  have hdec' : ∀ d : D, Tendsto
      (fun t : ℝ => ic.outputMap
        (NormedSpace.exp (t • (ic.closedLoopMap hwp).toContinuousLinearMap)
          (ic.disturbanceMap d))) atTop (nhds 0) := by
    intro d
    have hfun : (fun t : ℝ => ic.externalResponse hwp t d) =
        fun t : ℝ => ic.outputMap
          (NormedSpace.exp (t • (ic.closedLoopMap hwp).toContinuousLinearMap)
            (ic.disturbanceMap d)) := by
      funext t
      rw [ic.externalResponse_apply hwp t d, ic.closedLoopSystem_expFlow_eq hwp t]
      rw [ic.disturbanceMapWithF_of_F_eq_zero hwp (by rfl)]
    rw [← hfun]
    simpa [ic, hwp] using hdec d
  have htrans := dualReadout_tendsto_of_readout_tendsto
    (ic.closedLoopMap hwp) ic.disturbanceMap ic.outputMap hdec'
  have hdecD : ∀ z : Module.Dual ℝ Z, Tendsto
      (fun t : ℝ => icD.outputMap
        (NormedSpace.exp (t • (icD.closedLoopMap hwpD).toContinuousLinearMap)
          (icD.disturbanceMap z))) atTop (nhds 0) := by
    intro z
    convert htrans z using 1
    funext t
    exact genericW_dualExplicitResponse sys hD ctrl E H ic icD rfl rfl hwp hwpD t z
  have hdualRange : LinearMap.range H.dualMap ≤
      outputStabilizableSubspace sys.A.dualMap sys.C.dualMap E.dualMap := by
    simpa [dual_A, dual_B] using
      (firstInclusion_of_explicitReadout sys.dual (dual_D_eq_zero sys hD)
        H.dualMap E.dualMap ctrl.dual icD rfl hwpD hdecD)
  exact ⟨hfirst, secondInclusion_of_dual_range_le sys E H hdualRange⟩

/-- The time-domain stable-external-response criterion corresponding to
Corollary 6.22 for arbitrary finite-dimensional controller state and Hurwitz
stability. The transfer-function formulation is not identified with this
predicate. -/
theorem anyStateStableExternalResponse_iff_externalStabilizationConditions
    (sys : LinearSystem ℝ X U Y) (hD : sys.D = 0)
    (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    AnyStateStableExternalResponse sys hD E H ↔
      ExternalStabilizationConditions sys E H := by
  constructor
  · exact externalStabilizationConditions_of_anyStateStableExternalResponse sys hD E H
  · exact anyStateStableExternalResponse_of_externalStabilizationConditions sys hD E H

/-- A finite-dimensional channel has a decaying impulse readout in every input
direction exactly when its input range is contained in the sum of the
unobservable and Hurwitz spectral subspaces. This is a time-domain spectral
criterion, not yet a statement about poles of a rational transfer function. -/
theorem channelReadout_tendsto_iff_range_le_unobservable_sup_hurwitz
    (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    (∀ d : D, Tendsto
      (fun t : ℝ => H (NormedSpace.exp (t • A.toContinuousLinearMap) (E d)))
      atTop (nhds 0)) ↔
      LinearMap.range E ≤
        LinearMap.unobservableSubspace H A ⊔ LinearMap.hurwitzSubspace A := by
  constructor
  · intro hdec
    change ∀ y, y ∈ LinearMap.range E →
      y ∈ LinearMap.unobservableSubspace H A ⊔ LinearMap.hurwitzSubspace A
    intro y hy
    obtain ⟨d, rfl⟩ := LinearMap.mem_range.mp hy
    have hs := mem_outputStabilizableSubspace_of_decay_of_B_eq_zero
      (U := D) A H
      (fun x hx h => LinearMap.antistable_readout_forces_unobservable A H hx h)
      (hdec d)
    rw [outputStabilizableSubspace_zero_eq_sup_unobservableSubspace] at hs
    simpa [sup_comm] using hs
  · intro hrange d
    have hEd : E d ∈ LinearMap.unobservableSubspace H A ⊔
        LinearMap.hurwitzSubspace A :=
      hrange (LinearMap.mem_range_self E d)
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hEd
    have hu0 : ∀ t : ℝ, H (NormedSpace.exp (t • A.toContinuousLinearMap) u) = 0 :=
      fun t => readout_exp_eq_zero_of_mem_unobservableSubspace A H hu t
    have hvdec := tendsto_readout_exp_of_mem_hurwitzSubspace A H hv
    have hsum : ∀ t : ℝ,
        H (NormedSpace.exp (t • A.toContinuousLinearMap) (E d)) =
          H (NormedSpace.exp (t • A.toContinuousLinearMap) u) +
            H (NormedSpace.exp (t • A.toContinuousLinearMap) v) := by
      intro t
      rw [← huv, map_add, map_add]
    have heq : (fun t : ℝ =>
        H (NormedSpace.exp (t • A.toContinuousLinearMap) (E d))) =
        fun t => H (NormedSpace.exp (t • A.toContinuousLinearMap) v) := by
      funext t
      rw [hsum t, hu0 t, zero_add]
    rw [heq]
    exact hvdec

/-- A Hurwitz controllable–observable realization gives a decaying impulse
readout for the original channel, even when the original state map has
unreachable or unobservable non-Hurwitz modes. -/
theorem channelReadout_tendsto_of_isHurwitz_minimalRealization
    (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (h : LinearMap.IsHurwitz
      (LinearMap.controllableObservableRealization A E H 0).A)
    (d : D) :
    Tendsto (fun t : ℝ => H (NormedSpace.exp (t • A.toContinuousLinearMap) (E d)))
      atTop (nhds 0) := by
  let V := LinearMap.reachableUnobservable A E H
  let W := LinearMap.reachableSubspace A E
  have hW : Submodule.map A W ≤ W := LinearMap.map_reachableSubspace_le A E
  have hV : Submodule.map A V ≤ V := LinearMap.map_reachableUnobservable_le A E H
  have hVH : V ≤ LinearMap.ker H := by
    intro x hx
    exact LinearMap.unobservableSubspace_le_ker H A hx.2
  have hE : LinearMap.range E ≤ W := LinearMap.range_le_reachableSubspace A E
  apply tendsto_readout_exp_of_isHurwitz_mapQ_on A H E V W hW hV hVH hE
  exact h

private theorem channel_decay_imp_reachable_le_unobservable_sup_hurwitz
    (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (hdec : ∀ d : D, Tendsto
      (fun t : ℝ => H (NormedSpace.exp (t • A.toContinuousLinearMap) (E d)))
      atTop (nhds 0)) :
    LinearMap.reachableSubspace A E ≤
      LinearMap.unobservableSubspace H A ⊔ LinearMap.hurwitzSubspace A := by
  have hE : LinearMap.range E ≤
      LinearMap.unobservableSubspace H A ⊔ LinearMap.hurwitzSubspace A :=
    (channelReadout_tendsto_iff_range_le_unobservable_sup_hurwitz A E H).mp hdec
  apply LinearMap.reachableSubspace_le A E hE
  rw [Submodule.map_sup]
  exact sup_le
    ((LinearMap.map_unobservableSubspace_le H A).trans le_sup_left)
    ((LinearMap.map_hurwitzSubspace_le A).trans le_sup_right)

private theorem channel_decay_on_reachable
    (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (hdec : ∀ d : D, Tendsto
      (fun t : ℝ => H (NormedSpace.exp (t • A.toContinuousLinearMap) (E d)))
      atTop (nhds 0))
    (w : LinearMap.reachableSubspace A E) :
    Tendsto (fun t : ℝ => H (NormedSpace.exp (t • A.toContinuousLinearMap) (w : X)))
      atTop (nhds 0) := by
  have hW := channel_decay_imp_reachable_le_unobservable_sup_hurwitz A E H hdec
  have hSub : LinearMap.range (LinearMap.reachableSubspace A E).subtype ≤
      LinearMap.unobservableSubspace H A ⊔ LinearMap.hurwitzSubspace A := by
    rintro x ⟨y, rfl⟩
    exact hW y.2
  exact (channelReadout_tendsto_iff_range_le_unobservable_sup_hurwitz
    A (LinearMap.reachableSubspace A E).subtype H).mpr hSub w

/-- Decay of every channel impulse response forces the controllable–observable
realization to be Hurwitz. The converse to
`channelReadout_tendsto_of_isHurwitz_minimalRealization` relies on observability
to rule out antistable modes after restricting to the reachable space and
quotienting by its unobservable part. -/
theorem isHurwitz_minimalRealization_of_channelReadout_tendsto
    (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z)
    (hdec : ∀ d : D, Tendsto
      (fun t : ℝ => H (NormedSpace.exp (t • A.toContinuousLinearMap) (E d)))
      atTop (nhds 0)) :
    LinearMap.IsHurwitz (LinearMap.controllableObservableRealization A E H 0).A := by
  let W := LinearMap.reachableSubspace A E
  let I := LinearMap.reachableIntersection A E H
  let M := LinearMap.controllableObservableRealization A E H 0
  let AW := LinearMap.reachableRestrictionA A E
  haveI : IsClosed (I : Set W) := I.closed_of_finiteDimensional
  let q : W →L[ℝ] W ⧸ I := I.mkQ.toContinuousLinearMap
  letI : IsTopologicalRing (W →L[ℝ] W) :=
    { continuous_add := continuous_add
      continuous_mul := Continuous.clm_comp continuous_fst continuous_snd
      continuous_neg := continuous_neg }
  letI : IsTopologicalRing ((W ⧸ I) →L[ℝ] (W ⧸ I)) :=
    { continuous_add := continuous_add
      continuous_mul := Continuous.clm_comp continuous_fst continuous_snd
      continuous_neg := continuous_neg }
  have hq : q.comp AW.toContinuousLinearMap = M.A.toContinuousLinearMap.comp q := by
    ext y
    exact LinearMap.controllableObservableRealization_A_mkQ A E H 0 y
  have hsub : W.subtype.toContinuousLinearMap.comp AW.toContinuousLinearMap =
      A.toContinuousLinearMap.comp W.subtype.toContinuousLinearMap := by
    ext y
    rfl
  have hminread (y : W ⧸ I) : Tendsto
      (fun t : ℝ => M.C (NormedSpace.exp (t • M.A.toContinuousLinearMap) y))
      atTop (nhds 0) := by
    obtain ⟨w, rfl⟩ := I.mkQ_surjective y
    have hsame : (fun t : ℝ => M.C
        (NormedSpace.exp (t • M.A.toContinuousLinearMap) (I.mkQ w))) =
        (fun t : ℝ => H (NormedSpace.exp (t • A.toContinuousLinearMap) (w : X))) := by
      funext t
      have hqflow := clm_map_exp_smul q AW.toContinuousLinearMap
        M.A.toContinuousLinearMap hq t w
      have hwflow := clm_map_exp_smul W.subtype.toContinuousLinearMap
        AW.toContinuousLinearMap A.toContinuousLinearMap hsub t w
      change M.C (NormedSpace.exp (t • M.A.toContinuousLinearMap) (q w)) =
        H (NormedSpace.exp (t • A.toContinuousLinearMap) (w : X))
      rw [← hqflow]
      change M.C (I.mkQ (NormedSpace.exp (t • AW.toContinuousLinearMap) w)) = _
      rw [LinearMap.controllableObservableRealization_C_mkQ]
      exact congrArg H hwflow
    rw [hsame]
    exact channel_decay_on_reachable A E H hdec w
  have hobs : LinearMap.IsObservable M.C M.A :=
    LinearMap.isObservable_controllableObservableRealization A E H 0
  have hU : LinearMap.unstableSubspace M.A = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro y hy
    have hyN := LinearMap.antistable_readout_forces_unobservable M.A M.C hy (hminread y)
    change LinearMap.unobservableSubspace M.C M.A = ⊥ at hobs
    rw [hobs, Submodule.mem_bot] at hyN
    exact hyN
  exact LinearMap.isHurwitz_of_unstableSubspace_eq_bot M.A hU

/-- For a finite-dimensional real channel, the controllable–observable
realization is Hurwitz exactly when every impulse-response direction decays.
Unlike Hurwitzness of the original state map, this criterion allows unstable
unreachable or unobservable modes. It does not yet identify rational transfer
function poles with the eigenvalues of the minimal realization. -/
theorem isHurwitz_minimalRealization_iff_channelReadout_tendsto
    (A : X →ₗ[ℝ] X) (E : D →ₗ[ℝ] X) (H : X →ₗ[ℝ] Z) :
    LinearMap.IsHurwitz (LinearMap.controllableObservableRealization A E H 0).A ↔
      ∀ d : D, Tendsto
        (fun t : ℝ => H (NormedSpace.exp (t • A.toContinuousLinearMap) (E d)))
        atTop (nhds 0) := by
  constructor
  · intro h d
    exact channelReadout_tendsto_of_isHurwitz_minimalRealization A E H h d
  · exact isHurwitz_minimalRealization_of_channelReadout_tendsto A E H

end LinearSystem
