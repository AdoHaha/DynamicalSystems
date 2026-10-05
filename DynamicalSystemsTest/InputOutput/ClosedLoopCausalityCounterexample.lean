import DynamicalSystems.InputOutput.ClosedLoop
import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic.FinCases

/-!
# Global feedback well-posedness does not imply causality

There are two time instants, integer-valued signals, and counting measure.  Every signal is locally
`Lp`.  The encoder `(x₀, x₁) ↦ (x₀ / 2, 2 * x₁ + x₀ % 2)` moves one parity bit from the first
instant to the second while remaining causal and bijective.  Its inverse needs the second external
sample to reconstruct the first state sample.  Closing `G₁ = id` and `G₂ = encoder - id` realizes
this inverse.

Thus all original hypotheses of the unrepaired feedback-causality theorem hold, including global
existence and uniqueness and local `Lp` compatibility.  The closed loop is nevertheless noncausal;
the missing requirement is uniqueness of the truncated feedback equations.
-/

open Set MeasureTheory
open scoped ENNReal

namespace ClosedLoopCausalityCounterexample

noncomputable section

local instance : MetricSpace (Fin 2) :=
  MetricSpace.induced Fin.val Fin.val_injective inferInstance

abbrev Signal := Fin 2 → ℤ

/-- A causal bijection whose inverse is not causal. -/
def encoder (u : Signal) (t : Fin 2) : ℤ :=
  if t = 0 then u 0 / 2 else 2 * u 1 + u 0 % 2

def decoder (e : Signal) (t : Fin 2) : ℤ :=
  if t = 0 then 2 * e 0 + e 1 % 2 else e 1 / 2

theorem decoder_encoder (u : Signal) : decoder (encoder u) = u := by
  funext t
  fin_cases t <;> simp [decoder, encoder] <;> omega

theorem encoder_decoder (e : Signal) : encoder (decoder e) = e := by
  funext t
  fin_cases t <;> simp [decoder, encoder] <;> omega

def top : Signal → Signal := id

def bottom (u : Signal) : Signal := encoder u - u

def loop : SetRel.closedLoop (Fin 2) ℤ ℤ := ⟨top.graph, bottom.graph⟩

def prefixes (_ : Unit) : Set (Fin 2) := {0}

private theorem all_locallyLp {β E : Type*} [PseudoMetricSpace β] [MeasurableSpace β]
    [Finite β] [DiscreteMeasurableSpace β] [NormedAddCommGroup E] (u : β → E)
    (p : ℝ≥0∞) : MemLpLoc u p Measure.count :=
  MemLp.memLpLoc MemLp.of_discrete

theorem top_causal (p : ℝ≥0∞) : loop.topRel.IsCausal prefixes p Measure.count := by
  apply (Function.graph_isCausal_iff_isCausal (fun _ ↦ MeasurableSet.singleton 0)).mpr
  constructor
  · intro u _
    exact all_locallyLp _ p
  · intro t u _
    simp [top]

theorem bottom_causal (p : ℝ≥0∞) : loop.botRel.IsCausal prefixes p Measure.count := by
  apply (Function.graph_isCausal_iff_isCausal (fun _ ↦ MeasurableSet.singleton 0)).mpr
  constructor
  · intro u _
    exact all_locallyLp _ p
  · intro t u _
    funext x
    by_cases hx : x = 0
    · subst x
      simp [bottom, encoder]
    · simp [hx]

/-- The full feedback state is obtained by decoding the sum of external channels. -/
def state (e : Fin 2 → ℤ × ℤ) (t : Fin 2) : ℤ × ℤ :=
  (decoder (Prod.fst ∘ e + Prod.snd ∘ e) t - (e t).2,
    decoder (Prod.fst ∘ e + Prod.snd ∘ e) t)

theorem state_mem (e : Fin 2 → ℤ × ℤ) : (e, state e) ∈ loop.inputState := by
  constructor
  · change top (Prod.fst ∘ state e) = Prod.snd ∘ state e - Prod.snd ∘ e
    rfl
  · change bottom (Prod.snd ∘ state e) = Prod.fst ∘ e - Prod.fst ∘ state e
    have h : (Prod.snd ∘ state e) = decoder (Prod.fst ∘ e + Prod.snd ∘ e) := rfl
    unfold bottom
    rw [h, encoder_decoder]
    funext t
    dsimp [state]
    omega

theorem loop_isGraph : loop.inputState.IsGraph := by
  intro e
  refine ⟨state e, state_mem e, ?_⟩
  intro u hu
  have h₁ : Prod.fst ∘ u = Prod.snd ∘ u - Prod.snd ∘ e := hu.1
  have h₂ : encoder (Prod.snd ∘ u) - Prod.snd ∘ u =
      Prod.fst ∘ e - Prod.fst ∘ u := hu.2
  have henc : encoder (Prod.snd ∘ u) = Prod.fst ∘ e + Prod.snd ∘ e := by
    funext t
    have ha := congrFun h₁ t
    have hb := congrFun h₂ t
    dsimp at ha hb ⊢
    omega
  have hdec : Prod.snd ∘ u = decoder (Prod.fst ∘ e + Prod.snd ∘ e) := by
    rw [← henc, decoder_encoder]
  funext t
  apply Prod.ext
  · have ha := congrFun h₁ t
    have hd := congrFun hdec t
    dsimp [state] at ha hd ⊢
    omega
  · exact congrFun hdec t

theorem loop_locallyLpSolvable (p : ℝ≥0∞) : loop.LocallyLpSolvable p Measure.count := by
  intro e _
  exact ⟨state e, state_mem e, all_locallyLp _ p⟩

/-- External inputs agree at time zero; their second samples have different parity. -/
def external (b : ℤ) (t : Fin 2) : ℤ × ℤ :=
  (if t = 0 then 0 else b, 0)

theorem external_same_prefix :
    (prefixes ()).indicator (external 0) = (prefixes ()).indicator (external 1) := by
  funext t
  fin_cases t <;> simp [prefixes, external]

theorem state_at_zero (b : ℤ) : state (external b) 0 = (b % 2, b % 2) := by
  simp [state, decoder, external]

/-- The first state sample depends on the second external sample. -/
theorem loop_not_causal (p : ℝ≥0∞) : ¬ loop.inputState.IsCausal prefixes p Measure.count := by
  intro hc
  have h := hc.causal () (state_mem (external 0)) (state_mem (external 1))
    (all_locallyLp _ p) (all_locallyLp _ p) (all_locallyLp _ p) (all_locallyLp _ p)
    external_same_prefix
  have h0 := congrFun h 0
  norm_num [prefixes, state_at_zero] at h0


/-- The associated output also exposes the first decoded sample. -/
def output (e : Fin 2 → ℤ × ℤ) (t : Fin 2) : ℤ × ℤ :=
  ((state e t).1, bottom (Prod.snd ∘ state e) t)

theorem output_mem (e : Fin 2 → ℤ × ℤ) : (e, output e) ∈ loop.inputOutput := by
  apply SetRel.closedLoop.mem_inputOutput_of_mem_inputState (state_mem e)
    SetRel.isGraph_of_graph SetRel.isGraph_of_graph
  · rfl
  · rfl

theorem loop_output_not_causal (p : ℝ≥0∞) :
    ¬ loop.inputOutput.IsCausal prefixes p Measure.count := by
  intro hc
  have h := hc.causal () (output_mem (external 0)) (output_mem (external 1))
    (all_locallyLp _ p) (all_locallyLp _ p) (all_locallyLp _ p) (all_locallyLp _ p)
    external_same_prefix
  have h0 := congrArg (fun y ↦ (y 0).1) h
  norm_num [prefixes, output, state_at_zero] at h0

/-- The original theorem's assumptions are simultaneously satisfiable and its conclusion fails. -/
example (p : ℝ≥0∞) :
    loop.topRel.IsGraph ∧ loop.botRel.IsGraph ∧
      loop.topRel.IsCausal prefixes p Measure.count ∧
      loop.botRel.IsCausal prefixes p Measure.count ∧
      loop.inputState.IsGraph ∧ loop.LocallyLpSolvable p Measure.count ∧
      ¬ loop.inputState.IsCausal prefixes p Measure.count :=
  ⟨SetRel.isGraph_of_graph, SetRel.isGraph_of_graph, top_causal p, bottom_causal p,
    loop_isGraph, loop_locallyLpSolvable p, loop_not_causal p⟩

/-- The input-output version of the original claim fails for the same connection. -/
example (p : ℝ≥0∞) : loop.inputOutput.IsGraph ∧
    ¬ loop.inputOutput.IsCausal prefixes p Measure.count :=
  ⟨SetRel.closedLoop.isGraph_inputOutput SetRel.isGraph_of_graph SetRel.isGraph_of_graph
    loop_isGraph, loop_output_not_causal p⟩

#print axioms decoder_encoder
#print axioms encoder_decoder
#print axioms loop_isGraph
#print axioms loop_not_causal
#print axioms loop_output_not_causal

end

end ClosedLoopCausalityCounterexample
