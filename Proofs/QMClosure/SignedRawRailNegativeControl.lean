import Proofs.QMClosure.SignedRawRailReadoutBridge
import Proofs.QMClosure.RawRailReadoutPositiveControl

/-!
# A globally bounded signed physical-rail countermodel

The two supplied reference occurrences and every output rail are retained.
The conserved quadratic at t = -1 satisfies the five signed structural fields
at all finite widths, and its total absolute rail weight is at most three on
every raw word. A literal left-only original word nevertheless gives a negative
rail value. This is a mathematical control, with no preparation availability,
independence, event actualization, or physical probability interpretation.
-/

namespace IDT.QMClosure.SignedRawRailNegativeControl

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open ResponseContextQuotient NativeVacuumProbabilityFamily RawRailReadoutBridge
open MixerGeneratedProcessWall
open RawDoubledNormalizationCompiler (duplicate)
open scoped BigOperators

abbrev V := OriginalGateProbabilityWall.V
abbrev data := RawRailReadoutPositiveControl.data
abbrev reference := OriginalGateProbabilityWall.reference

def Q : V → ℝ := OriginalGateProbabilityWall.quadratic (-1)

theorem Q_zero : Q 0 = 0 := OriginalGateProbabilityWall.quadratic_zero _
theorem Q_reference : Q reference = 1 := OriginalGateProbabilityWall.quadratic_reference _
theorem Q_conserved (x y : V) :
    Q (data.operation (x,y)).1 + Q (data.operation (x,y)).2 = Q x + Q y :=
  OriginalGateProbabilityWall.quadratic_conserved _ x y

/-- Each quadratic has reference value one, independently of its parameter. -/
theorem duplicated_source_total (t : ℝ)
    {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) :
    (∑ w, OriginalGateProbabilityWall.quadratic t
      (duplicate (ResponseNativeProbabilitySelection.basisInput data reference s) w)) = 2 := by
  norm_num [Fintype.sum_sum_type, duplicate, ResponseNativeProbabilitySelection.basisInput,
    apply_ite, OriginalGateProbabilityWall.quadratic_reference,
    show data.chosenZero = (0 : V) from rfl, OriginalGateProbabilityWall.quadratic_zero]

/-- The original physical-rail structural contract with nonnegativity omitted. -/
def law : SignedRawRailReadoutBridge.SignedRailLaw data reference where
  prob s c w := Q (rawPrepared data reference s c w) / 2
  normalized s c := by
    rw [← Finset.sum_div]
    change (∑ w, Q (WeightFreeRawProbability.evalRaw data.operation c
      (duplicate (ResponseNativeProbabilitySelection.basisInput data reference s)) w)) / 2 = 1
    rw [RawNetworkMedialWall.evalRaw_preserves_readout data.operation Q Q_conserved]
    change (∑ w, OriginalGateProbabilityWall.quadratic (-1)
      (duplicate (ResponseNativeProbabilitySelection.basisInput data reference s) w)) / 2 = 1
    rw [duplicated_source_total]
    norm_num
  prepared_eq s c e h := by
    funext w
    have he : rawPrepared data reference s c w = rawPrepared data reference s e w :=
      ResponseContextQuotient.signature_eq (h w)
    rw [he]
  output_perm _ _ _ _ := rfl
  spectator_pair s c a b w hab hwa hwb := by
    simp only [rawPrepared, WeightFreeRawProbability.evalRaw, if_neg hwa, if_neg hwb]
  vacuum s c w := by rw [rawPrepared_railPad]

/-- Both complex-sector norm totals are exactly two, on every raw word. -/
theorem sector_totals {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native (ι ⊕ ι)) :
    (∑ w, Complex.normSq (rawPrepared data reference s c w).1) = 2 ∧
    (∑ w, Complex.normSq (rawPrepared data reference s c w).2) = 2 := by
  have h (t : ℝ) :
      (∑ w, OriginalGateProbabilityWall.quadratic t
        (rawPrepared data reference s c w)) = 2 := by
    unfold rawPrepared
    rw [RawNetworkMedialWall.evalRaw_preserves_readout data.operation
      (OriginalGateProbabilityWall.quadratic t)
      (OriginalGateProbabilityWall.quadratic_conserved t), duplicated_source_total]
  constructor
  · simpa [OriginalGateProbabilityWall.quadratic] using h 1
  · simpa [OriginalGateProbabilityWall.quadratic] using h 0

theorem abs_half_Q_le (x : V) :
    |Q x / 2| ≤ Complex.normSq x.1 / 2 + Complex.normSq x.2 := by
  have hp := Complex.normSq_nonneg x.1
  have hm := Complex.normSq_nonneg x.2
  simp only [Q, OriginalGateProbabilityWall.quadratic]
  apply abs_le.mpr
  constructor <;> nlinarith

/-- One width-independent bound covers all raw words and all retained rails. -/
theorem total_absolute_rail_weight_le_three
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native (ι ⊕ ι)) :
    (∑ w, |law.prob s c w|) ≤ 3 := by
  obtain ⟨hp, hm⟩ := sector_totals s c
  calc
    _ ≤ ∑ w, (Complex.normSq (rawPrepared data reference s c w).1 / 2 +
        Complex.normSq (rawPrepared data reference s c w).2) := by
      apply Finset.sum_le_sum
      intro w _
      exact abs_half_Q_le _
    _ = (∑ w, Complex.normSq (rawPrepared data reference s c w).1) / 2 +
        ∑ w, Complex.normSq (rawPrepared data reference s c w).2 := by
      rw [Finset.sum_add_distrib, Finset.sum_div]
    _ = 3 := by rw [hp, hm]; norm_num

/-- The same bound covers the selected physical descendants at every depth. -/
theorem eventwiseBoundedVariation :
    SignedRawRailReadoutBridge.EventwiseBoundedVariation data reference law := by
  intro ι _ _ s c i
  refine ⟨3, ?_⟩
  intro k _
  exact SignedRawRailReadoutBridge.selectedVariation_le_global_bound data reference law 3
    (fun s c => total_absolute_rail_weight_le_three s c) s c i k

/-- Forget only the original additive evaluator's gate annotation. -/
def originalNative {ι : Type} : OriginalGateProbabilityWall.Original ι → Native ι
  | .identity => .identity
  | .pair i j hij => .pair i j hij
  | .permute e => .permute e
  | .seq c e => .seq (originalNative c) (originalNative e)

/-- An explicit bridge between the original and literal raw evaluators. -/
theorem evalRaw_originalNative {ι : Type} [Fintype ι] [DecidableEq ι]
    (c : OriginalGateProbabilityWall.Original ι) (x : ι → V) :
    WeightFreeRawProbability.evalRaw data.operation (originalNative c) x = c.eval x := by
  induction c generalizing x with
  | identity => rfl
  | pair i j hij => rfl
  | permute e => rfl
  | seq c e hc he =>
    simp only [originalNative, WeightFreeRawProbability.evalRaw]
    rw [he, hc]
    rfl

def leftWitness : Native ((Fin 3) ⊕ (Fin 3)) :=
  NativeVacuumProbabilityFamily.padCircuit (Fin 3)
    (originalNative OriginalGateProbabilityWall.witness)

/-- Chronological order is 01, 02, 12, acting exclusively on the left rails. -/
theorem leftWitness_literal : leftWitness =
    .seq (.seq (.pair (.inl 0) (.inl 1) (by decide))
      (.pair (.inl 0) (.inl 2) (by decide)))
      (.pair (.inl 1) (.inl 2) (by decide)) := rfl

/-- The right supplied source is untouched; the left array is the old witness. -/
theorem leftWitness_prepared : rawPrepared data reference (0 : Fin 3) leftWitness =
    Sum.elim (OriginalGateProbabilityWall.witness.eval
      (OriginalGateProbabilityWall.source 0)) (OriginalGateProbabilityWall.source 0) := by
  have hb : ResponseNativeProbabilitySelection.basisInput data reference (0 : Fin 3) =
      OriginalGateProbabilityWall.source 0 := by
    funext i
    simp [ResponseNativeProbabilitySelection.basisInput,
      OriginalGateProbabilityWall.source, single, data, RawRailReadoutPositiveControl.data]
  unfold rawPrepared leftWitness
  rw [hb, ReferenceOccurrenceCompilation.evalRaw_padCircuit]
  change Sum.elim (WeightFreeRawProbability.evalRaw data.operation
    (originalNative OriginalGateProbabilityWall.witness)
    (OriginalGateProbabilityWall.source 0)) (OriginalGateProbabilityWall.source 0) = _
  rw [evalRaw_originalNative]

/-- No positivity-dependent original probability theorem is used here. -/
theorem leftWitness_negative_value :
    law.prob (0 : Fin 3) leftWitness (.inl 1) = -3 / 16 := by
  change Q (rawPrepared data reference (0 : Fin 3) leftWitness (.inl 1)) / 2 = _
  rw [leftWitness_prepared]
  change OriginalGateProbabilityWall.quadratic (-1)
    (OriginalGateProbabilityWall.witness.eval (OriginalGateProbabilityWall.source 0) 1) / 2 = _
  unfold OriginalGateProbabilityWall.quadratic
  rw [OriginalGateProbabilityWall.witness_plus_weight,
    OriginalGateProbabilityWall.witness_minus_weight]
  norm_num

/-- Global absolute boundedness does not imply raw physical-rail positivity. -/
theorem globally_bounded_with_negative_rail :
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι]
      (s : ι) (c : Native (ι ⊕ ι)), (∑ w, |law.prob s c w|) ≤ 3) ∧
    law.prob (0 : Fin 3) leftWitness (.inl 1) < 0 := by
  refine ⟨fun s c => total_absolute_rail_weight_le_three s c, ?_⟩
  rw [leftWitness_negative_value]
  norm_num

end
end IDT.QMClosure.SignedRawRailNegativeControl
