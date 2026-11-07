import Proofs.QMClosure.RawRailVacuumExtensionWall
import Proofs.QMClosure.ResponseDoubledNormalizationCompiler
import Proofs.QMClosure.RawRailReadoutBridge
import Proofs.QMClosure.ResponseSignatureControls

/-!
# A logical compiled law without the broad original-rail law

On supplied complex coordinates the original operation is the native mixer
followed by componentwise `x ↦ 1 - x`. Its diagonal normalization is the native
mixer. The original zero and source stay 0 and 1. The existing doubled logical
contract has a canonical inhabitant, whereas the four-field physical two-source
rail contract is impossible: the original gate sends (1,1) to (0,0).
No raw squared-norm conservation, uncoded single-source law, physical encoding
availability, reconstructed-group identification, or QM closure is claimed.
-/

namespace IDT.QMClosure.AffineRawRailExtensionControl

noncomputable section
open WeightFreeRawProbability NativeVacuumProbabilityFamily
open ResponseContextQuotient MedialSwapRoot
open NativeMixerEventConeExclusion (mixer)

def operation (p : ℂ × ℂ) : ℂ × ℂ := (1, 1) - mixer p

theorem mixer_complement (p : ℂ × ℂ) :
    mixer ((1, 1) - p) = (1, 1) - mixer p := by
  rw [map_sub, NativeMixerEventConeExclusion.mixer_transparent]

theorem operation_square (p : ℂ × ℂ) : operation (operation p) = p.swap := by
  unfold operation
  rw [mixer_complement, NativeMixerEventConeExclusion.mixer_square]
  abel

theorem operation_diagonal (x : ℂ) : operation (x, x) = (1 - x, 1 - x) := by
  simp [operation, NativeMixerEventConeExclusion.mixer_transparent]

theorem operation_medial (a b c d : ℂ) :
    MedialSwapRoot.firstChannel operation
      (MedialSwapRoot.firstChannel operation a b)
      (MedialSwapRoot.firstChannel operation c d) =
    MedialSwapRoot.firstChannel operation
      (MedialSwapRoot.firstChannel operation a c)
      (MedialSwapRoot.firstChannel operation b d) := by
  simp only [MedialSwapRoot.firstChannel, operation, Prod.fst_sub,
    NativeAttenuationCircuit.mixer_fst]
  ring

def rawData : RawOperationalData ℂ where
  chosenZero := 0
  operation := operation
  square := operation_square
  medial := operation_medial

theorem diagonal (x : ℂ) :
    DiagonalNormalization.diagonal (MedialSwapRoot.firstChannel operation) x = 1 - x :=
  congrArg Prod.fst (operation_diagonal x)

theorem normalizedOperation_eq_mixer : rawData.normalizedOperation = mixer := by
  funext p
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · change DiagonalNormalization.diagonal (MedialSwapRoot.firstChannel operation)
      (operation (x, y)).1 = (mixer (x, y)).1
    rw [diagonal]
    simp [operation]
  · change DiagonalNormalization.diagonal (MedialSwapRoot.firstChannel operation)
      (operation (y, x)).1 = (mixer (x, y)).2
    rw [diagonal]
    simp only [operation, Prod.fst_sub, sub_sub_cancel,
      NativeAttenuationCircuit.mixer_fst, NativeAttenuationCircuit.mixer_snd]
    ring

theorem source_pair_zero : operation (1, 1) = (0, 0) := by
  simpa using operation_diagonal 1

theorem no_twoSourceLaw :
    ¬ Nonempty (RawRailVacuumExtensionWall.TwoSourceLaw operation (0 : ℂ) 1) :=
  RawRailVacuumExtensionWall.no_law_of_source_pair_zero operation 0 1 source_pair_zero

/-- The full response signature is identity; all contexts remain in scope. -/
def data : Data ℂ ℂ where
  chosenZero := 0
  operation := operation
  signature := id
  square p := by
    constructor
    · apply (ResponseSignatureControls.identity_responseEq_iff_eq _ _ _).mpr
      exact congrArg Prod.fst (operation_square p)
    · apply (ResponseSignatureControls.identity_responseEq_iff_eq _ _ _).mpr
      exact congrArg Prod.snd (operation_square p)
  medial a b c d :=
    (ResponseSignatureControls.identity_responseEq_iff_eq _ _ _).mpr
      (operation_medial a b c d)

theorem responseEq_iff_eq (x y : ℂ) :
    ResponseEq data.operation data.signature x y ↔ x = y :=
  ResponseSignatureControls.identity_responseEq_iff_eq operation x y

/-- Literal whole-array simulation is available in this identity-response control. -/
theorem encodedPrepared_eq_duplicate {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι) (c : Native ι) :
    ResponseDoubledNormalizationCompiler.encodedPrepared data 1 s c =
      RawDoubledNormalizationCompiler.duplicate (c.eval (source s)) := by
  change evalRaw rawData.operation (RawDoubledNormalizationCompiler.compileWord c)
    (RawDoubledNormalizationCompiler.duplicate (source s)) = _
  rw [RawDoubledNormalizationCompiler.evalRaw_compileWord_rawData,
    normalizedOperation_eq_mixer, ResponseSignatureControls.evalRaw_native]

/-- An inhabitant of the existing six-field logical contract, with all
probabilities and the five other fields copied from the canonical scalar law. -/
def compiledLaw : ResponseDoubledNormalizationCompiler.CompiledLaw data 1 where
  prob := canonicalLaw.prob
  nonnegative := canonicalLaw.nonnegative
  normalized := canonicalLaw.normalized
  prepared_eq s c e h := by
    apply canonicalLaw.prepared_eq s c e
    apply RawDoubledNormalizationCompiler.duplicate_injective
    change RawDoubledNormalizationCompiler.duplicate (c.eval (source s)) =
      RawDoubledNormalizationCompiler.duplicate (e.eval (source s))
    rw [← encodedPrepared_eq_duplicate s c, ← encodedPrepared_eq_duplicate s e]
    funext w
    exact (responseEq_iff_eq _ _).mp (h w)
  output_perm := canonicalLaw.output_perm
  spectator_pair := canonicalLaw.spectator_pair
  vacuum := canonicalLaw.vacuum

theorem compiledLaw_nonempty :
    Nonempty (ResponseDoubledNormalizationCompiler.CompiledLaw data 1) := ⟨compiledLaw⟩

/-- The criterion concerns the original quotient reference, without asserting
that the reconstructed additive group is literally the supplied complex group. -/
theorem original_quotient_reference_infiniteOrder :
    WeightFreeRawProbability.ReferenceInfiniteOrder data.quotientData (data.classOf 1) :=
  (ResponseDoubledNormalizationCompiler.law_nonempty_iff_reference_infiniteOrder data 1).mp
    compiledLaw_nonempty

theorem logical_law_and_original_rail_wall :
    Nonempty (ResponseDoubledNormalizationCompiler.CompiledLaw data 1) ∧
      ¬ Nonempty (RawRailVacuumExtensionWall.TwoSourceLaw operation (0 : ℂ) 1) :=
  ⟨compiledLaw_nonempty, no_twoSourceLaw⟩

/-- This is the bridge's exact all-raw-word rail contract on supplied doubled
single-basis inputs. It differs from the generic law's arbitrary two-source
positions; its own Fin 1 doubled witness still has two physical input rails. -/
theorem no_railLaw : ¬ Nonempty (RawRailReadoutBridge.RailLaw data 1) := by
  apply RawRailReadoutBridge.no_law_of_source_pair_zero data (1 : ℂ)
  exact source_pair_zero

/-- The existing logical compiled law is inhabited while the exact bridge
physical-rail extension contract for the same data and source is impossible. -/
theorem compiled_law_and_no_railLaw :
    Nonempty (ResponseDoubledNormalizationCompiler.CompiledLaw data 1) ∧
      ¬ Nonempty (RawRailReadoutBridge.RailLaw data 1) :=
  ⟨compiledLaw_nonempty, no_railLaw⟩

end
end IDT.QMClosure.AffineRawRailExtensionControl
