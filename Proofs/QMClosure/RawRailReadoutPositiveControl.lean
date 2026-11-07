import Proofs.QMClosure.RawRailReadoutBridge
import Proofs.QMClosure.RawNetworkMedialWall
import Proofs.QMClosure.OriginalGateProbabilityWall
import Proofs.QMClosure.ResponseSignatureControls

/-!
# A mathematical existence control for the physical rail contract

The fixed quadratic readout at t = 1/2 is supplied on the existing two-sector
model. Its source is not fixed by the diagonal involution. This establishes
consistency of the new contract, without asserting physical event semantics.
-/

namespace IDT.QMClosure.RawRailReadoutPositiveControl

noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

open ResponseContextQuotient NativeVacuumProbabilityFamily RawRailReadoutBridge
open RawDoubledNormalizationCompiler (duplicate)
open scoped BigOperators

abbrev V := OriginalGateProbabilityWall.V

def data : Data V V where
  chosenZero := 0
  operation := OriginalGateProbabilityWall.operation
  signature := id
  square p := by
    rw [OriginalGateProbabilityWall.operation_square]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  medial a b c d := by
    rw [OriginalGateProbabilityWall.operation_medial]
    intro q
    rfl

def Q : V → ℝ := OriginalGateProbabilityWall.quadratic (1 / 2)

theorem Q_zero : Q 0 = 0 := OriginalGateProbabilityWall.quadratic_zero _
theorem Q_reference : Q OriginalGateProbabilityWall.reference = 1 :=
  OriginalGateProbabilityWall.quadratic_reference _
theorem Q_nonnegative (x : V) : 0 ≤ Q x :=
  OriginalGateProbabilityWall.quadratic_nonnegative _ (by norm_num) (by norm_num) x
theorem Q_conserved (x y : V) :
    Q (data.operation (x,y)).1 + Q (data.operation (x,y)).2 = Q x + Q y :=
  OriginalGateProbabilityWall.quadratic_conserved _ x y

theorem duplicated_source_total {ι : Type} [Fintype ι] [DecidableEq ι] (s : ι) :
    (∑ w, Q (duplicate (ResponseNativeProbabilitySelection.basisInput data
      OriginalGateProbabilityWall.reference s) w)) = 2 := by
  norm_num [Fintype.sum_sum_type, duplicate, ResponseNativeProbabilitySelection.basisInput,
    apply_ite, Q_reference, show data.chosenZero = (0 : V) from rfl, Q_zero]

/-- A concrete supplied law on all raw words, normalized over both physical rails. -/
def law : RailLaw data OriginalGateProbabilityWall.reference where
  prob s c w := Q (rawPrepared data OriginalGateProbabilityWall.reference s c w) / 2
  nonnegative _ _ _ := div_nonneg (Q_nonnegative _) (by norm_num)
  normalized s c := by
    rw [← Finset.sum_div]
    change (∑ w, Q (WeightFreeRawProbability.evalRaw data.operation c
      (duplicate (ResponseNativeProbabilitySelection.basisInput data
        OriginalGateProbabilityWall.reference s)) w)) / 2 = 1
    rw [RawNetworkMedialWall.evalRaw_preserves_readout data.operation Q Q_conserved,
      duplicated_source_total]
    norm_num
  prepared_eq s c e h := by
    funext w
    have he : rawPrepared data OriginalGateProbabilityWall.reference s c w =
        rawPrepared data OriginalGateProbabilityWall.reference s e w :=
      ResponseContextQuotient.signature_eq (h w)
    rw [he]
  output_perm _ _ _ _ := rfl
  spectator_pair s c a b w hab hwa hwb := by
    simp only [rawPrepared, WeightFreeRawProbability.evalRaw, if_neg hwa, if_neg hwb]
  vacuum s c w := by rw [rawPrepared_railPad]

theorem railLaw_nonempty : Nonempty (RailLaw data OriginalGateProbabilityWall.reference) :=
  ⟨law⟩

theorem source_not_diagonal_fixed :
    OriginalGateProbabilityWall.diagonal OriginalGateProbabilityWall.reference ≠
      OriginalGateProbabilityWall.reference := by
  intro h
  have hh := congrArg Prod.snd h
  norm_num [OriginalGateProbabilityWall.diagonal, OriginalGateProbabilityWall.reference] at hh

theorem zero_diagonal_fixed : OriginalGateProbabilityWall.diagonal (0 : V) = 0 := by
  simp [OriginalGateProbabilityWall.diagonal]

theorem compiledLaw_nonempty :
    Nonempty (ResponseDoubledNormalizationCompiler.CompiledLaw data
      OriginalGateProbabilityWall.reference) := ⟨toCompiledLaw _ _ law⟩

end
end IDT.QMClosure.RawRailReadoutPositiveControl
