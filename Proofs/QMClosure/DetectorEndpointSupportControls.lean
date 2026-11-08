import Proofs.QMClosure.DetectorEndpointSupportWall
import Proofs.QMClosure.DetectorConservationOmissionControls

/-!
Endpoint rigidity allows unequal strictly interior responses. Omitting the
support premise permits exact zero/one discrimination for distinct Dirac laws.
-/
namespace IDT.QMClosure.DetectorEndpointSupportControls

noncomputable section
open MeasureTheory InformationTheory
open InvariantEffectReadoutBridge DetectorEffectOperations
open DetectorConservationOmissionControls
open scoped ENNReal

/-- A single event detector on the existing positive finite-KL family. -/
def positiveEvent : Effect Bool := indicator {true} (measurableSet_singleton true)

theorem positiveEvent_response_zero :
    positiveEvent.acceptance (positivePreparation 0) = 1 / 3 := by
  norm_num [positiveEvent, acceptance_indicator, positivePreparation,
    Effect.binaryKernel, boolEffect, labelClass]

theorem positiveEvent_response_one :
    positiveEvent.acceptance (positivePreparation 1) = 2 / 3 := by
  norm_num [positiveEvent, acceptance_indicator, positivePreparation,
    Effect.binaryKernel, boolEffect, labelClass]

/-- Finite KL and a common detector coexist with unequal interior responses. -/
theorem finiteEntropy_nonconstant_response :
    (∀ x y, klDiv (positivePreparation x) (positivePreparation y) ≠ ∞) ∧
      positiveEvent.acceptance (positivePreparation 0) ≠
        positiveEvent.acceptance (positivePreparation 1) := by
  refine ⟨positivePreparation_kl_ne_top, ?_⟩
  rw [positiveEvent_response_zero, positiveEvent_response_one]
  norm_num

/-- The sharp singleton detector on the existing point preparations. -/
def diracEvent : Effect Label := indicator {0} (measurableSet_singleton 0)

theorem diracEvent_response_zero : diracEvent.acceptance (diracPreparation 0) = 1 := by
  simp [diracEvent, dirac_acceptance, indicator]

theorem diracEvent_response_one : diracEvent.acceptance (diracPreparation 1) = 0 := by
  norm_num [diracEvent, dirac_acceptance, indicator]

/-- Exact endpoint separation occurs outside the finite directed-KL premise. -/
theorem dirac_endpoint_separation :
    diracEvent.acceptance (diracPreparation 0) = 1 ∧
      diracEvent.acceptance (diracPreparation 1) = 0 ∧
      klDiv (diracPreparation 0) (diracPreparation 1) = ∞ :=
  ⟨diracEvent_response_zero, diracEvent_response_one,
    diracPreparation_kl_top (by decide)⟩

end
end IDT.QMClosure.DetectorEndpointSupportControls
