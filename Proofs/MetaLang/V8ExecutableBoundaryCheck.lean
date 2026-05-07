import Proofs.MetaLang.V8AcceptedDocumentInventory
import Proofs.MetaLang.V8CurrentStopReadiness

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 executable boundary check.

This module contains the Lean-side invariants mirrored by
`lake exe idt_v8_protocol_status -- --check-boundary`.
-/

structure ExecutableBoundarySnapshot where
  acceptedDocumentCount : Nat
  verificationDisciplineTheorems : Nat
  manifestInputTotal : Nat
  symbolInputs : Nat
  equationInputs : Nat
  derivationInputs : Nat
  finiteGateInputs : Nat
  residualQmExperiments : Nat
  qmUniversalPatternInputs : Nat
  qmCoreObligationInputs : Nat
  theoremCardInputs : Nat
  theoremCardFormalProofs : Nat
  qmObligationFormalProofs : Nat
  qmExperimentFormalProofs : Nat
  physicalFormalProofs : Nat
  qmFormalProofs : Nat

def currentExecutableBoundarySnapshot : ExecutableBoundarySnapshot :=
  {
    acceptedDocumentCount := currentAcceptedV8DocumentInventory.documentCount,
    verificationDisciplineTheorems :=
      currentFormalProofScopeCounts.verificationDiscipline,
    manifestInputTotal := currentV8ManifestCollectionCounts.total,
    symbolInputs := currentV8ManifestCollectionCounts.symbols,
    equationInputs := currentV8ManifestCollectionCounts.equations,
    derivationInputs := currentV8ManifestCollectionCounts.derivations,
    finiteGateInputs := currentV8ManifestCollectionCounts.finiteGates,
    residualQmExperiments :=
      currentExperimentProgramArchitecture.residualLedger.length,
    qmUniversalPatternInputs := currentV8ManifestCollectionCounts.qmUniversalPatterns,
    qmCoreObligationInputs := currentV8ManifestCollectionCounts.qmCoreProofObligations,
    theoremCardInputs := currentV8ManifestCollectionCounts.theoremCards,
    theoremCardFormalProofs := theoremCardFormalProofCount,
    qmObligationFormalProofs := qmCoreObligationFormalProofCount,
    qmExperimentFormalProofs := qmExperimentResidualFormalProofCount,
    physicalFormalProofs := currentFormalProofScopeCounts.physicalTheory,
    qmFormalProofs := currentFormalProofScopeCounts.qmClosure
  }

def ExecutableBoundarySnapshot.matchesCurrentBoundary
    (snapshot : ExecutableBoundarySnapshot) : Prop :=
  snapshot.acceptedDocumentCount = 9
    ∧ snapshot.verificationDisciplineTheorems = 273
    ∧ snapshot.manifestInputTotal = 596
    ∧ snapshot.symbolInputs = 178
    ∧ snapshot.equationInputs = 15
    ∧ snapshot.derivationInputs = 81
    ∧ snapshot.finiteGateInputs = 247
    ∧ snapshot.residualQmExperiments = 35
    ∧ snapshot.qmUniversalPatternInputs = 6
    ∧ snapshot.qmCoreObligationInputs = 11
    ∧ snapshot.theoremCardInputs = 23
    ∧ snapshot.theoremCardFormalProofs = 0
    ∧ snapshot.qmObligationFormalProofs = 0
    ∧ snapshot.qmExperimentFormalProofs = 0
    ∧ snapshot.physicalFormalProofs = 0
    ∧ snapshot.qmFormalProofs = 0

theorem current_executable_boundary_snapshot_matches :
    currentExecutableBoundarySnapshot.matchesCurrentBoundary := by
  unfold ExecutableBoundarySnapshot.matchesCurrentBoundary
  simp [
    currentExecutableBoundarySnapshot,
    currentAcceptedV8DocumentInventory,
    acceptedV8DocumentCount,
    acceptedV8DocumentIds,
    currentV8ManifestCollectionCounts,
    ManifestCollectionCounts.total,
    currentFormalProofScopeCounts,
    currentExperimentProgramArchitecture,
    currentQmExperimentResidualLedger,
    theoremCardFormalProofCount,
    qmCoreObligationFormalProofCount,
    qmExperimentResidualFormalProofCount,
  ]

end V8
end MetaLang
end IDT
