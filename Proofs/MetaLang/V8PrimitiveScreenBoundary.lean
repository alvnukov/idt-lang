namespace IDT.MetaLang.V8.PrimitiveScreen

/-!
Research ledger for the fast, pre-proof candidate screen.

Python performs bounded exploratory computations, not Lean-certified experiment
execution. This ledger neither verifies the Python implementation nor promotes
its results to physical derivations. The existing experiment/proof authorities
are unchanged. The known controls are regression cases, not new discoveries.
-/

inductive ScreenOutcome where
  | counterexampleUnderStatedAssumptions
  | noCounterexampleWithinBounds
  | inconclusive
  | unsupported
deriving DecidableEq, Repr

inductive EvidenceKind where
  | boundedComputation
  | kernelCheckedMathematicalProof
  | empiricalComparison
deriving DecidableEq, Repr

def currentEvidenceKind : EvidenceKind := .boundedComputation

def currentCheckIds : List String := [
  "unit_weight", "event_nonnegative", "coefficient_third_difference",
  "self_composition", "signed_reference_composition"
]

inductive ImportedStructure where
  | rationalCoefficientCarrier
  | coefficientAddition
  | candidateWeightRule
  | indicatorEvents
  | pairKernelRepresentation
  | tensorMultiplication
  | normalizedSignedRankOneReferencesWithNonzeroSum
deriving DecidableEq, Repr

def kernelReferenceScreenImports : List ImportedStructure := [
  .rationalCoefficientCarrier, .candidateWeightRule, .indicatorEvents,
  .pairKernelRepresentation, .tensorMultiplication,
  .normalizedSignedRankOneReferencesWithNonzeroSum
]

inductive OpenObligation where
  | deriveOperationalSemanticsFromLowerPrimitives
  | deriveDetectorRecordAndProbabilityBridge
  | addIndependentExperimentalDataWithUncertainties
  | addBellAndCompositeDynamicsWithoutUnstatedImports
  | proveSelectedSurvivingStatementsInLean
  | establishContinuumAndComplexCarrierScope
  | reconstructStandardModelAndGravity
deriving DecidableEq, Repr

def nextObligations : List OpenObligation := [
  .deriveOperationalSemanticsFromLowerPrimitives,
  .deriveDetectorRecordAndProbabilityBridge,
  .addIndependentExperimentalDataWithUncertainties,
  .addBellAndCompositeDynamicsWithoutUnstatedImports,
  .proveSelectedSurvivingStatementsInLean,
  .establishContinuumAndComplexCarrierScope,
  .reconstructStandardModelAndGravity
]

-- No mathematical proof or empirical result is inferred from an outcome tag.
def outcomeEvidence (_ : ScreenOutcome) : EvidenceKind := .boundedComputation

end IDT.MetaLang.V8.PrimitiveScreen
