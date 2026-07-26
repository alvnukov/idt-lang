import Mathlib

namespace IDT.QMClosure

/-!
# Two-postulate QM reconstruction import audit

This ledger audits the substrate relevance of arXiv:2605.23217v1, “Two
Operational Principles Single Out Quantum Theory” (submitted 2026-05-22).
The paper's theorem is a potentially strong finite-dimensional reconstruction
target: local equivalence plus equivalent-system (ES) purification selects
standard finite-dimensional complex quantum theory inside a causal OPT.

It is not yet a derivation from the current IDT lower base.  The causal OPT
framework already supplies twelve operational, probabilistic, compositional,
topological, and finite-dimensional assumptions.  The current lower search has
only partial structural analogues for four of them and derives none of them with
their full operational semantics.

The audit also records the real-quantum separator.  Real quantum theory has
ordinary positive probabilities and is reported to satisfy ES purification, but
fails local equivalence/local tomography.  The qubit dimension mismatch is
checked below in Lean.  Therefore positive probability scalars plus ES
purification alone do not select complex quantum theory.

This file audits assumptions and a finite dimension obstruction.  It does not
kernel-check the 29-page external reconstruction proof or promote that preprint
to an IDT formal proof.
-/

inductive CausalOptAmbientAssumption where
  | systemsFiniteTestsAndTransformations
  | trivialSystemIsFiniteProbabilityDistributions
  | serialParallelIdentityAssociativityUnitInterchange
  | probabilityCompositionIsMultiplication
  | ancillaryOperationalEquality
  | deterministicEffectForEverySystem
  | normalizedStatesAndProbabilityScaling
  | coarseGrainingClosure
  | conditionedTests
  | finiteDimensionalClosedStateSpaces
  | nontrivialInformationalDimension
  | compositeSwapEquivalence
deriving DecidableEq, Repr

inductive LowerBaseEvidenceStatus where
  | derivedFromLowerPrimitives
  | partialStructuralAnalogue
  | importedFromCausalOptFramework
deriving DecidableEq, Repr

structure AmbientAssumptionAuditEntry where
  assumption : CausalOptAmbientAssumption
  status : LowerBaseEvidenceStatus
  boundary : String
deriving Repr

def twoPostulateAmbientAssumptionAudit : List AmbientAssumptionAuditEntry :=
  [
    {
      assumption := .systemsFiniteTestsAndTransformations
      status := .partialStructuralAnalogue
      boundary := "typed rewrites resemble transformations, but finite tests and outcome semantics are not derived"
    },
    {
      assumption := .trivialSystemIsFiniteProbabilityDistributions
      status := .importedFromCausalOptFramework
      boundary := "the full nonnegative real probability simplex is not derived from lower rewrites"
    },
    {
      assumption := .serialParallelIdentityAssociativityUnitInterchange
      status := .partialStructuralAnalogue
      boundary := "composition laws have finite models, but the physical tensor and test semantics are not uniquely selected"
    },
    {
      assumption := .probabilityCompositionIsMultiplication
      status := .importedFromCausalOptFramework
      boundary := "multiplicative probability scalars are not derived"
    },
    {
      assumption := .ancillaryOperationalEquality
      status := .importedFromCausalOptFramework
      boundary := "equality under arbitrary ancillary systems is an operational framework rule"
    },
    {
      assumption := .deterministicEffectForEverySystem
      status := .partialStructuralAnalogue
      boundary := "discard exists in the process probe, but determinism and operational uniqueness are not derived"
    },
    {
      assumption := .normalizedStatesAndProbabilityScaling
      status := .importedFromCausalOptFramework
      boundary := "normalization and the decomposition of every state as p times a normalized state are not derived"
    },
    {
      assumption := .coarseGrainingClosure
      status := .importedFromCausalOptFramework
      boundary := "addition of outcomes and convex closure are not lower-level consequences"
    },
    {
      assumption := .conditionedTests
      status := .importedFromCausalOptFramework
      boundary := "classical control and conditioning on outcomes are not derived"
    },
    {
      assumption := .finiteDimensionalClosedStateSpaces
      status := .importedFromCausalOptFramework
      boundary := "finite dimensionality and topological closure are assumed and do not cover continuum QFT"
    },
    {
      assumption := .nontrivialInformationalDimension
      status := .importedFromCausalOptFramework
      boundary := "existence of a system with two distinguishable states is not derived from the empty lower base"
    },
    {
      assumption := .compositeSwapEquivalence
      status := .partialStructuralAnalogue
      boundary := "symmetric parallel composition is a candidate structural analogue, not yet a physical derivation"
    }
  ]

def ambientAssumptionStatusCount
    (status : LowerBaseEvidenceStatus)
    (entries : List AmbientAssumptionAuditEntry) : Nat :=
  (entries.filter fun entry => entry.status == status).length

theorem two_postulate_route_has_twelve_ambient_assumptions :
    twoPostulateAmbientAssumptionAudit.length = 12 := by
  rfl

theorem current_lower_base_fully_derives_no_ambient_assumption :
    ambientAssumptionStatusCount
      .derivedFromLowerPrimitives twoPostulateAmbientAssumptionAudit = 0 := by
  rfl

theorem current_lower_base_has_four_partial_structural_analogues :
    ambientAssumptionStatusCount
      .partialStructuralAnalogue twoPostulateAmbientAssumptionAudit = 4 := by
  rfl

theorem eight_causal_opt_assumptions_remain_imported :
    ambientAssumptionStatusCount
      .importedFromCausalOptFramework twoPostulateAmbientAssumptionAudit = 8 := by
  rfl

inductive ReconstructionSelectorPostulate where
  | localEquivalence
  | equivalentSystemPurification
deriving DecidableEq, Repr

structure SelectorPostulateAuditEntry where
  postulate : ReconstructionSelectorPostulate
  status : LowerBaseEvidenceStatus
  boundary : String
deriving Repr

def twoPostulateSelectorAudit : List SelectorPostulateAuditEntry :=
  [
    {
      postulate := .localEquivalence
      status := .importedFromCausalOptFramework
      boundary := "local input-output statistics identifying channels is not derived from boundary extensionality"
    },
    {
      postulate := .equivalentSystemPurification
      status := .importedFromCausalOptFramework
      boundary := "existence and reversible uniqueness of same-capacity purifications are not derived"
    }
  ]

theorem both_reconstruction_selectors_remain_lower_base_imports :
    twoPostulateSelectorAudit.length = 2 ∧
      twoPostulateSelectorAudit.all
        (fun entry => entry.status == .importedFromCausalOptFramework) = true := by
  constructor <;> rfl

def realQuantumObservableDimension (levels : Nat) : Nat :=
  levels * (levels + 1) / 2

def complexQuantumObservableDimension (levels : Nat) : Nat :=
  levels ^ 2

def LocallyTomographicAtQubits (dimension : Nat → Nat) : Prop :=
  dimension 4 = dimension 2 * dimension 2

theorem real_quantum_qubits_fail_local_tomography_dimension :
    ¬ LocallyTomographicAtQubits realQuantumObservableDimension := by
  change ¬ (10 = 9)
  decide

theorem real_quantum_qubit_pair_has_one_latent_parameter :
    realQuantumObservableDimension 4 =
      realQuantumObservableDimension 2 *
        realQuantumObservableDimension 2 + 1 := by
  rfl

theorem complex_quantum_qubits_pass_local_tomography_dimension :
    LocallyTomographicAtQubits complexQuantumObservableDimension := by
  rfl

inductive ExternalEvidenceKind where
  | primarySourceStatementNotLeanProof
  | leanCheckedFiniteConsequence
deriving DecidableEq, Repr

structure ExternalEvidenceAnchor where
  id : String
  kind : ExternalEvidenceKind
  locator : String
  claimBoundary : String
deriving Repr

def twoPostulateExternalEvidence : List ExternalEvidenceAnchor :=
  [
    {
      id := "nakahira_two_postulate_preprint_v1"
      kind := .primarySourceStatementNotLeanProof
      locator := "https://arxiv.org/abs/2605.23217v1"
      claimBoundary := "conditional theorem inside a finite-dimensional causal OPT; submitted arXiv v1, not an IDT formal proof"
    },
    {
      id := "probabilistic_theories_with_purification"
      kind := .primarySourceStatementNotLeanProof
      locator := "https://arxiv.org/abs/0908.1583"
      claimBoundary := "purification supplies reversible dilation and information-processing structure, not complex-QM uniqueness by itself"
    },
    {
      id := "real_quantum_limited_holism"
      kind := .primarySourceStatementNotLeanProof
      locator := "https://arxiv.org/abs/1005.4870"
      claimBoundary := "real quantum theory is bilocally but not locally tomographic"
    },
    {
      id := "real_qubit_dimension_check"
      kind := .leanCheckedFiniteConsequence
      locator := "Proofs/QMClosure/TwoPostulateReconstructionImportAudit.lean"
      claimBoundary := "K_R(4)=10 differs from K_R(2)^2=9"
    }
  ]

inductive PrimitiveRouteStatus where
  | rejectedAsSufficient
  | conditionalExternalReconstructionTarget
  | derivedFromLowerPrimitives
deriving DecidableEq, Repr

def positiveScalarsPlusEsPurificationStatus : PrimitiveRouteStatus :=
  .rejectedAsSufficient

def causalOptLocalEquivalenceEsPurificationStatus : PrimitiveRouteStatus :=
  .conditionalExternalReconstructionTarget

theorem positive_scalars_and_es_purification_are_not_current_complex_selector :
    positiveScalarsPlusEsPurificationStatus = .rejectedAsSufficient := by
  rfl

theorem full_two_postulate_route_is_conditional_not_lower_derived :
    causalOptLocalEquivalenceEsPurificationStatus =
      .conditionalExternalReconstructionTarget := by
  rfl

inductive TwoPostulateRouteOpenObligation where
  | independentlyAuditExternalPreprintProof
  | deriveCausalOptFrameworkFromLowerPrimitives
  | deriveLocalEquivalenceFromBoundarySemantics
  | deriveEquivalentSystemPurificationUniversally
  | justifyOrRemoveFiniteDimensionality
  | extendFiniteQuantumReconstructionToRelativisticQftAndStandardModel
deriving DecidableEq, Repr

def twoPostulateRouteOpenObligations : List TwoPostulateRouteOpenObligation :=
  [ .independentlyAuditExternalPreprintProof,
    .deriveCausalOptFrameworkFromLowerPrimitives,
    .deriveLocalEquivalenceFromBoundarySemantics,
    .deriveEquivalentSystemPurificationUniversally,
    .justifyOrRemoveFiniteDimensionality,
    .extendFiniteQuantumReconstructionToRelativisticQftAndStandardModel ]

theorem two_postulate_route_keeps_six_open_obligations :
    twoPostulateRouteOpenObligations.length = 6 := by
  rfl

def twoPostulateReconstructionAuditStatus : String :=
  "positive_scalars_plus_es_rejected_two_postulate_causal_opt_route_conditional"

def twoPostulateReconstructionAuditClaimBoundary : String :=
  "Real quantum theory separates ES purification from local equivalence, so positive probability scalars plus ES purification do not select complex quantum theory. The 2026 two-postulate preprint is retained only as a conditional finite-dimensional causal-OPT reconstruction target. Its twelve ambient assumptions and both selector postulates are not derived from the current lower base, and the result does not yet reach relativistic QFT, the Standard Model, or gravity."

end IDT.QMClosure
