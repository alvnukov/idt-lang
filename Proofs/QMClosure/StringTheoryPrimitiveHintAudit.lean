import Mathlib

namespace IDT.QMClosure

/-!
# String-theory primitive-hint audit

This ledger asks a narrow question: which mathematically controlled results from
string theory constrain the search for lower primitives?

The answer is deliberately weaker than "strings are fundamental". Every result
retained below is conditional on a quantum worldsheet, quantum fields, or a
unitary scattering-amplitude framework. None therefore derives quantum theory
from a pre-quantum IDT base. The results can constrain a later layer and suggest
selection principles, but cannot currently serve as confirmed lower primitives.

Two elementary consequences are checked by Lean:

* cancellation of the standard central-charge balances selects 26 and 10;
* the compact-boson momentum/winding quadratic form is invariant under the
  unit-radius T-duality shadow.

These checks verify only the displayed arithmetic. They do not formalize
worldsheet quantization, BRST cohomology, anomaly factorization, a string
S-matrix, or a physical claim about our universe.
-/

inductive StringMathematicalStatus where
  | theoremInsideSpecifiedQuantumModel
  | controlledPerturbativeOrEffectiveResult
  | protectedSectorCalculation
  | conjectureOrResearchProgram
  | noEstablishedDerivation
  deriving DecidableEq, Repr

inductive StringEmpiricalStatus where
  | reproducesEstablishedLowEnergyStructure
  | noStringSpecificExperimentalConfirmation
  deriving DecidableEq, Repr

inductive StringClaim where
  | bosonicCriticalDimension
  | rnsCriticalDimension
  | compactBosonTDuality
  | greenSchwarzAnomalyCancellation
  | closedStringMasslessSpinTwoState
  | leadingWorldsheetBetaFunctionsYieldBackgroundEquations
  | extremalBpsBlackHoleEntropyMatch
  | minimalTreeAmplitudeStringUniqueness
  | generalAdSCftDuality
  | completeMTheoryDefinition
  | uniqueStandardModelVacuum
  | controlledDeSitterDarkEnergyVacuum
  | allOrderFinitenessForPhenomenologicalVacua
  | fullNonperturbativeStringCompletion
  | stringSpecificExperimentalConfirmation
  deriving DecidableEq, Repr

structure StringClaimAuditEntry where
  claim : StringClaim
  mathematicalStatus : StringMathematicalStatus
  empiricalStatus : StringEmpiricalStatus
  quantumFrameworkImported : Bool
  source : String
  scopeBoundary : String
  deriving Repr

def controlledStringResults : List StringClaimAuditEntry :=
  [
    {
      claim := .bosonicCriticalDimension
      mathematicalStatus := .theoremInsideSpecifiedQuantumModel
      empiricalStatus := .noStringSpecificExperimentalConfirmation
      quantumFrameworkImported := true
      source := "Friedan-Martinec-Shenker, Nucl. Phys. B271 (1986), DOI 10.1016/S0550-3213(86)80006-2"
      scopeBoundary := "D=26 follows for the critical bosonic worldsheet theory from conformal/BRST consistency; this is not a derivation of observed D=4"
    },
    {
      claim := .rnsCriticalDimension
      mathematicalStatus := .theoremInsideSpecifiedQuantumModel
      empiricalStatus := .noStringSpecificExperimentalConfirmation
      quantumFrameworkImported := true
      source := "Friedan-Martinec-Shenker, Nucl. Phys. B271 (1986), DOI 10.1016/S0550-3213(86)80006-2"
      scopeBoundary := "D=10 follows for the critical RNS worldsheet theory; noncritical strings and compactification are outside this arithmetic shadow"
    },
    {
      claim := .compactBosonTDuality
      mathematicalStatus := .theoremInsideSpecifiedQuantumModel
      empiricalStatus := .noStringSpecificExperimentalConfirmation
      quantumFrameworkImported := true
      source := "Giveon-Porrati-Rabinovici, Phys. Rept. 244 (1994), arXiv:hep-th/9401139"
      scopeBoundary := "exact radius inversion with momentum-winding exchange in controlled compact-boson/toroidal models; not a proof of every proposed duality"
    },
    {
      claim := .greenSchwarzAnomalyCancellation
      mathematicalStatus := .theoremInsideSpecifiedQuantumModel
      empiricalStatus := .reproducesEstablishedLowEnergyStructure
      quantumFrameworkImported := true
      source := "Green-Schwarz, Phys. Lett. B149 (1984), DOI 10.1016/0370-2693(84)91565-X"
      scopeBoundary := "factorized gauge and gravitational anomaly cancellation for the specified ten-dimensional N=1 SUGRA-SYM setting and SO(32) or E8xE8; not a Standard Model derivation"
    },
    {
      claim := .closedStringMasslessSpinTwoState
      mathematicalStatus := .theoremInsideSpecifiedQuantumModel
      empiricalStatus := .reproducesEstablishedLowEnergyStructure
      quantumFrameworkImported := true
      source := "standard perturbative closed-string spectrum"
      scopeBoundary := "a massless spin-two state occurs in the quantized closed-string spectrum; identifying its consistent low-energy coupling with gravity does not prove strings are physical"
    },
    {
      claim := .leadingWorldsheetBetaFunctionsYieldBackgroundEquations
      mathematicalStatus := .controlledPerturbativeOrEffectiveResult
      empiricalStatus := .reproducesEstablishedLowEnergyStructure
      quantumFrameworkImported := true
      source := "Callan-Friedan-Martinec-Perry, Nucl. Phys. B262 (1985), DOI 10.1016/0550-3213(85)90506-1"
      scopeBoundary := "vanishing worldsheet beta functions yields metric, antisymmetric-tensor, and dilaton field equations order by order; leading equations contain Einstein gravity plus corrections, not exact full GR alone"
    },
    {
      claim := .extremalBpsBlackHoleEntropyMatch
      mathematicalStatus := .protectedSectorCalculation
      empiricalStatus := .reproducesEstablishedLowEnergyStructure
      quantumFrameworkImported := true
      source := "Strominger-Vafa, Phys. Lett. B379 (1996), arXiv:hep-th/9601029"
      scopeBoundary := "microstate counting matches area entropy for a class of five-dimensional extremal BPS black holes; not a result for generic astrophysical black holes"
    },
    {
      claim := .minimalTreeAmplitudeStringUniqueness
      mathematicalStatus := .theoremInsideSpecifiedQuantumModel
      empiricalStatus := .noStringSpecificExperimentalConfirmation
      quantumFrameworkImported := true
      source := "Cheung-Remmen-Sciotti-Tarquini, Phys. Rev. Lett. 136, 251601 (2026), arXiv:2508.09246v2"
      scopeBoundary := "Veneziano and Virasoro-Shapiro amplitudes are unique among minimally consistent tree amplitudes after assuming ultrasoft Regge behavior and no zeros beyond consistency-mandated zeros; the extra assumptions and nonperturbative completion are not derived"
    }
  ]

def unestablishedStringClaims : List StringClaimAuditEntry :=
  [
    {
      claim := .generalAdSCftDuality
      mathematicalStatus := .conjectureOrResearchProgram
      empiricalStatus := .noStringSpecificExperimentalConfirmation
      quantumFrameworkImported := true
      source := "broad AdS/CFT program"
      scopeBoundary := "many exact tests and special constructions exist, but no theorem establishes the full duality in unrestricted generality"
    },
    {
      claim := .completeMTheoryDefinition
      mathematicalStatus := .noEstablishedDerivation
      empiricalStatus := .noStringSpecificExperimentalConfirmation
      quantumFrameworkImported := true
      source := "M-theory research program"
      scopeBoundary := "no complete generally accepted nonperturbative definition covering all backgrounds"
    },
    {
      claim := .uniqueStandardModelVacuum
      mathematicalStatus := .noEstablishedDerivation
      empiricalStatus := .noStringSpecificExperimentalConfirmation
      quantumFrameworkImported := true
      source := "string phenomenology and vacuum-selection program"
      scopeBoundary := "no unique derivation of the observed Standard Model spectrum, masses, mixings, and couplings"
    },
    {
      claim := .controlledDeSitterDarkEnergyVacuum
      mathematicalStatus := .conjectureOrResearchProgram
      empiricalStatus := .noStringSpecificExperimentalConfirmation
      quantumFrameworkImported := true
      source := "string cosmology program"
      scopeBoundary := "proposed constructions and obstructions do not amount to a settled derivation of observed dark energy"
    },
    {
      claim := .allOrderFinitenessForPhenomenologicalVacua
      mathematicalStatus := .noEstablishedDerivation
      empiricalStatus := .noStringSpecificExperimentalConfirmation
      quantumFrameworkImported := true
      source := "perturbative finiteness program"
      scopeBoundary := "controlled cancellations at fixed orders or special settings do not establish all-order finiteness for realistic vacua"
    },
    {
      claim := .fullNonperturbativeStringCompletion
      mathematicalStatus := .noEstablishedDerivation
      empiricalStatus := .noStringSpecificExperimentalConfirmation
      quantumFrameworkImported := true
      source := "nonperturbative string-theory program"
      scopeBoundary := "dualities and special definitions do not yet provide one complete background-independent theory"
    },
    {
      claim := .stringSpecificExperimentalConfirmation
      mathematicalStatus := .noEstablishedDerivation
      empiricalStatus := .noStringSpecificExperimentalConfirmation
      quantumFrameworkImported := true
      source := "current experimental record"
      scopeBoundary := "no observation uniquely selects string theory over non-string alternatives"
    }
  ]

def stringStatusCount
    (status : StringMathematicalStatus)
    (entries : List StringClaimAuditEntry) : Nat :=
  (entries.filter fun entry => entry.mathematicalStatus == status).length

theorem controlled_audit_records_eight_scoped_results :
    controlledStringResults.length = 8 := by
  rfl

theorem six_results_are_theorems_inside_specified_quantum_models :
    stringStatusCount .theoremInsideSpecifiedQuantumModel
      controlledStringResults = 6 := by
  rfl

theorem one_result_is_explicitly_perturbative_or_effective :
    stringStatusCount .controlledPerturbativeOrEffectiveResult
      controlledStringResults = 1 := by
  rfl

theorem one_result_is_a_protected_sector_calculation :
    stringStatusCount .protectedSectorCalculation
      controlledStringResults = 1 := by
  rfl

theorem every_controlled_result_imports_a_quantum_framework :
    controlledStringResults.all (fun entry => entry.quantumFrameworkImported) = true := by
  rfl

theorem audit_keeps_seven_broad_claims_unestablished :
    unestablishedStringClaims.length = 7 := by
  rfl

/-! ## Lean-checked arithmetic shadows -/

def bosonicCentralChargeBalance (dimension : Int) : Int :=
  dimension - 26

theorem bosonic_central_charge_balance_selects_26 (dimension : Int) :
    bosonicCentralChargeBalance dimension = 0 ↔ dimension = 26 := by
  simp only [bosonicCentralChargeBalance]
  omega

/-- Twice the flat RNS matter-plus-ghost central-charge balance. -/
def rnsCentralChargeBalanceTimesTwo (dimension : Int) : Int :=
  3 * dimension - 30

theorem rns_central_charge_balance_selects_10 (dimension : Int) :
    rnsCentralChargeBalanceTimesTwo dimension = 0 ↔ dimension = 10 := by
  simp only [rnsCentralChargeBalanceTimesTwo]
  omega

/-- Momentum/winding part of the compact-boson spectrum in units alpha'=1. -/
def compactChargeQuadratic (momentum winding radius : ℚ) : ℚ :=
  momentum ^ 2 / radius ^ 2 + winding ^ 2 * radius ^ 2

theorem compact_charge_quadratic_t_duality
    (momentum winding radius : ℚ) (radiusNonzero : radius ≠ 0) :
    compactChargeQuadratic momentum winding radius =
      compactChargeQuadratic winding momentum (1 / radius) := by
  simp only [compactChargeQuadratic]
  field_simp [radiusNonzero]
  ring

inductive StringAmplitudeSelectorAssumption where
  | treeLevelLorentzInvariantUnitaryCrossingFramework
  | consistencyMandatedReggeZeros
  | ultrasoftReggeBehavior
  | noAdditionalZeros
  deriving DecidableEq, Repr

inductive SelectorEvidenceStatus where
  | ambientQuantumFrameworkImport
  | provedInsideAmbientFramework
  | additionalUnconfirmedPostulate
  | derivedFromLowerPrimitives
  deriving DecidableEq, Repr

structure StringAmplitudeSelectorAuditEntry where
  assumption : StringAmplitudeSelectorAssumption
  status : SelectorEvidenceStatus
  boundary : String
  deriving Repr

def stringAmplitudeSelectorAudit : List StringAmplitudeSelectorAuditEntry :=
  [
    {
      assumption := .treeLevelLorentzInvariantUnitaryCrossingFramework
      status := .ambientQuantumFrameworkImport
      boundary := "already assumes a quantum scattering-amplitude setting and is not derived from IDT lower primitives"
    },
    {
      assumption := .consistencyMandatedReggeZeros
      status := .provedInsideAmbientFramework
      boundary := "the 2026 theorem derives prescribed residue zeros from consistency inside its tree-level amplitude hypotheses"
    },
    {
      assumption := .ultrasoftReggeBehavior
      status := .additionalUnconfirmedPostulate
      boundary := "needed for the uniqueness result and not established as a universal law of nature"
    },
    {
      assumption := .noAdditionalZeros
      status := .additionalUnconfirmedPostulate
      boundary := "minimality assumption; consistency permits extra zeros"
    }
  ]

def selectorStatusCount
    (status : SelectorEvidenceStatus)
    (entries : List StringAmplitudeSelectorAuditEntry) : Nat :=
  (entries.filter fun entry => entry.status == status).length

theorem string_amplitude_uniqueness_uses_two_unconfirmed_selector_postulates :
    selectorStatusCount .additionalUnconfirmedPostulate
      stringAmplitudeSelectorAudit = 2 := by
  rfl

theorem string_amplitude_selector_is_not_lower_derived :
    selectorStatusCount .derivedFromLowerPrimitives
      stringAmplitudeSelectorAudit = 0 := by
  rfl

inductive PrimitivePressure where
  | compositionalGluingAndFactorization
  | globalConsistencySelection
  | presentationEquivalenceRatherThanBareGeometry
  | dimensionAsConsistencyOutput
  | gravityAsLateConsistencyConsequence
  | protectedInvariantAcrossDescriptionChanges
  | minimalityOfConsistentAmplitude
  deriving DecidableEq, Repr

inductive PrimitivePressureStatus where
  | retainedAsPostQuantumConstraint
  | retainedAsUnconfirmedSelectorCandidate
  | confirmedPreQuantumPrimitive
  deriving DecidableEq, Repr

structure PrimitivePressureAuditEntry where
  pressure : PrimitivePressure
  status : PrimitivePressureStatus
  reason : String
  deriving Repr

def stringPrimitivePressures : List PrimitivePressureAuditEntry :=
  [
    {
      pressure := .compositionalGluingAndFactorization
      status := .retainedAsPostQuantumConstraint
      reason := "worldsheet and S-matrix consistency make compatible composition a necessary later-layer check"
    },
    {
      pressure := .globalConsistencySelection
      status := .retainedAsPostQuantumConstraint
      reason := "anomaly cancellation and factorization show that global consistency can eliminate locally plausible theories"
    },
    {
      pressure := .presentationEquivalenceRatherThanBareGeometry
      status := .retainedAsPostQuantumConstraint
      reason := "compact-boson T-duality identifies distinct radius presentations, weakening bare geometry as a primitive ontology"
    },
    {
      pressure := .dimensionAsConsistencyOutput
      status := .retainedAsPostQuantumConstraint
      reason := "critical dimension is selected after specifying the worldsheet field and ghost content"
    },
    {
      pressure := .gravityAsLateConsistencyConsequence
      status := .retainedAsPostQuantumConstraint
      reason := "spin two and beta-function results support, but do not prove, gravity emerging after quantum consistency"
    },
    {
      pressure := .protectedInvariantAcrossDescriptionChanges
      status := .retainedAsPostQuantumConstraint
      reason := "BPS indices show which quantities can remain stable while coupling or presentation changes"
    },
    {
      pressure := .minimalityOfConsistentAmplitude
      status := .retainedAsUnconfirmedSelectorCandidate
      reason := "minimal zeros help select string amplitudes, but minimality and ultrasoftness are extra postulates"
    }
  ]

def primitivePressureStatusCount
    (status : PrimitivePressureStatus)
    (entries : List PrimitivePressureAuditEntry) : Nat :=
  (entries.filter fun entry => entry.status == status).length

theorem string_results_confirm_no_pre_quantum_primitive :
    primitivePressureStatusCount .confirmedPreQuantumPrimitive
      stringPrimitivePressures = 0 := by
  rfl

theorem six_pressures_survive_only_as_post_quantum_constraints :
    primitivePressureStatusCount .retainedAsPostQuantumConstraint
      stringPrimitivePressures = 6 := by
  rfl

theorem one_pressure_is_only_an_unconfirmed_selector_candidate :
    primitivePressureStatusCount .retainedAsUnconfirmedSelectorCandidate
      stringPrimitivePressures = 1 := by
  rfl

inductive StringPrimitiveOpenObligation where
  | deriveQuantumReadoutBeforeInvokingWorldsheetTheory
  | deriveComplexAmplitudesAndUnitarityFromLowerPrimitives
  | deriveCrossingAndFactorizationFromProcessSemantics
  | justifyOrFalsifyUltrasoftReggeBehavior
  | justifyOrRejectMinimalZeros
  | extendTreeLevelSelectionToLoopsAndNonperturbativePhysics
  | deriveObservedFourDimensionalStandardModelVacuum
  | produceStringSpecificExperimentalDiscriminator
  deriving DecidableEq, Repr

def stringPrimitiveOpenObligations : List StringPrimitiveOpenObligation :=
  [ .deriveQuantumReadoutBeforeInvokingWorldsheetTheory,
    .deriveComplexAmplitudesAndUnitarityFromLowerPrimitives,
    .deriveCrossingAndFactorizationFromProcessSemantics,
    .justifyOrFalsifyUltrasoftReggeBehavior,
    .justifyOrRejectMinimalZeros,
    .extendTreeLevelSelectionToLoopsAndNonperturbativePhysics,
    .deriveObservedFourDimensionalStandardModelVacuum,
    .produceStringSpecificExperimentalDiscriminator ]

theorem string_hint_route_keeps_eight_open_obligations :
    stringPrimitiveOpenObligations.length = 8 := by
  rfl

def stringTheoryPrimitiveHintAuditStatus : String :=
  "no_prequantum_primitive_confirmed_postquantum_consistency_pressures_retained"

def stringTheoryPrimitiveHintAuditClaimBoundary : String :=
  "Controlled string results are conditional inside already-quantum worldsheet, QFT, S-matrix, or protected-sector frameworks. They support composition, equivalence of presentations, global consistency, protected invariants, and gravity as a possible derived layer. They do not derive quantum probability, establish strings as physical ontology, select the observed Standard Model vacuum, prove full quantum gravity, or provide string-specific experimental confirmation."

end IDT.QMClosure
