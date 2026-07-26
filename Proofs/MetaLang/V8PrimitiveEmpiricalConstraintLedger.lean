import Proofs.MetaLang.V8QmExperimentResidualLedger

namespace IDT
namespace MetaLang
namespace V8

/-!
Empirical constraint ledger for lower-primitive research.

This is a coverage and claim-discipline artifact, not a derivation of physics.
It prevents a primitive candidate from being called confirmed after passing only
the current QM gates.  A static file cannot literally enumerate every datum, so
the ledger tracks versioned evidence families and remains open to new results.

Established constraints and robust unexplained observations are both relevant
to confirmation.  Active tensions are tracked, but cannot confirm a primitive
until they become stable, independently replicated constraints.
-/

inductive EmpiricalSector where
  | quantumOperational
  | relativisticQft
  | standardModel
  | gravity
  | thermodynamics
  | cosmology
  | anomalyWatch
deriving DecidableEq, Repr

inductive EvidenceTier where
  | establishedConstraint
  | robustUnexplainedObservation
  | activeTension
deriving DecidableEq, Repr

def EvidenceTier.confirmationRelevant : EvidenceTier → Bool
  | .establishedConstraint => true
  | .robustUnexplainedObservation => true
  | .activeTension => false

inductive EmpiricalConstraintId where
  | bornRuleStatistics
  | twoAndMultiPathInterference
  | noThirdOrderInterference
  | contextuality
  | bellNonlocalityNoSignalling
  | tsirelsonBoundary
  | complexQuantumDiscrimination
  | compositeEntanglementTomography
  | reversibleContinuousDynamics
  | decoherenceClassicalLimit
  | lorentzPoincareSymmetry
  | relativisticDispersion
  | localityMicrocausality
  | cptSymmetryBounds
  | spinStatistics
  | unitarityOpticalTheorem
  | renormalizationRunningEft
  | vacuumCorrelationCasimir
  | gaugeChiralRepresentation
  | gaugeAnomalyCancellation
  | threeGenerations
  | higgsElectroweakBreaking
  | particleMassWidthDecaySpectrum
  | qcdRunningConfinementHadronSpectrum
  | ckmFlavorCpViolation
  | neutrinoOscillationMassMixing
  | precisionElectroweakRareProcesses
  | weakEquivalenceFreeFall
  | newtonInverseSquarePpn
  | gravitationalRedshiftTimeDilation
  | lightDeflectionShapiroLensing
  | binaryPulsarRadiation
  | gravitationalWavePropagationPolarizationWaveform
  | strongFieldBlackHoleRingdownImaging
  | thermodynamicLaws
  | statisticalEquilibriumFluctuations
  | irreversibilityEntropyProduction
  | expansionHistory
  | bigBangNucleosynthesis
  | cmbSpectrumAnisotropies
  | baoLargeScaleStructureLensing
  | darkMatterMultiProbeEvidence
  | cosmicAcceleration
  | baryonAsymmetry
  | primordialPerturbationStatistics
  | activeAnomalyReplicationRegistry
deriving DecidableEq, Repr

structure EmpiricalConstraint where
  id : EmpiricalConstraintId
  sector : EmpiricalSector
  tier : EvidenceTier
  sourceFamily : String
deriving Repr

structure EmpiricalSourceAnchor where
  key : String
  locator : String
  scope : String
deriving Repr

def primitiveEmpiricalSourceAnchors : List EmpiricalSourceAnchor :=
  [
    {
      key := "idt_qm_ledger"
      locator := "Proofs/MetaLang/V8QmExperimentResidualLedger.lean"
      scope := "35 executable QM residual gates; no formal physical closure"
    },
    {
      key := "pdg_2025"
      locator := "https://pdg.lbl.gov/2025/reviews/standard_model_and_related.html"
      scope := "particle properties, Standard Model, QCD, flavor, neutrinos"
    },
    {
      key := "microscope_final"
      locator := "https://doi.org/10.1103/PhysRevLett.129.121102"
      scope := "weak-equivalence-principle test"
    },
    {
      key := "lvk_gwtc4_gr_tests"
      locator := "https://dcc.ligo.org/LIGO-P2500066/public"
      scope := "strong-field and propagation tests of general relativity"
    },
    {
      key := "planck_2018_parameters"
      locator := "https://arxiv.org/abs/1807.06209"
      scope := "CMB and cosmological-parameter evidence family"
    },
    {
      key := "versioned_primary_results"
      locator := "primary collaboration publications and maintained data releases"
      scope := "pulsars, lensing, BBN, BAO, structure, thermodynamics, active anomalies"
    }
  ]

def primitiveEmpiricalConstraints : List EmpiricalConstraint :=
  [
    { id := .bornRuleStatistics, sector := .quantumOperational,
      tier := .establishedConstraint, sourceFamily := "idt_qm_ledger" },
    { id := .twoAndMultiPathInterference, sector := .quantumOperational,
      tier := .establishedConstraint, sourceFamily := "idt_qm_ledger" },
    { id := .noThirdOrderInterference, sector := .quantumOperational,
      tier := .establishedConstraint, sourceFamily := "idt_qm_ledger" },
    { id := .contextuality, sector := .quantumOperational,
      tier := .establishedConstraint, sourceFamily := "idt_qm_ledger" },
    { id := .bellNonlocalityNoSignalling, sector := .quantumOperational,
      tier := .establishedConstraint, sourceFamily := "idt_qm_ledger" },
    { id := .tsirelsonBoundary, sector := .quantumOperational,
      tier := .establishedConstraint, sourceFamily := "idt_qm_ledger" },
    { id := .complexQuantumDiscrimination, sector := .quantumOperational,
      tier := .establishedConstraint, sourceFamily := "versioned_primary_results" },
    { id := .compositeEntanglementTomography, sector := .quantumOperational,
      tier := .establishedConstraint, sourceFamily := "idt_qm_ledger" },
    { id := .reversibleContinuousDynamics, sector := .quantumOperational,
      tier := .establishedConstraint, sourceFamily := "idt_qm_ledger" },
    { id := .decoherenceClassicalLimit, sector := .quantumOperational,
      tier := .establishedConstraint, sourceFamily := "idt_qm_ledger" },
    { id := .lorentzPoincareSymmetry, sector := .relativisticQft,
      tier := .establishedConstraint, sourceFamily := "pdg_2025" },
    { id := .relativisticDispersion, sector := .relativisticQft,
      tier := .establishedConstraint, sourceFamily := "pdg_2025" },
    { id := .localityMicrocausality, sector := .relativisticQft,
      tier := .establishedConstraint, sourceFamily := "pdg_2025" },
    { id := .cptSymmetryBounds, sector := .relativisticQft,
      tier := .establishedConstraint, sourceFamily := "pdg_2025" },
    { id := .spinStatistics, sector := .relativisticQft,
      tier := .establishedConstraint, sourceFamily := "pdg_2025" },
    { id := .unitarityOpticalTheorem, sector := .relativisticQft,
      tier := .establishedConstraint, sourceFamily := "pdg_2025" },
    { id := .renormalizationRunningEft, sector := .relativisticQft,
      tier := .establishedConstraint, sourceFamily := "pdg_2025" },
    { id := .vacuumCorrelationCasimir, sector := .relativisticQft,
      tier := .establishedConstraint, sourceFamily := "versioned_primary_results" },
    { id := .gaugeChiralRepresentation, sector := .standardModel,
      tier := .establishedConstraint, sourceFamily := "pdg_2025" },
    { id := .gaugeAnomalyCancellation, sector := .standardModel,
      tier := .establishedConstraint, sourceFamily := "pdg_2025" },
    { id := .threeGenerations, sector := .standardModel,
      tier := .establishedConstraint, sourceFamily := "pdg_2025" },
    { id := .higgsElectroweakBreaking, sector := .standardModel,
      tier := .establishedConstraint, sourceFamily := "pdg_2025" },
    { id := .particleMassWidthDecaySpectrum, sector := .standardModel,
      tier := .establishedConstraint, sourceFamily := "pdg_2025" },
    { id := .qcdRunningConfinementHadronSpectrum, sector := .standardModel,
      tier := .establishedConstraint, sourceFamily := "pdg_2025" },
    { id := .ckmFlavorCpViolation, sector := .standardModel,
      tier := .establishedConstraint, sourceFamily := "pdg_2025" },
    { id := .neutrinoOscillationMassMixing, sector := .standardModel,
      tier := .robustUnexplainedObservation, sourceFamily := "pdg_2025" },
    { id := .precisionElectroweakRareProcesses, sector := .standardModel,
      tier := .establishedConstraint, sourceFamily := "pdg_2025" },
    { id := .weakEquivalenceFreeFall, sector := .gravity,
      tier := .establishedConstraint, sourceFamily := "microscope_final" },
    { id := .newtonInverseSquarePpn, sector := .gravity,
      tier := .establishedConstraint, sourceFamily := "versioned_primary_results" },
    { id := .gravitationalRedshiftTimeDilation, sector := .gravity,
      tier := .establishedConstraint, sourceFamily := "versioned_primary_results" },
    { id := .lightDeflectionShapiroLensing, sector := .gravity,
      tier := .establishedConstraint, sourceFamily := "versioned_primary_results" },
    { id := .binaryPulsarRadiation, sector := .gravity,
      tier := .establishedConstraint, sourceFamily := "versioned_primary_results" },
    { id := .gravitationalWavePropagationPolarizationWaveform, sector := .gravity,
      tier := .establishedConstraint, sourceFamily := "lvk_gwtc4_gr_tests" },
    { id := .strongFieldBlackHoleRingdownImaging, sector := .gravity,
      tier := .establishedConstraint, sourceFamily := "lvk_gwtc4_gr_tests" },
    { id := .thermodynamicLaws, sector := .thermodynamics,
      tier := .establishedConstraint, sourceFamily := "versioned_primary_results" },
    { id := .statisticalEquilibriumFluctuations, sector := .thermodynamics,
      tier := .establishedConstraint, sourceFamily := "versioned_primary_results" },
    { id := .irreversibilityEntropyProduction, sector := .thermodynamics,
      tier := .establishedConstraint, sourceFamily := "versioned_primary_results" },
    { id := .expansionHistory, sector := .cosmology,
      tier := .establishedConstraint, sourceFamily := "planck_2018_parameters" },
    { id := .bigBangNucleosynthesis, sector := .cosmology,
      tier := .establishedConstraint, sourceFamily := "versioned_primary_results" },
    { id := .cmbSpectrumAnisotropies, sector := .cosmology,
      tier := .establishedConstraint, sourceFamily := "planck_2018_parameters" },
    { id := .baoLargeScaleStructureLensing, sector := .cosmology,
      tier := .establishedConstraint, sourceFamily := "versioned_primary_results" },
    { id := .darkMatterMultiProbeEvidence, sector := .cosmology,
      tier := .robustUnexplainedObservation, sourceFamily := "versioned_primary_results" },
    { id := .cosmicAcceleration, sector := .cosmology,
      tier := .robustUnexplainedObservation, sourceFamily := "versioned_primary_results" },
    { id := .baryonAsymmetry, sector := .cosmology,
      tier := .robustUnexplainedObservation, sourceFamily := "pdg_2025" },
    { id := .primordialPerturbationStatistics, sector := .cosmology,
      tier := .robustUnexplainedObservation, sourceFamily := "planck_2018_parameters" },
    { id := .activeAnomalyReplicationRegistry, sector := .anomalyWatch,
      tier := .activeTension, sourceFamily := "versioned_primary_results" }
  ]

inductive CandidateEvidenceStatus where
  | derivedWithoutTargetImport
  | reproducedWithDeclaredAnchor
  | compatibleOnly
  | partialExecutableCoverage
  | unassessed
  | contradicted
deriving DecidableEq, Repr

structure CandidateConstraintEntry where
  requirement : EmpiricalConstraint
  status : CandidateEvidenceStatus
deriving Repr

def currentPrimitiveSearchCoverage : List CandidateConstraintEntry :=
  primitiveEmpiricalConstraints.map fun requirement =>
    {
      requirement := requirement
      status :=
        if requirement.id == .complexQuantumDiscrimination then
          .unassessed
        else if requirement.sector == .quantumOperational then
          .partialExecutableCoverage
        else
          .unassessed
    }

def closesRequirementForConfirmation
    (entry : CandidateConstraintEntry) : Bool :=
  !entry.requirement.tier.confirmationRelevant ||
    entry.status == .derivedWithoutTargetImport

def candidateHasContradictedHardConstraint
    (coverage : List CandidateConstraintEntry) : Bool :=
  coverage.any fun entry =>
    entry.requirement.tier.confirmationRelevant &&
      entry.status == .contradicted

def candidateHasUnassessedHardConstraint
    (coverage : List CandidateConstraintEntry) : Bool :=
  coverage.any fun entry =>
    entry.requirement.tier.confirmationRelevant &&
      entry.status == .unassessed

def candidateClosesAllConfirmationRequirements
    (coverage : List CandidateConstraintEntry) : Bool :=
  coverage.all closesRequirementForConfirmation

inductive PrimitiveCandidateDecision where
  | rejected
  | unassessed
  | conditionalOnly
  | confirmedLowerBase
deriving DecidableEq, Repr

def decidePrimitiveCandidate
    (coverage : List CandidateConstraintEntry) : PrimitiveCandidateDecision :=
  if candidateHasContradictedHardConstraint coverage then
    .rejected
  else if candidateClosesAllConfirmationRequirements coverage then
    .confirmedLowerBase
  else if candidateHasUnassessedHardConstraint coverage then
    .unassessed
  else
    .conditionalOnly

def empiricalCoverageIsClosedWorld : Bool := false

theorem primitive_empirical_constraint_family_count :
    primitiveEmpiricalConstraints.length = 46 := by
  rfl

theorem existing_qm_ledger_is_executable_not_formal_closure :
    currentQmExperimentResidualLedger.length = 35 ∧
      qmExperimentResidualFormalProofCount = 0 := by
  constructor <;> rfl

theorem current_primitive_search_does_not_close_empirical_requirements :
    candidateClosesAllConfirmationRequirements currentPrimitiveSearchCoverage = false := by
  rfl

theorem current_primitive_search_is_unassessed_not_confirmed :
    decidePrimitiveCandidate currentPrimitiveSearchCoverage = .unassessed := by
  rfl

theorem active_tensions_are_not_confirmation_evidence :
    EvidenceTier.activeTension.confirmationRelevant = false := by
  rfl

theorem static_ledger_makes_no_timeless_completeness_claim :
    empiricalCoverageIsClosedWorld = false := by
  rfl

def primitiveEmpiricalConstraintResult : String :=
  "The present primitive search is not confirmed: QM has partial executable coverage, while relativistic QFT, the Standard Model, gravity, thermodynamics, cosmology, and robust unexplained observations remain unassessed from the candidate primitives. Active anomalies may guide falsification probes but cannot select or confirm the lower base before independent replication."

end V8
end MetaLang
end IDT
