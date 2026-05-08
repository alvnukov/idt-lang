import Proofs.QMClosure.V7BornReadoutRoute
import Proofs.QMClosure.V7HilbertCarrierRoute
import Proofs.QMClosure.V7SchrodingerDynamicsRoute
import Proofs.QMClosure.FullQMSectorClosure

namespace IDT
namespace QMClosure

/-!
V7 full-QM burden ledger recovery.

This module preserves the exact v7 proof-burden split so v8 does not lose the
already discovered structure. It is a ledger of obligations and conditional
routes, not a claim that full QM is proved.
-/

structure V7ResidualProjectiveCluster where
  finiteProjectionDeterminacy : Prop
  projectiveConsistency : Prop
  nonunitalStableDistinguishability : Prop
  conservativeProjectiveGluing : Prop

def V7ResidualProjectiveClusterClosed
    (cluster : V7ResidualProjectiveCluster) : Prop :=
  cluster.finiteProjectionDeterminacy
    ∧ cluster.projectiveConsistency
    ∧ cluster.nonunitalStableDistinguishability
    ∧ cluster.conservativeProjectiveGluing

structure V7RepresentationCluster where
  spectralDecomposition : Prop
  richDclReversibleSymmetry : Prop
  carrierFrontierExhaustion : Prop
  noHilbertImport : Prop

def V7RepresentationClusterClosed
    (cluster : V7RepresentationCluster) : Prop :=
  cluster.spectralDecomposition
    ∧ cluster.richDclReversibleSymmetry
    ∧ cluster.carrierFrontierExhaustion
    ∧ cluster.noHilbertImport

structure V7BornReadoutCluster where
  positiveQuadraticMeasure : Prop
  contextNormalization : Prop
  exclusivityAdditivity : Prop
  coarseGrainingConsistency : Prop
  operationalEquivalenceProbability : Prop
  admissibleReadoutContext : Prop
  frequencyInterpretation : Prop
  noBornImport : Prop

def V7BornReadoutClusterClosed
    (cluster : V7BornReadoutCluster) : Prop :=
  V7BornReadoutRouteClosed
    {
      positiveQuadraticMeasure := cluster.positiveQuadraticMeasure,
      contextNormalization := cluster.contextNormalization,
      exclusivityAdditivity := cluster.exclusivityAdditivity,
      coarseGrainingConsistency := cluster.coarseGrainingConsistency,
      operationalEquivalenceProbability :=
        cluster.operationalEquivalenceProbability,
      admissibleReadoutContext := cluster.admissibleReadoutContext,
      frequencyInterpretation := cluster.frequencyInterpretation,
      noBornImport := cluster.noBornImport
    }

structure V7DynamicsCluster where
  reversibleDclAutomorphism : Prop
  overlapPreservation : Prop
  projectiveAction : Prop
  continuousInheritanceFamily : Prop
  generatorClosure : Prop
  phaseOrientation : Prop
  normalizedTransitionReadout : Prop
  noUnitaryImport : Prop
  noStoneImport : Prop
  noGeneratorImport : Prop

def V7DynamicsClusterClosed
    (cluster : V7DynamicsCluster) : Prop :=
  V7DynamicsRouteClosed
    {
      reversibleDclAutomorphism := cluster.reversibleDclAutomorphism,
      overlapPreservation := cluster.overlapPreservation,
      projectiveAction := cluster.projectiveAction,
      continuousInheritanceFamily := cluster.continuousInheritanceFamily,
      generatorClosure := cluster.generatorClosure,
      phaseOrientation := cluster.phaseOrientation,
      normalizedTransitionReadout := cluster.normalizedTransitionReadout,
      noUnitaryImport := cluster.noUnitaryImport,
      noStoneImport := cluster.noStoneImport,
      noGeneratorImport := cluster.noGeneratorImport
    }

structure V7CompositeCluster where
  productContextExhaustion : Prop
  localTomography : Prop
  monoidalAssociativity : Prop
  entanglementClosure : Prop
  projectiveLimitConsistency : Prop
  noTensorImport : Prop

def V7CompositeClusterClosed
    (cluster : V7CompositeCluster) : Prop :=
  cluster.productContextExhaustion
    ∧ cluster.localTomography
    ∧ cluster.monoidalAssociativity
    ∧ cluster.entanglementClosure
    ∧ cluster.projectiveLimitConsistency
    ∧ cluster.noTensorImport

structure V7PhysicalScaleCluster where
  calibratedPhaseScaleBoundary : Prop
  firstPrinciplesActionScale : Prop
  noHbarDerivationClaim : Prop

def V7PhysicalScaleClusterClosed
    (cluster : V7PhysicalScaleCluster) : Prop :=
  cluster.calibratedPhaseScaleBoundary
    ∧ cluster.firstPrinciplesActionScale
    ∧ cluster.noHbarDerivationClaim

structure V7FullQMBurden where
  residualProjective : V7ResidualProjectiveCluster
  representation : V7RepresentationCluster
  bornReadout : V7BornReadoutCluster
  dynamics : V7DynamicsCluster
  composites : V7CompositeCluster
  physicalScale : V7PhysicalScaleCluster

def V7FullQMBurdenClosed
    (burden : V7FullQMBurden) : Prop :=
  V7ResidualProjectiveClusterClosed burden.residualProjective
    ∧ V7RepresentationClusterClosed burden.representation
    ∧ V7BornReadoutClusterClosed burden.bornReadout
    ∧ V7DynamicsClusterClosed burden.dynamics
    ∧ V7CompositeClusterClosed burden.composites
    ∧ V7PhysicalScaleClusterClosed burden.physicalScale

def v7RecoveredCurrentBurden : V7FullQMBurden :=
  {
    residualProjective := {
      finiteProjectionDeterminacy := False,
      projectiveConsistency := False,
      nonunitalStableDistinguishability := True,
      conservativeProjectiveGluing := True
    },
    representation := {
      spectralDecomposition := True,
      richDclReversibleSymmetry := True,
      carrierFrontierExhaustion := False,
      noHilbertImport := True
    },
    bornReadout := {
      positiveQuadraticMeasure := True,
      contextNormalization := False,
      exclusivityAdditivity := False,
      coarseGrainingConsistency := False,
      operationalEquivalenceProbability := False,
      admissibleReadoutContext := False,
      frequencyInterpretation := False,
      noBornImport := True
    },
    dynamics := {
      reversibleDclAutomorphism := True,
      overlapPreservation := True,
      projectiveAction := True,
      continuousInheritanceFamily := False,
      generatorClosure := False,
      phaseOrientation := True,
      normalizedTransitionReadout := True,
      noUnitaryImport := True,
      noStoneImport := True,
      noGeneratorImport := True
    },
    composites := {
      productContextExhaustion := False,
      localTomography := True,
      monoidalAssociativity := True,
      entanglementClosure := False,
      projectiveLimitConsistency := False,
      noTensorImport := True
    },
    physicalScale := {
      calibratedPhaseScaleBoundary := True,
      firstPrinciplesActionScale := False,
      noHbarDerivationClaim := True
    }
  }

theorem v7_recovered_current_burden_is_not_full_qm_closure :
    ¬ V7FullQMBurdenClosed v7RecoveredCurrentBurden := by
  intro closed
  exact closed.left.left

theorem v7_full_qm_burden_requires_born_operational_equivalence
    (burden : V7FullQMBurden) :
    V7FullQMBurdenClosed burden →
      burden.bornReadout.operationalEquivalenceProbability :=
  fun closed =>
    closed.right.right.left.right.right.right.right.left

theorem v7_full_qm_burden_requires_carrier_frontier_exhaustion
    (burden : V7FullQMBurden) :
    V7FullQMBurdenClosed burden →
      burden.representation.carrierFrontierExhaustion :=
  fun closed =>
    closed.right.left.right.right.left

theorem v7_full_qm_burden_requires_generator_closure
    (burden : V7FullQMBurden) :
    V7FullQMBurdenClosed burden →
      burden.dynamics.generatorClosure :=
  fun closed =>
    closed.right.right.right.left.right.right.right.right.left

end QMClosure
end IDT
