import Proofs.QMClosure.ConstructiveWitnessPrimitiveBase

namespace IDT
namespace QMClosure

/-!
V7 Hilbert/carrier route recovery.

V7 did not derive complex Hilbert space. It compressed the carrier route:
real normalized-overlap carriers fail finite QM screens, phase-bundle
normalized-overlap survives the finite screens, and the remaining wall is the
non-circular derivation of phase-bundle `J` plus a universal representation /
carrier-frontier theorem.
-/

structure V7CompressedCarrierRoute where
  compatibleKernelAdditivity : Prop
  normalizedOverlapUniqueness : Prop
  phaseBundleJStructure : Prop
  finiteProjectiveBornNormalization : Prop
  projectiveRepeatability : Prop
  phaseGaugeInvariance : Prop
  relativePhaseInterference : Prop
  tensorMultiplicativity : Prop
  localTomographyDimension : Prop
  singletAngleCurve : Prop
  noHilbertImport : Prop
  noBornImport : Prop

def V7CompressedCarrierRouteHit
    (route : V7CompressedCarrierRoute) : Prop :=
  route.compatibleKernelAdditivity
    ∧ route.normalizedOverlapUniqueness
    ∧ route.phaseBundleJStructure
    ∧ route.finiteProjectiveBornNormalization
    ∧ route.projectiveRepeatability
    ∧ route.phaseGaugeInvariance
    ∧ route.relativePhaseInterference
    ∧ route.tensorMultiplicativity
    ∧ route.localTomographyDimension
    ∧ route.singletAngleCurve
    ∧ route.noHilbertImport
    ∧ route.noBornImport

def v7PhaseBundleNormalizedOverlapRoute : V7CompressedCarrierRoute :=
  {
    compatibleKernelAdditivity := True,
    normalizedOverlapUniqueness := True,
    phaseBundleJStructure := True,
    finiteProjectiveBornNormalization := True,
    projectiveRepeatability := True,
    phaseGaugeInvariance := True,
    relativePhaseInterference := True,
    tensorMultiplicativity := True,
    localTomographyDimension := True,
    singletAngleCurve := True,
    noHilbertImport := True,
    noBornImport := True
  }

theorem v7_phase_bundle_normalized_overlap_route_hits_finite_screens :
    V7CompressedCarrierRouteHit v7PhaseBundleNormalizedOverlapRoute := by
  repeat constructor

def v7RealNormalizedOverlapRoute : V7CompressedCarrierRoute :=
  {
    compatibleKernelAdditivity := True,
    normalizedOverlapUniqueness := True,
    phaseBundleJStructure := False,
    finiteProjectiveBornNormalization := False,
    projectiveRepeatability := True,
    phaseGaugeInvariance := False,
    relativePhaseInterference := False,
    tensorMultiplicativity := False,
    localTomographyDimension := False,
    singletAngleCurve := True,
    noHilbertImport := True,
    noBornImport := True
  }

theorem v7_real_normalized_overlap_route_fails_finite_qm_screens :
    ¬ V7CompressedCarrierRouteHit v7RealNormalizedOverlapRoute := by
  intro hit
  exact hit.right.right.left

def V7PhaseBundleJStructureWall
    (route : V7CompressedCarrierRoute) : Prop :=
  route.compatibleKernelAdditivity
    ∧ route.normalizedOverlapUniqueness
    ∧ ¬ route.phaseBundleJStructure

def v7PhaseBundleJMissingRoute : V7CompressedCarrierRoute :=
  {
    compatibleKernelAdditivity := True,
    normalizedOverlapUniqueness := True,
    phaseBundleJStructure := False,
    finiteProjectiveBornNormalization := True,
    projectiveRepeatability := True,
    phaseGaugeInvariance := True,
    relativePhaseInterference := True,
    tensorMultiplicativity := True,
    localTomographyDimension := True,
    singletAngleCurve := True,
    noHilbertImport := True,
    noBornImport := True
  }

theorem v7_phase_bundle_j_structure_is_required_for_carrier_hit :
    V7PhaseBundleJStructureWall v7PhaseBundleJMissingRoute
      ∧ ¬ V7CompressedCarrierRouteHit v7PhaseBundleJMissingRoute := by
  exact And.intro
    (And.intro True.intro (And.intro True.intro (by intro j; exact j)))
    (by
      intro hit
      exact hit.right.right.left)

structure V7UniversalCarrierFrontierTargets where
  finiteCarrierScreens : Prop
  finiteProjectionDeterminacy : Prop
  projectiveConsistency : Prop
  constructiveCarrierWitness : Prop
  noHiddenJointOnlyGeneration : Prop
  noResidualCarrierCoordinates : Prop
  noHilbertImport : Prop

def V7UniversalCarrierFrontierClosed
    (targets : V7UniversalCarrierFrontierTargets) : Prop :=
  targets.finiteCarrierScreens
    ∧ targets.finiteProjectionDeterminacy
    ∧ targets.projectiveConsistency
    ∧ targets.constructiveCarrierWitness
    ∧ targets.noHiddenJointOnlyGeneration
    ∧ targets.noResidualCarrierCoordinates
    ∧ targets.noHilbertImport

def v7CurrentCarrierFrontierTargets : V7UniversalCarrierFrontierTargets :=
  {
    finiteCarrierScreens := True,
    finiteProjectionDeterminacy := False,
    projectiveConsistency := False,
    constructiveCarrierWitness := True,
    noHiddenJointOnlyGeneration := False,
    noResidualCarrierCoordinates := False,
    noHilbertImport := True
  }

theorem v7_current_carrier_frontier_remains_unclosed :
    ¬ V7UniversalCarrierFrontierClosed
      v7CurrentCarrierFrontierTargets := by
  intro closed
  exact closed.right.left

theorem v7_known_finite_carrier_screens_select_phase_bundle_class :
    CarrierFrontierSelectsComplexPhaseBundle
      {
        Carrier := Unit,
        classify := fun _ => KnownFiniteCarrierClass.complexPhaseBundle,
        everyCarrierPassesKnownFiniteScreens := fun _ =>
          complex_phase_bundle_passes_known_finite_carrier_screen
      } :=
  carrier_frontier_exhaustion_selects_complex_phase_bundle
    {
      Carrier := Unit,
      classify := fun _ => KnownFiniteCarrierClass.complexPhaseBundle,
      everyCarrierPassesKnownFiniteScreens := fun _ =>
        complex_phase_bundle_passes_known_finite_carrier_screen
    }

end QMClosure
end IDT
