import Proofs.QMClosure.S2BornProofSearch

namespace IDT
namespace QMClosure

/-!
Primitive-boundary finite-QM chain audit.

This file does not prove QM. It machine-checks the current boundary:
the B1-style bound primitive interface is not enough by itself to close the
finite Born/phase-bundle chain. A stronger primitive-boundary package would
need compatible kernel additivity, normalized overlap uniqueness, phase-bundle
J, and proper-subcontext/pairwise coverage.
-/

structure PrimitiveBoundaryCandidate where
  b1BoundInterface : Prop
  noTargetImports : Prop
  compatibleKernelAdditivity : Prop
  normalizedOverlapUniqueness : Prop
  phaseBundleJ : Prop
  properSubcontextPairwiseCoverage : Prop
  noHiddenTernaryFact : Prop

def B1BoundInterfaceOnly (candidate : PrimitiveBoundaryCandidate) : Prop :=
  candidate.b1BoundInterface ∧ candidate.noTargetImports

def PrimitiveBoundarySuppliesFiniteChainInputs
    (candidate : PrimitiveBoundaryCandidate) : Prop :=
  candidate.b1BoundInterface
    ∧ candidate.noTargetImports
    ∧ candidate.compatibleKernelAdditivity
    ∧ candidate.normalizedOverlapUniqueness
    ∧ candidate.phaseBundleJ

def PrimitiveBoundaryClosesPairwiseCoverage
    (candidate : PrimitiveBoundaryCandidate) : Prop :=
  candidate.properSubcontextPairwiseCoverage
    ∧ candidate.noHiddenTernaryFact

def PrimitiveBoundaryClosesFiniteBornChain
    (candidate : PrimitiveBoundaryCandidate) : Prop :=
  PrimitiveBoundarySuppliesFiniteChainInputs candidate
    ∧ PrimitiveBoundaryClosesPairwiseCoverage candidate

def b1InterfaceOnlyBoundary : PrimitiveBoundaryCandidate :=
  {
    b1BoundInterface := True,
    noTargetImports := True,
    compatibleKernelAdditivity := False,
    normalizedOverlapUniqueness := False,
    phaseBundleJ := False,
    properSubcontextPairwiseCoverage := False,
    noHiddenTernaryFact := False
  }

theorem b1_interface_only_is_bound_but_not_chain_closing :
    B1BoundInterfaceOnly b1InterfaceOnlyBoundary
      ∧ ¬ PrimitiveBoundaryClosesFiniteBornChain b1InterfaceOnlyBoundary :=
  And.intro
    (And.intro True.intro True.intro)
    (by
      intro closed
      exact closed.left.right.right.left)

def kernelOverlapJWithoutPairwiseBoundary : PrimitiveBoundaryCandidate :=
  {
    b1BoundInterface := True,
    noTargetImports := True,
    compatibleKernelAdditivity := True,
    normalizedOverlapUniqueness := True,
    phaseBundleJ := True,
    properSubcontextPairwiseCoverage := False,
    noHiddenTernaryFact := False
  }

theorem kernel_overlap_j_without_pairwise_coverage_is_not_enough :
    PrimitiveBoundarySuppliesFiniteChainInputs
        kernelOverlapJWithoutPairwiseBoundary
      ∧ ¬ PrimitiveBoundaryClosesFiniteBornChain
        kernelOverlapJWithoutPairwiseBoundary :=
  And.intro
    (And.intro True.intro
      (And.intro True.intro
        (And.intro True.intro
          (And.intro True.intro True.intro))))
    (by
      intro closed
      exact closed.right.left)

def fullPrimitiveBoundaryCandidate : PrimitiveBoundaryCandidate :=
  {
    b1BoundInterface := True,
    noTargetImports := True,
    compatibleKernelAdditivity := True,
    normalizedOverlapUniqueness := True,
    phaseBundleJ := True,
    properSubcontextPairwiseCoverage := True,
    noHiddenTernaryFact := True
  }

theorem full_primitive_boundary_candidate_closes_finite_born_chain :
    PrimitiveBoundaryClosesFiniteBornChain fullPrimitiveBoundaryCandidate :=
  And.intro
    (And.intro True.intro
      (And.intro True.intro
        (And.intro True.intro
          (And.intro True.intro True.intro))))
    (And.intro True.intro True.intro)

theorem full_primitive_boundary_candidate_supplies_checked_finite_chain :
    PrimitiveBoundaryClosesFiniteBornChain fullPrimitiveBoundaryCandidate
      ∧ FiniteBornChainHit finiteBornChainEvidence :=
  And.intro
    full_primitive_boundary_candidate_closes_finite_born_chain
    finite_born_chain_evidence_is_hit

/-!
Born selector reduction.

The finite Python screen checks the numerical/functional side: among bounded
binary probability selectors over signed normalized overlap, repeatability,
complement symmetry, unbiased zero, affine mixture response, and the
phase-bundle double cover select `p = (1 + r) / 2`, equivalently `p = |a|^2`
when `r = 2|a|^2 - 1`.

This Lean block records the dependency shape only. The remaining theorem
obligation is to derive signed expectation readout and affine mixture response
from the primitive boundary, not to assume them because they yield Born.
-/

structure AffineOverlapBornInputs where
  signedNormalizedOverlap : Prop
  binaryComplementReadout : Prop
  repeatabilityAndExclusion : Prop
  unbiasedZeroOverlap : Prop
  affineMixtureResponse : Prop
  phaseBundleDoubleCover : Prop
  noBornImport : Prop

/-!
Finite signed-overlap arithmetic.

This is the exact algebraic core behind the finite selector screen. If a binary
readout has signed expectation numerator `plus - minus`, and the phase bundle
supplies `signed = 2 * amplitudeSquare - total`, then the exposed `plus`
count is forced to be the amplitude-square count. This proves only the
arithmetic recovery once the semantic premises are supplied.
-/

structure BinarySignedReadoutCounts where
  plus : Int
  minus : Int

def signedReadoutTotal (counts : BinarySignedReadoutCounts) : Int :=
  counts.plus + counts.minus

def signedReadoutNumerator (counts : BinarySignedReadoutCounts) : Int :=
  counts.plus - counts.minus

theorem signed_readout_affine_plus_recovery
    (counts : BinarySignedReadoutCounts) :
    signedReadoutTotal counts + signedReadoutNumerator counts =
      2 * counts.plus := by
  cases counts
  unfold signedReadoutTotal signedReadoutNumerator
  omega

structure PhaseDoubleCoverCounts where
  amplitudeSquare : Int
  total : Int

def phaseDoubleCoverSignedNumerator
    (counts : PhaseDoubleCoverCounts) : Int :=
  2 * counts.amplitudeSquare - counts.total

theorem phase_double_cover_affine_recovery
    (counts : PhaseDoubleCoverCounts) :
    counts.total + phaseDoubleCoverSignedNumerator counts =
      2 * counts.amplitudeSquare := by
  cases counts
  unfold phaseDoubleCoverSignedNumerator
  omega

theorem signed_phase_double_cover_selects_amplitude_square_count
    (readout : BinarySignedReadoutCounts)
    (phase : PhaseDoubleCoverCounts)
    (totalMatch : signedReadoutTotal readout = phase.total)
    (signedMatch :
      signedReadoutNumerator readout =
        phaseDoubleCoverSignedNumerator phase) :
    readout.plus = phase.amplitudeSquare := by
  cases readout
  cases phase
  unfold signedReadoutTotal signedReadoutNumerator
    phaseDoubleCoverSignedNumerator at *
  omega

/-!
External-randomizer frequency calibration.

The affine step is likewise recorded at finite-count level. A randomized
mixture of two already facticizable binary records has the cross-multiplied hit
count given by the branch-frequency weighted sum of the two branch hit counts.
This is the operational frequency fact; it is not an imported convex
probability axiom.
-/

structure BinaryFrequencyRecord where
  hits : Int
  trials : Int

structure ExternalRandomizerCounts where
  leftTrials : Int
  rightTrials : Int

def randomizedFrequencyHits
    (randomizer : ExternalRandomizerCounts)
    (left right : BinaryFrequencyRecord) : Int :=
  randomizer.leftTrials * left.hits * right.trials
    + randomizer.rightTrials * right.hits * left.trials

def randomizedFrequencyTrials
    (randomizer : ExternalRandomizerCounts)
    (left right : BinaryFrequencyRecord) : Int :=
  (randomizer.leftTrials + randomizer.rightTrials)
    * left.trials
    * right.trials

def affineFrequencyMixtureNumerator
    (randomizer : ExternalRandomizerCounts)
    (left right : BinaryFrequencyRecord) : Int :=
  randomizer.leftTrials * left.hits * right.trials
    + randomizer.rightTrials * right.hits * left.trials

theorem randomized_frequency_hits_are_affine
    (randomizer : ExternalRandomizerCounts)
    (left right : BinaryFrequencyRecord) :
    randomizedFrequencyHits randomizer left right =
      affineFrequencyMixtureNumerator randomizer left right := by
  rfl

def chooseLeftRandomizer : ExternalRandomizerCounts :=
  {
    leftTrials := 1,
    rightTrials := 0
  }

def chooseRightRandomizer : ExternalRandomizerCounts :=
  {
    leftTrials := 0,
    rightTrials := 1
  }

theorem randomized_frequency_left_endpoint
    (left right : BinaryFrequencyRecord) :
    randomizedFrequencyHits chooseLeftRandomizer left right =
      left.hits * right.trials
    ∧ randomizedFrequencyTrials chooseLeftRandomizer left right =
      left.trials * right.trials := by
  simp [
    randomizedFrequencyHits,
    randomizedFrequencyTrials,
    chooseLeftRandomizer,
  ]

theorem randomized_frequency_right_endpoint
    (left right : BinaryFrequencyRecord) :
    randomizedFrequencyHits chooseRightRandomizer left right =
      right.hits * left.trials
    ∧ randomizedFrequencyTrials chooseRightRandomizer left right =
      left.trials * right.trials := by
  simp [
    randomizedFrequencyHits,
    randomizedFrequencyTrials,
    chooseRightRandomizer,
  ]

def AffineBornSelectorHit (inputs : AffineOverlapBornInputs) : Prop :=
  inputs.signedNormalizedOverlap
    ∧ inputs.binaryComplementReadout
    ∧ inputs.repeatabilityAndExclusion
    ∧ inputs.unbiasedZeroOverlap
    ∧ inputs.affineMixtureResponse
    ∧ inputs.phaseBundleDoubleCover
    ∧ inputs.noBornImport

def finiteAffineOverlapBornInputs : AffineOverlapBornInputs :=
  {
    signedNormalizedOverlap := True,
    binaryComplementReadout := True,
    repeatabilityAndExclusion := True,
    unbiasedZeroOverlap := True,
    affineMixtureResponse := True,
    phaseBundleDoubleCover := True,
    noBornImport := True
  }

theorem finite_affine_overlap_born_selector_is_hit :
    AffineBornSelectorHit finiteAffineOverlapBornInputs :=
  And.intro True.intro
    (And.intro True.intro
      (And.intro True.intro
        (And.intro True.intro
          (And.intro True.intro
            (And.intro True.intro True.intro)))))

/-!
Positive quadratic actualization reduction.

The remaining Born wall is not solved by probability normalization. On the
direct finite route it is reduced to the signed-overlap selector gates:
normalized overlap has signed-expectation semantics, the binary readout has
the right endpoint/complement/zero behavior, facticizable mixtures read out
affinely, and the phase bundle supplies the double-cover relation. This is a
candidate reduction of the actualization principle, not a universal Born proof.
-/

def PositiveQuadraticActualizationFromSignedOverlap
    (inputs : AffineOverlapBornInputs) : Prop :=
  inputs.signedNormalizedOverlap
    ∧ inputs.binaryComplementReadout
    ∧ inputs.repeatabilityAndExclusion
    ∧ inputs.unbiasedZeroOverlap
    ∧ inputs.affineMixtureResponse
    ∧ inputs.phaseBundleDoubleCover
    ∧ inputs.noBornImport

theorem affine_overlap_born_selector_supplies_positive_quadratic_actualization
    (inputs : AffineOverlapBornInputs) :
    AffineBornSelectorHit inputs →
      PositiveQuadraticActualizationFromSignedOverlap inputs := by
  intro hit
  exact hit

theorem finite_affine_overlap_supplies_positive_quadratic_actualization :
    PositiveQuadraticActualizationFromSignedOverlap
      finiteAffineOverlapBornInputs :=
  affine_overlap_born_selector_supplies_positive_quadratic_actualization
    finiteAffineOverlapBornInputs
    finite_affine_overlap_born_selector_is_hit

def DirectFiniteBornRouteHit
    (boundary : PrimitiveBoundaryCandidate)
    (inputs : AffineOverlapBornInputs) : Prop :=
  PrimitiveBoundaryClosesFiniteBornChain boundary
    ∧ FiniteBornChainHit finiteBornChainEvidence
    ∧ AffineBornSelectorHit inputs

theorem full_boundary_plus_affine_overlap_closes_direct_finite_born_route :
    DirectFiniteBornRouteHit
      fullPrimitiveBoundaryCandidate
      finiteAffineOverlapBornInputs :=
  And.intro
    full_primitive_boundary_candidate_closes_finite_born_chain
    (And.intro
      finite_born_chain_evidence_is_hit
      finite_affine_overlap_born_selector_is_hit)

theorem direct_finite_born_route_supplies_actualization_reduction
    (boundary : PrimitiveBoundaryCandidate)
    (inputs : AffineOverlapBornInputs) :
    DirectFiniteBornRouteHit boundary inputs →
      PrimitiveBoundaryClosesFiniteBornChain boundary
        ∧ PositiveQuadraticActualizationFromSignedOverlap inputs := by
  intro route
  exact And.intro route.left
    (affine_overlap_born_selector_supplies_positive_quadratic_actualization
      inputs
      route.right.right)

theorem finite_actualization_reduction_still_not_universal_born_or_s2 :
    PrimitiveBoundaryClosesFiniteBornChain fullPrimitiveBoundaryCandidate
      ∧ PositiveQuadraticActualizationFromSignedOverlap
          finiteAffineOverlapBornInputs
      ∧ ¬ UniversalBornS2Closed finiteBornChainEvidence :=
  And.intro
    full_primitive_boundary_candidate_closes_finite_born_chain
    (And.intro
      finite_affine_overlap_supplies_positive_quadratic_actualization
      (by
        intro closed
        exact closed.left))

theorem direct_finite_born_route_still_does_not_close_universal_born_or_s2 :
    DirectFiniteBornRouteHit
        fullPrimitiveBoundaryCandidate
        finiteAffineOverlapBornInputs
      ∧ ¬ UniversalBornS2Closed finiteBornChainEvidence :=
  And.intro
    full_boundary_plus_affine_overlap_closes_direct_finite_born_route
    (by
      intro closed
      exact closed.left)

end QMClosure
end IDT
