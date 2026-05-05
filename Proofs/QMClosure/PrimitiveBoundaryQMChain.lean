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
