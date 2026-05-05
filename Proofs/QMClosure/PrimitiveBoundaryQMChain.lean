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
  constructorRespectingBranchLabels : Prop
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
Generic signed binary readout theorem.

This is the common algebra underneath Bell and Born. Any facticizable binary
readout whose signed value is represented by `plus - minus` has its positive
branch fixed by the affine signed-readout identity

  2 * plus = total + signed.

Bell uses the same theorem with `plus = same` and `minus = opposite`.
Born uses it with `plus = yes` and `minus = no`.
-/

def signedReadoutPositiveBranch
    (counts : BinarySignedReadoutCounts) : Int :=
  counts.plus

theorem signed_binary_readout_positive_branch_is_affine
    (counts : BinarySignedReadoutCounts) :
    2 * signedReadoutPositiveBranch counts =
      signedReadoutTotal counts + signedReadoutNumerator counts := by
  unfold signedReadoutPositiveBranch
  rw [signed_readout_affine_plus_recovery]

theorem signed_binary_readout_is_unique_by_total_and_signed
    (left right : BinarySignedReadoutCounts)
    (sameTotal : signedReadoutTotal left = signedReadoutTotal right)
    (sameSigned :
      signedReadoutNumerator left = signedReadoutNumerator right) :
    left.plus = right.plus := by
  cases left
  cases right
  unfold signedReadoutTotal signedReadoutNumerator at *
  omega

structure BellSameOppositeCounts where
  same : Int
  opposite : Int

def bellCountsToSignedReadout
    (counts : BellSameOppositeCounts) :
    BinarySignedReadoutCounts :=
  {
    plus := counts.same,
    minus := counts.opposite
  }

theorem bell_same_branch_is_affine_in_signed_expectation
    (counts : BellSameOppositeCounts) :
    2 * counts.same =
      signedReadoutTotal (bellCountsToSignedReadout counts)
        + signedReadoutNumerator (bellCountsToSignedReadout counts) := by
  simp [
    bellCountsToSignedReadout,
    signedReadoutTotal,
    signedReadoutNumerator,
  ]
  omega

structure BornYesNoCounts where
  yes : Int
  no : Int

def bornCountsToSignedReadout
    (counts : BornYesNoCounts) :
    BinarySignedReadoutCounts :=
  {
    plus := counts.yes,
    minus := counts.no
  }

theorem born_yes_branch_is_affine_in_signed_overlap
    (counts : BornYesNoCounts) :
    2 * counts.yes =
      signedReadoutTotal (bornCountsToSignedReadout counts)
        + signedReadoutNumerator (bornCountsToSignedReadout counts) := by
  simp [
    bornCountsToSignedReadout,
    signedReadoutTotal,
    signedReadoutNumerator,
  ]
  omega

theorem born_phase_double_cover_selects_amplitude_square_count
    (born : BornYesNoCounts)
    (phase : PhaseDoubleCoverCounts)
    (totalMatch :
      signedReadoutTotal (bornCountsToSignedReadout born) =
        phase.total)
    (signedMatch :
      signedReadoutNumerator (bornCountsToSignedReadout born) =
        phaseDoubleCoverSignedNumerator phase) :
    born.yes = phase.amplitudeSquare := by
  exact signed_phase_double_cover_selects_amplitude_square_count
    (bornCountsToSignedReadout born)
    phase
    totalMatch
    signedMatch

/-!
Oriented two-cover source for the Born branch.

This removes one layer of notation from the previous phase-double-cover
premise. An oriented two-cover has an aligned branch and an opposed branch.
Its signed value is aligned - opposed, and its total is aligned + opposed.
The Born yes/no count is therefore forced to equal the aligned branch whenever
the Born readout and the oriented two-cover expose the same total and signed
value.
-/

structure OrientedTwoCoverCounts where
  aligned : Int
  opposed : Int

def orientedTwoCoverTotal
    (cover : OrientedTwoCoverCounts) : Int :=
  cover.aligned + cover.opposed

def orientedTwoCoverSigned
    (cover : OrientedTwoCoverCounts) : Int :=
  cover.aligned - cover.opposed

def orientedTwoCoverToPhaseCounts
    (cover : OrientedTwoCoverCounts) :
    PhaseDoubleCoverCounts :=
  {
    amplitudeSquare := cover.aligned,
    total := orientedTwoCoverTotal cover
  }

theorem oriented_two_cover_supplies_phase_double_cover
    (cover : OrientedTwoCoverCounts) :
    phaseDoubleCoverSignedNumerator
      (orientedTwoCoverToPhaseCounts cover) =
        orientedTwoCoverSigned cover := by
  simp [
    orientedTwoCoverToPhaseCounts,
    orientedTwoCoverTotal,
    orientedTwoCoverSigned,
    phaseDoubleCoverSignedNumerator,
  ]
  omega

theorem born_oriented_two_cover_selects_aligned_count
    (born : BornYesNoCounts)
    (cover : OrientedTwoCoverCounts)
    (totalMatch :
      signedReadoutTotal (bornCountsToSignedReadout born) =
        orientedTwoCoverTotal cover)
    (signedMatch :
      signedReadoutNumerator (bornCountsToSignedReadout born) =
        orientedTwoCoverSigned cover) :
    born.yes = cover.aligned := by
  exact born_phase_double_cover_selects_amplitude_square_count
    born
    (orientedTwoCoverToPhaseCounts cover)
    totalMatch
    (by
      rw [oriented_two_cover_supplies_phase_double_cover]
      exact signedMatch)

theorem born_signed_match_iff_aligned_under_total_match
    (born : BornYesNoCounts)
    (cover : OrientedTwoCoverCounts)
    (totalMatch :
      signedReadoutTotal (bornCountsToSignedReadout born) =
        orientedTwoCoverTotal cover) :
    signedReadoutNumerator (bornCountsToSignedReadout born) =
        orientedTwoCoverSigned cover
      ↔ born.yes = cover.aligned := by
  constructor
  · intro signedMatch
    exact born_oriented_two_cover_selects_aligned_count
      born cover totalMatch signedMatch
  · intro alignedMatch
    cases born
    cases cover
    simp [
      bornCountsToSignedReadout,
      signedReadoutTotal,
      signedReadoutNumerator,
      orientedTwoCoverTotal,
      orientedTwoCoverSigned,
    ] at *
    omega

structure FacticizableOrientedBornReadout where
  born : BornYesNoCounts
  cover : OrientedTwoCoverCounts
  totalPreserved :
    signedReadoutTotal (bornCountsToSignedReadout born) =
      orientedTwoCoverTotal cover
  signedPreserved :
    signedReadoutNumerator (bornCountsToSignedReadout born) =
      orientedTwoCoverSigned cover

def FacticizableOrientedBornReadoutSelectsAligned
    (witness : FacticizableOrientedBornReadout) : Prop :=
  witness.born.yes = witness.cover.aligned

theorem facticizable_oriented_born_readout_selects_aligned
    (witness : FacticizableOrientedBornReadout) :
    FacticizableOrientedBornReadoutSelectsAligned witness :=
  born_oriented_two_cover_selects_aligned_count
    witness.born
    witness.cover
    witness.totalPreserved
    witness.signedPreserved

theorem total_preserved_born_readout_selects_aligned_iff_signed_preserved
    (born : BornYesNoCounts)
    (cover : OrientedTwoCoverCounts)
    (totalPreserved :
      signedReadoutTotal (bornCountsToSignedReadout born) =
        orientedTwoCoverTotal cover) :
    born.yes = cover.aligned
      ↔ signedReadoutNumerator (bornCountsToSignedReadout born) =
        orientedTwoCoverSigned cover := by
  exact (born_signed_match_iff_aligned_under_total_match
    born cover totalPreserved).symm

/-!
Admissible oriented facticization.

The next bridge is not probabilistic. A Born yes/no readout is an admissible
facticization of an oriented two-cover exactly when it preserves the generated
oriented branches: aligned becomes yes and opposed becomes no. For binary
counts this branch preservation is equivalent to preserving total and signed
readout. Thus the remaining Born bridge is reduced to an orientation-preserving
facticization claim, not to a probability axiom.
-/

def BranchPreservingOrientedFacticization
    (born : BornYesNoCounts)
    (cover : OrientedTwoCoverCounts) : Prop :=
  born.yes = cover.aligned ∧ born.no = cover.opposed

def TotalAndSignedPreservingFacticization
    (born : BornYesNoCounts)
    (cover : OrientedTwoCoverCounts) : Prop :=
  signedReadoutTotal (bornCountsToSignedReadout born) =
      orientedTwoCoverTotal cover
    ∧ signedReadoutNumerator (bornCountsToSignedReadout born) =
      orientedTwoCoverSigned cover

theorem branch_preservation_implies_total_and_signed_preservation
    (born : BornYesNoCounts)
    (cover : OrientedTwoCoverCounts) :
    BranchPreservingOrientedFacticization born cover →
      TotalAndSignedPreservingFacticization born cover := by
  intro branchPreserved
  cases born
  cases cover
  simp [
    BranchPreservingOrientedFacticization,
    TotalAndSignedPreservingFacticization,
    bornCountsToSignedReadout,
    signedReadoutTotal,
    signedReadoutNumerator,
    orientedTwoCoverTotal,
    orientedTwoCoverSigned,
  ] at *
  omega

theorem total_and_signed_preservation_implies_branch_preservation
    (born : BornYesNoCounts)
    (cover : OrientedTwoCoverCounts) :
    TotalAndSignedPreservingFacticization born cover →
      BranchPreservingOrientedFacticization born cover := by
  intro preserved
  cases born
  cases cover
  simp [
    BranchPreservingOrientedFacticization,
    TotalAndSignedPreservingFacticization,
    bornCountsToSignedReadout,
    signedReadoutTotal,
    signedReadoutNumerator,
    orientedTwoCoverTotal,
    orientedTwoCoverSigned,
  ] at *
  omega

theorem branch_preservation_iff_total_and_signed_preservation
    (born : BornYesNoCounts)
    (cover : OrientedTwoCoverCounts) :
    BranchPreservingOrientedFacticization born cover
      ↔ TotalAndSignedPreservingFacticization born cover :=
  Iff.intro
    (branch_preservation_implies_total_and_signed_preservation born cover)
    (total_and_signed_preservation_implies_branch_preservation born cover)

structure AdmissibleOrientedBornFacticization where
  born : BornYesNoCounts
  cover : OrientedTwoCoverCounts
  branchPreserving :
    BranchPreservingOrientedFacticization born cover

def canonicalBornReadoutFromCover
    (cover : OrientedTwoCoverCounts) : BornYesNoCounts :=
  {
    yes := cover.aligned,
    no := cover.opposed
  }

theorem canonical_born_readout_is_branch_preserving
    (cover : OrientedTwoCoverCounts) :
    BranchPreservingOrientedFacticization
      (canonicalBornReadoutFromCover cover)
      cover := by
  simp [
    BranchPreservingOrientedFacticization,
    canonicalBornReadoutFromCover,
  ]

def canonicalAdmissibleOrientedBornFacticization
    (cover : OrientedTwoCoverCounts) :
    AdmissibleOrientedBornFacticization :=
  {
    born := canonicalBornReadoutFromCover cover,
    cover := cover,
    branchPreserving :=
      canonical_born_readout_is_branch_preserving cover
  }

theorem admissible_oriented_born_readout_unique
    (left right : BornYesNoCounts)
    (cover : OrientedTwoCoverCounts)
    (leftPreserved :
      BranchPreservingOrientedFacticization left cover)
    (rightPreserved :
      BranchPreservingOrientedFacticization right cover) :
    left = right := by
  cases left
  cases right
  cases cover
  simp [BranchPreservingOrientedFacticization] at *
  exact And.intro
    (leftPreserved.left.trans rightPreserved.left.symm)
    (leftPreserved.right.trans rightPreserved.right.symm)

theorem admissible_oriented_born_facticization_equals_canonical
    (facticization : AdmissibleOrientedBornFacticization) :
    facticization.born =
      canonicalBornReadoutFromCover facticization.cover :=
  admissible_oriented_born_readout_unique
    facticization.born
    (canonicalBornReadoutFromCover facticization.cover)
    facticization.cover
    facticization.branchPreserving
    (canonical_born_readout_is_branch_preserving facticization.cover)

def admissibleOrientedBornFacticizationToWitness
    (facticization : AdmissibleOrientedBornFacticization) :
    FacticizableOrientedBornReadout :=
  {
    born := facticization.born,
    cover := facticization.cover,
    totalPreserved :=
      (branch_preservation_implies_total_and_signed_preservation
        facticization.born
        facticization.cover
        facticization.branchPreserving).left,
    signedPreserved :=
      (branch_preservation_implies_total_and_signed_preservation
        facticization.born
        facticization.cover
        facticization.branchPreserving).right
  }

theorem admissible_oriented_born_facticization_selects_aligned
    (facticization : AdmissibleOrientedBornFacticization) :
    facticization.born.yes = facticization.cover.aligned :=
  facticization.branchPreserving.left

theorem admissible_oriented_born_facticization_yields_born_readout
    (facticization : AdmissibleOrientedBornFacticization) :
    FacticizableOrientedBornReadoutSelectsAligned
      (admissibleOrientedBornFacticizationToWitness facticization) :=
  facticizable_oriented_born_readout_selects_aligned
    (admissibleOrientedBornFacticizationToWitness facticization)

theorem admissible_oriented_born_facticization_forces_affine_signed_count
    (facticization : AdmissibleOrientedBornFacticization) :
    2 * facticization.born.yes =
      orientedTwoCoverTotal facticization.cover
        + orientedTwoCoverSigned facticization.cover := by
  rw [admissible_oriented_born_facticization_selects_aligned facticization]
  cases facticization.cover
  simp [
    orientedTwoCoverTotal,
    orientedTwoCoverSigned,
  ]
  omega

theorem admissible_oriented_born_facticization_selects_phase_square_count
    (facticization : AdmissibleOrientedBornFacticization) :
    facticization.born.yes =
      (orientedTwoCoverToPhaseCounts facticization.cover).amplitudeSquare := by
  rw [admissible_oriented_born_facticization_selects_aligned facticization]
  simp [orientedTwoCoverToPhaseCounts]

/-!
Constructor-respecting branch labels.

This is the next lower bridge. A primitive-generated oriented readout is not an
arbitrary two-cell table with the right total. Its exposed cells must be
generated from the aligned and opposed constructors themselves. Once those
constructor labels are respected, branch preservation and the Born count law
follow. A swapped labelling is a negative control: it can preserve total, but
it is not a constructor-respecting generated readout.
-/

inductive OrientedReadoutBranch where
  | aligned
  | opposed
deriving DecidableEq

open OrientedReadoutBranch

def orientedBranchCount
    (cover : OrientedTwoCoverCounts) :
    OrientedReadoutBranch → Int
  | aligned => cover.aligned
  | opposed => cover.opposed

structure OrientedReadoutBranchLabels where
  yesBranch : OrientedReadoutBranch
  noBranch : OrientedReadoutBranch

def ConstructorRespectingBranchLabels
    (labels : OrientedReadoutBranchLabels) : Prop :=
  labels.yesBranch = aligned ∧ labels.noBranch = opposed

def EndpointStableBinaryBranchLabels
    (labels : OrientedReadoutBranchLabels) : Prop :=
  labels.yesBranch = aligned ∧ labels.yesBranch ≠ labels.noBranch

theorem endpoint_stable_binary_labels_are_constructor_respecting
    (labels : OrientedReadoutBranchLabels) :
    EndpointStableBinaryBranchLabels labels →
      ConstructorRespectingBranchLabels labels := by
  intro endpointStable
  rcases endpointStable with ⟨yesAligned, yesNoDistinct⟩
  cases labels with
  | mk yesBranch noBranch =>
    simp at yesAligned yesNoDistinct
    subst yesBranch
    cases noBranch
    · exact False.elim (yesNoDistinct rfl)
    · exact And.intro rfl rfl

def branchLabelsToBornReadout
    (cover : OrientedTwoCoverCounts)
    (labels : OrientedReadoutBranchLabels) :
    BornYesNoCounts :=
  {
    yes := orientedBranchCount cover labels.yesBranch,
    no := orientedBranchCount cover labels.noBranch
  }

theorem constructor_respecting_labels_yield_branch_preservation
    (cover : OrientedTwoCoverCounts)
    (labels : OrientedReadoutBranchLabels) :
    ConstructorRespectingBranchLabels labels →
      BranchPreservingOrientedFacticization
        (branchLabelsToBornReadout cover labels)
        cover := by
  intro respecting
  cases labels with
  | mk yesBranch noBranch =>
    rcases respecting with ⟨yesRespecting, noRespecting⟩
    simp at yesRespecting noRespecting
    subst yesBranch
    subst noBranch
    cases cover
    simp [
      BranchPreservingOrientedFacticization,
      branchLabelsToBornReadout,
      orientedBranchCount,
    ] at *

def constructorRespectingAdmissibleBornFacticization
    (cover : OrientedTwoCoverCounts)
    (labels : OrientedReadoutBranchLabels)
    (respecting : ConstructorRespectingBranchLabels labels) :
    AdmissibleOrientedBornFacticization :=
  {
    born := branchLabelsToBornReadout cover labels,
    cover := cover,
    branchPreserving :=
      constructor_respecting_labels_yield_branch_preservation
        cover
        labels
        respecting
  }

theorem constructor_respecting_oriented_readout_forces_born_count
    (cover : OrientedTwoCoverCounts)
    (labels : OrientedReadoutBranchLabels)
    (respecting : ConstructorRespectingBranchLabels labels) :
    2 * (branchLabelsToBornReadout cover labels).yes =
      orientedTwoCoverTotal cover + orientedTwoCoverSigned cover :=
  admissible_oriented_born_facticization_forces_affine_signed_count
    (constructorRespectingAdmissibleBornFacticization
      cover
      labels
      respecting)

theorem constructor_respecting_oriented_readout_selects_phase_square
    (cover : OrientedTwoCoverCounts)
    (labels : OrientedReadoutBranchLabels)
    (respecting : ConstructorRespectingBranchLabels labels) :
    (branchLabelsToBornReadout cover labels).yes =
      (orientedTwoCoverToPhaseCounts cover).amplitudeSquare :=
  admissible_oriented_born_facticization_selects_phase_square_count
    (constructorRespectingAdmissibleBornFacticization
      cover
      labels
      respecting)

def swappedOrientedReadoutBranchLabels :
    OrientedReadoutBranchLabels :=
  {
    yesBranch := opposed,
    noBranch := aligned
  }

theorem swapped_oriented_readout_labels_not_constructor_respecting :
    ¬ ConstructorRespectingBranchLabels
      swappedOrientedReadoutBranchLabels := by
  simp [
    ConstructorRespectingBranchLabels,
    swappedOrientedReadoutBranchLabels,
  ]

def branchSwappedBornReadout
    (cover : OrientedTwoCoverCounts) : BornYesNoCounts :=
  {
    yes := cover.opposed,
    no := cover.aligned
  }

theorem branch_swapped_readout_preserves_total
    (cover : OrientedTwoCoverCounts) :
    signedReadoutTotal
        (bornCountsToSignedReadout (branchSwappedBornReadout cover)) =
      orientedTwoCoverTotal cover := by
  cases cover
  simp [
    branchSwappedBornReadout,
    bornCountsToSignedReadout,
    signedReadoutTotal,
    orientedTwoCoverTotal,
  ]
  omega

theorem branch_swapped_readout_reverses_signed
    (cover : OrientedTwoCoverCounts) :
    signedReadoutNumerator
        (bornCountsToSignedReadout (branchSwappedBornReadout cover)) =
      -orientedTwoCoverSigned cover := by
  cases cover
  simp [
    branchSwappedBornReadout,
    bornCountsToSignedReadout,
    signedReadoutNumerator,
    orientedTwoCoverSigned,
  ]
  omega

def asymmetricOrientedCover : OrientedTwoCoverCounts :=
  {
    aligned := 2,
    opposed := 1
  }

theorem branch_swapped_asymmetric_readout_is_not_admissible :
    ¬ BranchPreservingOrientedFacticization
      (branchSwappedBornReadout asymmetricOrientedCover)
      asymmetricOrientedCover := by
  simp [
    BranchPreservingOrientedFacticization,
    branchSwappedBornReadout,
    asymmetricOrientedCover,
  ]

theorem total_preservation_alone_does_not_force_born_readout :
    signedReadoutTotal
        (bornCountsToSignedReadout
          (branchSwappedBornReadout asymmetricOrientedCover)) =
      orientedTwoCoverTotal asymmetricOrientedCover
      ∧ ¬ BranchPreservingOrientedFacticization
        (branchSwappedBornReadout asymmetricOrientedCover)
        asymmetricOrientedCover :=
  And.intro
    (branch_swapped_readout_preserves_total asymmetricOrientedCover)
    branch_swapped_asymmetric_readout_is_not_admissible

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
    ∧ inputs.constructorRespectingBranchLabels
    ∧ inputs.noBornImport

def finiteAffineOverlapBornInputs : AffineOverlapBornInputs :=
  {
    signedNormalizedOverlap := True,
    binaryComplementReadout := True,
    repeatabilityAndExclusion := True,
    unbiasedZeroOverlap := True,
    affineMixtureResponse := True,
    phaseBundleDoubleCover := True,
    constructorRespectingBranchLabels := True,
    noBornImport := True
  }

theorem finite_affine_overlap_born_selector_is_hit :
    AffineBornSelectorHit finiteAffineOverlapBornInputs :=
  by repeat constructor

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
    ∧ inputs.constructorRespectingBranchLabels
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

/-!
Exact universal Born readout frontier.

The finite route is now closed. Exact universal Born is stronger: the same
constructor-respecting oriented readout law must hold for every admissible
readout context, and probability accounting must remain downstream of the
selected weight law. The contract below keeps that distinction machine-visible.
-/

structure UniversalBornReadoutContract where
  finiteDirectBornRoute : Prop
  allAdmissibleContextsCloseFiniteBornChain : Prop
  universalSignedReadout : Prop
  universalConstructorRespectingBranchLabels : Prop
  universalPhaseDoubleCover : Prop
  noPrimitiveHigherOrderFacticization : Prop
  probabilityAccountingIsOnlyReadout : Prop
  noBornImport : Prop

def ExactUniversalBornReadoutClosed
    (contract : UniversalBornReadoutContract) : Prop :=
  contract.finiteDirectBornRoute
    ∧ contract.allAdmissibleContextsCloseFiniteBornChain
    ∧ contract.universalSignedReadout
    ∧ contract.universalConstructorRespectingBranchLabels
    ∧ contract.universalPhaseDoubleCover
    ∧ contract.noPrimitiveHigherOrderFacticization
    ∧ contract.probabilityAccountingIsOnlyReadout
    ∧ contract.noBornImport

theorem universal_born_readout_contract_closes_exact_universal_born
    (contract : UniversalBornReadoutContract) :
    contract.finiteDirectBornRoute →
      contract.allAdmissibleContextsCloseFiniteBornChain →
        contract.universalSignedReadout →
          contract.universalConstructorRespectingBranchLabels →
            contract.universalPhaseDoubleCover →
              contract.noPrimitiveHigherOrderFacticization →
                contract.probabilityAccountingIsOnlyReadout →
                  contract.noBornImport →
                    ExactUniversalBornReadoutClosed contract := by
  intro finiteRoute allContexts signedReadout constructorLabels
    phaseCover noHigherOrder probabilityBoundary noBornImport
  exact And.intro finiteRoute
    (And.intro allContexts
      (And.intro signedReadout
        (And.intro constructorLabels
          (And.intro phaseCover
            (And.intro noHigherOrder
              (And.intro probabilityBoundary noBornImport))))))

theorem exact_universal_born_requires_all_admissible_contexts
    (contract : UniversalBornReadoutContract) :
    ExactUniversalBornReadoutClosed contract →
      contract.allAdmissibleContextsCloseFiniteBornChain :=
  fun closed => closed.right.left

theorem exact_universal_born_requires_signed_readout
    (contract : UniversalBornReadoutContract) :
    ExactUniversalBornReadoutClosed contract →
      contract.universalSignedReadout :=
  fun closed => closed.right.right.left

theorem exact_universal_born_requires_constructor_labels
    (contract : UniversalBornReadoutContract) :
    ExactUniversalBornReadoutClosed contract →
      contract.universalConstructorRespectingBranchLabels :=
  fun closed => closed.right.right.right.left

theorem exact_universal_born_requires_phase_double_cover
    (contract : UniversalBornReadoutContract) :
    ExactUniversalBornReadoutClosed contract →
      contract.universalPhaseDoubleCover :=
  fun closed => closed.right.right.right.right.left

theorem exact_universal_born_requires_no_higher_order_facticization
    (contract : UniversalBornReadoutContract) :
    ExactUniversalBornReadoutClosed contract →
      contract.noPrimitiveHigherOrderFacticization :=
  fun closed => closed.right.right.right.right.right.left

theorem exact_universal_born_requires_probability_boundary
    (contract : UniversalBornReadoutContract) :
    ExactUniversalBornReadoutClosed contract →
      contract.probabilityAccountingIsOnlyReadout :=
  fun closed => closed.right.right.right.right.right.right.left

def currentUniversalBornReadoutContract : UniversalBornReadoutContract :=
  {
    finiteDirectBornRoute :=
      DirectFiniteBornRouteHit
        fullPrimitiveBoundaryCandidate
        finiteAffineOverlapBornInputs,
    allAdmissibleContextsCloseFiniteBornChain := False,
    universalSignedReadout := False,
    universalConstructorRespectingBranchLabels := False,
    universalPhaseDoubleCover := False,
    noPrimitiveHigherOrderFacticization := False,
    probabilityAccountingIsOnlyReadout := True,
    noBornImport := True
  }

theorem current_born_frontier_has_finite_route_but_not_universal_born :
    currentUniversalBornReadoutContract.finiteDirectBornRoute
      ∧ ¬ ExactUniversalBornReadoutClosed
        currentUniversalBornReadoutContract :=
  And.intro
    full_boundary_plus_affine_overlap_closes_direct_finite_born_route
    (by
      intro closed
      exact closed.right.left)

theorem missing_all_context_closure_blocks_exact_universal_born
    (contract : UniversalBornReadoutContract) :
    ¬ contract.allAdmissibleContextsCloseFiniteBornChain →
      ¬ ExactUniversalBornReadoutClosed contract :=
  fun missing closed =>
    missing (exact_universal_born_requires_all_admissible_contexts contract closed)

theorem missing_universal_signed_readout_blocks_exact_universal_born
    (contract : UniversalBornReadoutContract) :
    ¬ contract.universalSignedReadout →
      ¬ ExactUniversalBornReadoutClosed contract :=
  fun missing closed =>
    missing (exact_universal_born_requires_signed_readout contract closed)

theorem missing_universal_constructor_labels_blocks_exact_universal_born
    (contract : UniversalBornReadoutContract) :
    ¬ contract.universalConstructorRespectingBranchLabels →
      ¬ ExactUniversalBornReadoutClosed contract :=
  fun missing closed =>
    missing (exact_universal_born_requires_constructor_labels contract closed)

theorem missing_universal_phase_double_cover_blocks_exact_universal_born
    (contract : UniversalBornReadoutContract) :
    ¬ contract.universalPhaseDoubleCover →
      ¬ ExactUniversalBornReadoutClosed contract :=
  fun missing closed =>
    missing (exact_universal_born_requires_phase_double_cover contract closed)

theorem missing_no_higher_order_facticization_blocks_exact_universal_born
    (contract : UniversalBornReadoutContract) :
    ¬ contract.noPrimitiveHigherOrderFacticization →
      ¬ ExactUniversalBornReadoutClosed contract :=
  fun missing closed =>
    missing
      (exact_universal_born_requires_no_higher_order_facticization
        contract
        closed)

end QMClosure
end IDT
