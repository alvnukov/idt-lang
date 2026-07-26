import Mathlib

namespace IDT.QMClosure

/-!
# Boundary-reversible completion probe

This file records a finite falsification probe for the candidate primitive
construction in which observable processes are boundary shadows of reversible
completions, modulo reversible changes of the hidden boundary.

The target is motivated by Nakahira, arXiv:2605.23217 (2026): inside a
finite-dimensional causal operational-probabilistic theory, local equivalence
plus equivalent-system purification selects standard finite-dimensional complex
quantum theory. That theorem starts above the substrate level: real
probabilities, convex mixtures, serial and parallel composition, finite
dimensionality, and causality already belong to its ambient framework.

The results below therefore check only the smallest concrete separator pattern:

* a classical bit passes the local dimension count but its uniform mixed state
  is not the marginal of a classical pure joint state;
* a quadratic joint amplitude has two explicit purifications of the uniform
  bit related by an involutive hidden-boundary rewrite;
* real and quaternionic qubit dimension profiles fail local tomography, while
  the classical and complex profiles pass it;
* no universal reconstruction, probability derivation, Standard Model result,
  or gravity result is claimed.
-/

structure BitWeights where
  zero : Nat
  one : Nat
deriving DecidableEq, Repr

def uniformBitWeights : BitWeights := ⟨1, 1⟩

inductive ClassicalPureJoint where
  | zeroZero
  | zeroOne
  | oneZero
  | oneOne
deriving DecidableEq, Repr

def classicalFirstMarginal : ClassicalPureJoint → BitWeights
  | .zeroZero => ⟨2, 0⟩
  | .zeroOne => ⟨2, 0⟩
  | .oneZero => ⟨0, 2⟩
  | .oneOne => ⟨0, 2⟩

theorem classical_uniform_bit_has_no_pure_joint_marginal :
    ∀ joint : ClassicalPureJoint,
      classicalFirstMarginal joint ≠ uniformBitWeights := by
  intro joint
  cases joint <;> decide

structure NatAmplitude2x2 where
  a00 : Nat
  a01 : Nat
  a10 : Nat
  a11 : Nat
deriving DecidableEq, Repr

def quadraticFirstMarginal (amplitude : NatAmplitude2x2) : BitWeights :=
  ⟨amplitude.a00 ^ 2 + amplitude.a01 ^ 2,
   amplitude.a10 ^ 2 + amplitude.a11 ^ 2⟩

def bellLikeAmplitude : NatAmplitude2x2 :=
  ⟨1, 0, 0, 1⟩

def crossBellLikeAmplitude : NatAmplitude2x2 :=
  ⟨0, 1, 1, 0⟩

def swapHiddenBoundary (amplitude : NatAmplitude2x2) : NatAmplitude2x2 :=
  ⟨amplitude.a01, amplitude.a00, amplitude.a11, amplitude.a10⟩

theorem bell_like_amplitude_purifies_uniform_bit :
    quadraticFirstMarginal bellLikeAmplitude = uniformBitWeights := by
  rfl

theorem cross_bell_like_amplitude_purifies_uniform_bit :
    quadraticFirstMarginal crossBellLikeAmplitude = uniformBitWeights := by
  rfl

theorem hidden_boundary_swap_relates_sample_purifications :
    swapHiddenBoundary bellLikeAmplitude = crossBellLikeAmplitude := by
  rfl

theorem hidden_boundary_swap_is_involutive :
    Function.Involutive swapHiddenBoundary := by
  intro amplitude
  cases amplitude
  rfl

structure SampleEquivalentSystemPurification (State Pure : Type) where
  target : State
  marginal : Pure → State
  first : Pure
  second : Pure
  hiddenRewrite : Pure → Pure
  firstPurifies : marginal first = target
  secondPurifies : marginal second = target
  hiddenRewriteRelates : hiddenRewrite first = second
  hiddenRewriteReversible : Function.Involutive hiddenRewrite

def uniformBitAmplitudePurification :
    SampleEquivalentSystemPurification BitWeights NatAmplitude2x2 :=
  {
    target := uniformBitWeights
    marginal := quadraticFirstMarginal
    first := bellLikeAmplitude
    second := crossBellLikeAmplitude
    hiddenRewrite := swapHiddenBoundary
    firstPurifies := bell_like_amplitude_purifies_uniform_bit
    secondPurifies := cross_bell_like_amplitude_purifies_uniform_bit
    hiddenRewriteRelates := hidden_boundary_swap_relates_sample_purifications
    hiddenRewriteReversible := hidden_boundary_swap_is_involutive
  }

def classicalObservableDim (levels : Nat) : Nat :=
  levels

def realObservableDim (levels : Nat) : Nat :=
  levels * (levels + 1) / 2

def complexObservableDim (levels : Nat) : Nat :=
  levels ^ 2

def quaternionicObservableDim (levels : Nat) : Nat :=
  levels * (2 * levels - 1)

def LocallyTomographicDimensionAt
    (dimension : Nat → Nat)
    (leftLevels rightLevels : Nat) : Prop :=
  dimension (leftLevels * rightLevels) =
    dimension leftLevels * dimension rightLevels

theorem classical_bit_passes_local_tomography_dimension :
    LocallyTomographicDimensionAt classicalObservableDim 2 2 := by
  rfl

theorem complex_qubit_passes_local_tomography_dimension :
    LocallyTomographicDimensionAt complexObservableDim 2 2 := by
  rfl

theorem real_qubit_fails_local_tomography_dimension :
    ¬ LocallyTomographicDimensionAt realObservableDim 2 2 := by
  change ¬ (10 = 9)
  decide

theorem quaternionic_qubit_fails_local_tomography_dimension :
    ¬ LocallyTomographicDimensionAt quaternionicObservableDim 2 2 := by
  change ¬ (28 = 36)
  decide

structure BoundaryCompletionFiniteSeparator where
  classicalLocalDimension :
    LocallyTomographicDimensionAt classicalObservableDim 2 2
  classicalPurificationFailure :
    ∀ joint : ClassicalPureJoint,
      classicalFirstMarginal joint ≠ uniformBitWeights
  sampleAmplitudePurification :
    SampleEquivalentSystemPurification BitWeights NatAmplitude2x2
  realLocalDimensionFailure :
    ¬ LocallyTomographicDimensionAt realObservableDim 2 2
  quaternionicLocalDimensionFailure :
    ¬ LocallyTomographicDimensionAt quaternionicObservableDim 2 2
  complexLocalDimension :
    LocallyTomographicDimensionAt complexObservableDim 2 2

def boundaryCompletionFiniteSeparator : BoundaryCompletionFiniteSeparator :=
  {
    classicalLocalDimension :=
      classical_bit_passes_local_tomography_dimension
    classicalPurificationFailure :=
      classical_uniform_bit_has_no_pure_joint_marginal
    sampleAmplitudePurification := uniformBitAmplitudePurification
    realLocalDimensionFailure :=
      real_qubit_fails_local_tomography_dimension
    quaternionicLocalDimensionFailure :=
      quaternionic_qubit_fails_local_tomography_dimension
    complexLocalDimension :=
      complex_qubit_passes_local_tomography_dimension
  }

/--
Raw boundary completion, before probability or convexity is available. The
structure requires concrete completion and reversible hidden-boundary
transport for every state; it does not merely store abstract proposition flags.
-/
structure UniversalEquivalentSystemCompletion (State Pure : Type) where
  marginal : Pure → State
  canonicalCompletion : State → Pure
  canonicalCompletes : ∀ state,
    marginal (canonicalCompletion state) = state
  hiddenRewrite : Pure → Pure → Pure → Pure
  hiddenRewriteRelates : ∀ first second,
    marginal first = marginal second →
      hiddenRewrite first second first = second
  hiddenRewriteReversible : ∀ first second,
    Function.Involutive (hiddenRewrite first second)

def boolBoundaryMarginal (value : Bool × Bool) : Bool :=
  value.1

def boolBoundaryCompletion (state : Bool) : Bool × Bool :=
  (state, false)

def boolHiddenBoundaryRewrite
    (first second value : Bool × Bool) : Bool × Bool :=
  if first.2 = second.2 then value else (value.1, !value.2)

theorem bool_hidden_boundary_rewrite_relates_equal_marginals
    (first second : Bool × Bool)
    (sameMarginal : boolBoundaryMarginal first = boolBoundaryMarginal second) :
    boolHiddenBoundaryRewrite first second first = second := by
  rcases first with ⟨firstState, firstHidden⟩
  rcases second with ⟨secondState, secondHidden⟩
  simp only [boolBoundaryMarginal] at sameMarginal
  subst secondState
  cases firstHidden <;> cases secondHidden <;>
    simp [boolHiddenBoundaryRewrite]

theorem bool_hidden_boundary_rewrite_is_involutive
    (first second : Bool × Bool) :
    Function.Involutive (boolHiddenBoundaryRewrite first second) := by
  intro value
  by_cases sameHidden : first.2 = second.2
  · simp [boolHiddenBoundaryRewrite, sameHidden]
  · simp [boolHiddenBoundaryRewrite, sameHidden]

def boolUniversalBoundaryCompletion :
    UniversalEquivalentSystemCompletion Bool (Bool × Bool) :=
  {
    marginal := boolBoundaryMarginal
    canonicalCompletion := boolBoundaryCompletion
    canonicalCompletes := by
      intro state
      rfl
    hiddenRewrite := boolHiddenBoundaryRewrite
    hiddenRewriteRelates :=
      bool_hidden_boundary_rewrite_relates_equal_marginals
    hiddenRewriteReversible :=
      bool_hidden_boundary_rewrite_is_involutive
  }

structure RawBoundaryCompletionCandidate where
  State : Type
  Pure : Type
  completion : UniversalEquivalentSystemCompletion State Pure
  observableDimension : Nat → Nat

def boolRealProfileBoundaryCandidate : RawBoundaryCompletionCandidate :=
  {
    State := Bool
    Pure := Bool × Bool
    completion := boolUniversalBoundaryCompletion
    observableDimension := realObservableDim
  }

def RawBoundaryCompletionCandidate.PassesLocalTomographyDimension
    (candidate : RawBoundaryCompletionCandidate) : Prop :=
  LocallyTomographicDimensionAt candidate.observableDimension 2 2

theorem raw_boundary_completion_does_not_force_local_tomography :
    ¬ ∀ candidate : RawBoundaryCompletionCandidate,
      candidate.PassesLocalTomographyDimension := by
  intro forced
  exact real_qubit_fails_local_tomography_dimension
    (forced boolRealProfileBoundaryCandidate)

inductive BoundaryCompletionProbeFinding where
  | classicalPassesLocalDimensionButFailsPurification
  | sampleAmplitudePurificationExistsAndIsReversiblyRelated
  | realAndQuaternionicProfilesFailLocalDimension
  | complexProfilePassesBothFiniteScreens
  | ambientProbabilityAndCompositionRemainImported
  | rawBoundaryCompletionDoesNotForceLocalTomography
  | twoPostulateCausalOperationalTargetRemainsConditional
deriving DecidableEq, Repr

def boundaryCompletionProbeFindings : List BoundaryCompletionProbeFinding :=
  [ .classicalPassesLocalDimensionButFailsPurification,
    .sampleAmplitudePurificationExistsAndIsReversiblyRelated,
    .realAndQuaternionicProfilesFailLocalDimension,
    .complexProfilePassesBothFiniteScreens,
    .ambientProbabilityAndCompositionRemainImported,
    .rawBoundaryCompletionDoesNotForceLocalTomography,
    .twoPostulateCausalOperationalTargetRemainsConditional ]

theorem boundary_completion_probe_records_seven_findings :
    boundaryCompletionProbeFindings.length = 7 := by
  rfl

inductive BoundaryCompletionOpenObligation where
  | derivePurityAndConvexityFromRewriteSubstrate
  | deriveOperationalProbabilitiesFromRewriteSubstrate
  | deriveLocalEquivalenceFromBoundaryExtensionality
  | proveUniversalEquivalentSystemPurificationInsideCausalTheory
  | liftFiniteDimensionScreenToUniversalCarrierSelection
  | deriveFieldLocalityAndStandardModelSector
  | deriveDynamicalSpacetimeGeometry
deriving DecidableEq, Repr

def boundaryCompletionOpenObligations :
    List BoundaryCompletionOpenObligation :=
  [ .derivePurityAndConvexityFromRewriteSubstrate,
    .deriveOperationalProbabilitiesFromRewriteSubstrate,
    .deriveLocalEquivalenceFromBoundaryExtensionality,
    .proveUniversalEquivalentSystemPurificationInsideCausalTheory,
    .liftFiniteDimensionScreenToUniversalCarrierSelection,
    .deriveFieldLocalityAndStandardModelSector,
    .deriveDynamicalSpacetimeGeometry ]

theorem boundary_completion_probe_keeps_seven_open_obligations :
    boundaryCompletionOpenObligations.length = 7 := by
  rfl

def boundaryCompletionProbeStatus : String :=
  "raw_boundary_completion_rejected_two_postulate_operational_target_retained"

def boundaryCompletionProbeClaimBoundary : String :=
  "Raw reversible boundary completion is insufficient: a concrete universal completion model fails local tomography. Local equivalence plus equivalent-system purification remains a conditional finite-dimensional causal-OPT reconstruction target, not a substrate derivation or a proof of the Standard Model or gravity."

end IDT.QMClosure
