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

inductive BoundaryCompletionProbeFinding where
  | classicalPassesLocalDimensionButFailsPurification
  | sampleAmplitudePurificationExistsAndIsReversiblyRelated
  | realAndQuaternionicProfilesFailLocalDimension
  | complexProfilePassesBothFiniteScreens
  | ambientProbabilityAndCompositionRemainImported
deriving DecidableEq, Repr

def boundaryCompletionProbeFindings : List BoundaryCompletionProbeFinding :=
  [ .classicalPassesLocalDimensionButFailsPurification,
    .sampleAmplitudePurificationExistsAndIsReversiblyRelated,
    .realAndQuaternionicProfilesFailLocalDimension,
    .complexProfilePassesBothFiniteScreens,
    .ambientProbabilityAndCompositionRemainImported ]

theorem boundary_completion_probe_records_five_findings :
    boundaryCompletionProbeFindings.length = 5 := by
  rfl

inductive BoundaryCompletionOpenObligation where
  | deriveOperationalProbabilitiesFromRewriteSubstrate
  | deriveLocalEquivalenceFromBoundaryExtensionality
  | proveUniversalEquivalentSystemPurification
  | liftFiniteDimensionScreenToUniversalCarrierSelection
  | deriveFieldLocalityAndStandardModelSector
  | deriveDynamicalSpacetimeGeometry
deriving DecidableEq, Repr

def boundaryCompletionOpenObligations :
    List BoundaryCompletionOpenObligation :=
  [ .deriveOperationalProbabilitiesFromRewriteSubstrate,
    .deriveLocalEquivalenceFromBoundaryExtensionality,
    .proveUniversalEquivalentSystemPurification,
    .liftFiniteDimensionScreenToUniversalCarrierSelection,
    .deriveFieldLocalityAndStandardModelSector,
    .deriveDynamicalSpacetimeGeometry ]

theorem boundary_completion_probe_keeps_six_open_obligations :
    boundaryCompletionOpenObligations.length = 6 := by
  rfl

def boundaryCompletionProbeStatus : String :=
  "finite_separator_hit_universal_derivation_open"

def boundaryCompletionProbeClaimBoundary : String :=
  "The finite separator matches the expected classical/real/complex pattern, but does not derive the operational-probabilistic framework, universal complex quantum theory, the Standard Model, or gravity from local rewrites."

end IDT.QMClosure
