import Mathlib
import Proofs.MetaLang.V8ContextFirstPrimitiveBase

namespace IDT.QMClosure

open IDT.MetaLang.V8

/-!
# Context-first readout underdetermination probe

The current context-first base is explicitly a Lean migration vocabulary: its
five entries are names, not semantic structures with laws. This file tests
whether that vocabulary, even after adding the weakest normalized binary
readout and independent product composition, selects numerical probabilities.

It does not. Two distinct readout laws extend exactly the same canonical base.
They should be read as rival interpretations of the same fixed but otherwise
unspecified preparation. This is not the ordinary fact that quantum theory has
both fair and biased states; the point is that the current primitive base has no
preparation/effect semantics capable of making that distinction.
-/

structure NormalizedBinaryReadout where
  weight : Bool → ℚ
  weightNonnegative : ∀ outcome, 0 ≤ weight outcome
  normalized : weight false + weight true = 1

def fairBinaryReadout : NormalizedBinaryReadout where
  weight := fun _ => 1 / 2
  weightNonnegative := by
    intro outcome
    cases outcome <;> norm_num
  normalized := by
    norm_num

def biasedBinaryReadout : NormalizedBinaryReadout where
  weight := fun outcome => if outcome then 2 / 3 else 1 / 3
  weightNonnegative := by
    intro outcome
    cases outcome <;> norm_num
  normalized := by
    norm_num

def independentPairWeight
    (readout : NormalizedBinaryReadout)
    (outcomes : Bool × Bool) : ℚ :=
  readout.weight outcomes.1 * readout.weight outcomes.2

theorem independent_pair_weight_factorizes
    (readout : NormalizedBinaryReadout)
    (left right : Bool) :
    independentPairWeight readout (left, right) =
      readout.weight left * readout.weight right := by
  rfl

theorem independent_pair_readout_is_normalized
    (readout : NormalizedBinaryReadout) :
    independentPairWeight readout (false, false) +
        independentPairWeight readout (false, true) +
        independentPairWeight readout (true, false) +
        independentPairWeight readout (true, true) = 1 := by
  simp only [independentPairWeight]
  calc
    readout.weight false * readout.weight false +
          readout.weight false * readout.weight true +
          readout.weight true * readout.weight false +
          readout.weight true * readout.weight true =
        (readout.weight false + readout.weight true) *
          (readout.weight false + readout.weight true) := by
            ring
    _ = 1 := by rw [readout.normalized]; norm_num

structure ContextFirstReadoutInterpretation where
  base : ContextFirstPrimitiveBaseCandidate
  baseIsMigrationBoundary : base.isLeanMigrationBoundary
  readout : NormalizedBinaryReadout

def fairContextFirstInterpretation : ContextFirstReadoutInterpretation where
  base := canonicalContextFirstBaseCandidate
  baseIsMigrationBoundary := canonical_context_first_base_is_migration_boundary
  readout := fairBinaryReadout

def biasedContextFirstInterpretation : ContextFirstReadoutInterpretation where
  base := canonicalContextFirstBaseCandidate
  baseIsMigrationBoundary := canonical_context_first_base_is_migration_boundary
  readout := biasedBinaryReadout

def ContextFirstBaseSelectsUniqueBinaryReadout
    (base : ContextFirstPrimitiveBaseCandidate) : Prop :=
  ∀ first second : ContextFirstReadoutInterpretation,
    first.base = base →
      second.base = base →
        first.readout.weight = second.readout.weight

theorem fair_and_biased_interpretations_share_the_canonical_base :
    fairContextFirstInterpretation.base =
        biasedContextFirstInterpretation.base := by
  rfl

theorem fair_and_biased_readouts_are_distinct :
    fairContextFirstInterpretation.readout.weight ≠
      biasedContextFirstInterpretation.readout.weight := by
  intro sameWeight
  have atFalse := congrFun sameWeight false
  norm_num [fairContextFirstInterpretation, biasedContextFirstInterpretation,
    fairBinaryReadout, biasedBinaryReadout] at atFalse

theorem current_context_first_base_does_not_select_unique_binary_readout :
    ¬ ContextFirstBaseSelectsUniqueBinaryReadout
      canonicalContextFirstBaseCandidate := by
  intro selects
  exact fair_and_biased_readouts_are_distinct
    (selects fairContextFirstInterpretation biasedContextFirstInterpretation
      rfl rfl)

inductive ContextFirstReadoutProbeFinding where
  | canonicalBaseIsVocabularyMigrationBoundary
  | sameBaseAdmitsDistinctNormalizedReadouts
  | bothReadoutsAdmitNormalizedIndependentProducts
  | structuralNamesDoNotSelectProbabilityWeights
  | contextAndDistinguishabilityRemainCandidateIngredients
  | completePhysicalPrimitiveBaseIsRejected
  deriving DecidableEq, Repr

def contextFirstReadoutProbeFindings :
    List ContextFirstReadoutProbeFinding :=
  [ .canonicalBaseIsVocabularyMigrationBoundary,
    .sameBaseAdmitsDistinctNormalizedReadouts,
    .bothReadoutsAdmitNormalizedIndependentProducts,
    .structuralNamesDoNotSelectProbabilityWeights,
    .contextAndDistinguishabilityRemainCandidateIngredients,
    .completePhysicalPrimitiveBaseIsRejected ]

theorem context_first_readout_probe_records_six_findings :
    contextFirstReadoutProbeFindings.length = 6 := by
  rfl

inductive ContextFirstSemanticOpenObligation where
  | assignSemanticTypesAndLawsToFiveVocabularyItems
  | deriveTypedSequentialComposition
  | deriveTypedParallelComposition
  | deriveAlternativeCoarseGraining
  | deriveOrderedNormalizedScalars
  | connectPreparationsAndEffectsToReadout
  | deriveLocalEquivalenceAndPurificationWithoutQuantumImports
  deriving DecidableEq, Repr

def contextFirstSemanticOpenObligations :
    List ContextFirstSemanticOpenObligation :=
  [ .assignSemanticTypesAndLawsToFiveVocabularyItems,
    .deriveTypedSequentialComposition,
    .deriveTypedParallelComposition,
    .deriveAlternativeCoarseGraining,
    .deriveOrderedNormalizedScalars,
    .connectPreparationsAndEffectsToReadout,
    .deriveLocalEquivalenceAndPurificationWithoutQuantumImports ]

theorem context_first_readout_probe_keeps_seven_open_obligations :
    contextFirstSemanticOpenObligations.length = 7 := by
  rfl

def contextFirstReadoutProbeStatus : String :=
  "context_first_vocabulary_rejected_as_complete_physical_primitive_base"

def contextFirstReadoutProbeClaimBoundary : String :=
  "The five context-first names remain possible ingredients, but the current migration vocabulary does not determine even a binary readout law. This rejects it as a complete physical primitive base; it does not derive the Born rule, quantum mechanics, the Standard Model, or gravity."

end IDT.QMClosure
