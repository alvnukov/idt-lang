import Mathlib
import Proofs.MetaLang.V8ContextFirstPrimitiveBase

namespace IDT.QMClosure

open IDT.MetaLang.V8

/-!
# Context-first Bell countermodel

The current context-first primitive vocabulary names local outcome events and
stable distinguishability, but imposes no obstruction to one global assignment
of outcomes for every measurement setting. This file exhibits that missing
constraint without assuming Hilbert space, amplitudes, or the Born rule.

Every deterministic local assignment has CHSH magnitude exactly two. The
canonical context-first migration base admits such an interpretation, so the
base alone cannot force the Bell-nonclassical correlations required by
experiment. This is a logical insufficiency result, not a derivation of an
experimental statistic.
-/

def boolOutcomeSign (outcome : Bool) : ℤ :=
  if outcome then 1 else -1

def deterministicCHSH
    (aliceZero aliceOne bobZero bobOne : Bool) : ℤ :=
  boolOutcomeSign aliceZero * boolOutcomeSign bobZero +
    boolOutcomeSign aliceZero * boolOutcomeSign bobOne +
    boolOutcomeSign aliceOne * boolOutcomeSign bobZero -
    boolOutcomeSign aliceOne * boolOutcomeSign bobOne

theorem deterministic_local_chsh_magnitude_is_two
    (aliceZero aliceOne bobZero bobOne : Bool) :
    Int.natAbs
      (deterministicCHSH aliceZero aliceOne bobZero bobOne) = 2 := by
  cases aliceZero <;>
    cases aliceOne <;>
      cases bobZero <;>
        cases bobOne <;>
          norm_num [deterministicCHSH, boolOutcomeSign]

structure ContextFirstDeterministicBellInterpretation where
  base : ContextFirstPrimitiveBaseCandidate
  baseIsMigrationBoundary : base.isLeanMigrationBoundary
  aliceOutcome : Bool → Bool
  bobOutcome : Bool → Bool

def ContextFirstDeterministicBellInterpretation.chsh
    (interpretation : ContextFirstDeterministicBellInterpretation) : ℤ :=
  deterministicCHSH
    (interpretation.aliceOutcome false)
    (interpretation.aliceOutcome true)
    (interpretation.bobOutcome false)
    (interpretation.bobOutcome true)

theorem every_context_first_deterministic_interpretation_has_chsh_two
    (interpretation : ContextFirstDeterministicBellInterpretation) :
    Int.natAbs interpretation.chsh = 2 := by
  exact deterministic_local_chsh_magnitude_is_two
    (interpretation.aliceOutcome false)
    (interpretation.aliceOutcome true)
    (interpretation.bobOutcome false)
    (interpretation.bobOutcome true)

def canonicalGlobalAssignmentInterpretation :
    ContextFirstDeterministicBellInterpretation where
  base := canonicalContextFirstBaseCandidate
  baseIsMigrationBoundary := canonical_context_first_base_is_migration_boundary
  aliceOutcome := fun _ => false
  bobOutcome := fun _ => false

def ContextFirstBaseForcesBellViolation
    (base : ContextFirstPrimitiveBaseCandidate) : Prop :=
  ∀ interpretation : ContextFirstDeterministicBellInterpretation,
    interpretation.base = base →
      2 < Int.natAbs interpretation.chsh

theorem current_context_first_base_does_not_force_bell_violation :
    ¬ ContextFirstBaseForcesBellViolation
      canonicalContextFirstBaseCandidate := by
  intro forcesViolation
  have forced := forcesViolation canonicalGlobalAssignmentInterpretation rfl
  have classicalBound :=
    every_context_first_deterministic_interpretation_has_chsh_two
      canonicalGlobalAssignmentInterpretation
  omega

inductive ContextFirstBellFinding where
  | canonicalBaseAdmitsGlobalOutcomeAssignment
  | deterministicLocalAssignmentsHaveChshTwo
  | vocabularyDoesNotEncodeGlobalSectionObstruction
  | loopholeFreeBellDataRequireAstrongerDerivedConstraint
  | contextualGluingObstructionRemainsCandidateIngredient
  deriving DecidableEq, Repr

def contextFirstBellFindings : List ContextFirstBellFinding :=
  [ .canonicalBaseAdmitsGlobalOutcomeAssignment,
    .deterministicLocalAssignmentsHaveChshTwo,
    .vocabularyDoesNotEncodeGlobalSectionObstruction,
    .loopholeFreeBellDataRequireAstrongerDerivedConstraint,
    .contextualGluingObstructionRemainsCandidateIngredient ]

theorem context_first_bell_probe_records_five_findings :
    contextFirstBellFindings.length = 5 := by
  rfl

inductive ContextFirstBellOpenObligation where
  | deriveNoGlobalSectionForEmpiricalContextCovers
  | preserveNoSignallingWithoutLocalHiddenVariables
  | deriveQuantumRatherThanSuperquantumCorrelationBoundary
  | connectContextualObstructionToProbabilityReadout
  | deriveComplexCarrierAndContinuousReversibleDynamics
  deriving DecidableEq, Repr

def contextFirstBellOpenObligations :
    List ContextFirstBellOpenObligation :=
  [ .deriveNoGlobalSectionForEmpiricalContextCovers,
    .preserveNoSignallingWithoutLocalHiddenVariables,
    .deriveQuantumRatherThanSuperquantumCorrelationBoundary,
    .connectContextualObstructionToProbabilityReadout,
    .deriveComplexCarrierAndContinuousReversibleDynamics ]

theorem context_first_bell_probe_keeps_five_open_obligations :
    contextFirstBellOpenObligations.length = 5 := by
  rfl

def contextFirstBellProbeStatus : String :=
  "context_first_vocabulary_fails_bell_exclusion_gate"

def contextFirstBellProbeClaimBoundary : String :=
  "The canonical vocabulary admits a deterministic local global-assignment interpretation with CHSH magnitude two. Therefore it does not yet exclude the local-realistic sector rejected by Bell experiments; this does not derive quantum correlations, the Tsirelson bound, the Standard Model, or gravity."

end IDT.QMClosure
