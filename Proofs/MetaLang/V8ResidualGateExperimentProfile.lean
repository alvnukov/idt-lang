import Proofs.MetaLang.V8CurrentFrontierBlockers

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 residual gate and experiment profile.

This module migrates the broad finite-gate and QM-experiment residual profile
into Lean. It intentionally keeps the long finite-gate type tail summarized:
the goal is to preserve migration boundaries without creating noisy, fragile
micro-ledgers.
-/

structure ResidualFiniteGateProfile where
  totalGates : Nat
  distinctTypes : Nat
  singletonTypes : Nat
  repeatedTypes : Nat
  repeatedTypeItems : Nat
deriving Repr

def currentResidualFiniteGateProfile : ResidualFiniteGateProfile :=
  {
    totalGates := 247,
    distinctTypes := 237,
    singletonTypes := 234,
    repeatedTypes := 3,
    repeatedTypeItems := 13
  }

def ResidualFiniteGateProfile.isConsistent
    (profile : ResidualFiniteGateProfile) : Prop :=
  profile.singletonTypes + profile.repeatedTypes = profile.distinctTypes
    ∧ profile.repeatedTypeItems ≤ profile.totalGates
    ∧ profile.distinctTypes ≤ profile.totalGates

theorem current_residual_finite_gate_profile_is_consistent :
    currentResidualFiniteGateProfile.isConsistent := by
  exact And.intro rfl (And.intro (by decide) (by decide))

theorem current_residual_finite_gate_total_is_247 :
    currentResidualFiniteGateProfile.totalGates = 247 := by
  rfl

theorem current_residual_finite_gate_types_are_long_tail :
    currentResidualFiniteGateProfile.singletonTypes >
      currentResidualFiniteGateProfile.repeatedTypes := by
  decide

inductive ResidualExperimentClassification where
  | unclassified
  | idtV8Classified
deriving DecidableEq, Repr

structure ResidualQmExperimentProfile where
  totalExperiments : Nat
  unclassifiedExperiments : Nat
  classification : ResidualExperimentClassification
deriving Repr

def currentResidualQmExperimentProfile : ResidualQmExperimentProfile :=
  {
    totalExperiments := 35,
    unclassifiedExperiments := 35,
    classification := ResidualExperimentClassification.unclassified
  }

def ResidualQmExperimentProfile.needsIdtV8Classification
    (profile : ResidualQmExperimentProfile) : Prop :=
  profile.unclassifiedExperiments = profile.totalExperiments
    ∧ profile.classification = ResidualExperimentClassification.unclassified

theorem current_qm_experiments_need_idt_v8_classification :
    currentResidualQmExperimentProfile.needsIdtV8Classification := by
  exact And.intro rfl rfl

structure ResidualGateExperimentBoundary where
  gates : ResidualFiniteGateProfile
  experiments : ResidualQmExperimentProfile
  authority : VerificationAuthority
deriving Repr

def currentResidualGateExperimentBoundary : ResidualGateExperimentBoundary :=
  {
    gates := currentResidualFiniteGateProfile,
    experiments := currentResidualQmExperimentProfile,
    authority := VerificationAuthority.declarativeInputCheck
  }

def ResidualGateExperimentBoundary.isAcceptedForV8
    (boundary : ResidualGateExperimentBoundary) : Prop :=
  boundary.authority = VerificationAuthority.declarativeInputCheck
    ∧ boundary.gates.isConsistent
    ∧ boundary.experiments.needsIdtV8Classification

theorem current_residual_gate_experiment_boundary_is_accepted :
    currentResidualGateExperimentBoundary.isAcceptedForV8 := by
  exact And.intro rfl
    (And.intro
      current_residual_finite_gate_profile_is_consistent
      current_qm_experiments_need_idt_v8_classification)

end V8
end MetaLang
end IDT
