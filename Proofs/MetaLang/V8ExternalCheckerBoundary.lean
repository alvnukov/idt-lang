import Proofs.MetaLang.V8VerificationLanguage

namespace IDT
namespace MetaLang
namespace V8

inductive ExternalCheckerKind where
  | numericGate
  | dataProvenanceGate
  | legacyManifestGate
  | idtV8DeclarativeGate
  | leanProofKernel
  | ciPipeline
deriving DecidableEq, Repr

structure ExternalChecker where
  identifier : String
  kind : ExternalCheckerKind
  command : String
  trustedScope : String
deriving Repr

structure ExternalVerificationResult where
  checker : ExternalChecker
  claim : Claim
  resultStatus : ClaimStatus
deriving Repr

def ExternalVerificationResult.isFiniteVerifierPass
    (result : ExternalVerificationResult) : Prop :=
  result.resultStatus = ClaimStatus.finiteVerifierPass

def ExternalVerificationResult.isFormalProof
    (result : ExternalVerificationResult) : Prop :=
  result.resultStatus = ClaimStatus.formalProof

def ExternalVerificationResult.respectsProofBoundary
    (result : ExternalVerificationResult) : Prop :=
  result.isFiniteVerifierPass → ¬ result.isFormalProof

theorem finite_verifier_pass_is_not_formal_proof
    (result : ExternalVerificationResult)
    (finitePass : result.isFiniteVerifierPass) :
    ¬ result.isFormalProof := by
  intro formal
  unfold ExternalVerificationResult.isFiniteVerifierPass at finitePass
  unfold ExternalVerificationResult.isFormalProof at formal
  rw [finitePass] at formal
  contradiction

structure DeprecatedPythonVerifierBoundary where
  checker : ExternalChecker
  allowedStatus : ClaimStatus
  forbiddenStatus : ClaimStatus
  decommissionTarget : ExternalCheckerKind

def DeprecatedPythonVerifierBoundary.valid
    (boundary : DeprecatedPythonVerifierBoundary) : Prop :=
  boundary.checker.kind = ExternalCheckerKind.legacyManifestGate
    ∧ boundary.allowedStatus = ClaimStatus.finiteVerifierPass
    ∧ boundary.forbiddenStatus = ClaimStatus.formalProof
    ∧ boundary.decommissionTarget = ExternalCheckerKind.leanProofKernel

def deprecatedPythonVerifierBoundary : DeprecatedPythonVerifierBoundary :=
  {
    checker := {
      identifier := "legacy_python_manifest_verifier",
      kind := ExternalCheckerKind.legacyManifestGate,
      command := "python3 -m theory_verifier --json theory_verifier_manifest.json",
      trustedScope := "deprecated_compatibility_only_not_proof_truth"
    },
    allowedStatus := ClaimStatus.finiteVerifierPass,
    forbiddenStatus := ClaimStatus.formalProof,
    decommissionTarget := ExternalCheckerKind.leanProofKernel
  }

theorem deprecated_python_verifier_boundary_is_valid :
    deprecatedPythonVerifierBoundary.valid := by
  exact And.intro rfl (And.intro rfl (And.intro rfl rfl))

theorem deprecated_python_verifier_cannot_assign_formal_proof :
    deprecatedPythonVerifierBoundary.forbiddenStatus = ClaimStatus.formalProof := by
  rfl

theorem deprecated_python_verifier_targets_lean_decommission :
    deprecatedPythonVerifierBoundary.decommissionTarget =
      ExternalCheckerKind.leanProofKernel := by
  rfl

abbrev LegacyPythonVerifierBoundary := DeprecatedPythonVerifierBoundary
abbrev legacyPythonVerifierBoundary := deprecatedPythonVerifierBoundary

theorem legacy_python_verifier_boundary_is_valid :
    legacyPythonVerifierBoundary.valid :=
  deprecated_python_verifier_boundary_is_valid

theorem legacy_python_verifier_cannot_assign_formal_proof :
    legacyPythonVerifierBoundary.forbiddenStatus = ClaimStatus.formalProof :=
  deprecated_python_verifier_cannot_assign_formal_proof

end V8
end MetaLang
end IDT
