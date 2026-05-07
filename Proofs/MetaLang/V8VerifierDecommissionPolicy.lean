import Proofs.MetaLang.V8ClaimStrengthInvariant

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 verifier decommission policy.

The target architecture is Lean + IDT v8. The old Python verifier may remain
temporarily as a compatibility checker, but it is deprecated and cannot be a
source of proof truth.
-/

inductive VerificationAuthority where
  | proofTruth
  | declarativeInputCheck
  | deprecatedCompatibility
deriving DecidableEq, Repr

structure VerifierRole where
  checker : ExternalChecker
  authority : VerificationAuthority
deriving Repr

def VerifierRole.canAssignFormalProof (role : VerifierRole) : Prop :=
  role.authority = VerificationAuthority.proofTruth
    ∧ role.checker.kind = ExternalCheckerKind.leanProofKernel

def VerifierRole.isDeprecatedCompatibility (role : VerifierRole) : Prop :=
  role.authority = VerificationAuthority.deprecatedCompatibility

def oldPythonVerifierRole : VerifierRole :=
  {
    checker := deprecatedPythonVerifierBoundary.checker,
    authority := VerificationAuthority.deprecatedCompatibility
  }

def leanV8ProofKernelRole : VerifierRole :=
  {
    checker := {
      identifier := "lean_v8_proof_kernel",
      kind := ExternalCheckerKind.leanProofKernel,
      command := "lake build",
      trustedScope := "proof_truth_for_machine_checked_artifacts"
    },
    authority := VerificationAuthority.proofTruth
  }

def idtV8DeclarativeGateRole : VerifierRole :=
  {
    checker := {
      identifier := "idt_v8_declarative_gate",
      kind := ExternalCheckerKind.idtV8DeclarativeGate,
      command := "IDT v8 declarative rule evaluation",
      trustedScope := "research_input_validation_not_proof_truth"
    },
    authority := VerificationAuthority.declarativeInputCheck
  }

theorem old_python_verifier_is_deprecated_compatibility :
    oldPythonVerifierRole.isDeprecatedCompatibility := by
  rfl

theorem old_python_verifier_cannot_assign_formal_proof :
    ¬ oldPythonVerifierRole.canAssignFormalProof := by
  intro canAssign
  exact nomatch canAssign.left

theorem idt_v8_declarative_gate_cannot_assign_formal_proof :
    ¬ idtV8DeclarativeGateRole.canAssignFormalProof := by
  intro canAssign
  exact nomatch canAssign.left

theorem lean_v8_kernel_can_assign_formal_proof :
    leanV8ProofKernelRole.canAssignFormalProof := by
  exact And.intro rfl rfl

structure DecommissionPlan where
  deprecated : VerifierRole
  replacement : VerifierRole
  deprecatedIsCompatibilityOnly : deprecated.isDeprecatedCompatibility
  replacementCanAssignFormalProof : replacement.canAssignFormalProof

def pythonToLeanV8DecommissionPlan : DecommissionPlan :=
  {
    deprecated := oldPythonVerifierRole,
    replacement := leanV8ProofKernelRole,
    deprecatedIsCompatibilityOnly := old_python_verifier_is_deprecated_compatibility,
    replacementCanAssignFormalProof := lean_v8_kernel_can_assign_formal_proof
  }

theorem python_decommission_replacement_is_lean_proof_kernel :
    pythonToLeanV8DecommissionPlan.replacement.checker.kind =
      ExternalCheckerKind.leanProofKernel := by
  rfl

end V8
end MetaLang
end IDT
