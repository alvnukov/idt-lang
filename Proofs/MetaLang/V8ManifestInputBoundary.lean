import Proofs.MetaLang.V8MigrationRoadmap

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 manifest input boundary.

This module records the active manifest as an IDT v8 input boundary. The
manifest is not proof truth; it is the structured residual input that must be
either migrated into Lean or encoded in IDT v8 before the legacy verifier can
be archived.
-/

structure ManifestVersion where
  major : Nat
  minor : Nat
  patch : Nat
deriving Repr

def ManifestVersion.isV8 (version : ManifestVersion) : Prop :=
  version.major = 8

structure ManifestCollectionCounts where
  symbols : Nat
  equations : Nat
  derivations : Nat
  finiteGates : Nat
  qmExperiments : Nat
  qmUniversalPatterns : Nat
  qmCoreProofObligations : Nat
  theoremCards : Nat
deriving Repr

def ManifestCollectionCounts.total
    (counts : ManifestCollectionCounts) : Nat :=
  counts.symbols
    + counts.equations
    + counts.derivations
    + counts.finiteGates
    + counts.qmExperiments
    + counts.qmUniversalPatterns
    + counts.qmCoreProofObligations
    + counts.theoremCards

def currentV8ManifestCollectionCounts : ManifestCollectionCounts :=
  {
    symbols := 178,
    equations := 15,
    derivations := 81,
    finiteGates := 247,
    qmExperiments := 35,
    qmUniversalPatterns := 6,
    qmCoreProofObligations := 11,
    theoremCards := 23
  }

structure ManifestInputBoundary where
  version : ManifestVersion
  counts : ManifestCollectionCounts
  proofAuthority : VerificationAuthority
deriving Repr

def currentManifestInputBoundary : ManifestInputBoundary :=
  {
    version := { major := 8, minor := 0, patch := 0 },
    counts := currentV8ManifestCollectionCounts,
    proofAuthority := VerificationAuthority.declarativeInputCheck
  }

def ManifestInputBoundary.isAcceptedForV8
    (boundary : ManifestInputBoundary) : Prop :=
  boundary.version.isV8
    ∧ boundary.proofAuthority = VerificationAuthority.declarativeInputCheck
    ∧ boundary.counts.total > 0

theorem current_manifest_boundary_is_v8 :
    currentManifestInputBoundary.version.isV8 := by
  rfl

theorem current_manifest_boundary_is_not_proof_truth :
    currentManifestInputBoundary.proofAuthority ≠
      VerificationAuthority.proofTruth := by
  decide

theorem current_manifest_collection_total_is_596 :
    currentV8ManifestCollectionCounts.total = 596 := by
  rfl

theorem current_manifest_input_boundary_is_accepted_for_v8 :
    currentManifestInputBoundary.isAcceptedForV8 := by
  exact And.intro rfl (And.intro rfl (by decide))

def ManifestInputBoundary.hasResidualMaterial
    (boundary : ManifestInputBoundary) : Prop :=
  boundary.counts.finiteGates > 0
    ∨ boundary.counts.qmExperiments > 0
    ∨ boundary.counts.theoremCards > 0

theorem current_manifest_has_residual_material :
    currentManifestInputBoundary.hasResidualMaterial := by
  left
  decide

end V8
end MetaLang
end IDT
