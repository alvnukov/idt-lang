import Proofs.MetaLang.V8ManifestInputBoundary

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 residual migration ledger.

After Lean migration, remaining material must be encoded as IDT v8 residual
input. This ledger records the current residual surface and prevents it from
being mistaken for formal proof material.
-/

inductive ResidualMaterialKind where
  | finiteGate
  | qmExperiment
  | theoremCard
  | qmCoreProofObligation
deriving DecidableEq, Repr

structure ResidualMaterialCount where
  kind : ResidualMaterialKind
  count : Nat
deriving Repr

def currentResidualMaterialCounts : List ResidualMaterialCount :=
  [
    { kind := ResidualMaterialKind.finiteGate, count := 247 },
    { kind := ResidualMaterialKind.qmExperiment, count := 35 },
    { kind := ResidualMaterialKind.theoremCard, count := 23 },
    { kind := ResidualMaterialKind.qmCoreProofObligation, count := 11 }
  ]

def ResidualMaterialCount.hasResidual (item : ResidualMaterialCount) : Prop :=
  item.count > 0

def residualTotal (items : List ResidualMaterialCount) : Nat :=
  items.foldl (fun total item => total + item.count) 0

theorem current_residual_material_total_is_316 :
    residualTotal currentResidualMaterialCounts = 316 := by
  rfl

theorem current_residual_material_is_nonempty :
    ∃ item, item ∈ currentResidualMaterialCounts ∧ item.hasResidual := by
  exact ⟨{ kind := ResidualMaterialKind.finiteGate, count := 247 },
    by simp [currentResidualMaterialCounts],
    by
      unfold ResidualMaterialCount.hasResidual
      decide⟩

structure ResidualStatusCounts where
  blocked : Nat
  conditional : Nat
  finiteSupported : Nat
  openOrTarget : Nat
  formalProof : Nat
deriving Repr

def currentResidualTheoremCardStatusCounts : ResidualStatusCounts :=
  {
    blocked := 2,
    conditional := 14,
    finiteSupported := 1,
    openOrTarget := 6,
    formalProof := 0
  }

def currentResidualProofObligationStatusCounts : ResidualStatusCounts :=
  {
    blocked := 3,
    conditional := 1,
    finiteSupported := 4,
    openOrTarget := 3,
    formalProof := 0
  }

def ResidualStatusCounts.hasNoFormalProof
    (counts : ResidualStatusCounts) : Prop :=
  counts.formalProof = 0

def ResidualStatusCounts.hasUnclosedMaterial
    (counts : ResidualStatusCounts) : Prop :=
  counts.blocked + counts.openOrTarget > 0

theorem current_residual_theorem_cards_have_no_formal_proof :
    currentResidualTheoremCardStatusCounts.hasNoFormalProof := by
  rfl

theorem current_residual_proof_obligations_have_no_formal_proof :
    currentResidualProofObligationStatusCounts.hasNoFormalProof := by
  rfl

theorem current_residual_theorem_cards_have_unclosed_material :
    currentResidualTheoremCardStatusCounts.hasUnclosedMaterial := by
  unfold ResidualStatusCounts.hasUnclosedMaterial
  decide

theorem current_residual_proof_obligations_have_unclosed_material :
    currentResidualProofObligationStatusCounts.hasUnclosedMaterial := by
  unfold ResidualStatusCounts.hasUnclosedMaterial
  decide

structure ResidualMigrationBoundary where
  material : List ResidualMaterialCount
  theoremCardStatuses : ResidualStatusCounts
  proofObligationStatuses : ResidualStatusCounts
  authority : VerificationAuthority
deriving Repr

def currentResidualMigrationBoundary : ResidualMigrationBoundary :=
  {
    material := currentResidualMaterialCounts,
    theoremCardStatuses := currentResidualTheoremCardStatusCounts,
    proofObligationStatuses := currentResidualProofObligationStatusCounts,
    authority := VerificationAuthority.declarativeInputCheck
  }

def ResidualMigrationBoundary.isAcceptedForV8
    (boundary : ResidualMigrationBoundary) : Prop :=
  boundary.authority = VerificationAuthority.declarativeInputCheck
    ∧ boundary.theoremCardStatuses.hasNoFormalProof
    ∧ boundary.proofObligationStatuses.hasNoFormalProof
    ∧ residualTotal boundary.material > 0

theorem current_residual_migration_boundary_is_accepted :
    currentResidualMigrationBoundary.isAcceptedForV8 := by
  exact And.intro rfl (And.intro rfl (And.intro rfl (by decide)))

end V8
end MetaLang
end IDT
