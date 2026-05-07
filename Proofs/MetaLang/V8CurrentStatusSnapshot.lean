import Proofs.MetaLang.V8TheoremCardLedger

namespace IDT
namespace MetaLang
namespace V8

/-!
Current v8 status snapshot.

This file intentionally contains no physics upgrade. It transfers the current
public proof-status boundary into Lean so that later migration work can compare
against a machine-checked baseline.
-/

structure TheoremCardStatusCounts where
  blocked : Nat
  conditionalProof : Nat
  finiteVerifierPass : Nat
  openCount : Nat
  formalProofCount : Nat
deriving Repr

def currentTheoremCardStatusCounts : TheoremCardStatusCounts :=
  {
    blocked := 2,
    conditionalProof := 14,
    finiteVerifierPass := 1,
    openCount := 6,
    formalProofCount := 0
  }

def TheoremCardStatusCounts.total (counts : TheoremCardStatusCounts) : Nat :=
  counts.blocked
    + counts.conditionalProof
    + counts.finiteVerifierPass
    + counts.openCount
    + counts.formalProofCount

theorem current_theorem_card_count_is_23 :
    currentTheoremCardStatusCounts.total = 23 := by
  rfl

theorem current_theorem_cards_have_no_formal_proof_status :
    currentTheoremCardStatusCounts.formalProofCount = 0 := by
  rfl

theorem current_theorem_cards_are_not_all_proved :
    currentTheoremCardStatusCounts.openCount
      + currentTheoremCardStatusCounts.blocked > 0 := by
  decide

structure ProofObligationStatusCounts where
  blocked : Nat
  derivedConditional : Nat
  regressionSupported : Nat
  target : Nat
  formalProof : Nat
deriving Repr

def currentProofObligationStatusCounts : ProofObligationStatusCounts :=
  {
    blocked := 3,
    derivedConditional := 1,
    regressionSupported := 4,
    target := 3,
    formalProof := 0
  }

def ProofObligationStatusCounts.total
    (counts : ProofObligationStatusCounts) : Nat :=
  counts.blocked
    + counts.derivedConditional
    + counts.regressionSupported
    + counts.target
    + counts.formalProof

theorem current_proof_obligation_count_is_11 :
    currentProofObligationStatusCounts.total = 11 := by
  rfl

theorem current_proof_obligations_have_no_formal_proof_status :
    currentProofObligationStatusCounts.formalProof = 0 := by
  rfl

theorem current_proof_obligations_are_not_all_closed :
    currentProofObligationStatusCounts.target
      + currentProofObligationStatusCounts.blocked > 0 := by
  decide

structure CurrentV8ProofBoundary where
  theoremCards : TheoremCardStatusCounts
  proofObligations : ProofObligationStatusCounts
deriving Repr

def currentV8ProofBoundary : CurrentV8ProofBoundary :=
  {
    theoremCards := currentTheoremCardStatusCounts,
    proofObligations := currentProofObligationStatusCounts
  }

def CurrentV8ProofBoundary.hasNoFalseFormalClosure
    (boundary : CurrentV8ProofBoundary) : Prop :=
  boundary.theoremCards.formalProofCount = 0
    ∧ boundary.proofObligations.formalProof = 0
    ∧ boundary.theoremCards.openCount + boundary.theoremCards.blocked > 0
    ∧ boundary.proofObligations.target + boundary.proofObligations.blocked > 0

theorem current_v8_boundary_has_no_false_formal_closure :
    currentV8ProofBoundary.hasNoFalseFormalClosure := by
  exact And.intro rfl (And.intro rfl (And.intro (by decide) (by decide)))

end V8
end MetaLang
end IDT
