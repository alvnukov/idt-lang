import Proofs.MetaLang.V8CoreClaimDisciplineRules

namespace IDT
namespace MetaLang
namespace V8

/-!
V8 controlled-vocabulary inventory.

This file mirrors the already accepted v8 declarative vocabulary into Lean. It
does not introduce new terminology; it records which terms are standard and
which are project-local so claim text cannot silently blur that boundary.
-/

def claimVocabularyEntry : VocabularyEntry :=
  {
    term := "claim",
    status := VocabularyStatus.standard,
    domain := "scientific claim verification",
    definition := "A bounded scientific assertion with explicit evidence.",
    approvalRequired := false
  }

def evidenceVocabularyEntry : VocabularyEntry :=
  {
    term := "evidence",
    status := VocabularyStatus.standard,
    domain := "scientific claim verification",
    definition := "Material support linked to a claim.",
    approvalRequired := false
  }

def proofArtifactVocabularyEntry : VocabularyEntry :=
  {
    term := "proof artifact",
    status := VocabularyStatus.standard,
    domain := "formal methods",
    definition := "A machine-checkable artifact used to verify a proof claim.",
    approvalRequired := false
  }

def proofObligationVocabularyEntry : VocabularyEntry :=
  {
    term := "proof obligation",
    status := VocabularyStatus.standard,
    domain := "formal methods",
    definition := "A required proof step or unresolved verification target.",
    approvalRequired := false
  }

def dependencyVocabularyEntry : VocabularyEntry :=
  {
    term := "dependency",
    status := VocabularyStatus.standard,
    domain := "research graph",
    definition := "A referenced claim, gate, proof, or data object.",
    approvalRequired := false
  }

def provenanceVocabularyEntry : VocabularyEntry :=
  {
    term := "provenance",
    status := VocabularyStatus.standard,
    domain := "scientific data management",
    definition := "Traceable origin and processing history for evidence.",
    approvalRequired := false
  }

def counterexampleVocabularyEntry : VocabularyEntry :=
  {
    term := "counterexample",
    status := VocabularyStatus.standard,
    domain := "mathematics and scientific method",
    definition := "A case that falsifies a proposed universal claim.",
    approvalRequired := false
  }

def witnessVocabularyEntry : VocabularyEntry :=
  {
    term := "witness",
    status := VocabularyStatus.standard,
    domain := "mathematics and formal verification",
    definition := "A concrete object establishing an existential condition.",
    approvalRequired := false
  }

def finiteVerifierPassVocabularyEntry : VocabularyEntry :=
  {
    term := "finite verifier pass",
    status := VocabularyStatus.projectLocal,
    domain := "IDT verification",
    definition := "A successful finite executable check, not a formal proof.",
    approvalRequired := false
  }

def facticizationWitnessVocabularyEntry : VocabularyEntry :=
  {
    term := "facticization witness",
    status := VocabularyStatus.projectLocal,
    domain := "IDT verification",
    definition := "A project-local witness for readout/fact formation.",
    approvalRequired := false
  }

def v8ControlledVocabulary : List VocabularyEntry :=
  [
    claimVocabularyEntry,
    evidenceVocabularyEntry,
    proofArtifactVocabularyEntry,
    proofObligationVocabularyEntry,
    dependencyVocabularyEntry,
    provenanceVocabularyEntry,
    counterexampleVocabularyEntry,
    witnessVocabularyEntry,
    finiteVerifierPassVocabularyEntry,
    facticizationWitnessVocabularyEntry
  ]

def VocabularyEntry.isProjectLocal (entry : VocabularyEntry) : Prop :=
  entry.status = VocabularyStatus.projectLocal

def VocabularyEntry.isStandard (entry : VocabularyEntry) : Prop :=
  entry.status = VocabularyStatus.standard

theorem v8_controlled_vocabulary_has_ten_terms :
    v8ControlledVocabulary.length = 10 := by
  rfl

theorem finite_verifier_pass_is_project_local :
    finiteVerifierPassVocabularyEntry.isProjectLocal := by
  rfl

theorem facticization_witness_is_project_local :
    facticizationWitnessVocabularyEntry.isProjectLocal := by
  rfl

theorem project_local_terms_are_not_standard
    (entry : VocabularyEntry)
    (projectLocal : entry.isProjectLocal) :
    ¬ entry.isStandard := by
  intro standard
  unfold VocabularyEntry.isProjectLocal at projectLocal
  unfold VocabularyEntry.isStandard at standard
  rw [projectLocal] at standard
  contradiction

theorem finite_verifier_pass_is_not_standard :
    ¬ finiteVerifierPassVocabularyEntry.isStandard :=
  project_local_terms_are_not_standard
    finiteVerifierPassVocabularyEntry
    finite_verifier_pass_is_project_local

theorem facticization_witness_is_not_standard :
    ¬ facticizationWitnessVocabularyEntry.isStandard :=
  project_local_terms_are_not_standard
    facticizationWitnessVocabularyEntry
    facticization_witness_is_project_local

theorem proposed_terms_in_v8_vocabulary_require_approval
    (entry : VocabularyEntry)
    (entryPresent : entry ∈ v8ControlledVocabulary)
    (proposed : entry.status = VocabularyStatus.proposedTerm) :
    entry.approvalRequired = true := by
  simp [
    v8ControlledVocabulary,
    claimVocabularyEntry,
    evidenceVocabularyEntry,
    proofArtifactVocabularyEntry,
    proofObligationVocabularyEntry,
    dependencyVocabularyEntry,
    provenanceVocabularyEntry,
    counterexampleVocabularyEntry,
    witnessVocabularyEntry,
    finiteVerifierPassVocabularyEntry,
    facticizationWitnessVocabularyEntry,
  ] at entryPresent
  rcases entryPresent with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals contradiction

end V8
end MetaLang
end IDT
