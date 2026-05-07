import Proofs.MetaLang.V8CurrentStopReadiness
import Proofs.MetaLang.V8FormalProofScopeBoundary
import Proofs.MetaLang.V8AcceptedDocumentInventory
import Proofs.MetaLang.V8ExecutableBoundaryCheck

open IDT.MetaLang.V8

def residualQmExperimentCount : Nat :=
  currentExperimentProgramArchitecture.residualLedger.length

def verificationDisciplineTheoremCount : Nat :=
  currentFormalProofScopeCounts.verificationDiscipline

def physicalFormalProofCount : Nat :=
  currentFormalProofScopeCounts.physicalTheory

def qmFormalProofCount : Nat :=
  currentFormalProofScopeCounts.qmClosure

def acceptedV8Documents : Nat :=
  currentExecutableBoundarySnapshot.acceptedDocumentCount

def boundarySnapshot : ExecutableBoundarySnapshot :=
  currentExecutableBoundarySnapshot

def jsonString (value : String) : String :=
  "\"" ++ value ++ "\""

def residualExperimentIdsJson : String :=
  let ids :=
    currentExperimentProgramArchitecture.residualLedger.map
      (fun entry => jsonString entry.manifestId)
  "[" ++ String.intercalate "," ids ++ "]"

def acceptedV8DocumentIdsJson : String :=
  let ids :=
    acceptedV8DocumentIds.map
      (fun document => jsonString document.toDocumentId)
  "[" ++ String.intercalate "," ids ++ "]"

def protocolStatusText : String :=
  String.intercalate "\n" [
    "IDT v8 Lean migration and experiment protocol status",
    "protocol_logic_authority=lean_checked",
    "result_status=certified_executable_check",
    "proof_authority=declarative_input_check",
    s!"accepted_v8_documents={acceptedV8Documents}",
    s!"verification_discipline_theorems={verificationDisciplineTheoremCount}",
    s!"residual_qm_experiments={residualQmExperimentCount}",
    "residuals_need_idt_v8_classification=true",
    "can_assign_physical_formal_proof=false",
    s!"physical_formal_proofs={physicalFormalProofCount}",
    s!"qm_formal_proofs={qmFormalProofCount}",
    "lean_eligible_migration_complete=false",
    "residual_encoding_ready=false",
    "experiment_program_ready=false",
    "ready_for_research_handoff=false",
    "ready_for_migration_stop=false"
  ]

def boundaryCheckPassed : Bool :=
  boundarySnapshot.acceptedDocumentCount == 4
    && boundarySnapshot.verificationDisciplineTheorems == 255
    && boundarySnapshot.residualQmExperiments == 35
    && boundarySnapshot.theoremCardFormalProofs == 0
    && boundarySnapshot.qmObligationFormalProofs == 0
    && boundarySnapshot.qmExperimentFormalProofs == 0
    && boundarySnapshot.physicalFormalProofs == 0
    && boundarySnapshot.qmFormalProofs == 0

def main (args : List String) : IO Unit := do
  if args.contains "--check-boundary" then
    if boundaryCheckPassed then
      IO.println "boundary_check=ok"
    else
      throw <| IO.userError "boundary_check=failed"
  else if args.contains "--residuals-json" then
    IO.println residualExperimentIdsJson
  else if args.contains "--documents-json" then
    IO.println acceptedV8DocumentIdsJson
  else if args.contains "--json" then
    let residualCount :=
      toString residualQmExperimentCount
    let verificationCount :=
      toString verificationDisciplineTheoremCount
    let documentCount :=
      toString acceptedV8Documents
    IO.println (
      "{\"protocol_logic_authority\":\"lean_checked\","
      ++ "\"result_status\":\"certified_executable_check\","
      ++ "\"proof_authority\":\"declarative_input_check\","
      ++ "\"accepted_v8_documents\":" ++ documentCount ++ ","
      ++ "\"accepted_v8_document_ids\":" ++ acceptedV8DocumentIdsJson ++ ","
      ++ "\"verification_discipline_theorems\":" ++ verificationCount ++ ","
      ++ "\"residual_qm_experiments\":" ++ residualCount ++ ","
      ++ "\"residual_qm_experiment_ids\":" ++ residualExperimentIdsJson ++ ","
      ++ "\"residuals_need_idt_v8_classification\":true,"
      ++ "\"can_assign_physical_formal_proof\":false,"
      ++ "\"theorem_card_formal_proofs\":0,"
      ++ "\"qm_obligation_formal_proofs\":0,"
      ++ "\"qm_experiment_formal_proofs\":0,"
      ++ "\"physical_formal_proofs\":0,"
      ++ "\"qm_formal_proofs\":0,"
      ++ "\"lean_eligible_migration_complete\":false,"
      ++ "\"residual_encoding_ready\":false,"
      ++ "\"experiment_program_ready\":false,"
      ++ "\"ready_for_research_handoff\":false,"
      ++ "\"ready_for_migration_stop\":false}"
    )
  else
    IO.println protocolStatusText
