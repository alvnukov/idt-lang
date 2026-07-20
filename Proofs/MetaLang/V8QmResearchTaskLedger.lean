import Proofs.MetaLang.V8CurrentFrontierBlockers
import Proofs.QMClosure.CGSCGroundedSemanticExtensions

namespace IDT
namespace MetaLang
namespace V8

open IDT.QMClosure

/-!
V8 QM research task ledger.

This module keeps the next research tasks in Lean, not only in Markdown.  It is
a planning and claim-discipline artifact: it does not prove QM, does not
upgrade any theorem card, and does not convert source-witness scaffolds into
target-specific physical derivations.
-/

inductive QmResearchTaskKind where
  | splitClaimSourceAliases
  | proveProductLocalTomographyTarget
  | proveProductMonoidalAssociativityTarget
  | proveProductEntanglementClosureTarget
  | proveExposedSpectralTarget
  | proveReversibleOverlapDynamicsTarget
  | deriveBornReadoutCoreFromPrimitiveBase
  | deriveCarrierFrontierExhaustion
  | recompileExperimentsFromTargetSpecificProofs
deriving DecidableEq, Repr

inductive QmResearchTaskStatus where
  | active
  | blocked
  | target
deriving DecidableEq, Repr

structure QmResearchTask where
  kind : QmResearchTaskKind
  status : QmResearchTaskStatus
  blocksExactQM : Bool
  dependsOnClaimSourceAliasingBoundary : Bool
deriving Repr

inductive QmResearchFrontKind where
  | compositeMonoidalLocalTomography
deriving DecidableEq, Repr

inductive CompositeMonoidalProbeKind where
  | deriveMonoidalFromContextProductExhaustion
  | preserveRebitHiddenJointInvariantNegativeControl
  | auditTensorImportBoundary
deriving DecidableEq, Repr

structure CompositeMonoidalProbe where
  kind : CompositeMonoidalProbeKind
  status : QmResearchTaskStatus
  blocksExactQMUpgrade : Bool
deriving Repr

structure QmResearchFront where
  kind : QmResearchFrontKind
  primaryTask : QmResearchTaskKind
  localTomographyTask : QmResearchTaskKind
  openTheoremCard : CurrentTheoremCardId
  targetObligation : CurrentQmObligationId
  negativeControl : CurrentTheoremCardId
  bornHilbertDeferred : Bool
  status : QmResearchTaskStatus
deriving Repr

def currentQmResearchTasks : List QmResearchTask :=
  [
    {
      kind := QmResearchTaskKind.splitClaimSourceAliases,
      status := QmResearchTaskStatus.active,
      blocksExactQM := true,
      dependsOnClaimSourceAliasingBoundary := true
    },
    {
      kind := QmResearchTaskKind.proveProductLocalTomographyTarget,
      status := QmResearchTaskStatus.target,
      blocksExactQM := true,
      dependsOnClaimSourceAliasingBoundary := true
    },
    {
      kind := QmResearchTaskKind.proveProductMonoidalAssociativityTarget,
      status := QmResearchTaskStatus.target,
      blocksExactQM := true,
      dependsOnClaimSourceAliasingBoundary := true
    },
    {
      kind := QmResearchTaskKind.proveProductEntanglementClosureTarget,
      status := QmResearchTaskStatus.target,
      blocksExactQM := true,
      dependsOnClaimSourceAliasingBoundary := true
    },
    {
      kind := QmResearchTaskKind.proveExposedSpectralTarget,
      status := QmResearchTaskStatus.target,
      blocksExactQM := true,
      dependsOnClaimSourceAliasingBoundary := true
    },
    {
      kind := QmResearchTaskKind.proveReversibleOverlapDynamicsTarget,
      status := QmResearchTaskStatus.target,
      blocksExactQM := true,
      dependsOnClaimSourceAliasingBoundary := true
    },
    {
      kind := QmResearchTaskKind.deriveBornReadoutCoreFromPrimitiveBase,
      status := QmResearchTaskStatus.blocked,
      blocksExactQM := true,
      dependsOnClaimSourceAliasingBoundary := false
    },
    {
      kind := QmResearchTaskKind.deriveCarrierFrontierExhaustion,
      status := QmResearchTaskStatus.blocked,
      blocksExactQM := true,
      dependsOnClaimSourceAliasingBoundary := false
    },
    {
      kind := QmResearchTaskKind.recompileExperimentsFromTargetSpecificProofs,
      status := QmResearchTaskStatus.blocked,
      blocksExactQM := true,
      dependsOnClaimSourceAliasingBoundary := true
    }
  ]

def currentCompositeMonoidalProbes : List CompositeMonoidalProbe :=
  [
    {
      kind := CompositeMonoidalProbeKind.deriveMonoidalFromContextProductExhaustion,
      status := QmResearchTaskStatus.active,
      blocksExactQMUpgrade := true
    },
    {
      kind := CompositeMonoidalProbeKind.preserveRebitHiddenJointInvariantNegativeControl,
      status := QmResearchTaskStatus.active,
      blocksExactQMUpgrade := true
    },
    {
      kind := CompositeMonoidalProbeKind.auditTensorImportBoundary,
      status := QmResearchTaskStatus.active,
      blocksExactQMUpgrade := true
    }
  ]

def currentQmResearchFront : QmResearchFront :=
  {
    kind := QmResearchFrontKind.compositeMonoidalLocalTomography,
    primaryTask := QmResearchTaskKind.proveProductMonoidalAssociativityTarget,
    localTomographyTask := QmResearchTaskKind.proveProductLocalTomographyTarget,
    openTheoremCard := CurrentTheoremCardId.monoidalTensorCompositionTheorem,
    targetObligation := CurrentQmObligationId.tensorCompositionLaw,
    negativeControl := CurrentTheoremCardId.realHilbertCompositeHiddenJointInvariant,
    bornHilbertDeferred := true,
    status := QmResearchTaskStatus.active
  }

def QmResearchTask.isOpenForResearch
    (task : QmResearchTask) : Prop :=
  task.status = QmResearchTaskStatus.active
    ∨ task.status = QmResearchTaskStatus.blocked
    ∨ task.status = QmResearchTaskStatus.target

def QmResearchTasksOpen
    (tasks : List QmResearchTask) : Prop :=
  ∀ task, task ∈ tasks → task.isOpenForResearch

theorem current_qm_research_task_count :
    currentQmResearchTasks.length = 9 := by
  rfl

theorem current_composite_monoidal_probe_count :
    currentCompositeMonoidalProbes.length = 3 := by
  rfl

theorem current_qm_research_tasks_are_open :
    QmResearchTasksOpen currentQmResearchTasks := by
  intro task present
  simp [currentQmResearchTasks] at present
  rcases present with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    unfold QmResearchTask.isOpenForResearch
    first | left; rfl | right; left; rfl | right; right; rfl

def TaskBlocksExactQM
    (kind : QmResearchTaskKind)
    (tasks : List QmResearchTask) : Prop :=
  ∃ task, task ∈ tasks
    ∧ task.kind = kind
    ∧ task.blocksExactQM = true

theorem split_claim_source_aliases_blocks_exact_qm_research :
    TaskBlocksExactQM
      QmResearchTaskKind.splitClaimSourceAliases
      currentQmResearchTasks := by
  exact ⟨{
      kind := QmResearchTaskKind.splitClaimSourceAliases,
      status := QmResearchTaskStatus.active,
      blocksExactQM := true,
      dependsOnClaimSourceAliasingBoundary := true
    },
    by simp [currentQmResearchTasks],
    And.intro rfl rfl⟩

theorem local_tomography_target_blocks_exact_qm_research :
    TaskBlocksExactQM
      QmResearchTaskKind.proveProductLocalTomographyTarget
      currentQmResearchTasks := by
  exact ⟨{
      kind := QmResearchTaskKind.proveProductLocalTomographyTarget,
      status := QmResearchTaskStatus.target,
      blocksExactQM := true,
      dependsOnClaimSourceAliasingBoundary := true
    },
    by simp [currentQmResearchTasks],
    And.intro rfl rfl⟩

theorem monoidal_target_blocks_exact_qm_research :
    TaskBlocksExactQM
      QmResearchTaskKind.proveProductMonoidalAssociativityTarget
      currentQmResearchTasks := by
  exact ⟨{
      kind := QmResearchTaskKind.proveProductMonoidalAssociativityTarget,
      status := QmResearchTaskStatus.target,
      blocksExactQM := true,
      dependsOnClaimSourceAliasingBoundary := true
    },
    by simp [currentQmResearchTasks],
    And.intro rfl rfl⟩

theorem born_readout_core_task_blocks_exact_qm_research :
    TaskBlocksExactQM
      QmResearchTaskKind.deriveBornReadoutCoreFromPrimitiveBase
      currentQmResearchTasks := by
  exact ⟨{
      kind := QmResearchTaskKind.deriveBornReadoutCoreFromPrimitiveBase,
      status := QmResearchTaskStatus.blocked,
      blocksExactQM := true,
      dependsOnClaimSourceAliasingBoundary := false
    },
    by simp [currentQmResearchTasks],
    And.intro rfl rfl⟩

def ClaimSourceAliasingBoundaryAcknowledged : Prop :=
  ∀ base : GroundedCGSCSemanticExtensionBase,
    GroundedCGSCClaimSourceAliasing base

theorem current_research_plan_acknowledges_claim_source_aliasing_boundary :
    ClaimSourceAliasingBoundaryAcknowledged :=
  grounded_cgsc_claim_source_aliasing_boundary

def ClaimSourceAliasingDependentTasksOpen : Prop :=
  ∀ task, task ∈ currentQmResearchTasks →
    task.dependsOnClaimSourceAliasingBoundary = true →
      task.isOpenForResearch

theorem current_claim_source_aliasing_dependent_tasks_remain_open :
    ClaimSourceAliasingDependentTasksOpen := by
  intro task present _depends
  exact current_qm_research_tasks_are_open task present

def CurrentCompositeMonoidalResearchFrontSelected : Prop :=
  currentQmResearchFront.kind =
      QmResearchFrontKind.compositeMonoidalLocalTomography
    ∧ currentQmResearchFront.primaryTask =
      QmResearchTaskKind.proveProductMonoidalAssociativityTarget
    ∧ currentQmResearchFront.localTomographyTask =
      QmResearchTaskKind.proveProductLocalTomographyTarget
    ∧ currentQmResearchFront.status = QmResearchTaskStatus.active

theorem current_composite_monoidal_research_front_selected :
    CurrentCompositeMonoidalResearchFrontSelected := by
  unfold CurrentCompositeMonoidalResearchFrontSelected currentQmResearchFront
  exact And.intro rfl (And.intro rfl (And.intro rfl rfl))

def CurrentCompositeMonoidalClaimBoundaryPreserved : Prop :=
  currentQmResearchFront.openTheoremCard =
      CurrentTheoremCardId.monoidalTensorCompositionTheorem
    ∧ currentQmResearchFront.targetObligation =
      CurrentQmObligationId.tensorCompositionLaw
    ∧ currentQmResearchFront.negativeControl =
      CurrentTheoremCardId.realHilbertCompositeHiddenJointInvariant
    ∧ currentQmResearchFront.bornHilbertDeferred = true
    ∧ currentLedgerTheoremCardFormalProofCount = 0
    ∧ currentLedgerQmObligationFormalProofCount = 0

theorem current_composite_monoidal_front_preserves_claim_boundary :
    CurrentCompositeMonoidalClaimBoundaryPreserved := by
  unfold CurrentCompositeMonoidalClaimBoundaryPreserved currentQmResearchFront
  exact And.intro rfl
    (And.intro rfl
      (And.intro rfl
        (And.intro rfl
          (And.intro
            current_theorem_card_formal_proof_count_is_zero
            current_qm_obligation_formal_proof_count_is_zero))))

def CompositeMonoidalNegativeControlPreserved : Prop :=
  ∃ entry, entry ∈ currentTheoremCardLedger
    ∧ entry.id = CurrentTheoremCardId.realHilbertCompositeHiddenJointInvariant
    ∧ entry.role = TheoremCardRole.failure
    ∧ entry.status = CurrentProofStatus.finiteVerifierPass

theorem composite_monoidal_front_preserves_rebit_negative_control :
    CompositeMonoidalNegativeControlPreserved := by
  exact ⟨{
      id := CurrentTheoremCardId.realHilbertCompositeHiddenJointInvariant,
      role := TheoremCardRole.failure,
      status := CurrentProofStatus.finiteVerifierPass
    },
    by simp [currentTheoremCardLedger],
    And.intro rfl (And.intro rfl rfl)⟩

theorem qm_research_plan_does_not_close_current_born_or_hilbert_blockers :
    exactQmClosureBlockedByCurrentFrontier :=
  current_frontier_blocks_exact_qm_closure

end V8
end MetaLang
end IDT
