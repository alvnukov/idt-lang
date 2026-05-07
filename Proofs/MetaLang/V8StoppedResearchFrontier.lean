import Proofs.MetaLang.V8ContextFirstPrimitiveBase
import Proofs.QMClosure.FullQMSectorClosure

namespace IDT
namespace MetaLang
namespace V8

open IDT.QMClosure

/-!
V8 migration frontier.

This file records the layer where research is frozen for migration into Lean.
It does not introduce new physics. It only exposes, in Lean, the current
frontier already present in the repository:

* finite standard-QM sector closure is conditional on B1, constructive
  context-first witness completeness, and carrier-frontier exhaustion;
* exact fundamental QM still requires lower-base derivations, external
  Hilbert/Born/unitary/tensor adequacy, exact universal Born readout, and
  first-principles physical phase scale.
-/

structure V8FiniteSectorMigrationInputs where
  base : B1PrimitiveBase
  source : ContextFirstConstructiveWitnessCompleteness
  frontier : CarrierFrontierExhaustion
  sourceReady : ContextFirstConstructiveWitnessCompletenessReady source

def V8FiniteSectorMigrated
    (inputs : V8FiniteSectorMigrationInputs) : Prop :=
  FullFiniteStandardQMSectorClosed
    (b1ContextFirstFrontierSectorStatus
      inputs.base
      inputs.source
      inputs.frontier)

theorem v8_finite_sector_migration_closes_under_existing_inputs
    (inputs : V8FiniteSectorMigrationInputs) :
    V8FiniteSectorMigrated inputs :=
  b1_context_first_frontier_closes_full_finite_standard_qm_sector
    inputs.base
    inputs.source
    inputs.frontier
    inputs.sourceReady

def V8ExactFundamentalQMStillRequires
    (contract : ExactFundamentalQMClosureContract) : Prop :=
  contract.lowerBaseDerivesB1
    ∧ contract.lowerBaseDerivesContextFirstWitnessCompleteness
    ∧ contract.lowerBaseDerivesCarrierFrontierExhaustion
    ∧ contract.externalHilbertBornUnitaryTensorAdequacy
    ∧ contract.exactUniversalBornReadout
    ∧ contract.firstPrinciplesPhysicalPhaseScale

theorem v8_exact_fundamental_qm_requires_all_frontier_obligations
    (contract : ExactFundamentalQMClosureContract)
    (ready : ExactFundamentalQMClosureContractReady contract) :
    V8ExactFundamentalQMStillRequires contract :=
  ready

structure V8ResearchFreezeBoundary where
  contextFirstBase : ContextFirstPrimitiveBaseCandidate
  exactContract : ExactFundamentalQMClosureContract
  noNewPhysicalClaims : Prop

def V8ResearchFreezeBoundary.valid
    (boundary : V8ResearchFreezeBoundary) : Prop :=
  boundary.contextFirstBase.isLeanMigrationBoundary
    ∧ V8ExactFundamentalQMStillRequires boundary.exactContract
    ∧ boundary.noNewPhysicalClaims

theorem v8_research_freeze_preserves_context_first_boundary
    (boundary : V8ResearchFreezeBoundary)
    (valid : boundary.valid) :
    boundary.contextFirstBase.isLeanMigrationBoundary :=
  valid.left

theorem v8_research_freeze_preserves_exact_qm_frontier
    (boundary : V8ResearchFreezeBoundary)
    (valid : boundary.valid) :
    V8ExactFundamentalQMStillRequires boundary.exactContract :=
  valid.right.left

end V8
end MetaLang
end IDT
