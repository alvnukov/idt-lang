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

/-!
Recording the `overlap_preservation_dynamics` wall.

The `overlap_preservation_dynamics` full_qm_proof_closure obligation requires
"reversible inheritance preserves normalized overlap" as a universal statement
about bijective inheritance maps. The Lean artifact
`Proofs/QMClosure/OverlapPreservationDynamicsProof.lean` establishes the
closure properties of the IDT-native `PreservesOverlap` predicate (identity,
composition, and inverse closure under bijectivity), but does NOT derive
`PreservesOverlap` from `Bijective` alone.

This is an explicit IDT-native bridge wall: the preservation property must be
supplied as an IDT-native hypothesis (analogous to how `FacticizationStability`
is supplied as an IDT primitive for `context_normalization`), and the IDT
primitive base currently does not provide a `Bijective → PreservesOverlap`
derivation. Until such a primitive or bridge lemma is added, this obligation
must not be promoted to formal_proof on the basis of the existing Lean
artifact.

This ledger entry records the wall so a future agent does not mechanically
promote `overlap_preservation_dynamics` to formal_proof using the closure
theorems, which would be an overclaim.
-/

def overlap_preservation_dynamics_bridge_wall_recorded : Prop :=
  -- The artifact exists and compiles, but its top-level witness is the
  -- tautological `reversible_inheritance_preserves_overlap` (a conjunction
  -- of the supplied hypotheses), which does not derive preservation from
  -- bijectivity. The closure lemmas are real but weaker than the obligation.
  True

theorem overlap_preservation_dynamics_remains_behind_bridge_wall :
    overlap_preservation_dynamics_bridge_wall_recorded := by
  trivial

/-!
Born wall research result (2026-07-20 audit).

The Born wall is machine-diagnosed as an IMPOSSIBILITY for the current
hypothesized primitive base (B0/B1/B2-accounting), with four independent
Lean countermodels:

  * `Proofs/QMClosure/BornWallSeparation.lean:69`
    `readout_accounting_does_not_select_quadratic_actualization`:
    linear `[3,4]/7` and quadratic `[9,16]/25` are both admitted by
    `ReadoutAccountingAdmits` with distinct denominators.
  * `Proofs/QMClosure/S2BornProofSearch.lean:77`
    `b2_like_accounting_does_not_force_s2` (witness `thirdOrderStableCore`).
  * `Proofs/QMClosure/S2BornProofSearch.lean:377`
    `current_primitive_discipline_does_not_force_pairwise_basis`
    (witness `localTernaryPrimitiveDiscipline`).
  * `Proofs/QMClosure/BornHilbertUniversalClosure.lean:397`
    `b1_interface_projection_does_not_force_context_first_endpoint_data`
    (witness `b1OnlyMissingContextFirstSource`).

Three falsification probes were run against the conditional bridge
`context_first_endpoint_data_plus_frontier_closes_born_hilbert`
(`BornHilbertUniversalClosure.lean:343`):

  1. Bridge soundness — PASS. The bridge is a pure field projection
     composing `context_first_endpoint_data_selects_born`
     (`BornHilbertUniversalClosure.lean:329`) with
     `context_first_plus_frontier_exhaustion_closes_hilbert_frontier`.
     No `sorry`/`admit`/`axiom`/`Classical.choice`. Sound conditional on
     the existence of a `ContextFirstUniversalEndpointData` inhabitant
     satisfying `ContextFirstConstructiveWitnessCompletenessReady`.
  2. Semantic-equivalence wall — PASS. The three load-bearing witness
     fields of `ContextFirstConstructiveWitnessCompleteness`
     (`externalFrequencyWitness`, `constructiveCarrierWitness`,
     `noHiddenJointOnlyGeneration`) are defined strictly weaker than
     Born. They speak about oriented two-cover counts, endpoint
     alignment (`yesBranch = aligned`), pairwise closure, and exclusion
     of hidden joint-only invariants. The quadratic Born weight law
     appears only as a CONSEQUENCE in the external lemma
     `constructor_respecting_oriented_readout_select_phase_square`, not
     as a hypothesis or definition. The bridge is not circular.
  3. Countermodel on successor base — PASS. Every recorded countermodel
     targets B0/B1/B2-accounting. No Lean witness or markdown claim
     exhibits a model where the three witness fields hold AND Born still
     fails. The bridge is not known to be falsifiable on the successor
     base.

Synthesis: the Born wall is NOT an impossibility in principle. It is an
impossibility for B1 specifically, because B1 does not supply three
independent constructive witnesses that the bridge requires. Crossing
the wall requires constructing an inhabitant of
`ContextFirstConstructiveWitnessCompleteness` with
`externalFrequencyWitness = True`,
`constructiveCarrierWitness = True`,
`noHiddenJointOnlyGeneration = True`,
without importing `born_rule`/`hilbert_space`/`tensor_product_axiom`.

Critical caveat (do not gloss over): no concrete inhabitant of
`BoundPrimitiveGeneratedBase` or `B1PrimitiveBase` exists anywhere in
`Proofs/`. Every CGSC/B1 closure theorem is of the form
`∀ base : B1PrimitiveBase, …`, which is vacuously true if no inhabitant
exists. So the entire CGSC edifice is conditional on a HYPOTHESIZED
base, not a proven one. Constructing the successor base is the load-
bearing research step, not a mechanical lemma.

Most likely shape of the missing input (not a primitive recommendation,
just the structural shape the evidence points to):
  * the three witness fields are INDEPENDENT — none is derivable from
    the other two or from B0/B1 alone;
  * `noHiddenJointOnlyGeneration` is the narrowest because it overlaps
    with the composite-closure / local-tomography front and the claim-
    source aliasing boundary recorded elsewhere in this ledger;
  * any new primitive that supplies these three witnesses must come with
    a `V7FPrimitiveIndependence.lean`-style countermodel showing it is
    strictly weaker than Born (else the wall is being bridged by hidden
    equivalence, which is the original circularity the wall was erected
    to prevent).

This entry records the diagnosis so a future research pass does not
re-derive it and does not mis-classify the wall as either "missing
proof, keep trying" (it is not — countermodels say B1 cannot do it) or
"fundamental impossibility" (it is not — the successor-base bridge is
sound and no countermodel on that base is known).
-/

def born_wall_diagnosis_recorded : Prop :=
  -- Three falsification probes (bridge soundness, semantic-equivalence
  -- wall, successor-base countermodel) all PASS, and the wall is
  -- recorded as an impossibility for B1 specifically, bridgeable on a
  -- successor base whose inhabitant is currently absent from Lean.
  True

theorem born_wall_is_impossibility_for_b1_bridgeable_on_successor_base :
    born_wall_diagnosis_recorded := by
  trivial

theorem b1_primitive_base_has_no_known_lean_inhabitant :
    -- Structural observation recorded for future research passes: the
    -- CGSC/B1 closure theorems are universally quantified over
    -- `base : B1PrimitiveBase`, and no concrete inhabitant of that type
    -- is constructed anywhere in `Proofs/`. This makes the closure
    -- vacuously sound until an inhabitant is built. The theorem is
    -- recorded as `True` because the non-existence of an inhabitant in
    -- the current codebase is an empirical fact about the proof tree,
    -- not a proposition Lean can decide; the prose above carries the
    -- load-bearing content.
    True := by
  trivial

/-!
Refinement of the Born wall diagnosis (2026-07-21 follow-up audit).

The 2026-07-20 entry above classified the wall as an impossibility for B1
bridgeable on a successor base, on the strength of three PASS probes
(bridge soundness, semantic-equivalence wall, successor-base countermodel).
A follow-up pass examined the actual carrier shape the bridge consumes
and refined the picture. Two structural facts need to be on record so the
next research pass does not misjudge how close the wall is to closing.

FACT A — the witness completeness layer is a bag of abstract Prop flags.
`Proofs/QMClosure/ConstructiveWitnessPrimitiveBase.lean:444-466`
`ContextFirstConstructiveWitnessCompleteness` is a structure with 22
fields, ALL of type `Prop`, with no operations, no carrier, no laws. Its
`Ready` predicate (lines 468-491) is the conjunction of all 22 flags.
`ConstructiveFacticizationSemantics` (ConstructiveFacticizationSemantics.lean
:19-43) is the same shape with 24 abstract Prop fields. None of these
fields is connected to a concrete mathematical object (no `Fin n` carrier,
no D-endpoint data, no concrete `OrientedTwoCoverCounts`); they are
abstract propositions whose content lives in markdown, not in Lean.

Consequence: an all-True inhabitant of either structure is trivial to
build (set every flag to `True`) and would satisfy the `Ready` predicate
by `trivial`. This means that *at the witness-completeness layer alone*
the bridge is vacuously satisfiable. The bridge's `Ready` premise does
not, by itself, encode a non-trivial mathematical constraint.

FACT B — the bridge is NOT purely witness-layer; it also consumes
concrete data. `ContextFirstUniversalEndpointData`
(BornHilbertUniversalClosure.lean:288-295) bundles the witness `source`
plus three concrete fields:
  * `cover : context → OrientedTwoCoverCounts`
  * `labels : context → OrientedReadoutBranchLabels`
  * `endpointAligned : ∀ ctx, (labels ctx).yesBranch = aligned`
  * `binaryExclusive : ∀ ctx, (labels ctx).yesBranch ≠ (labels ctx).noBranch`
Similarly `UniversalPrimitiveBoundaryEndpointCoverage` (lines 245-254)
requires a concrete `boundary : context → PrimitiveBoundaryCandidate`
plus a non-vacuous `pairwiseClosed :
∀ ctx, PrimitiveBoundaryClosesPairwiseCoverage (boundary ctx)`.

So the bridge is sound and non-vacuous ONLY IF the concrete combinatorial
fields (`cover`, `labels`, `boundary`, `pairwiseClosed`, `endpointAligned`,
`binaryExclusive`) carry real mathematical content for some carrier
`context`. The witness layer being a bag of True flags is necessary but
not sufficient; the bridge actually requires a concrete finite model in
which the oriented two-cover counts, branch labels, and primitive
boundary candidate all satisfy the closure conditions on every context.

REFINED SYNTHESIS:
  * The 2026-07-20 PASS probes are still valid: the bridge is not
    syntactically broken and is not circular.
  * But the wall is NOT as close to closing as the all-True-inhabitant
    reading might suggest. The hard step is constructing a concrete
    carrier with concrete `cover`/`labels`/`boundary` data such that
    `PrimitiveBoundaryClosesPairwiseCoverage` holds on every context AND
    `ContextFirstConstructiveWitnessCompletenessReady source` holds AND
    none of the three import guards (`noBornImport`, `noHilbertImport`,
    `noTensorImport`) is violated.
  * The right next probe is therefore NOT "build an all-True witness"
    (that is vacuous and proves nothing) but "exhibit a concrete finite
    carrier model, or prove no such model exists without Born". That is
    constructive model theory on `Fin n` carriers and is beyond
    mechanical scaffolding.

OPEN FOLLOW-UP PROBE (recorded for a stronger model):
  * Try `context := Fin 2` or `context := Bool` as the smallest carrier.
  * Enumerate the `OrientedTwoCoverCounts` and `OrientedReadoutBranchLabels`
    inhabitants for that carrier.
  * Check whether ANY combination satisfies `endpointAligned`,
    `binaryExclusive`, and `PrimitiveBoundaryClosesPairwiseCoverage`
    simultaneously without importing Born.
  * If yes: the wall is bridged on a minimal model, and the remaining
    work is lifting to the universal quantifier.
  * If no: record the smallest carrier at which no such model exists;
    that becomes the new hardest obstruction and may require either a
    larger successor primitive or an explicit impossibility theorem.

This entry is documentation of a research diagnosis. It does not upgrade
any scientific status. No theorem here proves physics; the `True`
theorem is a machine-visible marker that the prose block above has been
installed in the ledger.
-/

def born_wall_bridge_carrier_probe_pending : Prop :=
  -- The bridge's witness-completeness layer is vacuously satisfiable,
  -- but the bridge also requires concrete combinatorial data; the
  -- refined open probe is to exhibit a concrete finite carrier that
  -- satisfies both layers without importing Born.
  True

theorem born_wall_bridge_remains_pending_concrete_carrier_probe :
    born_wall_bridge_carrier_probe_pending := by
  trivial

end V8
end MetaLang
end IDT
