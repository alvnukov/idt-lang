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

/-!
Born wall: literature grounding and the Γ-coherence negative (2026-07-21).

This block records a concrete advance in shape (not in proof), by tying
the Born wall diagnosis to the standard reconstruction-of-quantum-theory
literature, and recording a falsified hypothesis about how the wall
might have been crossed.

LITERATURE GROUNDING — purification is the known selector.
The Chiribella–D'Ariano–Perinotti reconstruction
(G. Chiribella, G. M. D'Ariano, P. Perinotti, "Informational
derivation of Quantum Theory", Phys. Rev. A 84, 012311 (2011),
arXiv:1011.6451; companion "Probabilistic theories with purification",
Phys. Rev. A 81, 062348 (2010), arXiv:0908.1583) derives finite-
dimensional complex Hilbert space, the Born rule, the tensor-product
composition, and the spectral theorem from a single informational
postulate:

  PURIFICATION POSTULATE. Every mixed state ρ on system A admits a
  purification: a pure state ψ on A ⊗ E (for some auxiliary system E)
  whose marginal on A is ρ, and every two purifications of the same
  ρ differ by a reversible transformation on E alone.

The crucial word is UNIQUENESS UP TO REVERSIBLE TRANSFORMATION ON THE
PURIFYING SYSTEM. Without that half of the postulate, classical
theories, real-quantum, and box-world all satisfy "every mixed state
has some extension". The uniqueness half is what kills the
non-quadratic alternatives.

IDT-native correspondence.
The IDT field `noHiddenJointOnlyGeneration`
(ConstructiveWitnessPrimitiveBase.lean:463;
ContextFirstConstructiveWitnessCompletenessReady requires it at line
488) is the context-first, history-space reading of the same physical
content: every stable composite context invariant must be generated
from subsystem witnesses by a reversible inheritance transport, with
no invariant that lives only at the joint context (a "hidden joint-
only generation"). Read this way, the three load-bearing witness
fields of the bridge layer correspond to:
  * noHiddenJointOnlyGeneration  ≈  purification-uniqueness half
  * constructiveCarrierWitness   ≈  existence of an auxiliary carrier
                                    E that supports the purification
  * externalFrequencyWitness     ≈  the measurable marginal (the
                                    "frequency" side of A) being
                                    stably reconstructable from E
So the bridge is not ad hoc: it is the IDT-typed shadow of the
standard reconstruction. The hard research step is the same in both:
type `noHiddenJointOnlyGeneration` as a real proposition about a
concrete carrier, not as an abstract `Prop` flag, and either exhibit
a model or prove impossibility.

FALSIFIED STRENGTHENING — Γ-coherence per single readout is not enough.
A natural but insufficient strengthening of `StableFiniteReadout`
accounting is to require the weights to come from a positive-
semidefinite kernel Γ via the IDT actualization measure
μ(A) = Σ_{h,h'∈A} W_h W_h' Γ_{h,h'}. This is the form already used by
the four machine-checked Born-readout proofs (ContextNormalizationProof
through OperationalEquivalenceProbability), so it is tempting to hope
it selects the quadratic exponent. It does NOT, in the single-readout
form. Concrete counterexample, verified by hand:
  * Linear pair (3,4) is realized by Γ_L = diag(3,4) with W = (1,1),
    giving μ = (3,4) up to scale.
  * Quadratic pair (9,16) is realized by Γ_Q = I with W = (3,4),
    giving μ = (9,16).
Both Γ_L and Γ_Q are PSD. Requiring the weights to "arise from some
PSD Γ" therefore does not select the quadratic law; the linear
countermodel survives. The PSD carrier is per-readout, so this says
nothing about cross-readout consistency. A Lean formalization of this
counterexample was drafted and withdrawn only because of unrelated
`decide`-over-ℝ reduction friction; the mathematical content above is
the load-bearing part and is correct.

This sharpens the shape of the missing selector. It is NOT enough to
require Γ-coherence at the level of an individual readout; the
selector must constrain Γ ACROSS contexts (the same Γ must be shared
between readouts AND their coarse-graining AND their purifications),
which is exactly the cross-context content of the purification
postulate above. IDT's `noHiddenJointOnlyGeneration`, read as
purification-uniqueness, is precisely the right kind of cross-context
constraint. The research frontier is to type it as a real proposition.

OPEN PROBE (revised, for a stronger model):
  * Type `noHiddenJointOnlyGeneration` as a concrete statement about a
    2-point context with carrier E, in the form
    "every pure invariant on A ⊗ E has its A-marginal reconstructable
    from a subsystem witness, and any two purifications differ by a
    reversible map on E".
  * Check the smallest case: A = {0,1}, E = {0,1}. Under that typed
    condition, do linear readouts (3,4) survive? The CDP theorem says
    no; an explicit IDT-native witness would either reproduce that
    theorem or expose a divergence between IDT's noHiddenJointOnlyGeneration
    and the CDP postulate.
  * If IDT's reading diverges (e.g. it is strictly weaker than the CDP
    uniqueness half), the Born wall is a real impossibility for the
    IDT primitive base, not just an under-typing; that would itself be
    a publishable negative result. If they coincide, the wall is
    bridgeable and the remaining work is the standard CDP derivation
    re-expressed in IDT terms.

This block is documentation of research positioning. It does not
upgrade any scientific status, does not import quantum-theoretic
machinery, and does not prove physics. The `True` theorems below are
machine-visible markers that the prose block has been installed.
-/

def born_wall_literature_grounding_recorded : Prop :=
  -- The wall has been positioned relative to the CDP purification
  -- reconstruction, and a falsified single-readout Γ-coherence
  -- strengthening has been recorded.
  True

theorem born_wall_positioned_against_purification_reconstruction :
    born_wall_literature_grounding_recorded := by
  trivial

/-!
Logical-coherence audit of the entire theory (2026-07-21).

A 5-axis audit cross-checked the formal proof ledger, the derivation paths,
the primitive base coherence, the manifest ↔ Lean correspondence, and the
hidden assumptions/contradictions. The audit was concrete and brutally
honest: every finding below is sourced to a specific file:line. The
purpose is to prevent prose-driven overestimation of how much of the
theory is actually derived, and to mark the precise locus of each gap.

This block records the audit. It does NOT upgrade any scientific status;
the `True` theorems are machine-visible markers that the prose has been
installed. The audit's load-bearing content is in the prose, not in the
theorems.

FINDING 1 — of the 38 formal_proof refs in IDTCore.lean:7-45, only 5
carry real mathematical content; the other 33 are registry self-checks.

  * 5/38 are FINITE_COMBINATORIAL_IDENTITY (real Lean theorems):
    - `IDT.QMClosure.measure_nonneg` (ContextNormalizationProof.lean:22)
      — F → μ(A) ≥ 0; real `linarith` over `Finset.sum_subset`.
    - `IDT.QMClosure.exclusivity_additivity` (ExclusivityAdditivityProof.lean:78)
      — μ(A∪B) = μ(A)+μ(B) under facticity; real `simp`/`rw`.
    - `IDT.QMClosure.coarse_graining_consistency` (CoarseGrainingConsistencyProof.lean:14)
      — 3-block iterated additivity; real `abel` after rewriting.
    - `IDT.QMClosure.operational_equivalence_probability` (OperationalEquivalenceProbabilityProof.lean:16)
      — μ(A) = μ(A') under W/Γ-preserving bijection; real `Finset.sum_bij'`.
    - `IDT.QMClosure.projective_action_identity` + `_composition` + `_laws_universal`
      (ProjectiveActionProof.lean:66, 82, 103) — universal preimage-action laws;
      real `funext`/`propext`.
    In all 5 the physics is in the hypotheses (F supplied, Γ Hermitian, cross-
    actualization vanishes); the theorems verify that the finite algebra is
    correct given the physics.

  * 33/38 are NATIVE_DECIDE_REGISTRY: literal `"formal_proof"` strings in
    manifest fields, re-validated by `native_decide` in IDTCore.lean:1199-1261
    against an in-file copy of the same manifest. They check Nodup, length,
    SHA-256 digest, count, and string-equality-with-itself. None proves any
    mathematical fact about the physics; none can fail unless the file
    disagrees with itself. They are the manifest auditing itself.

FINDING 2 — the only real, non-circular physics derivations in the entire
proof tree are:

  * `F → 2×2 PSD forward conditions` (V7PositiveGeometryGeneral.lean:22-32):
    a≥0, c≥0, a+2b+c≥0, a-2b+c≥0, by `linarith` with witnesses (1,0),(0,1),
    (1,1),(1,-1). Real.
  * `F → ac≥b²` (V7PositiveGeometryGeneral.lean:48-89, `det_nonneg`): by
    `nlinarith`/`by_cases` with witnesses (-b,a) and (c,-b). Real.
    NOTE: sections/175-primitive-base-completeness-status.md:25 still
    labels this an "axiom (strategy known)"; the label is stale, the
    theorem is proved.
  * `F → μ(A) ≥ 0` (ContextNormalizationProof.lean:22) plus the four
    finite-combinatorial identities in FINDING 1.

That is the entire real derivation surface. Everything else is either
conditional (`∀ base : B1PrimitiveBase, …`, see FINDING 4) or vacuous.

FINDING 3 — several markdown status labels overstate what the Lean file
proves. Specifically:

  * `sections/175-primitive-base-completeness-status.md` labels B0 →
    `product_context_exhaustion` / `local_tomography` / `bounded_correlations`
    as `derived_from_B0` / `derived_from_B0_F`. The actual Lean theorems
    (V7ProductContextExhaustion.lean:32, V7LocalTomography.lean:31,
    V7BoundedCorrelations.lean:27-42) are all `… → True := trivial` with
    `D := fun _ _ _ => True`. They are vacuous; the markdown labels are
    not currently supported by the code.
  * `sections/175:25` labels `F → ac≥b²` an "axiom (strategy known)". It
    is proved; the label should be updated to "derived".
  * `sections/175:37,76` labels `D_G = 4` as "NOT derivable". The Lean
    file V7DimensionAnalysis.lean has `theorem dg4_not_from_b0 : True
    := trivial` and `def status := "analysis_only"`. The non-derivability
    is argued in markdown, not proved in Lean.
  * `sections/175:31` "CONTEXT_FIRST_ENDPOINT_DATA_TO_BORN_HILBERT_PROVED"
    overstates: the bridge theorem is conditional on an unproven
    `ContextFirstConstructiveWitnessCompletenessReady source` and a
    further `ContextFirstUniversalEndpointData context` payload (see
    FINDING 4); the universal frontier is provably NOT closed
    (BornHilbertUniversalClosure.lean:547,
    `current_finite_born_hilbert_route_does_not_close_universal_frontier`).

FINDING 4 — three of the four "primitives" have no Lean formalization,
and the fourth (F) is only proved independent of a stub of B0.

  * `V7FPrimitiveIndependence.lean`: real countermodel for F vs. a 2-clause
    toy B0 (`Ctx = Bool, Alt = Bool, R case-wise, D := True`). F is
    independent of THAT toy B0, not of the full B0 contract.
  * `V7QPrimitiveIndependence.lean:38`: `def status := "independence_argued"`.
    No Lean `def Q`, no Lean theorem.
  * `V7ActionPrimitiveIndependence.lean:57`: `def status :=
    "independence_argued"`. No Lean `def action_quantum`, no theorem.
  * No Lean countermodel proves the FOUR primitives are JOINTLY
    consistent (a model where B0 ∧ F ∧ Q ∧ action_quantum all hold).
  * No Lean countermodel proves MUTUAL independence of the four
    (Q vs. (B0∧F∧action), action vs. (B0∧F∧Q), etc.). Only F-vs-toy-B0
    has a countermodel.

FINDING 5 — `BoundPrimitiveGeneratedBase`, `B1PrimitiveBase`, and
`GroundedCGSCSemanticExtensionBase` have NO concrete inhabitant anywhere
in `Proofs/`. Every CGSC/B1 closure theorem is of the form
`∀ base : <base_structure>, …`. Until a concrete inhabitant is constructed
these theorems are vacuously true. The CGSC edifice is conditional on a
hypothesized, not constructed, base.

FINDING 6 — claim-source aliasing structurally inflates apparent coverage
by roughly 3-4×. Per CGSCGroundedSemanticExtensions.lean:392-501 and the
recorded boundary `grounded_cgsc_claim_source_aliasing_boundary` (line
492):

  * `completeExposedSource ground` fills 5 slots
    (completeExposedContextPartition, spectralDecomposition,
    contextNormalization, operationalEquivalenceProbability,
    physicalPhaseScaleBoundary).
  * `reversibleSource ground` fills 4 slots
    (richDclReversibleSymmetry, dclAutomorphismDynamics,
    overlapPreservationDynamics, projectiveAction).
  * `productSource ground` fills 5 slots
    (productContextExhaustion, localTomography,
    monoidalAssociativity, entanglementClosure,
    projectiveLimitConsistency).
  * `noHiddenJointSource ground` fills 2 slots
    (constructiveCarrierWitness, noHiddenJointOnlyGeneration).
  * `refinementSource ground` fills 2 slots
    (coherentRefinementCompactness, continuousInheritanceFamily).
  * `generatorSource ground` fills 2 slots
    (generatorBookkeepingWithoutStone, generatorClosure).

So ~20 named target slots are populated by ~6 underlying source
propositions. The theory HONESTLY records this (sections/177:1093-1095:
"source-witness scaffold, not target-specific derivation"; the task
`splitClaimSourceAliases` is registered as actively blocking exact-QM
research at V8QmResearchTaskLedger.lean:195-206). But the count "21 full-
QM proof obligations" reads as 21 independent claims and is actually
~6 source propositions restated under multiple names. This is the single
largest prose-vs-code gap.

FINDING 7 — the seven CGSC clauses (finiteGeneration,
facticizableSeparation, exposedContextDecomposition,
reversibleRouteClosure, coherentRefinementFlow,
compositeRouteGeneration, importBoundary; CGSCStructuralTargetKernel.lean
:6-13) have NO Lean theorem of mutual non-redundancy or independence.
The claim "seven independent CGSC clauses" is unverified. Given the
aliasing in FINDING 6, several clauses are doing double duty.

FINDING 8 — the manifest's machine-checked surface is clean. All 6
`machine_checked_finite_proof` proof cards in gate 173 cite Lean theorems
that exist, compile, carry no `sorry`/`admit`, and have signatures
matching the obligation statements. The bidirectional ledger check
(check_formal_proof_ledger_coverage, theory_verifier/core.py:5816-5863)
correctly finds no `missing` or `stale` violation. The verifier is not
the source of the overstatement; the markdown prose is.

FINDING 9 — no hidden contradiction found. The assumed components
(facticizable_distinguishability_closure,
proper_subcontext_endpoint_exhaustion, no_hidden_context_only_fact,
ContextFirstConstructiveWitnessCompleteness, B1PrimitiveBase,
BoundPrimitiveGeneratedBase) are not mutually inconsistent; they are
layered necessities none of which is currently derived from primitives.
The bridge `context_first_endpoint_data_plus_frontier_closes_born_hilbert`
(BornHilbertUniversalClosure.lean:343) is provably non-circular with
respect to Born (the three load-bearing witness fields are strictly
weaker than Born; see the 2026-07-20 audit block earlier in this file).

SYNTHESIS — IDT is an assembled collection of conditional scaffolds over
a small, real kernel of finite-combinatorial lemmas, not a coherent
derivation of QM from primitives. The kernel of real derivation content
is: F → 2×2 PSD forward conditions + det_nonneg, and F → 4 finite Born-
readout identities + projective_action universal preimage laws. Around
this kernel, the theory assembles: (i) three primitives without Lean
formalization (Q, action_quantum, full B0); (ii) conditional universal
closures over structures that have no concrete inhabitant
(BoundPrimitiveGeneratedBase, B1PrimitiveBase,
GroundedCGSCSemanticExtensionBase); (iii) ~20 named target slots
populated by ~6 underlying source propositions (acknowledged aliasing);
(iv) markdown status labels that overstate Lean's content (derived vs.
trivial, axiom vs. proved, PROVED vs. conditional).

None of this is fraud: the conditional structures are honestly labelled
in the manifest, the aliasing is recorded as an open blocker, the
countermodels are real, the forbidden-import discipline is sound. The
correctable issue is the prose-vs-code gap: markdown uses "derived" /
"proved" / "from B0" in places where the code is `True := trivial` or
`∀ base, …` over an uninhabited type.

RECOMMENDED CORRECTIVE WORK (not done in this commit; recorded as a
target for the next pass):
  (a) Audit sections/174 and sections/175 line by line against the
      Lean files; reword or remove every "derived_from_B0" /
      "PROVED" / "axiom" label that the Lean does not support. FINDING
      3 lists the specific stale labels.
  (b) Construct an explicit Lean countermodel for the joint consistency
      of the four primitives (B0, F, Q, action_quantum) on a minimal
      carrier, or prove no such model exists. FINDING 4 (d).
  (c) Prove mutual independence of the four primitives, on the pattern
      of V7FPrimitiveIndependence.lean, for at least the missing pair
      Q vs. (B0 ∧ F ∧ action_quantum) and action vs. (B0 ∧ F ∧ Q).
      FINDING 4 (e).
  (d) Either prove the seven CGSC clauses mutually independent or
      reduce the count to the actually-independent subset and rename.
      FINDING 7.
  (e) Replace the markdown "21 obligations" framing with the honest
      "~6 source propositions aliased across ~20 named slots" framing
      in PUBLIC_CLAIM_SHEET.md and README.md. FINDING 6.

This audit is documentation; it does not upgrade any scientific status.
The closure verdict remains CONDITIONAL_PACKAGE_ARTIFACTS_REGISTERED
with proved=5, conditional=16, missing=0.
-/

def theory_logical_coherence_audit_recorded : Prop :=
  -- A 9-finding logical-coherence audit has been installed in the
  -- ledger, identifying the real derivation surface (F → 2×2 PSD +
  -- det_nonneg + 4 finite Born-readout identities + projective_action
  -- universal preimage laws), the prose-vs-code gaps, the unformalized
  -- primitives, the uninhabited base structures, and the aliasing
  -- inflation. No hidden contradiction found; the gap is prose
  -- overstatement, not manifest fraud.
  True

theorem theory_logical_coherence_audit_installed :
    theory_logical_coherence_audit_recorded := by
  trivial

/-!
IDT principle for Born: physical-content note + critical falsification
of an over-claim (2026-07-21).

A first pass at identifying the IDT-native Born selector produced an
over-claim that this block corrects. The correction matters because
truth is the project's non-negotiable priority.

PHYSICAL HYPOTHESIS (the candidate principle, stated honestly).

The IDT research notes (sections/175:160-167, 522-545) propose that the
Born rule's quadratic exponent is the readout shadow of an ontological
claim about distinction:

  STABLE DISTINCTION IS PAIRWISE COMPARISON DATA.
  No stable facticizable invariant lives only at the whole-context
  level; every stable facticizable invariant decomposes into proper-
  subcontext (singleton + pairwise) witnesses via reversible inheritance
  transport, with loss/accounting for any residue.

Stated this way, this is the IDT-context-first version of Sorkin I3 = 0
and the naturality of arity 2. It is conceptually distinct from the
Chiribella-D'Ariano-Perinotti purification-uniqueness postulate (Phys.
Rev. A 84, 012311 (2011), arXiv:1011.6451): CDP is system-extension
(existence and uniqueness-up-to-reversible-E of a purification on
A ⊗ E), the IDT candidate is context-first ontology (non-existence of
whole-context-only stable facts). They coincide in conclusion but are
not known to be equivalent as axioms.

That much is a real research hypothesis worth pursuing.

OVER-CLAIM THAT IS NOW REVERTED.

A previous version of this block (commit 93c283d, since reverted in
4d8422d) asserted that "the selection theorem is already in the repo",
citing S2BornProofSearch.lean:122-133 as a machine-checked derivation
that the IDT principle selects S2. Critical re-examination shows this
is FALSE.

The Lean in S2BornProofSearch.lean operates over `S2CandidateCore`
(lines 16-25), a structure whose fields are nine abstract `Prop` flags
(`dclClosed`, `finiteFacticity`, `orientedComparisons`, `lossAccounting`,
`singletonWitness`, `pairwiseWitness`, `ternaryWitness`,
`nonnegativeCompositeWeights`, `stableI3Nonzero`). There is no concrete
carrier, no measurement algebra, no Born-vs-linear weights, no actual
Sorkin I3 invariant. The "countermodel" `thirdOrderStableCore`
(lines 50-61) is the same structure with all nine flags set to `True`
— it is a degenerate witness of the same bag-of-Prop-flags kind that
the FINDING 4 audit (above) identified for B1PrimitiveBase.

Concretely:
  * `HiddenContextOnlyFact core := ternaryWitness ∧ stableI3Nonzero ∧
    ¬ PairwiseWitnessExhaustive core` (lines 42-45), with
    `PairwiseWitnessExhaustive core := ternaryWitness → False` (line 40).
  * Simplifying: `HiddenContextOnlyFact core = ternaryWitness ∧
    stableI3Nonzero`, and `NoHiddenContextOnlyFact core = ¬(ternary ∧
    stableI3)`.
  * `SecondOrderFacticization core := ¬ternary ∧ ¬stableI3` (lines 36-37)
    is STRICTLY STRONGER than `NoHiddenContextOnlyFact core`.
  * The "selection lemma" `no_hidden_context_only_fact_supplies_s2_when_
    ternary_is_i3_source` (lines 122-133) derives the strictly-stronger
    from the strictly-weaker UNDER the bridge `ternaryWitness ↔
    stableI3Nonzero`. That bridge is itself an abstract flag equation,
    not a physical theorem.

The lemma is therefore a tautology about Prop flags. It does not prove
that the IDT physical principle selects Born, because the structure it
quantifies over has no mathematical content to select from. This is the
same pattern the FINDING 4 audit caught for B1: a conditional theorem
over an uninhabited-of-content type, dressed up as physics.

WHAT REMAINS HONEST.

  (a) The physical hypothesis in the first paragraph is not invalidated
      by this. It is a real candidate principle, distinct from CDP,
      worth investigating. But it is currently an UNTESTED hypothesis,
      not a derived theorem.
  (b) The literature distinction (IDT context-first ontology vs CDP
      system-extension) is real and remains the right framing for the
      research question.
  (c) The actual test of the hypothesis is constructive: build a
      concrete carrier model (e.g. context := Fin 2 × Fin 2 with a real
      measurement algebra over Fin 2 outcomes), define the IDT
      principle as a real proposition over that model, and check
      whether it implies Born (weights [9,16]) and excludes linear
      (weights [3,4]) and cubic (weights [8,27]) readouts. No one has
      done this yet.

WHAT IS NOT HONEST AND WAS ALMOST COMMITTED.

  * "The IDT principle for Born is already formalized." (No: the
    formalization is Prop-flag tautology.)
  * "The linear/cubic countermodels are killed by the IDT principle."
    (No: the countermodels are degenerate flag-witnesses, not linear/
    cubic readouts. A real linear readout model has not been built.)
  * "The wall is not a fundamental obstruction." (Untested: the
    obstruction has not been honestly probed on a concrete model.)

KILL TEST, RESTATED HONESTLY.

To test the hypothesis one must construct, on a concrete finite
carrier, a model M that simultaneously:
  (i) satisfies a real-typed version of "no whole-context-only stable
      facticizable invariant",
  (ii) has a linear readout (weights proportional to |a|, not |a|^2),
  (iii) has identically vanishing Sorkin I3.
If M exists, the IDT principle is INSUFFICIENT to select Born. If M
provably cannot exist on any finite carrier, the IDT principle (in its
real-typed form) is SUFFICIENT. Until one of these is shown, the IDT
principle for Born is a research hypothesis, not a result.

This block records the correction. The earlier over-claim commit
(93c283d) is reverted in 4d8422d. No scientific status is upgraded or
downgraded by this block; the closure verdict is unchanged
(CONDITIONAL_PACKAGE_ARTIFACTS_REGISTERED, proved=5, conditional=16,
missing=0).

The lesson recorded for future passes: when a "selection theorem"
looks too clean, check whether it operates over a bag of abstract
Prop flags. If it does, it is not a physics theorem regardless of how
persuasive the prose around it sounds. This is the same discipline as
FINDING 4 of the logical-coherence audit; it applies at every layer of
the proof tree, not just at the primitive base.
-/

def idt_born_principle_status_is_open_hypothesis_not_theorem : Prop :=
  -- The IDT principle "stable distinction is pairwise comparison data"
  -- is a real, distinct-from-CDP research hypothesis about why
  -- probabilities are quadratic. It is NOT a derived theorem: the
  -- existing Lean operates over abstract Prop flags and is therefore
  -- tautological. The hypothesis is testable on a concrete Fin n
  -- carrier but has not been so tested.
  True

theorem idt_born_principle_remains_untested_hypothesis :
    idt_born_principle_status_is_open_hypothesis_not_theorem := by
  trivial

/-!
Honest answer: does the IDT principle select Born? (2026-07-21 analysis).

The previous block recorded the IDT principle as an OPEN hypothesis. A
follow-up hand analysis asked the question concretely: under any of the
natural readings of "stable distinction is pairwise comparison data",
does the principle select Born weights (|a|^2) and exclude linear
weights (|a|) and cubic weights (|a|^3)?

Answer: NO. Every natural reading either fails to select Born, or is
circular (equivalent to assuming Born in the first place). This is a
negative result recorded honestly.

The analysis uses Sorkin I3, the third-order interference invariant:
  I3(A,B,C) = P(A ∪ B ∪ C) - P(A∪B) - P(A∪C) - P(B∪C) + P(A) + P(B) + P(C).
In quantum mechanics (Born), I3 = 0 identically (no third-order
interference). In genuine higher-order theories (e.g. cubic weights
|a|^3), I3 ≠ 0.

FOUR READINGS OF THE PRINCIPLE, ALL CRITICALLY EXAMINED.

Reading 1 — "absence of ternary facts" (weakest reading).
"No stable facticizable invariant lives only at the whole-context level."
  * Linear weights (|a|): PASS trivially. Linear probabilities have no
    cross-terms at all, so every 'fact' is a singleton, which is a
    special case of 'no ternary facts'. The principle holds.
  * Born weights (|a|^2): PASS. Born has only pairwise interference
    terms (2Re(a*b)); I3 = 0.
  * Cubic weights (|a|^3): FAIL. Genuine third-order interference.
  VERDICT: the principle distinguishes cubic from {linear, Born} but
  does NOT distinguish linear from Born. It does not select Born.

Reading 2 — "existence of pairwise facts" (stronger reading).
"Stable facts must reduce to pairwise witnesses (not singletons only)."
  * Linear: FAIL (all facts are singletons, no pairwise interference).
  * Born: PASS (2Re(a*b) is a pairwise fact).
  * Cubic: PASS or FAIL depending on whether cubic residue is ternary.
  VERDICT: this reading selects Born over linear, but it is CIRCULAR.
  'Existence of pairwise interference facts' is exactly the content of
  the Born rule itself. Postulating it is postulating Born.

Reading 3 — "pairwise comparison metric" (metricity reading).
"Stable distinguishability is pairwise metric comparison data."
  * An L2 metric D(a,b) = ⟨a,b⟩ yields ||a||^2 = ⟨a,a⟩ and hence Born.
  * An L1 metric D(a,b) = |a-b| yields ||a||_1 = |a| and hence linear.
  VERDICT: the principle is compatible with both L1 and L2 metrics.
  It does not select Born. To select Born, one must additionally
  postulate that the metric is L2 — which is postulating Born.

Reading 4 — "norm-preserving rotations" (orientation-overlap reading,
sections/175:675-707).
"Context transport composes by norm-preserving rotations."
  * L2-norm-preserving rotations are unitary maps; they select Born.
  * L1-norm-preserving 'rotations' are contractive maps; they select
    linear weights.
  VERDICT: 'norm-preserving' alone does not specify which norm. To
  select Born one must specify L2, which is postulating Born.

SYNTHESIS — the honest answer is NO.

Under every natural reading, the IDT principle "stable distinction is
pairwise comparison data" does not uniquely select Born:
  * Weak readings exclude cubic but admit linear (the principle is too
    weak).
  * Strong readings exclude linear but are equivalent to assuming Born
    (the principle is circular).
  * Metric/orientation readings are norm-agnostic and admit L1 alongside
    L2.

The principle is therefore not, by itself, a Born selector. The Born
wall is real at the level of the IDT primitive base as currently
conceived. To bridge the wall, the project must EITHER:
  (i) find a fifth reading that selects Born non-circularly (none has
      been identified despite four natural attempts);
  (ii) add a primitive that genuinely fixes the L2 norm without
      postulating it (e.g. a reconstruction-style postulate such as
      purification-uniqueness on the CDP pattern, see the 2026-07-21
      literature-grounding block earlier in this file);
  (iii) accept that Born is a sector law, not a derived theorem — the
      'sector perspective' of sections/175:182-198 — and stop claiming
      derivation.

This is a NEGATIVE result. It does not upgrade or downgrade the closure
verdict. The verdict remains CONDITIONAL_PACKAGE_ARTIFACTS_REGISTERED
(proved=5, conditional=16, missing=0). The new ledger entries below are
True-recorded documentation of a hand-analysis result; they do not
prove physics in Lean.

CONSEQUENCE FOR THE PUBLIC SURFACE.

The prose in sections/175:30-36 and the "no hidden context-only fact
=> S2 => Born" implication chain should be read as a CONDITIONAL
research route, not as a derivation. The route's first implication
("no hidden context-only fact => no stable primitive I3") is correct
only under the weak reading that does NOT exclude linear. The chain
does not reach Born without an additional, non-circular L2-fixing
postulate that has not been supplied.

The IDT project can still be honest and useful as a candidate
reconstruction framework, but the specific claim "IDT primitives
derive Born" is not supported by the current analysis. The CDP
reconstruction remains the only published finite-dimensional Born
derivation known; reproducing it (or any equivalent) inside IDT would
require importing its purification-uniqueness postulate, which would
no longer be 'context-first only'.
-/

def idt_principle_does_not_select_born_under_natural_readings : Prop :=
  -- Hand analysis over Sorkin I3 and L1/L2 metric alternatives shows
  -- every natural reading of the IDT principle either admits linear
  -- (too weak) or is equivalent to assuming Born (circular). The
  -- principle does not by itself select Born. Negative result.
  True

theorem idt_principle_for_born_is_not_a_non_circular_selector :
    idt_principle_does_not_select_born_under_natural_readings := by
  trivial

/-!
Finite operational primitive countermodel matrix (2026-07-24).

This block replaces the earlier bag-of-Prop pattern with concrete finite
carriers and exact arithmetic. It does not prove Born, Hilbert-space
uniqueness, purification uniqueness, or full QM. The results are deliberately
small:

* a balanced linear mixer uniformly rescales quadratic weight but cannot
  uniformly rescale linear weight even on two explicit inputs;
* a classical pure joint state cannot purify the explicit mixed bit;
* a quadratic bipartite amplitude has an explicit mixed marginal witness;
* standard observable-dimension counts pass for complex composites and fail
  for real and quaternionic qubit composites;
* a square-bit composite passes the dimension-count gate, showing that this
  gate alone does not select quantum theory.
-/

namespace FiniteOperationalPrimitiveMatrix

structure SignedPair where
  left : Int
  right : Int
deriving DecidableEq, Repr

def balancedMixer (value : SignedPair) : SignedPair :=
  ⟨value.left + value.right, value.left - value.right⟩

def doublePair (value : SignedPair) : SignedPair :=
  ⟨2 * value.left, 2 * value.right⟩

def linearWeight (value : SignedPair) : Nat :=
  value.left.natAbs + value.right.natAbs

def quadraticWeight (value : SignedPair) : Int :=
  value.left * value.left + value.right * value.right

def basisLeft : SignedPair := ⟨1, 0⟩

def diagonal : SignedPair := ⟨1, 1⟩

theorem balanced_mixer_squared_on_samples :
    balancedMixer (balancedMixer basisLeft) = doublePair basisLeft
      ∧ balancedMixer (balancedMixer diagonal) = doublePair diagonal := by
  decide

theorem balanced_mixer_uniformly_scales_quadratic_samples :
    quadraticWeight (balancedMixer basisLeft) = 2 * quadraticWeight basisLeft
      ∧ quadraticWeight (balancedMixer diagonal) =
        2 * quadraticWeight diagonal := by
  decide

/-- Cross-multiplication proves that the two linear-weight scale ratios differ. -/
theorem balanced_mixer_linear_sample_scalings_disagree :
    linearWeight (balancedMixer basisLeft) * linearWeight diagonal ≠
      linearWeight (balancedMixer diagonal) * linearWeight basisLeft := by
  decide

/-- Real dimension of the unnormalised observable space. -/
def realObservableDim (levels : Nat) : Nat :=
  levels * (levels + 1) / 2

/-- Complex dimension of the unnormalised observable space. -/
def complexObservableDim (levels : Nat) : Nat :=
  levels * levels

/-- Quaternionic dimension of the unnormalised observable space. -/
def quaternionicObservableDim (levels : Nat) : Nat :=
  levels * (2 * levels - 1)

def classicalObservableDim (levels : Nat) : Nat :=
  levels

def LocallyTomographicDimensionAt
    (dimension : Nat → Nat)
    (leftLevels rightLevels : Nat) : Prop :=
  dimension (leftLevels * rightLevels) =
    dimension leftLevels * dimension rightLevels

theorem classical_qubit_composite_passes_local_tomography_dimension :
    LocallyTomographicDimensionAt classicalObservableDim 2 2 := by
  change 4 = 4
  rfl

theorem complex_qubit_composite_passes_local_tomography_dimension :
    LocallyTomographicDimensionAt complexObservableDim 2 2 := by
  change 16 = 16
  rfl

theorem real_qubit_composite_fails_local_tomography_dimension :
    ¬ LocallyTomographicDimensionAt realObservableDim 2 2 := by
  change ¬ (10 = 9)
  decide

theorem quaternionic_qubit_composite_fails_local_tomography_dimension :
    ¬ LocallyTomographicDimensionAt quaternionicObservableDim 2 2 := by
  change ¬ (28 = 36)
  decide

inductive SquareBitPure where
  | positivePositive
  | positiveNegative
  | negativePositive
  | negativeNegative
deriving DecidableEq, Repr

def squareBitCoordinates : SquareBitPure → Int × Int
  | .positivePositive => (1, 1)
  | .positiveNegative => (1, -1)
  | .negativePositive => (-1, 1)
  | .negativeNegative => (-1, -1)

theorem square_bit_vertices_are_distinct :
    List.Nodup
      [ squareBitCoordinates .positivePositive,
        squareBitCoordinates .positiveNegative,
        squareBitCoordinates .negativePositive,
        squareBitCoordinates .negativeNegative ] := by
  decide

def squareBitLocalObservableDim : Nat := 3

def squareBitMaxCompositeObservableDim : Nat := 9

theorem square_bit_passes_dimension_count_gate :
    squareBitMaxCompositeObservableDim =
      squareBitLocalObservableDim * squareBitLocalObservableDim := by
  rfl

structure BitWeights where
  zero : Nat
  one : Nat
deriving DecidableEq, Repr

def mixedBitWeights : BitWeights := ⟨1, 1⟩

inductive ClassicalPureJoint where
  | zeroZero
  | zeroOne
  | oneZero
  | oneOne
deriving DecidableEq, Repr

def classicalFirstMarginal : ClassicalPureJoint → BitWeights
  | .zeroZero => ⟨2, 0⟩
  | .zeroOne => ⟨2, 0⟩
  | .oneZero => ⟨0, 2⟩
  | .oneOne => ⟨0, 2⟩

theorem classical_pure_joint_cannot_purify_mixed_bit :
    ∀ joint : ClassicalPureJoint,
      classicalFirstMarginal joint ≠ mixedBitWeights := by
  intro joint
  cases joint <;> decide

structure NatAmplitude2x2 where
  a00 : Nat
  a01 : Nat
  a10 : Nat
  a11 : Nat
deriving DecidableEq, Repr

def quadraticFirstMarginal (amplitude : NatAmplitude2x2) : BitWeights :=
  ⟨amplitude.a00 * amplitude.a00 + amplitude.a01 * amplitude.a01,
   amplitude.a10 * amplitude.a10 + amplitude.a11 * amplitude.a11⟩

def bellLikeAmplitude : NatAmplitude2x2 :=
  ⟨1, 0, 0, 1⟩

def crossBellLikeAmplitude : NatAmplitude2x2 :=
  ⟨0, 1, 1, 0⟩

def swapEnvironment (amplitude : NatAmplitude2x2) : NatAmplitude2x2 :=
  ⟨amplitude.a01, amplitude.a00, amplitude.a11, amplitude.a10⟩

theorem bell_like_amplitude_has_mixed_quadratic_marginal :
    quadraticFirstMarginal bellLikeAmplitude = mixedBitWeights := by
  rfl

theorem cross_bell_like_amplitude_has_mixed_quadratic_marginal :
    quadraticFirstMarginal crossBellLikeAmplitude = mixedBitWeights := by
  rfl

theorem finite_purification_witnesses_are_related_by_environment_swap :
    swapEnvironment bellLikeAmplitude = crossBellLikeAmplitude := by
  rfl

inductive FinitePrimitiveMatrixFinding where
  | quadraticMixerHasUniformScale
  | linearMixerHasNoUniformScale
  | classicalPureJointFailsMixedPurification
  | quadraticAmplitudeHasFinitePurificationWitness
  | complexCompositePassesDimensionGate
  | realAndQuaternionicCompositesFailDimensionGate
  | squareBitAlsoPassesDimensionGate
deriving DecidableEq, Repr

def finitePrimitiveMatrixFindings : List FinitePrimitiveMatrixFinding :=
  [ .quadraticMixerHasUniformScale,
    .linearMixerHasNoUniformScale,
    .classicalPureJointFailsMixedPurification,
    .quadraticAmplitudeHasFinitePurificationWitness,
    .complexCompositePassesDimensionGate,
    .realAndQuaternionicCompositesFailDimensionGate,
    .squareBitAlsoPassesDimensionGate ]

theorem finite_primitive_matrix_finding_count :
    finitePrimitiveMatrixFindings.length = 7 := by
  rfl

inductive FinitePrimitiveMatrixOpenObligation where
  | deriveAffineOperationalCarrierWithoutAmplitudeImport
  | proveUniversalPurificationAndUniqueness
  | excludeSpinFactorsAndExceptionalJordanModels
  | liftFiniteTomographyToGaugeCompatibleComposition
  | deriveComplexBornReadoutWithoutTargetImports
deriving DecidableEq, Repr

def finitePrimitiveMatrixOpenObligations :
    List FinitePrimitiveMatrixOpenObligation :=
  [ .deriveAffineOperationalCarrierWithoutAmplitudeImport,
    .proveUniversalPurificationAndUniqueness,
    .excludeSpinFactorsAndExceptionalJordanModels,
    .liftFiniteTomographyToGaugeCompatibleComposition,
    .deriveComplexBornReadoutWithoutTargetImports ]

theorem finite_primitive_matrix_open_obligation_count :
    finitePrimitiveMatrixOpenObligations.length = 5 := by
  rfl

end FiniteOperationalPrimitiveMatrix

/-- The finite matrix is a real research advance but does not close exact QM. -/
def finiteOperationalPrimitiveMatrixResearchStatus : QmResearchTaskStatus :=
  QmResearchTaskStatus.blocked

theorem finite_operational_primitive_matrix_keeps_exact_qm_blocked :
    finiteOperationalPrimitiveMatrixResearchStatus =
      QmResearchTaskStatus.blocked := by
  rfl

def finiteOperationalPrimitiveMatrixClaimBoundary : String :=
  "finite countermodel evidence; does not derive Born, Hilbert, or full QM"

/-!
Jordan/spin-factor primitive probe (2026-07-24).

This pass checks the remaining division-algebra qubit family with exact finite
dimension arithmetic. It does not assume or prove the classification of all
homogeneous self-dual cones. The machine-checked result is narrower:

* real, complex, and quaternionic qubits have the same single-system observable
  dimensions as spin factors with ball dimensions 2, 3, and 5;
* the stabilizer-dimension gate selects the complex candidate inside this
  three-member family only;
* standard composite observable dimensions fail the local-product dimension
  gate for real and quaternionic qubits and pass for the complex qubit;
* the earlier square-bit witness still passes the dimension-count gate, so the
  result is not a uniqueness proof over all operational theories;
* universal purification, exceptional Jordan composites, and gauge-compatible
  composition remain open.
-/

namespace JordanSpinFactorProbe

open FiniteOperationalPrimitiveMatrix

/-- A spin factor with ball dimension `d` has an observable space of dimension `d + 1`. -/
def spinFactorObservableDim (ballDim : Nat) : Nat :=
  ballDim + 1

inductive DivisionAlgebraQubit where
  | real
  | complex
  | quaternionic
deriving DecidableEq, Repr

def DivisionAlgebraQubit.ballDim : DivisionAlgebraQubit → Nat
  | .real => 2
  | .complex => 3
  | .quaternionic => 5

def DivisionAlgebraQubit.observableDim
    (candidate : DivisionAlgebraQubit) : Nat :=
  spinFactorObservableDim candidate.ballDim

/-- Dimension of the connected stabilizer `SO(d-1)` at one pure-state axis. -/
def spinFactorAxisStabilizerDim (ballDim : Nat) : Nat :=
  (ballDim - 1) * (ballDim - 2) / 2

def DivisionAlgebraQubit.phaseStabilizerDim
    (candidate : DivisionAlgebraQubit) : Nat :=
  spinFactorAxisStabilizerDim candidate.ballDim

theorem matrix_qubits_match_spin_factor_observable_dimensions :
    realObservableDim 2 = spinFactorObservableDim 2
      ∧ complexObservableDim 2 = spinFactorObservableDim 3
      ∧ quaternionicObservableDim 2 = spinFactorObservableDim 5 := by
  decide

theorem division_algebra_qubit_phase_stabilizer_dimensions :
    DivisionAlgebraQubit.real.phaseStabilizerDim = 0
      ∧ DivisionAlgebraQubit.complex.phaseStabilizerDim = 1
      ∧ DivisionAlgebraQubit.quaternionic.phaseStabilizerDim = 6 := by
  decide

theorem one_dimensional_phase_stabilizer_selects_complex_within_family :
    ∀ candidate : DivisionAlgebraQubit,
      candidate.phaseStabilizerDim = 1 ↔
        candidate = DivisionAlgebraQubit.complex := by
  intro candidate
  cases candidate <;> decide

def spinFactorLocallyTomographicCompositeDim (ballDim : Nat) : Nat :=
  spinFactorObservableDim ballDim * spinFactorObservableDim ballDim

theorem standard_qubit_composite_dimension_probe :
    realObservableDim 4 ≠ spinFactorLocallyTomographicCompositeDim 2
      ∧ complexObservableDim 4 = spinFactorLocallyTomographicCompositeDim 3
      ∧ quaternionicObservableDim 4 ≠
        spinFactorLocallyTomographicCompositeDim 5 := by
  decide

theorem standard_qubit_composite_dimension_values :
    realObservableDim 4 = 10
      ∧ spinFactorLocallyTomographicCompositeDim 2 = 9
      ∧ complexObservableDim 4 = 16
      ∧ spinFactorLocallyTomographicCompositeDim 3 = 16
      ∧ quaternionicObservableDim 4 = 28
      ∧ spinFactorLocallyTomographicCompositeDim 5 = 36 := by
  decide

/-- Observable dimension of the exceptional Albert algebra `H₃(O)`. -/
def exceptionalJordanObservableDim : Nat := 27

def exceptionalJordanLocallyTomographicCompositeBurden : Nat :=
  exceptionalJordanObservableDim * exceptionalJordanObservableDim

theorem exceptional_jordan_local_composite_burden_is_729 :
    exceptionalJordanLocallyTomographicCompositeBurden = 729 := by
  rfl

inductive JordanSpinFactorFinding where
  | matrixQubitsMatchSpinFactorDimensions
  | phaseDimensionSelectsComplexOnlyWithinRCHFamily
  | standardCompositeDimensionsRejectRealAndQuaternionic
  | squareBitPreventsDimensionGateUniqueness
  | exceptionalJordanCompositeRemainsOpen
deriving DecidableEq, Repr

def jordanSpinFactorFindings : List JordanSpinFactorFinding :=
  [ .matrixQubitsMatchSpinFactorDimensions,
    .phaseDimensionSelectsComplexOnlyWithinRCHFamily,
    .standardCompositeDimensionsRejectRealAndQuaternionic,
    .squareBitPreventsDimensionGateUniqueness,
    .exceptionalJordanCompositeRemainsOpen ]

theorem jordan_spin_factor_finding_count :
    jordanSpinFactorFindings.length = 5 := by
  rfl

inductive JordanSpinFactorOpenObligation where
  | proveOrRefuteUniversalSpinFactorPurification
  | constructSquareBitPhaseGroupAndPurificationProbe
  | classifyExceptionalJordanCompositeCompatibility
  | deriveCompositeRuleWithoutTargetTensorImport
  | scopeTomographyAcrossGaugeSuperselectionSectors
  | deriveBornPairingFromOperationalPrimitives
deriving DecidableEq, Repr

def jordanSpinFactorOpenObligations : List JordanSpinFactorOpenObligation :=
  [ .proveOrRefuteUniversalSpinFactorPurification,
    .constructSquareBitPhaseGroupAndPurificationProbe,
    .classifyExceptionalJordanCompositeCompatibility,
    .deriveCompositeRuleWithoutTargetTensorImport,
    .scopeTomographyAcrossGaugeSuperselectionSectors,
    .deriveBornPairingFromOperationalPrimitives ]

theorem jordan_spin_factor_open_obligation_count :
    jordanSpinFactorOpenObligations.length = 6 := by
  rfl

end JordanSpinFactorProbe

/-- Single-system and dimension gates do not yet isolate complex QM globally. -/
def jordanSpinFactorPrimitiveSearchStatus : QmResearchTaskStatus :=
  QmResearchTaskStatus.blocked

theorem jordan_spin_factor_probe_keeps_exact_qm_blocked :
    jordanSpinFactorPrimitiveSearchStatus = QmResearchTaskStatus.blocked := by
  rfl

def jordanSpinFactorClaimBoundary : String :=
  "complex selected only inside the R/C/H qubit family; all-GPT uniqueness remains open"

/-!
Square-bit purification and phase probe (2026-07-24).

The purification principle used here requires every mixed state to be the
marginal of a pure bipartite state, with purifications unique up to reversible
environment dynamics (Chiribella--D'Ariano--Perinotti, arXiv:0908.1583).
The standard `(2,2,2)` no-signalling polytope has 24 extremal states: 16 local
deterministic vertices and 8 PR vertices (Bierhorst, arXiv:1511.04127).

This finite probe imports that 24-vertex classification as its model boundary;
it does not derive the classification from IDT primitives. It proves that a
noncentral square-bit mixture has no pure-state marginal witness inside this
standard maximal same-system composite. It also proves that the stabilizer of
one coordinate effect inside all signed-coordinate square symmetries has only
two elements. Neither result excludes an exotic composite or a larger
purifying environment without an additional composite-independence theorem.
-/

namespace SquareBitPurificationPhaseProbe

open FiniteOperationalPrimitiveMatrix

abbrev SquareBitState := Int × Int

def addSquareBitStates (left right : SquareBitState) : SquareBitState :=
  (left.1 + right.1, left.2 + right.2)

def doubleSquareBitState (state : SquareBitState) : SquareBitState :=
  (2 * state.1, 2 * state.2)

/-- The midpoint of the right edge of the normalized square state space. -/
def squareBitRightEdgeMidpoint : SquareBitState :=
  (1, 0)

/-- Integer arithmetic records the exact half-half convex-mixture witness. -/
theorem square_bit_right_edge_midpoint_has_exact_mixture_witness :
    doubleSquareBitState squareBitRightEdgeMidpoint =
      addSquareBitStates
        (squareBitCoordinates .positivePositive)
        (squareBitCoordinates .positiveNegative) := by
  decide

inductive SquareBitMaxPureJoint where
  | localDeterministic (left right : SquareBitPure)
  | pr (label : Fin 8)
deriving DecidableEq, Repr

/-- Four local vertices on each side give 16 local deterministic extremes. -/
def squareBitMaxLocalDeterministicCount : Nat :=
  4 * 4

/-- The `(2,2,2)` maximal no-signalling polytope has eight PR extremes. -/
def squareBitMaxPrCount : Nat :=
  8

def squareBitMaxPureJointCount : Nat :=
  squareBitMaxLocalDeterministicCount + squareBitMaxPrCount

theorem square_bit_maximal_composite_has_24_modelled_extremes :
    squareBitMaxLocalDeterministicCount = 16
      ∧ squareBitMaxPrCount = 8
      ∧ squareBitMaxPureJointCount = 24 := by
  decide

/-- Local deterministic extremes have pure marginals; PR extremes are unbiased. -/
def squareBitMaxPureFirstMarginal : SquareBitMaxPureJoint → SquareBitState
  | .localDeterministic left _ => squareBitCoordinates left
  | .pr _ => (0, 0)

/--
The standard maximal same-square composite cannot purify the noncentral edge
mixture: no one of its 24 extremal states has that first marginal.
-/
theorem square_bit_maximal_pure_states_cannot_purify_right_edge_midpoint :
    ∀ joint : SquareBitMaxPureJoint,
      squareBitMaxPureFirstMarginal joint ≠ squareBitRightEdgeMidpoint := by
  intro joint
  cases joint with
  | localDeterministic left right =>
      cases left <;>
        simp [squareBitMaxPureFirstMarginal, squareBitRightEdgeMidpoint,
          squareBitCoordinates]
  | pr label =>
      simp [squareBitMaxPureFirstMarginal, squareBitRightEdgeMidpoint]

structure SquareBitSignedSymmetry where
  swapAxes : Bool
  flipFirst : Bool
  flipSecond : Bool
deriving DecidableEq, Repr

def signedSquareBitCoordinate (flip : Bool) (coordinate : Int) : Int :=
  if flip then -coordinate else coordinate

/-- The full eight-element family of signed coordinate permutations of a square. -/
def applySquareBitSignedSymmetry
    (symmetry : SquareBitSignedSymmetry)
    (state : SquareBitState) : SquareBitState :=
  let permuted := if symmetry.swapAxes then (state.2, state.1) else state
  ( signedSquareBitCoordinate symmetry.flipFirst permuted.1,
    signedSquareBitCoordinate symmetry.flipSecond permuted.2 )

/-- Preservation of the first coordinate effect, checked on all four pure vertices. -/
def PreservesFirstSquareBitEffect
    (symmetry : SquareBitSignedSymmetry) : Prop :=
  (applySquareBitSignedSymmetry symmetry
      (squareBitCoordinates .positivePositive)).1 = 1
    ∧ (applySquareBitSignedSymmetry symmetry
      (squareBitCoordinates .positiveNegative)).1 = 1
    ∧ (applySquareBitSignedSymmetry symmetry
      (squareBitCoordinates .negativePositive)).1 = -1
    ∧ (applySquareBitSignedSymmetry symmetry
      (squareBitCoordinates .negativeNegative)).1 = -1

/-- Only no axis swap and no first-coordinate flip preserve the first effect. -/
theorem square_bit_first_effect_stabilizer_classification
    (symmetry : SquareBitSignedSymmetry) :
    PreservesFirstSquareBitEffect symmetry ↔
      symmetry.swapAxes = false ∧ symmetry.flipFirst = false := by
  cases symmetry with
  | mk swapAxes flipFirst flipSecond =>
      cases swapAxes <;> cases flipFirst <;> cases flipSecond <;>
        simp [PreservesFirstSquareBitEffect, applySquareBitSignedSymmetry,
          signedSquareBitCoordinate, squareBitCoordinates]

def squareBitPhaseIdentity : SquareBitSignedSymmetry :=
  ⟨false, false, false⟩

def squareBitPhaseFlipSecond : SquareBitSignedSymmetry :=
  ⟨false, false, true⟩

def squareBitFirstEffectStabilizer : List SquareBitSignedSymmetry :=
  [squareBitPhaseIdentity, squareBitPhaseFlipSecond]

theorem square_bit_first_effect_stabilizer_is_exactly_two_elements
    (symmetry : SquareBitSignedSymmetry) :
    PreservesFirstSquareBitEffect symmetry ↔
      symmetry = squareBitPhaseIdentity ∨
        symmetry = squareBitPhaseFlipSecond := by
  cases symmetry with
  | mk swapAxes flipFirst flipSecond =>
      cases swapAxes <;> cases flipFirst <;> cases flipSecond <;>
        simp [PreservesFirstSquareBitEffect, applySquareBitSignedSymmetry,
          signedSquareBitCoordinate, squareBitCoordinates,
          squareBitPhaseIdentity, squareBitPhaseFlipSecond]

theorem square_bit_first_effect_stabilizer_order_is_two :
    squareBitFirstEffectStabilizer.length = 2
      ∧ squareBitFirstEffectStabilizer.Nodup := by
  decide

inductive SquareBitPurificationPhaseFinding where
  | noncentralStateHasExactMixtureWitness
  | standardMaximalCompositeHas24Extremes
  | standardMaximalPureMarginalsExcludeEdgeMidpoint
  | firstEffectStabilizerIsFiniteOrderTwo
  | arbitraryEnvironmentExclusionRemainsOpen
deriving DecidableEq, Repr

def squareBitPurificationPhaseFindings :
    List SquareBitPurificationPhaseFinding :=
  [ .noncentralStateHasExactMixtureWitness,
    .standardMaximalCompositeHas24Extremes,
    .standardMaximalPureMarginalsExcludeEdgeMidpoint,
    .firstEffectStabilizerIsFiniteOrderTwo,
    .arbitraryEnvironmentExclusionRemainsOpen ]

theorem square_bit_purification_phase_finding_count :
    squareBitPurificationPhaseFindings.length = 5 := by
  rfl

inductive SquareBitPurificationPhaseOpenObligation where
  | excludePurificationByArbitraryEnvironmentTypes
  | proveCompositeIndependentSquareBitNoPurification
  | deriveContinuousOneDimensionalPhaseRequirement
  | proveOrRefuteUniversalNonComplexSpinFactorPurification
deriving DecidableEq, Repr

def squareBitPurificationPhaseOpenObligations :
    List SquareBitPurificationPhaseOpenObligation :=
  [ .excludePurificationByArbitraryEnvironmentTypes,
    .proveCompositeIndependentSquareBitNoPurification,
    .deriveContinuousOneDimensionalPhaseRequirement,
    .proveOrRefuteUniversalNonComplexSpinFactorPurification ]

theorem square_bit_purification_phase_open_obligation_count :
    squareBitPurificationPhaseOpenObligations.length = 4 := by
  rfl

end SquareBitPurificationPhaseProbe

/-- The standard square-bit model fails the probe, but global exclusion is open. -/
def squareBitPurificationPhaseResearchStatus : QmResearchTaskStatus :=
  QmResearchTaskStatus.blocked

theorem square_bit_purification_phase_probe_keeps_exact_qm_blocked :
    squareBitPurificationPhaseResearchStatus = QmResearchTaskStatus.blocked := by
  rfl

def squareBitPurificationPhaseClaimBoundary : String :=
  "finite rejection of the standard maximal same-square composite; not a composite-independent square-bit no-go theorem"

end V8
end MetaLang
end IDT
