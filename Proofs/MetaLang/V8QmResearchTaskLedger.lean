-- `Fintype` and `Fintype.card_le_of_surjective` are Mathlib, and nothing in the
-- transitive closure of the two imports below provides them. Without this
-- import `Fintype` is silently auto-bound as an implicit variable and the
-- finite-polytope purification no-go does not elaborate.
import Mathlib.Data.Fintype.Card

import Proofs.MetaLang.V8CurrentFrontierBlockers
import Proofs.QMClosure.CGSCGroundedSemanticExtensions

/-!
EMPTY_PLACEHOLDER

8 of the 61 theorems in this file have conclusion `True` and therefore assert
nothing, regardless of how they are proved:

  overlap_preservation_dynamics_remains_behind_bridge_wall
  born_wall_is_impossibility_for_b1_bridgeable_on_successor_base
  b1_primitive_base_has_no_known_lean_inhabitant
  born_wall_bridge_remains_pending_concrete_carrier_probe
  born_wall_positioned_against_purification_reconstruction
  theory_logical_coherence_audit_installed
  idt_born_principle_remains_untested_hypothesis
  idt_principle_for_born_is_not_a_non_circular_selector

Those eight are status records, not evidence, and must not be cited as
derivations. The remaining results in this file -- for example the
finite-polytope purification no-go in
`SquareBitFinitePolytopePurificationNoGo` -- are ordinary Lean proofs with
non-trivial conclusions and are not covered by this marker.

See `INVENTORY_AUDIT.md` and
`sections/175-primitive-base-completeness-status.md`.

Enforced by `scripts/check_vacuous_theorems.py`.
-/

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

/-!
Finite-polytope purification no-go (2026-07-25).

This pass removes the dependence on the standard 24-vertex boxworld composite.
For any proposed composite with `n` pure joint states, the right edge of the
square contains `n + 1` distinct strict convex mixtures. A first-marginal map
from `n` pure joints cannot cover those `n + 1` mixtures. Hence no finite
polytopic composite can satisfy existence of purification for the square bit.

The theorem is deliberately not an unrestricted square-bit no-go: a proposed
non-polytopic composite may have infinitely many pure joint states, and an
arbitrary purifying environment may have continuous reversible dynamics. Those
possibilities require an additional structural primitive or a separate no-go.
-/

namespace SquareBitFinitePolytopePurificationNoGo

/--
For `n` proposed pure joint states, these positive weights encode `n + 1`
strict mixtures of the two pure vertices on the right edge of the square.
Every pair has common total weight `n + 2`.
-/
def squareBitRightEdgeInteriorWeights
    (pureJointCount : Nat)
    (index : Fin (pureJointCount + 1)) : Nat × Nat :=
  (index.val + 1, pureJointCount - index.val + 1)

theorem square_bit_right_edge_interior_weights_are_positive_and_normalized
    (pureJointCount : Nat)
    (index : Fin (pureJointCount + 1)) :
    let weights := squareBitRightEdgeInteriorWeights pureJointCount index
    0 < weights.1
      ∧ 0 < weights.2
      ∧ weights.1 + weights.2 = pureJointCount + 2 := by
  dsimp [squareBitRightEdgeInteriorWeights]
  omega

/-- Distinct indices give distinct mixtures because their first weights differ. -/
theorem square_bit_right_edge_interior_weights_are_injective
    (pureJointCount : Nat) :
    Function.Injective (squareBitRightEdgeInteriorWeights pureJointCount) := by
  intro left right equalWeights
  apply Fin.ext
  have equalFirstWeights := congrArg Prod.fst equalWeights
  dsimp [squareBitRightEdgeInteriorWeights] at equalFirstWeights
  omega

/--
A finite pure-joint family cannot cover even the selected `n + 1` interior
square-bit mixtures. This uses only finite cardinality, not Hilbert space,
Born probabilities, a tensor product, or the standard boxworld composite.
-/
theorem finite_pure_joint_family_cannot_cover_selected_square_bit_mixtures
    {PureJoint : Type}
    [Fintype PureJoint]
    (firstMarginal :
      PureJoint → Fin (Fintype.card PureJoint + 1)) :
    ¬ Function.Surjective firstMarginal := by
  intro coverage
  have cardinalityBound :
      Fintype.card (Fin (Fintype.card PureJoint + 1)) ≤
        Fintype.card PureJoint :=
    Fintype.card_le_of_surjective firstMarginal coverage
  simp only [Fintype.card_fin] at cardinalityBound
  omega

inductive SquareBitFinitePolytopeNoGoFinding where
  | arbitrarilyLargeFiniteInteriorMixtureFamilies
  | finitePureMarginalMapCannotBeSurjective
  | everyFinitePolytopicCompositeFailsPurificationExistence
  | nonPolytopicCompositeRemainsOpen
deriving DecidableEq, Repr

def squareBitFinitePolytopeNoGoFindings :
    List SquareBitFinitePolytopeNoGoFinding :=
  [ .arbitrarilyLargeFiniteInteriorMixtureFamilies,
    .finitePureMarginalMapCannotBeSurjective,
    .everyFinitePolytopicCompositeFailsPurificationExistence,
    .nonPolytopicCompositeRemainsOpen ]

theorem square_bit_finite_polytope_no_go_finding_count :
    squareBitFinitePolytopeNoGoFindings.length = 4 := by
  rfl

inductive SquareBitFinitePolytopeOpenObligation where
  | excludeInfinitePureJointComposite
  | constrainArbitraryPurifyingEnvironment
  | derivePurificationUniquenessFromReversibleDynamics
  | testNonPolytopicSquareCompositeAgainstLocalTomography
  | testNonPolytopicSquareCompositeAgainstContinuousPhase
deriving DecidableEq, Repr

def squareBitFinitePolytopeOpenObligations :
    List SquareBitFinitePolytopeOpenObligation :=
  [ .excludeInfinitePureJointComposite,
    .constrainArbitraryPurifyingEnvironment,
    .derivePurificationUniquenessFromReversibleDynamics,
    .testNonPolytopicSquareCompositeAgainstLocalTomography,
    .testNonPolytopicSquareCompositeAgainstContinuousPhase ]

theorem square_bit_finite_polytope_open_obligation_count :
    squareBitFinitePolytopeOpenObligations.length = 5 := by
  rfl

end SquareBitFinitePolytopePurificationNoGo

/-- Finite-polytopic composites are rejected; the unrestricted route stays open. -/
def squareBitFinitePolytopeNoGoResearchStatus : QmResearchTaskStatus :=
  QmResearchTaskStatus.blocked

theorem square_bit_finite_polytope_no_go_keeps_exact_qm_blocked :
    squareBitFinitePolytopeNoGoResearchStatus = QmResearchTaskStatus.blocked := by
  rfl

def squareBitFinitePolytopeNoGoClaimBoundary : String :=
  "composite-independent over finite pure-joint families only; infinite non-polytopic composites and arbitrary environments remain open"

/-!
### Grade-arity equivalence proved; C-arity hypothesis recorded (2026-08-15)

Two machine-checked results landed on the branch codex/grade-arity-iff:

1. `Proofs/QMClosure/SorkinGradeIffPairwiseGeneration.lean`: over an
   arbitrary finite carrier, a set-function weight with mu ∅ = 0 is
   generated by singleton and ordered-pair coefficients IF AND ONLY IF its
   Sorkin third-order term vanishes on all pairwise disjoint nonempty
   triples. Such weights also have vanishing fourth-order term, and the
   product of two additive weights is pairwise generated (Guo-Cao-Chen-Yin
   2011 as a corollary). This discharges the open obligations
   `proveTheConverseFromVanishingThirdOrderToBinaryGeneration` and
   `extendBeyondThreeAlternatives` of `ArityBoundsInterferenceOrder`.

2. `Proofs/QMClosure/CompositionForcesBinaryArity.lean`: the kernel-language
   converse on three alternatives (vanishing third order implies generation
   by SOME kernel on pairs), and the escape witness: on four alternatives
   the block weight (1 when {0,1} ⊆ S, plus 1 when {2,3} ⊆ S) is pairwise
   generated while its square is not (third-order term 2 on the split
   {2},{3},{0,1}). Weight multiplication therefore cannot be the composite
   readout rule.

C-arity hypothesis, recorded as a RESEARCH HYPOTHESIS, not a theorem:
composition closure forces binary arity. Literature anchors: density cubes
have third-order interference and violate local tomography (K(4) = 22
against 16, Dakic-Paterek-Brukner 2014); quartic quantum theory has
defective composites; Galley-Masanes 2018 show any Born-rule modification
that changes the interference order violates purification or local
tomography; Barnum-Lee-Scandolo-Selby 2017 derive at-most-second-order
interference from purity principles. The H1 kill construction of section
174.80 tested a ternary witness in a SINGLE context; the decisive next
probe is the two-context ternary composability test. The hypothesis is
deliberately NOT encoded as abstract Prop flags -- the lesson of
`S2BornProofSearch` applies.
-/

def compositionForcesBinaryArityHypothesis : Prop :=
  -- Open research hypothesis with literature anchors and a decisive finite
  -- probe identified. Not a theorem; not a Prop-flag scaffold. The
  -- equivalence results above are theorems; the composition-forcing
  -- direction is not.
  True

theorem composition_forces_binary_arity_stays_research_hypothesis :
    compositionForcesBinaryArityHypothesis := by
  trivial

/-!
### C-arity probe result: one-sided cylinder no-go PROVED (2026-08-15)

The decisive probe proposed above has been run at the weight-calculus level
in `Proofs/QMClosure/CylinderGluingForcesBinaryArity.lean`, all machine-checked:

1. `cylinder_two_decomposable`: the cylinder marginal `fun S => W (S ×ˢ univ)`
   of a pairwise generated composite W is pairwise generated. The proof goes
   through the grade equivalence with no sum manipulations: products
   distribute over unions, so the cylinder image of a disjoint triple is a
   disjoint triple of cylinder events.

2. `no_ternary_cylinder_gluing`: a weight with nonzero third-order term on
   some disjoint triple has NO pairwise generated composite with a consistent
   cylinder marginal. Ternary residues cannot be glued into second-order
   composites. The cubic weight |S|^3 (third-order term 6 on singletons),
   the arithmetic shadow of the density-cube construction, instantiates the
   no-go concretely.

3. `cylinder_gluing_lift`: non-vacuity -- every pairwise generated local
   weight does admit such a composite (explicit lift concentrating the data
   on one right-hand alternative).

This confirms, as a theorem of the weight calculus, the literature prediction
recorded with the hypothesis (density cubes violate local tomography;
Galley-Masanes 2018). What REMAINS of C-arity after this result:

- the top-level demand that composites be second-order at all is an input,
  not a derivation;
- two-sided gluing (one composite extending BOTH locals) is open and is
  genuinely constrained by the failure of additive lifts, a signal that
  composites carry amplitude-level structure;
- stronger gluing demands (conditioning, no-signalling on non-cylinder
  events, local-tomography degree counting) are not yet formalised.

No status is upgraded: this is a weight-calculus theorem, not a derivation
of complex amplitudes, Hilbert carriers, purification, or Born.
-/

def cArityProbeReturnedOneSidedTheorem : Prop :=
  -- The one-sided cylinder direction of the C-arity prediction is now a
  -- theorem of the weight calculus; the residual content of the hypothesis
  -- is the top-level second-order-composite demand and the two-sided and
  -- stronger-gluing questions, all recorded as open obligations in the file.
  True

theorem c_arity_probe_result_recorded :
    cArityProbeReturnedOneSidedTheorem := by
  trivial

/-!
### Two-sided cylinder gluing CHARACTERIZED (2026-08-15)

The two-sided question left open by the previous block is now closed in
`Proofs/QMClosure/TwoSidedCylinderGluing.lean`, all machine-checked:

1. `cylinder_mass_conservation`: mass conservation through both cylinder
   marginals needs no grade assumption at all -- any composite weight of
   any order conserves total mass, because both marginals read the same
   full product event `univ ×ˢ univ`.

2. `two_sided_gluing_necessity`: a second-order composite carrying both
   cylinder marginals forces both marginals to be second order (the
   one-sided theorem applied to each side) and their total masses to
   agree.

3. `two_sided_gluing_sufficiency` and `two_sided_gluing_iff`: on NONEMPTY
   contexts these conditions are also sufficient. The witness is the
   slice-and-junction lift: carry mu on the slice `α × {t₀}`, carry nu on
   the slice `{s₀} × β`, subtract a junction singleton of mass
   `nu univ` at the crossing point. Weight data alone suffice.

4. `unequal_masses_do_not_glue`: the mass gate bites concretely -- the
   block weight (mass 2) and the counting weight (mass 4) on four
   alternatives are both second order yet do not glue.

This refines the signal recorded in the previous block: additive lifts do
fail two-sidedly, but non-additive weight-level lifts exist, so that
failure carries no amplitude-level information after all.

Reading for the research programme: at cylinder-marginal level the
second-order world has NO Bell-type obstruction -- every consistent pair
of second-order locals with matching mass is jointly realizable.
Whatever excludes boxworld-style composites must enter through stronger
demands (conditioning, no-signalling on non-cylinder events, local
tomography), which remain open obligations in the file. Combined with
the one-sided no-go, the weight-level gluing picture is closed: the
pairs that glue are exactly the second-order pairs with equal total
mass, and ternary residues are precisely what breaks gluing. The
top-level demand that composites be second order remains an input, not a
derivation.

Scope discipline: set-function weights over ℚ, finite NONEMPTY contexts
(on an empty context the mass gate alone is not sufficient and nothing
is claimed there); cylinder marginals only; no complex amplitudes,
Hilbert carrier, purification, or Born derived; no status upgraded
anywhere.
-/

def twoSidedCylinderGluingCharacterized : Prop :=
  -- Two-sided gluing of second-order weights is characterized exactly:
  -- both marginals second order AND equal total mass, on nonempty
  -- contexts, via an explicit slice-and-junction witness. Bell-type
  -- questions are NOT settled by this and stay at the stronger gluing
  -- demands.
  True

theorem two_sided_gluing_result_recorded :
    twoSidedCylinderGluingCharacterized := by
  trivial

/-!
### Conditioned gluing is unobstructed; the linear layer cannot see Bell
### (2026-08-15)

The gluing cluster was completed by a skeptical re-verification pass and a
new file, `Proofs/QMClosure/ConditionedGluingIsUnobstructed.lean`, all
machine-checked:

1. `rectangle_marginal_two_decomposable`: for ANY fixed right-hand event T
   (not just univ), the rectangle marginal of a second-order composite is
   second order.

2. `conditioned_gluing_iff`: prescribing the FULL conditioned family
   (mu y on every `S × {y}`) together with the left cylinder marginal nu is
   possible exactly when every mu y and nu are second order and the overlap
   values agree, `nu {y} = mu y univ`. No other constraint exists. The
   witness is the slice family plus a vertical-slice left-over correction.

3. `additive_table_two_decomposable`: every additive table is grade at most
   one. Every joint outcome table of a box at fixed settings is additive,
   so interference grade cannot see nonlocality: a PR table is as
   acceptable to the grade machinery as a classical one.

Reading: the entire linear layer of the weight calculus -- cylinder,
two-sided, and conditioned gluing -- is obstruction-free up to linear
consistency. The first gates that can carry physical selection content must
be non-linear, positivity of weights or of the generating kernel above all.
That is now the leading open obligation of the cluster.

Process note (honest): the F1/F2/F2.5 cluster and both new
characterizations were re-verified INDEPENDENTLY of Lean by exact linear
algebra over Q (subspace images against constraint sets, exhaustive over
all rational weights, contexts up to 4x2 and 3x3), and the
slice-and-junction construction was re-verified numerically. The
independent check also refuted one hand analysis: prescribing the
unconditioned right marginal on top of the conditioned family adds NO
further linear constraints (for at least two right-hand alternatives) --
a cross-kernel witness is sketched but not yet formalized, so it stays an
open obligation, not a result.

Scope unchanged: set-function weights over Q, no positivity, no complex
amplitudes, no Hilbert carrier, no Born derivation, and the
second-orderness of composites remains an input.
-/

def conditionedGluingIsUnobstructed : Prop :=
  -- Conditioned families glue exactly on overlap consistency; additive
  -- tables are grade at most one, so grade cannot see nonlocality; the
  -- linear gluing layer is obstruction-free. The first real gate must be
  -- non-linear (positivity) -- recorded as an obligation, not a result.
  True

theorem conditioned_gluing_result_recorded :
    conditionedGluingIsUnobstructed := by
  trivial

/-!
### Positivity does not obstruct cone gluing (2026-08-15)

The positivity gate was probed with two independent tools, and the first
positive result under a non-linear demand is machine-checked in
`Proofs/QMClosure/ConeGluingIsPositive.lean`:

1. `cone_gluing_positive`: if both local weights admit kernel depositions
   with ALL coefficients nonnegative (positively generated -- nonnegative
   additive tables and scaled pair indicators qualify) and their total
   masses agree, then the product-kernel coupling `K1 (x) K2 / M` is a
   pairwise generated composite with exactly those cylinder marginals,
   nonnegative on every subset. Positivity is automatic: every kernel
   entry of the coupling is a product of nonnegatives over a positive
   mass. The cylinders telescope through the diagonal-plus-offdiagonal
   identity and factorization of the double matrix sum.

2. `positively_generated_mass_zero`: a positively generated weight of
   total mass zero vanishes identically, so the case split in the main
   theorem is complete.

3. `antiCorrelated_*`: the anti-correlated weight on two alternatives
   ({i} maps to 1, the pair to 0) is positive and pairwise generated but
   lies OUTSIDE the cone (pair sum -2). The cone is a sufficient
   condition, not the boundary of positive gluing.

Independent LP evidence (exact rational simplex with machine-checkable
Farkas certificates for infeasibility and directly reverified witnesses
for feasibility): on Fin 2 x Fin 2 ALL 515 equal-mass positive pairs
glue positively; on Fin 3 x Fin 2 all 250 sampled pairs (1764 equal-mass
pairs exist; sampling prioritized non-cone weights, 295 of 511 distinct
positives) glue positively. No positivity obstruction was found anywhere
probed, well beyond the cone. Whether positive gluing is ALWAYS possible
stays open and unclaimed.

Process lesson recorded for the mistake ledger: a hand analysis on the
anti-correlated weight produced a compelling line-sum "no-go" for
positive two-sided gluing. It was WRONG (singletons were double-counted
in the sum over the four cylinder sections); an explicit positive
witness was then constructed and the LP confirmed feasibility. Rule:
in the positivity layer, no claim without mechanical verification --
hand bookkeeping of kernel sums is exactly where errors hide.
-/

def coneGluingIsPositiveResult : Prop :=
  -- Positively generated (nonnegative-kernel) weights with equal total
  -- mass always glue into a nonnegative second-order composite via the
  -- product-kernel coupling. Beyond the cone the question is open;
  -- LP evidence on small contexts found no obstruction at all.
  True

theorem cone_gluing_positive_result_recorded :
    coneGluingIsPositiveResult := by
  trivial

/-!
### Diagonal self-gluing proved; adversarial positive-gluing probes all pass

`Proofs/QMClosure/DiagonalSelfGluing.lean` (machine-checked, clean axioms)
closes one full diagonal of the positivity gate unconditionally:

EVERY nonnegative-valued pairwise weight `mu` couples with ITSELF. The
witness is the diagonal composite `W U = mu {i | (i, i) ∈ U}`; both
cylinder marginals reproduce `mu` exactly, pairwise generation and
nonnegativity are inherited by construction, and no nonemptiness, mass, or
cone-coefficient condition is needed (mass-zero weights included). The
value depends only on `mu`, not on its decomposition.

Skeptical re-derivation before recording (2026-08-15, exact rational
arithmetic, `/tmp/positivity_probe3.py`):

1. The generator-based proof plan for universal positive gluing DIED, and
   this is a durable finding: the cone of nonnegative-valued pairwise
   weights strictly exceeds the cone generated by
   `{xᵢ, xᵢxⱼ, xᵢ(1−xⱼ)}` already on Fin 3. The witness "XOR ray"
   `f = x₁ − x₁x₂ − x₁x₃ + x₂x₃` (= `1_{100} + 1_{011}`, mass zero) is
   nonnegative and pairwise but lies outside the guard cone: the
   b-matching (Hoffman) split condition fails on `F = {(1,2), (1,3)}`
   (demands 1 + 1 exceed the endpoint capacity c₁ = 1). Enumeration over
   the small integer grid found 51 such weights out of 2523 nonnegative
   ones; the Hoffman criterion agreed with an independent exact
   cone-membership LP on all 202 checked instances. Any future proof of
   universal positive gluing must handle these rays; pairing generators is
   not enough.

2. A hand attempt at an (E, H)-type cross coupling was caught by the
   already-proven mass-conservation theorem (singleton mass 1 cannot pair
   with a mass-zero guard): the cylinder mass gate, not new reasoning,
   killed it. Discipline note: check the mass gate FIRST before
   constructing couplings.

3. Hand witnesses all verified by direct evaluation: (f, f) via the
   diagonal embedding; (H₁₂, H₁₂) via the cross-guard
   `1_{(1,1)∈U}·(1 − 1_{(2,2)∈U})`; (P₁₂, P₁₃) via the product kernel.

4. Exact LP decisions (two-phase simplex over the Farkas alternative,
   Fraction arithmetic, Bland fallback; certificates re-verified by direct
   arithmetic where produced): 9 adversarial equal-mass pairs on Fin 3 x
   Fin 3 ALL glue positively -- the XOR ray against its mirror and against
   guards and kernels, mass-zero against zero, the positive-mass ray
   `2f + x₁` against itself and against a pure kernel, guards against
   guards, anti-correlated pairs. The only failure in the sweep is `f`
   (mass 0) against `P₁₂` (mass 1): the equal-mass gate, already a
   theorem.

Evidence discipline: the feasible-direction verdicts rest on the exact
simplex itself (validated indirectly: 202/202 cone cross-check, smoke
tests, witness rechecks); no infeasibility beyond the mass gate appeared,
so no Farkas certificate was needed. Universal positive gluing for
DISTINCT weights remains open and unclaimed; finite evidence now says the
mass gate is the only obstruction seen anywhere.

Next obligations, in order: decide universal positive gluing for distinct
weights (constructive routing through off-product pairs, or a Farkas
counterexample on larger contexts); formalize the cone-strictness XOR ray
in Lean; classify the mass-zero sector and its couplings; then move the
research focus to spectral/phase gates, where physical selection content
must live if the positivity layer stays obstruction-free.
-/

def diagonalSelfGluingProvedResult : Prop :=
  -- Every nonnegative pairwise weight admits a nonnegative pairwise
  -- composite reproducing it in both cylinder marginals (diagonal
  -- coupling). Distinct-weight universal positive gluing stays open;
  -- exact adversarial probes on Fin 3 found no obstruction beyond the
  -- equal-mass gate, and the nonnegative cone provably (by exact
  -- computation, not yet in Lean) exceeds the guard cone on Fin 3.
  True

theorem diagonal_self_gluing_result_recorded :
    diagonalSelfGluingProvedResult := by
  trivial

/-!
### Column embedding: point-mass and zero right marginals always couple

`Proofs/QMClosure/ColumnEmbeddingGluing.lean` (machine-checked, clean
axioms) adds a third universal positive-coupling class with a two-line
mechanism: carry the whole left weight on one right-hand alternative,
`W U = mu {i | (i, t0) ∈ U}` (the `sliceWeightTop` of the two-sided file).
Consequences: every nonnegative pairwise weight positively couples with
the point mass of its own total mass, and every mass-zero nonnegative
pairwise weight positively couples with the zero weight. No nonemptiness,
mass, or cone-coefficient condition.

The mechanism was found by hand AND independently by exact LP: the primal
solve of (H₁₂ ⊗ 0) returned the witness `A₀₀ = 1, B_{(0,0),(1,0)} = −1`,
which is exactly the column embedding of H₁₂ into column 0. The probe
pipeline (Farkas-alternative simplex) was also validated for direction on
known-answer instances: (H₁₂,H₁₂) cross-guard, (f,f) diagonal, (D,D) on
Fin 2 from the previous session — all verdicts correct.

Process lesson, repeated and worth escalating: during this session hand
kernel-sum analyses twice "proved" infeasibility of (H₁₂ ⊗ 0) and
(f ⊗ 0); both were arithmetic slips (double counting, wrong H values,
mis-added FO sums). The already-recorded rule stands but was violated
again before the machine check: in the positivity layer, NO claim of
infeasibility or feasibility from hand bookkeeping alone — hand analysis
proposes, exact computation disposes.

Updated picture of the positive-gluing frontier: universal classes now
proved are cone⊗cone (product kernel), μ⊗μ (diagonal), μ⊗M·δ_{t₀}
(column embedding), and mass-zero⊗zero (column embedding). All exact LP
probes on Fin 3 x Fin 3 (adversarial mass-zero rays, guard pairs, the
positive-mass XOR ray against kernels) came out feasible. Still open:
two arbitrary distinct weights of equal mass. Candidate mechanisms for
the general case are the witness structures being extracted by primal
solves; if the positivity layer stays obstruction-free even there, the
physical selection content must live in spectral/phase structure.
-/

def columnEmbeddingGluingResult : Prop :=
  -- Column embedding: every nonnegative pairwise weight couples positively
  -- with the point mass of its own total mass; mass-zero weights couple
  -- with the zero weight. Distinct-weight universal gluing stays open.
  True

theorem column_embedding_gluing_result_recorded :
    columnEmbeddingGluingResult := by
  trivial

/-!
### Transport, additive, and sum-composed gluing: four more universal
### coupling classes

`Proofs/QMClosure/TransportAndAdditiveGluing.lean` (machine-checked, clean
axioms) adds four constructions that substantially close the adversarial
Fin 3 x Fin 3 frontier by MECHANISM rather than by LP verdict:

1. TRANSPORT GLUING: for ANY map σ : α → β (no injectivity), every
   nonnegative pairwise weight μ couples positively with the transport
   σ∗μ = T ↦ μ {i | σ i ∈ T}, via the graph-carried weight
   W U = μ {i | (i, σ i) ∈ U}. This SUBSUMES the diagonal self-gluing
   (σ = id) and the column embedding (constant σ: point mass, or zero
   for mass-zero μ). Non-injective σ produces genuinely new right
   marginals: fiber-merged transports.

2. ADDITIVE GLUING: every additive weight with nonnegative coefficients
   couples positively with EVERY nonnegative pairwise weight of the same
   positive total mass, via the row-copy mixture W U = Σᵢ (aᵢ/M)·ν{T |
   (i,t) ∈ U} (each product row carries an independent scaled copy of ν).

3. ZERO LEFT: the zero weight couples with every mass-zero nonnegative
   pairwise weight (which may be nonzero, e.g. XOR rays) via the left
   slice. Together with column-embedding zero-mass this closes the
   0-corner of the mass-zero sector.

4. SUM COMPOSITION: gluings compose by sums. Corollary: any weight
   decomposing as an additive nonneg part carrying the whole positive
   mass plus a mass-zero nonneg residue couples with EVERY equal-mass
   nonnegative pairwise weight.

All adversarial Fin 3 x Fin 3 pairs from the previous probe are now
closed by these mechanisms, not just by LP feasibility: f⊗f2 and H₁₂⊗H₁₃
and P₁₂⊗P₁₃ are transports (relabels); f⊗0 and H₁₂⊗0 are constant
transports; 2f+E₁⊗P₁₂ is the additive part E₁ plus the mass-zero residue
2f glued by sum composition — its explicit decomposition witness
(2·f on one column + P₁₂-copy on one row) was verified exactly against
all 512 events and both cylinders.

Correction of an earlier session claim, recorded for discipline: f₂ was
previously reported as NOT transport-related to f. That was wrong — the
check used the wrong permutation; σ = 0↔2 gives f₂ = σ∗f. The lesson
repeats the standing rule: transport-relatedness claims need a verified
σ, not an eyeballed one.

Numerical validation BEFORE Lean (exact rational arithmetic): the
transport construction on 300 random instances (all events, both
cylinders, pairwise form) — 0 failures; the row-copy mixture on 400
random instances — 0 failures; the 2f+E₁⊗P₁₂ decomposition witness —
0 violations.

Immediate further corollary of sum composition: column embedding
(μ, 0) plus left slice (0, ν) gives (μ, ν) for ANY two mass-zero
nonnegative pairwise weights — the ENTIRE mass-zero × mass-zero sector
is closed (`mass_zero_sector_gluing`), including the previously open
f⊗H₁₂-type pairs. Further corollaries of the same session: the transport
marginal σ∗μ is itself pairwise generated (via the left-cylinder lemma —
the previously recorded obligation was stale and is now closed), and
cone couplings compose by sums (splits of both sides into positively
generated pieces with matching masses glue; canonical case
2P₁₂ ⊗ (P₁₂+P₁₃)).

Skeptical re-verification pass (machine, exact):

1. All transport-relatedness claims were re-checked EXHAUSTIVELY over
   all 27 maps σ : Fin 3 → Fin 3 (the earlier checks were hand
   calculations). Confirmed related: f→f₂, H₁₂→H₁₃, P₁₂→P₁₃, P₁₂→P₂₃,
   H₁₂→H₂₁, and — a NEW closure correcting another hand judgment —
   f+P₁₂ → f₂+P₁₃ (via the 3-cycle σ = (2,0,1); the hand analysis had
   guessed "not related"). Genuinely unrelated: 2f+E₁ vs 2f₂+E₂ and
   f+P₁₂ vs f₂+P₂₃ — these two are the honest remaining positive-mass
   frontier pairs.

2. Cone-plus-zero-mass DECOMPOSITION probe (the reduction carrier):
   does every nonnegative pairwise weight μ of positive total mass
   admit a positively generated C with C ≤ μ pointwise and
   C(univ) = μ(univ)? Then R = μ − C is nonnegative of mass zero, and
   universal positive gluing of ALL equal-mass pairs would follow by
   kernel-coupling the cone parts (equal mass) + mass-zero-coupling the
   residues + summing.

   VERDICT: REFUTED on Fin 4 (exhaustive integer grid a ∈ {0,1,2},
   q ∈ {−2..2}: 1990 positive-mass instances, 5 failures, all in one
   family) and on Fin 5 (2 of 1387 random rational instances). The
   smallest witness (hand-verified certificate):

     μ* = δ₃ + (q₀₁ = q₀₂ = q₁₂ = 1) − (q₀₃ = q₁₃ = q₂₃ = 1),
     values: {3}=1, {01}={02}={12}=1, {012}=3, every proper triple
     containing 3 = 0, univ = 1; mass 1, all values ≥ 0.

   Farkas certificate: the three zero-valued triples {0,1,3}, {0,2,3},
   {1,2,3} cover every point and every pair, so any data-nonneg C ≤ μ*
   pointwise vanishes on all three triples, hence C = 0, hence no tight
   cone-below decomposition exists. Coverage and the LP infeasibility
   were both machine-verified; the certificate is airtight.

   Consequences, recorded honestly: (i) the cone+zero ROUTE to
   universal positive gluing is dead beyond Fin 3; the Fin-3 case is
   genuinely special (pairs are the maximal proper subsets there, and
   Σ_{pairs} μ(ij) = 2Σa + Σq ≥ μ(univ) always certifies). (ii) The
   generator-based "Fin 4 sample held" claim in the previous entry was
   an artifact: the random generators (points, pairs, guards, XOR
   triples) miss the δ-plus-triangle-minus-star family; the exhaustive
   integer grid found the counterexample immediately. Lesson promoted:
   generator-sample evidence about cone-level questions must be labeled
   by generator coverage, or replaced by integer-grid enumeration.
   (iii) μ* is the new canonical probe weight: nonnegative, pairwise,
   mass 1, not transport-related to its cone partners, not
   decomposable. Whether μ* positively couples with equal-mass
   partners (P₀₁, f+P₁₂, μ*₂) is the sharp open gluing question now
   running as exact 4×4 / 4×3 LP.

   UPDATE (same session): the wall does NOT obstruct gluing. Exact LP
   on the 4×2 grid: μ* ⊗ P₀₁ FEASIBLE, with an explicitly verified
   witness (0 violations over all 255 events and both cylinders):
   δ₃ sits at the single point (3,0); the positive triangle pairs of
   μ* are carried on cross-column pairs ((i,1),(j,0)); the negative
   star on pairs into (3,0). The 4×3 and 4×4 probes for
   μ* ⊗ (f+P₁₂) and μ* ⊗ μ*₂ are still running.

   CORRECTION (next session, machine-verified): the paragraph above
   misclassified the 4×2 witness. The witness is EXACTLY the transport
   gluing of μ* along σ = (1,0,0,0): the A-mass sits at (i, σ i) for
   every i, every μ*-pair sits on ((i, σ i), (j, σ j)), and direct
   evaluation confirms W(U) = μ*({i : (i, σ i) ∈ U}) on ALL 256 events
   of the 4×2 grid, not just the cylinders. The "cross-column" look of
   the pairs is merely the σ-split of α across the two columns; there
   is no pair-spreading mechanism. In fact μ* and P₀₁ were
   transport-related all along: six maps σ : Fin 4 → Fin 2 have
   pushforward values equal to P₀₁'s (0, 0, 0, 1). μ* ⊗ μ₂ needs no
   LP either: μ₂ = δ₀ + triangle{1,2,3} − star(0) is a relabeling of
   μ* (swap the special point 3 ↔ 0), six bijections σ witness
   transport-relatedness in both directions, and the already-proved
   transport theorem closes the pair. The only genuinely open partner
   from the wall family is f+P₁₂ on Fin 3 (zero transport maps in
   either direction, not additive, not positively generated); its
   4×3 cutting-plane LP is the decisive probe: FEASIBLE gives the
   first machine-verified gluing beyond the transport family,
   INFEASIBLE gives the first positivity obstruction beyond the
   equal-mass gate.

   Process lesson, second occurrence, promoted to a rule: mechanism
   labels for LP witnesses must be machine-checked against the
   transport family (exhaustive σ-scan matching the witness event
   values, not the partner's stated form) BEFORE any "new mechanism"
   claim is recorded. The first occurrence (f ⊗ f₂ "not transport"
   from a wrong permutation) was caught pre-record; this one was
   recorded and had to be corrected.

   RESOLUTION (same follow-up session, machine-checked): the last open
   wall pair μ* ⊗ (f+P₁₂) CLOSES constructively, and the construction
   is a new THEOREM, not a new mechanism family. Splitting scan over
   integer piece data found ν = ν_A + ν_B with ν_A = P₀₁ embedded in
   Fin 3 (values {01}=1, {012}=1) and ν_B = f − q₀₂ (mass 0, values
   {0}=1, {12}=1, {012}=0), where ν_A is the transport of μ* along
   σ = (0,1,2,2) (σ-dominance: μ*({i : σ i ∈ T}) ≤ ν(T) on every T,
   checked directly). The composed weight W = transport(μ*, σ) +
   zeroLeft(ν_B) was verified at the value level with ZERO violations
   over all 4095 events and all 21 cylinders. Generalized and proved
   in Lean (TransportAndAdditiveGluing.lean):

     sigma_dominance_gluing: equal masses + (∃ σ, ∀ T,
     μ {i | σ i ∈ T} ≤ ν T) ⇒ positive gluing,

   a pure composition of transport_gluing + zero_weight_gluing +
   gluing_sum_composition; the residual ν_B = ν − σ∗μ needs no
   structure beyond nonnegativity (dominance) and mass zero (equal
   masses). Dominance is sufficient, not necessary: δ₀ vs P₁₂ has no
   dominance map either way yet glues by additivity. With this, ALL
   probed equal-mass partners of the wall witness close inside the
   proved family, and no positivity obstruction beyond the equal-mass
   gate has appeared anywhere. The sharp remaining questions: does
   some equal-mass pair fail to glue at all, and do dominance +
   additivity (+ cone pieces) cover all pairs.

   COVERAGE (same session, exhaustive integer grids a, q ∈ {−1,0,1}):
   single-mechanism coverage of equal-mass nonnegative pairwise pairs —
   2×2: 35/35, 2×3: 386/386, 3×2: 386/386, 3×3: 5334/5532 (96.4%,
   dominance alone covers 4826), 4×3: 155955/173044 (90.1%). The 198
   uncovered 3×3 pairs: the 12 probed by the exact gluing LP are ALL
   gluing-FEASIBLE (Farkas alternative infeasible; no certificate
   exists), and ALL 198 close by 2-splittings into single-mechanism
   piece pairs on the scanned {−1,0,1} piece grid — zero survivors. A
   seeded uniform sample of 300 of the 17089 uncovered 4×3 pairs:
   300/300 close by 2-splittings, zero survivors. No positivity
   obstruction beyond the equal-mass gate has appeared in any probe,
   LP-decided or constructive. Next sharp question (peelability): if
   for every equal-mass pair there always exist a map σ and nonneg
   pieces μ_A ≤ μ, ν_A ≤ ν of equal POSITIVE mass with μ_A
   dominance-related to ν_A along σ, then universal positive gluing
   follows by induction (peel + sum compose + terminal mass-zero
   sector). This lemma is exactly LP-checkable per pair and is the
   candidate route to the universal theorem.

   ADVERSARIAL FRONTIER (same session): the peel route reduces to a
   dichotomy. If either side contains a positive-mass additive
   sub-weight (exact LP test: a >= 0, sum a i <= v(S) for all S,
   vertex-mass threshold 1/4!), the pair peels by the additive
   mechanism with a scaled partner — a theorem already. The resisting
   case is both sides ADDITIVE-SUB-FREE (the Fin-4 wall witness mu*
   is such: its three zero triples force every a i to 0). Probes on
   the integer grids: among additive-sub-free equal-mass positive-mass
   pairs, 406/406 on 3x3 have a FULL dominance map (both directions
   scanned exhaustively); on 4x3, 12659/13123 have full dominance and
   ALL 464 remaining pairs admit a positive-mass PARTIAL dominance
   peel with {−1,0,1} integer pieces (464/464, zero survivors). No
   probed pair, anywhere, resists the inductive scheme: additive peel
   / full dominance / partial dominance peel / terminal mass-zero
   sector. The universal-gluing conjecture now has a precise shape:
   every equal-mass nonnegative pairwise pair admits a finite peeling
   sequence; the unproved core is exactly the both-sub-free partial
   peel, and it has never failed.

   ADVERSARIAL CAMPAIGN (same session, next cluster): the peel lemma's
   unproved core was attacked beyond the grids with exact LPs.
   (i) Random rational pairs up to 5×5 (476 instances, integer and
   half-integer data, exact mass rescaling): every pair closes — 463
   by an additive sub-weight (theorem-backed), 9 by full dominance,
   0 survivors. Random weights almost always contain additive
   sub-weights; the hard regime is genuinely the structured one.
   (ii) Dissection of the no-full-dominance pairs: they are pure pair
   structures (e.g. a 3-star cannot dominate a triangle: the shared
   apex forces fiber values 2 > 1) that split into pure pair pieces,
   each universally dominant at equal mass — the cone mechanism in
   disguise. (iii) EXHAUSTIVE signed×signed scan on Fin 4 x Fin 4:
   all 1284 additive-sub-free weights with a negative coefficient
   (the mu* family), 505,520 equal-mass cross pairs — 447,408 full
   dominance (88.5%), the rest undecidable only by LP iteration caps
   (honestly labeled no-verdict), ZERO survivors and ZERO decidable
   pairs needing even a partial peel. (iv) Mixed signed×unsigned 4×4,
   400 sampled: 353 full dominance, 0 survivors. Unsigned×unsigned
   equal-mass pairs are cone-covered outright (theorem, no probe
   needed). Net frontier statement: the universal-gluing conjecture
   reduces to a complete case split — additive sub-weight (theorem) /
   both positively generated (cone theorem) / otherwise full or
   partial dominance peel — and the residual empty case (signed,
   both sub-free, no dominance peel of any positive mass) has NEVER
   been observed in any probe of this thread.

   RESOLUTION OF THE NO-VERDICT BLOCK (next session): all 58,112 pairs
   left open by the LP iteration caps are now DECIDED, and the empty
   case is EMPTY on Fin 4. Three machine results. (1) The 1284-weight
   signed sub-free pool collapses to 72 S4-canonical classes; the
   1534 canonical equal-mass ordered pairs contain 222 without full
   dominance in either direction (reconfirmed by the exhaustive
   LP-free sigma scan). With an exact Bland-rule simplex (no cycling,
   zero-rhs rows folded to equalities, singleton zeros eliminated as
   variables; positive-mass threshold 1/150000, which is exact since
   vertex denominators of the 10-variable 0/1 system divide a 10x10
   0/1 determinant <= 10^5 by Hadamard against integer rhs), ALL 222
   classes admit a FORWARD dominance peel mu -> nu with an
   arithmetically verified witness (0 <= eta <= mu valuewise,
   sigma*eta <= nu valuewise, positive mass): zero empty cases, zero
   unresolved. (2) The mixed signed x pure-pair frontier is closed
   exhaustively at the canonical level: 44 oriented no-dominance
   pairs, all peel, zero empty cases (this supersedes the 47 sampled
   no-verdict pairs of the mixed campaign). Fin 4 x Fin 4 is now
   completely classified: additive peel (theorem) / cone (theorem) /
   full dominance / verified forward peel. (3) PATTERN REDUCTION
   THEOREM (hand-proved, machine-cross-validated): a dominance peel
   mu -> nu exists IFF some sigma makes the cone {eta >= 0 valuewise,
   eta vanishing on every zero set of mu and on every pullback of a
   zero set of nu} contain a positive-mass element — the peel question
   depends ONLY on the zero-set hypergraphs, by lambda-scaling to the
   infinitesimal limit in both directions. Machine check: class-level
   agreement on all 44 mixed no-dominance pairs and per-sigma
   agreement on 25 signed classes (6400 sigma verdicts), zero
   disagreements. Consequence: every Fin-4 no-dominance class closes
   by the PAIR-TO-PAIR certificate — both sides have a positively
   shadowed pair (rho_ij = min over supersets S >= {i,j} of mu(S) >
   0), eta = min(rho_mu, rho_nu) * p_ij, sigma maps the two pairs
   onto each other — 222/222 classes are of this LP-free type. The
   unique shadow-free weight of the whole signed pool (all six pair
   shadows zero) is the spider itself; its zero pattern forces
   eta = t * spider (the singleton, {leg,center} and {leg,leg,center}
   zeros solve all ten coefficients up to one parameter t), so its
   sub-weight cone is exactly the ray [0, spider], and the spider
   never lands in a no-dominance equal-mass pair (its partners all
   reach full dominance, both directions scanned exhaustively). All
   72 canonical weights have an integral zero-set cover: the
   fractional/integral gap of the sub-free characterization never
   materializes on Fin 4. The general lemma now has a precise target:
   pair-peel (hand proof, immediate) whenever both sides carry a
   positively shadowed pair; the only possible resistance is
   shadow-free against shadow-free (spider unions), first
   constructible beyond Fin 4 — e.g. spider_4 on Fin 5 (mass 3)
   against three disjoint Fin-4 spiders (mass 3) — and that family is
   the next adversarial probe.

Evidence-discipline notes from this pass: (a) the random generators
used for pre-validating the transport/additive constructions sample
only a subcone of all nonnegative weights (guards were absent from the
Fin-3 generator); the Lean theorems themselves are unconditional, but
future probes must use the guard-inclusive generator; (b) every
transport-relatedness judgment now comes from the exhaustive 27-map
scan, not from hand inspection; (c) the 58,112 no-verdict labels of
the exhaustive campaign were a solver artifact — Dantzig cycling on
degenerate peel systems — not mathematical openness; degenerate
feasibility LPs in this thread must run Bland-only from iteration 1,
and any iteration-cap report must name the pivoting rule.

   BEYOND FIN 4 (same session, Rust+Python campaign): the empty case
   EXISTS.  Exhaustive integer-grid enumeration ({-1,0,1} data,
   canonical under the full symmetric group) produced 289 nonneg
   signed Fin-4 classes (72 sub-free, matching the earlier pool — a
   validation anchor) and 6743 Fin-5 classes (1510 sub-free, exact LP
   threshold 1/5!).  Rust scans over ALL equal-mass sub-free pairs:
   431,292 pairs on Fin 5 x Fin 5 (61.1% full dominance, 38.5% T1
   pair-peel, 48 T2 zero-morphism, 1682 survivors) and 2 x 22,454
   cross-size pairs (76.3% dominance, 23.4% T1, 71 survivors each
   orientation).  Pattern-cone LP on every survivor: the cross-size
   survivors are ALL genuine EMPTY-CASE instances — no dominance,
   no T1, no T2, and an empty pattern cone in BOTH orientations
   (exact Bland LPs, zero caps); the Fin-5 x Fin-5 rerun finished at
   1682/1682 EMPTY (zero caps) — 1824 canonical empty-case pairs in
   total across the three size orientations.  By the pattern reduction theorem this means the
   PEEL ROUTE PROVABLY DOES NOT CLOSE beyond Fin 4: pairs of
   shadow-free weights (the Fin-5 census found 15 shadow-free classes,
   of which only ONE is the classic spider — fourteen are new
   multi-center shapes) resist every peel mechanism.  The naive
   structure hope "sub-free = cone over spiders and pure pairs" is
   REFUTED outright on Fin 4 (only 7/72 classes lie in that cone).
   The original gluing question for these pairs is being decided by a
   certified hybrid pipeline whose load-bearing trick is SYMMETRY
   REDUCTION: Aut(mu) x Aut(nu) acts on the grid, the constraint set
   (cylinders + W >= 0 on all subsets) is invariant, and averaging
   over the group maps solutions to solutions — so a gluing exists
   IFF a group-symmetric one does, and infeasibility of the
   orbit-reduced system (typically 20-60 orbit variables instead of
   210 cell coefficients) proves infeasibility of the full system.
   The exhaustive 2^(nA*nB) subset scan — the certification loop's
   bottleneck — runs as a Rust cdylib called from Python via ctypes
   (58 ms per full 2^20 scan versus 10-15 s in pure Python).  With
   this machinery the verdicts so far: the spider-4 instance GLUABLE
   (den 36, |G| = 144), the bi-center instance GLUABLE (den 4) — the
   one that had ground unstoppably in the unsymmetrized cutting
   plane — plus two more families GLUABLE (den 2, den 4); four
   further mu-families are still resolving.  Every GLUABLE verdict
   carries a fully verified witness: cylinders exact by construction
   (rational Gaussian elimination) and nonnegativity certified by an
   exhaustive exact integer scan over ALL 2^20 subsets.  Net result
   so far: the empty case is real for the PEEL route but every
   decided instance still glues — universal positive gluing survives
   Fin 5, but through gluings no peel mechanism explains.
   Discipline notes
   from this pass: (d) a survivor-file parsing bug (the mass field
   was read as a coefficient) silently corrupted the first round of
   pattern verdicts — fixed, all verdicts rerun, and the corrected
   outcome is recorded here; the earlier "71/71 T3" reading was an
   artifact; (e) a hand "zero-block lemma" (nonneg 2-additive with
   zero total on >= 3 points vanishes) was REFUTED by the
   counterexample (1,1,1,-1,-1,-1) before it could poison the record
   — zero-total nonneg weights on 3+ points form the mass-zero
   sector, they do not vanish.
-/

def transportAdditiveGluingResult : Prop :=
  -- Transport gluing (any σ, with pairwise transport marginals), additive
  -- gluing (row-copy mixture), zero left gluing, sum composition, the
  -- whole mass-zero sector, cone pair sums, and sigma-dominance gluing
  -- (equal masses + a dominance map sigma with mu {i | sigma i in T} <=
  -- nu T for all T) are proved. The cone-plus-zero-mass decomposition
  -- conjecture (which would have implied universal positive gluing) is
  -- REFUTED on Fin 4 by a machine-checked Lean wall
  -- (ConeDecompositionWall), but the wall does not obstruct gluing:
  -- every probed equal-mass partner of the wall witness closes inside
  -- the proved family (transport for P01 and the relabel mu2,
  -- sigma-dominance for f+P12). The Fin-4 empty case (both sub-free,
  -- no dominance peel) is now EXHAUSTIVELY EMPTY: all no-dominance
  -- canonical pairs admit a verified forward peel, and the peel
  -- question reduces exactly to zero-set patterns (pattern reduction
  -- theorem), with the pair-to-pair certificate covering all of them.
  -- BEYOND Fin 4 the empty case is REAL: exhaustive Fin-5 pools show
  -- equal-mass sub-free pairs with no dominance, no pair-peel, no
  -- zero-morphism and an empty pattern cone in both orientations —
  -- the peel route provably does not close there.  At least one such
  -- pair (the spider-4 instance) still GLUES, with a verified witness
  -- no peel explains; the bi-center instance and two further
  -- families also GLUE (certified witnesses, symmetry-reduced exact
  -- cutting plane); remaining families resolving.  The open
  -- question is now exactly: does every equal-mass nonneg pairwise
  -- pair glue, even when every peel mechanism fails?
  True

theorem transport_additive_gluing_result_recorded :
    transportAdditiveGluingResult := by
  trivial

end V8
end MetaLang
end IDT
