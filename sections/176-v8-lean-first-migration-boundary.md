## 176. V8 Lean-First Migration Boundary

Status: migration boundary, not a new physical proof.

The v8 direction is Lean-first:

```text
proved claim -> Lean artifact
research route -> IDT declarative language / manifest
numeric gate -> executable trusted checker
legacy Python verifier -> deprecated compatibility only, not proof source of truth
```

The migration freezes new physical research claims until the already recorded
claim discipline has been moved into Lean. The first Lean layer is:

The non-negotiable v8 goal is not to prove the whole theory at any cost. It is
to ensure that every recorded conclusion is exactly as strong as the available
evidence and proof artifacts justify. A research route, plausible argument,
finite verifier pass, calibration, or successful experiment must never be
upgraded into a stronger claim than it supports.

```text
Proofs/MetaLang/V8VerificationLanguage.lean
Proofs/MetaLang/V8ContextFirstPrimitiveBase.lean
Proofs/MetaLang/V8TheoremCardLedger.lean
Proofs/MetaLang/V8CurrentStatusSnapshot.lean
Proofs/MetaLang/V8ExternalCheckerBoundary.lean
Proofs/MetaLang/V8StatusTransitionPolicy.lean
Proofs/MetaLang/V8DependencyGraphPolicy.lean
Proofs/MetaLang/V8ProofArtifactContract.lean
Proofs/MetaLang/V8LeanFirstTrustKernel.lean
Proofs/MetaLang/V8CoreClaimDisciplineRules.lean
Proofs/MetaLang/V8ControlledVocabularyInventory.lean
Proofs/MetaLang/V8ManifestCollectionContract.lean
Proofs/MetaLang/V8RuleManifestGrounding.lean
Proofs/MetaLang/V8AssertionPredicateSemantics.lean
Proofs/MetaLang/V8CoreRuleSemanticClosure.lean
Proofs/MetaLang/V8DeclarativeReportContract.lean
Proofs/MetaLang/V8ClaimStrengthInvariant.lean
Proofs/MetaLang/V8VerifierDecommissionPolicy.lean
Proofs/MetaLang/V8DeclarativeDocumentSchema.lean
Proofs/MetaLang/V8CoreClaimDisciplineDocument.lean
Proofs/MetaLang/V8MigrationRoadmap.lean
Proofs/MetaLang/V8ManifestInputBoundary.lean
Proofs/MetaLang/V8ResidualMigrationLedger.lean
Proofs/MetaLang/V8MigrationStopBoundary.lean
Proofs/MetaLang/V8FormalProofScopeBoundary.lean
Proofs/MetaLang/V8ResidualRouteClassification.lean
Proofs/MetaLang/V8TaskBlockerLedger.lean
Proofs/MetaLang/V8CurrentMigrationState.lean
Proofs/MetaLang/V8CurrentTheoremAndObligationLedger.lean
Proofs/MetaLang/V8TheoremDependencyBoundaryLedger.lean
Proofs/MetaLang/V8CurrentFrontierBlockers.lean
Proofs/MetaLang/V8ResidualGateExperimentProfile.lean
Proofs/MetaLang/V8ResidualEncodingRequirements.lean
Proofs/MetaLang/V8MigrationCompletionCriterion.lean
Proofs/MetaLang/V8StoppedResearchFrontier.lean
```

This layer encodes:

1. controlled vocabulary discipline;
2. `formal_proof` requires a Lean proof artifact;
3. `derived` claims cannot depend on open or blocked dependencies;
4. theorem cards and proof obligations must preserve machine boundaries;
5. the current proof-status snapshot has no false `formal_proof` closure;
6. Python/numeric/data gates may supply finite verifier passes only while they
   remain compatibility checks, but not `formal_proof`;
7. status transitions require explicit evidence and cannot silently upgrade;
8. dependency records require grounded edges, acyclicity, and clean forward
   status dependencies;
9. formal proof upgrades require runnable Lean artifacts with path, theorem
   name, and check command;
10. accepted theorem-card, transition, dependency, artifact, and legacy-checker
    ledgers compose into a single Lean-first trust kernel;
11. the v8 core claim-discipline specification has exactly the accepted six
    rule shapes mirrored from the declarative input;
12. the v8 controlled vocabulary is mirrored into Lean with project-local terms
    kept distinct from standard scientific/formal-methods vocabulary;
13. the v8 manifest reference-index collection set is fixed in Lean without
    freezing current manifest collection sizes;
14. every v8 core rule target collection is grounded in the Lean manifest
    collection contract;
15. all ten v8 assertion predicate operations have abstract Lean semantics;
16. every predicate used by the six v8 core claim-discipline rules is connected
    to Lean-side assertion semantics;
17. declarative reports with issues are not accepted, and accepted core reports
    must check the six v8 core rules;
18. conclusion strength must not exceed evidence strength;
19. the old Python verifier is deprecated compatibility only and targets
    decommission in favor of the Lean proof kernel;
20. IDT v8 declarative verification documents have a Lean-side schema whose
    accepted rules must target allowed collections and use Lean-semantics
    assertions;
21. the current core claim-discipline document is mirrored as an accepted Lean
    object;
22. the migration roadmap is fixed: Lean migration first, residual IDT v8
    encoding second, then stop; only after that are new CI, legacy archive,
    mandatory compressed research-context packing, and research handoff allowed;
23. the active manifest is an IDT v8 input boundary, not proof authority;
24. the current residual manifest surface is counted as IDT v8 input with no
    formal-proof status;
25. the migration stop boundary is explicit: only after the core document,
    manifest input boundary, residual ledger, and Python deprecation boundary
    are accepted can new CI, legacy archive, and research handoff happen;
26. current formal proofs are scoped to verification discipline; theorem-card
    physical claims and QM core obligations still have zero formal-proof
    closures;
27. residual material is routed either to Lean migration or to IDT v8 residual
    input encoding;
28. migration tasks are typed Lean blockers for later phases such as new CI,
    legacy archive, and research readiness;
29. the current migration state is Lean migration, and IDT v8 residual encoding,
    migration stop, legacy archive, and research readiness remain blocked until
    their task blockers are completed;
30. all 23 current theorem cards and all 11 current QM core proof obligations
    are represented in Lean as typed status ledgers with zero formal-proof
    physical/QM closures;
31. theorem-card dependency and forbidden-claim boundaries, plus QM-obligation
    dependency/open-gap/claim-boundary profiles, are represented in Lean;
32. the exact/full-QM frontier has explicit active blockers in Lean, including
    Hilbert-carrier and Born-rule blockers;
33. finite gates and QM experiments have a residual IDT v8 profile: 247 gates
    across a long-tail type surface, and 35 QM experiments awaiting IDT v8
    classification;
34. IDT v8 residual encoding is not ready for migration stop while the 35 QM
    experiments still need v8 classification and the residual boundary remains
    declarative input rather than proof truth;
35. Lean-eligible migration has an explicit completion criterion: the theorem
    and QM-obligation ledgers are encoded and have no false formal-proof
    closure, but current open/blocked theorem candidates keep the phase
    incomplete and block IDT v8 residual encoding;
36. a compressed full research-tree context packer is mandatory research-model
    work after migration stop/new CI/legacy archive, not current migration work;
37. the context-first primitive base:

```text
B0 = (C, O, I, R, D)
```

where:

- `C` is admissible context cover/category;
- `O` is local outcome-event presheaf;
- `I` is inheritance transition family;
- `R` is facticization/readout witness relation;
- `D` is stable distinguishability relation.

The old `H/E/M/I` scaffold is retained only as compatibility/readout
machinery. It is not the current primitive base.

The stopped QM frontier is also encoded, without upgrading the claim:

```text
B1
+ context-first constructive witness completeness
+ carrier-frontier exhaustion
=> finite standard-QM sector closure
```

Exact fundamental QM still requires:

1. lower-base derivation of B1;
2. lower-base derivation of context-first witness completeness;
3. lower-base derivation of carrier-frontier exhaustion;
4. external Hilbert/Born/unitary/tensor adequacy;
5. exact universal Born readout;
6. first-principles physical phase scale.

Therefore v8 does not claim that QM is proved. It changes the trust model:
anything marked as proved must survive Lean.
