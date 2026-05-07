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
    encoding second, then stop; only after that are new CI, legacy archive, and
    research handoff allowed;
23. the active manifest is an IDT v8 input boundary, not proof authority;
24. the current residual manifest surface is counted as IDT v8 input with no
    formal-proof status;
25. the context-first primitive base:

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
